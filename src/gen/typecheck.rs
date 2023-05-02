use std::borrow::Cow;

use crate::{
    ast::{
        type_expr::{self, NumericType, TypeExpr},
        Ast, AstNode, AstNodeRef, CookedAst, Function, LocalContext, Variable,
    },
    error::{
        location::{SourceLocation, Traced},
        CollectIfErr, ErrorContent,
    },
    token::NumValue,
};

use super::{clif_types, trans_ty, ClifType, GlobalContext};

static ANY_NUMERIC: TypeExpr = TypeExpr::_UnknownNumeric(NumericType::new());

#[must_use]
pub fn type_matches(global: &GlobalContext, expect: &TypeExpr, found: &TypeExpr) -> bool {
    use TypeExpr::*;
    match (expect, found) {
        (TypeName(..), TypeName(..)) => todo!(),
        (TypeName(..), _) => todo!(),
        (_, TypeName(..)) => todo!(),
        (_, Never) | (_Unknown, _) | (_, _Unknown) => true,
        (USize, USize)
        | (ISize, ISize)
        | (U128, U128)
        | (U64, U64)
        | (U32, U32)
        | (U16, U16)
        | (U8, U8)
        | (I128, I128)
        | (I64, I64)
        | (I32, I32)
        | (I16, I16)
        | (I8, I8)
        | (F64, F64)
        | (F32, F32)
        | (Char, Char)
        | (Bool, Bool) => true,
        (Ptr(lhs), Ptr(rhs)) => type_matches(global, lhs, rhs),
        (Ref(lhs), Ref(rhs)) => type_matches(global, lhs, rhs),
        (Slice(lhs), Slice(rhs)) => type_matches(global, lhs, rhs),
        (Array(lhs_len, _), Array(rhs_len, _)) if lhs_len != rhs_len => false,
        (Array(_, lhs), Array(_, rhs)) => type_matches(global, lhs, rhs),
        (Tuple(lhs), Tuple(rhs)) if lhs.len() != rhs.len() => false,
        (Tuple(lhs), Tuple(rhs)) => {
            let mut rhs_iter = rhs.iter();
            for lhs in lhs.iter() {
                // we know that lhs and rhs have the same length
                let rhs = unsafe { rhs_iter.next().unwrap_unchecked() };
                if !type_matches(global, lhs, rhs) {
                    return false;
                }
            }
            true
        }
        // tuple of one field is the same as a value due to limitations of the syntax
        (Tuple(lhs), rhs) => match lhs.as_slice() {
            [lhs] => type_matches(global, lhs, rhs),
            _ => false,
        },
        (lhs, Tuple(rhs)) => match rhs.as_slice() {
            [rhs] => type_matches(global, lhs, rhs),
            _ => false,
        },
        (Fn(l_args, l_ret), Fn(r_args, r_ret)) => {
            // TODO: counter-variance logic
            for (lhs, rhs) in l_args.iter().zip(r_args.iter()) {
                if lhs != rhs {
                    return false;
                }
            }
            l_ret == r_ret
        }
        (_UnknownNumeric(expect), _UnknownNumeric(found)) => {
            if expect.is_int && !found.is_int {
                return false;
            }
            if !expect.is_signed && found.is_signed {
                return false;
            }
            true
        }
        (_UnknownNumeric(expect), found) => match (expect.is_int, expect.is_signed) {
            // expect signed int (-255)
            (true, true) => found.is_i(),
            // expect int (255)
            (true, false) => found.is_i() || found.is_u(),
            // expect signed (-255.0)
            (false, true) => found.is_f() || found.is_i(),
            // expect unsigned (255.0)
            (false, false) => found.is_f() || found.is_i() || found.is_u(),
        },
        (expect, _UnknownNumeric(found)) => match (found.is_int, found.is_signed) {
            // found signed int (-255)
            (true, true) => expect.is_i() || expect.is_f(),
            // found int (255)
            (true, false) => expect.is_i() || expect.is_u() || expect.is_f(),
            // found signed (-255.0)
            (false, true) => expect.is_f(),
            // found unsigned (255.0)
            (false, false) => expect.is_f(),
        },
        _ => false,
    }
}

/// Type check and AST and attack type informations to it, making a `CookedAst`
pub fn cook_ast(global: &GlobalContext, mut ast: Ast) -> CookedAst {
    for root_node in ast.root_nodes.iter_mut() {
        let root_node = root_node.as_mut();
        match root_node.inner_mut() {
            AstNode::FnDef(ref mut func) => cook_func(global, func),
            _ => (), // already reported error in `build_global_context`
        }
    }
    CookedAst(ast)
}

fn cook_func(global: &GlobalContext, func: &mut Function) {
    let local = &mut func.local_ctx;
    for (arg_name, arg_ty) in func.sign.args.iter() {
        local.add_var(&arg_name, arg_ty.clone());
    }
    let body: &mut [AstNodeRef] = match func.body {
        Some(ref mut x) => x,
        None => return,
    };
    for node_ref in body.iter() {
        let node = node_ref.as_ref().inner();
        match node {
            &AstNode::Tail(node) => cook_expr(global, local, node, &func.sign.ret_type),
            _ => cook_expr(global, local, *node_ref, &TypeExpr::_Unknown),
        };
    }
}

fn cook_expr<'l, 'g: 'l>(
    global: &'g GlobalContext,
    local: &'l mut LocalContext,
    mut node: AstNodeRef,
    expect_ty: &TypeExpr,
) -> Option<Cow<'l, TypeExpr>> {
    let node = node.as_mut();
    let node_loc = node.src_loc();
    let node = node.inner_mut();
    match node {
        AstNode::Identifier(var_name) => match local.var_id(var_name) {
            Some(var) => {
                *node = AstNode::Variable(var);
                cook_var(global, local, node_loc, var, expect_ty)
            }
            None => {
                ErrorContent::UndefinedVar(&var_name)
                    .wrap(node_loc)
                    .collect_into(&global.err_collector);
                None
            }
        },
        &mut AstNode::Number(num_val) => {
            cook_num(global, node_loc, expect_ty, node, num_val).map(|x| Cow::Owned(x))
        }
        AstNode::String(..) => todo!(),
        AstNode::Char(..) => {
            if !type_matches(global, expect_ty, &TypeExpr::Char) {
                ErrorContent::MismatchdTypes(expect_ty.clone(), TypeExpr::Char)
                    .wrap(node_loc)
                    .collect_into(&global.err_collector);
                None
            } else {
                Some(Cow::Owned(TypeExpr::Char))
            }
        }
        AstNode::Bool(..) => {
            if !type_matches(global, expect_ty, &TypeExpr::Bool) {
                ErrorContent::MismatchdTypes(expect_ty.clone(), TypeExpr::Bool)
                    .wrap(node_loc)
                    .collect_into(&global.err_collector);
                None
            } else {
                Some(Cow::Owned(TypeExpr::Bool))
            }
        }
        AstNode::Array(_) => todo!(),
        &mut AstNode::MathOp(_, lhs, rhs) => cook_numeric_op(global, local, expect_ty, lhs, rhs),
        &mut AstNode::BitOp(_, lhs, rhs) => cook_numeric_op(global, local, expect_ty, lhs, rhs),
        &mut AstNode::BoolOp(_, lhs, rhs) => cook_bool_op(global, local, expect_ty, lhs, rhs),
        &mut AstNode::Cmp(_, lhs, rhs) => cook_cmp(global, local, expect_ty, lhs, rhs),
        AstNode::MemberAccess(_, _) => todo!(),
        AstNode::BitNot(_) => todo!(),
        AstNode::BoolNot(_) => todo!(),
        &mut AstNode::UnarySub(child) => {
            cook_unary_sub(global, local, node, child, expect_ty).map(|x| Cow::Owned(x))
        }
        AstNode::UnaryAdd(_) => todo!(),
        AstNode::Call(callee, args) => {
            cook_call(global, local, expect_ty, *callee, &args, node_loc)
        }
        AstNode::Let(lhs, ty, rhs) => cook_let(global, local, *lhs, ty.as_ref(), *rhs),
        &mut AstNode::Assign(lhs, rhs) => {
            cook_assign(global, local, lhs, rhs);
            Some(Cow::Owned(TypeExpr::void()))
        }
        AstNode::MathOpAssign(_, _, _) => todo!(),
        AstNode::BitOpAssign(_, _, _) => todo!(),
        AstNode::TakeRef(_) => todo!(),
        AstNode::Deref(_) => todo!(),
        AstNode::Block(_) => todo!(),
        AstNode::FnDef(_) => todo!(),
        AstNode::If(_) => todo!(),
        AstNode::Loop(_) => todo!(),
        &mut AstNode::Return(Some(node)) => cook_return(global, local, node),
        // never type matches all types, there is no need to check
        AstNode::Break | AstNode::Continue | AstNode::Return(None) => {
            Some(Cow::Owned(TypeExpr::Never))
        }
        AstNode::Typecast(_, _) => todo!(),
        AstNode::TypeDef(_, _) => todo!(),
        AstNode::StructDef(_) => todo!(),
        AstNode::UnionDef(_) => todo!(),
        AstNode::EnumDef(_) => todo!(),
        AstNode::Tuple(_) => todo!(),
        AstNode::TypedNumber(..) | AstNode::Variable(..) | AstNode::Tail(..) => unreachable!(),
    }
}

fn cook_var<'l, 'g: 'l>(
    global: &'g GlobalContext,
    local: &'l mut LocalContext,
    loc: SourceLocation,
    var: Variable,
    expect_ty: &TypeExpr,
) -> Option<Cow<'l, TypeExpr>> {
    let var_ty = local.var_ty_mut(var).unwrap();
    if !type_matches(global, expect_ty, var_ty) {
        ErrorContent::MismatchdTypes(expect_ty.clone(), var_ty.clone())
            .wrap(loc)
            .collect_into(&global.err_collector);
        return None;
    }

    // try to collapse the variable to a concrete type if needed
    if var_ty.is_unknown() || var_ty.is_unknown_numeric() && !expect_ty.is_unknown() {
        *var_ty = expect_ty.clone();
    }
    Some(Cow::Borrowed(var_ty))
}

/// Try to collapse the variable to a concrete type if needed, assumes type of variable matches `expect_ty`
fn try_collapse_var_ty<'l>(local: &'l mut LocalContext, node: AstNodeRef, expect_ty: &TypeExpr) {
    match node.as_ref().inner() {
        &AstNode::Variable(var) => {
            let var_ty = local.var_ty_mut(var).unwrap();
            if var_ty.is_unknown() || var_ty.is_unknown_numeric() && !expect_ty.is_unknown() {
                *var_ty = expect_ty.clone();
            }
        }
        _ => (),
    }
}

fn cook_num<'l>(
    global: &GlobalContext,
    loc: SourceLocation,
    expect_ty: &TypeExpr,
    node: &mut AstNode,
    num_val: NumValue,
) -> Option<TypeExpr> {
    let (ty, clif_ty) = match expect_ty {
        TypeExpr::USize => (TypeExpr::USize, clif_types::I64),
        TypeExpr::ISize => (TypeExpr::ISize, clif_types::I64),
        TypeExpr::U64 => (TypeExpr::U64, clif_types::I64),
        TypeExpr::I64 => (TypeExpr::I64, clif_types::I64),
        TypeExpr::U32 => (TypeExpr::U32, clif_types::I32),
        TypeExpr::I32 => (TypeExpr::I32, clif_types::I32),
        TypeExpr::U16 => (TypeExpr::U16, clif_types::I16),
        TypeExpr::I16 => (TypeExpr::I16, clif_types::I16),
        TypeExpr::U8 => (TypeExpr::U8, clif_types::I8),
        TypeExpr::I8 => (TypeExpr::I8, clif_types::I8),
        TypeExpr::F64 => (TypeExpr::F64, clif_types::F64),
        TypeExpr::F32 => (TypeExpr::F32, clif_types::F32),
        expect_ty @ &TypeExpr::_UnknownNumeric(num_ty) => {
            let ty = match (num_ty.is_int, num_ty.is_signed, num_val) {
                //  int?   signed? provided
                (true, true, NumValue::U(..)) => todo!(),
                (true, true, NumValue::I(..)) => expect_ty.clone(),
                (true, true, NumValue::F(..)) => todo!(),
                (true, false, NumValue::U(..)) => expect_ty.clone(),
                (true, false, NumValue::I(..)) => expect_ty.clone(),
                (true, false, NumValue::F(..)) => todo!(),
                (false, ..) => todo!(),
            };
            return Some(ty);
        }
        TypeExpr::_Unknown => {
            let ty = match num_val {
                NumValue::U(..) => TypeExpr::_UnknownNumeric(NumericType::default().int()),
                NumValue::I(..) => TypeExpr::_UnknownNumeric(NumericType::default().int().signed()),
                NumValue::F(..) => TypeExpr::_UnknownNumeric(NumericType::default()),
            };
            return Some(ty);
        }
        ty => {
            ErrorContent::MismatchdTypes(
                ty.clone(),
                TypeExpr::_UnknownNumeric(NumericType::default()),
            )
            .wrap(loc)
            .collect_into(&global.err_collector);
            *node = AstNode::TypedNumber(clif_types::INVALID, num_val);
            return None;
        }
    };
    *node = AstNode::TypedNumber(clif_ty, num_val);
    Some(ty)
}

fn cook_let<'l, 'g: 'l>(
    global: &'g GlobalContext,
    local: &'l mut LocalContext,
    lhs: AstNodeRef,
    ty: Option<&TypeExpr>,
    rhs: Option<AstNodeRef>,
) -> Option<Cow<'l, TypeExpr>> {
    let var_ty = match (ty, rhs) {
        (None, None) => {
            ErrorContent::LetNoTypeOrRHS
                .wrap(lhs.as_ref().src_loc())
                .collect_into(&global.err_collector);
            TypeExpr::_Unknown
        }
        (None, Some(rhs)) => cook_expr(global, local, rhs, &TypeExpr::_Unknown)
            .map_or(TypeExpr::_Unknown, Cow::into_owned),
        (Some(ty), None) => ty.clone(),
        (Some(ty), Some(rhs)) => {
            let rhs_ty =
                cook_expr(global, local, rhs, ty).unwrap_or(Cow::Owned(TypeExpr::_Unknown));
            if !type_matches(global, ty, &rhs_ty) {
                ErrorContent::MismatchdTypes(ty.clone(), Cow::into_owned(rhs_ty))
                    .wrap(rhs.as_ref().src_loc())
                    .collect_into(&global.err_collector);
            }
            ty.clone()
        }
    };
    cook_let_lhs(global, local, lhs, var_ty);
    Some(Cow::Owned(TypeExpr::void()))
}

fn cook_let_lhs<'l, 'g: 'l>(
    global: &GlobalContext,
    local: &mut LocalContext,
    mut node: AstNodeRef,
    ty: TypeExpr,
) {
    let node = node.as_mut();
    let loc = node.src_loc();
    match node.inner_mut() {
        &mut AstNode::Identifier(name) => {
            let var = local.add_var(name, ty);
            *node.inner_mut() = AstNode::Variable(var);
        }
        AstNode::Tuple(_) => todo!(),
        _ => ErrorContent::InvalidLetLHS
            .wrap(loc)
            .collect_into(&global.err_collector),
    }
}

fn cook_assign(
    global: &GlobalContext,
    local: &mut LocalContext,
    mut lhs: AstNodeRef,
    rhs: AstNodeRef,
) {
    let node = lhs.as_mut();
    let loc = node.src_loc();
    let expect_ty = match node.inner_mut() {
        &mut AstNode::Identifier(name) => match local.var_id(name) {
            Some(var) => {
                let var_ty = local.var_ty(var).unwrap();
                *node.inner_mut() = AstNode::Variable(var);
                var_ty.clone()
            }
            None => {
                ErrorContent::UndefinedVar(name)
                    .wrap(loc)
                    .collect_into(&global.err_collector);
                TypeExpr::_Unknown
            }
        },
        AstNode::Tuple(_) => todo!(),
        _ => {
            ErrorContent::InvalidAssignLHS
                .wrap(loc)
                .collect_into(&global.err_collector);
            TypeExpr::_Unknown
        }
    };
    dbg!(&expect_ty);
    cook_expr(global, local, rhs, &expect_ty);
}

fn cook_call<'l, 'g: 'l>(
    global: &'g GlobalContext,
    local: &'l mut LocalContext,
    expect_ty: &TypeExpr,
    callee: AstNodeRef,
    args: &[AstNodeRef],
    loc: SourceLocation,
) -> Option<Cow<'l, TypeExpr>> {
    let func_name = callee
        .as_ref()
        .inner()
        .as_identifier()
        .expect("TODO: Indirect function calling");
    let func_info = global
        .func(func_name)
        .ok_or(ErrorContent::FuncNotExist(func_name).wrap(loc))
        .collect_err(&global.err_collector)?;
    if args.len() != func_info.args.len() {
        ErrorContent::MismatchedArgsCount(Some(func_name), func_info.args.len(), args.len())
            .wrap(loc)
            .collect_into(&global.err_collector);
        // still check if at least the provided arguments are valid expressions
        for &arg in args.iter() {
            cook_expr(global, local, arg, &TypeExpr::_Unknown)?;
        }
        return None;
    }
    for (i, &arg) in args.iter().enumerate() {
        let expect_ty = unsafe { &func_info.sig.args.get_unchecked(i).1 };
        cook_expr(global, local, arg, expect_ty);
    }
    if !type_matches(global, expect_ty, &func_info.sig.ret_type) {
        ErrorContent::MismatchdTypes(expect_ty.clone(), func_info.sig.ret_type.clone())
            .wrap(loc)
            .collect_into(&global.err_collector);
    }
    Some(Cow::Borrowed(&func_info.sig.ret_type))
}

fn cook_return<'l>(
    global: &GlobalContext,
    local: &'l mut LocalContext,
    node: AstNodeRef,
) -> Option<Cow<'l, TypeExpr>> {
    cook_expr(global, local, node, &local.return_type.clone());
    Some(Cow::Owned(TypeExpr::Never))
}

fn cook_unary_sub(
    global: &GlobalContext,
    local: &mut LocalContext,
    node: &mut AstNode,
    child: AstNodeRef,
    expect_ty: &TypeExpr,
) -> Option<TypeExpr> {
    // If the expected type is unsigned or isn't numeric
    if !expect_ty.is_i()
        && !expect_ty.is_f()
        && !expect_ty.is_unknown_signed_numeric()
        && !expect_ty.is_unknown()
    {
        ErrorContent::MismatchdTypes(
            expect_ty.clone(),
            TypeExpr::_UnknownNumeric(NumericType::default().signed()),
        )
        .wrap(child.as_ref().src_loc())
        .collect_into(&global.err_collector);
        return None;
    }
    let ty = cook_expr(global, local, child, expect_ty).unwrap_or(Cow::Owned(TypeExpr::_Unknown));
    // if the child node is a number literal, flatten this unary sub to one number literal, otherwise check the type
    match child.as_ref().inner() {
        &AstNode::Number(num_val) => {
            *node = AstNode::Number(negate_num_val(num_val));
        }
        &AstNode::TypedNumber(ty, num_val) => {
            dbg!();
            *node = AstNode::TypedNumber(ty, negate_num_val(num_val));
        }
        _ => {
            let expect_ty = match expect_ty {
                TypeExpr::_UnknownNumeric(num_ty) => TypeExpr::_UnknownNumeric(num_ty.signed()),
                TypeExpr::_Unknown => TypeExpr::_UnknownNumeric(NumericType::new().signed()),
                ty => ty.clone(),
            };
            if !type_matches(global, &expect_ty, &ty) {
                ErrorContent::MismatchdTypes(expect_ty.clone(), ty.into_owned())
                    .wrap(child.as_ref().src_loc())
                    .collect_into(&global.err_collector);
                return None;
            }
        }
    }
    let ty = match ty.into_owned() {
        TypeExpr::_Unknown => TypeExpr::_UnknownNumeric(NumericType::default().signed()),
        TypeExpr::_UnknownNumeric(num_ty) => TypeExpr::_UnknownNumeric(num_ty.signed()),
        ty => ty,
    };
    Some(ty)
}

fn negate_num_val(num_val: NumValue) -> NumValue {
    match num_val {
        NumValue::U(u) => NumValue::I(-(u as i64)),
        NumValue::I(i) => NumValue::I(-i),
        NumValue::F(f) => NumValue::F(-f),
    }
}

fn cook_numeric_op<'l, 'g: 'l>(
    global: &'g GlobalContext,
    local: &'l mut LocalContext,
    expect_ty: &TypeExpr,
    lhs: AstNodeRef,
    rhs: AstNodeRef,
) -> Option<Cow<'l, TypeExpr>> {
    let expect_ty = match expect_ty {
        t if t.is_numeric() || t.is_unknown_numeric() => t,
        TypeExpr::_Unknown => &ANY_NUMERIC,
        _ => {
            ErrorContent::MismatchdTypes(
                expect_ty.clone(),
                TypeExpr::_UnknownNumeric(NumericType::default()),
            )
            .wrap(lhs.as_ref().src_loc().join(rhs.as_ref().src_loc()))
            .collect_into(&global.err_collector);
            &ANY_NUMERIC
        }
    };
    let lhs_ty = cook_expr(global, local, lhs, expect_ty)
        .map(Cow::into_owned)
        .unwrap_or(TypeExpr::_Unknown);
    let rhs_ty = cook_expr(global, local, rhs, &lhs_ty)
        .map(Cow::into_owned)
        .unwrap_or(TypeExpr::_Unknown);
    try_collapse_var_ty(local, lhs, &rhs_ty);
    if !type_matches(global, &lhs_ty, &rhs_ty) {
        ErrorContent::MismatchdTypes(lhs_ty, rhs_ty)
            .wrap(rhs.as_ref().src_loc())
            .collect_into(&global.err_collector);
        None
    } else if !type_matches(global, &rhs_ty, &lhs_ty) {
        ErrorContent::MismatchdTypes(rhs_ty, lhs_ty)
            .wrap(lhs.as_ref().src_loc())
            .collect_into(&global.err_collector);
        None
    } else {
        Some(Cow::Owned(lhs_ty))
    }
}

fn cook_cmp<'l, 'g: 'l>(
    global: &'g GlobalContext,
    local: &'l mut LocalContext,
    expect_ty: &TypeExpr,
    lhs: AstNodeRef,
    rhs: AstNodeRef,
) -> Option<Cow<'l, TypeExpr>> {
    let lhs_ty = cook_expr(global, local, lhs, &TypeExpr::_Unknown)
        .map(Cow::into_owned)
        .unwrap_or(TypeExpr::_Unknown);
    let rhs_ty = cook_expr(global, local, rhs, &TypeExpr::_Unknown)
        .unwrap_or(Cow::Owned(TypeExpr::_Unknown));
    if !type_matches(global, &lhs_ty, &rhs_ty) {
        ErrorContent::MismatchdTypes(lhs_ty, rhs_ty.into_owned())
            .wrap(rhs.as_ref().src_loc())
            .collect_into(&global.err_collector);
        None
    } else if !type_matches(global, &rhs_ty, &lhs_ty) {
        ErrorContent::MismatchdTypes(rhs_ty.into_owned(), lhs_ty)
            .wrap(lhs.as_ref().src_loc())
            .collect_into(&global.err_collector);
        None
    } else if !type_matches(global, &TypeExpr::Bool, expect_ty) {
        ErrorContent::MismatchdTypes(TypeExpr::Bool, expect_ty.clone())
            .wrap(lhs.as_ref().src_loc())
            .collect_into(&global.err_collector);
        None
    } else {
        Some(Cow::Owned(lhs_ty))
    }
}

fn cook_bool_op<'l, 'g: 'l>(
    global: &'g GlobalContext,
    local: &'l mut LocalContext,
    expect_ty: &TypeExpr,
    lhs: AstNodeRef,
    rhs: AstNodeRef,
) -> Option<Cow<'l, TypeExpr>> {
    cook_expr(global, local, lhs, &TypeExpr::Bool);
    cook_expr(global, local, rhs, &TypeExpr::Bool);
    if !type_matches(global, &TypeExpr::Bool, expect_ty) {
        ErrorContent::MismatchdTypes(TypeExpr::Bool, expect_ty.clone())
            .wrap(lhs.as_ref().src_loc())
            .collect_into(&global.err_collector);
        None
    } else {
        Some(Cow::Owned(TypeExpr::Bool))
    }
}
