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

use super::{clif_types, ClifType, GlobalContext};

#[must_use]
pub fn type_matches(global: &GlobalContext, expect: &TypeExpr, found: &TypeExpr) -> bool {
    use TypeExpr::*;
    match (expect, found) {
        (TypeName(..), TypeName(..)) => todo!(),
        (TypeName(..), _) => todo!(),
        (_, TypeName(..)) => todo!(),
        (_, Never) | (_, _Unknown) => true,
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
            if expect.is_signed && !found.is_signed {
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

/// Infer a type from an **uncooked** AST node
fn infer_type(global: &GlobalContext, local: &LocalContext, node: &AstNode) -> Option<TypeExpr> {
    match node {
        &AstNode::Identifier(name) => local
            .var_id(name)
            .and_then(|var| local.var_ty(var).cloned()),
        AstNode::Number(NumValue::U(..)) => Some(TypeExpr::_UnknownNumeric(NumericType {
            is_int: true,
            is_signed: false,
        })),
        AstNode::Number(NumValue::I(..)) => Some(TypeExpr::_UnknownNumeric(NumericType {
            is_int: true,
            is_signed: true,
        })),
        AstNode::Number(NumValue::F(..)) => Some(TypeExpr::_UnknownNumeric(NumericType {
            is_int: false,
            is_signed: true,
        })),
        AstNode::String(_) => todo!("string literals"),
        AstNode::Char(..) => Some(TypeExpr::Char),
        AstNode::Bool(..) => Some(TypeExpr::Bool),
        AstNode::Array(elements) => match elements.as_slice() {
            [] => Some(TypeExpr::Array(0, Box::new(TypeExpr::void()))),
            elements => infer_type(
                global,
                local,
                unsafe { elements.get_unchecked(0) }.as_ref().inner(),
            ),
        },
        AstNode::MathOp(_, lhs, _) | AstNode::BitOp(_, lhs, _) => {
            infer_type(global, local, lhs.as_ref().inner())
        }
        AstNode::BoolOp(..) | AstNode::Cmp(..) | AstNode::BoolNot(..) => Some(TypeExpr::Bool),
        AstNode::MemberAccess(_, _) => todo!(),
        AstNode::BitNot(n) | AstNode::UnaryAdd(n) => infer_type(global, local, n.as_ref().inner()),
        AstNode::UnarySub(n) => match infer_type(global, local, n.as_ref().inner()) {
            Some(TypeExpr::_UnknownNumeric(num_ty)) => {
                Some(TypeExpr::_UnknownNumeric(num_ty.signed()))
            }
            Some(t) if t.is_i() || t.is_f() => Some(t),
            Some(_) | None => None,
        },
        AstNode::Call(callee, _) => match callee.as_ref().inner() {
            &AstNode::Identifier(name) => global.func(name).map(|info| info.sig.ret_type.clone()),
            _ => todo!("Indirect function calling"),
        },
        AstNode::TakeRef(node) => {
            let inner = infer_type(global, local, node.as_ref().inner())?;
            Some(TypeExpr::Ref(Box::new(inner)))
        }
        AstNode::Deref(node) => match infer_type(global, local, node.as_ref().inner())? {
            TypeExpr::Ref(t) | TypeExpr::Ptr(t) => Some(t.as_ref().clone()),
            _ => None,
        },
        AstNode::Block(_) => todo!("type infer for block"),
        AstNode::If(_) => todo!("type infer for if"),
        AstNode::Loop(_) => todo!("type infer for loop"),
        AstNode::Return(..) | AstNode::Break | AstNode::Continue => Some(TypeExpr::Never),
        AstNode::Typecast(_, ty) => Some(ty.clone()),
        AstNode::Tuple(_) => todo!("type infer for tuple"),
        AstNode::Let(..)
        | AstNode::Assign(..)
        | AstNode::MathOpAssign(..)
        | AstNode::BitOpAssign(..)
        | AstNode::TypeDef(_, _)
        | AstNode::StructDef(_)
        | AstNode::UnionDef(_)
        | AstNode::EnumDef(_)
        | AstNode::FnDef(_) => None,
        // tail is handled specially outside
        AstNode::Tail(_) => unreachable!(),
        // only appears in cooked AST
        AstNode::TypedNumber(..) | AstNode::Variable(..) => unreachable!(),
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
                cook_var(global, local, node_loc, var, expect_ty);
                Some(Cow::Borrowed(local.var_ty(var)?))
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
        &mut AstNode::MathOp(_, _, _) => {
            todo!()
        }
        &mut AstNode::BitOp(_, _, _) => {
            todo!()
        }
        &mut AstNode::BoolOp(_, _, _) => {
            todo!()
        }
        &mut AstNode::Cmp(_, _, _) => {
            todo!()
        }
        AstNode::MemberAccess(_, _) => todo!(),
        AstNode::BitNot(_) => todo!(),
        AstNode::BoolNot(_) => todo!(),
        &mut AstNode::UnarySub(node) => match infer_type(global, local, node.as_ref().inner()) {
            Some(t) if t.is_u() => {
                ErrorContent::MismatchdTypes(
                    TypeExpr::_UnknownNumeric(NumericType::default().int().signed()),
                    t.clone(),
                )
                .wrap(node.as_ref().src_loc())
                .collect_into(&global.err_collector);
                None
            }
            Some(t) if t.is_numeric() || matches!(t, TypeExpr::_UnknownNumeric(..)) => {
                cook_expr(global, local, node, expect_ty)
            }
            Some(t) => {
                ErrorContent::MismatchdTypes(
                    TypeExpr::_UnknownNumeric(NumericType::default()),
                    t.clone(),
                )
                .wrap(node.as_ref().src_loc())
                .collect_into(&global.err_collector);
                None
            }
            None => {
                ErrorContent::MismatchdTypes(
                    TypeExpr::_UnknownNumeric(NumericType::default()),
                    TypeExpr::_Unknown,
                )
                .wrap(node.as_ref().src_loc())
                .collect_into(&global.err_collector);
                None
            }
        },
        AstNode::UnaryAdd(_) => todo!(),
        AstNode::Call(callee, args) => {
            cook_call(global, local, expect_ty, *callee, &args, node_loc)
        }
        AstNode::Let(lhs, ty, rhs) => cook_let(global, local, *lhs, ty.as_ref(), *rhs),
        &mut AstNode::Assign(lhs, rhs) => {
            let expect_ty = cook_assign_lhs(global, local, lhs);
            cook_expr(global, local, rhs, &expect_ty)
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

fn cook_var(
    global: &GlobalContext,
    local: &mut LocalContext,
    loc: SourceLocation,
    var: Variable,
    expect_ty: &TypeExpr,
) {
    let var_ty = local.var_ty(var).unwrap();
    if !type_matches(global, expect_ty, var_ty) {
        ErrorContent::MismatchdTypes(expect_ty.clone(), var_ty.clone())
            .wrap(loc)
            .collect_into(&global.err_collector);
    }
    // try to collapse the variable to a concrete type if needed
    match var_ty {
        TypeExpr::_Unknown | TypeExpr::_UnknownNumeric(..) => {
            *local.var_ty_mut(var).unwrap() = expect_ty.clone()
        }
        _ => (),
    }
}

/// If a variable is of unconcrete type, try to collase it, provided that the type already matches
fn try_collapse_var_ty(local: &mut LocalContext, node: &AstNode, expect_ty: &TypeExpr) {
    match node {
        &AstNode::Variable(var) => {
            let var_ty = local.var_ty(var).unwrap();
            match var_ty {
                TypeExpr::_Unknown | TypeExpr::_UnknownNumeric(..) => {
                    *local.var_ty_mut(var).unwrap() = expect_ty.clone()
                }
                _ => (),
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
        TypeExpr::_UnknownNumeric(..) | TypeExpr::_Unknown => {
            return None;
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
    let infered_type: TypeExpr;
    let ty = match ty {
        Some(t) => t,
        None => {
            infered_type = infer_type(
                global,
                local,
                rhs.ok_or(ErrorContent::LetNoTypeOrRHS.wrap(lhs.as_ref().src_loc()))
                    .collect_err(&global.err_collector)?
                    .as_ref()
                    .inner(),
            )
            .unwrap_or(TypeExpr::_Unknown);
            &infered_type
        }
    };
    let ty = cook_let_lhs(global, local, lhs, ty.clone())?;
    if let Some(rhs) = rhs {
        cook_expr(global, local, rhs, &ty);
    }
    Some(ty)
}

fn cook_let_lhs<'l, 'g: 'l>(
    global: &GlobalContext,
    local: &mut LocalContext,
    mut node: AstNodeRef,
    ty: TypeExpr,
) -> Option<Cow<'l, TypeExpr>> {
    let node = node.as_mut();
    let loc = node.src_loc();
    match node.inner_mut() {
        &mut AstNode::Identifier(name) => {
            let var = local.add_var(name, ty);
            *node.inner_mut() = AstNode::Variable(var);
            Some(Cow::Owned(TypeExpr::_Unknown))
        }
        AstNode::Tuple(_) => todo!(),
        _ => {
            ErrorContent::InvalidLetLHS
                .wrap(loc)
                .collect_into(&global.err_collector);
            None
        }
    }
}

/// Returns the expected type for the rhs
fn cook_assign_lhs(global: &GlobalContext, local: &LocalContext, mut node: AstNodeRef) -> TypeExpr {
    let node = node.as_mut();
    let loc = node.src_loc();
    match node.inner_mut() {
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
    }
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
