use crate::{
    ast::{type_expr::TypeExpr, Ast, AstNode, AstNodeRef, CookedAst, Function, VarTable, Variable},
    error::{
        location::{SourceLocation, Traced},
        ErrorContent,
    },
    token::NumValue,
};

use super::{clif_types, ClifType, GlobalContext};

#[must_use]
pub fn type_matches(global: &GlobalContext, expect: &TypeExpr, found: &TypeExpr) -> bool {
    use TypeExpr::*;
    match (expect, found) {
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
            for (lhs, rhs) in lhs.iter().zip(rhs.iter()) {
                if !type_matches(global, lhs, rhs) {
                    return false;
                }
            }
            true
        }
        (Fn(l_args, l_ret), Fn(r_args, r_ret)) => {
            // TODO: counter-variance logic
            for (lhs, rhs) in l_args.iter().zip(r_args.iter()) {
                if lhs != rhs {
                    return false;
                }
            }
            l_ret == r_ret
        }
        (TypeName(..), TypeName(..)) => todo!(),
        (TypeName(..), _) => todo!(),
        (_, TypeName(..)) => todo!(),
        (lhs, _Numeric) => lhs.is_u() || lhs.is_i() || lhs.is_f(),
        (lhs, _Int) => lhs.is_u() || lhs.is_i(),
        (lhs, _SInt) => lhs.is_i(),
        (lhs, _Float) => lhs.is_f(),
        _ => false,
    }
}

#[allow(unused_variables)]
/// Type check and AST and attack type informations to it, making a `CookedAst`
pub fn cook_ast(global: &GlobalContext, mut ast: Ast) -> CookedAst {
    for root_node in ast.root_nodes.iter_mut() {
        let root_node = root_node.as_mut();
        match root_node.inner_mut() {
            AstNode::FnDef(ref mut func) => typecheck_func(global, func),
            _ => (), // already reported error in `build_global_context`
        }
    }
    CookedAst(ast)
}

fn typecheck_func(global: &GlobalContext, func: &mut Function) {
    let var_table = &mut func.var_table;
    for (arg_name, arg_ty) in func.sign.args.iter() {
        var_table.add_var(&arg_name, arg_ty.clone());
    }
    let body: &mut [AstNodeRef] = match func.body {
        Some(ref mut x) => x,
        None => return,
    };
    for node_ref in body.iter() {
        let node = node_ref.as_ref().inner();
        match node {
            &AstNode::Tail(node) => typecheck_expr(global, var_table, node, &func.sign.ret_type),
            _ => typecheck_expr(global, var_table, *node_ref, &TypeExpr::_Unknown),
        }
    }
}

fn typecheck_expr(
    global: &GlobalContext,
    var_table: &mut VarTable,
    mut node: AstNodeRef,
    expect_ty: &TypeExpr,
) {
    let node = node.as_mut();
    let node_loc = node.src_loc();
    let node = node.inner_mut();
    match node {
        AstNode::Identifier(var_name) => match var_table.var_id(var_name) {
            Some(var) => {
                *node = AstNode::Variable(var);
                typecheck_var(global, var_table, node_loc, var, expect_ty);
            }
            None => ErrorContent::UndefinedVar(&var_name)
                .wrap(node_loc)
                .collect_into(&global.err_collector),
        },
        AstNode::Number(num_val) => *node = make_typed_num(global, node_loc, expect_ty, *num_val),
        AstNode::String(..) => todo!(),
        AstNode::Char(..) => {
            if !type_matches(global, expect_ty, &TypeExpr::Char) {
                ErrorContent::MismatchdTypes(expect_ty.clone(), TypeExpr::Char)
                    .wrap(node_loc)
                    .collect_into(&global.err_collector)
            }
        }
        AstNode::Bool(..) => {
            if !type_matches(global, expect_ty, &TypeExpr::Bool) {
                ErrorContent::MismatchdTypes(expect_ty.clone(), TypeExpr::Bool)
                    .wrap(node_loc)
                    .collect_into(&global.err_collector)
            }
        }
        AstNode::Array(_) => todo!(),
        AstNode::MathOp(_, _, _) => todo!(),
        AstNode::BitOp(_, _, _) => todo!(),
        AstNode::BoolOp(_, _, _) => todo!(),
        AstNode::Cmp(_, _, _) => todo!(),
        AstNode::MemberAccess(_, _) => todo!(),
        AstNode::BitNot(_) => todo!(),
        AstNode::BoolNot(_) => todo!(),
        AstNode::UnarySub(_) => todo!(),
        AstNode::UnaryAdd(_) => todo!(),
        AstNode::Call(_, _) => todo!(),
        AstNode::Let(lhs, ty, rhs) => cook_let(global, var_table, *lhs, ty.as_ref(), *rhs),
        AstNode::Assign(_, _) => todo!(),
        AstNode::MathOpAssign(_, _, _) => todo!(),
        AstNode::BitOpAssign(_, _, _) => todo!(),
        AstNode::TakeRef(_) => todo!(),
        AstNode::Deref(_) => todo!(),
        AstNode::Block(_) => todo!(),
        AstNode::FnDef(_) => todo!(),
        AstNode::If(_) => todo!(),
        AstNode::Loop(_) => todo!(),
        // never type matches all types, there is no need to check
        AstNode::Break | AstNode::Continue | AstNode::Return(..) => (),
        AstNode::Typecast(_, _) => todo!(),
        AstNode::TypeDef(_, _) => todo!(),
        AstNode::StructDef(_) => todo!(),
        AstNode::UnionDef(_) => todo!(),
        AstNode::EnumDef(_) => todo!(),
        AstNode::Tuple(_) => todo!(),
        AstNode::TypedNumber(..) | AstNode::Variable(..) | AstNode::Tail(..) => unreachable!(),
    }
}

fn typecheck_var(
    global: &GlobalContext,
    var_table: &mut VarTable,
    loc: SourceLocation,
    var: Variable,
    expect_ty: &TypeExpr,
) {
    let var_ty = var_table.var_ty(var).unwrap();
    if !type_matches(global, var_ty, expect_ty) {
        let var_name = var_table.var_name(var).unwrap();
        ErrorContent::UndefinedVar(var_name)
            .wrap(loc)
            .collect_into(&global.err_collector);
    }
}

fn make_typed_num(
    global: &GlobalContext,
    loc: SourceLocation,
    expect_ty: &TypeExpr,
    num_val: NumValue,
) -> AstNode {
    let ty = match expect_ty {
        TypeExpr::_Numeric if num_val.is_int() => clif_types::I64,
        TypeExpr::_Numeric if num_val.is_f() => clif_types::F64,
        TypeExpr::_Int | TypeExpr::_SInt => clif_types::I64,
        TypeExpr::USize | TypeExpr::ISize => clif_types::I64,
        TypeExpr::U64 | TypeExpr::I64 => clif_types::I64,
        TypeExpr::U32 | TypeExpr::I32 => clif_types::I32,
        TypeExpr::U16 | TypeExpr::I16 => clif_types::I16,
        TypeExpr::U8 | TypeExpr::I8 => clif_types::I8,
        TypeExpr::F64 => clif_types::F64,
        TypeExpr::F32 => clif_types::F32,
        TypeExpr::_Unknown => match num_val {
            // TODO: range checking
            NumValue::U(..) => clif_types::I64,
            NumValue::I(..) => clif_types::I64,
            NumValue::F(..) => clif_types::F64,
        },
        ty => {
            ErrorContent::MismatchdTypes(TypeExpr::_Numeric, ty.clone())
                .wrap(loc)
                .collect_into(&global.err_collector);
            return AstNode::TypedNumber(clif_types::INVALID, num_val);
        }
    };
    AstNode::TypedNumber(ty, num_val)
}

fn cook_let(
    global: &GlobalContext,
    var_table: &mut VarTable,
    lhs: AstNodeRef,
    ty: Option<&TypeExpr>,
    rhs: Option<AstNodeRef>,
) {
    let ty = ty.expect("TODO: type infer");
    cook_let_lhs(global, var_table, lhs, ty.clone());
    if let Some(rhs) = rhs {
        typecheck_expr(global, var_table, rhs, ty);
    }
}

fn cook_let_lhs(
    global: &GlobalContext,
    var_table: &mut VarTable,
    mut node: AstNodeRef,
    ty: TypeExpr,
) {
    let node = node.as_mut();
    let loc = node.src_loc();
    match node.inner_mut() {
        &mut AstNode::Identifier(name) => {
            let var = var_table.add_var(name, ty);
            *node = AstNode::Variable(var).traced(loc);
        }
        AstNode::Tuple(_) => todo!(),
        _ => ErrorContent::InvalidLetLHS
            .wrap(loc)
            .collect_into(&global.err_collector),
    }
}
