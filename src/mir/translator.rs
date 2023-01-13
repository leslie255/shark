#![allow(dead_code, unused_imports, unused_mut, unused_variables)]
use std::{collections::HashMap, ops::Deref};

use crate::{
    ast::{type_expr::TypeExpr, Ast, AstNode, FnDef},
    checks::symboltable::{PossibleTypes, SymbolTable},
};

use super::{cl_types, ClType, MirBlock, MirFnDef, MirNode, MirNodeRef, MirProgram, MirVarInfo};

pub(super) fn basic_asttype_to_cltype<'s>(node: &TypeExpr<'s>) -> Option<ClType> {
    use TypeExpr::*;
    match node {
        U128 | I128 => Some(cl_types::I128),
        USize | ISize | U64 | I64 => Some(cl_types::I64),
        U32 | I32 | Char => Some(cl_types::I32),
        U16 | I16 => Some(cl_types::I16),
        U8 | I8 | Bool => Some(cl_types::I8),
        F64 => Some(cl_types::F64),
        F32 => Some(cl_types::F32),
        Ptr(_) | Ref(_) => Some(cl_types::R64),
        Array(1, t) => basic_asttype_to_cltype(t),
        Array(2, t) => basic_asttype_to_cltype(t).map_or(None, |t| match t {
            cl_types::I32 => Some(cl_types::I32X2),
            cl_types::I64 => Some(cl_types::I64X2),
            cl_types::I128 => Some(cl_types::I128X2),
            cl_types::F32 => Some(cl_types::F32X2),
            cl_types::F64 => Some(cl_types::F64X2),
            _ => None,
        }),
        Array(4, t) => basic_asttype_to_cltype(t).map_or(None, |t| match t {
            cl_types::I16 => Some(cl_types::I16X4),
            cl_types::I32 => Some(cl_types::I32X4),
            cl_types::I64 => Some(cl_types::I64X4),
            cl_types::I128 => Some(cl_types::I128X4),
            cl_types::F32 => Some(cl_types::F32X4),
            cl_types::F64 => Some(cl_types::F64X4),
            _ => None,
        }),
        Array(8, t) => basic_asttype_to_cltype(t).map_or(None, |t| match t {
            cl_types::I8 => Some(cl_types::I8X8),
            cl_types::I16 => Some(cl_types::I16X8),
            cl_types::I32 => Some(cl_types::I32X8),
            cl_types::I64 => Some(cl_types::I64X8),
            cl_types::F32 => Some(cl_types::F32X8),
            cl_types::F64 => Some(cl_types::F64X8),
            _ => None,
        }),
        Array(16, t) => basic_asttype_to_cltype(t).map_or(None, |t| match t {
            cl_types::I8 => Some(cl_types::I8X16),
            cl_types::I16 => Some(cl_types::I16X16),
            cl_types::I32 => Some(cl_types::I32X16),
            cl_types::F32 => Some(cl_types::F32X16),
            _ => None,
        }),
        Array(32, t) => basic_asttype_to_cltype(t).map_or(None, |t| match t {
            cl_types::I8 => Some(cl_types::I8X32),
            cl_types::I16 => Some(cl_types::I16X32),
            _ => None,
        }),
        Array(64, t) => basic_asttype_to_cltype(t).map_or(None, |t| match t {
            cl_types::I8 => Some(cl_types::I8X64),
            _ => None,
        }),
        Slice(_) | Array(_, _) | Tuple(_) | Fn(_, _) | TypeName(_) | Struct | Union | Enum => None,
    }
}

pub(super) static TUPLE_PATHS: [&'static str; 32] = [
    "_0", "_1", "_2", "_3", "_4", "_5", "_6", "_7", "_8", "_9", "_10", "_11", "_12", "_13", "_14",
    "_15", "_16", "_17", "_18", "_19", "_20", "_21", "_22", "_23", "_24", "_25", "_26", "_27",
    "_28", "_29", "_30", "_31",
];

fn flatten_type<'s>(name: &'s str, ty: &TypeExpr<'s>, mut f: impl FnMut(&Vec<&'s str>, ClType)) {
    if ty.is_void() {
        return;
    }
    let mut path = vec![name];
    fn recursive<'s>(
        path: &mut Vec<&'s str>,
        ty: &TypeExpr<'s>,
        f: &mut impl FnMut(&Vec<&'s str>, ClType),
    ) {
        if ty.is_void() {
            return;
        }
        if let Some(cl_ty) = basic_asttype_to_cltype(&ty) {
            f(&path, cl_ty);
            return;
        }
        match ty {
            TypeExpr::Slice(_) => {
                path.push("size");
                f(path, cl_types::I64);
                path.pop();
                f(path, cl_types::R64);
            }
            TypeExpr::Array(_, _) => todo!("freeform array"),
            TypeExpr::Tuple(children) => {
                if children.len() > 32 {
                    todo!("tuple with more than 32 children");
                }
                children
                    .iter()
                    .zip(TUPLE_PATHS)
                    .for_each(|(child, sub_path)| {
                        path.push(sub_path);
                        recursive(path, child, f);
                        path.pop();
                    })
            }
            TypeExpr::Fn(_, _) => todo!(),
            TypeExpr::TypeName(_) => todo!(),
            TypeExpr::Struct => todo!(),
            TypeExpr::Union => todo!(),
            TypeExpr::Enum => todo!(),
            _ => unimplemented!(), // covered by `basic_asttype_to_cltype`
        }
    }

    if let Some(cl_ty) = basic_asttype_to_cltype(ty) {
        f(&path, cl_ty);
    } else {
        recursive(&mut path, ty, &mut f);
    }
}

#[cfg(test)]
#[test]
fn test_flatten_ty() {
    fn test_case<'s>(t: &TypeExpr<'s>, name: &'s str) -> (Vec<Vec<&'s str>>, Vec<ClType>) {
        let mut paths = Vec::<Vec<&'static str>>::new();
        let mut flattened = Vec::<ClType>::new();
        flatten_type(name, &t, |path, ty| {
            paths.push(path.clone());
            flattened.push(ty);
        });
        (paths, flattened)
    }
    let (paths, flattened) = test_case(&TypeExpr::U128, "test_var");
    assert_eq!(paths, vec![vec!["test_var"]]);
    assert_eq!(flattened, vec![cl_types::I128]);

    let (paths, flattened) = test_case(
        &TypeExpr::Tuple(vec![TypeExpr::U64, TypeExpr::Ptr(Box::new(TypeExpr::U8))]),
        "test_var",
    );
    assert_eq!(paths, vec![vec!["test_var", "_0"], vec!["test_var", "_1"]]);
    assert_eq!(flattened, vec![cl_types::I64, cl_types::R64]);

    let (paths, flattened) = test_case(&TypeExpr::Slice(Box::new(TypeExpr::U8)), "test_var");
    assert_eq!(paths, vec![vec!["test_var", "size"], vec!["test_var"]]);
    assert_eq!(flattened, vec![cl_types::I64, cl_types::R64]);
}

/// convert an AST into a MIR program
///
/// This is the main entry point for the conversion process.
/// It takes an AST and returns a MIR program.
pub fn ast_into_mir<'s>(ast: Ast<'s>) -> MirProgram<'s> {
    let mut mir_program = MirProgram::default();
    let mut symbol_table = SymbolTable::default();
    for n in ast.root_nodes.into_iter() {
        let ast_node = n.inner();
        let mir_node_ref = convert_top_level(&mut mir_program, ast_node, &mut symbol_table);
        mir_program.root_nodes.push(mir_node_ref);
    }
    mir_program
}

pub fn convert_top_level<'s>(
    program: &mut MirProgram<'s>,
    node: &AstNode<'s>,
    symbol_table: &mut SymbolTable<'s>,
) -> MirNodeRef<'s> {
    match node {
        AstNode::FnDef(ast_fn_def) => convert_fn_def(program, ast_fn_def, symbol_table),
        #[allow(unused_variables)]
        AstNode::Let(lhs, dtype, rhs) => {
            todo!("convert static variable `let` into MIR")
        }
        _ => unimplemented!(),
    }
}

fn convert_fn_def<'s>(
    program: &mut MirProgram<'s>,
    ast_fn_def: &FnDef<'s>,
    symbol_table: &mut SymbolTable<'s>,
) -> MirNodeRef<'s> {
    symbol_table.add_fn(ast_fn_def.name, ast_fn_def.sign.clone());
    symbol_table.push_layer();
    let mut context = Context::default();
    let (mut arg_types, mut arg_vars): (Vec<ClType>, HashMap<Vec<&str>, MirVarInfo>) =
        Default::default();
    todo!()
}

fn convert_block_body<'s>(
    node: &AstNode<'s>,
    symbol_table: &mut SymbolTable<'s>,
    program: &mut MirProgram<'s>,
    target: &mut MirBlock<'s>,
    context: &mut Context,
) {
    #[allow(unused_variables)]
    match node {
        AstNode::Call(callee, args) => todo!(),
        AstNode::Let(lhs, ty, rhs) => todo!(),
        AstNode::Assign(lhs, rhs) => todo!(),
        AstNode::MathOpAssign(op_kind, lhs, rhs) => todo!(),
        AstNode::BitOpAssign(op_kind, lhs, rhs) => todo!(),
        AstNode::Block(body) => todo!(),
        AstNode::If(if_expr) => todo!(),
        AstNode::Loop(body) => todo!(),
        AstNode::Return(Some(child)) => todo!(),
        AstNode::Return(None) => todo!(),
        AstNode::Break => todo!(),
        AstNode::Continue => todo!(),
        _ => unimplemented!(),
    }
}

#[allow(unused_variables)]
fn convert_assignment<'s>(
    lhs_path: &Vec<&'s str>,
    rhs: AstNode<'s>,
    target: &mut MirBlock<'s>,
    context: &mut Context,
) {
    todo!()
}

#[allow(dead_code)]
fn flatten_expr<'s, F: FnMut()>(node: &AstNode<'s>, parent_block: &MirBlock<'s>, handler: F) {
    match node {
        &AstNode::Identifier(id) => {}
        AstNode::Number(..) => todo!(),
        AstNode::String(..) => todo!(),
        AstNode::Char(..) => todo!(),
        AstNode::Bool(..) => todo!(),
        AstNode::Array(..) => todo!(),
        AstNode::MathOp(..) => todo!(),
        AstNode::BitOp(..) => todo!(),
        AstNode::BoolOp(..) => todo!(),
        AstNode::Cmp(..) => todo!(),
        AstNode::MemberAccess(..) => todo!(),
        AstNode::BitNot(..) => todo!(),
        AstNode::BoolNot(..) => todo!(),
        AstNode::MinusNum(..) => todo!(),
        AstNode::PlusNum(..) => todo!(),
        AstNode::Call(..) => todo!(),
        AstNode::TakeRef(..) => todo!(),
        AstNode::Deref(..) => todo!(),
        AstNode::Typecast(..) => todo!(),
        AstNode::Tuple(..) => todo!(),
        _ => unimplemented!(),
    }
}

/// Context for converting AST into MIR when inside a function
#[derive(Debug, Clone)]
struct Context {
    last_var_id: Option<u64>,
}

impl Default for Context {
    fn default() -> Self {
        Self { last_var_id: None }
    }
}

impl Context {
    fn suggest_new_var_id(&mut self) -> u64 {
        let var_id = self.last_var_id.map_or(0, |i| i + 1);
        self.last_var_id = Some(var_id);
        var_id
    }
}
