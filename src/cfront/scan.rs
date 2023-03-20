#![allow(unused)]
use std::{
    collections::{hash_map::RawEntryMut, HashMap},
    hash::{Hash, Hasher},
    io::{self, Write},
};

use crate::ast::{parser::AstParser, type_expr::TypeExpr, Ast, AstNode};

/// Keep track of expanded generics
/// Currently shark doesn't have custom generic expansions yet, so it is only used by arrays and
/// tuples
#[derive(Debug, Clone, Default)]
pub struct GenericExpansions<'s> {
    pub arrs: HashMap<(u64, TypeExpr<'s>), u64>,
    pub slices: HashMap<TypeExpr<'s>, u64>,
}

#[derive(Debug)]
pub struct Context<'s, C: Write, H: Write> {
    pub c_file: C,
    pub h_file: H,
    pub generics: GenericExpansions<'s>,
}

fn quick_hash<T: Hash>(x: &T) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    x.hash(&mut hasher);
    hasher.finish()
}

impl<'s, C: Write, H: Write> Context<'s, C, H> {
    fn add_arr_if_needed(&mut self, size_ty: &(u64, TypeExpr)) {
        todo!()
    }

    fn add_slice_if_needed(&mut self, ty: &TypeExpr<'s>) {
        gen_typedef_if_needed(self, ty);
        let id = self.generics.slices.len() as u64;
        match self.generics.slices.raw_entry_mut().from_key(ty) {
            RawEntryMut::Occupied(_) => (),
            RawEntryMut::Vacant(entry) => {
                entry.insert(ty.clone(), id);
            }
        };
    }

    fn add_tuple_if_needed(&mut self, size_ty: &(u64, TypeExpr)) {
        todo!()
    }
}

fn gen_typedef_if_needed<'s>(
    context: &mut Context<'s, impl Write, impl Write>,
    ty: &TypeExpr<'s>,
) -> io::Result<()> {
    match ty {
        TypeExpr::Slice(ty) => context.add_slice_if_needed(ty.as_ref()),
        TypeExpr::Array(_) => todo!(),
        TypeExpr::Tuple(x) if x.is_empty() => (),
        TypeExpr::Tuple(_) => todo!(),
        TypeExpr::Fn(_, _) => todo!(),
        TypeExpr::TypeName(_) => (),
        TypeExpr::Struct => todo!(),
        TypeExpr::Union => todo!(),
        TypeExpr::Enum => todo!(),
        TypeExpr::USize
        | TypeExpr::ISize
        | TypeExpr::U128
        | TypeExpr::U64
        | TypeExpr::U32
        | TypeExpr::U16
        | TypeExpr::U8
        | TypeExpr::I128
        | TypeExpr::I64
        | TypeExpr::I32
        | TypeExpr::I16
        | TypeExpr::I8
        | TypeExpr::F64
        | TypeExpr::F32
        | TypeExpr::Char
        | TypeExpr::Bool
        | TypeExpr::Ptr(_)
        | TypeExpr::Ref(_) => (),
    }
    Ok(())
}

fn scan_node<'s>(
    context: &mut Context<'s, impl Write, impl Write>,
    node: &AstNode<'s>,
) -> io::Result<()> {
    match node {
        AstNode::Let(_, ty, rhs) => {
            ty.as_ref()
                .map(|ty| gen_typedef_if_needed(context, ty).unwrap());
            rhs.as_ref()
                .map(|nr| scan_node(context, nr.as_ref().inner()).unwrap());
        }
        AstNode::FnDef(fn_def) => {
            fn_def
                .sign
                .args
                .iter()
                .find_map(|(_, ty)| gen_typedef_if_needed(context, ty).err())
                .map_or(Ok(()), |e| Err(e))?;
            gen_typedef_if_needed(context, &fn_def.sign.ret_type)?;
        }
        AstNode::TypeDef(_, ty) => gen_typedef_if_needed(context, ty)?,
        AstNode::StructDef(def) => def
            .fields
            .iter()
            .find_map(|(_, ty)| gen_typedef_if_needed(context, ty).err())
            .map_or(Ok(()), |e| Err(e))?,
        AstNode::UnionDef(def) => def
            .fields
            .iter()
            .find_map(|(_, ty)| gen_typedef_if_needed(context, ty).err())
            .map_or(Ok(()), |e| Err(e))?,
        AstNode::Array(children) => children
            .iter()
            .find_map(|nr| scan_node(context, &nr).err())
            .map_or(Ok(()), |e| Err(e))?,
        AstNode::MathOp(_, lhs, rhs)
        | AstNode::BitOp(_, lhs, rhs)
        | AstNode::BoolOp(_, lhs, rhs)
        | AstNode::Cmp(_, lhs, rhs) => {
            scan_node(context, &lhs)?;
            scan_node(context, &rhs)?;
        }
        AstNode::BitNot(child) | AstNode::BoolNot(child) => scan_node(context, &child)?,
        AstNode::MinusNum(_) => todo!(),
        AstNode::PlusNum(_) => todo!(),
        AstNode::Call(_, _) => todo!(),
        AstNode::Assign(_, _) => todo!(),
        AstNode::MathOpAssign(_, _, _) => todo!(),
        AstNode::BitOpAssign(_, _, _) => todo!(),
        AstNode::TakeRef(_) => todo!(),
        AstNode::Deref(_) => todo!(),
        AstNode::Block(_) => todo!(),
        AstNode::If(_) => todo!(),
        AstNode::Loop(_) => todo!(),
        AstNode::Return(Some(child)) => todo!(),
        AstNode::Typecast(_, _) => todo!(),
        AstNode::Tuple(_) => todo!(),
        AstNode::MemberAccess(..)
        | AstNode::EnumDef(..)
        | AstNode::Identifier(..)
        | AstNode::Number(..)
        | AstNode::String(..)
        | AstNode::Char(..)
        | AstNode::Bool(..)
        | AstNode::Return(None)
        | AstNode::Break
        | AstNode::Continue => (),
    }
    Ok(())
}

/// Scans throught the AST to generate definitions for non-native C types, such as tuples and
/// slices.
/// Also builds a `HashMap` of typenames for the generated objects.
pub fn scan<'s>(
    target_c: impl Write,
    target_h: impl Write,
    mut ast_parser: AstParser<'s>,
) -> (Context<impl Write, impl Write>, Ast<'s>) {
    let mut context = Context {
        c_file: target_c,
        h_file: target_h,
        generics: GenericExpansions::default(),
    };
    for root_node in ast_parser.iter() {
        scan_node(&mut context, &root_node).expect("write error");
    }

    (context, ast_parser.ast)
}
