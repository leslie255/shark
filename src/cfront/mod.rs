#![allow(dead_code)]

mod scan;

use std::{
    hash::{Hash, Hasher},
    io::{self, Write},
};

use crate::{
    ast::{parser::AstParser, type_expr::TypeExpr, AstNode, AstNodeRef, FnDef, StructOrUnionDef},
    token::NumValue,
};

use self::scan::Context;

#[inline]
#[must_use]
fn is_c_keyword(s: &str) -> bool {
    match s {
        "auto" | "double" | "int" | "struct" | "break" | "else" | "long" | "switch" | "case"
        | "enum" | "register" | "typedef" | "char" | "extern" | "return" | "union" | "continue"
        | "for" | "signed" | "void" | "do" | "if" | "static" | "while" | "default" | "goto"
        | "sizeof" | "volatile" | "const" | "float" | "short" | "unsigned" => true,
        s if s.chars().next().expect("empty identifier string") == '_' => true,
        _ => false,
    }
}

#[inline]
#[must_use]
fn quick_hash_str(s: &str) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    s.chars().for_each(|c| c.hash(&mut hasher));
    hasher.finish()
}

pub(self) fn codegen_ty(context: &mut Context<impl Write, impl Write>, ty: &TypeExpr<'_>) -> io::Result<()> {
    match ty {
        TypeExpr::USize => write!(context.c_file, "size_t"),
        TypeExpr::ISize => write!(context.c_file, "ssize_t"),
        TypeExpr::U128 => todo!("u128 type"),
        TypeExpr::U64 => write!(context.c_file, "uint64_t"),
        TypeExpr::U32 => write!(context.c_file, "uint32_t"),
        TypeExpr::U16 => write!(context.c_file, "uint16_t"),
        TypeExpr::U8 => write!(context.c_file, "uint8_t"),
        TypeExpr::I128 => todo!("i128 type"),
        TypeExpr::I64 => write!(context.c_file, "int64_t"),
        TypeExpr::I32 => write!(context.c_file, "int32_t"),
        TypeExpr::I16 => write!(context.c_file, "int16_t"),
        TypeExpr::I8 => write!(context.c_file, "int8_t"),
        TypeExpr::F64 => write!(context.c_file, "double"),
        TypeExpr::F32 => write!(context.c_file, "float"),
        TypeExpr::Char => write!(context.c_file, "uint32_t"),
        TypeExpr::Bool => write!(context.c_file, "uint8_t"),
        TypeExpr::Ptr(ty) | TypeExpr::Ref(ty) => {
            codegen_ty(context, ty.as_ref())?;
            write!(context.c_file, "*")
        }
        TypeExpr::Slice(_) => todo!("slice type"),
        TypeExpr::Array(..) => todo!("array type"),
        TypeExpr::Tuple(fields) if fields.is_empty() => write!(context.c_file, "void"),
        TypeExpr::Tuple(_) => todo!("tuple type"),
        TypeExpr::Fn(_, _) => todo!("function pointer type"),
        TypeExpr::TypeName(id) => codegen_id(context, id),
        TypeExpr::Struct => todo!("struct"),
        TypeExpr::Union => todo!("union"),
        TypeExpr::Enum => todo!("enum"),
    }
}

#[inline]
fn codegen_id(context: &mut Context<impl Write, impl Write>, id: &str) -> io::Result<()> {
    if is_c_keyword(id) {
        write!(context.c_file, "ID_{}___{}_", id, quick_hash_str(id))
    } else {
        write!(context.c_file, "{}", id)
    }
}

#[inline]
fn codegen_num(context: &mut Context<impl Write, impl Write>, num: NumValue) -> io::Result<()> {
    write!(context.c_file, "{:?}", num)
}

#[inline]
fn codegen_bool(context: &mut Context<impl Write, impl Write>, val: bool) -> io::Result<()> {
    write!(context.c_file, "{}", if val { 1 } else { 0 })
}

#[inline]
fn codegen_char(context: &mut Context<impl Write, impl Write>, val: char) -> io::Result<()> {
    write!(context.c_file, "{}", u32::from(val))
}

#[inline]
fn codegen_let<'s>(
    context: &mut Context<impl Write, impl Write>,
    lhs: &'s str,
    ty: Option<&TypeExpr<'s>>,
    rhs: Option<AstNodeRef<'s>>,
) -> io::Result<()> {
    let ty = ty.expect("type infer is unimplemented");
    codegen_ty(context, ty)?;
    write!(context.c_file, " ")?;
    codegen_id(context, lhs)?;
    if let Some(rhs_node) = rhs.map(|n| n.as_ref().inner()) {
        write!(context.c_file, " = ")?;
        codegen_node(context, rhs_node)?;
    } else {
    }
    Ok(())
}

#[inline]
fn codegen_fn_def<'s>(
    context: &mut Context<impl Write, impl Write>,
    fn_def: &FnDef<'s>,
) -> io::Result<()> {
    codegen_ty(context, &fn_def.sign.ret_type)?;
    write!(context.c_file, " ")?;
    codegen_id(context, fn_def.name)?;
    write!(context.c_file, "(")?;
    for (i, (arg_name, arg_ty)) in fn_def.sign.args.iter().enumerate() {
        codegen_ty(context, arg_ty)?;
        write!(context.c_file, " ")?;
        codegen_id(context, *arg_name)?;
        if i < fn_def.sign.args.len() - 1 {
            write!(context.c_file, ",")?;
        }
    }
    write!(context.c_file, ")")?;
    match fn_def.body {
        Some(ref body) => {
            write!(context.c_file, "{{")?;
            for n in body {
                codegen_node(context, n.as_ref().inner())?;
                write!(context.c_file, ";")?;
            }
            write!(context.c_file, "}}")?;
        }
        None => write!(context.c_file, ";")?,
    }
    Ok(())
}

#[inline]
fn codegen_ret<'s>(
    context: &mut Context<impl Write, impl Write>,
    child: Option<AstNodeRef<'_>>,
) -> io::Result<()> {
    write!(context.c_file, "return ")?;
    match child {
        Some(child) => codegen_node(context, child.as_ref().inner())?,
        None => (),
    }
    Ok(())
}

#[inline]
fn codegen_call(
    context: &mut Context<impl Write, impl Write>,
    callee: &AstNode,
    args: &Vec<AstNodeRef>,
) -> io::Result<()> {
    codegen_node(context, callee)?;
    write!(context.c_file, "(")?;
    for (i, arg_node) in args.iter().enumerate() {
        codegen_node(context, arg_node.as_ref().inner())?;
        if i < args.len() - 1 {
            write!(context.c_file, ",")?;
        }
    }
    write!(context.c_file, ")")?;
    Ok(())
}

#[inline]
fn codegen_str(context: &mut Context<impl Write, impl Write>, s: *const str) -> io::Result<()> {
    write!(context.c_file, "{:?}", unsafe { s.as_ref().unwrap() })
}

/// Because `struct` and `union` definition syntax are so similar in C, this function is in charge
/// of generation `NAME {field0:ty0;field1:ty1; ... }` right after the `struct` or `union` keyword
#[inline]
fn codegen_struct_union_name_and_body(
    context: &mut Context<impl Write, impl Write>,
    def: &StructOrUnionDef,
) -> io::Result<()> {
    codegen_id(context, def.name)?;
    write!(context.c_file, "{{")?;
    for (id, ty) in &def.fields {
        codegen_ty(context, ty)?;
        write!(context.c_file, " ")?;
        codegen_id(context, id)?;
        write!(context.c_file, ";")?;
    }
    write!(context.c_file, "}}")?;
    codegen_id(context, def.name)?;
    write!(context.c_file, ";")?;
    Ok(())
}

#[inline]
fn codegen_struct_def(
    context: &mut Context<impl Write, impl Write>,
    def: &StructOrUnionDef,
) -> io::Result<()> {
    write!(context.c_file, "typedef struct ")?;
    codegen_struct_union_name_and_body(context, def)
}

#[inline]
fn codegen_union_def(
    context: &mut Context<impl Write, impl Write>,
    def: &StructOrUnionDef,
) -> io::Result<()> {
    write!(context.c_file, "typedef union ")?;
    codegen_struct_union_name_and_body(context, def)
}

#[inline]
fn codegen_typedef(
    context: &mut Context<impl Write, impl Write>,
    id: &str,
    ty: &TypeExpr,
) -> io::Result<()> {
    write!(context.c_file, "typedef ")?;
    codegen_ty(context, ty)?;
    write!(context.c_file, " ")?;
    codegen_id(context, id)?;
    write!(context.c_file, ";")?;
    Ok(())
}

fn codegen_node<C: Write, H: Write>(context: &mut Context<C, H>, node: &AstNode) -> io::Result<()> {
    match node {
        AstNode::Let(lhs, ty, rhs) => codegen_let(context, *lhs, ty.as_ref(), *rhs),
        AstNode::FnDef(fn_def) => codegen_fn_def(context, fn_def),
        AstNode::TypeDef(id, ty) => codegen_typedef(context, id, ty),
        AstNode::StructDef(def) => codegen_struct_def(context, def),
        AstNode::UnionDef(def) => codegen_union_def(context, def),
        AstNode::EnumDef(_) => todo!(),
        AstNode::Identifier(id) => codegen_id(context, *id),
        AstNode::Number(num) => codegen_num(context, *num),
        AstNode::String(s) => codegen_str(context, *s),
        AstNode::Char(val) => codegen_char(context, *val),
        AstNode::Bool(val) => codegen_bool(context, *val),
        AstNode::Array(_) => todo!(),
        AstNode::MathOp(_, _, _) => todo!(),
        AstNode::BitOp(_, _, _) => todo!(),
        AstNode::BoolOp(_, _, _) => todo!(),
        AstNode::Cmp(_, _, _) => todo!(),
        AstNode::MemberAccess(_, _) => todo!(),
        AstNode::BitNot(_) => todo!(),
        AstNode::BoolNot(_) => todo!(),
        AstNode::MinusNum(_) => todo!(),
        AstNode::PlusNum(_) => todo!(),
        AstNode::Call(callee, args) => codegen_call(context, callee, args),
        AstNode::Assign(_, _) => todo!(),
        AstNode::MathOpAssign(_, _, _) => todo!(),
        AstNode::BitOpAssign(_, _, _) => todo!(),
        AstNode::TakeRef(_) => todo!(),
        AstNode::Deref(_) => todo!(),
        AstNode::Block(_) => todo!(),
        AstNode::If(_) => todo!(),
        AstNode::Loop(_) => todo!(),
        AstNode::Return(child) => codegen_ret(context, *child),
        AstNode::Break => write!(context.c_file, "break"),
        AstNode::Continue => write!(context.c_file, "continue"),
        AstNode::Typecast(_, _) => todo!(),
        AstNode::Tuple(_) => unreachable!(),
    }
}

pub fn gen_c_code(mut target_c: impl Write, target_h: impl Write, ast_parser: AstParser<'_>) {
    write!(target_c, "#include\"common.h\"\n").expect("write error when writing to files");
    let (mut context, ast) = scan::scan(target_c, target_h, ast_parser);
    for root_node in &ast.root_nodes {
        codegen_node(&mut context, root_node.as_ref().inner())
            .expect("write error when writing to files");
    }
}
