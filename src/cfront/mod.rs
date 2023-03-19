use std::{
    hash::{Hash, Hasher},
    io,
};

use crate::{
    ast::{parser::AstParser, type_expr::TypeExpr, AstNode, AstNodeRef, FnDef},
    token::NumValue,
};

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

fn quick_hash_str(s: &str) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    s.chars().for_each(|c| c.hash(&mut hasher));
    hasher.finish()
}

fn gen_code_for_ty(target: &mut impl io::Write, ty: &TypeExpr<'_>) -> io::Result<()> {
    match ty {
        TypeExpr::USize => write!(target, "size_t"),
        TypeExpr::ISize => write!(target, "ssize_t"),
        TypeExpr::U128 => todo!("u128 type"),
        TypeExpr::U64 => write!(target, "uint64_t"),
        TypeExpr::U32 => write!(target, "uint32_t"),
        TypeExpr::U16 => write!(target, "uint16_t"),
        TypeExpr::U8 => write!(target, "uint8_t"),
        TypeExpr::I128 => todo!("i128 type"),
        TypeExpr::I64 => write!(target, "int64_t"),
        TypeExpr::I32 => write!(target, "int32_t"),
        TypeExpr::I16 => write!(target, "int16_t"),
        TypeExpr::I8 => write!(target, "int8_t"),
        TypeExpr::F64 => write!(target, "double"),
        TypeExpr::F32 => write!(target, "float"),
        TypeExpr::Char => write!(target, "uint32_t"),
        TypeExpr::Bool => write!(target, "uint8_t"),
        TypeExpr::Ptr(ty) => gen_code_for_ty(target, ty.as_ref()),
        TypeExpr::Ref(ty) => gen_code_for_ty(target, ty.as_ref()),
        TypeExpr::Slice(_) => todo!("slice type"),
        TypeExpr::Array(_, _) => todo!("array type"),
        TypeExpr::Tuple(fields) if fields.is_empty() => write!(target, "void"),
        TypeExpr::Tuple(_) => todo!("tuple type"),
        TypeExpr::Fn(_, _) => todo!("function pointer type"),
        TypeExpr::TypeName(_) => todo!("type name type"),
        TypeExpr::Struct => todo!("struct"),
        TypeExpr::Union => todo!("union"),
        TypeExpr::Enum => todo!("enum"),
    }
}

#[inline]
fn gen_code_for_id(target: &mut impl io::Write, id: &str) -> io::Result<()> {
    if is_c_keyword(id) {
        write!(target, "id{}___{}", id, quick_hash_str(id))
    } else {
        write!(target, "{}", id)
    }
}

#[inline]
fn gen_code_for_num(target: &mut impl io::Write, num: NumValue) -> io::Result<()> {
    write!(target, "{:?}", num)
}

#[inline]
fn gen_code_for_bool(target: &mut impl io::Write, val: bool) -> io::Result<()> {
    write!(target, "{}", if val { 1 } else { 0 })
}

#[inline]
fn gen_code_for_char(target: &mut impl io::Write, val: char) -> io::Result<()> {
    write!(target, "{}", u32::from(val))
}

#[inline]
fn gen_code_for_let<'s>(
    target: &mut impl io::Write,
    lhs: &'s str,
    ty: Option<&TypeExpr<'s>>,
    rhs: Option<AstNodeRef<'s>>,
) -> io::Result<()> {
    let ty = ty.expect("type infer is unimplemented");
    gen_code_for_ty(target, ty)?;
    write!(target, " ")?;
    gen_code_for_id(target, lhs)?;
    if let Some(rhs_node) = rhs.map(|n| n.as_ref().inner()) {
        write!(target, " = ")?;
        gen_code_for_node(target, rhs_node)?;
    } else {
    }
    write!(target, ";")?;
    Ok(())
}

#[inline]
fn gen_code_for_fn_def<'s>(target: &mut impl io::Write, fn_def: &FnDef<'s>) -> io::Result<()> {
    gen_code_for_ty(target, &fn_def.sign.ret_type)?;
    write!(target, " ")?;
    gen_code_for_id(target, fn_def.name)?;
    write!(target, "(")?;
    for (i, (arg_name, arg_ty)) in fn_def.sign.args.iter().enumerate() {
        gen_code_for_ty(target, arg_ty)?;
        write!(target, " ")?;
        gen_code_for_id(target, *arg_name)?;
        if i < fn_def.sign.args.len() - 1 {
            write!(target, ",")?;
        }
    }
    write!(target, ")")?;
    match fn_def.body {
        Some(ref body) => {
            write!(target, "{{")?;
            for n in body {
                gen_code_for_node(target, n.as_ref().inner())?;
            }
            write!(target, "}}")?;
        }
        None => write!(target, ";")?,
    }
    Ok(())
}

#[inline]
fn gen_code_for_ret<'s>(
    target: &mut impl io::Write,
    child: Option<AstNodeRef<'_>>,
) -> io::Result<()> {
    write!(target, "return ")?;
    match child {
        Some(child) => gen_code_for_node(target, child.as_ref().inner())?,
        None => (),
    }
    write!(target, ";")?;
    Ok(())
}

fn gen_code_for_node<'s>(target: &mut impl io::Write, node: &AstNode) -> io::Result<()> {
    match node {
        AstNode::Let(lhs, ty, rhs) => gen_code_for_let(target, *lhs, ty.as_ref(), *rhs),
        AstNode::FnDef(fn_def) => gen_code_for_fn_def(target, fn_def),
        AstNode::TypeDef(_, _) => todo!(),
        AstNode::StructDef(_) => todo!(),
        AstNode::UnionDef(_) => todo!(),
        AstNode::EnumDef(_) => todo!(),
        AstNode::Identifier(id) => gen_code_for_id(target, *id),
        AstNode::Number(num) => gen_code_for_num(target, *num),
        AstNode::String(_) => todo!(),
        AstNode::Char(val) => gen_code_for_char(target, *val),
        AstNode::Bool(val) => gen_code_for_bool(target, *val),
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
        AstNode::Call(_, _) => todo!(),
        AstNode::Assign(_, _) => todo!(),
        AstNode::MathOpAssign(_, _, _) => todo!(),
        AstNode::BitOpAssign(_, _, _) => todo!(),
        AstNode::TakeRef(_) => todo!(),
        AstNode::Deref(_) => todo!(),
        AstNode::Block(_) => todo!(),
        AstNode::If(_) => todo!(),
        AstNode::Loop(_) => todo!(),
        AstNode::Return(child) => gen_code_for_ret(target, *child),
        AstNode::Break => write!(target, "break"),
        AstNode::Continue => write!(target, "continue"),
        AstNode::Typecast(_, _) => todo!(),
        AstNode::Tuple(_) => unreachable!(),
    }
}

pub fn gen_c_code(target: &mut impl io::Write, mut ast_parser: AstParser<'_>) -> io::Result<()> {
    for root_node in ast_parser.iter() {
        gen_code_for_node(target, root_node.as_ref().inner())?;
    }
    Ok(())
}
