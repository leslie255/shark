use std::{
    hash::{Hash, Hasher},
    io,
};

use crate::{
    ast::{parser::AstParser, type_expr::TypeExpr, AstNode, AstNodeRef, FnDef, StructOrUnionDef},
    token::NumValue,
};

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

fn codegen_ty(target: &mut impl io::Write, ty: &TypeExpr<'_>) -> io::Result<()> {
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
        TypeExpr::Ptr(ty) | TypeExpr::Ref(ty) => {
            codegen_ty(target, ty.as_ref())?;
            write!(target, "*")
        }
        TypeExpr::Slice(_) => todo!("slice type"),
        TypeExpr::Array(_, _) => todo!("array type"),
        TypeExpr::Tuple(fields) if fields.is_empty() => write!(target, "void"),
        TypeExpr::Tuple(_) => todo!("tuple type"),
        TypeExpr::Fn(_, _) => todo!("function pointer type"),
        TypeExpr::TypeName(id) => codegen_id(target, id),
        TypeExpr::Struct => todo!("struct"),
        TypeExpr::Union => todo!("union"),
        TypeExpr::Enum => todo!("enum"),
    }
}

#[inline]
fn codegen_id(target: &mut impl io::Write, id: &str) -> io::Result<()> {
    if is_c_keyword(id) {
        write!(target, "ID_{}___{}_", id, quick_hash_str(id))
    } else {
        write!(target, "{}", id)
    }
}

#[inline]
fn codegen_num(target: &mut impl io::Write, num: NumValue) -> io::Result<()> {
    write!(target, "{:?}", num)
}

#[inline]
fn codegen_bool(target: &mut impl io::Write, val: bool) -> io::Result<()> {
    write!(target, "{}", if val { 1 } else { 0 })
}

#[inline]
fn codegen_char(target: &mut impl io::Write, val: char) -> io::Result<()> {
    write!(target, "{}", u32::from(val))
}

#[inline]
fn codegen_let<'s>(
    target: &mut impl io::Write,
    lhs: &'s str,
    ty: Option<&TypeExpr<'s>>,
    rhs: Option<AstNodeRef<'s>>,
) -> io::Result<()> {
    let ty = ty.expect("type infer is unimplemented");
    codegen_ty(target, ty)?;
    write!(target, " ")?;
    codegen_id(target, lhs)?;
    if let Some(rhs_node) = rhs.map(|n| n.as_ref().inner()) {
        write!(target, " = ")?;
        codegen_node(target, rhs_node)?;
    } else {
    }
    Ok(())
}

#[inline]
fn codegen_fn_def<'s>(target: &mut impl io::Write, fn_def: &FnDef<'s>) -> io::Result<()> {
    codegen_ty(target, &fn_def.sign.ret_type)?;
    write!(target, " ")?;
    codegen_id(target, fn_def.name)?;
    write!(target, "(")?;
    for (i, (arg_name, arg_ty)) in fn_def.sign.args.iter().enumerate() {
        codegen_ty(target, arg_ty)?;
        write!(target, " ")?;
        codegen_id(target, *arg_name)?;
        if i < fn_def.sign.args.len() - 1 {
            write!(target, ",")?;
        }
    }
    write!(target, ")")?;
    match fn_def.body {
        Some(ref body) => {
            write!(target, "{{")?;
            for n in body {
                codegen_node(target, n.as_ref().inner())?;
                write!(target, ";")?;
            }
            write!(target, "}}")?;
        }
        None => write!(target, ";")?,
    }
    Ok(())
}

#[inline]
fn codegen_ret<'s>(target: &mut impl io::Write, child: Option<AstNodeRef<'_>>) -> io::Result<()> {
    write!(target, "return ")?;
    match child {
        Some(child) => codegen_node(target, child.as_ref().inner())?,
        None => (),
    }
    Ok(())
}

#[inline]
fn codegen_call(
    target: &mut impl io::Write,
    callee: &AstNode,
    args: &Vec<AstNodeRef>,
) -> io::Result<()> {
    codegen_node(target, callee)?;
    write!(target, "(")?;
    for (i, arg_node) in args.iter().enumerate() {
        codegen_node(target, arg_node.as_ref().inner())?;
        if i < args.len() - 1 {
            write!(target, ",")?;
        }
    }
    write!(target, ")")?;
    Ok(())
}

#[inline]
fn codegen_str(target: &mut impl io::Write, s: *const str) -> io::Result<()> {
    write!(target, "{:?}", unsafe { s.as_ref().unwrap() })
}

/// Because `struct` and `union` definition syntax are so similar in C, this function is in charge
/// of generation `NAME {field0:ty0;field1:ty1; ... }` right after the `struct` or `union` keyword
#[inline]
fn codegen_struct_union_name_and_body(
    target: &mut impl io::Write,
    def: &StructOrUnionDef,
) -> io::Result<()> {
    codegen_id(target, def.name)?;
    write!(target, "{{")?;
    for (id, ty) in &def.fields {
        codegen_ty(target, ty)?;
        write!(target, " ")?;
        codegen_id(target, id)?;
        write!(target, ";")?;
    }
    write!(target, "}}")?;
    codegen_id(target, def.name)?;
    write!(target, ";")?;
    Ok(())
}

#[inline]
fn codegen_struct_def(target: &mut impl io::Write, def: &StructOrUnionDef) -> io::Result<()> {
    write!(target, "typedef struct ")?;
    codegen_struct_union_name_and_body(target, def)
}

#[inline]
fn codegen_union_def(target: &mut impl io::Write, def: &StructOrUnionDef) -> io::Result<()> {
    write!(target, "typedef union ")?;
    codegen_struct_union_name_and_body(target, def)
}

#[inline]
fn codegen_typedef(target: &mut impl io::Write, id: &str, ty: &TypeExpr) -> io::Result<()> {
    write!(target, "typedef ")?;
    codegen_ty(target, ty)?;
    write!(target, " ")?;
    codegen_id(target, id)?;
    write!(target, ";")?;
    Ok(())
}

fn codegen_node(target: &mut impl io::Write, node: &AstNode) -> io::Result<()> {
    match node {
        AstNode::Let(lhs, ty, rhs) => codegen_let(target, *lhs, ty.as_ref(), *rhs),
        AstNode::FnDef(fn_def) => codegen_fn_def(target, fn_def),
        AstNode::TypeDef(id, ty) => codegen_typedef(target, id, ty),
        AstNode::StructDef(def) => codegen_struct_def(target, def),
        AstNode::UnionDef(def) => codegen_union_def(target, def),
        AstNode::EnumDef(_) => todo!(),
        AstNode::Identifier(id) => codegen_id(target, *id),
        AstNode::Number(num) => codegen_num(target, *num),
        AstNode::String(s) => codegen_str(target, *s),
        AstNode::Char(val) => codegen_char(target, *val),
        AstNode::Bool(val) => codegen_bool(target, *val),
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
        AstNode::Call(callee, args) => codegen_call(target, callee, args),
        AstNode::Assign(_, _) => todo!(),
        AstNode::MathOpAssign(_, _, _) => todo!(),
        AstNode::BitOpAssign(_, _, _) => todo!(),
        AstNode::TakeRef(_) => todo!(),
        AstNode::Deref(_) => todo!(),
        AstNode::Block(_) => todo!(),
        AstNode::If(_) => todo!(),
        AstNode::Loop(_) => todo!(),
        AstNode::Return(child) => codegen_ret(target, *child),
        AstNode::Break => write!(target, "break"),
        AstNode::Continue => write!(target, "continue"),
        AstNode::Typecast(_, _) => todo!(),
        AstNode::Tuple(_) => unreachable!(),
    }
}

pub fn gen_c_code(target: &mut impl io::Write, mut ast_parser: AstParser<'_>) -> io::Result<()> {
    write!(target, "#include\"common.h\"\n")?;
    for root_node in ast_parser.iter() {
        codegen_node(target, root_node.as_ref().inner())?;
    }
    Ok(())
}
