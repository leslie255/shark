use std::fmt::{Debug, Display, Formatter};

use crate::checks::symboltable::{PossibleTypes, SymbolTable};

#[derive(Clone)]
pub enum TypeExpr<'s> {
    USize,
    ISize,
    U128,
    U64,
    U32,
    U16,
    U8,
    I128,
    I64,
    I32,
    I16,
    I8,
    F64,
    F32,
    Char,
    Bool,

    Ptr(Box<Self>),
    Ref(Box<Self>),
    Slice(Box<Self>),
    /// length, child node
    Array(u64, Box<Self>),
    Tuple(Vec<Self>),

    /// arg types, ret type
    Fn(Vec<Self>, Box<Self>),

    TypeName(&'s str),

    #[allow(dead_code)]
    Struct,
    #[allow(dead_code)]
    Union,
    #[allow(dead_code)]
    Enum,
}
impl<'s> TypeExpr<'s> {
    /// A shorthand for creating the `()` empty tuple type
    #[inline]
    #[must_use]
    pub const fn void() -> Self {
        Self::Tuple(Vec::new())
    }

    pub fn is_void(&self) -> bool {
        match self {
            Self::Tuple(children) => children.is_empty(),
            _ => false,
        }
    }

    pub fn is_numeric(&self, symbol_table: &SymbolTable<'s>) -> bool {
        match self {
            Self::USize
            | Self::ISize
            | Self::U128
            | Self::U64
            | Self::U32
            | Self::U16
            | Self::U8
            | Self::I128
            | Self::I64
            | Self::I32
            | Self::I16
            | Self::I8
            | Self::F64
            | Self::F32 => true,
            &Self::TypeName(name) => symbol_table.var_type(name).map_or(false, |t| match t {
                PossibleTypes::IntNumeric => true,
                PossibleTypes::NegativeIntNumeric => true,
                PossibleTypes::FloatNumeric => true,
                PossibleTypes::Known(t) => t.is_numeric(symbol_table),
            }),
            _ => false,
        }
    }

    pub fn is_signed_numeric(&self, symbol_table: &SymbolTable<'s>) -> bool {
        match self {
            Self::ISize
            | Self::I128
            | Self::I64
            | Self::I32
            | Self::I16
            | Self::I8 => true,
            &Self::TypeName(name) => symbol_table.var_type(name).map_or(false, |t| match t {
                PossibleTypes::IntNumeric => true,
                PossibleTypes::NegativeIntNumeric => true,
                PossibleTypes::FloatNumeric => true,
                PossibleTypes::Known(t) => t.is_signed_numeric(symbol_table),
            }),
            _ => false,
        }
    }

    pub fn is_float_numeric(&self, symbol_table: &SymbolTable<'s>) -> bool {
        match self {
            Self::F64 | Self::F32 => true,
            &Self::TypeName(name) => symbol_table.var_type(name).map_or(false, |t| match t {
                PossibleTypes::IntNumeric => false,
                PossibleTypes::NegativeIntNumeric => false,
                PossibleTypes::FloatNumeric => true,
                PossibleTypes::Known(t) => t.is_float_numeric(symbol_table),
            }),
            _ => false,
        }
    }
}
impl Debug for TypeExpr<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::USize => write!(f, "usize")?,
            Self::ISize => write!(f, "isize")?,
            Self::U128 => write!(f, "u128")?,
            Self::U64 => write!(f, "u64")?,
            Self::U32 => write!(f, "u32")?,
            Self::U16 => write!(f, "u16")?,
            Self::U8 => write!(f, "u8")?,
            Self::I128 => write!(f, "i128")?,
            Self::I64 => write!(f, "i64")?,
            Self::I32 => write!(f, "i32")?,
            Self::I16 => write!(f, "i16")?,
            Self::I8 => write!(f, "i8")?,
            Self::F64 => write!(f, "f64")?,
            Self::F32 => write!(f, "f32")?,
            Self::Char => write!(f, "char")?,
            Self::Bool => write!(f, "bool")?,
            Self::Ptr(child) => write!(f, "*{:?}", child)?,
            Self::Ref(child) => write!(f, "&{:?}", child)?,
            Self::Slice(child) => write!(f, "[]{:?}", child)?,
            Self::Array(len, child) => write!(f, "[{}]{:?}", len, child)?,
            Self::Tuple(children) => {
                write!(f, "(")?;
                let child_count = children.len();
                match child_count {
                    0 => (),
                    1 => {
                        unsafe { children.get_unchecked(0) }.fmt(f)?;
                    }
                    _ => {
                        if f.alternate() {
                            for node in children[0..child_count - 1].iter() {
                                node.fmt(f)?;
                                write!(f, ", ")?;
                            }
                        } else {
                            for node in children[0..child_count - 1].iter() {
                                node.fmt(f)?;
                                write!(f, ",")?;
                            }
                        }
                        let last = unsafe { children.last().unwrap_unchecked() };
                        last.fmt(f)?;
                    }
                }
                write!(f, ")")?;
            }
            Self::Fn(arg_types, ret_type) => {
                write!(f, "fn(")?;
                let arg_count = arg_types.len();
                match arg_count {
                    0 => (),
                    1 => {
                        Debug::fmt(&unsafe { arg_types.get_unchecked(0) }, f)?;
                    }
                    _ => {
                        if f.alternate() {
                            for arg_type in arg_types[0..arg_count - 1].iter() {
                                Debug::fmt(&arg_type, f)?;
                                write!(f, ", ")?;
                            }
                        } else {
                            for arg_type in arg_types[0..arg_count - 1].iter() {
                                Debug::fmt(&arg_type, f)?;
                                write!(f, ",")?;
                            }
                        }
                        let last = unsafe { arg_types.last().unwrap_unchecked() };
                        Debug::fmt(&last, f)?;
                    }
                }
                write!(f, ")")?;
                if f.alternate() {
                    write!(f, "->")?;
                } else {
                    write!(f, " -> ")?;
                }
                Debug::fmt(&ret_type, f)?;
            }
            Self::TypeName(name) => Display::fmt(&name.escape_default(), f)?,
            Self::Struct => write!(f, "{{STRUCT}}")?,
            Self::Union => write!(f, "{{UNION}}")?,
            Self::Enum => write!(f, "{{ENUM}}")?,
        }
        Ok(())
    }
}
impl<'s> TypeExpr<'s> {
    pub fn eq(lhs: &Self, rhs: &Self, symbol_table: &SymbolTable<'s>) -> bool {
        match (lhs, rhs) {
            (TypeExpr::USize, TypeExpr::USize)
            | (TypeExpr::ISize, TypeExpr::ISize)
            | (TypeExpr::U128, TypeExpr::U128)
            | (TypeExpr::I128, TypeExpr::I128)
            | (TypeExpr::U64, TypeExpr::U64)
            | (TypeExpr::U32, TypeExpr::U32)
            | (TypeExpr::U16, TypeExpr::U16)
            | (TypeExpr::U8, TypeExpr::U8)
            | (TypeExpr::I64, TypeExpr::I64)
            | (TypeExpr::I32, TypeExpr::I32)
            | (TypeExpr::I16, TypeExpr::I16)
            | (TypeExpr::I8, TypeExpr::I8)
            | (TypeExpr::F64, TypeExpr::F64)
            | (TypeExpr::F32, TypeExpr::F32)
            | (TypeExpr::Char, TypeExpr::Char)
            | (TypeExpr::Bool, TypeExpr::Bool) => true,
            (TypeExpr::Ptr(lhs), TypeExpr::Ptr(rhs))
            | (TypeExpr::Ref(lhs), TypeExpr::Ref(rhs))
            | (TypeExpr::Slice(lhs), TypeExpr::Slice(rhs)) => Self::eq(lhs, rhs, symbol_table),
            (TypeExpr::Array(lhs_len, lhs), TypeExpr::Array(rhs_len, rhs)) => {
                lhs_len == rhs_len && Self::eq(lhs, rhs, symbol_table)
            }
            (TypeExpr::Tuple(lhs_children), TypeExpr::Tuple(rhs_children)) => {
                lhs_children.len() == rhs_children.len()
                    && lhs_children
                        .iter()
                        .zip(rhs_children)
                        .find(|&(lhs, rhs)| !Self::eq(lhs, rhs, symbol_table))
                        .is_none()
            }
            (TypeExpr::Fn(lhs_args, lhs_ret), TypeExpr::Fn(rhs_args, rhs_ret)) => {
                lhs_args.len() == rhs_args.len()
                    && Self::eq(lhs_ret, rhs_ret, symbol_table)
                    && lhs_args
                        .iter()
                        .zip(rhs_args)
                        .find(|&(lhs, rhs)| !Self::eq(lhs, rhs, symbol_table))
                        .is_none()
            }
            (&TypeExpr::TypeName(lhs_name), &TypeExpr::TypeName(rhs_name)) => {
                if lhs_name == rhs_name {
                    return true;
                }
                let lhs = match symbol_table.typename(lhs_name) {
                    Some(t) => t,
                    None => return false,
                };
                let rhs = match symbol_table.typename(rhs_name) {
                    Some(t) => t,
                    None => return false,
                };
                Self::eq(lhs, rhs, symbol_table)
            }
            (&TypeExpr::TypeName(lhs_name), rhs) => {
                let lhs = match symbol_table.typename(lhs_name) {
                    Some(t) => t,
                    None => return false,
                };
                Self::eq(lhs, rhs, symbol_table)
            }
            (lhs, &TypeExpr::TypeName(rhs_name)) => {
                let rhs = match symbol_table.typename(rhs_name) {
                    Some(t) => t,
                    None => return false,
                };
                Self::eq(lhs, rhs, symbol_table)
            }
            _ => {
                false
                // struct, union or enum are always used through type names, if the type names are
                // equal then it should return true in earlier branches
            }
        }
    }
}
