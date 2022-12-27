use std::fmt::{Debug, Display, Formatter};

use crate::checks::symboltable::SymbolTable;

#[derive(Clone)]
pub struct TypeExpr<'a> {
    pub pool: Vec<TypeExprNode<'a>>,
    pub root: usize,
}
impl<'a> TypeExpr<'a> {
    #[inline]
    fn root(&self) -> &TypeExprNode<'a> {
        &self.pool[self.root]
    }

    #[inline]
    pub fn is_numeric(&self, symbol_table: &SymbolTable<'a>) -> bool {
        match self.root() {
            TypeExprNode::USize
            | TypeExprNode::ISize
            | TypeExprNode::U64
            | TypeExprNode::U32
            | TypeExprNode::U16
            | TypeExprNode::U8
            | TypeExprNode::I64
            | TypeExprNode::I32
            | TypeExprNode::I16
            | TypeExprNode::I8 => true,
            &TypeExprNode::TypeName(typename) => symbol_table
                .typename(typename)
                .map_or(false, |t| t.is_numeric(symbol_table)),
            _ => false,
        }
    }

    #[inline]
    pub fn is_signed_numeric(&self, symbol_table: &SymbolTable<'a>) -> bool {
        match self.root() {
            TypeExprNode::ISize
            | TypeExprNode::I64
            | TypeExprNode::I32
            | TypeExprNode::I16
            | TypeExprNode::I8
            | TypeExprNode::F64
            | TypeExprNode::F32 => true,
            &TypeExprNode::TypeName(typename) => symbol_table
                .typename(typename)
                .map_or(false, |t| t.is_signed_numeric(symbol_table)),
            _ => false,
        }
    }

    #[inline]
    pub fn is_float(&self, symbol_table: &SymbolTable<'a>) -> bool {
        match self.root() {
            TypeExprNode::F64 | TypeExprNode::F32 => true,
            &TypeExprNode::TypeName(typename) => symbol_table
                .typename(typename)
                .map_or(false, |t| t.is_float(symbol_table)),
            _ => false,
        }
    }

    pub fn eq(lhs: &Self, rhs: &Self, symbol_table: &SymbolTable<'a>) -> bool {
        TypeExprNode::eq(lhs, rhs, lhs.root(), rhs.root(), symbol_table)
    }
}
impl<'a> Display for TypeExpr<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.root().fmt(&self.pool, f)
    }
}
impl<'a> Debug for TypeExpr<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.root().fmt(&self.pool, f)
    }
}

#[derive(Clone)]
pub enum TypeExprNode<'a> {
    USize,
    ISize,
    U64,
    U32,
    U16,
    U8,
    I64,
    I32,
    I16,
    I8,
    F64,
    F32,
    Char,
    Bool,

    Ptr(usize),
    Ref(usize),
    Slice(usize),
    /// length, child node
    Array(u64, usize),
    Tuple(Vec<usize>),

    /// arg types, ret type
    Fn(Vec<usize>, usize),

    TypeName(&'a str),

    #[allow(dead_code)]
    Struct,
    #[allow(dead_code)]
    Union,
    #[allow(dead_code)]
    Enum,
}
impl<'a> TypeExprNode<'a> {
    /// A shorthand for creating the `()` empty tuple type
    #[inline]
    #[must_use]
    pub const fn void() -> Self {
        Self::Tuple(Vec::new())
    }

    fn fmt(&self, pool: &Vec<TypeExprNode<'_>>, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::USize => write!(f, "usize")?,
            Self::ISize => write!(f, "isize")?,
            Self::U64 => write!(f, "u64")?,
            Self::U32 => write!(f, "u32")?,
            Self::U16 => write!(f, "u16")?,
            Self::U8 => write!(f, "u8")?,
            Self::I64 => write!(f, "i64")?,
            Self::I32 => write!(f, "i32")?,
            Self::I16 => write!(f, "i16")?,
            Self::I8 => write!(f, "i8")?,
            Self::F64 => write!(f, "f64")?,
            Self::F32 => write!(f, "f32")?,
            Self::Char => write!(f, "char")?,
            Self::Bool => write!(f, "bool")?,
            Self::Ptr(child_i) => {
                write!(f, "*")?;
                pool[*child_i].fmt(pool, f)?;
            }
            Self::Ref(child_i) => {
                write!(f, "&")?;
                pool[*child_i].fmt(pool, f)?;
            }
            Self::Slice(child_i) => {
                write!(f, "[]")?;
                pool[*child_i].fmt(pool, f)?;
            }
            Self::Array(len, child_i) => {
                write!(f, "[{}]", len)?;
                pool[*child_i].fmt(pool, f)?;
            }
            Self::Tuple(children) => {
                write!(f, "(")?;
                let child_count = children.len();
                match child_count {
                    0 => (),
                    1 => {
                        let node = &pool[children[0]];
                        node.fmt(pool, f)?;
                    }
                    _ => {
                        if f.alternate() {
                            for node in children[0..child_count - 1].iter() {
                                let node = &pool[*node];
                                node.fmt(pool, f)?;
                                write!(f, ", ")?;
                            }
                        } else {
                            for node in children[0..child_count - 1].iter() {
                                let node = &pool[*node];
                                node.fmt(pool, f)?;
                                write!(f, ",")?;
                            }
                        }
                        let &last_i = unsafe { children.last().unwrap_unchecked() };
                        pool[last_i].fmt(pool, f)?;
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
                        let node = &pool[arg_types[0]];
                        node.fmt(pool, f)?;
                    }
                    _ => {
                        if f.alternate() {
                            for arg in arg_types[0..arg_count - 1].iter() {
                                let node = &pool[*arg];
                                node.fmt(pool, f)?;
                                write!(f, ", ")?;
                            }
                        } else {
                            for arg in arg_types[0..arg_count - 1].iter() {
                                let node = &pool[*arg];
                                node.fmt(pool, f)?;
                                write!(f, ",")?;
                            }
                        }
                        let &last_i = unsafe { arg_types.last().unwrap_unchecked() };
                        pool[last_i].fmt(pool, f)?;
                    }
                }
                write!(f, ")")?;
                if f.alternate() {
                    write!(f, "->")?;
                } else {
                    write!(f, " -> ")?;
                }
                pool[*ret_type].fmt(pool, f)?;
            }
            Self::TypeName(name) => Display::fmt(&name.escape_default(), f)?,
            Self::Struct => write!(f, "STRUCT")?,
            Self::Union => write!(f, "UNION")?,
            Self::Enum => write!(f, "ENUM")?,
        }
        Ok(())
    }

    /// Wrap the `TypeExprNode` into a `TypeExpr` with only one node
    #[inline]
    #[must_use]
    pub fn wrap(self) -> TypeExpr<'a> {
        TypeExpr {
            pool: vec![self],
            root: 0,
        }
    }

    pub fn eq(
        lhs_pool: &TypeExpr<'a>,
        rhs_pool: &TypeExpr<'a>,
        lhs: &Self,
        rhs: &Self,
        symbol_table: &SymbolTable<'a>,
    ) -> bool {
        match (lhs, rhs) {
            (TypeExprNode::USize, TypeExprNode::USize)
            | (TypeExprNode::ISize, TypeExprNode::ISize)
            | (TypeExprNode::U64, TypeExprNode::U64)
            | (TypeExprNode::U32, TypeExprNode::U32)
            | (TypeExprNode::U16, TypeExprNode::U16)
            | (TypeExprNode::U8, TypeExprNode::U8)
            | (TypeExprNode::I64, TypeExprNode::I64)
            | (TypeExprNode::I32, TypeExprNode::I32)
            | (TypeExprNode::I16, TypeExprNode::I16)
            | (TypeExprNode::I8, TypeExprNode::I8)
            | (TypeExprNode::F64, TypeExprNode::F64)
            | (TypeExprNode::F32, TypeExprNode::F32)
            | (TypeExprNode::Char, TypeExprNode::Char)
            | (TypeExprNode::Bool, TypeExprNode::Bool) => true,
            (&TypeExprNode::Ptr(lhs), &TypeExprNode::Ptr(rhs))
            | (&TypeExprNode::Ref(lhs), &TypeExprNode::Ref(rhs))
            | (&TypeExprNode::Slice(lhs), &TypeExprNode::Slice(rhs)) => Self::eq(
                lhs_pool,
                rhs_pool,
                &lhs_pool.pool[lhs],
                &rhs_pool.pool[rhs],
                symbol_table,
            ),
            (&TypeExprNode::Array(lhs_len, lhs), &TypeExprNode::Array(rhs_len, rhs)) => {
                lhs_len == rhs_len
                    && Self::eq(
                        lhs_pool,
                        rhs_pool,
                        &lhs_pool.pool[lhs],
                        &rhs_pool.pool[rhs],
                        symbol_table,
                    )
            }
            (TypeExprNode::Tuple(lhs_children), TypeExprNode::Tuple(rhs_children)) => lhs_children
                .iter()
                .zip(rhs_children)
                .map(|(&lhs_i, &rhs_i)| (&lhs_pool.pool[lhs_i], &rhs_pool.pool[rhs_i]))
                .find(|(lhs, rhs)| !Self::eq(lhs_pool, rhs_pool, lhs, rhs, symbol_table))
                .is_none(),
            (TypeExprNode::Fn(lhs_args, lhs_ret), TypeExprNode::Fn(rhs_args, rhs_ret)) => {
                Self::eq(
                    lhs_pool,
                    rhs_pool,
                    &lhs_pool.pool[*lhs_ret],
                    &rhs_pool.pool[*rhs_ret],
                    symbol_table,
                ) && lhs_args
                    .iter()
                    .zip(rhs_args)
                    .map(|(&lhs_i, &rhs_i)| (&lhs_pool.pool[lhs_i], &rhs_pool.pool[rhs_i]))
                    .find(|(lhs, rhs)| !Self::eq(lhs_pool, rhs_pool, lhs, rhs, symbol_table))
                    .is_none()
            }
            (&TypeExprNode::TypeName(lhs_name), &TypeExprNode::TypeName(rhs_name)) => {
                let lhs_pool = match symbol_table.typename(lhs_name) {
                    Some(t) => t,
                    None => return false,
                };
                let rhs_pool = match symbol_table.typename(rhs_name) {
                    Some(t) => t,
                    None => return false,
                };
                Self::eq(lhs_pool, rhs_pool, lhs_pool.root(), rhs_pool.root(), symbol_table)
            },
            (&TypeExprNode::TypeName(lhs_name), rhs) => {
                let lhs_pool = match symbol_table.typename(lhs_name) {
                    Some(t) => t,
                    None => return false,
                };
                Self::eq(lhs_pool, rhs_pool, lhs_pool.root(), rhs, symbol_table)
            },
            (lhs, TypeExprNode::TypeName(rhs_name)) => {
                let rhs_pool = match symbol_table.typename(rhs_name) {
                    Some(t) => t,
                    None => return false,
                };
                Self::eq(lhs_pool, rhs_pool, lhs, rhs_pool.root(), symbol_table)
            },
            (TypeExprNode::Struct, _) => false,
            (TypeExprNode::Union, _) => false,
            (TypeExprNode::Enum, _) => false,
            (_, TypeExprNode::Struct) => false,
            (_, TypeExprNode::Union) => false,
            (_, TypeExprNode::Enum) => false,
            _ => todo!(),
        }
    }
}
