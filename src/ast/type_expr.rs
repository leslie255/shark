use std::fmt::{Debug, Display, Formatter};

#[derive(Clone)]
pub struct TypeExpr<'a> {
    pub pool: Vec<TypeExprNode<'a>>,
    pub root: usize,
}
impl<'a> TypeExpr<'a> {
    fn root(&self) -> TypeExprNode {
        self.pool[self.root]
    }
}
impl<'a> Debug for TypeExpr<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.root().fmt(&self.pool, f)
    }
}

#[derive(Clone, Copy)]
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
    Char32,
    Char8,
    Bool,

    None,

    Ptr(usize),
    Ref(usize),
    Slice(usize),

    TypeName(&'a str),
}
impl<'a> TypeExprNode<'a> {
    fn fmt(self, pool: &Vec<TypeExprNode<'_>>, f: &mut Formatter<'_>) -> std::fmt::Result {
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
            Self::Char32 => write!(f, "char32")?,
            Self::Char8 => write!(f, "char8")?,
            Self::Bool => write!(f, "bool")?,
            Self::None => write!(f, "none")?,
            Self::Ptr(child_i) => {
                write!(f, "*")?;
                pool[child_i].fmt(pool, f)?;
            }
            Self::Ref(child_i) => {
                write!(f, "&")?;
                pool[child_i].fmt(pool, f)?;
            }
            Self::Slice(child_i) => {
                write!(f, "[]")?;
                pool[child_i].fmt(pool, f)?;
            }
            Self::TypeName(name) => Display::fmt(&name.escape_default(), f)?,
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
}
