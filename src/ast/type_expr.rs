use std::fmt::{Debug, Display, Formatter};

#[derive(Clone)]
pub struct TypeExpr<'a> {
    pub pool: Vec<TypeExprNode<'a>>,
    pub root: usize,
}
impl<'a> TypeExpr<'a> {
    fn root(&self) -> &TypeExprNode<'a> {
        &self.pool[self.root]
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
    Char32,
    Char8,
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
            Self::Char32 => write!(f, "char32")?,
            Self::Char8 => write!(f, "char8")?,
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
