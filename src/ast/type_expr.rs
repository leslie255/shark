use std::fmt::{Debug, Formatter, Display};

#[derive(Clone)]
pub struct TypeExpr<'a> {
    pool: Vec<TypeExprNode<'a>>,
    root: usize,
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

    Ptr(usize),
    Ref(usize),
    Slice(usize),

    TypeName(&'a str),
}
impl TypeExprNode<'_> {
    fn fmt(self, pool: &Vec<TypeExprNode<'_>>, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeExprNode::USize => write!(f, "usize")?,
            TypeExprNode::ISize => write!(f, "isize")?,
            TypeExprNode::U64 => write!(f, "u64")?,
            TypeExprNode::U32 => write!(f, "u32")?,
            TypeExprNode::U16 => write!(f, "u16")?,
            TypeExprNode::U8 => write!(f, "u8")?,
            TypeExprNode::I64 => write!(f, "i64")?,
            TypeExprNode::I32 => write!(f, "i32")?,
            TypeExprNode::I16 => write!(f, "i16")?,
            TypeExprNode::I8 => write!(f, "i8")?,
            TypeExprNode::Char32 => write!(f, "char32")?,
            TypeExprNode::Char8 => write!(f, "char8")?,
            TypeExprNode::Ptr(child_i) => {
                write!(f, "ptr<")?;
                pool[child_i].fmt(pool, f)?;
                write!(f, ">")?;
            }
            TypeExprNode::Ref(child_i) => {
                write!(f, "ref<")?;
                pool[child_i].fmt(pool, f)?;
                write!(f, ">")?;
            }
            TypeExprNode::Slice(child_i) => {
                write!(f, "slice<")?;
                pool[child_i].fmt(pool, f)?;
                write!(f, ">")?;
            }
            TypeExprNode::TypeName(name) => Display::fmt(&name.escape_default(), f)?,
        }
        Ok(())
    }
}
