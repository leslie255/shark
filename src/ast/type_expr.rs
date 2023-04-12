use std::fmt::{Debug, Display, Formatter};

#[derive(Clone)]
pub enum TypeExpr {
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

    TypeName(&'static str),

    #[allow(dead_code)]
    Struct,
    #[allow(dead_code)]
    Union,
    #[allow(dead_code)]
    Enum,
}
impl TypeExpr {
    /// A shorthand for creating the `()` empty tuple type
    #[inline]
    #[must_use]
    pub const fn void() -> Self {
        Self::Tuple(Vec::new())
    }

    #[allow(dead_code)]
    pub fn is_void_tuple(&self) -> bool {
        matches!(self, Self::Tuple(children) if children.is_empty())
    }
}
impl Debug for TypeExpr {
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
