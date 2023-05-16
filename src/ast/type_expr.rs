use std::fmt::{Debug, Display, Formatter};

/// `TypeExpr` implements `Eq`, but in the type checker it should always be compared by
/// `gen::type_matches` to comparing with co-variance
#[derive(Clone, PartialEq, Eq)]
pub enum TypeExpr {
    INVALID,
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

    _UnknownNumeric(NumericType),
    _Unknown,

    Never,
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

    /// Returns `true` if the type expr is [`Never`].
    ///
    /// [`Never`]: TypeExpr::Never
    #[must_use]
    pub fn is_never(&self) -> bool {
        matches!(self, Self::Never)
    }

    /// Doesn't include `_UnknownNumeric`
    pub fn is_numeric(&self) -> bool {
        matches!(
            self,
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
        )
    }

    pub fn is_u(&self) -> bool {
        matches!(
            self,
            TypeExpr::USize
                | TypeExpr::U128
                | TypeExpr::U64
                | TypeExpr::U32
                | TypeExpr::U16
                | TypeExpr::U8
        )
    }

    pub fn is_i(&self) -> bool {
        matches!(
            self,
            TypeExpr::ISize
                | TypeExpr::I128
                | TypeExpr::I64
                | TypeExpr::I32
                | TypeExpr::I16
                | TypeExpr::I8
        )
    }

    pub fn is_f(&self) -> bool {
        matches!(self, TypeExpr::F64 | TypeExpr::F32)
    }

    pub fn is_concrete(&self) -> bool {
        !matches!(self, TypeExpr::_UnknownNumeric(..) | TypeExpr::_Unknown)
    }

    /// Returns `true` if the type expr is [`_UnknownNumeric`].
    ///
    /// [`_UnknownNumeric`]: TypeExpr::_UnknownNumeric
    #[must_use]
    pub const fn is_unknown_numeric(&self) -> bool {
        matches!(self, Self::_UnknownNumeric(..))
    }

    /// Returns `true` if the type expr is [`_UnknownNumeric`] and is signed.
    ///
    /// [`_UnknownNumeric`]: TypeExpr::_UnknownNumeric
    #[must_use]
    pub const fn is_unknown_signed_numeric(&self) -> bool {
        matches!(self, Self::_UnknownNumeric(num_ty) if num_ty.is_signed)
    }

    /// Returns `true` if the type expr is [`_Unknown`].
    ///
    /// [`_Unknown`]: TypeExpr::_Unknown
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::_Unknown)
    }

    pub fn is_trivial(&self) -> bool {
        match self {
            TypeExpr::INVALID => false,
            TypeExpr::USize => false,
            TypeExpr::ISize => false,
            TypeExpr::U128 => false,
            TypeExpr::U64 => false,
            TypeExpr::U32 => false,
            TypeExpr::U16 => false,
            TypeExpr::U8 => false,
            TypeExpr::I128 => false,
            TypeExpr::I64 => false,
            TypeExpr::I32 => false,
            TypeExpr::I16 => false,
            TypeExpr::I8 => false,
            TypeExpr::F64 => false,
            TypeExpr::F32 => false,
            TypeExpr::Char => false,
            TypeExpr::Bool => false,
            TypeExpr::Ptr(_) => false,
            TypeExpr::Ref(_) => false,
            TypeExpr::Slice(_) => false,
            TypeExpr::Array(_, _) => false,
            TypeExpr::Tuple(fields) => fields.is_empty(),
            TypeExpr::Fn(_, _) => false,
            TypeExpr::TypeName(_) => false,
            TypeExpr::Struct => false,
            TypeExpr::Union => false,
            TypeExpr::Enum => false,
            TypeExpr::_UnknownNumeric(_) => false,
            TypeExpr::_Unknown => false,
            TypeExpr::Never => false,
        }
    }
}

impl Debug for TypeExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::INVALID => writeln!(f, "{{invalid}}")?,
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
            Self::_Unknown => write!(f, "{{unknown}}")?,
            Self::_UnknownNumeric(num_ty) => num_ty.fmt(f)?,
            Self::Never => write!(f, "!")?,
        }
        Ok(())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub struct NumericType {
    pub is_int: bool,
    pub is_signed: bool,
}
impl Debug for NumericType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match (self.is_int, self.is_signed) {
            (true, true) => write!(f, "{{signed integer}}"),
            (true, false) => write!(f, "{{integer}}"),
            (false, true) => write!(f, "{{signed numeric}}"),
            (false, false) => write!(f, "{{numeric}}"),
        }
    }
}
impl NumericType {
    pub const fn new() -> Self {
        Self {
            is_int: false,
            is_signed: false,
        }
    }
    pub const fn int(self) -> Self {
        Self {
            is_int: true,
            is_signed: self.is_signed,
        }
    }
    pub const fn signed(self) -> Self {
        Self {
            is_int: self.is_int,
            is_signed: true,
        }
    }
}
