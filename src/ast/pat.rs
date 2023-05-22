use crate::error::location::{SourceLocation, Traced};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mutability {
    Mutable,
    Const,
}

impl Mutability {
    /// Returns `true` if the mutability is [`Mutable`].
    ///
    /// [`Mutable`]: Mutability::Mutable
    #[must_use]
    pub fn is_mut(&self) -> bool {
        matches!(self, Self::Mutable)
    }

    /// Returns `true` if the mutability is [`Const`].
    ///
    /// [`Const`]: Mutability::Const
    #[must_use]
    pub fn is_const(&self) -> bool {
        matches!(self, Self::Const)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    Var(Mutability, &'static str),
    #[allow(dead_code)]
    Tuple(Vec<Pattern>),
}

impl Pattern {
    pub fn traced(self, src_loc: SourceLocation) -> Traced<Self> {
        Traced::new(self, src_loc)
    }
}
