use std::{
    fmt::{Debug, Display},
    ops::{Deref, Range},
};

/// Describes the location of a token or an AST node in source code
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct SourceLocation<'a> {
    pub file_name: &'a str,
    pub range: (usize, usize),
}
impl Debug for SourceLocation<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "`{}` #{}~{}",
            self.file_name.escape_debug(),
            self.range.0,
            self.range.1
        )
    }
}
impl Display for SourceLocation<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}:{}",
            self.file_name.escape_debug(),
            self.range.0,
            self.range.1
        )
    }
}

pub trait IntoSourceLoc<'a> {
    fn into_source_location(self) -> SourceLocation<'a>;
}
impl<'a> IntoSourceLoc<'a> for SourceLocation<'a> {
    fn into_source_location(self) -> SourceLocation<'a> {
        self
    }
}
impl<'a> IntoSourceLoc<'a> for (&'a str, usize) {
    fn into_source_location(self) -> SourceLocation<'a> {
        SourceLocation {
            file_name: self.0,
            range: (self.1, self.1),
        }
    }
}
impl<'a> IntoSourceLoc<'a> for (&'a str, (usize, usize)) {
    fn into_source_location(self) -> SourceLocation<'a> {
        SourceLocation {
            file_name: self.0,
            range: (self.1 .0, self.1 .1),
        }
    }
}
impl<'a> IntoSourceLoc<'a> for (&'a str, usize, usize) {
    fn into_source_location(self) -> SourceLocation<'a> {
        SourceLocation {
            file_name: self.0,
            range: (self.1, self.2),
        }
    }
}
impl<'a> IntoSourceLoc<'a> for (&'a str, Range<usize>) {
    fn into_source_location(self) -> SourceLocation<'a> {
        SourceLocation {
            file_name: self.0,
            range: (self.1.start, self.1.end),
        }
    }
}

/// A wrapper for attaching a source location to a token or AST node
#[derive(Clone, PartialEq)]
pub struct Traced<'a, T>(T, SourceLocation<'a>);
impl<'a, T> Traced<'a, T> {
    pub fn new(inner: T, source_location: impl IntoSourceLoc<'a>) -> Self {
        Self(inner, source_location.into_source_location())
    }
    pub fn into_inner(&self) -> &T {
        &self.0
    }
    pub fn source_location(&self) -> SourceLocation {
        self.1
    }
}
impl<'a, T> Deref for Traced<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<'a, T> Debug for Traced<'a, T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.into_inner().fmt(f)
    }
}
impl<'a, T> Display for Traced<'a, T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.into_inner().fmt(f)
    }
}
