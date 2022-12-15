use std::{
    fmt::{Debug, Display},
    ops::{Deref, Range},
};

use crate::string::SourceIndex;

/// Describes the location of a token or an AST node in source code
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct SourceLocation<'src> {
    pub file_name: &'src str,
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
impl<'a> IntoSourceLoc<'a> for (&'a str, SourceIndex<'a>) {
    fn into_source_location(self) -> SourceLocation<'a> {
        SourceLocation {
            file_name: self.0,
            range: (self.1.position, self.1.position),
        }
    }
}
impl<'a> IntoSourceLoc<'a> for (&'a str, (SourceIndex<'a>, SourceIndex<'a>)) {
    fn into_source_location(self) -> SourceLocation<'a> {
        SourceLocation {
            file_name: self.0,
            range: (self.1 .0.position, self.1 .1.position),
        }
    }
}
impl<'a> IntoSourceLoc<'a> for (&'a str, SourceIndex<'a>, SourceIndex<'a>) {
    fn into_source_location(self) -> SourceLocation<'a> {
        SourceLocation {
            file_name: self.0,
            range: (self.1.position, self.2.position),
        }
    }
}
impl<'a> IntoSourceLoc<'a> for (&'a str, Range<SourceIndex<'a>>) {
    fn into_source_location(self) -> SourceLocation<'a> {
        SourceLocation {
            file_name: self.0,
            range: (self.1.start.position, self.1.end.position),
        }
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
pub struct Traced<'src, T> {
    inner: T,
    src_loc: SourceLocation<'src>,
}

impl<'src, T> Default for Traced<'src, T>
where
    T: Default,
{
    fn default() -> Self {
        Self {
            inner: Default::default(),
            src_loc: SourceLocation {
                file_name: "",
                range: (0, 0),
            },
        }
    }
}

impl<'src, T> Traced<'src, T> {
    /// Wrap an thing into `Traced`
    /// Call this function by...
    /// ```
    /// Traced::new(x, (file_name, start, end))
    /// Traced::new(x, (file_name, (start, end)))
    /// Traced::new(x, (file_name, start..end))
    /// Traced::new(x, (file_name, pos))
    /// Traced::new(x, SourceLocation {file_name, range: (start, end)})
    /// ```
    /// ... Or anything else that implements `IntoSourceLoc`
    pub fn new(inner: T, src_loc: impl IntoSourceLoc<'src>) -> Self {
        Self {
            inner,
            src_loc: src_loc.into_source_location(),
        }
    }
    /// Returns the wrapped content by reference
    #[inline]
    #[must_use]
    pub fn inner(&self) -> &T {
        &self.inner
    }
    /// Consumes `self` and returns the wrapped content
    #[inline]
    #[must_use]
    pub fn into_inner(self) -> T {
        self.inner
    }
    /// Returns the attached source location
    #[inline]
    #[must_use]
    pub fn src_loc(&self) -> SourceLocation<'src> {
        self.src_loc
    }
}
impl<'src, T> Deref for Traced<'src, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}
impl<'src, T> Debug for Traced<'src, T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}
impl<'src, T> Display for Traced<'src, T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}
