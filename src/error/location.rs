use std::{
    fmt::{Debug, Display},
    ops::{Deref, DerefMut, Range},
};

use crate::string::SourceIndex;

/// Describes the location of a token or an AST node in source code
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct SourceLocation {
    pub file_name: &'static str,
    pub range: (usize, usize),
}

impl SourceLocation {
    /// Make another source location by using the file name and starting position of `self` and
    /// ending position of `other`
    pub fn join(self, other: Self) -> Self {
        (self.file_name, self.range.0, other.range.1).into_source_location()
    }

    /// Make another source location by using the file name and ending position of `self`
    pub fn end(self) -> Self {
        (self.file_name, self.range.1).into_source_location()
    }
}
impl Debug for SourceLocation {
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
impl Display for SourceLocation {
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

pub trait IntoSourceLoc {
    fn into_source_location(self) -> SourceLocation;
}
impl IntoSourceLoc for SourceLocation {
    #[inline]
    fn into_source_location(self) -> SourceLocation {
        self
    }
}
impl IntoSourceLoc for (&'static str, SourceIndex) {
    #[inline]
    fn into_source_location(self) -> SourceLocation {
        SourceLocation {
            file_name: self.0,
            range: (self.1.position, self.1.position),
        }
    }
}
impl IntoSourceLoc for (&'static str, (SourceIndex, SourceIndex)) {
    #[inline]
    fn into_source_location(self) -> SourceLocation {
        SourceLocation {
            file_name: self.0,
            range: (self.1 .0.position, self.1 .1.position),
        }
    }
}
impl IntoSourceLoc for (&'static str, SourceIndex, SourceIndex) {
    #[inline]
    fn into_source_location(self) -> SourceLocation {
        SourceLocation {
            file_name: self.0,
            range: (self.1.position, self.2.position),
        }
    }
}
impl IntoSourceLoc for (&'static str, Range<SourceIndex>) {
    #[inline]
    fn into_source_location(self) -> SourceLocation {
        SourceLocation {
            file_name: self.0,
            range: (self.1.start.position, self.1.end.position),
        }
    }
}
impl IntoSourceLoc for (&'static str, usize) {
    #[inline]
    fn into_source_location(self) -> SourceLocation {
        SourceLocation {
            file_name: self.0,
            range: (self.1, self.1),
        }
    }
}
impl IntoSourceLoc for (&'static str, (usize, usize)) {
    #[inline]
    fn into_source_location(self) -> SourceLocation {
        SourceLocation {
            file_name: self.0,
            range: (self.1 .0, self.1 .1),
        }
    }
}
impl IntoSourceLoc for (&'static str, usize, usize) {
    #[inline]
    fn into_source_location(self) -> SourceLocation {
        SourceLocation {
            file_name: self.0,
            range: (self.1, self.2),
        }
    }
}
impl IntoSourceLoc for (&'static str, Range<usize>) {
    #[inline]
    fn into_source_location(self) -> SourceLocation {
        SourceLocation {
            file_name: self.0,
            range: (self.1.start, self.1.end),
        }
    }
}

/// A wrapper for attaching a source location to a token or AST node
#[derive(Clone, PartialEq)]
pub struct Traced<T> {
    inner: T,
    src_loc: SourceLocation,
}

impl<T> Default for Traced<T>
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

impl<T> Traced<T> {
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
    pub fn new(inner: T, src_loc: impl IntoSourceLoc) -> Self {
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
    /// Returns the wrapped content by mutable reference
    #[inline]
    #[must_use]
    #[allow(dead_code)]
    pub fn inner_mut(&mut self) -> &mut T {
        &mut self.inner
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
    pub fn src_loc(&self) -> SourceLocation {
        self.src_loc
    }
}
impl<T> Deref for Traced<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}
impl<T> DerefMut for Traced<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}
impl<T> Debug for Traced<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}
impl<T> Display for Traced<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}
