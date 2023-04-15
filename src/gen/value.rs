use std::slice;

use super::{ClifType, ClifValue};

/// A higher level value is a collection of 0, 1, or more clif values
#[derive(Clone)]
pub(super) enum Value {
    Empty,
    Single([ClifValue; 1]),
    Multi(Vec<ClifValue>),
}

impl From<ClifValue> for Value {
    fn from(value: ClifValue) -> Self {
        Self::Single([value])
    }
}

impl From<Vec<ClifValue>> for Value {
    fn from(value: Vec<ClifValue>) -> Self {
        Self::Multi(value)
    }
}

impl Value {
    pub fn clif_values(&self) -> ClifValues {
        match self {
            Self::Empty => ClifValues::Empty,
            Self::Single(x) => ClifValues::Single(x[0]),
            Self::Multi(vec) => ClifValues::Multi(vec.iter()),
        }
    }

    pub fn as_slice(&self) -> &[ClifValue] {
        match self {
            Self::Empty => &[],
            Self::Single(x) => x.as_slice(),
            Self::Multi(x) => x.as_slice(),
        }
    }

    pub(super) fn as_single(&self) -> Option<ClifValue> {
        if let &Self::Single(v) = self {
            Some(v[0])
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub(super) enum ClifValues<'short> {
    Empty,
    Single(ClifValue),
    Multi(slice::Iter<'short, ClifValue>),
}

impl Iterator for ClifValues<'_> {
    type Item = ClifValue;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Empty => None,
            &mut Self::Single(x) => {
                *self = ClifValues::Empty;
                Some(x)
            }
            Self::Multi(iter) => iter.next().copied(),
        }
    }
}

/// A collection of clif types, can be created by flattening a TypeExpr
#[derive(Clone)]
pub(super) enum FlatType {
    Empty,
    Single([ClifType; 1]),
    Multi(Vec<ClifType>),
}

impl std::fmt::Debug for FlatType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl FlatType {
    pub fn as_slice(&self) -> &[ClifType] {
        match self {
            FlatType::Empty => &[],
            FlatType::Single(arr) => arr.as_slice(),
            FlatType::Multi(vec) => vec.as_slice(),
        }
    }

    pub fn fields(&self) -> Fields {
        match self {
            FlatType::Empty => Fields::Empty,
            &FlatType::Single([ty]) => Fields::Single(ty),
            FlatType::Multi(x) => Fields::Multi(x.iter()),
        }
    }

    pub fn len(&self) -> usize {
        match self {
            FlatType::Empty => 0,
            FlatType::Single(..) => 1,
            FlatType::Multi(vec) => vec.len(),
        }
    }
}

impl From<ClifType> for FlatType {
    fn from(value: ClifType) -> Self {
        Self::Single([value])
    }
}

impl From<Vec<ClifType>> for FlatType {
    fn from(value: Vec<ClifType>) -> Self {
        Self::Multi(value)
    }
}

#[derive(Debug, Clone)]
pub(super) enum Fields<'short> {
    Empty,
    Single(ClifType),
    Multi(slice::Iter<'short, ClifType>),
}

impl Iterator for Fields<'_> {
    type Item = ClifType;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            &mut Fields::Empty => None,
            &mut Fields::Single(x) => {
                *self = Fields::Empty;
                Some(x)
            }
            Fields::Multi(iter) => iter.next().copied(),
        }
    }
}
