pub mod builder;

use std::fmt::Debug;

use index_vec::IndexVec;

use crate::{
    ast::{type_expr::TypeExpr, Signature},
    token::NumValue,
};

// all variables listed in function head
// control flow is in SSA-style CFG but variables can be mutable

#[derive(Debug, Clone, Default)]
pub struct MirObject {
    pub imported_functions: Vec<Signature>,
    pub functions: Vec<MirFunction>,
}

#[derive(Clone)]
pub struct VarInfo {
    pub is_mut: bool,
    pub ty: TypeExpr,
    pub name: Option<&'static str>,
}

#[derive(Clone)]
pub struct MirFunction {
    pub vars: IndexVec<Variable, VarInfo>,
    pub blocks: IndexVec<BlockRef, Block>,
}

#[derive(Debug, Clone, Default)]
pub struct Block {
    pub body: IndexVec<StatementRef, Statement>,
    pub terminator: Option<Terminator>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockRef(usize);
impl index_vec::Idx for BlockRef {
    fn from_usize(idx: usize) -> Self {
        Self(idx)
    }
    fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone)]
pub enum Statement {
    Assign(Place, Value),
    StaticCall {
        func_name: &'static str,
        args: Vec<Value>,
        result: Place,
    },
    /// TODO
    DynCall,
    /// Used for deleting a statement
    Nop,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StatementRef(usize);
impl index_vec::Idx for StatementRef {
    fn from_usize(idx: usize) -> Self {
        Self(idx)
    }
    fn index(self) -> usize {
        self.0
    }
}

/// An lvalue can be used as LHS of assignment, but it can also be used to just yield a value
/// TODO: projections
#[derive(Clone)]
pub struct Place {
    pub local: Variable,
    pub projections: Vec<!>,
}

impl Place {
    pub fn no_projection(local: Variable) -> Self {
        Self {
            local,
            projections: Vec::new(),
        }
    }
}

#[derive(Clone)]
pub enum Value {
    Number(TypeExpr, NumValue),
    Bool(bool),
    Char(char),
    Copy(Place),
    AddrOf(Place),
    Void,
    Unreachable,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Variable(usize);
impl index_vec::Idx for Variable {
    fn from_usize(idx: usize) -> Self {
        Self(idx)
    }
    fn index(self) -> usize {
        self.0
    }
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Jmp(BlockRef),
    CondJmp {
        cond: CmpKind,
        lhs: Value,
        rhs: Value,
        target: BlockRef,
        otherwise: BlockRef,
    },
    Return(Value),
    Unreachable,
}

#[derive(Debug, Clone)]
pub enum CmpKind {
    Ne,
    Eq,
    Gr,
    Le,
    GrEq,
    LeEq,
}

impl Debug for BlockRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "block{}", self.0)
    }
}

impl Debug for StatementRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "stmt{}", self.0)
    }
}

impl Debug for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "var{}", self.0)
    }
}

impl Debug for Place {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO: projections
        self.local.fmt(f)
    }
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(ty, num) => write!(f, "num({:?} as {:?})", num, ty),
            Self::Bool(b) => write!(f, "bool({})", b),
            Self::Char(ch) => write!(f, "char('{}')", ch.escape_unicode()),
            Self::Copy(place) => write!(f, "copy({:?})", place),
            Self::AddrOf(place) => write!(f, "addr({:?})", place),
            Self::Void => write!(f, "void"),
            Self::Unreachable => write!(f, "unreachable"),
        }
    }
}

/// A format "functor" for showing a variable table inside a function
struct VarsFormatter<'short>(&'short IndexVec<Variable, VarInfo>);
impl<'short> Debug for VarsFormatter<'short> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.0.iter_enumerated()).finish()
    }
}

impl Debug for VarInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_mut {
            write!(f, "mut ")?;
        } else {
            write!(f, "const ")?;
        }
        write!(f, "{:?}", self.ty)?;
        if let Some(name) = self.name {
            write!(f, " => {:?}", name)?;
        }
        Ok(())
    }
}

impl Debug for MirFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MirFunction")
            .field("vars", &VarsFormatter(&self.vars))
            .field("blocks", &self.blocks)
            .finish()
    }
}
