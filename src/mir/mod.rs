pub mod builder;

use std::fmt::Debug;

use either::Either;
use index_vec::IndexVec;

use crate::{ast::{type_expr::TypeExpr, Signature}, token::NumValue};

// all variables listed in function head
// control flow is in SSA-style CFG but variables can be mutable

#[derive(Debug, Clone, Default)]
pub struct MirObject {
    pub imported_functions: Vec<Signature>,
    pub functions: Vec<MirFunction>,
}

#[derive(Debug, Clone)]
pub struct VarInfo {
    pub is_mut: bool,
    pub ty: TypeExpr,
    pub name: Option<&'static str>,
}

#[derive(Debug, Clone)]
pub struct MirFunction {
    pub blocks: IndexVec<BlockRef, Block>,
    pub vars: IndexVec<Variable, VarInfo>,
}

#[derive(Debug, Clone, Default)]
pub struct Block {
    pub body: IndexVec<StatementRef, Statement>,
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
    Assign(Lvalue, Operand),
    StaticCall {
        func_name: &'static str,
        args: Vec<Operand>,
        results: Vec<Operand>,
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

#[derive(Clone)]
pub enum Lvalue {
    Deref(Box<Lvalue>),
    Variable(Variable),
}

#[derive(Debug, Clone)]
pub enum Rvalue {
    Number(TypeExpr, NumValue),
    Bool(bool),
    Char(char),
}

#[derive(Clone)]
pub struct Operand(pub Either<Lvalue, Rvalue>);

impl From<Lvalue> for Operand {
    fn from(lval: Lvalue) -> Self {
        Self(Either::Left(lval))
    }
}

impl From<Rvalue> for Operand {
    fn from(rval: Rvalue) -> Self {
        Self(Either::Right(rval))
    }
}

impl Operand {
    pub fn is_lval(&self) -> bool {
        self.0.is_left()
    }

    pub fn is_rval(&self) -> bool {
        self.0.is_right()
    }
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
        lhs: Operand,
        rhs: Operand,
        target: BlockRef,
        otherwise: BlockRef,
    },
    Return(Operand),
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

impl Debug for Lvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Deref(lval) => write!(f, "deref({:?})", lval),
            Self::Variable(var) => var.fmt(f),
        }
    }
}

impl Debug for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            Either::Left(lval) => lval.fmt(f),
            Either::Right(rval) => rval.fmt(f),
        }
    }
}

impl Debug for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "var{}", self.0)
    }
}
