#![allow(dead_code)]

pub mod translator;

use std::{collections::HashMap, fmt::Debug, ops::Deref};

pub(self) use cranelift::codegen::ir::{types as cl_types, types::Type as ClType};

/// - ADT expanded into multiple variables with basic types
/// - Non-direction expressions as function arguments are flattened
/// - If statements are split and flattened
/// - Loops and if statements are marked with block ID
/// - Variables are turned into ID
/// - Boolean logic operators and bitwise operators are no longer differentiated
/// - All typedefs are gone
#[derive(Debug, Clone)]
pub enum MirNode<'s> {
    Identifier(&'s str),
    Number(&'s str),
    String(Vec<u8>),
    Char(char),
    Bool(bool),
    Array(Vec<u8>),

    VarDef(u64, ClType),
    VarAssign(u64, MirNodeRef<'s>),
    FnCall(&'s str, Vec<MirNodeRef<'s>>),

    Add(MirNodeRef<'s>, MirNodeRef<'s>),
    Sub(MirNodeRef<'s>, MirNodeRef<'s>),
    Mul(MirNodeRef<'s>, MirNodeRef<'s>),
    Div(MirNodeRef<'s>, MirNodeRef<'s>),
    Mod(MirNodeRef<'s>, MirNodeRef<'s>),
    Not(MirNodeRef<'s>, MirNodeRef<'s>),
    And(MirNodeRef<'s>, MirNodeRef<'s>),
    Or(MirNodeRef<'s>, MirNodeRef<'s>),
    Xor(MirNodeRef<'s>, MirNodeRef<'s>),

    Loop(MirLoop<'s>),
    IfThenBreak(MirNodeRef<'s>, u64),
    IfThenContinue(MirNodeRef<'s>, u64),
    If(MirIf<'s>),
    Block(Vec<MirNodeRef<'s>>),

    Break(u64),
    Continue(u64),
    RetVal(MirNodeRef<'s>),
    RetVoid(MirNodeRef<'s>),

    FnDef(MirFnDef<'s>),
    StaticVar(&'s str, MirNodeRef<'s>),
}

/// A loop statement in MIR
#[derive(Debug, Clone)]
pub struct MirLoop<'s> {
    pub block_id: u64,
    pub body: Vec<MirNodeRef<'s>>,
}

/// An if statement in MIR
#[derive(Debug, Clone)]
pub struct MirIf<'s> {
    pub id: u64,
    pub condition: MirNodeRef<'s>,
    pub body: Vec<MirNodeRef<'s>>,
    pub else_block: Option<u64>,
}

/// A function definition in MIR
#[derive(Debug, Clone)]
pub struct MirFnDef<'s> {
    pub name: &'s str,
    pub args: Vec<ClType>,
    pub ret_type: Option<ClType>,
    pub body: MirBlock<'s>,
}

/// An array of MIR nodes, with a header containing information about all the variables defined in
/// this block
#[derive(Debug, Clone)]
pub struct MirBlock<'s> {
    pub body: Vec<MirNodeRef<'s>>,
    /// Information of the variables defined in this block
    pub vars: HashMap<Vec<&'s str>, MirVarInfo>,
}

/// Stores information about a variable
#[derive(Debug, Clone)]
pub struct MirVarInfo {
    pub id: u64,
    pub dtype: ClType,
    pub is_mut: bool,
}

impl From<(u64, ClType, bool)> for MirVarInfo {
    fn from((id, dtype, is_mut): (u64, ClType, bool)) -> Self {
        Self { id, dtype, is_mut }
    }
}

/// A program in MIR
#[derive(Debug, Clone, Default)]
pub struct MirProgram<'s> {
    node_pool: Box<Vec<MirNode<'s>>>,
    pub root_nodes: Vec<MirNodeRef<'s>>,
}

impl<'s> MirProgram<'s> {
    pub fn add_node(&mut self, node: MirNode<'s>) -> MirNodeRef<'s> {
        self.node_pool.push(node);
        let i = self.node_pool.len() - 1;
        MirNodeRef {
            pool: self.node_pool.deref() as *const Vec<MirNode<'s>>,
            i,
        }
    }
}

#[derive(Clone)]
pub struct MirNodeRef<'s> {
    pool: *const Vec<MirNode<'s>>,
    i: usize,
}

impl<'s> Deref for MirNodeRef<'s> {
    type Target = MirNode<'s>;

    fn deref(&self) -> &Self::Target {
        unsafe { (*self.pool).get_unchecked(self.i) }
    }
}

impl Debug for MirNodeRef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}
