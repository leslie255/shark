#![allow(dead_code)]

pub mod parser;
pub mod type_expr;

use std::{fmt::Debug, ops::Deref};

use crate::{
    error::location::{IntoSourceLoc, Traced},
    token::NumValue,
};
use type_expr::TypeExpr;

/// All AST nodes are stored inside a pool
/// Uses `AstNodeRef` for inter-reference between nodes
#[derive(Debug, Clone, Default)]
pub struct Ast<'src> {
    node_pool: Vec<Traced<'src, AstNode<'src>>>,
    pub str_pool: Vec<String>,
    pub root_nodes: Vec<Traced<'src, AstNodeRef<'src>>>,
}

impl<'src> Ast<'src> {
    /// Add a new node to pool
    /// Returns a reference to that node
    #[must_use]
    pub fn add_node(&mut self, new_node: Traced<'src, AstNode<'src>>) -> AstNodeRef<'src> {
        self.node_pool.push(new_node);
        let i = self.node_pool.len() - 1;
        let node_ref = AstNodeRef {
            pool: &self.node_pool as *const Vec<Traced<'src, AstNode<'src>>>,
            i,
        };
        node_ref
    }
    /// Add a new string to `str_pool` and return the index of that string
    pub fn add_str(&mut self, str: String) -> usize {
        self.str_pool.push(str);
        self.str_pool.len() - 1
    }
}

/// A node inside an AST
#[derive(Debug, Clone)]
pub enum AstNode<'a> {
    // --- Simple things
    /// Sliced from source
    Identifier(&'a str),
    Number(NumValue),
    /// By index in `Ast.str_pool`
    String(usize),
    Char(char),

    // --- Operators
    /// add, sub, mul, div
    MathOp(MathOpKind, AstNodeRef<'a>, AstNodeRef<'a>),
    /// and, or, xor
    /// Not including not because not doesn't have an RHS
    BitOp(BitOpKind, AstNodeRef<'a>, AstNodeRef<'a>),
    /// Bitwise NOT (~)
    BitNot(AstNodeRef<'a>),

    // --- Assignments
    Assign(AstNodeRef<'a>, AstNodeRef<'a>),
    /// +=, -=, *=, /=, %=
    MathOpAssign(MathOpKind, AstNodeRef<'a>, AstNodeRef<'a>),
    /// |=, &=, ^=
    BitOpAssign(BitOpKind, AstNodeRef<'a>, AstNodeRef<'a>),
    Let(&'a str, Option<TypeExpr<'a>>, Option<AstNodeRef<'a>>),

    // --- Reference operations
    TakeRef(AstNodeRef<'a>),
    Deref(AstNodeRef<'a>),

    // -- Control flow
    FnDef(FnDef<'a>),
    If(IfExpr<'a>),
    Loop(Vec<AstNodeRef<'a>>),
}
impl<'src> AstNode<'src> {
    pub fn wrap_loc(self, loc: impl IntoSourceLoc<'src>) -> Traced<'src, Self> {
        Traced::new(self, loc.into_source_location())
    }
}

/// A reference to an AstNode
/// Should only refer to an AstNode owned by Ast
/// Should only be initialized by an Ast
#[derive(Clone, Copy)]
pub struct AstNodeRef<'a> {
    pool: *const Vec<Traced<'a, AstNode<'a>>>,
    i: usize,
}
impl<'a> Deref for AstNodeRef<'a> {
    type Target = Traced<'a, AstNode<'a>>;

    fn deref(&self) -> &Self::Target {
        unsafe { self.pool.as_ref().unwrap().get(self.i).unwrap() }
    }
}
impl<'a> Debug for AstNodeRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}

#[derive(Debug, Clone)]
pub struct FnDef<'a> {
    pub name: &'a str,
    pub args: Vec<(&'a str, TypeExpr<'a>)>,
    pub ret_type: TypeExpr<'a>,
    pub body: Option<Vec<AstNodeRef<'a>>>,
}

#[derive(Debug, Clone)]
pub struct IfExpr<'a> {
    /// Condition and body
    /// `if` and `else if` blocks are treated the same
    pub if_blocks: Vec<(AstNodeRef<'a>, Vec<AstNodeRef<'a>>)>,
    pub else_block: Option<Vec<AstNodeRef<'a>>>,
}

/// Type of an arithmatic operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MathOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

/// Type of a bitwise operations
/// Not including `not`, because `not` doesn't have an RHS
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitOpKind {
    And,
    Or,
    Xor,

    Sl,
    Sr,
}
