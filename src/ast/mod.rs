#![allow(dead_code)]

mod parser;
mod type_expr;

use std::{fmt::Debug, ops::Deref};

use crate::{error::location::Traced, token::NumValue};
use type_expr::TypeExpr;

/// All AST nodes are stored inside a pool
/// Uses `AstNodeRef` for inter-reference between nodes
#[derive(Debug, Clone)]
pub struct Ast<'a> {
    node_pool: Vec<Traced<'a, AstNode<'a>>>,
    pub str_pool: Vec<String>,
    pub root_nodes: Vec<Traced<'a, AstNodeRef<'a>>>,
}

impl<'a> Ast<'a> {
    /// Add a new node to pool
    /// Returns a reference to that node
    pub fn add_to_pool(&mut self, new_node: Traced<'a, AstNode<'a>>) -> AstNodeRef<'a> {
        self.node_pool.push(new_node);
        let node_ref = self.node_pool.last().unwrap();
        AstNodeRef {
            raw_ptr: node_ref as *const Traced<'a, AstNode>,
        }
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
    /// ~=
    BitNotAssign(AstNodeRef<'a>, AstNodeRef<'a>),
    Let(&'a str, Option<TypeExpr<'a>>, Option<AstNodeRef<'a>>),

    // --- Reference operations
    TakeRef(AstNodeRef<'a>),
    Deref(AstNodeRef<'a>),

    // -- Control flow
    FnDef(FnDef<'a>),
    If(IfExpr<'a>),
    Loop(Vec<AstNodeRef<'a>>),
}

/// A reference to an AstNode
/// Should only refer to an AstNode owned by Ast
/// Cannot be initialized independently
#[derive(Clone, Copy)]
pub struct AstNodeRef<'a> {
    raw_ptr: *const Traced<'a, AstNode<'a>>,
}
impl<'a> Deref for AstNodeRef<'a> {
    type Target = AstNode<'a>;

    fn deref(&self) -> &Self::Target {
        unsafe { self.raw_ptr.as_ref().unwrap() }
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
}

/// Type of a bitwise operations
/// Not including `not`, because `not` doesn't have an RHS
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitOpKind {
    And,
    Or,
    Xor,
}
