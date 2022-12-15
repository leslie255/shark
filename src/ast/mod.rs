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
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum AstNode<'src> {
    // --- Simple things
    /// Sliced from source
    Identifier(&'src str),
    Number(NumValue),
    /// By index in `Ast.str_pool`
    String(usize),
    Char(char),
    Bool(bool),

    // --- Operators
    /// add, sub, mul, div
    MathOp(MathOpKind, AstNodeRef<'src>, AstNodeRef<'src>),
    /// used when a minus sign is in front of a number, such as `-255`
    MinusNum(AstNodeRef<'src>),
    /// used when a plus sign is in front of a number, such as `+255`
    PlusNum(AstNodeRef<'src>),
    /// and, or, xor
    /// Not including not because not doesn't have an RHS
    BitOp(BitOpKind, AstNodeRef<'src>, AstNodeRef<'src>),
    /// Bitwise NOT (~)
    BitNot(AstNodeRef<'src>),

    Call(AstNodeRef<'src>, Vec<AstNodeRef<'src>>),

    // --- Assignments
    Assign(AstNodeRef<'src>, AstNodeRef<'src>),
    /// +=, -=, *=, /=, %=
    MathOpAssign(MathOpKind, AstNodeRef<'src>, AstNodeRef<'src>),
    /// |=, &=, ^=
    BitOpAssign(BitOpKind, AstNodeRef<'src>, AstNodeRef<'src>),
    Let(&'src str, Option<TypeExpr<'src>>, Option<AstNodeRef<'src>>),

    // --- Reference operations
    TakeRef(AstNodeRef<'src>),
    Deref(AstNodeRef<'src>),

    // -- Control flow
    Block(Vec<AstNodeRef<'src>>),
    FnDef(FnDef<'src>),
    If(IfExpr<'src>),
    Loop(Vec<AstNodeRef<'src>>),

    Return(AstNodeRef<'src>),
}
impl<'src> AstNode<'src> {
    #[inline]
    pub fn traced(self, loc: impl IntoSourceLoc<'src>) -> Traced<'src, Self> {
        Traced::new(self, loc.into_source_location())
    }
}

impl<'src> Default for AstNode<'src> {
    fn default() -> Self {
        Self::Number(0u64.into())
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

#[derive(Clone)]
pub struct FnDef<'a> {
    pub name: &'a str,
    pub args: Vec<(&'a str, TypeExpr<'a>)>,
    pub ret_type: TypeExpr<'a>,
    pub body: Option<Vec<AstNodeRef<'a>>>,
}

impl Debug for FnDef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_fn_head(f, self)?;
        let body = match &self.body {
            Some(b) => b,
            None => return Ok(()),
        };
        if f.alternate() {
            writeln!(f, " {{")?;
            for n in body {
                f.pad("")?;
                writeln!(f, "\t{:?}\n\t{:?}\n", n.src_loc(), n)?;
            }
        } else {
            write!(f, "{{")?;
            for n in body {
                print!("{:?}\t{:?};", n.src_loc(), n);
            }
        }
        write!(f, "}}")?;
        Ok(())
    }
}

#[inline]
fn fmt_fn_head<'src>(f: &mut std::fmt::Formatter<'_>, fn_def: &FnDef<'src>) -> std::fmt::Result {
    write!(f, "{}", fn_def.name.escape_default())?;
    let arg_count = fn_def.args.len();
    match arg_count {
        0 => write!(f, "()")?,
        1 => {
            let (name, dtype) = unsafe { fn_def.args.first().unwrap_unchecked() };
            write!(f, "({}:{:?})", name, dtype)?;
        }
        _ => {
            write!(f, "(")?;
            if f.alternate() {
                for (name, dtype) in fn_def.args[0..fn_def.args.len() - 1].iter() {
                    write!(f, "{}:{:?}, ", name.escape_default(), dtype)?;
                }
            } else {
                for (name, dtype) in fn_def.args[0..fn_def.args.len() - 1].iter() {
                    write!(f, "{}:{:?},", name.escape_default(), dtype)?;
                }
            }
            let (name, dtype) = unsafe { fn_def.args.last().unwrap_unchecked() };
            write!(f, "{}:{:?}", name.escape_default(), dtype)?;
            write!(f, ")")?;
        }
    }
    if f.alternate() {
        write!(f, " -> ")?;
    } else {
        write!(f, "->")?;
    }
    fn_def.ret_type.fmt(f)?;
    Ok(())
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
