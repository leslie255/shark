pub mod parser;
pub mod type_expr;

use std::{
    fmt::{Debug, Write},
    ops::Deref,
};

use crate::{
    error::location::{IntoSourceLoc, Traced},
    token::NumValue,
};
use type_expr::TypeExpr;

/// All AST nodes are stored inside a pool
/// Uses `AstNodeRef` for inter-reference between nodes
#[derive(Debug, Clone, Default)]
pub struct Ast<'src> {
    node_pool: Box<Vec<Traced<'src, AstNode<'src>>>>,
    pub str_pool: Vec<String>,
    pub root_nodes: Vec<AstNodeRef<'src>>,
}

impl<'src> Ast<'src> {
    /// Add a new node to pool
    /// Returns a reference to that node
    #[must_use]
    pub fn add_node(&mut self, new_node: Traced<'src, AstNode<'src>>) -> AstNodeRef<'src> {
        self.node_pool.push(new_node);
        let i = self.node_pool.len() - 1;
        let node_ref = AstNodeRef {
            pool: self.node_pool.deref() as *const Vec<Traced<'src, AstNode<'src>>>,
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
pub enum AstNode<'src> {
    // --- Simple things
    /// Sliced from source
    Identifier(&'src str),
    Number(NumValue),
    /// By index in `Ast.str_pool`
    String(usize),
    Char(char),
    Bool(bool),
    Array(Vec<AstNodeRef<'src>>),

    // --- Operators
    // -- Binary operators
    MathOp(MathOpKind, AstNodeRef<'src>, AstNodeRef<'src>),
    BitOp(BitOpKind, AstNodeRef<'src>, AstNodeRef<'src>),
    BoolOp(BoolOpKind, AstNodeRef<'src>, AstNodeRef<'src>),
    Cmp(CmpKind, AstNodeRef<'src>, AstNodeRef<'src>),
    MemberAccess(AstNodeRef<'src>, AstNodeRef<'src>),

    // -- Singular operators
    BitNot(AstNodeRef<'src>),
    BoolNot(AstNodeRef<'src>),
    /// used when a minus sign is in front of a number, such as `-255`
    MinusNum(AstNodeRef<'src>),
    /// used when a plus sign is in front of a number, such as `+255`
    PlusNum(AstNodeRef<'src>),

    Call(AstNodeRef<'src>, Vec<AstNodeRef<'src>>),

    // --- Assignments
    Let(&'src str, Option<TypeExpr<'src>>, Option<AstNodeRef<'src>>),
    Assign(AstNodeRef<'src>, AstNodeRef<'src>),
    /// +=, -=, *=, /=, %=
    MathOpAssign(MathOpKind, AstNodeRef<'src>, AstNodeRef<'src>),
    /// |=, &=, ^=
    BitOpAssign(BitOpKind, AstNodeRef<'src>, AstNodeRef<'src>),

    // --- Reference operations
    TakeRef(AstNodeRef<'src>),
    Deref(AstNodeRef<'src>),

    // -- Control flow
    Block(Vec<AstNodeRef<'src>>),
    FnDef(FnDef<'src>),
    If(IfExpr<'src>),
    Loop(Vec<AstNodeRef<'src>>),
    Return(Option<AstNodeRef<'src>>),
    Break,
    Continue,

    Typecast(AstNodeRef<'src>, TypeExpr<'src>),

    // type definitions
    TypeDef(&'src str, TypeExpr<'src>),
    StructDef(StructOrUnionDef<'src>),
    UnionDef(StructOrUnionDef<'src>),
    EnumDef(EnumDef<'src>),

    Tuple(Vec<Traced<'src, AstNode<'src>>>),
}
impl<'src> AstNode<'src> {
    /// Create a `Traced<AstNode> from this `AstNode`
    ///
    /// # Safety
    ///
    /// `loc` must be a valid source location
    #[inline]
    pub fn traced(self, loc: impl IntoSourceLoc<'src>) -> Traced<'src, Self> {
        Traced::new(self, loc.into_source_location())
    }

    /// Whether this AST node allows a semicolon to be omitted
    #[inline]
    pub fn allow_omit_semicolon(&self) -> bool {
        match self {
            &AstNode::Block(_)
            | &AstNode::FnDef(_)
            | &AstNode::If(_)
            | &AstNode::Loop(_)
            | &AstNode::StructDef(_)
            | &AstNode::UnionDef(_)
            | &AstNode::EnumDef(_) => true,
            _ => false,
        }
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

    /// Dereferences the AstNodeRef to the AstNode it points to
    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { (*self.pool).get_unchecked(self.i) }
    }
}
impl<'a> Debug for AstNodeRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}

/// Signature of a function
#[derive(Clone)]
pub struct FnSignature<'a> {
    pub args: Vec<(&'a str, TypeExpr<'a>)>,
    pub ret_type: TypeExpr<'a>,
}

impl Debug for FnSignature<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let arg_count = self.args.len();
        match arg_count {
            0 => write!(f, "()")?,
            1 => {
                let (name, dtype) = unsafe { self.args.first().unwrap_unchecked() };
                write!(f, "({}:{:?})", name, dtype)?;
            }
            _ => {
                write!(f, "(")?;
                if f.alternate() {
                    for (name, dtype) in self.args[0..self.args.len() - 1].iter() {
                        write!(f, "{}:{:?}, ", name.escape_default(), dtype)?;
                    }
                } else {
                    for (name, dtype) in self.args[0..self.args.len() - 1].iter() {
                        write!(f, "{}:{:?},", name.escape_default(), dtype)?;
                    }
                }
                let (name, dtype) = unsafe { self.args.last().unwrap_unchecked() };
                write!(f, "{}:{:?}", name.escape_default(), dtype)?;
                write!(f, ")")?;
            }
        }
        if f.alternate() {
            write!(f, " -> ")?;
        } else {
            write!(f, "->")?;
        }
        self.ret_type.fmt(f)?;
        Ok(())
    }
}

#[derive(Clone)]
pub struct FnDef<'a> {
    pub name: &'a str,
    pub sign: FnSignature<'a>,
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

/// Formats the head of a function definition.
#[inline]
fn fmt_fn_head<'src>(f: &mut std::fmt::Formatter<'_>, fn_def: &FnDef<'src>) -> std::fmt::Result {
    write!(f, "{}", fn_def.name.escape_default())?;
    fn_def.sign.fmt(f)?;
    Ok(())
}

#[derive(Debug, Clone)]
pub struct IfExpr<'a> {
    /// Condition and body
    /// `if` and `else if` blocks are treated the same
    pub if_blocks: Vec<(AstNodeRef<'a>, Vec<AstNodeRef<'a>>)>,
    pub else_block: Option<Vec<AstNodeRef<'a>>>,
}

/// Definition information of a struct or union
#[derive(Clone)]
pub struct StructOrUnionDef<'a> {
    pub name: &'a str,
    pub fields: Vec<(&'a str, TypeExpr<'a>)>,
}

impl Debug for StructOrUnionDef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name)?;
        f.write_char(' ')?;
        f.debug_map()
            .entries(self.fields.iter().map(|&(ref k, ref v)| (k, v)))
            .finish()?;
        Ok(())
    }
}

/// Definition information of an enum
#[derive(Clone)]
pub struct EnumDef<'a> {
    pub name: &'a str,
    pub cases: Vec<&'a str>,
}

impl Debug for EnumDef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name)?;
        f.write_char(' ')?;
        f.debug_set()
            .entries(self.cases.iter().map(|v| (v)))
            .finish()?;
        Ok(())
    }
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

/// Type of a bitwise operations
/// Not including `not`, because `not` doesn't have an RHS
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolOpKind {
    And,
    Or,
}

/// Type of a bitwise operations
/// Not including `not`, because `not` doesn't have an RHS
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpKind {
    Eq,
    Neq,
    Gr,
    Le,
    GrEq,
    LeEq,
}
