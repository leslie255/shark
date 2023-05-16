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
#[derive(Debug, Default)]
pub struct Ast {
    node_pool: Box<Vec<Traced<AstNode>>>,
    pub str_pool: Vec<String>,
    pub root_nodes: Vec<AstNodeRef>,
}

/// Type checked AST with attached type informations for variables
/// Wrapped as another type to prevent backflowing of data
#[derive(Debug, Default)]
pub struct CookedAst(pub(super) Ast);
impl Deref for CookedAst {
    type Target = Ast;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Ast {
    /// Add a new node to pool
    /// Returns a reference to that node
    #[must_use]
    pub fn add_node(&mut self, new_node: Traced<AstNode>) -> AstNodeRef {
        self.node_pool.push(new_node);
        let i = self.node_pool.len() - 1;
        AstNodeRef {
            pool: self.node_pool.as_mut() as *mut Vec<Traced<AstNode>>,
            i,
        }
    }
    /// Add a new string to `str_pool` and return the index of that string
    pub fn add_str(&mut self, str: String) -> usize {
        self.str_pool.push(str);
        self.str_pool.len() - 1
    }

    /// Get the node pool for debug
    pub unsafe fn node_pool(&self) -> *const Vec<Traced<AstNode>> {
        self.node_pool.as_ref()
    }
}

/// A node inside an AST
#[derive(Debug)]
pub enum AstNode {
    // --- Simple things
    // Global identifier
    Identifier(&'static str),
    Number(NumValue),
    /// By index in `Ast.str_pool`
    String(usize),
    Char(char),
    Bool(bool),
    Array(Vec<AstNodeRef>),

    // --- Operators
    // -- Binary operators
    MathOp(MathOpKind, AstNodeRef, AstNodeRef),
    BitOp(BitOpKind, AstNodeRef, AstNodeRef),
    BoolOp(BoolOpKind, AstNodeRef, AstNodeRef),
    Cmp(CmpKind, AstNodeRef, AstNodeRef),
    MemberAccess(AstNodeRef, AstNodeRef),

    // -- Singular operators
    BitNot(AstNodeRef),
    BoolNot(AstNodeRef),
    /// used when a minus sign is in front of a number, such as `-255`
    UnarySub(AstNodeRef),
    /// used when a plus sign is in front of a number, such as `+255`
    UnaryAdd(AstNodeRef),

    Call(AstNodeRef, Vec<AstNodeRef>),

    // --- Assignments
    Let(AstNodeRef, Option<TypeExpr>, Option<AstNodeRef>),
    Assign(AstNodeRef, AstNodeRef),
    /// +=, -=, *=, /=, %=
    MathOpAssign(MathOpKind, AstNodeRef, AstNodeRef),
    /// |=, &=, ^=
    BitOpAssign(BitOpKind, AstNodeRef, AstNodeRef),

    // --- Reference operations
    TakeRef(AstNodeRef),
    Deref(AstNodeRef),

    // -- Control flow
    Block(Vec<AstNodeRef>),
    FnDef(Function),
    If(IfExpr),
    Loop(Vec<AstNodeRef>),
    Return(Option<AstNodeRef>),
    Break,
    Continue,
    Tail(AstNodeRef),

    Typecast(AstNodeRef, TypeExpr),

    // type definitions
    TypeDef(&'static str, TypeExpr),
    StructDef(StructOrUnionDef),
    UnionDef(StructOrUnionDef),
    EnumDef(EnumDef),

    Tuple(Vec<AstNodeRef>),
}
impl AstNode {
    /// Create a `Traced<AstNode> from this `AstNode`
    ///
    /// # Safety
    ///
    /// `loc` must be a valid source location
    #[inline]
    pub fn traced(self, loc: impl IntoSourceLoc) -> Traced<Self> {
        Traced::new(self, loc.into_source_location())
    }

    /// Whether this AST node allows a semicolon to be omitted
    #[inline]
    pub fn allow_omit_semicolon(&self) -> bool {
        matches!(
            self,
            &AstNode::Block(_)
                | &AstNode::FnDef(_)
                | &AstNode::If(_)
                | &AstNode::Loop(_)
                | &AstNode::StructDef(_)
                | &AstNode::UnionDef(_)
                | &AstNode::EnumDef(_)
        )
    }

    pub fn as_identifier(&self) -> Option<&'static str> {
        if let &Self::Identifier(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the ast node is [`Return`].
    ///
    /// [`Return`]: AstNode::Return
    #[must_use]
    pub const fn is_return(&self) -> bool {
        matches!(self, Self::Return(..))
    }
}

impl Default for AstNode {
    fn default() -> Self {
        Self::Number(0u64.into())
    }
}

/// A reference to an AstNode
/// Should only refer to an AstNode owned by Ast
/// Should only be initialized by an Ast
#[derive(Clone, Copy)]
pub struct AstNodeRef {
    pool: *const Vec<Traced<AstNode>>,
    i: usize,
}
impl Deref for AstNodeRef {
    type Target = Traced<AstNode>;
    fn deref(&self) -> &Self::Target {
        unsafe { (*self.pool).get_unchecked(self.i) }
    }
}
impl Debug for AstNodeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}

/// Signature of a function
#[derive(Clone)]
pub struct Signature {
    pub args: Vec<(&'static str, TypeExpr)>,
    pub ret_type: TypeExpr,
}

impl Debug for Signature {
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
pub struct Function {
    pub name: &'static str,
    pub sign: Signature,
    pub body: Option<Vec<AstNodeRef>>,
}

impl Function {
    pub fn new(name: &'static str, sign: Signature, body: Option<Vec<AstNodeRef>>) -> Self {
        Self { name, sign, body }
    }
}

impl Debug for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_fn_head(f, self)?;
        let body = match &self.body {
            Some(b) => b,
            None => return Ok(()),
        };
        if f.alternate() {
            writeln!(f, " {{")?;
            for n in body {
                let n = n.deref();
                f.pad("")?;
                writeln!(f, "\t{:?}\n\t{:?}\n", n.src_loc(), n)?;
            }
        } else {
            write!(f, "{{")?;
            for n in body.iter() {
                let n = n.deref();
                write!(f, "{:?}\t{:?};", n.src_loc(), n)?;
            }
        }
        write!(f, "}},")?;
        if f.alternate() {
            writeln!(f, "")?;
        }
        Ok(())
    }
}

/// Formats the head of a function definition.
#[inline]
fn fmt_fn_head(f: &mut std::fmt::Formatter<'_>, fn_def: &Function) -> std::fmt::Result {
    write!(f, "{}", fn_def.name.escape_default())?;
    fn_def.sign.fmt(f)?;
    Ok(())
}

#[derive(Debug, Clone)]
pub struct IfExpr {
    /// Condition and body
    /// `if` and `else if` blocks are treated the same
    pub if_blocks: Vec<(AstNodeRef, Vec<AstNodeRef>)>,
    pub else_block: Option<Vec<AstNodeRef>>,
}

/// Definition information of a struct or union
#[derive(Clone)]
pub struct StructOrUnionDef {
    pub name: &'static str,
    pub fields: Vec<(&'static str, TypeExpr)>,
}

impl Debug for StructOrUnionDef {
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
pub struct EnumDef {
    pub name: &'static str,
    pub cases: Vec<&'static str>,
}

impl Debug for EnumDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name)?;
        f.write_char(' ')?;
        f.debug_set().entries(self.cases.iter()).finish()?;
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
