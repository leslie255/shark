#![allow(dead_code)]
use std::fmt::Debug;

use crate::error::location::{IntoSourceLoc, Traced};

pub mod tokenizer;

#[derive(Clone, Copy, PartialEq)]
pub enum NumValue {
    U(u64),
    I(i64),
    F(f64),
}
impl Debug for NumValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::U(val) => write!(f, "{}u", val),
            Self::I(val) => write!(f, "{}i", val),
            Self::F(val) => write!(f, "{}f", val),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token<'a> {
    // --- Values
    /// Identifier name string is sliced from the source string, owned by `BufferedSources`
    Identifier(&'a str),
    Number(NumValue),
    Character(char),
    /// Unlike `Identifier`, contents of string literals are owned and not sliced from the source
    /// string because of possible escape sequences
    String(String),

    // --- Keywards
    As,
    Break,
    Continue,
    Else,
    Enum,
    Extern,
    False,
    Fn,
    For,
    If,
    Let,
    Loop,
    Mut,
    Pub,
    Return,
    Static,
    Struct,
    True,
    Union,
    While,

    // --- Operators
    // Inambiguous
    // (When encountered by the tokenizer, it doesn't need any peeking)
    Squiggle,        // ~
    RoundParenOpen,  // (
    RoundParenClose, // )
    RectParenOpen,   // [
    RectParenClose,  // ]
    BraceOpen,       // {
    BraceClose,      // }
    Colon,           // :
    Semicolon,       // ;
    Dot,             // .

    // 2-levels ambiguous
    // (Tokenizer has to peek 1 character forward)
    Add,   // +
    Sub,   // -
    Mul,   // *
    Div,   // /
    Mod,   // %
    OrOp,  // |
    AndOp, // &
    XorOp, // ^
    Eq,    // =
    Exc,   // !

    AddEq,  // +=
    SubEq,  // -=
    Arrow,  // ->
    MulEq,  // *=
    DivEq,  // /=
    ModEq,  // %=
    OrEq,   // |=
    OrOr,   // ||
    AndEq,  // &=
    AndAnd, // &&
    XorEq,  // ^=
    EqEq,   // ==
    ExcEq,  // !=

    // 3-levels ambiguous
    // (Tokenizer has to peek 2 character forward)
    Le, // <
    Gr, // >

    LeLe, // <<
    LeEq, // <=
    GrEq, // >=
    GrGr, // >>

    LeLeEq, // <<=
    GrGrEq, // >>=
}
impl<'a> Token<'a> {
    pub fn wrap_loc(self, loc: impl IntoSourceLoc<'a>) -> Traced<'a, Self> {
        Traced::new(self, loc.into_source_location())
    }
}
