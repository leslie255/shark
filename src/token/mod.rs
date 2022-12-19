use std::fmt::Debug;

use crate::error::location::{IntoSourceLoc, Traced};

pub mod tokenizer;

/// Because of macros expansions, there are multiple character iterators existing at the same time,
/// they are stored in a stack
/// Everytime a macro expansion is needed, a new iterator will be pushed onto the stack
/// When fetching
/// For fetching a character, a character is attempted to be fetched from the top most of the
/// character, if that iterator has depleted, it will be poped off and the process will be repeated
/// again until the stack is empty
/// In some cases, the iterator will output tokens instead of characters
mod iterstack;

#[allow(dead_code)]
#[derive(Clone, Copy)]
pub enum NumValue {
    U(u64),
    I(i64),
    F(f64),
}
impl NumValue {
    pub fn as_unsigned(self) -> Option<u64> {
        match self {
            Self::U(u) => Some(u),
            _ => None,
        }
    }
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
impl From<u64> for NumValue {
    fn from(u: u64) -> Self {
        Self::U(u)
    }
}
impl From<i64> for NumValue {
    fn from(i: i64) -> Self {
        Self::I(i)
    }
}
impl From<f64> for NumValue {
    fn from(f: f64) -> Self {
        Self::F(f)
    }
}

#[derive(Debug, Clone)]
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
    Typedef, // >>=
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
    Comma,           // ,

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
    GrGrEq,
}
impl<'src> Token<'src> {
    /// Wrap the token into `Traced<Token>`
    pub fn wrap_loc(self, loc: impl IntoSourceLoc<'src>) -> Traced<'src, Self> {
        Traced::new(self, loc.into_source_location())
    }
    pub fn expect_identifier(&self) -> Option<&'src str> {
        match self {
            Token::Identifier(s) => Some(s),
            _ => None,
        }
    }
}
