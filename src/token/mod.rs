use std::fmt::Debug;

use crate::error::location::{IntoSourceLoc, Traced};

pub mod tokenizer;

#[allow(dead_code)]
#[derive(Clone, Copy)]
pub enum NumValue {
    U(u64),
    I(i64),
    F(f64),
}
#[allow(dead_code)]
impl NumValue {
    pub fn as_unsigned(self) -> Option<u64> {
        match self {
            Self::U(u) => Some(u),
            _ => None,
        }
    }

    /// Returns a `i64` value from be bytes, ignoring arithmetics
    pub fn to_be(self) -> i64 {
        i64::from_be_bytes(match self {
            NumValue::U(x) => x.to_be_bytes(),
            NumValue::I(x) => x.to_be_bytes(),
            NumValue::F(x) => x.to_be_bytes(),
        })
    }

    pub fn to_be_bytes(self) -> [u8; 8] {
        match self {
            NumValue::U(x) => x.to_be_bytes(),
            NumValue::I(x) => x.to_be_bytes(),
            NumValue::F(x) => x.to_be_bytes(),
        }
    }

    /// Returns `true` if the num value is [`F`].
    ///
    /// [`F`]: NumValue::F
    #[must_use]
    pub fn is_f(&self) -> bool {
        matches!(self, Self::F(..))
    }

    /// Returns `true` if the num value is either [`I`] or [`U`].
    ///
    /// [`I`]: NumValue::I
    /// [`U`]: NumValue::U
    #[must_use]
    pub fn is_int(&self) -> bool {
        matches!(self, Self::I(..) | Self::U(..))
    }

    pub fn as_f(&self) -> Option<f64> {
        if let &Self::F(v) = self {
            Some(v)
        } else {
            None
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
pub enum Token {
    // --- Values
    /// Identifier name string is sliced from the source string, owned by `BufferedSources`
    Identifier(&'static str),
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
    Typedef,
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
impl Token {
    /// Wrap the token into `Traced<Token>`
    pub fn wrap_loc(self, loc: impl IntoSourceLoc) -> Traced<Self> {
        Traced::new(self, loc.into_source_location())
    }
    pub fn expect_identifier(&self) -> Option<&'static str> {
        match self {
            Token::Identifier(s) => Some(s),
            _ => None,
        }
    }
}
