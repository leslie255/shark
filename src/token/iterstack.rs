use std::str::CharIndices;

use crate::error::{
    location::{IntoSourceLoc, Traced},
    Error, ErrorContent,
};

use super::{tokenizer::TokenStream, Token};

#[derive(Debug)]
pub enum IterStackItem<'src> {
    Default(CharIndices<'src>),
    Included(CharIndices<'src>),
    MacroExpand(TokenStream<'src>),
}
#[derive(Debug, Clone)]
pub enum CharOrToken<'src> {
    Char(usize, char),
    Token(Traced<'src, Token<'src>>),
}

impl<'src> CharOrToken<'src> {
    pub fn as_char(&self) -> Option<(usize, char)> {
        if let &Self::Char(i, c) = self {
            Some((i, c))
        } else {
            None
        }
    }
    #[allow(dead_code)]
    pub fn as_token(&self) -> Option<&Traced<'src, Token<'src>>> {
        if let Self::Token(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn is_char_and_eq(&self, rhs: char) -> bool {
        if let &Self::Char(_, lhs) = self {
            rhs == lhs
        } else {
            false
        }
    }
}
impl From<(usize, char)> for CharOrToken<'_> {
    fn from(x: (usize, char)) -> Self {
        Self::Char(x.0, x.1)
    }
}
impl<'src> From<Traced<'src, Token<'src>>> for CharOrToken<'src> {
    fn from(x: Traced<'src, Token<'src>>) -> Self {
        Self::Token(x)
    }
}
impl<'src> Iterator for IterStackItem<'src> {
    type Item = CharOrToken<'src>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            IterStackItem::Default(char_iter) => Some(char_iter.next()?.into()),
            IterStackItem::Included(char_iter) => Some(char_iter.next()?.into()),
            IterStackItem::MacroExpand(token_iter) => Some(token_iter.next()?.into()),
        }
    }
}

/// Because of macros expansions, there are multiple character iterators existing at the same time,
/// they are stored in a stack
/// Everytime a macro expansion is needed, a new iterator will be pushed onto the stack
/// When fetching
/// For fetching a character, a character is attempted to be fetched from the top most of the
/// character, if that iterator has depleted, it will be poped off and the process will be repeated
/// again until the stack is empty
/// In some cases, the iterator will output tokens instead of characters
#[derive(Debug)]
pub struct IterStack<'src> {
    stack: Vec<IterStackItem<'src>>,
}
impl<'src> IterStack<'src> {
    pub fn new(source: &'src str) -> Self {
        let chars_iter = source.char_indices();
        let stack_item = IterStackItem::Default(chars_iter);
        Self {
            stack: vec![stack_item],
        }
    }
    /// Push a new iterator onto the stack with the content of included file
    #[allow(dead_code)]
    pub fn include_source(&mut self, source: &'src str) {
        let chars_iter = source.char_indices();
        let stack_item = IterStackItem::Included(chars_iter);
        self.stack.push(stack_item);
    }
    /// Push a new iterator of tokens onto the stack containing tokens expanded from a macro
    #[allow(dead_code)]
    pub fn expand_macro(&mut self, token_stream: TokenStream<'src>) {
        // TODO: expand macros with arguments
        let stack_item = IterStackItem::MacroExpand(token_stream);
        self.stack.push(stack_item);
    }
}
impl<'src> Iterator for IterStack<'src> {
    type Item = CharOrToken<'src>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let top_iter = self.stack.last_mut()?;
            if let Some(item) = top_iter.next() {
                break Some(item);
            }
            self.stack.pop();
        }
    }
}
pub trait OptionCharOrToken<'a, T> {
    fn err_if_eof(self, loc: impl IntoSourceLoc<'a>) -> Result<T, Error<'a>>;
}
impl<'a> OptionCharOrToken<'a, CharOrToken<'a>> for Option<CharOrToken<'a>> {
    fn err_if_eof(self, loc: impl IntoSourceLoc<'a>) -> Result<CharOrToken<'a>, Error<'a>> {
        self.ok_or(ErrorContent::UnexpectedEOF.wrap(loc))
    }
}
impl<'a> OptionCharOrToken<'a, &'a CharOrToken<'a>> for Option<&'a CharOrToken<'a>> {
    fn err_if_eof(self, loc: impl IntoSourceLoc<'a>) -> Result<&'a CharOrToken<'a>, Error<'a>> {
        self.ok_or(ErrorContent::UnexpectedEOF.wrap(loc))
    }
}
