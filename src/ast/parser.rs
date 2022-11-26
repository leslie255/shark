use std::iter::Peekable;

use crate::token::tokenizer::TokenStream;

use super::{Ast, AstNode};

pub struct AstParser<'a> {
    token_stream: Peekable<TokenStream<'a>>,
    ast: Ast<'a>,
}
impl<'a> Iterator for AstParser<'a> {
    type Item = AstNode<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}
