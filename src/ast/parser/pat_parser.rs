use crate::{
    ast::pat::{Mutability, Pattern},
    error::{
        location::{SourceLocation, Traced},
        Error, ErrorContent,
    },
    token::Token,
};

use super::AstParser;

/// Parse a type expression, starting from the token before that expression
#[inline]
pub fn parse_pat(
    parser: &mut AstParser,
    current_loc: SourceLocation,
) -> Result<Traced<Pattern>, Error> {
    parse_pat_node(parser, current_loc)
}

fn parse_pat_node(
    parser: &mut AstParser,
    current_loc: SourceLocation,
) -> Result<Traced<Pattern>, Error> {
    let next_token = parser
        .token_stream
        .next()
        .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
    let token_location = next_token.src_loc();
    match next_token.into_inner() {
        Token::Mut => {
            let child = parse_pat_node(parser, current_loc)?;
            match child.inner() {
                Pattern::Var(_, id) => Ok(Pattern::Var(Mutability::Mutable, id)
                    .traced(token_location.join(child.src_loc()))),
                Pattern::Tuple(..) => Ok(child),
            }
        }
        Token::Identifier(id) => Ok(Pattern::Var(Mutability::Const, id).traced(token_location)),
        _ => Err(ErrorContent::UnexpectedToken.wrap(token_location)),
    }
}
