use crate::{
    ast::{pat::Mutability, type_expr::TypeExpr},
    error::{location::SourceLocation, CollectIfErr, Error, ErrorContent},
    token::Token,
};

use super::AstParser;

const TYPE_PARSER_RECURSIVE_LIMIT: usize = 256;

/// Parse a type expression, starting from the token before that expression
#[inline]
pub fn parse_type_expr(
    parser: &mut AstParser,
    current_loc: SourceLocation,
) -> Result<TypeExpr, Error> {
    parse_type_expr_node(parser, current_loc, 0)
}

fn parse_type_expr_node(
    parser: &mut AstParser,
    current_loc: SourceLocation,
    recursive_counter: usize,
) -> Result<TypeExpr, Error> {
    if recursive_counter >= TYPE_PARSER_RECURSIVE_LIMIT {
        return Err(ErrorContent::TypeExprStackOverflow.wrap(current_loc));
    }
    let next_token = parser
        .token_stream
        .next()
        .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
    let token_location = next_token.src_loc();
    Ok(match next_token.into_inner() {
        Token::Identifier("usize") => TypeExpr::USize,
        Token::Identifier("isize") => TypeExpr::ISize,
        Token::Identifier("u64") => TypeExpr::U64,
        Token::Identifier("u128") => TypeExpr::U128,
        Token::Identifier("i128") => TypeExpr::I128,
        Token::Identifier("u32") => TypeExpr::U32,
        Token::Identifier("u16") => TypeExpr::U16,
        Token::Identifier("u8") => TypeExpr::U8,
        Token::Identifier("i64") => TypeExpr::I64,
        Token::Identifier("i32") => TypeExpr::I32,
        Token::Identifier("i16") => TypeExpr::I16,
        Token::Identifier("i8") => TypeExpr::I8,
        Token::Identifier("f64") => TypeExpr::F64,
        Token::Identifier("f32") => TypeExpr::F32,
        Token::Identifier("char") => TypeExpr::Char,
        Token::Identifier("bool") => TypeExpr::Bool,
        Token::Identifier(typename) => TypeExpr::TypeName(typename),
        Token::Exc => TypeExpr::Never,
        Token::AndOp => {
            let mutability = match parser
                .token_stream
                .next_if(|t| matches!(t.inner(), Token::Mut))
            {
                Some(..) => Mutability::Mutable,
                None => Mutability::Const,
            };
            let child = parse_type_expr_node(parser, current_loc, recursive_counter + 1)?;
            TypeExpr::Ref(mutability, Box::new(child))
        }
        Token::Mul => {
            let mutability = match parser
                .token_stream
                .next_if(|t| matches!(t.inner(), Token::Mut))
            {
                Some(_) => Mutability::Mutable,
                None => Mutability::Const,
            };
            let child = parse_type_expr_node(parser, current_loc, recursive_counter + 1)?;
            TypeExpr::Ptr(mutability, Box::new(child))
        }
        Token::RectParenOpen => {
            let peeked_token = parser
                .token_stream
                .peek()
                .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
            let peeked_location = peeked_token.src_loc();
            // If the next token is `]`, it's a slice, if it's an number then it's an array
            // But first make a macro to report a no closing rect paren error because it will
            // be used twice
            match peeked_token.inner() {
                Token::RectParenClose => {
                    parser.token_stream.next();
                    let child =
                        parse_type_expr_node(parser, peeked_location, recursive_counter + 1)?;
                    TypeExpr::Slice(Box::new(child))
                }
                Token::Number(len) => {
                    let len = len
                        .as_unsigned()
                        .ok_or(ErrorContent::NonUIntForArrLen.wrap(peeked_location))
                        .collect_err(&parser.err_collector)
                        .unwrap_or(0);
                    parser.token_stream.next();
                    let peeked_token = parser
                        .token_stream
                        .peek()
                        .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
                    let peeked_location = peeked_token.src_loc();
                    if let Token::RectParenClose = peeked_token.inner() {
                        parser.token_stream.next();
                    } else {
                        return Err(ErrorContent::SliceNoClosingParen.wrap(peeked_location));
                    }
                    let child =
                        parse_type_expr_node(parser, peeked_location, recursive_counter + 1)?;
                    TypeExpr::Array(len, Box::new(child))
                }
                _ => return Err(ErrorContent::SliceNoClosingParen.wrap(peeked_location)),
            }
        }
        Token::RoundParenOpen => {
            let mut children = Vec::<TypeExpr>::new();
            loop {
                let peeked_token = parser
                    .token_stream
                    .peek()
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
                if let Token::RoundParenClose = peeked_token.inner() {
                    parser.token_stream.next();
                    break;
                }
                let child = parse_type_expr_node(parser, current_loc, recursive_counter + 1)?;
                // TODO: continue parsing if there is an error
                children.push(child);
                let peeked_token = parser
                    .token_stream
                    .peek()
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
                let peeked_location = peeked_token.src_loc();
                match peeked_token.inner() {
                    Token::RoundParenClose => (),
                    Token::Comma => {
                        parser.token_stream.next();
                    }
                    _ => {
                        return Err(ErrorContent::ExpectMultipleTokens(vec![
                            Token::RoundParenClose,
                            Token::Comma,
                        ])
                        .wrap(peeked_location))
                    }
                }
            }
            TypeExpr::Tuple(children)
        }
        Token::Fn => {
            let next_token = parser
                .token_stream
                .next()
                .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
            let token_loc = next_token.src_loc();
            match next_token.inner() {
                Token::RoundParenOpen => (),
                _ => return Err(ErrorContent::ExpectToken(Token::RoundParenOpen).wrap(token_loc)),
            }
            let mut args = Vec::<TypeExpr>::new();
            loop {
                let peeked_token = parser
                    .token_stream
                    .peek()
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
                if let Token::RoundParenClose = peeked_token.inner() {
                    parser.token_stream.next();
                    break;
                }
                let child = parse_type_expr_node(parser, current_loc, recursive_counter + 1)?;
                // TODO: continue parsing if there is an error
                args.push(child);
                let peeked_token = parser
                    .token_stream
                    .peek()
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
                let peeked_location = peeked_token.src_loc();
                match peeked_token.inner() {
                    Token::RoundParenClose => (),
                    Token::Comma => {
                        parser.token_stream.next();
                    }
                    _ => {
                        return Err(ErrorContent::ExpectMultipleTokens(vec![
                            Token::RoundParenClose,
                            Token::Comma,
                        ])
                        .wrap(peeked_location))
                    }
                }
            }
            let ret_type = {
                let peeked_token = parser
                    .token_stream
                    .peek()
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
                match peeked_token.inner() {
                    Token::Arrow => {
                        parser.token_stream.next();
                        parse_type_expr_node(parser, current_loc, recursive_counter + 1)?
                    }
                    _ => TypeExpr::void(),
                }
            };
            TypeExpr::Fn(args, Box::new(ret_type))
        }
        _ => {
            return Err(ErrorContent::InvalidTypeExpr.wrap(token_location));
        }
    })
}
