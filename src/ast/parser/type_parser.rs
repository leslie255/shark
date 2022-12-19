use crate::{
    ast::type_expr::{TypeExpr, TypeExprNode},
    error::{location::SourceLocation, CollectIfErr, Error, ErrorContent},
    token::Token,
};

use super::AstParser;

const TYPE_PARSER_RECURSIVE_LIMIT: usize = 256;

/// Parse a type expression, starting from the token before that expression
/// Returns `None` if unexpected EOF, errors handled internally
#[inline]
#[must_use]
pub fn parse_type_expr<'src>(
    parser: &mut AstParser<'src>,
    current_loc: SourceLocation<'src>,
) -> Result<TypeExpr<'src>, Error<'src>> {
    let mut type_expr = TypeExpr {
        pool: Vec::new(),
        root: 0,
    };
    let root = parse_type_expr_node(parser, current_loc, 0, &mut type_expr)?;
    type_expr.root = root;
    Ok(type_expr)
}

#[must_use]
fn parse_type_expr_node<'src>(
    parser: &mut AstParser<'src>,
    current_loc: SourceLocation<'src>,
    recursive_counter: usize,
    type_expr: &mut TypeExpr<'src>,
) -> Result<usize, Error<'src>> {
    if recursive_counter >= TYPE_PARSER_RECURSIVE_LIMIT {
        return Err(ErrorContent::TypeExprStackOverflow.wrap(current_loc));
    }
    let next_token = parser
        .token_stream
        .next()
        .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
    let token_location = next_token.src_loc();
    let node = match next_token.into_inner() {
        Token::Identifier("usize") => TypeExprNode::USize,
        Token::Identifier("isize") => TypeExprNode::ISize,
        Token::Identifier("u64") => TypeExprNode::U64,
        Token::Identifier("u32") => TypeExprNode::U32,
        Token::Identifier("u16") => TypeExprNode::U16,
        Token::Identifier("u8") => TypeExprNode::U8,
        Token::Identifier("i64") => TypeExprNode::I64,
        Token::Identifier("i32") => TypeExprNode::I32,
        Token::Identifier("i16") => TypeExprNode::I16,
        Token::Identifier("i8") => TypeExprNode::I8,
        Token::Identifier("f64") => TypeExprNode::F64,
        Token::Identifier("f32") => TypeExprNode::F32,
        Token::Identifier("char32") => TypeExprNode::Char32,
        Token::Identifier("char8") => TypeExprNode::Char8,
        Token::Identifier("bool") => TypeExprNode::Bool,
        Token::Identifier(typename) => TypeExprNode::TypeName(typename),
        Token::AndOp => {
            let child_i =
                parse_type_expr_node(parser, current_loc, recursive_counter + 1, type_expr)?;
            TypeExprNode::Ref(child_i)
        }
        Token::Mul => {
            let child_i =
                parse_type_expr_node(parser, current_loc, recursive_counter + 1, type_expr)?;
            TypeExprNode::Ptr(child_i)
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
            macro_rules! ret_no_closing_paren_err {
                ($loc: expr) => {{
                    return Err(ErrorContent::SliceNoClosingParen.wrap($loc));
                }};
            }
            match peeked_token.inner() {
                Token::RectParenClose => {
                    parser.token_stream.next();
                    let child_i = parse_type_expr_node(
                        parser,
                        peeked_location,
                        recursive_counter + 1,
                        type_expr,
                    )?;
                    TypeExprNode::Slice(child_i)
                }
                Token::Number(len) => {
                    let len = len
                        .as_unsigned()
                        .ok_or(ErrorContent::NonUIntForArrLen.wrap(peeked_location))
                        .collect_err(parser.err_collector)
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
                        ret_no_closing_paren_err!(peeked_location)
                    }
                    let child_i = parse_type_expr_node(
                        parser,
                        peeked_location,
                        recursive_counter + 1,
                        type_expr,
                    )?;
                    TypeExprNode::Array(len, child_i)
                }
                _ => ret_no_closing_paren_err!(peeked_location),
            }
        }
        Token::RoundParenOpen => {
            let mut children = Vec::<usize>::new();
            loop {
                let peeked_token = parser
                    .token_stream
                    .peek()
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
                if let Token::RoundParenClose = peeked_token.inner() {
                    parser.token_stream.next();
                    break;
                }
                let child =
                    parse_type_expr_node(parser, current_loc, recursive_counter + 1, type_expr)?;
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
            TypeExprNode::Tuple(children)
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
            let mut args = Vec::<usize>::new();
            loop {
                let peeked_token = parser
                    .token_stream
                    .peek()
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))?;
                if let Token::RoundParenClose = peeked_token.inner() {
                    parser.token_stream.next();
                    break;
                }
                let child =
                    parse_type_expr_node(parser, current_loc, recursive_counter + 1, type_expr)?;
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
                        parse_type_expr_node(parser, current_loc, recursive_counter + 1, type_expr)?
                    }
                    _ => {
                        type_expr.pool.push(TypeExprNode::void());
                        type_expr.pool.len() - 1
                    }
                }
            };
            TypeExprNode::Fn(args, ret_type)
        }
        _ => {
            return Err(ErrorContent::InvalidTypeExpr.wrap(token_location));
        }
    };
    type_expr.pool.push(node);
    Ok(type_expr.pool.len() - 1)
}
