use std::iter::Peekable;

use crate::{
    ast::BitOpKind,
    buffered_content::BufferedContent,
    error::{location::Traced, CollectIfErr, ErrorCollector, ErrorContent},
    token::{tokenizer::TokenStream, Token},
};

use super::{Ast, AstNode, AstNodeRef, MathOpKind};

/// Owns a `TokenStream` and parses it into AST incrementally
/// Implements `Iterator`
#[derive(Debug)]
pub struct AstParser<'src> {
    path: &'src str,
    err_collector: &'src ErrorCollector<'src>,
    token_stream: Peekable<TokenStream<'src>>,
    ast: Ast<'src>,
}
impl<'src> AstParser<'src> {
    pub fn new(
        path: &'src str,
        buffers: &'src BufferedContent<'src>,
        err_collector: &'src ErrorCollector<'src>,
    ) -> Self {
        Self {
            path: unsafe { (path as *const str).as_ref().unwrap() },
            err_collector,
            token_stream: TokenStream::new(path, buffers, err_collector).peekable(),
            ast: Ast::default(),
        }
    }
    /// Operator precedence is similar to C, expect:
    /// - Slot for tenary conditional operator `?:` as replaced by `as`
    /// - Slot for tenary conditional operator as replaced by `as`
    fn parse_expr(&mut self, precedence: usize) -> Option<Traced<'src, AstNode<'src>>> {
        let mut node: Traced<'src, AstNode<'src>>;
        loop {
            let token = self.token_stream.next()?;
            let token_location = token.src_loc();
            match token.into_inner() {
                Token::Identifier(id) => node = AstNode::Identifier(id).wrap_loc(token_location),
                Token::Number(num) => node = AstNode::Number(num).wrap_loc(token_location),
                Token::Character(ch) => node = AstNode::Char(ch).wrap_loc(token_location),
                Token::String(str) => {
                    let str_id = self.ast.add_str(str);
                    node = AstNode::String(str_id).wrap_loc(token_location)
                }
                _ => {
                    ErrorContent::UnexpectedToken
                        .wrap(token_location)
                        .collect_into(self.err_collector);
                    continue;
                }
            }
            loop {
                macro_rules! peek {
                    () => {{
                        if let Some(t) = self.token_stream.peek() {
                            t
                        } else {
                            return Some(node);
                        }
                    }};
                }
                macro_rules! parse_lhs_rhs {
                    ($precedence: expr) => {{
                        if precedence <= $precedence {
                            return Some(node);
                        }
                        let token_loc = self.token_stream.next().unwrap().src_loc();
                        let lhs_node_ref = self.ast.add_node(node);
                        let rhs_node = self
                            .parse_expr($precedence)
                            .ok_or(ErrorContent::UnexpectedEOF.wrap(token_loc))
                            .collect_err(self.err_collector)?;
                        let rhs_node_ref = self.ast.add_node(rhs_node);
                        (lhs_node_ref, rhs_node_ref)
                    }};
                }
                macro_rules! parse_lhs_op_rhs {
                    ($precedence: expr, $nodekind: tt) => {{
                        let (lhs_node_ref, rhs_node_ref) = parse_lhs_rhs!($precedence);
                        let start_index = lhs_node_ref.src_loc().range.0;
                        let end_index = rhs_node_ref.src_loc().range.0;
                        node = AstNode::$nodekind(lhs_node_ref, rhs_node_ref).wrap_loc((
                            self.path,
                            start_index,
                            end_index,
                        ));
                        continue;
                    }};
                    ($precedence: expr, $nodekind: tt, $opkind: expr) => {{
                        let (lhs_node_ref, rhs_node_ref) = parse_lhs_rhs!($precedence);
                        let start_index = lhs_node_ref.src_loc().range.0;
                        let end_index = rhs_node_ref.src_loc().range.0;
                        node = AstNode::$nodekind($opkind, lhs_node_ref, rhs_node_ref).wrap_loc((
                            self.path,
                            start_index,
                            end_index,
                        ));
                        continue;
                    }};
                }
                match peek!().inner() {
                    Token::Mul => parse_lhs_op_rhs!(3, MathOp, MathOpKind::Mul),
                    Token::Div => parse_lhs_op_rhs!(3, MathOp, MathOpKind::Div),
                    Token::Mod => parse_lhs_op_rhs!(3, MathOp, MathOpKind::Mod),
                    Token::Add => parse_lhs_op_rhs!(4, MathOp, MathOpKind::Add),
                    Token::Sub => parse_lhs_op_rhs!(4, MathOp, MathOpKind::Sub),
                    Token::LeLe => parse_lhs_op_rhs!(5, BitOp, BitOpKind::Sl),
                    Token::GrGr => parse_lhs_op_rhs!(5, BitOp, BitOpKind::Sr),
                    Token::AndOp => parse_lhs_op_rhs!(8, BitOp, BitOpKind::And),
                    Token::XorOp => parse_lhs_op_rhs!(8, BitOp, BitOpKind::Xor),
                    Token::OrOp => parse_lhs_op_rhs!(8, BitOp, BitOpKind::Or),
                    Token::Eq => parse_lhs_op_rhs!(14, Assign),
                    Token::AddEq => parse_lhs_op_rhs!(14, MathOpAssign, MathOpKind::Add),
                    Token::SubEq => parse_lhs_op_rhs!(14, MathOpAssign, MathOpKind::Sub),
                    Token::MulEq => parse_lhs_op_rhs!(14, MathOpAssign, MathOpKind::Mul),
                    Token::DivEq => parse_lhs_op_rhs!(14, MathOpAssign, MathOpKind::Div),
                    Token::ModEq => parse_lhs_op_rhs!(14, MathOpAssign, MathOpKind::Mod),
                    Token::LeLeEq => parse_lhs_op_rhs!(14, BitOpAssign, BitOpKind::Sl),
                    Token::GrGrEq => parse_lhs_op_rhs!(14, BitOpAssign, BitOpKind::Sr),
                    Token::AndEq => parse_lhs_op_rhs!(14, BitOpAssign, BitOpKind::And),
                    Token::OrEq => parse_lhs_op_rhs!(14, BitOpAssign, BitOpKind::Or),
                    Token::XorEq => parse_lhs_op_rhs!(14, BitOpAssign, BitOpKind::Xor),
                    _ => return Some(node),
                }
            }
        }
    }
}
impl<'src> Iterator for AstParser<'src> {
    type Item = AstNodeRef<'src>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.parse_expr(15)?;
        Some(self.ast.add_node(node))
    }
}
