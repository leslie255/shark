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
    fn parse_expr(
        &mut self,
        precedence: usize,
        expects_semicolon: bool,
    ) -> Option<Traced<'src, AstNode<'src>>> {
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
                macro_rules! parse_binary_op_expr {
                    ($precedence: expr) => {{
                        if precedence <= $precedence {
                            break;
                        }
                        let token_loc = self.token_stream.next()?.src_loc();
                        let lhs_node_ref = self.ast.add_node(node);
                        let rhs_node = self
                            .parse_expr($precedence, false)
                            .ok_or(ErrorContent::UnexpectedEOF.wrap(token_loc))
                            .collect_err(self.err_collector)?;
                        let rhs_node_ref = self.ast.add_node(rhs_node);
                        let start_index = lhs_node_ref.src_loc().range.0;
                        let end_index = rhs_node_ref.src_loc().range.1;
                        (lhs_node_ref, rhs_node_ref, (start_index, end_index))
                    }};
                }
                let peek = match self.token_stream.peek() {
                    Some(t) => t,
                    None => break,
                };
                // If there is an operator && the precedence matches, parse the rhs, "swallow" the
                // node and preduce a new one that is the root of this binary operator expression
                match peek.inner() {
                    Token::Mul => {
                        let (l, r, pos) = parse_binary_op_expr!(3);
                        node = AstNode::MathOp(MathOpKind::Mul, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::Div => {
                        let (l, r, pos) = parse_binary_op_expr!(3);
                        node = AstNode::MathOp(MathOpKind::Div, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::Mod => {
                        let (l, r, pos) = parse_binary_op_expr!(3);
                        node = AstNode::MathOp(MathOpKind::Mod, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::Add => {
                        let (l, r, pos) = parse_binary_op_expr!(4);
                        node = AstNode::MathOp(MathOpKind::Add, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::Sub => {
                        let (l, r, pos) = parse_binary_op_expr!(4);
                        node = AstNode::MathOp(MathOpKind::Sub, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::LeLe => {
                        let (l, r, pos) = parse_binary_op_expr!(5);
                        node = AstNode::BitOp(BitOpKind::Sl, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::GrGr => {
                        let (l, r, pos) = parse_binary_op_expr!(5);
                        node = AstNode::BitOp(BitOpKind::Sr, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::AndOp => {
                        let (l, r, pos) = parse_binary_op_expr!(8);
                        node = AstNode::BitOp(BitOpKind::And, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::XorOp => {
                        let (l, r, pos) = parse_binary_op_expr!(8);
                        node = AstNode::BitOp(BitOpKind::Xor, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::OrOp => {
                        let (l, r, pos) = parse_binary_op_expr!(8);
                        node = AstNode::BitOp(BitOpKind::Or, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::Eq => {
                        let (l, r, pos) = parse_binary_op_expr!(14);
                        node = AstNode::Assign(l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::AddEq => {
                        let (l, r, pos) = parse_binary_op_expr!(14);
                        node =
                            AstNode::MathOpAssign(MathOpKind::Add, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::SubEq => {
                        let (l, r, pos) = parse_binary_op_expr!(14);
                        node =
                            AstNode::MathOpAssign(MathOpKind::Sub, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::MulEq => {
                        let (l, r, pos) = parse_binary_op_expr!(14);
                        node =
                            AstNode::MathOpAssign(MathOpKind::Mul, l, r).wrap_loc((self.path, pos));
                    }
                    Token::DivEq => {
                        let (l, r, pos) = parse_binary_op_expr!(14);
                        node =
                            AstNode::MathOpAssign(MathOpKind::Div, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::ModEq => {
                        let (l, r, pos) = parse_binary_op_expr!(14);
                        node =
                            AstNode::MathOpAssign(MathOpKind::Mod, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::LeLeEq => {
                        let (l, r, pos) = parse_binary_op_expr!(14);
                        node = AstNode::BitOpAssign(BitOpKind::Sl, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::GrGrEq => {
                        let (l, r, pos) = parse_binary_op_expr!(14);
                        node = AstNode::BitOpAssign(BitOpKind::Sr, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::AndEq => {
                        let (l, r, pos) = parse_binary_op_expr!(14);
                        node =
                            AstNode::BitOpAssign(BitOpKind::And, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::OrEq => {
                        let (l, r, pos) = parse_binary_op_expr!(14);
                        node = AstNode::BitOpAssign(BitOpKind::Or, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    Token::XorEq => {
                        let (l, r, pos) = parse_binary_op_expr!(14);
                        node =
                            AstNode::BitOpAssign(BitOpKind::Xor, l, r).wrap_loc((self.path, pos));
                        continue;
                    }
                    _ => {
                        break;
                    }
                }
            }
            // End of expression
            let next = self.token_stream.peek().map(|t| t.inner());
            match (next, expects_semicolon) {
                (Some(Token::Semicolon), true) => {
                    self.token_stream.next();
                }
                (Some(_), true) => {
                    let loc = node.src_loc().range.1;
                    ErrorContent::ExpectsSemicolon
                        .wrap((self.path, loc))
                        .collect_into(self.err_collector);
                }
                (Some(_), false) => {}
                (None, true) => {
                    let loc = node.src_loc().range.1;
                    ErrorContent::ExpectsSemicolonFoundEOF
                        .wrap((self.path, loc))
                        .collect_into(self.err_collector);
                }
                (None, false) => (),
            }
            return Some(node);
        }
    }
}
impl<'src> Iterator for AstParser<'src> {
    type Item = AstNodeRef<'src>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.parse_expr(15, true)?;
        Some(self.ast.add_node(node))
    }
}
