use std::iter::Peekable;

use crate::{
    ast::BitOpKind,
    buffered_content::BufferedContent,
    error::{
        location::{SourceLocation, Traced},
        CollectIfErr, ErrorCollector, ErrorContent,
    },
    token::{tokenizer::TokenStream, Token},
};

use super::{
    type_expr::{TypeExpr, TypeExprNode},
    Ast, AstNode, AstNodeRef, MathOpKind,
};

/// Owns a `TokenStream` and parses it into AST incrementally
/// Implements `Iterator`
#[derive(Debug)]
pub struct AstParser<'src> {
    path: &'src str,
    err_collector: &'src ErrorCollector<'src>,
    token_stream: Peekable<TokenStream<'src>>,
    ast: Ast<'src>,
}
/// Increment one token forward, if it's EOF than create an UnexpectedEOF error and collect it into
/// an `ErrorCollector`
macro_rules! next_token {
    ($self: expr, $loc: expr) => {
        $self
            .token_stream
            .next()
            .ok_or(ErrorContent::UnexpectedEOF.wrap($loc))
            .collect_err($self.err_collector)?
    };
}
/// Peek one token forward, if it's EOF than create an UnexpectedEOF error and collect it into an
/// `ErrorCollector`
macro_rules! peek_token {
    ($self: expr, $loc: expr) => {
        $self
            .token_stream
            .peek()
            .ok_or(ErrorContent::UnexpectedEOF.wrap($loc))
            .collect_err($self.err_collector)?
    };
}
/// When encountering an error, skip to the (presumed) end of the expression
macro_rules! skip_to_expr_end {
    ($token_stream: expr) => {
        while let Some(token) = $token_stream.peek() {
            {
                let token = token.inner();
                if token == &Token::Eq
                    || token == &Token::Semicolon
                    || token == &Token::RoundParenClose
                    || token == &Token::RectParenClose
                    || token == &Token::BraceClose
                {
                    break;
                }
                match token {
                    &Token::Eq
                    | &Token::Semicolon
                    | &Token::RoundParenClose
                    | &Token::RectParenClose
                    | &Token::BraceClose
                    | &Token::Comma => break,
                    _ => {
                        $token_stream.next();
                    }
                }
            }
        }
    };
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
    #[must_use]
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
                Token::Let => node = self.parse_let(token_location)?,
                Token::Fn => {
                    todo!()
                }
                _ => {
                    ErrorContent::UnexpectedToken
                        .wrap(token_location)
                        .collect_into(self.err_collector);
                    continue;
                }
            }
            break;
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
                    node = AstNode::MathOpAssign(MathOpKind::Add, l, r).wrap_loc((self.path, pos));
                    continue;
                }
                Token::SubEq => {
                    let (l, r, pos) = parse_binary_op_expr!(14);
                    node = AstNode::MathOpAssign(MathOpKind::Sub, l, r).wrap_loc((self.path, pos));
                    continue;
                }
                Token::MulEq => {
                    let (l, r, pos) = parse_binary_op_expr!(14);
                    node = AstNode::MathOpAssign(MathOpKind::Mul, l, r).wrap_loc((self.path, pos));
                }
                Token::DivEq => {
                    let (l, r, pos) = parse_binary_op_expr!(14);
                    node = AstNode::MathOpAssign(MathOpKind::Div, l, r).wrap_loc((self.path, pos));
                    continue;
                }
                Token::ModEq => {
                    let (l, r, pos) = parse_binary_op_expr!(14);
                    node = AstNode::MathOpAssign(MathOpKind::Mod, l, r).wrap_loc((self.path, pos));
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
                    node = AstNode::BitOpAssign(BitOpKind::And, l, r).wrap_loc((self.path, pos));
                    continue;
                }
                Token::OrEq => {
                    let (l, r, pos) = parse_binary_op_expr!(14);
                    node = AstNode::BitOpAssign(BitOpKind::Or, l, r).wrap_loc((self.path, pos));
                    continue;
                }
                Token::XorEq => {
                    let (l, r, pos) = parse_binary_op_expr!(14);
                    node = AstNode::BitOpAssign(BitOpKind::Xor, l, r).wrap_loc((self.path, pos));
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
        Some(node)
    }

    /// Parse a `let` expression, starting from the token `let`
    /// EOF error handled inside
    /// Takes in the location of the token `let` as argument
    #[must_use]
    fn parse_let(
        &mut self,
        start_loc: SourceLocation<'src>,
    ) -> Option<Traced<'src, AstNode<'src>>> {
        // Get variable name
        let next_token = next_token!(self, start_loc);
        let token_location = next_token.src_loc();
        let var_name = next_token
            .expect_identifier()
            .ok_or(ErrorContent::ExpectIDAfterLet.wrap(token_location))
            .collect_err(self.err_collector)?;

        // Get type
        let mut peeked_token = peek_token!(self, token_location);
        let mut peeked_location = peeked_token.src_loc();
        let var_type = match peeked_token.inner() {
            Token::Colon => {
                self.token_stream.next();
                let type_expr = self.parse_type_expr(0, peeked_location, |token_stream| {
                    skip_to_expr_end!(token_stream)
                })?;
                peeked_token = peek_token!(self, peeked_location);
                peeked_location = peeked_token.src_loc();
                Some(type_expr)
            }
            _ => Option::<TypeExpr<'src>>::None,
        };

        // Get rhs
        let rhs = match peeked_token.inner() {
            Token::Eq => {
                self.token_stream.next();
                let rhs = self
                    .parse_expr(15, false)
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(peeked_location))
                    .collect_err(self.err_collector)?;
                Some(rhs)
            }
            _ => None,
        };
        let end_loc = match &rhs {
            Some(n) => n.src_loc().range.1,
            None => peeked_location.range.1,
        };

        let start_loc = start_loc.range.0;
        let rhs = rhs.map(|n| self.ast.add_node(n));
        Some(AstNode::Let(var_name, var_type, rhs).wrap_loc((self.path, start_loc, end_loc)))
    }

    /// Parse a type expression, starting from the token before that expression
    /// Returns None if unexpected EOF, errors handled internally
    #[must_use]
    fn parse_type_expr<F>(
        &mut self,
        recursive_counter: usize,
        current_loc: SourceLocation<'src>,
        err_handler: F,
    ) -> Option<TypeExpr<'src>>
    where
        F: Fn(&mut Peekable<TokenStream<'src>>),
    {
        let next_token = next_token!(self, current_loc);
        let token_location = next_token.src_loc();
        match next_token.into_inner() {
            Token::Identifier("usize") => Some(TypeExprNode::USize.wrap()),
            Token::Identifier("isize") => Some(TypeExprNode::ISize.wrap()),
            Token::Identifier("u64") => Some(TypeExprNode::U64.wrap()),
            Token::Identifier("u32") => Some(TypeExprNode::U32.wrap()),
            Token::Identifier("u16") => Some(TypeExprNode::U16.wrap()),
            Token::Identifier("u8") => Some(TypeExprNode::U8.wrap()),
            Token::Identifier("i64") => Some(TypeExprNode::I64.wrap()),
            Token::Identifier("i32") => Some(TypeExprNode::I32.wrap()),
            Token::Identifier("i16") => Some(TypeExprNode::I16.wrap()),
            Token::Identifier("i8") => Some(TypeExprNode::I8.wrap()),
            Token::Identifier("char32") => Some(TypeExprNode::Char32.wrap()),
            Token::Identifier("char8") => Some(TypeExprNode::Char8.wrap()),
            Token::Identifier("none") => Some(TypeExprNode::None.wrap()),
            Token::Identifier(typename) => Some(TypeExprNode::TypeName(typename).wrap()),
            Token::AndOp => {
                let mut node =
                    self.parse_type_expr(recursive_counter + 1, current_loc, err_handler)?;
                node.pool.push(TypeExprNode::Ref(node.root));
                node.root = node.pool.len() - 1;
                Some(node)
            }
            Token::Mul => {
                let mut node =
                    self.parse_type_expr(recursive_counter + 1, current_loc, err_handler)?;
                node.pool.push(TypeExprNode::Ptr(node.root));
                node.root = node.pool.len() - 1;
                Some(node)
            }
            Token::RectParenOpen => {
                let peeked_token = self
                    .token_stream
                    .peek()
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(token_location))
                    .collect_err(self.err_collector)?;
                let peeked_location = peeked_token.src_loc();
                match peeked_token.inner() {
                    Token::RectParenClose => {
                        self.token_stream.next();
                    }
                    _ => {
                        ErrorContent::SliceNoClosingParen
                            .wrap((self.path, peeked_location.range.0))
                            .collect_into(self.err_collector);
                        err_handler(&mut self.token_stream);
                        return Some(TypeExprNode::None.wrap());
                    }
                }
                let mut node =
                    self.parse_type_expr(recursive_counter + 1, current_loc, err_handler)?;
                node.pool.push(TypeExprNode::Slice(node.root));
                node.root = node.pool.len() - 1;
                Some(node)
            }
            _ => {
                ErrorContent::InvalidTypeExpr
                    .wrap(token_location)
                    .collect_into(self.err_collector);
                err_handler(&mut self.token_stream);
                None
            }
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
