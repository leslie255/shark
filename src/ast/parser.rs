use std::iter::Peekable;

use crate::{
    ast::BitOpKind,
    buffered_content::BufferedContent,
    error::{
        location::{IntoSourceLoc, SourceLocation, Traced},
        CollectIfErr, ErrorCollector, ErrorContent,
    },
    token::{tokenizer::TokenStream, Token},
};

use super::{
    type_expr::{TypeExpr, TypeExprNode},
    Ast, AstNode, AstNodeRef, FnDef, MathOpKind,
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

impl<'src> Iterator for AstParser<'src> {
    type Item = AstNodeRef<'src>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.parse_expr(15, true)?;
        Some(self.ast.add_node(node))
    }
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
    #[allow(dead_code)]
    #[must_use]
    #[inline]
    pub fn str_pool(&self) -> &Vec<String> {
        &self.ast.str_pool
    }
    /// Operator precedence is similar to C, expect:
    /// - Slot for tenary conditional operator `?:` as replaced by `as`
    #[must_use]
    fn parse_expr(
        &mut self,
        precedence: usize,
        expects_semicolon: bool,
    ) -> Option<Traced<'src, AstNode<'src>>> {
        let mut node: Traced<'src, AstNode<'src>> = Default::default();
        macro_rules! parse {
            (binary_op, precedence > $precedence:expr; else: $else:expr) => {{
                if precedence <= $precedence {
                    $else;
                }
                let token_loc = self.token_stream.next()?.src_loc();
                let lhs_node_ref = self.ast.add_node(node);
                let rhs_node = self
                    .parse_expr($precedence, false)
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(token_loc))
                    .collect_err(self.err_collector)?;
                let rhs_node_ref = self.ast.add_node(rhs_node);
                let lhs_pos = lhs_node_ref.src_loc();
                let file_name = lhs_pos.file_name;
                let start_index = lhs_pos.range.0;
                let end_index = rhs_node_ref.src_loc().range.1;
                (
                    lhs_node_ref,
                    rhs_node_ref,
                    (file_name, start_index, end_index),
                )
            }};
            (mono_op, precedence = $precedence:expr) => {{
                let current_loc = node.src_loc();
                let child = self
                    .parse_expr($precedence, false)
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(current_loc))
                    .collect_err(self.err_collector)?;
                let loc = (
                    if current_loc.file_name.is_empty() {
                        self.path
                    } else {
                        current_loc.file_name
                    },
                    current_loc.range.0,
                    child.src_loc().range.1,
                );
                let child = self.ast.add_node(child);
                (child, loc)
            }};
        }
        loop {
            let token = self.token_stream.next()?;
            let token_location = token.src_loc();
            match token.into_inner() {
                Token::Identifier(id) => node = AstNode::Identifier(id).traced(token_location),
                Token::Number(num) => node = AstNode::Number(num).traced(token_location),
                Token::Character(ch) => node = AstNode::Char(ch).traced(token_location),
                Token::String(str) => {
                    let str_id = self.ast.add_str(str);
                    node = AstNode::String(str_id).traced(token_location)
                }
                Token::Let => node = self.parse_let(token_location)?,
                Token::Fn => node = self.parse_fn_def(token_location)?,
                Token::BraceOpen => {
                    let (loc, children) = self.parse_block(token_location)?;
                    let block = AstNode::Block(children);
                    node = block.traced(loc);
                }
                Token::RoundParenOpen => node = self.parse_paren(token_location)?,
                Token::Return => {
                    let (child, loc) = parse!(mono_op, precedence = 15);
                    node = AstNode::Return(child).traced(loc);
                }
                Token::AndOp => {
                    let (child, loc) = parse!(mono_op, precedence = 1);
                    node = AstNode::TakeRef(child).traced(loc);
                }
                Token::Mul => {
                    let (child, loc) = parse!(mono_op, precedence = 1);
                    node = AstNode::Deref(child).traced(loc);
                }
                Token::Add => {
                    let (child, loc) = parse!(mono_op, precedence = 1);
                    node = AstNode::PlusNum(child).traced(loc);
                }
                Token::Sub => {
                    let (child, loc) = parse!(mono_op, precedence = 1);
                    node = AstNode::MinusNum(child).traced(loc);
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
        // If there is an operator and the precedence matches, parse the rhs, "swallow" the node,
        // use it as the LHS, and preduce a new node that is the root of this binary operator
        loop {
            let peek = match self.token_stream.peek() {
                Some(t) => t,
                None => break,
            };
            match peek.inner() {
                Token::Mul => {
                    let (l, r, pos) = parse!(binary_op, precedence > 3; else: break);
                    node = AstNode::MathOp(MathOpKind::Mul, l, r).traced(pos);
                    continue;
                }
                Token::Div => {
                    let (l, r, pos) = parse!(binary_op, precedence > 3; else: break);
                    node = AstNode::MathOp(MathOpKind::Div, l, r).traced(pos);
                    continue;
                }
                Token::Mod => {
                    let (l, r, pos) = parse!(binary_op, precedence > 3; else: break);
                    node = AstNode::MathOp(MathOpKind::Mod, l, r).traced(pos);
                    continue;
                }
                Token::Add => {
                    let (l, r, pos) = parse!(binary_op, precedence > 4; else: break);
                    node = AstNode::MathOp(MathOpKind::Add, l, r).traced(pos);
                    continue;
                }
                Token::Sub => {
                    let (l, r, pos) = parse!(binary_op, precedence > 4; else: break);
                    node = AstNode::MathOp(MathOpKind::Sub, l, r).traced(pos);
                    continue;
                }
                Token::LeLe => {
                    let (l, r, pos) = parse!(binary_op, precedence > 5; else: break);
                    node = AstNode::BitOp(BitOpKind::Sl, l, r).traced(pos);
                    continue;
                }
                Token::GrGr => {
                    let (l, r, pos) = parse!(binary_op, precedence > 5; else: break);
                    node = AstNode::BitOp(BitOpKind::Sr, l, r).traced(pos);
                    continue;
                }
                Token::AndOp => {
                    let (l, r, pos) = parse!(binary_op, precedence > 8; else: break);
                    node = AstNode::BitOp(BitOpKind::And, l, r).traced(pos);
                    continue;
                }
                Token::XorOp => {
                    let (l, r, pos) = parse!(binary_op, precedence > 8; else: break);
                    node = AstNode::BitOp(BitOpKind::Xor, l, r).traced(pos);
                    continue;
                }
                Token::OrOp => {
                    let (l, r, pos) = parse!(binary_op, precedence > 8; else: break);
                    node = AstNode::BitOp(BitOpKind::Or, l, r).traced(pos);
                    continue;
                }
                Token::Eq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 14; else: break);
                    node = AstNode::Assign(l, r).traced(pos);
                    continue;
                }
                Token::AddEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 14; else: break);
                    node = AstNode::MathOpAssign(MathOpKind::Add, l, r).traced(pos);
                    continue;
                }
                Token::SubEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 14; else: break);
                    node = AstNode::MathOpAssign(MathOpKind::Sub, l, r).traced(pos);
                    continue;
                }
                Token::MulEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 14; else: break);
                    node = AstNode::MathOpAssign(MathOpKind::Mul, l, r).traced(pos);
                }
                Token::DivEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 14; else: break);
                    node = AstNode::MathOpAssign(MathOpKind::Div, l, r).traced(pos);
                    continue;
                }
                Token::ModEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 14; else: break);
                    node = AstNode::MathOpAssign(MathOpKind::Mod, l, r).traced(pos);
                    continue;
                }
                Token::LeLeEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 14; else: break);
                    node = AstNode::BitOpAssign(BitOpKind::Sl, l, r).traced(pos);
                    continue;
                }
                Token::GrGrEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 14; else: break);
                    node = AstNode::BitOpAssign(BitOpKind::Sr, l, r).traced(pos);
                    continue;
                }
                Token::AndEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 14; else: break);
                    node = AstNode::BitOpAssign(BitOpKind::And, l, r).traced(pos);
                    continue;
                }
                Token::OrEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 14; else: break);
                    node = AstNode::BitOpAssign(BitOpKind::Or, l, r).traced(pos);
                    continue;
                }
                Token::XorEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 14; else: break);
                    node = AstNode::BitOpAssign(BitOpKind::Xor, l, r).traced(pos);
                    continue;
                }
                Token::RoundParenOpen => {
                    let loc_start = node.src_loc().range.0;
                    let node_ref = self.ast.add_node(node);
                    let token_loc = self.token_stream.next()?.src_loc();
                    let (args, loc_end) = self.parse_fn_call_args(token_loc)?;
                    node = AstNode::Call(node_ref, args).traced((self.path, loc_start, loc_end));
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
            (Some(_), true) => match node.inner() {
                &AstNode::Block(_) | &AstNode::FnDef(_) | &AstNode::If(_) | &AstNode::Loop(_) => {}
                _ => {
                    let loc = node.src_loc().range.1;
                    ErrorContent::ExpectsSemicolon
                        .wrap((node.src_loc().file_name, loc))
                        .collect_into(self.err_collector);
                }
            },
            (Some(_), false) => {}
            (None, true) => match node.inner() {
                &AstNode::Block(_) | &AstNode::FnDef(_) | &AstNode::If(_) | &AstNode::Loop(_) => {}
                _ => {
                    let loc = node.src_loc().range.1;
                    ErrorContent::ExpectsSemicolonFoundEOF
                        .wrap((node.src_loc().file_name, loc))
                        .collect_into(self.err_collector);
                }
            },
            (None, false) => (),
        }
        Some(node)
    }

    /// Parse a `let` expression, starting from the token `let`
    /// EOF error handled inside
    /// Takes in the location of the token `let` as argument
    #[must_use]
    #[inline]
    fn parse_let(
        &mut self,
        start_loc: SourceLocation<'src>,
    ) -> Option<Traced<'src, AstNode<'src>>> {
        // Get variable name
        let next_token = next_token!(self, start_loc);
        let token_location = next_token.src_loc();
        let var_name = next_token
            .expect_identifier()
            .ok_or(ErrorContent::ExpectToken(Token::Identifier("")).wrap(token_location))
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
        let node_loc = (self.path, start_loc, end_loc);

        match (&var_type, &rhs) {
            (None, None) => ErrorContent::LetNoTypeOrRHS
                .wrap(node_loc)
                .collect_into(self.err_collector),
            _ => (),
        }
        Some(AstNode::Let(var_name, var_type, rhs).traced(node_loc))
    }

    /// Parse arguments in a function call, starting from the `(`
    /// Returns the arguments, and where the call ended
    /// Returns `None` if unexpected EOF, errors handled internally
    #[must_use]
    #[inline]
    fn parse_fn_call_args(
        &mut self,
        current_loc: SourceLocation<'src>,
    ) -> Option<(Vec<AstNodeRef<'src>>, usize)> {
        let mut args = Vec::<AstNodeRef<'src>>::new();

        let close_paren_loc: usize;
        loop {
            // If there's a `)`, break
            let peeked_token = peek_token!(self, current_loc);
            let peeked_location = peeked_token.src_loc();
            match peeked_token.inner() {
                Token::RoundParenClose => {
                    close_paren_loc = peeked_location.range.1;
                    self.token_stream.next();
                    break;
                }
                _ => (),
            }
            let node = self
                .parse_expr(15, false)
                .ok_or(ErrorContent::UnexpectedEOF.wrap(peeked_location))
                .collect_err(self.err_collector)?;
            let node_ref = self.ast.add_node(node);
            args.push(node_ref);

            let peeked_token = peek_token!(self, current_loc);
            match peeked_token.inner() {
                Token::RoundParenClose => {
                    continue;
                }
                Token::Comma => {
                    self.token_stream.next();
                    continue;
                }
                _ => ErrorContent::ExpectMultipleTokens(vec![Token::RoundParenClose, Token::Comma])
                    .wrap(peeked_token.src_loc())
                    .collect_into(self.err_collector),
            }
        }
        Some((args, close_paren_loc))
    }

    /// Parse inside a `(...)`, starting from the `(`
    /// Returns the `SourceLocation` of the node, and the child node
    /// Returns `None` if unexpected EOF, errors handled internally
    #[must_use]
    #[inline]
    fn parse_paren(
        &mut self,
        start_loc: SourceLocation<'src>,
    ) -> Option<Traced<'src, AstNode<'src>>> {
        let inner_node = self
            .parse_expr(15, false)
            .ok_or(ErrorContent::UnexpectedEOF.wrap(start_loc))
            .collect_err(self.err_collector)?;

        // check if there is a closing parenthese
        let loc = inner_node.src_loc();
        let peek = peek_token!(self, (loc.file_name, loc.range.1));
        let peek_loc = peek.src_loc();
        match peek.inner() {
            Token::RoundParenClose => {
                self.token_stream.next();
            }
            _ => {
                ErrorContent::ExpectToken(Token::RoundParenClose)
                    .wrap(peek_loc)
                    .collect_into(self.err_collector);
            }
        }

        Some(inner_node)
    }

    /// Parse a block, starting from the `{`
    /// Returns the `SourceLocation` of the block, and the child nodes
    /// Returns `None` if unexpected EOF, errors handled internally
    #[must_use]
    #[inline]
    fn parse_block(
        &mut self,
        start_loc: SourceLocation<'src>,
    ) -> Option<(SourceLocation<'src>, Vec<AstNodeRef<'src>>)> {
        let mut nodes = Vec::<AstNodeRef<'src>>::new();
        let peek_token = peek_token!(self, start_loc);
        let mut end_loc: usize = peek_token.src_loc().range.1;
        match peek_token.inner() {
            &Token::BraceClose => {
                self.token_stream.next();
                return Some((
                    (start_loc.file_name, start_loc.range.0, end_loc).into_source_location(),
                    nodes,
                ));
            }
            _ => (),
        }
        loop {
            let node = self
                .parse_expr(15, true)
                .ok_or(ErrorContent::UnexpectedEOF.wrap(start_loc))
                .collect_err(self.err_collector)?;
            let node_ref = self.ast.add_node(node);
            nodes.push(node_ref);
            let peek = peek_token!(self, start_loc);
            end_loc = peek.src_loc().range.1;
            match peek.inner() {
                Token::BraceClose => {
                    self.token_stream.next();
                    break;
                }
                _ => continue,
            }
        }
        let loc = (start_loc.file_name, start_loc.range.0, end_loc).into_source_location();
        Some((loc, nodes))
    }

    /// Parse an `fn` expression, starting from the token `fn`
    /// Returns `None` if unexpected EOF, errors handled internally
    #[must_use]
    #[inline]
    fn parse_fn_def(
        &mut self,
        start_loc: SourceLocation<'src>,
    ) -> Option<Traced<'src, AstNode<'src>>> {
        let next_token = next_token!(self, start_loc);
        let loc = next_token.src_loc();
        let name = next_token
            .expect_identifier()
            .ok_or(ErrorContent::ExpectToken(Token::Identifier("")).wrap(loc))
            .collect_err(self.err_collector)?;
        let (args, mut end_loc) = self.parse_fn_def_args(loc)?;
        let peeked_token = peek_token!(self, (loc.file_name, end_loc));
        let peeked_location = peeked_token.src_loc();
        let ret_type = match peeked_token.inner() {
            &Token::Arrow => {
                self.token_stream.next();
                end_loc = peeked_location.range.1;
                self.parse_type_expr(0, peeked_location, |token_stream| {
                    skip_to_expr_end!(token_stream)
                })?
            }
            &Token::BraceOpen | &Token::Semicolon | &Token::Comma => TypeExprNode::None.wrap(),
            _ => todo!("error"),
        };
        let peeked_token = next_token!(self, peeked_location);
        let peeked_location = peeked_token.src_loc();
        let body = match peeked_token.into_inner() {
            Token::BraceOpen => {
                let (body_end_loc, body) = self.parse_block(peeked_location)?;
                end_loc = body_end_loc.range.1;
                Some(body)
            }
            Token::Semicolon | Token::Comma => Option::None,
            _ => todo!("error"),
        };

        let node = AstNode::FnDef(FnDef {
            name,
            args,
            ret_type,
            body,
        });
        Some(node.traced((start_loc.file_name, start_loc.range.0, end_loc)))
    }

    /// Parse arguments in a function definition, starting from the token `(`
    /// Returns the arguments, and where the call ended
    /// Returns `None` if unexpected EOF, errors handled internally
    #[must_use]
    #[inline]
    fn parse_fn_def_args(
        &mut self,
        start_loc: SourceLocation<'src>,
    ) -> Option<(Vec<(&'src str, TypeExpr<'src>)>, usize)> {
        let mut args = Vec::<(&'src str, TypeExpr<'src>)>::new();
        let peek_token = peek_token!(self, start_loc);
        let loc = peek_token.src_loc();
        if let Token::RoundParenOpen = peek_token.inner() {
            self.token_stream.next();
        } else {
            ErrorContent::ExpectToken(Token::RoundParenOpen)
                .wrap(loc)
                .collect_into(self.err_collector)
        }

        let close_paren_loc: usize;
        loop {
            // If there's a `)`, break
            let next_token = next_token!(self, start_loc);
            let token_location = next_token.src_loc();
            let arg_name = match next_token.into_inner() {
                Token::RoundParenClose => {
                    close_paren_loc = token_location.range.1;
                    break;
                }
                Token::Identifier(id) => id,
                _ => {
                    ErrorContent::ExpectMultipleTokens(vec![
                        Token::Identifier(""),
                        Token::RoundParenClose,
                    ])
                    .wrap(token_location)
                    .collect_into(self.err_collector);
                    skip_to_expr_end!(self.token_stream);
                    return None;
                }
            };
            let next_token = next_token!(self, start_loc);
            let token_location = next_token.src_loc();
            match next_token.into_inner() {
                Token::Colon => (),
                _ => {
                    todo!("error")
                }
            }
            let arg_type = self.parse_type_expr(0, token_location, {
                |token_stream| skip_to_expr_end!(token_stream)
            })?;
            args.push((arg_name, arg_type));

            let peeked_token = peek_token!(self, start_loc);
            match peeked_token.inner() {
                Token::RoundParenClose => {
                    continue;
                }
                Token::Comma => {
                    self.token_stream.next();
                    continue;
                }
                _ => ErrorContent::ExpectMultipleTokens(vec![Token::RoundParenClose, Token::Comma])
                    .wrap(peeked_token.src_loc())
                    .collect_into(self.err_collector),
            }
        }
        Some((args, close_paren_loc))
    }

    /// Parse a type expression, starting from the token before that expression
    /// Returns `None` if unexpected EOF, errors handled internally
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
