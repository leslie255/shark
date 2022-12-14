use std::iter::Peekable;

mod type_parser;

use crate::{
    ast::{BitOpKind, BoolOpKind, CmpKind},
    buffered_content::BufferedContent,
    checks::syntaxchecker,
    error::{
        location::{IntoSourceLoc, SourceLocation, Traced},
        CollectIfErr, ErrorCollector, ErrorContent,
    },
    token::{tokenizer::TokenStream, Token},
};

use self::type_parser::parse_type_expr;

use super::{
    type_expr::{TypeExpr, TypeExprNode},
    Ast, AstNode, AstNodeRef, EnumDef, FnDef, FnSignature, IfExpr, MathOpKind, StructOrUnionDef,
};

/// Owns a `TokenStream` and parses it into AST incrementally
/// Implements `Iterator`
#[derive(Debug)]
pub struct AstParser<'src> {
    path: &'src str,
    err_collector: &'src ErrorCollector<'src>,
    token_stream: Peekable<TokenStream<'src>>,
    pub ast: Ast<'src>,
}

impl<'src> Iterator for AstParser<'src> {
    type Item = AstNodeRef<'src>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.parse_expr(15, true)?;
        syntaxchecker::check_top_level(&node, self.err_collector);
        let node_ref = self.ast.add_node(node);
        self.ast.root_nodes.push(node_ref.clone());
        Some(node_ref)
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

/// Expect the next token to fit a pattern, otherwise collect an `ExpectToken` error and call `otherwise`.
///
/// The location of the expected token is returned.
///
/// # Parameters
/// - `$self`: The parser.
/// - `$loc`: The location of the previous token.
/// - `$expected`: Pattern of the expected token.
/// - `$err_handler`: The error handler.
///
/// # Exampls
///
/// ```
/// let loc = expect_token!(self, loc, Token::Colon, otherwise: return None);
/// ```
///
#[macro_export]
macro_rules! expect_token {
    ($self:expr, $loc:expr, $expected:pat, otherwise: $err_handler:expr) => {{
        let peeked_token = peek_token!($self, $loc);
        let peeked_location = peeked_token.src_loc();
        if !matches!(peeked_token.inner(), &$expected) {
            ErrorContent::ExpectToken(Token::Colon)
                .wrap(peeked_location)
                .collect_into($self.err_collector);
            $err_handler;
        } else {
            $self.token_stream.next();
        }
        peeked_location
    }};
}

/// Expect the next token to be an identifier, otherwise collect an `ExpectToken` error and call `otherwise`.
///
/// The location of the token and the identifier string is returned
///
/// # Parameters
/// - `$self`: The parser.
/// - `$loc`: The location of the previous token.
/// - `$err_handler`: The error handler.
///
/// # Exampls
///
/// ```
/// let (loc, id) = expect_token!(self, loc, otherwise: return None);
/// ```
///
#[macro_export]
macro_rules! expect_identifier {
    ($self:expr, $loc:expr, otherwise: $err_handler:expr) => {{
        let peeked_token = peek_token!($self, $loc);
        let peeked_location = peeked_token.src_loc();
        let result = peeked_token
            .expect_identifier()
            .ok_or(ErrorContent::ExpectToken(Token::Identifier("")).wrap(peeked_location))
            .collect_err($self.err_collector);
        match result {
            Some(id) => {
                $self.token_stream.next();
                (peeked_location, id)
            }
            None => $err_handler,
        }
    }};
}

impl<'src> AstParser<'src> {
    /// Create a new parser.
    ///
    /// # Parameters
    ///
    /// - `path`: The path of the source file.
    /// - `buffers`: The content of the source file.
    /// - `err_collector`: The error collector.
    ///
    /// Note: `BufferedContent` and `ErrorCollector` both uses internal mutability so there is no
    /// need for `&mut` borrow
    ///
    /// # Returns
    ///
    /// The parser.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::ast::parser::AstParser;
    /// use crate::buffered_content::BufferedContent;
    /// use crate::error::ErrorCollector;
    ///
    /// let path = "test.shark";
    /// let buffers = BufferedContent::default();
    /// let err_collector = ErrorCollector::new(path);
    /// let parser = AstParser::new(path, &buffers, &err_collector);
    /// ```
    #[must_use]
    #[inline]
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

    /// Parse a expression.
    ///
    /// # Parameters
    ///
    /// - `precedence`: The precedence of the expression.
    /// (only used in recursive calls, when calling from outside always use `15`)
    ///
    /// - `expects_semicolon`: Whether the expression should be followed by a semicolon.
    ///
    /// # Returns
    /// The parsed expression, or `None` if EOF
    /// Errors collected internally
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
                syntaxchecker::check_child(&node, self.err_collector);
                let lhs_node_ref = self.ast.add_node(node);
                let rhs_node = self
                    .parse_expr($precedence, false)
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(token_loc))
                    .collect_err(self.err_collector)?;
                syntaxchecker::check_child(&rhs_node, self.err_collector);
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
                syntaxchecker::check_child(&child, self.err_collector);
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
                Token::True => node = AstNode::Bool(true).traced(token_location),
                Token::False => node = AstNode::Bool(false).traced(token_location),
                Token::String(str) => {
                    let str_id = self.ast.add_str(str);
                    node = AstNode::String(str_id).traced(token_location)
                }
                Token::Let => node = self.parse_let(token_location)?,
                Token::Fn => node = self.parse_fn_def(token_location)?,
                Token::Loop => node = self.parse_loop(token_location)?,
                Token::If => node = self.parse_if(token_location)?,
                Token::BraceOpen => {
                    let (loc, children) =
                        self.parse_block(token_location, syntaxchecker::check_fn_body)?;
                    let block = AstNode::Block(children);
                    node = block.traced(loc);
                }
                Token::RoundParenOpen => node = self.parse_paren(token_location)?,
                Token::RectParenOpen => node = self.parse_arr_literal(token_location)?,
                Token::Return => {
                    let peek = peek_token!(self, token_location);
                    match peek.inner() {
                        &Token::Semicolon | &Token::Comma => {
                            node = AstNode::Return(None).traced(token_location);
                        }
                        _ => {
                            let (child, loc) = parse!(mono_op, precedence = 15);
                            node = AstNode::Return(Some(child)).traced(loc);
                        }
                    }
                }
                Token::Break => node = AstNode::Break.traced(token_location),
                Token::Continue => node = AstNode::Continue.traced(token_location),
                Token::Typedef => node = self.parse_typedef(token_location)?,
                Token::Struct => {
                    let (fields, pos) = self.parse_struct_or_union(token_location)?;
                    node = AstNode::StructDef(fields).traced(pos);
                }
                Token::Union => {
                    let (fields, pos) = self.parse_struct_or_union(token_location)?;
                    node = AstNode::UnionDef(fields).traced(pos);
                }
                Token::Enum => node = self.parse_enum(token_location)?,
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
                Token::Squiggle => {
                    let (child, loc) = parse!(mono_op, precedence = 2);
                    node = AstNode::BitNot(child).traced(loc);
                }
                Token::Exc => {
                    let (child, loc) = parse!(mono_op, precedence = 2);
                    node = AstNode::BoolNot(child).traced(loc);
                    continue;
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
                Token::Dot => {
                    let (l, r, pos) = parse!(binary_op, precedence > 1; else: break);
                    node = AstNode::MemberAccess(l, r).traced(pos);
                    continue;
                }
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
                Token::AndAnd => {
                    let (l, r, pos) = parse!(binary_op, precedence > 11; else: break);
                    node = AstNode::BoolOp(BoolOpKind::And, l, r).traced(pos);
                    continue;
                }
                Token::OrOr => {
                    let (l, r, pos) = parse!(binary_op, precedence > 12; else: break);
                    node = AstNode::BoolOp(BoolOpKind::Or, l, r).traced(pos);
                    continue;
                }
                Token::EqEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 7; else: break);
                    node = AstNode::Cmp(CmpKind::Eq, l, r).traced(pos);
                    continue;
                }
                Token::ExcEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 7; else: break);
                    node = AstNode::Cmp(CmpKind::Neq, l, r).traced(pos);
                    continue;
                }
                Token::Le => {
                    let (l, r, pos) = parse!(binary_op, precedence > 6; else: break);
                    node = AstNode::Cmp(CmpKind::Le, l, r).traced(pos);
                    continue;
                }
                Token::Gr => {
                    let (l, r, pos) = parse!(binary_op, precedence > 6; else: break);
                    node = AstNode::Cmp(CmpKind::Gr, l, r).traced(pos);
                    continue;
                }
                Token::LeEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 6; else: break);
                    node = AstNode::Cmp(CmpKind::LeEq, l, r).traced(pos);
                    continue;
                }
                Token::GrEq => {
                    let (l, r, pos) = parse!(binary_op, precedence > 6; else: break);
                    node = AstNode::Cmp(CmpKind::GrEq, l, r).traced(pos);
                    continue;
                }
                Token::As => {
                    if precedence <= 2 {
                        break;
                    }
                    let token_loc = self.token_stream.next()?.src_loc();
                    let node_loc = node.src_loc();
                    let node_ref = self.ast.add_node(node);
                    let dtype = parse_type_expr(self, token_loc).collect_err(self.err_collector)?;
                    node = AstNode::Typecast(node_ref, dtype).traced((
                        node_loc.file_name,
                        node_loc.range.0,
                        token_loc.range.1,
                    ));
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
        // Semicolon check
        let next = self.token_stream.peek().map(|t| t.inner());
        match (next, expects_semicolon) {
            (Some(Token::Semicolon), true) => {
                self.token_stream.next();
            }
            (Some(_), true) if !node.allow_omit_semicolon() => {
                let loc = node.src_loc().range.1;
                ErrorContent::ExpectsSemicolon
                    .wrap((node.src_loc().file_name, loc))
                    .collect_into(self.err_collector);
            }
            (Some(_), false) => {}
            (None, true) if !node.allow_omit_semicolon() => {
                let loc = node.src_loc().range.1;
                ErrorContent::ExpectsSemicolonFoundEOF
                    .wrap((node.src_loc().file_name, loc))
                    .collect_into(self.err_collector);
            }
            (None, false) => (),
            _ => (),
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
                let type_expr =
                    parse_type_expr(self, peeked_location).collect_err(self.err_collector)?;
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
                syntaxchecker::check_child(&rhs, self.err_collector);
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
            let arg_node = self
                .parse_expr(15, false)
                .ok_or(ErrorContent::UnexpectedEOF.wrap(peeked_location))
                .collect_err(self.err_collector)?;
            syntaxchecker::check_child(&arg_node, self.err_collector);
            let node_ref = self.ast.add_node(arg_node);
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
        let peek_token = peek_token!(self, start_loc);
        let peek_location = peek_token.src_loc();
        if let &Token::RoundParenClose = peek_token.inner() {
            self.token_stream.next();
            return Some(AstNode::Tuple(Vec::new()).traced((
                start_loc.file_name,
                start_loc.range.0,
                peek_location.range.1,
            )));
        }
        let inner_node = self
            .parse_expr(15, false)
            .ok_or(ErrorContent::UnexpectedEOF.wrap(start_loc))
            .collect_err(self.err_collector)?;
        syntaxchecker::check_child(&inner_node, self.err_collector);

        // if there's a closing parenthese, then it's just one node, if it's a comma, then it's a
        // tuple
        let loc = inner_node.src_loc();
        let peek = peek_token!(self, (loc.file_name, loc.range.1));
        let peek_loc = peek.src_loc();
        match peek.inner() {
            Token::RoundParenClose => {
                self.token_stream.next();
                Some(inner_node)
            }
            Token::Comma => {
                self.token_stream.next();
                let mut previous_loc = peek_loc;
                let mut nodes = vec![inner_node];
                let end_loc = loop {
                    let peek = peek_token!(self, previous_loc);
                    let peek_loc = peek.src_loc();
                    if let Token::RoundParenClose = peek.inner() {
                        self.token_stream.next();
                        break peek_loc;
                    }
                    let node = self
                        .parse_expr(15, false)
                        .ok_or(ErrorContent::UnexpectedEOF.wrap(peek_loc))
                        .collect_err(self.err_collector)?;
                    syntaxchecker::check_child(&node, self.err_collector);
                    previous_loc = node.src_loc();
                    nodes.push(node);
                    let peek = peek_token!(self, previous_loc);
                    let peek_loc = peek.src_loc();
                    match peek.inner() {
                        Token::Comma => {
                            self.token_stream.next();
                        }
                        Token::RoundParenClose => continue,
                        _ => {
                            ErrorContent::ExpectMultipleTokens(vec![
                                Token::Comma,
                                Token::RoundParenClose,
                            ])
                            .wrap(peek_loc)
                            .collect_into(self.err_collector);
                            break peek_loc;
                        }
                    }
                };
                let node = AstNode::Tuple(nodes);
                let node = node.traced((start_loc.file_name, start_loc.range.0, end_loc.range.1));
                Some(node)
            }
            _ => {
                ErrorContent::ExpectMultipleTokens(vec![Token::RoundParenClose, Token::Comma])
                    .wrap(peek_loc)
                    .collect_into(self.err_collector);
                Some(inner_node)
            }
        }
    }

    /// Parse a block, starting from the `{`
    /// Returns the `SourceLocation` of the block, and the child nodes
    /// Returns `None` if unexpected EOF, errors handled internally
    #[must_use]
    #[inline]
    fn parse_block<F>(
        &mut self,
        start_loc: SourceLocation<'src>,
        syntax_checker: F,
    ) -> Option<(SourceLocation<'src>, Vec<AstNodeRef<'src>>)>
    where
        F: Fn(&Traced<'src, AstNode<'src>>, &ErrorCollector<'src>),
    {
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
            syntax_checker(&node, self.err_collector);
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

    /// Parse a `loop` expression, starting from the token `loop`
    #[must_use]
    #[inline]
    fn parse_loop(
        &mut self,
        start_loc: SourceLocation<'src>,
    ) -> Option<Traced<'src, AstNode<'src>>> {
        let peek_token = peek_token!(self, start_loc);
        let peek_location = peek_token.src_loc();
        match peek_token.inner() {
            &Token::BraceOpen => {
                self.token_stream.next();
                let (end_loc, body) =
                    self.parse_block(peek_location, syntaxchecker::check_fn_body)?;
                let node = AstNode::Loop(body).traced((
                    start_loc.file_name,
                    start_loc.range.0,
                    end_loc.range.1,
                ));
                Some(node)
            }
            _ => {
                ErrorContent::ExpectToken(Token::BraceOpen)
                    .wrap(peek_location)
                    .collect_into(self.err_collector);
                // parse the expression regardless
                let node = self.parse_expr(15, false)?;
                Some(node)
            }
        }
    }

    /// Parse an `fn` expression, starting from the token `fn`
    /// # Parameters
    ///
    /// - `start_loc`: The source location of the token `fn`
    ///
    /// # Returns
    ///
    /// The parsed `fn` expression, or `None` if an error occurred
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
                parse_type_expr(self, peeked_location).collect_err(self.err_collector)?
            }
            &Token::BraceOpen | &Token::Semicolon | &Token::Comma => TypeExprNode::void().wrap(),
            _ => todo!("error"),
        };
        let peeked_token = next_token!(self, peeked_location);
        let peeked_location = peeked_token.src_loc();
        let body = match peeked_token.into_inner() {
            Token::BraceOpen => {
                let (body_end_loc, body) =
                    self.parse_block(peeked_location, syntaxchecker::check_fn_body)?;
                end_loc = body_end_loc.range.1;
                Some(body)
            }
            Token::Semicolon | Token::Comma => Option::None,
            _ => todo!("error"),
        };

        let node = AstNode::FnDef(FnDef {
            name,
            sign: FnSignature { args, ret_type },
            body,
        });
        Some(node.traced((start_loc.file_name, start_loc.range.0, end_loc)))
    }

    /// Parse arguments in a function definition, starting from the token `(`
    /// # Parameters
    ///
    /// * `start_loc` - The location of the `(` token
    ///
    /// # Returns
    ///
    /// A tuple of the arguments and the location of the `)` token, or `None` if an error occurs
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
            let arg_type = parse_type_expr(self, token_location).collect_err(self.err_collector)?;
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

    /// Parse an if expression, starting from the token `if`
    /// # Arguments
    ///
    /// * `start_loc`: The source location of the token `if`
    ///
    /// # Return
    ///
    /// The `AstNode` of the if expression, or `None` if an error occurred.
    #[must_use]
    #[inline]
    fn parse_if(&mut self, start_loc: SourceLocation<'src>) -> Option<Traced<'src, AstNode<'src>>> {
        let mut if_blocks = Vec::<(AstNodeRef<'src>, Vec<AstNodeRef<'src>>)>::new();
        let mut else_block = Option::<Vec<AstNodeRef<'src>>>::None;
        let mut end_loc: SourceLocation<'src>;
        macro_rules! no_brace_err {
            ($loc:expr) => {
                ErrorContent::ExpectToken(Token::BraceOpen)
                    .wrap($loc)
                    .collect_into(self.err_collector);
                let if_expr = IfExpr {
                    if_blocks,
                    else_block,
                };
                return Some(AstNode::If(if_expr).traced((
                    start_loc.file_name,
                    start_loc.range.0,
                    $loc.range.1,
                )));
            };
        }
        macro_rules! parse_if_condition_and_block {
            () => {
                let if_condition = self
                    .parse_expr(15, false)
                    .ok_or(ErrorContent::UnexpectedEOF.wrap(start_loc))
                    .collect_err(self.err_collector)?;
                syntaxchecker::check_child(&if_condition, self.err_collector);
                let if_condition = self.ast.add_node(if_condition);
                let peeked_token = peek_token!(self, start_loc);
                let peeked_location = peeked_token.src_loc();
                match peeked_token.inner() {
                    Token::BraceOpen => {
                        self.token_stream.next();
                        let (block_end_loc, body) =
                            self.parse_block(peeked_location, syntaxchecker::check_fn_body)?;
                        if_blocks.push((if_condition, body));
                        end_loc = block_end_loc;
                    }
                    _ => {
                        no_brace_err!(peeked_location);
                    }
                }
            };
        }

        // parse the first if block
        parse_if_condition_and_block!();

        // parse the rest of the `else if` blocks and `else block`
        loop {
            let peeked_token = peek_token!(self, start_loc);
            match peeked_token.inner() {
                Token::Else => {
                    self.token_stream.next();
                    let peeked_token = peek_token!(self, start_loc);
                    let peeked_location = peeked_token.src_loc();
                    match peeked_token.inner() {
                        Token::If => {
                            self.token_stream.next();
                            parse_if_condition_and_block!();
                        }
                        Token::BraceOpen => {
                            self.token_stream.next();
                            let (block_end_loc, body) =
                                self.parse_block(peeked_location, syntaxchecker::check_fn_body)?;
                            else_block = Some(body);
                            end_loc = block_end_loc;
                            break;
                        }
                        _ => {
                            no_brace_err!(peeked_location);
                        }
                    }
                }
                _ => break,
            }
        }
        let if_expr = IfExpr {
            if_blocks,
            else_block,
        };
        let node =
            AstNode::If(if_expr).traced((start_loc.file_name, start_loc.range.0, end_loc.range.1));
        Some(node)
    }

    /// Parse an array literal expression, starting from the token `[`
    /// # Parameters
    ///
    /// * `start_loc` - The source location of the `[` token
    ///
    /// # Returns
    ///
    /// An `AstNode::ArrLiteral` node, or `None` if an error occurred
    #[must_use]
    #[inline]
    fn parse_arr_literal(
        &mut self,
        start_loc: SourceLocation<'src>,
    ) -> Option<Traced<'src, AstNode<'src>>> {
        let mut arr_elements = Vec::<AstNodeRef<'src>>::new();
        let mut previous_loc = start_loc;
        let end_loc = loop {
            let peek_token = peek_token!(self, start_loc);
            match peek_token.inner() {
                &Token::RectParenClose => {
                    let peek_location = peek_token.src_loc();
                    self.token_stream.next();
                    break peek_location;
                }
                _ => {
                    let node = self
                        .parse_expr(15, false)
                        .ok_or(ErrorContent::UnexpectedEOF.wrap(previous_loc))
                        .collect_err(self.err_collector)?;
                    syntaxchecker::check_child(&node, self.err_collector);
                    let node_loc = node.src_loc();
                    previous_loc = (node_loc.file_name, node_loc.range.1).into_source_location();
                    let node_ref = self.ast.add_node(node);
                    arr_elements.push(node_ref);
                    let peek_token = peek_token!(self, previous_loc);
                    let peek_location = peek_token.src_loc();
                    match peek_token.inner() {
                        Token::Comma => {
                            self.token_stream.next();
                        }
                        Token::RectParenClose => (),
                        _ => ErrorContent::ExpectMultipleTokens(vec![
                            Token::Comma,
                            Token::RectParenClose,
                        ])
                        .wrap(peek_location)
                        .collect_into(self.err_collector),
                    }
                }
            }
        };
        let node = AstNode::Array(arr_elements);
        let node = node.traced((start_loc.file_name, start_loc.range.0, end_loc.range.1));
        Some(node)
    }

    /// Parse an enum definition, starting from the token `enum`
    /// Returns the the node of the `enum` definition expression
    /// Returns `None` if an EOF error is encountered (errors collected internally)
    ///
    /// # Parameters
    ///
    /// - `start_loc`: The source location of the `enum` token
    ///
    /// # Returns
    ///
    /// - `Some(Traced<AstNode>)`: The parsed enum definition and its source location
    /// - `None`: If an EOF error is encountered
    #[must_use]
    #[inline]
    fn parse_enum(
        &mut self,
        start_loc: SourceLocation<'src>,
    ) -> Option<Traced<'src, AstNode<'src>>> {
        let (name_loc, name) = expect_identifier!(self, start_loc, otherwise: return None);
        let braceopen_loc = expect_token!(self, name_loc, Token::BraceOpen, otherwise: return None);
        let mut previous_loc = braceopen_loc;
        let mut cases = Vec::<&'src str>::new();
        let end_loc = loop {
            let next_token = next_token!(self, previous_loc);
            let token_loc = next_token.src_loc();
            let case_name = match next_token.into_inner() {
                Token::BraceClose => {
                    break token_loc;
                }
                Token::Identifier(field_name) => field_name,
                _ => {
                    ErrorContent::ExpectMultipleTokens(vec![
                        Token::BraceClose,
                        Token::Identifier(""),
                    ])
                    .wrap(token_loc)
                    .collect_into(self.err_collector);
                    return None;
                }
            };
            cases.push(case_name);
            let peeked_token = peek_token!(self, token_loc);
            let peeked_location = peeked_token.src_loc();
            match peeked_token.inner() {
                Token::Comma => {
                    self.token_stream.next();
                }
                _ => (),
            }
            previous_loc = peeked_location;
        };
        let enum_def = EnumDef { name, cases };
        let node = AstNode::EnumDef(enum_def);
        Some(node.traced((start_loc.file_name, start_loc.range.0, end_loc.range.1)))
    }

    /// Parse a struct or union definition, starting from the token `struct` or `union`
    /// Returns the `StructOrUnionDef` information as well as the `SourceLocation` of the definition
    /// Returns `None` if an EOF error is encountered (errors collected internally)
    ///
    /// # Parameters
    ///
    /// - `start_loc`: The source location of the `struct` token
    ///
    /// # Returns
    ///
    /// - `Some((StructOrUnionDef, SourceLocation))`: The parsed struct or union definition and its source location
    /// - `None`: If an EOF error is encountered
    #[must_use]
    #[inline]
    fn parse_struct_or_union(
        &mut self,
        start_loc: SourceLocation<'src>,
    ) -> Option<(StructOrUnionDef<'src>, SourceLocation<'src>)> {
        let next_token = next_token!(self, start_loc);
        let token_loc = next_token.src_loc();
        let struct_name = next_token
            .expect_identifier()
            .ok_or(ErrorContent::ExpectToken(Token::Identifier("")).wrap(token_loc))
            .collect_err(self.err_collector)?;

        let braceopen_loc =
            expect_token!(self, token_loc, Token::BraceOpen, otherwise: return None);

        let mut fields = Vec::<(&'src str, TypeExpr<'src>)>::new();
        let mut previous_loc = braceopen_loc;
        let end_loc = loop {
            // get name
            let next_token = next_token!(self, previous_loc);
            let token_loc = next_token.src_loc();
            let field_name = match next_token.into_inner() {
                Token::BraceClose => {
                    break token_loc;
                }
                Token::Identifier(field_name) => field_name,
                _ => {
                    ErrorContent::ExpectMultipleTokens(vec![
                        Token::BraceClose,
                        Token::Identifier(""),
                    ])
                    .wrap(token_loc)
                    .collect_into(self.err_collector);
                    return None;
                }
            };

            let colon_loc = expect_token!(self, start_loc, Token::Colon, otherwise: return None);

            // get type
            let field_type = parse_type_expr(self, colon_loc).collect_err(self.err_collector)?;
            fields.push((field_name, field_type));

            let peeked_token = peek_token!(self, colon_loc);
            let peeked_location = peeked_token.src_loc();
            match peeked_token.inner() {
                Token::Comma => {
                    self.token_stream.next();
                }
                _ => (),
            }
            previous_loc = peeked_location;
        };
        let info = StructOrUnionDef {
            name: struct_name,
            fields,
        };
        let pos = (start_loc.file_name, start_loc.range.0, end_loc.range.1).into_source_location();
        Some((info, pos))
    }

    /// Parse a typedef statement, starting from the token `typedef`.
    /// # Parameters
    ///
    /// - `start_loc`: The source location of the `typedef` keyword.
    ///
    /// # Returns
    ///
    /// - `Some(node)`: The parsed typedef statement.
    /// - `None`: The statement is not a typedef statement.
    #[must_use]
    #[inline]
    fn parse_typedef(
        &mut self,
        start_loc: SourceLocation<'src>,
    ) -> Option<Traced<'src, AstNode<'src>>> {
        let token = next_token!(self, start_loc);
        let token_loc = token.src_loc();
        let typename = token
            .expect_identifier()
            .ok_or(ErrorContent::ExpectToken(Token::Identifier("")).wrap(token_loc))
            .collect_err(self.err_collector)?;
        let eq_token_loc = expect_token!(self, token_loc, Token::Eq, otherwise: return None);
        let rhs_type = parse_type_expr(self, eq_token_loc).collect_err(self.err_collector)?;
        let node = AstNode::TypeDef(typename, rhs_type);
        Some(node.traced((start_loc.file_name, start_loc.range.0, eq_token_loc.range.1)))
    }
}
