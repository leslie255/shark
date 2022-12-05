use std::{iter::Peekable, str::CharIndices};

use crate::{
    buffered_content::BufferedContent,
    error::{
        location::{IntoSourceLoc, Traced},
        CollectIfErr, Error, ErrorCollector, ErrorContent, StrOrChar,
    },
    token::Token,
};

use super::NumValue;

trait CharCustomFuncs {
    fn is_alphabetic_or_underscore(self) -> bool;
    fn is_alphanumeric_or_underscore(self) -> bool;
}

impl CharCustomFuncs for char {
    fn is_alphabetic_or_underscore(self) -> bool {
        self.is_alphabetic() || self == '_'
    }
    fn is_alphanumeric_or_underscore(self) -> bool {
        self.is_alphanumeric() || self == '_'
    }
}

/// Converts a hexadecimal numerical character to a number of type $t
/// If `result > 15` or `result < 0`, it is not a valid hex numeric
macro_rules! hex_char_to_digit {
    ($c: expr, $t: tt) => {
        ($c as $t)
            .wrapping_sub('0' as $t)
            .min(($c as $t).wrapping_sub('a' as $t - 10))
            .min(($c as $t).wrapping_sub('A' as $t - 10))
    };
}

#[allow(dead_code)]
#[derive(Debug)]
enum IterStackItem<'src> {
    Default(CharIndices<'src>),
    Included(CharIndices<'src>),
    MacroExpand(TokenStream<'src>),
}
#[derive(Debug, Clone)]
enum CharOrToken<'src> {
    Char(usize, char),
    Token(Traced<'src, Token<'src>>),
}

impl<'src> CharOrToken<'src> {
    fn as_char(&self) -> Option<(usize, char)> {
        if let &Self::Char(i, c) = self {
            Some((i, c))
        } else {
            None
        }
    }
    #[allow(dead_code)]
    fn as_token(&self) -> Option<&Traced<'src, Token<'src>>> {
        if let Self::Token(v) = self {
            Some(v)
        } else {
            None
        }
    }
    fn is_char_and_eq(&self, rhs: char) -> bool {
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
struct IterStack<'src> {
    stack: Vec<IterStackItem<'src>>,
}
impl<'src> IterStack<'src> {
    fn new(source: &'src str) -> Self {
        let chars_iter = source.char_indices();
        let stack_item = IterStackItem::Default(chars_iter);
        Self {
            stack: vec![stack_item],
        }
    }
    /// Push a new iterator onto the stack with the content of included file
    #[allow(dead_code)]
    fn include_source(&mut self, source: &'src str) {
        let chars_iter = source.char_indices();
        let stack_item = IterStackItem::Included(chars_iter);
        self.stack.push(stack_item);
    }
    /// Push a new iterator of tokens onto the stack containing tokens expanded from a macro
    #[allow(dead_code)]
    fn expand_macro(&mut self, token_stream: TokenStream<'src>) {
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
trait OptionCharOrToken<'a, T> {
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

/// Tokenizes a file incrementally, implements `Iterator`
#[derive(Debug)]
pub struct TokenStream<'src> {
    #[allow(dead_code)] // for expanding `#include` macros in the future
    buffers: &'src BufferedContent<'src>,
    path: &'src str,
    source: &'src str,
    iter: Peekable<IterStack<'src>>,
    err_collector: &'src ErrorCollector<'src>,
}
impl<'src> TokenStream<'src> {
    pub fn new(
        path: &'src str,
        buffers: &'src BufferedContent<'src>,
        err_collector: &'src ErrorCollector<'src>,
    ) -> Self {
        let source = buffers.read_file(path);
        Self {
            buffers,
            path,
            source,
            iter: IterStack::new(source).peekable(),
            err_collector,
        }
    }

    /// Parse an identifer *or a keyword*, starting from the second character
    /// Will always return `Some(...)`, just so it is consistent with other `parse_` functions
    fn parse_identifier(&mut self, start_index: usize) -> Option<Traced<'src, Token<'src>>> {
        let mut end_index = start_index;
        while let Some(CharOrToken::Char(i, c)) = self.iter.peek() {
            if !c.is_alphanumeric_or_underscore() {
                end_index = *i;
                break;
            }
            self.iter.next();
        }
        let str = &self.source[start_index..end_index];
        match str {
            "as" => Some(Token::As.wrap_loc((self.path, start_index, end_index))),
            "break" => Some(Token::Break.wrap_loc((self.path, start_index, end_index))),
            "continue" => Some(Token::Continue.wrap_loc((self.path, start_index, end_index))),
            "else" => Some(Token::Else.wrap_loc((self.path, start_index, end_index))),
            "enum" => Some(Token::Enum.wrap_loc((self.path, start_index, end_index))),
            "extern" => Some(Token::Extern.wrap_loc((self.path, start_index, end_index))),
            "false" => Some(Token::False.wrap_loc((self.path, start_index, end_index))),
            "fn" => Some(Token::Fn.wrap_loc((self.path, start_index, end_index))),
            "for" => Some(Token::For.wrap_loc((self.path, start_index, end_index))),
            "if" => Some(Token::If.wrap_loc((self.path, start_index, end_index))),
            "let" => Some(Token::Let.wrap_loc((self.path, start_index, end_index))),
            "loop" => Some(Token::Loop.wrap_loc((self.path, start_index, end_index))),
            "mut" => Some(Token::Mut.wrap_loc((self.path, start_index, end_index))),
            "pub" => Some(Token::Pub.wrap_loc((self.path, start_index, end_index))),
            "return" => Some(Token::Return.wrap_loc((self.path, start_index, end_index))),
            "static" => Some(Token::Static.wrap_loc((self.path, start_index, end_index))),
            "struct" => Some(Token::Struct.wrap_loc((self.path, start_index, end_index))),
            "true" => Some(Token::True.wrap_loc((self.path, start_index, end_index))),
            "union" => Some(Token::Union.wrap_loc((self.path, start_index, end_index))),
            "while" => Some(Token::While.wrap_loc((self.path, start_index, end_index))),
            _ => Some(Token::Identifier(str).wrap_loc((self.path, start_index, end_index))),
        }
    }

    /// Parse an identifer starting from the second character
    /// Unlike `parse_identifier(...)`, it does need to know the first character
    fn parse_number(
        &mut self,
        start_index: usize,
        first_ch: char,
    ) -> Option<Traced<'src, Token<'src>>> {
        let mut end_index = start_index;
        let mut val = first_ch as u64 - ('0' as u64);
        if val == 0 {
            // could be 0x, 0o, 0d, 0b prefix numbers
            let (suffix_index, second_char) =
                if let Some(&CharOrToken::Char(i, c)) = self.iter.peek() {
                    (i, c)
                } else {
                    let token = Token::Number(NumValue::U(0));
                    return Some(token.wrap_loc((self.path, start_index, end_index)));
                };
            match second_char {
                'x' => {
                    self.iter.next();
                    while let Some(&CharOrToken::Char(i, c)) = self.iter.peek() {
                        let digit = hex_char_to_digit!(c, u64);
                        if digit > 15 {
                            end_index = i;
                            break;
                        }
                        val *= 16;
                        val += digit;
                        self.iter.next();
                    }
                    let token = Token::Number(NumValue::U(val));
                    Some(token.wrap_loc((self.path, start_index, end_index)))
                }
                'd' => {
                    self.iter.next();
                    while let Some(&CharOrToken::Char(i, c)) = self.iter.peek() {
                        let digit = (c as u64).wrapping_sub('0' as u64);
                        if digit > 9 {
                            end_index = i;
                            break;
                        }
                        val *= 10;
                        val += digit;
                        self.iter.next();
                    }
                    let token = Token::Number(NumValue::U(val));
                    Some(token.wrap_loc((self.path, start_index, end_index)))
                }
                'o' => {
                    self.iter.next();
                    while let Some(&CharOrToken::Char(i, c)) = self.iter.peek() {
                        let digit = (c as u64).wrapping_sub('0' as u64);
                        if digit > 7 {
                            end_index = i;
                            break;
                        }
                        val *= 8;
                        val += digit;
                        self.iter.next();
                    }
                    let token = Token::Number(NumValue::U(val));
                    Some(token.wrap_loc((self.path, start_index, end_index)))
                }
                'b' => {
                    self.iter.next();
                    while let Some(&CharOrToken::Char(i, c)) = self.iter.peek() {
                        match c {
                            '0' => {
                                val <<= 1;
                            }
                            '1' => {
                                val <<= 1;
                                val |= 1;
                            }
                            _ => {
                                end_index = i;
                                break;
                            }
                        }
                        self.iter.next();
                    }
                    let token = Token::Number(NumValue::U(val));
                    Some(token.wrap_loc((self.path, start_index, end_index)))
                }
                '.' => todo!("Parse floating point numbers"),
                c if c.is_numeric() => {
                    self.iter.next();
                    val += second_char as u64 - ('0' as u64);
                    while let Some(&CharOrToken::Char(i, c)) = self.iter.peek() {
                        let digit = (c as u64).wrapping_sub('0' as u64);
                        if digit > 9 {
                            end_index = i;
                            break;
                        }
                        val *= 10;
                        val += digit;
                        self.iter.next();
                    }
                    let token = Token::Number(NumValue::U(val));
                    Some(token.wrap_loc((self.path, start_index, end_index)))
                }
                c if c.is_alphabetic_or_underscore() => {
                    ErrorContent::InvalidIntSuffix(c)
                        .wrap((self.path, suffix_index))
                        .collect_into(self.err_collector);
                    None
                }
                _ => Some(Token::Number(NumValue::U(0)).wrap_loc((
                    self.path,
                    start_index,
                    end_index,
                ))),
            }
        } else {
            // TODO: floating point numbers
            while let Some(&CharOrToken::Char(i, c)) = self.iter.peek() {
                let digit = (c as u64).wrapping_sub('0' as u64);
                if digit > 9 {
                    end_index = i;
                    if c == '.' {
                        todo!("Parse floating point numbers");
                    }
                    break;
                }
                val *= 10;
                val += digit;
                self.iter.next();
            }
            let token = Token::Number(NumValue::U(val));
            Some(token.wrap_loc((self.path, start_index, end_index)))
        }
    }

    fn parse_string_escape(
        &mut self,
        str_or_char: StrOrChar,
        i: usize,
    ) -> Result<char, Error<'src>> {
        macro_rules! eof_err {
            () => {
                ErrorContent::EofInStringOrChar(str_or_char)
            };
        }
        let escape_char = self
            .iter
            .next()
            .err_if_eof((self.path, i))?
            .as_char()
            .unwrap()
            .1;
        match escape_char {
            'x' => {
                let (_, ch) = self
                    .iter
                    .next()
                    .err_if_eof((self.path, i))?
                    .as_char()
                    .unwrap();
                let digit0 = hex_char_to_digit!(ch, u8);
                let (i1, ch) = self
                    .iter
                    .next()
                    .err_if_eof((self.path, i))?
                    .as_char()
                    .unwrap();
                let digit1 = hex_char_to_digit!(ch, u8);
                if digit0 > 15 {
                    ErrorContent::NumericEscNonHexDigit
                        .wrap((self.path, i1))
                        .collect_into(self.err_collector)
                }
                if digit1 > 15 {
                    ErrorContent::NumericEscNonHexDigit
                        .wrap((self.path, i1))
                        .collect_into(self.err_collector)
                }
                Ok((digit0 * 16 + digit1) as char)
            }
            'u' => {
                let (i, ch) = self
                    .iter
                    .next()
                    .err_if_eof((self.path, i))?
                    .as_char()
                    .unwrap();
                if ch != '{' {
                    return Err(ErrorContent::UnicodeEscNoOpeningBrace.wrap((self.path, i)));
                }
                let mut val = 0u32;
                let mut count = 0usize;
                while let Some(CharOrToken::Char(i, _)) =
                    self.iter.next_if(|t| !t.is_char_and_eq('}'))
                {
                    count += 1;
                    val *= 16;
                    if count > 6 {
                        return Err(ErrorContent::UnicodeEscOverflow.wrap((self.path, i)));
                    }
                    let digit = hex_char_to_digit!(ch, u32);
                    if digit > 15 {
                        return Err(ErrorContent::UnicodeEscNonHexDigit.wrap((self.path, i)));
                    }
                    val += digit;
                }
                match self.iter.next() {
                    Some(CharOrToken::Char(_, '}')) => Ok(unsafe { char::from_u32_unchecked(val) }),
                    Some(_) => Err(ErrorContent::UnicodeEscNoClosingBrace.wrap((self.path, i))),
                    None => Err(eof_err!().wrap((self.path, i + count))),
                }
            }
            'n' => Ok('\n'),
            'r' => Ok('\r'),
            't' => Ok('\t'),
            '\\' => Ok('\\'),
            '0' => Ok('\0'),
            '\'' => Ok('\''),
            '\"' => Ok('\"'),
            c => Err(ErrorContent::InvalidCharEsc(c).wrap((self.path, i))),
        }
    }

    /// Parse a character literal, starting from the character after quote sign
    /// Errors are handled internally
    fn parse_char(&mut self, start_index: usize) -> Option<Traced<'src, Token<'src>>> {
        let (i, ch) = match self
            .iter
            .next()
            .ok_or(ErrorContent::EofInStringOrChar(StrOrChar::Str).wrap((self.path, start_index)))
            .collect_err(self.err_collector)?
            .as_char()
            .unwrap()
        {
            (i, '\\') => {
                let esc_char = self
                    .parse_string_escape(StrOrChar::Char, i)
                    .collect_err(self.err_collector)
                    .unwrap_or_default();
                (i, esc_char)
            }
            (i, ch) => (i, ch),
        };
        let (end_index, next_char) = self
            .iter
            .next()
            .ok_or(ErrorContent::EofInStringOrChar(StrOrChar::Str).wrap((self.path, i)))
            .collect_err(self.err_collector)?
            .as_char()
            .ok_or(ErrorContent::EofInStringOrChar(StrOrChar::Str).wrap((self.path, i)))
            .collect_err(self.err_collector)?;
        if next_char == '\'' {
            let token = Token::Character(ch);
            Some(token.wrap_loc((self.path, start_index, end_index)))
        } else {
            ErrorContent::CharNoEndQuote
                .wrap((self.path, end_index))
                .collect_into(self.err_collector);
            None
        }
    }

    /// Parse a string literal, start from the character after quote sign
    /// Errors handled internally
    fn parse_string(&mut self, start_index: usize) -> Option<Traced<'src, Token<'src>>> {
        let mut parsed_string = String::new();
        let mut end_index = start_index;
        if self.iter.peek().is_none() {
            ErrorContent::EofInStringOrChar(StrOrChar::Str)
                .wrap((self.path, start_index))
                .collect_into(self.err_collector);
            return None;
        }
        while let Some(CharOrToken::Char(current_index, ch)) =
            self.iter.next_if(|x| !x.is_char_and_eq('\"'))
        {
            if ch == '\\' {
                let esc_char = self
                    .parse_string_escape(StrOrChar::Str, current_index)
                    .collect_err(self.err_collector)
                    .unwrap_or('\0');
                parsed_string.push(esc_char);
            } else {
                parsed_string.push(ch);
            }
        }
        if let Some(CharOrToken::Char(i, _)) = self.iter.next() {
            end_index = i;
        }
        Some(Token::String(parsed_string).wrap_loc((self.path, start_index, end_index)))
    }
}
impl<'src> Iterator for TokenStream<'src> {
    type Item = Traced<'src, Token<'src>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            macro_rules! peek {
                () => {
                    self.iter.peek()
                };
            }
            macro_rules! case {
                ($c: expr) => {
                    Some(&CharOrToken::Char(_, $c))
                };
            }
            macro_rules! token {
                ($content: tt, $i: expr) => {{
                    Some(Token::$content.wrap_loc((self.path, $i)))
                }};
                ($content: tt, $i: expr, 1) => {{
                    self.iter.next();
                    Some(Token::$content.wrap_loc((self.path, $i, $i + 1)))
                }};
                ($content: tt, $i: expr, 2) => {{
                    self.iter.next();
                    Some(Token::$content.wrap_loc((self.path, $i, $i + 2)))
                }};
            }
            let x = self.iter.next();
            println!("{}:{}\t{x:?}", file!(), line!());
            let (i, c) = match x? {
                CharOrToken::Char(i, c) => (i, c),
                CharOrToken::Token(t) => return Some(t),
            };
            break match (i, c) {
                (_, c) if c.is_whitespace() => {
                    println!("lol");
                    println!("{:?}", self.iter.peek());
                    continue;
                },

                // Values
                (i, c) if c.is_alphabetic_or_underscore() => self.parse_identifier(i),
                (i, c) if c.is_numeric() => self.parse_number(i, c),
                (i, '\'') => self.parse_char(i),
                (i, '\"') => self.parse_string(i),

                // Operators
                (i, '~') => token!(Squiggle, i),
                (i, '(') => token!(RoundParenOpen, i),
                (i, ')') => token!(RoundParenClose, i),
                (i, '[') => token!(RectParenOpen, i),
                (i, ']') => token!(RectParenClose, i),
                (i, '{') => token!(BraceOpen, i),
                (i, '}') => token!(BraceClose, i),
                (i, ':') => token!(Colon, i),
                (i, ';') => token!(Semicolon, i),
                (i, '.') => token!(Dot, i),

                (i, '+') => match peek!() {
                    case!('=') => token!(AddEq, i, 1),
                    _ => token!(Add, i),
                },
                (i, '-') => match peek!() {
                    case!('=') => token!(SubEq, i, 1),
                    case!('>') => token!(Arrow, i, 1),
                    _ => token!(Sub, i),
                },
                (i, '*') => match peek!() {
                    case!('=') => token!(MulEq, i, 1),
                    _ => token!(Mul, i),
                },
                (i, '/') => match peek!() {
                    case!('=') => token!(DivEq, i, 1),
                    case!('/') => {
                        // Single line comment
                        while let Some(CharOrToken::Char(_, c)) = self.iter.next() {
                            if c == '\n' {
                                break;
                            }
                        }
                        continue;
                    }
                    case!('*') => {
                        // Multi-line comment
                        let mut level = 1usize;
                        while level != 0 {
                            match peek!()?.as_char().unwrap().1 {
                                '/' => {
                                    if self.iter.next()?.as_char().unwrap().1 == '*' {
                                        level += 1;
                                    }
                                }
                                '*' => {
                                    if self.iter.next()?.as_char().unwrap().1 == '/' {
                                        level -= 1;
                                    }
                                }
                                _ => (),
                            }
                        }
                        continue;
                    }
                    _ => token!(Div, i),
                },
                (i, '%') => match peek!() {
                    case!('=') => token!(ModEq, i, 1),
                    _ => token!(Mod, i),
                },
                (i, '|') => match peek!() {
                    case!('=') => token!(OrEq, i, 1),
                    case!('|') => token!(OrOr, i, 1),
                    _ => token!(OrOp, i),
                },
                (i, '&') => match peek!() {
                    case!('=') => token!(AndEq, i, 1),
                    case!('&') => token!(AndAnd, i, 1),
                    _ => token!(AndOp, i),
                },
                (i, '^') => match peek!() {
                    case!('=') => token!(XorEq, i, 1),
                    _ => token!(XorOp, i),
                },
                (i, '=') => match peek!() {
                    case!('=') => token!(EqEq, i, 1),
                    _ => token!(Eq, i),
                },
                (i, '!') => match peek!() {
                    case!('=') => token!(ExcEq, i, 1),
                    _ => token!(Exc, i),
                },

                (i, '<') => match peek!() {
                    case!('=') => token!(LeEq, i, 1),
                    case!('<') => {
                        self.iter.next();
                        match peek!() {
                            case!('=') => token!(LeLeEq, i, 2),
                            _ => token!(LeLe, i, 1),
                        }
                    }
                    _ => token!(Le, i),
                },
                (i, '>') => match peek!() {
                    case!('=') => token!(GrEq, i, 1),
                    case!('>') => {
                        self.iter.next();
                        match peek!() {
                            case!('=') => token!(GrGrEq, i, 2),
                            _ => token!(GrGr, i, 1),
                        }
                    }
                    _ => Some(Token::Gr.wrap_loc((self.path, i, i))),
                },
                (i, c) => {
                    ErrorContent::InvalidCharacter(c)
                        .wrap((self.path, i))
                        .collect_into(self.err_collector);
                    continue;
                }
            };
        }
    }
}
