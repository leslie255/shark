use std::{iter::Peekable, str::CharIndices};

use crate::{buffered_content::BufferedContent, error::location::Traced, token::Token};

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

/// Tokenizes a file on-the-pass, implements an iterator for scanning through a file
#[derive(Debug)]
pub struct TokenStream<'a> {
    buffed_sources: &'a BufferedContent<'a>,
    path: &'a str,
    source: &'a str,
    iter: Peekable<CharIndices<'a>>,
}
impl<'a> TokenStream<'a> {
    pub fn new(path: &'a str, buffed_sources: &'a BufferedContent<'a>) -> Self {
        let source = buffed_sources.open_file(path);
        Self {
            buffed_sources,
            path,
            source,
            iter: source.char_indices().peekable(),
        }
    }

    /// Parse an identifer *or a keyword*, starting from the second character
    /// Will always return `Some(...)`, just so it is consistent with other `parse_` functions
    fn parse_identifier(&mut self, start_index: usize) -> Option<Traced<'a, Token<'a>>> {
        let mut end_index = start_index;
        while let Some((i, c)) = self.iter.peek() {
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
    #[allow(unused_variables)]
    fn parse_number(
        &mut self,
        start_index: usize,
        first_ch: char,
    ) -> Option<Traced<'a, Token<'a>>> {
        let mut end_index = start_index;
        let mut val = first_ch as u64 - ('0' as u64);
        if val == 0 {
            // could be 0x, 0o, 0d, 0b prefix numbers
            let second_char = if let Some((_, c)) = self.iter.peek() {
                c
            } else {
                let token = Token::Number(NumValue::U(0));
                return Some(token.wrap_loc((self.path, start_index, end_index)));
            };
            match second_char {
                'x' => {
                    self.iter.next();
                    while let Some((i, c)) = self.iter.peek() {
                        let digit = hex_char_to_digit!(*c, u64);
                        if digit > 15 {
                            end_index = *i;
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
                    while let Some((i, c)) = self.iter.peek() {
                        let digit = (*c as u64).wrapping_sub('0' as u64);
                        if digit > 9 {
                            end_index = *i;
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
                    while let Some((i, c)) = self.iter.peek() {
                        let digit = (*c as u64).wrapping_sub('0' as u64);
                        if digit > 7 {
                            end_index = *i;
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
                    while let Some((i, c)) = self.iter.peek() {
                        match *c {
                            '0' => {
                                val <<= 1;
                            }
                            '1' => {
                                val <<= 1;
                                val |= 1;
                            }
                            _ => {
                                end_index = *i;
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
                    let second_char = *second_char;
                    self.iter.next();
                    val += second_char as u64 - ('0' as u64);
                    while let Some((i, c)) = self.iter.peek() {
                        let digit = (*c as u64).wrapping_sub('0' as u64);
                        if digit > 9 {
                            end_index = *i;
                            break;
                        }
                        val *= 10;
                        val += digit;
                        self.iter.next();
                    }
                    let token = Token::Number(NumValue::U(val));
                    Some(token.wrap_loc((self.path, start_index, end_index)))
                }
                c if c.is_alphabetic_or_underscore() => panic!(
                    "Expects 0~9, x, o, d, b after `0`, found `{}`",
                    c.escape_default()
                ),
                _ => Some(Token::Number(NumValue::U(0)).wrap_loc((
                    self.path,
                    start_index,
                    end_index,
                ))),
            }
        } else {
            // TODO: floating point numbers
            while let Some((i, c)) = self.iter.peek() {
                let digit = (*c as u64).wrapping_sub('0' as u64);
                if digit > 9 {
                    end_index = *i;
                    if *c == '.' {
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

    fn parse_string_escape(&mut self) -> char {
        match self.iter.next().expect("Unexpected EOF after backslash").1 {
            'x' => {
                let (_, ch) = self
                    .iter
                    .next()
                    .expect("Unexpected EOF after `\\x` escape sequence");
                let digit0 = hex_char_to_digit!(ch, u8);
                let (_, ch) = self
                    .iter
                    .next()
                    .expect("Unexpected EOF after `\\x` escape sequence");
                let digit1 = hex_char_to_digit!(ch, u8);
                if digit0 > 15 || digit1 > 15 {
                    panic!("Non-hex digit following `\\x` in escape sequence")
                }
                (digit0 * 16 + digit1) as char
            }
            'u' => {
                let (_, ch) = self
                    .iter
                    .next()
                    .expect("Unexpected EOF after `\\x` escape sequence");
                if ch != '{' {
                    panic!("Expects `{{` after `\\u` in escape sequence");
                }
                let mut val = 0u32;
                let mut count = 0usize;
                while let Some((_, ch)) = self.iter.next_if(|&(_, c)| c != '}') {
                    count += 1;
                    val *= 16;
                    if count > 6 {
                        panic!("Only 6 hex digits are allowed in \\u{{...}} escape sequence")
                    }
                    let digit = hex_char_to_digit!(ch, u32);
                    if digit > 15 {
                        panic!("Only hex digits are allowed in \\u{{...}} escape sequence")
                    }
                    val += digit;
                }
                match self.iter.next() {
                    Some((_, '}')) => (),
                    Some((_, c)) => panic!(
                        "Expects `}}` at the end of \\u{{...}} escape sequence, found `{}`",
                        c.escape_debug()
                    ),
                    None => {
                        panic!("Expects `}}` at the end of \\u{{...}} escape sequence, found EOF")
                    }
                }
                unsafe { char::from_u32_unchecked(val) }
            }
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            '\\' => '\\',
            '0' => '\0',
            '\'' => '\'',
            '\"' => '\"',
            c => panic!("Unsupported escape code `{}`", c.escape_debug()),
        }
    }

    /// Parse a character literal
    fn parse_char(&mut self, start_index: usize) -> Option<Traced<'a, Token<'a>>> {
        match self
            .iter
            .next()
            .expect("Unexpected EOF after single quote sign")
        {
            (_, '\\') => {
                let c = self.parse_string_escape();
                if let (end_index, '\'') = self
                    .iter
                    .next()
                    .expect("Expects single quote sign, found EOF")
                {
                    Some(Token::Character(c).wrap_loc((self.path, start_index, end_index)))
                } else {
                    panic!("Expects single quote sign");
                }
            }
            (_, c) => {
                if let (end_index, '\'') = self
                    .iter
                    .next()
                    .expect("Expects single quote sign, found EOF")
                {
                    let token = Token::Character(c);
                    Some(token.wrap_loc((self.path, start_index, end_index)))
                } else {
                    panic!("Expects single quote sign");
                }
            }
        }
    }

    /// Parse a string literal
    /// Start from the character after quote sign
    fn parse_string(&mut self, start_index: usize) -> Option<Traced<'a, Token<'a>>> {
        let mut parsed_string = String::new();
        let mut end_index = start_index;
        while let Some((_, ch)) = self.iter.next_if(|&(_, c)| c != '\"') {
            if ch == '\\' {
                parsed_string.push(self.parse_string_escape());
            } else {
                parsed_string.push(ch);
            }
        }
        if let Some((i, _)) = self.iter.next() {
            end_index = i;
        }
        Some(Token::String(parsed_string).wrap_loc((self.path, start_index, end_index)))
    }
}
impl<'a> Iterator for TokenStream<'a> {
    type Item = Traced<'a, Token<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            macro_rules! next_and_ret_token {
                ($t: tt, $i0: expr, $i1: expr) => {{
                    self.iter.next();
                    Some(Token::$t.wrap_loc((self.path, $i0, $i1)))
                }};
            }
            break match self.iter.next()? {
                (_, c) if c.is_whitespace() => continue,

                // Values
                (i, c) if c.is_alphabetic_or_underscore() => self.parse_identifier(i),
                (i, c) if c.is_numeric() => self.parse_number(i, c),
                (i, '\'') => self.parse_char(i),
                (i, '\"') => self.parse_string(i),

                // Operators
                (i, '~') => Some(Token::Squiggle.wrap_loc((self.path, i, i))),
                (i, '(') => Some(Token::RoundParenOpen.wrap_loc((self.path, i, i))),
                (i, ')') => Some(Token::RoundParenClose.wrap_loc((self.path, i, i))),
                (i, '[') => Some(Token::RectParenOpen.wrap_loc((self.path, i, i))),
                (i, ']') => Some(Token::RectParenClose.wrap_loc((self.path, i, i))),
                (i, '{') => Some(Token::BraceOpen.wrap_loc((self.path, i, i))),
                (i, '}') => Some(Token::BraceClose.wrap_loc((self.path, i, i))),
                (i, ':') => Some(Token::Colon.wrap_loc((self.path, i, i))),
                (i, ';') => Some(Token::Semicolon.wrap_loc((self.path, i, i))),
                (i, '.') => Some(Token::Dot.wrap_loc((self.path, i, i))),

                (i, '+') => match self.iter.peek().clone() {
                    Some(&(i0, '=')) => next_and_ret_token!(AddEq, i, i0),
                    _ => Some(Token::Add.wrap_loc((self.path, i, i))),
                },
                (i, '-') => match self.iter.peek() {
                    Some(&(i0, '=')) => next_and_ret_token!(SubEq, i, i0),
                    Some(&(i0, '>')) => next_and_ret_token!(Arrow, i, i0),
                    _ => Some(Token::Sub.wrap_loc((self.path, i, i))),
                },
                (i, '*') => match self.iter.peek() {
                    Some(&(i0, '=')) => next_and_ret_token!(MulEq, i, i0),
                    _ => Some(Token::Mul.wrap_loc((self.path, i, i))),
                },
                (i, '/') => match self.iter.peek() {
                    Some(&(i0, '=')) => next_and_ret_token!(DivEq, i, i0),
                    Some(&(_, '/')) => {
                        // Single line comment
                        while let Some((_, c)) = self.iter.next() {
                            if c == '\n' {
                                break;
                            }
                        }
                        continue;
                    }
                    Some(&(_, '*')) => {
                        // Multi-line comment
                        let mut level = 1usize;
                        while level != 0 {
                            match self.iter.next()?.1 {
                                '/' => {
                                    if self.iter.next()?.1 == '*' {
                                        level += 1;
                                    }
                                }
                                '*' => {
                                    if self.iter.next()?.1 == '/' {
                                        level -= 1;
                                    }
                                }
                                _ => (),
                            }
                        }
                        continue;
                    }
                    _ => Some(Token::Div.wrap_loc((self.path, i, i))),
                },
                (i, '%') => match self.iter.peek() {
                    Some(&(i0, '=')) => next_and_ret_token!(ModEq, i, i0),
                    _ => Some(Token::Mod.wrap_loc((self.path, i, i))),
                },
                (i, '|') => match self.iter.peek() {
                    Some(&(i0, '=')) => next_and_ret_token!(OrEq, i, i0),
                    Some(&(i0, '|')) => next_and_ret_token!(OrOr, i, i0),
                    _ => Some(Token::OrOp.wrap_loc((self.path, i, i))),
                },
                (i, '&') => match self.iter.peek() {
                    Some(&(i0, '=')) => next_and_ret_token!(AndEq, i, i0),
                    Some(&(i0, '&')) => next_and_ret_token!(AndAnd, i, i0),
                    _ => Some(Token::AndOp.wrap_loc((self.path, i, i))),
                },
                (i, '^') => match self.iter.peek() {
                    Some(&(i0, '=')) => next_and_ret_token!(XorEq, i, i0),
                    _ => Some(Token::XorOp.wrap_loc((self.path, i, i))),
                },
                (i, '=') => match self.iter.peek() {
                    Some(&(i0, '=')) => next_and_ret_token!(EqEq, i, i0),
                    _ => Some(Token::Eq.wrap_loc((self.path, i, i))),
                },
                (i, '!') => match self.iter.peek() {
                    Some(&(i0, '=')) => next_and_ret_token!(ExcEq, i, i0),
                    _ => Some(Token::Exc.wrap_loc((self.path, i, i))),
                },

                (i, '<') => match self.iter.peek() {
                    Some(&(i0, '=')) => next_and_ret_token!(LeEq, i, i0),
                    Some(&(i0, '<')) => {
                        self.iter.next();
                        match self.iter.peek() {
                            Some(&(i0, '=')) => next_and_ret_token!(LeLeEq, i, i0),
                            _ => Some(Token::LeLe.wrap_loc((self.path, i, i0))),
                        }
                    }
                    _ => Some(Token::XorOp.wrap_loc((self.path, i, i))),
                },
                (i, '>') => match self.iter.peek() {
                    Some(&(i0, '=')) => next_and_ret_token!(LeEq, i, i0),
                    Some(&(i0, '>')) => {
                        self.iter.next();
                        match self.iter.peek() {
                            Some(&(i0, '=')) => next_and_ret_token!(GrGrEq, i, i0),
                            _ => Some(Token::GrGr.wrap_loc((self.path, i, i0))),
                        }
                    }
                    _ => Some(Token::XorOp.wrap_loc((self.path, i, i))),
                },
                (_, c) => panic!("Unexpected character `{}`", c.escape_debug()),
            };
        }
    }
}
