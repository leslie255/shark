use std::{collections::HashMap, fs, iter::Peekable, str::CharIndices};

use crate::{errors::location::Traced, token::Token};

use super::NumValue;

/// Contents of source files used during compilation
/// Allows for no copying for identifier strings and will be used for error reporting
/// Does not own the path strings
/// TODO: buffers parsed tokens to prevent re-lexing a header file included multiple times
#[derive(Debug, Clone, Default)]
pub struct BufferedSources<'a> {
    map: HashMap<&'a str, String>,
}

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
    buffed_sources: &'a mut BufferedSources<'a>,
    path: &'a str,
    source: &'a String,
    iter: Peekable<CharIndices<'a>>,
}
impl<'a> TokenStream<'a> {
    pub fn new(path: &'a str, buffed_sources: &'a mut BufferedSources<'a>) -> Self {
        let source = if let Some(source) = buffed_sources.map.get(path) {
            source
        } else {
            let content = fs::read_to_string(path).expect("Unable to read file: {:?}");
            buffed_sources.map.insert(path, content);
            buffed_sources.map.get(path).unwrap()
        };
        let borrow = unsafe { (source as *const String).as_ref().unwrap() };
        TokenStream {
            buffed_sources,
            path,
            source: borrow,
            iter: borrow.char_indices().peekable(),
        }
    }

    /// Parse an identifer, starting from the second character
    /// This function will always return `Some(...)`, just so it is consistent with other
    /// `parse_` functions
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
            let second_char = if let Some((_, c)) = self.iter.next() {
                c
            } else {
                let token = Token::Number(NumValue::U(0));
                return Some(token.wrap_loc((self.path, start_index, end_index)));
            };
            match second_char {
                'x' => {
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
                _ => panic!("Expects 0~9, x, o, d, b after `0`"),
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
            'u' => todo!("Unicode escape code"),
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

                (i, c) if c.is_alphabetic_or_underscore() => self.parse_identifier(i),
                (i, c) if c.is_numeric() => self.parse_number(i, c),
                (i, '\'') => self.parse_char(i),
                (i, '\"') => self.parse_string(i),

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
