use std::{iter::Peekable, str::CharIndices};

use crate::{
    buffered_content::BufferedContent,
    error::{location::Traced, CollectIfErr, Error, ErrorCollector, ErrorContent, StrOrChar},
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

/// Tokenizes a file incrementally, implements `Iterator`
#[derive(Debug)]
pub struct TokenStream<'src> {
    #[allow(dead_code)] // for expanding `#include` macros in the future
    buffers: &'src BufferedContent<'src>,
    path: &'src str,
    source: &'src str,
    iter: Peekable<CharIndices<'src>>,
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
            iter: source.char_indices().peekable(),
            err_collector,
        }
    }

    /// Parse an identifer *or a keyword*, starting from the second character
    /// Will always return `Some(...)`, just so it is consistent with other `parse_` functions
    fn parse_identifier(&mut self, start_index: usize) -> Option<Traced<'src, Token<'src>>> {
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
    fn parse_number(
        &mut self,
        start_index: usize,
        first_ch: char,
    ) -> Option<Traced<'src, Token<'src>>> {
        let mut end_index = start_index;
        let mut val = first_ch as u64 - ('0' as u64);
        if val == 0 {
            // could be 0x, 0o, 0d, 0b prefix numbers
            let (suffix_index, second_char) = if let Some(x) = self.iter.peek() {
                *x
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
        let escape_char = self.iter.next().ok_or(eof_err!().wrap((self.path, i)))?.1;
        match escape_char {
            'x' => {
                let (i0, ch) = self.iter.next().ok_or(eof_err!().wrap((self.path, i)))?;
                let digit0 = hex_char_to_digit!(ch, u8);
                let (i1, ch) = self.iter.next().ok_or(eof_err!().wrap((self.path, i0)))?;
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
                let (i, ch) = self.iter.next().ok_or(eof_err!().wrap((self.path, i)))?;
                if ch != '{' {
                    return Err(ErrorContent::UnicodeEscNoOpeningBrace.wrap((self.path, i)));
                }
                let mut val = 0u32;
                let mut count = 0usize;
                while let Some((i, ch)) = self.iter.next_if(|&(_, c)| c != '}') {
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
                    Some((_, '}')) => Ok(unsafe { char::from_u32_unchecked(val) }),
                    Some((i, _)) => {
                        Err(ErrorContent::UnicodeEscNoClosingBrace.wrap((self.path, i)))
                    }
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
        match self
            .iter
            .next()
            .ok_or(ErrorContent::EofInStringOrChar(StrOrChar::Str).wrap((self.path, start_index)))
            .collect_err(self.err_collector)?
        {
            (i, '\\') => {
                let esc_char = self
                    .parse_string_escape(StrOrChar::Char, i)
                    .collect_err(self.err_collector)
                    .unwrap_or('\0');
                let (end_index, next_char) = self
                    .iter
                    .next()
                    .ok_or(ErrorContent::EofInStringOrChar(StrOrChar::Char).wrap((self.path, i)))
                    .collect_err(self.err_collector)?;
                if next_char == '\'' {
                    Some(Token::Character(esc_char).wrap_loc((self.path, start_index, end_index)))
                } else {
                    ErrorContent::CharNoEndQuote
                        .wrap((self.path, end_index))
                        .collect_into(self.err_collector);
                    None
                }
            }
            (i, c) => {
                let (end_index, next_char) = self
                    .iter
                    .next()
                    .ok_or(ErrorContent::EofInStringOrChar(StrOrChar::Str).wrap((self.path, i)))
                    .collect_err(self.err_collector)?;
                if next_char == '\'' {
                    let token = Token::Character(c);
                    Some(token.wrap_loc((self.path, start_index, end_index)))
                } else {
                    ErrorContent::CharNoEndQuote
                        .wrap((self.path, end_index))
                        .collect_into(self.err_collector);
                    None
                }
            }
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
        while let Some((current_index, ch)) = self.iter.next_if(|&(_, c)| c != '\"') {
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
        if let Some((i, _)) = self.iter.next() {
            end_index = i;
        }
        Some(Token::String(parsed_string).wrap_loc((self.path, start_index, end_index)))
    }
}
impl<'src> Iterator for TokenStream<'src> {
    type Item = Traced<'src, Token<'src>>;

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
                    _ => Some(Token::Le.wrap_loc((self.path, i, i))),
                },
                (i, '>') => match self.iter.peek() {
                    Some(&(i0, '=')) => next_and_ret_token!(GrEq, i, i0),
                    Some(&(i0, '>')) => {
                        self.iter.next();
                        match self.iter.peek() {
                            Some(&(i0, '=')) => next_and_ret_token!(GrGrEq, i, i0),
                            _ => Some(Token::GrGr.wrap_loc((self.path, i, i0))),
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
