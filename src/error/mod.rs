pub mod location;

use std::cell::RefCell;

use colored::Colorize;
use location::{IntoSourceLoc, SourceLocation};

use crate::buffered_content::BufferedContent;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StrOrChar {
    Str,
    Char,
}

#[derive(Debug, Clone)]
pub enum ErrorContent<'src> {
    // --- Tokenizer stage
    InvalidCharacter(char),

    // String or character literal
    EofInStringOrChar(StrOrChar),
    UnicodeEscOverflow,
    UnicodeEscNonHexDigit,
    UnicodeEscNoOpeningBrace,
    UnicodeEscNoClosingBrace,
    NumericEscNonHexDigit,
    InvalidCharEsc(char),
    CharNoEndQuote,

    // Number literal
    /// "Expects 0~9, x, o, d, b after `0`"
    InvalidIntSuffix(char),

    // --- AST Parsing stage
    UnexpectedToken,
    UnexpectedEOF,
    ExpectsSemicolon,
    ExpectsSemicolonFoundEOF,
    ExpectIDAfterLet,
    InvalidTypeExpr,
    SliceNoClosingParen,
    LetNoTypeOrRHS,

    #[allow(dead_code)]
    VarNotExist(&'src str),
}
impl<'src> ErrorContent<'src> {
    #[must_use]
    pub fn wrap(self, loc: impl IntoSourceLoc<'src>) -> Error<'src> {
        Error {
            location: loc.into_source_location(),
            content: self,
        }
    }
    fn name(&self) -> &str {
        match self {
            Self::EofInStringOrChar(str_or_char) => match str_or_char {
                StrOrChar::Str => "eof in string literal",
                StrOrChar::Char => "eof in character literal",
            },
            Self::UnicodeEscOverflow => "unicode escape overflow",
            Self::UnicodeEscNonHexDigit => "invalid unicode escape",
            Self::UnicodeEscNoOpeningBrace => "no opening brace for unicode escape",
            Self::UnicodeEscNoClosingBrace => "no terminating brace for unicode escape",
            Self::NumericEscNonHexDigit => "invalid numeric escape",
            Self::InvalidCharEsc(_) => "invalid character escape",
            Self::InvalidIntSuffix(_) => "invalid integer suffix",
            Self::CharNoEndQuote => "missing terminating quote for character literal",
            Self::InvalidCharacter(_) => "invalid character",
            Self::UnexpectedToken => "unexpected token",
            Self::UnexpectedEOF => "unexpected EOF",
            Self::ExpectsSemicolon => "expects semicolon",
            Self::ExpectsSemicolonFoundEOF => "expects semicolon but found EOF",
            Self::ExpectIDAfterLet => "expects an identifier after `let`",
            Self::InvalidTypeExpr => "invalid type expression",
            Self::SliceNoClosingParen => "missing closing rect paren in slice type",
            Self::LetNoTypeOrRHS => "missing type annotation for let expression",
            Self::VarNotExist(_) => "variable does not exist",
        }
    }
    fn description(&self) -> String {
        match self {
            Self::EofInStringOrChar(str_or_char) => match str_or_char {
                StrOrChar::Str => "Unexpected EOF in string literal".to_string(),
                StrOrChar::Char => "Unexpected EOF in character literal".to_string(),
            },
            Self::UnicodeEscOverflow => "Unicode escape must have at most 6 hex digits".to_string(),
            Self::UnicodeEscNonHexDigit => {
                "Unicode escape must contain only hex digits".to_string()
            }
            Self::UnicodeEscNoOpeningBrace => {
                "Expects a `{{` after `\\u` for unicod escape".to_string()
            }
            Self::UnicodeEscNoClosingBrace => "No `}}` in unicode escape".to_string(),
            Self::NumericEscNonHexDigit => "Numeric escape can only have hex digits".to_string(),
            Self::InvalidCharEsc(c) => {
                format!("Unknown character escape `{}`", c.escape_default())
            }
            Self::CharNoEndQuote => "missing terminating quote for character literal".to_string(),
            Self::InvalidIntSuffix(c) => {
                format!("Unkown suffix for number literal `0{}`", c)
            }
            Self::InvalidCharacter(c) => {
                format!("Invalid character `{}`", c.escape_default())
            }
            Self::UnexpectedToken => "Unexpected token".to_string(),
            Self::UnexpectedEOF => "Unexpected EOF".to_string(),
            Self::ExpectsSemicolon => "Expects semicolon".to_string(),
            Self::ExpectsSemicolonFoundEOF => "Expects semicolon, but found EOF".to_string(),
            Self::ExpectIDAfterLet => "Expects an identifier after `let`".to_string(),
            Self::InvalidTypeExpr => "Invalid type expression".to_string(),
            Self::SliceNoClosingParen => "Missing a `]`".to_string(),
            Self::LetNoTypeOrRHS => {
                "`let` expressions needs to have a type annotation or RHS (or both)".to_string()
            }
            Self::VarNotExist(s) => {
                format!("Variable `{}` not found in the current scope", s)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Error<'src> {
    pub location: SourceLocation<'src>,
    pub content: ErrorContent<'src>,
}

impl<'src> Error<'src> {
    pub fn collect_into(self, collector: &ErrorCollector<'src>) {
        collector.collect(self)
    }
}

#[derive(Debug, Clone, Default)]
pub struct ErrorCollector<'src> {
    errors: RefCell<Vec<Error<'src>>>,
}

impl<'a> ErrorCollector<'a> {
    pub fn collect(&self, e: Error<'a>) {
        self.errors.borrow_mut().push(e);
    }
    /// Print the errors in it's final presentation format, and remove all the errors
    pub fn print_and_dump_all(&self, sources: &'a BufferedContent<'a>) {
        // TODO: If multiple errors happen in one line, print them in one block
        let mut current_filename = "";
        let mut current_file_content = "";
        for error in self.errors.borrow().iter() {
            // TODO: this is really inefficient since it has to iterate from the beginning of the
            // file for every error, but optimize it later lol
            let mut line_num = 0usize;
            let mut line_start: usize;
            let mut line_end = 0usize;
            let error_filename = error.location.file_name;
            if current_filename != error_filename {
                current_filename = error_filename;
                current_file_content = sources.read_file(current_filename).as_str();
            }
            for (i, ch) in current_file_content.char_indices() {
                line_num += 1;
                if ch == '\n' {
                    line_start = line_end;
                    line_end = i;
                    let error_range = error.location.range;
                    if line_start <= error_range.0 && line_end >= error_range.1 {
                        let len = error_range.1 - error_range.0;
                        let col_num = error_range.0 - line_start;
                        print_err(
                            error,
                            current_file_content,
                            line_start,
                            line_end,
                            line_num,
                            col_num,
                            len,
                        );
                    }
                }
            }
        }
        self.errors.borrow_mut().clear()
    }
}

/// Format an error in it's final presentation form and output it
/// `col_num` and `line_num` starts with 0
fn print_err(
    err: &Error,
    file_content: &str,
    line_start: usize,
    line_end: usize,
    line_num: usize,
    col_num: usize,
    len: usize,
) {
    // TODO: only show a slice of the line if the line is too long
    print!(
        "{} {}\n    {}\n\n",
        "-->".blue().bold(),
        format!(
            "{}:{}:{}",
            err.location.file_name.escape_default(),
            line_num + 1,
            col_num + 1,
        )
        .bold(),
        err.content.name(),
    );
    let line_text = &file_content[line_start..line_end];
    println!("{}", line_text);
    for c in line_text[0..col_num - 1].chars() {
        if c == '\t' {
            print!("   ");
        } else {
            print!(" ");
        }
    }
    if len == 0 {
        print!("{}", "^".red().bold())
    } else {
        for _ in 0..=len {
            print!("{}", "~".red().bold())
        }
    }
    println!(" {}", err.content.description().red().bold());
}

pub trait CollectIfErr<'src> {
    type Product;
    fn collect_err(self, err_collector: &ErrorCollector<'src>) -> Self::Product;
}

impl<'src, T> CollectIfErr<'src> for Result<T, Error<'src>> {
    type Product = Option<T>;

    fn collect_err(self, err_collector: &ErrorCollector<'src>) -> Self::Product {
        match self {
            Ok(shitfuck) => Some(shitfuck),
            Err(e) => {
                err_collector.collect(e);
                None
            }
        }
    }
}
