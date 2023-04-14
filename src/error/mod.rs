pub mod location;

use std::cell::RefCell;

use location::{IntoSourceLoc, SourceLocation};

use crate::{buffered_content::BufferedContent, token::Token};

use crate::term_color;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StrOrChar {
    Str,
    Char,
}

#[derive(Debug, Clone)]
pub enum ErrorContent {
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
    InvalidTypeExpr,
    SliceNoClosingParen,
    LetNoTypeOrRHS,
    ExpectToken(Token),
    ExpectMultipleTokens(Vec<Token>),
    NonUIntForArrLen,
    TypeExprStackOverflow,

    // -- Syntax checker error
    ExprNotAllowedAtTopLevel,
    ExprNotAllowedAsFnBody,
    ExprNotAllowedAsChild,
    FuncRedef,

    // -- Type checker error
    #[allow(dead_code)]
    InvalidMemberAccess,
    FuncWithoutBody,
    UndefinedVar(&'static str),
}
impl ErrorContent {
    #[must_use]
    pub fn wrap(self, loc: impl IntoSourceLoc) -> Error {
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
            Self::InvalidTypeExpr => "invalid type expression",
            Self::SliceNoClosingParen => "missing closing rect paren in slice type",
            Self::LetNoTypeOrRHS => "missing type annotation for let expression",
            Self::ExpectToken(_) => "expect token",
            Self::ExpectMultipleTokens(_) => "expect tokens",
            Self::NonUIntForArrLen => "expect unsigned integer for array",
            Self::TypeExprStackOverflow => "type expression exceeds recursive limit (256)",
            Self::ExprNotAllowedAtTopLevel => "expression not allowed at top level",
            Self::ExprNotAllowedAsFnBody => "expression not allowed as function body",
            Self::ExprNotAllowedAsChild => "expression is not allowed as child",
            Self::InvalidMemberAccess => "invalid member access",
            Self::FuncRedef => "redefinition of function",
            Self::FuncWithoutBody => "function without",
            Self::UndefinedVar(..) => "undefined variable",
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
            Self::InvalidTypeExpr => "Invalid type expression".to_string(),
            Self::SliceNoClosingParen => "Missing a `]`".to_string(),
            Self::LetNoTypeOrRHS => {
                "`let` expressions needs to have a type annotation or RHS (or both)".to_string()
            }
            Self::ExpectToken(t) => format!("Expect {:?}", t),
            // TODO: pretty format this
            Self::ExpectMultipleTokens(tokens) => format!("Expect tokens: {:?}", tokens),
            Self::NonUIntForArrLen => "Array length should be an unsigned integer".to_string(),
            Self::TypeExprStackOverflow => "Type expression exceeds stack limit".to_string(),
            Self::ExprNotAllowedAtTopLevel => "Consider wrapping this into a function".to_string(),
            Self::ExprNotAllowedAsFnBody => {
                "This expression is allowed as a statement in function body".to_string()
            }
            Self::ExprNotAllowedAsChild => "This expression is not allowed here".to_string(),
            Self::InvalidMemberAccess => "No such path exists".to_string(),
            Self::FuncRedef => "This function was previously declared".to_string(),
            Self::FuncWithoutBody => "Function without body is not allowed".to_string(),
            Self::UndefinedVar(name) => format!("Undefined variable `{}`", name).to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Error {
    pub location: SourceLocation,
    pub content: ErrorContent,
}

impl Error {
    pub fn collect_into(self, collector: &ErrorCollector) {
        collector.collect(self)
    }
}

/// A container that collects all compile errors
/// Uses internal mutability because it is write-only
#[derive(Debug, Clone, Default)]
pub struct ErrorCollector {
    errors: RefCell<Vec<Error>>,
}

impl ErrorCollector {
    pub fn collect(&self, e: Error) {
        self.errors.borrow_mut().push(e);
    }
    /// Print the errors in it's final presentation format, and remove all the errors
    pub fn print_and_dump_all(&self, sources: &BufferedContent) {
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
    use term_color::AnsiEscCode::*;
    // TODO: only show a slice of the line if the line is too long
    print!(
        "{FgBlue}-->{ResetColor} {}\n    {}\n\n",
        format!(
            "{}:{}:{}",
            err.location.file_name.escape_default(),
            line_num + 1,
            col_num + 1,
        ),
        err.content.name(),
    );
    let line_text = &file_content[line_start..line_end];
    println!("{}", line_text);
    for c in line_text[0..col_num.saturating_sub(1)].chars() {
        if c == '\t' {
            print!("    ");
        } else {
            print!(" ");
        }
    }
    if len == 0 {
        print!("{FgRed}^{ResetColor}")
    } else {
        for _ in 0..=len {
            print!("{FgRed}~{ResetColor}")
        }
    }
    println!(" {FgRed}{}{ResetColor}", err.content.description());
}

pub trait CollectIfErr {
    type Product;
    fn collect_err(self, err_collector: &ErrorCollector) -> Self::Product;
}

impl<T> CollectIfErr for Result<T, Error> {
    type Product = Option<T>;

    fn collect_err(self, err_collector: &ErrorCollector) -> Self::Product {
        match self {
            Ok(shitfuck) => Some(shitfuck),
            Err(e) => {
                err_collector.collect(e);
                None
            }
        }
    }
}
