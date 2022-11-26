#![allow(dead_code)]
pub mod location;

use location::{IntoSourceLoc, SourceLocation};

use crate::buffered_content::BufferedContent;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringOrChar {
    String,
    Char,
}

#[derive(Debug, Clone)]
pub enum ErrorContent<'a> {
    // --- Tokenizer stage
    // String or character literal
    EofInStringOrChar(StringOrChar),
    UnicodeEscOverflow,
    UnicodeEscNonHexDigit,
    UnicodeEscNoClosingBrace,
    NumericEscNonHexDigit,
    InvalidCharEsc(char),

    // Number literal
    /// "Expects 0~9, x, o, d, b after `0`"
    InvalidIntSuffix(char),

    InvalidCharacter(char),

    VarNotExist(&'a str),
}
impl<'a> ErrorContent<'a> {
    pub fn package(self, loc: impl IntoSourceLoc<'a>) -> Error<'a> {
        Error {
            location: loc.into_source_location(),
            content: self,
        }
    }
    fn name(&self) -> &str {
        match self {
            ErrorContent::EofInStringOrChar(str_or_char) => match str_or_char {
                StringOrChar::String => "eof in string literal",
                StringOrChar::Char => "eof in character literal",
            },
            ErrorContent::UnicodeEscOverflow => "unicode escape overflow",
            ErrorContent::UnicodeEscNonHexDigit => "invalid unicode escape",
            ErrorContent::UnicodeEscNoClosingBrace => "unicode escape no terminater",
            ErrorContent::NumericEscNonHexDigit => "invalid numeric escape",
            ErrorContent::InvalidCharEsc(_) => "invalid character escape",
            ErrorContent::InvalidIntSuffix(_) => "invalid integer suffix",
            ErrorContent::InvalidCharacter(_) => "invalid character",
            ErrorContent::VarNotExist(_) => "variable does not exist",
        }
    }
    fn print_description(&self) {
        match self {
            ErrorContent::EofInStringOrChar(str_or_char) => match str_or_char {
                StringOrChar::String => print!("Unexpected EOF in string literal"),
                StringOrChar::Char => print!("Unexpected EOF in character literal"),
            },
            ErrorContent::UnicodeEscOverflow => {
                print!("Unicode escape must have at most 6 hex digits")
            }
            ErrorContent::UnicodeEscNonHexDigit => {
                print!("Unicode escape must contain only hex digits")
            }
            ErrorContent::UnicodeEscNoClosingBrace => print!("No `}}` in unicode escape"),
            ErrorContent::NumericEscNonHexDigit => {
                print!("Numeric escape can only have hex digits")
            }
            ErrorContent::InvalidCharEsc(c) => {
                print!("Unknown character escape `{}`", c.escape_default())
            }
            ErrorContent::InvalidIntSuffix(c) => {
                print!("Unkown suffix for number literal `0{}`", c)
            }
            ErrorContent::InvalidCharacter(c) => {
                print!("Invalid character `{}`", c.escape_default())
            }
            ErrorContent::VarNotExist(s) => {
                print!("Variable `{}` not found in the current scope", s)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Error<'a> {
    pub location: SourceLocation<'a>,
    pub content: ErrorContent<'a>,
}

impl<'a> Error<'a> {
    pub fn collect_into(self, collector: &mut ErrorCollector<'a>) {
        collector.collect(self)
    }
}

#[derive(Debug, Clone, Default)]
pub struct ErrorCollector<'a>(Vec<Error<'a>>);

impl<'a> ErrorCollector<'a> {
    pub fn collect(&mut self, e: Error<'a>) {
        self.0.push(e);
    }
    #[allow(unused)]
    /// Print the errors in it's final presentation format, and remove all the errors
    pub fn print_and_dump_all(&mut self, sources: &'a BufferedContent<'a>) {
        // TODO: If multiple errors happen in one line, print them in one block
        let first_error = if let Some(e) = self.0.first() {
            e
        } else {
            return;
        };
        let mut current_filename = first_error.location.file_name;
        let mut current_file_content = sources.open_file(current_filename);
        for error in &self.0 {
            // TODO: this is really inefficient since it has to iterate from the beginning of the
            // file for every error, but optimize it later lol
            let mut line_num = 0usize;
            let mut line_start = 0usize;
            let mut line_end = 0usize;
            let error_filename = error.location.file_name;
            if current_filename != error_filename {
                current_filename = error_filename;
                current_file_content = sources.open_file(current_filename);
            }
            for (i, ch) in current_file_content.char_indices() {
                line_num += 1;
                if ch == '\n' {
                    line_start = line_end;
                    line_end = i;
                    let error_range = error.location.range;
                    if line_start <= error_range.0 {
                        let len = error_range.1 - error_range.0;
                        let col_num = error_range.0.max(line_start);
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
        self.0.clear()
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
        "--> {}:{}:{}\n    {}\n\n",
        err.location.file_name.escape_default(),
        line_num + 1,
        col_num + 1,
        err.content.name()
    );
    let line_text = &file_content[line_start..line_end];
    println!("{}", line_text);
    for c in line_text[0..col_num].chars() {
        if c == '\t' {
            print!("   ");
        } else {
            print!(" ");
        }
    }
    if len == 0 {
        print!("^")
    } else {
        for _ in 0..=len {
            print!("~")
        }
    }
    println!();
    err.content.print_description();
    print!("\n\n");
}
