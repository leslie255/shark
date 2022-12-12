mod ast;
mod buffered_content;
mod error;
mod string;
mod token;

use std::env;

use ast::parser::AstParser;
use buffered_content::BufferedContent;
use error::ErrorCollector;

fn main() {
    let mut args = env::args();
    args.next().expect("wtf");
    let file_name = args.next().expect("Expects one argument");
    let buffers = BufferedContent::default();
    let err_collector = ErrorCollector::default();
    let ast_parser = AstParser::new(&file_name, &buffers, &err_collector);
    ast_parser.for_each(|n| println!("{:?}\n{:?}", n.src_loc(), n));
    err_collector.print_and_dump_all(&buffers);
}

#[cfg(test)]
#[test]
fn test_tokenizer() {
    use token::tokenizer::TokenStream;

    let buffers = BufferedContent::default();
    let err_collector = ErrorCollector::default();
    let token_stream = TokenStream::new("token_test.shark", &buffers, &err_collector);
    token_stream.for_each(|t| println!("{:?}\t{:?}", t.src_loc(), t));
}

#[cfg(test)]
#[test]
fn test_string() {
    use string::*;

    let string = SourceString::from("你好，世界\n🌮\nПривет, мир\n");

    let mut iter = string.char_indices();

    let (index, char) = iter.next().unwrap();
    assert_eq!(string.get(index), '你');
    assert_eq!(char, '你');

    let (index, char) = iter.next().unwrap();
    assert_eq!(string.get(index), '好');
    assert_eq!(char, '好');
}
