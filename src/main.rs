mod ast;
mod buffered_content;
mod error;
mod token;

use ast::parser::AstParser;
use buffered_content::BufferedContent;
use error::ErrorCollector;

fn main() {
    let buffers = BufferedContent::default();
    let file_name = "test.shark";
    let err_collector = ErrorCollector::default();
    let ast_parser = AstParser::new(file_name, &buffers, &err_collector);
    ast_parser.for_each(|n| println!("{:?}\n{:?}", n.src_loc(), n));
    err_collector.print_and_dump_all(&buffers);
}
#[cfg(test)]
#[test]
fn test_tokens() {
    use token::tokenizer::TokenStream;

    let buffers = BufferedContent::default();
    let file_name = "test.shark";
    let err_collector = ErrorCollector::default();
    let token_stream = TokenStream::new(file_name, &buffers, &err_collector);
    token_stream.for_each(|t| println!("{:?}\n{:?}", t.src_loc(), t));
}
