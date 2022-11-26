mod ast;
mod buffered_content;
mod error;
mod token;

use buffered_content::BufferedContent;
use error::ErrorCollector;
use token::tokenizer::TokenStream;

fn main() {
    let buffers = BufferedContent::default();
    let file_name = "test.shark";
    let err_collector = ErrorCollector::default();
    let token_stream = TokenStream::new(file_name, &buffers, &err_collector);
    token_stream.for_each(|t| println!("{:?}\t{:?}", t.source_location(), t));
    err_collector.print_and_dump_all(&buffers);
}
