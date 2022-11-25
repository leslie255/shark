mod error;
mod token;
mod buffered_content;

use error::{ErrorCollector, ErrorContent};
use token::tokenizer::TokenStream;
use buffered_content::BufferedContent;

fn main() {
    let buffers = BufferedContent::default();
    let token_stream = TokenStream::new("test.shark", &buffers);
    token_stream.for_each(|t| println!("{:?}\t{:?}", t.source_location(), t));
    let mut err_collector = ErrorCollector::default();
    ErrorContent::VarNotExist("lol")
        .package(("test.shark", 0, 1))
        .collect_into(&mut err_collector);
    err_collector.print_and_dump_all(&buffers);
}
