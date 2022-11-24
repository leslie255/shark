mod errors;
mod token;

use crate::token::{tokenizer::BufferedSources, tokenizer::TokenStream};

fn main() {
    let mut buffed_sources = BufferedSources::default();
    let token_stream = TokenStream::new("test.shark", &mut buffed_sources);
    token_stream.for_each(|t| println!("{t:?}\t{:?}", t.source_location()));
}
