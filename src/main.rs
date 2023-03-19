mod ast;
mod buffered_content;
mod checks;
mod error;
mod string;
mod token;
mod term_color;
mod cfront;

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
    err_collector.print_and_dump_all(&buffers);
    cfront::gen_c_code(&mut std::io::stdout().lock(), ast_parser).unwrap();
}
