mod ast;
mod buffered_content;
mod checks;
mod error;
mod mir;
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
    let mut ast_parser = AstParser::new(&file_name, &buffers, &err_collector);
    while let Some(_) = ast_parser.next() {
    }
    let ast = ast_parser.ast;
    let mir_program = mir::translator::ast_into_mir(ast);
    mir_program.root_nodes.iter().for_each(|n|println!("{n:#?}"));
    err_collector.print_and_dump_all(&buffers);
}
