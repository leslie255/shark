#![feature(string_leak)]
#![feature(iter_collect_into)]
#![allow(dead_code)]

mod ast;
mod buffered_content;
mod error;
mod gen;
mod string;
mod term_color;
mod token;

use std::{env, rc::Rc, fs};

use ast::parser::AstParser;
use buffered_content::BufferedContent;
use error::ErrorCollector;

fn main() {
    let mut args = env::args();
    args.next().expect("wtf");
    let file_name: &'static str = String::leak(args.next().expect("Expects one argument"));
    let buffers = Rc::new(BufferedContent::default());
    let err_collector = Rc::new(ErrorCollector::default());
    let mut ast_parser = AstParser::new(&file_name, Rc::clone(&buffers), Rc::clone(&err_collector));
    let global_context = gen::build_global_context(
        &mut ast_parser,
        gen::make_empty_obj_module("output"),
        Rc::clone(&err_collector),
    );
    dbg!(&global_context);
    println!("-------------- Raw AST:");
    dbg!(&ast_parser.ast.root_nodes);
    let cooked_ast = gen::cook_ast(&global_context, ast_parser.ast);
    println!("-------------- Cooked AST:");
    dbg!(&cooked_ast.0.root_nodes);

    //gen::compile(&mut global_context, &ast_parser.ast);

    //let bytes = global_context.finish().emit().unwrap();
    //write_bytes_to_file("output.o", &bytes).unwrap();

    err_collector.print_and_dump_all(&buffers);
}

fn write_bytes_to_file(path: &str, buf: &[u8]) -> std::io::Result<()> {
    let mut file = fs::File::create(path)?;
    std::io::prelude::Write::write_all(&mut file, buf)
}
