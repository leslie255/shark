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

use std::{env, rc::Rc};

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
    let mut global_context = gen::build_global_context(
        &mut ast_parser,
        gen::make_empty_obj_module("output"),
        Rc::clone(&err_collector),
    );
    dbg!(&global_context);

    gen::compile(&mut global_context, &ast_parser.ast);

    err_collector.print_and_dump_all(&buffers);
}
