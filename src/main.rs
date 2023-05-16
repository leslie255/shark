#![feature(string_leak)]
#![feature(never_type)]
#![feature(iter_collect_into)]
#![allow(dead_code)]

extern crate index_vec;

mod ast;
mod buffered_content;
mod error;
mod gen;
mod mir;
mod string;
mod term_color;
mod token;

use std::{env, fs, rc::Rc};

use ast::parser::AstParser;
use buffered_content::BufferedContent;
use error::ErrorCollector;

fn main() {
    let mut args = env::args();
    args.next().expect("wtf");
    let file_name = String::leak(args.next().expect("Expects one argument")) as &'static str;
    let buffers = Rc::new(BufferedContent::default());
    let err_collector = Rc::new(ErrorCollector::default());
    let mut ast_parser = AstParser::new(&file_name, Rc::clone(&buffers), Rc::clone(&err_collector));
    let global_context = gen::build_global_context(&mut ast_parser, Rc::clone(&err_collector));
    dbg!(&global_context);
    let ast = ast_parser.ast;
    dbg!(&ast.root_nodes);
    let mir_object = mir::builder::make_mir(&global_context, &ast);
    dbg!(&mir_object);

    //gen::compile(&mut global_context, &mir_object);

    //let bytes = global_context.finish().emit().unwrap();
    //write_bytes_to_file("output.o", &bytes).unwrap();

    err_collector.print_and_dump_all(&buffers);
}

fn write_bytes_to_file(path: &str, buf: &[u8]) -> std::io::Result<()> {
    let mut file = fs::File::create(path)?;
    std::io::prelude::Write::write_all(&mut file, buf)
}
