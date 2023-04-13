#![feature(string_leak)]
#![allow(dead_code)]

mod ast;
mod buffered_content;
mod error;
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
    err_collector.print_and_dump_all(&buffers);
    ast_parser.iter().for_each(|n| println!("{n:?}"));
}
