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
use cranelift_codegen::settings;
use cranelift_object::{ObjectBuilder, ObjectModule};
use error::ErrorCollector;

fn main() {
    let mut args = env::args();
    args.next().expect("wtf");
    let file_name: &'static str = String::leak(args.next().expect("Expects one argument"));
    let buffers = Rc::new(BufferedContent::default());
    let err_collector = Rc::new(ErrorCollector::default());
    let mut ast_parser = AstParser::new(&file_name, Rc::clone(&buffers), Rc::clone(&err_collector));
    let obj_module = {
        let isa = cranelift_native::builder()
            .expect("Error getting the native ISA")
            .finish(settings::Flags::new(settings::builder()))
            .unwrap();
        let obj_builder =
            ObjectBuilder::new(isa, "output", cranelift_module::default_libcall_names()).unwrap();
        ObjectModule::new(obj_builder)
    };
    let global_context = gen::build_global_context(&mut ast_parser, obj_module, Rc::clone(&err_collector));
    dbg!(global_context);

    err_collector.print_and_dump_all(&buffers);
}
