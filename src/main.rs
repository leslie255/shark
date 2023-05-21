#![feature(string_leak)]
#![feature(never_type)] // for placeholders in prototyping
#![feature(iter_collect_into)]

mod ast;
mod buffered_content;
mod error;
mod gen;
mod mir;
mod string;
mod term_color;
mod token;

use index_vec::IndexVec;
use std::{env, fmt::Debug, fs, rc::Rc};

use ast::parser::AstParser;
use buffered_content::BufferedContent;
use error::ErrorCollector;

fn main() {
    let mut args = env::args();
    args.next().expect("wtf");
    let file_name = String::leak(args.next().expect("Expects one argument")) as &'static str;
    let buffers = Rc::new(BufferedContent::default());
    let err_collector = Rc::new(ErrorCollector::default());

    // AST
    let mut ast_parser = AstParser::new(&file_name, Rc::clone(&buffers), Rc::clone(&err_collector));
    if err_collector.print_and_dump_all(&buffers) {
        return;
    }

    // Global context
    let mut global_context =
        gen::context::build_global_context(&mut ast_parser, Rc::clone(&err_collector));
    dbg!(&global_context);
    if err_collector.print_and_dump_all(&buffers) {
        return;
    }

    // MIR
    let mir_object = mir::builder::make_mir(&global_context);
    dbg!(&mir_object);
    if err_collector.print_and_dump_all(&buffers) {
        return;
    }

    // Cranelift Codegen
    let obj_module = gen::compile(&mut global_context, &mir_object);
    if err_collector.print_and_dump_all(&buffers) {
        return;
    }

    let bytes = obj_module.finish().emit().unwrap();
    write_bytes_to_file("output.o", &bytes).unwrap();
}

fn write_bytes_to_file(path: &str, buf: &[u8]) -> std::io::Result<()> {
    let mut file = fs::File::create(path)?;
    std::io::prelude::Write::write_all(&mut file, buf)
}

/// A format "functor" for displaying an `IndexVec` as key-value pairs
struct IndexVecFormatter<'short, I: Debug + index_vec::Idx, T: Debug>(&'short IndexVec<I, T>);
impl<'short, I: Debug + index_vec::Idx, T: Debug> Debug for IndexVecFormatter<'short, I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.0.iter_enumerated()).finish()
    }
}
