#![feature(hash_raw_entry)]

mod ast;
mod buffered_content;
mod cfront;
mod checks;
mod error;
mod string;
mod term_color;
mod token;

use std::{env, fs::File};

use ast::parser::AstParser;
use buffered_content::BufferedContent;
use error::ErrorCollector;

struct ArgOptions {
    input_path: String,
    output_c: String,
    output_h: String,
}

fn get_args() -> ArgOptions {
    let mut args = env::args();
    args.next().expect("wtf");

    let input_path = args.next().expect("No input path provided");

    if args.next().is_some() {
        panic!("Cannot have multiple input paths");
    }

    let output_c = {
        let size_hint = input_path
            .len()
            .checked_sub(4) // removing ".shark" and adding ".c" => sub 4 bytes
            .expect("No output path provided nor could it be derived from the input path");
        let mut s = String::with_capacity(size_hint);
        let stripped_path = input_path
            .strip_suffix(".shark")
            .expect("No output path provided nor could it be derived from the input path");
        s.push_str(stripped_path);
        s.push_str(".c");
        s
    };
    let output_h = {
        let size_hint = input_path
            .len()
            .checked_sub(4) // removing ".shark" and adding ".c" => sub 4 bytes
            .expect("No output path provided nor could it be derived from the input path");
        let mut s = String::with_capacity(size_hint);
        let stripped_path = input_path
            .strip_suffix(".shark")
            .expect("No output path provided nor could it be derived from the input path");
        s.push_str(stripped_path);
        s.push_str(".h");
        s
    };

    ArgOptions {
        input_path,
        output_c,
        output_h,
    }
}

fn main() {
    let options = get_args();
    let buffers = BufferedContent::default();
    let err_collector = ErrorCollector::default();
    let ast_parser = AstParser::new(&options.input_path, &buffers, &err_collector);
    err_collector.print_and_dump_all(&buffers);
    let output_file_c = File::options()
        .create(true)
        .write(true)
        .truncate(true)
        .open(options.output_c.as_str())
        .expect("Unable to open the specified output file, the path either does not exist or you do not have write permission");
    let output_file_h = File::options()
        .create(true)
        .write(true)
        .truncate(true)
        .open(options.output_h.as_str())
        .expect("Unable to open the specified output file, the path either does not exist or you do not have write permission");
    cfront::gen_c_code(output_file_c, output_file_h, ast_parser);
}
