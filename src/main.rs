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
    output_path: String,
}

#[allow(unused)]
fn get_args() -> ArgOptions {
    let mut args = env::args();
    args.next().expect("wtf");

    let mut input_path = Option::<String>::None;
    let mut output_path = Option::<String>::None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-o" => {
                if output_path.is_some() {
                    panic!("Multiple output path is not ok! If you meant for it to be an input path, remove `-o`");
                }
                output_path = Some(
                    args.next()
                        .expect("Expects another argument after `-o` for output path"),
                );
            }
            _ => {
                if input_path.is_some() {
                    panic!("Multiple input path is not supported yet, did you mean to use `-o` for output path?");
                }
                input_path = Some(arg)
            }
        }
    }

    let input_path = input_path.expect("No input path provided");
    let output_path = output_path.unwrap_or({
        let size_hint = input_path
            .len()
            .checked_sub(4) // removing ".shark" and adding ".c"
            .expect("No output path provided nor could it be derived from the input path");
        let mut s = String::with_capacity(size_hint);
        let stripped_path = input_path
            .strip_suffix(".shark")
            .expect("No output path provided nor could it be derived from the input path");
        s.push_str(stripped_path);
        s.push_str(".c");
        s
    });

    ArgOptions {
        input_path,
        output_path,
    }
}

fn main() {
    let options = get_args();
    let buffers = BufferedContent::default();
    let err_collector = ErrorCollector::default();
    let ast_parser = AstParser::new(&options.input_path, &buffers, &err_collector);
    err_collector.print_and_dump_all(&buffers);
    let mut output_file = File::options()
        .create(true)
        .write(true)
        .truncate(true)
        .open(options.output_path.as_str())
        .expect("Unable to open the specified output file, the path either does not exist or you do not have write permission");
    cfront::gen_c_code(&mut output_file, ast_parser).unwrap();
}
