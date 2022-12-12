mod ast;
mod buffered_content;
mod error;
mod string;
mod token;

use ast::parser::AstParser;
use buffered_content::BufferedContent;
use error::ErrorCollector;

fn main() {
    let buffers = BufferedContent::default();
    let file_name = "test.shark";
    let err_collector = ErrorCollector::default();
    let ast_parser = AstParser::new(file_name, &buffers, &err_collector);
    ast_parser.for_each(|n| println!("{:?}\n{:?}", n.src_loc(), n));
    err_collector.print_and_dump_all(&buffers);
}

#[cfg(test)]
#[test]
fn test_string() {
    use string::*;

    
    let string = SourceString::from("你好，世界\n🌮\nПривет, мир\n");

    let mut iter = string.char_indices();
    
    let (index, char) = iter.next().unwrap();
    assert_eq!(string.get(index), Some('你'));
    assert_eq!(char, '你');
    
    let (index, char) = iter.next().unwrap();
    assert_eq!(string.get(index), Some('好'));
    assert_eq!(char, '好');
}
