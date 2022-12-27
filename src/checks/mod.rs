#![allow(dead_code)]
use std::collections::HashMap;

use crate::ast::{type_expr::TypeExpr, FnSignature};

pub mod syntaxchecker;
pub mod symboltable;

/// One item in the symbol table stack
/// The symbol table is stored as a stack, every time the parser enters a block, a new `Symbol` is
/// pushed onto the stack containing the symbols in that block
#[derive(Debug, Clone)]
pub struct Symbols<'src> {
    pub vars: HashMap<&'src str, TypeExpr<'src>>,
    pub functions: HashMap<&'src str, FnSignature<'src>>,
    pub typenames: HashMap<&'src str, TypeExpr<'src>>,
}
