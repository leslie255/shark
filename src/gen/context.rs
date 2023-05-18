use std::{collections::HashMap, fmt::Debug, ops::Deref, rc::Rc};

use cranelift::prelude::Block;
use cranelift_module::Linkage;
use index_vec::IndexVec;

use crate::{
    ast::{parser::AstParser, AstNode, AstNodeRef, Signature},
    error::{CollectIfErr, ErrorCollector, ErrorContent},
};

/// Information about a function
#[derive(Clone, Debug)]
pub struct FuncInfo {
    pub name: &'static str,
    pub sig: Signature,
    pub ast_node: AstNodeRef,
}

#[derive(Clone, Debug)]
pub(super) struct LoopInfo {
    pub break_block: Block,
    pub continue_block: Block,
}

impl LoopInfo {
    pub fn new(break_block: Block, continue_block: Block) -> Self {
        Self {
            break_block,
            continue_block,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncIndex(pub usize);
impl Debug for FuncIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn{}", self.0)
    }
}
impl index_vec::Idx for FuncIndex {
    fn from_usize(idx: usize) -> Self {
        Self(idx)
    }
    fn index(self) -> usize {
        self.0
    }
}

/// Keeps track of global symbols
#[derive(Debug)]
pub struct GlobalContext {
    pub funcs: IndexVec<FuncIndex, FuncInfo>,
    /// Map from function name to function index
    pub func_indices: HashMap<&'static str, FuncIndex>,
    pub err_collector: Rc<ErrorCollector>,
}


impl GlobalContext {
    /// An empty global context
    pub(self) fn prototype(err_collector: Rc<ErrorCollector>) -> Self {
        Self {
            funcs: IndexVec::new(),
            func_indices: HashMap::new(),
            err_collector,
        }
    }

    /// Get the `FuncIndex` and `FuncInfo` of a function by its name
    pub fn func(&self, name: &str) -> Option<(FuncIndex, &FuncInfo)> {
        let &idx = self.func_indices.get(name)?;
        Some((idx, self.funcs.get(idx)?))
    }

    /// Declares a new function, if the function already existed, returns `Err`
    pub fn declare_func(
        &mut self,
        name: &'static str,
        sig: Signature,
        _linkage: Linkage,
        ast_node: AstNodeRef,
    ) -> Result<(), ()> {
        let func_info = FuncInfo {
            name,
            sig,
            ast_node,
        };
        let idx = self.funcs.push(func_info);
        match self.func_indices.insert(name, idx) {
            Some(..) => Err(()),
            None => Ok(()),
        }
    }
}

pub fn build_global_context(
    ast_parser: &mut AstParser,
    err_collector: Rc<ErrorCollector>,
) -> GlobalContext {
    let mut global = GlobalContext::prototype(err_collector);
    for node_ref in ast_parser.iter() {
        let node = node_ref.deref();
        match node.inner() {
            AstNode::FnDef(function) => {
                let linkage = match function.body {
                    Some(..) => Linkage::Export,
                    None => Linkage::Import,
                };
                global
                    .declare_func(function.name, function.sign.clone(), linkage, node_ref)
                    .map_err(|_| ErrorContent::FuncRedef.wrap(node.src_loc()))
                    .collect_err(&global.err_collector);
            }
            _ => ErrorContent::ExprNotAllowedAtTopLevel
                .wrap(node.src_loc())
                .collect_into(&global.err_collector),
        }
    }
    global
}
