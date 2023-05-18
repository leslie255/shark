use std::{
    cell::{Ref, RefCell, RefMut},
    collections::{hash_map::Entry, HashMap},
    fmt::Debug,
    ops::{Deref, Range},
    rc::Rc,
};

use cranelift::prelude::{AbiParam, Block, EntityRef, Signature as ClifSignature};
use cranelift_codegen::{ir::FuncRef, isa::CallConv};
use cranelift_frontend::Variable;
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::{ObjectModule, ObjectProduct};
use index_vec::IndexVec;

use crate::{
    ast::{parser::AstParser, type_expr::TypeExpr, AstNode, AstNodeRef, Signature},
    error::{CollectIfErr, ErrorCollector, ErrorContent},
};

use super::trans_ty;

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
pub struct GlobalContext {
    pub funcs: IndexVec<FuncIndex, FuncInfo>,
    /// Map from function name to function index
    pub func_indices: HashMap<&'static str, FuncIndex>,
    pub err_collector: Rc<ErrorCollector>,
}

impl Debug for GlobalContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GlobalContext")
            .field("funcs", &self.funcs)
            .field("obj_module", &"*****" as &dyn Debug)
            .finish()
    }
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

///// Translate a function signature information to cranelift signature.
///// Returns the clif signature, the flattened argument variables, and the flattened return type.
//fn trans_sig(global: &GlobalContext, sig: &Signature) -> (ClifSignature, Vec<VarInfo>, FlatType) {
//    let call_conv = CallConv::SystemV;
//    let mut clif_sig = ClifSignature::new(call_conv);
//    let mut args = Vec::<VarInfo>::with_capacity(sig.args.len());
//    clif_sig.params.reserve(sig.args.len());
//    let mut id_counter = 0usize;
//    for (_, ty) in sig.args.iter() {
//        let var_info = make_var_info(global, &mut id_counter, ty.clone());
//        var_info
//            .flat_ty()
//            .fields()
//            .map(AbiParam::new)
//            .for_each(|t| clif_sig.params.push(t));
//        args.push(var_info);
//    }
//    for ty in trans_ty(global, &sig.ret_type).fields() {
//        clif_sig.returns.push(AbiParam::new(ty));
//    }
//    let ret_ty = super::trans_ty(global, &sig.ret_type);
//    (clif_sig, args, ret_ty)
//}
