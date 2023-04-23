use std::{
    cell::{Ref, RefCell, RefMut},
    collections::{hash_map::Entry, HashMap},
    fmt::Debug,
    ops::Range,
    rc::Rc,
};

use cranelift::prelude::{AbiParam, Block, EntityRef, Signature as ClifSignature};
use cranelift_codegen::{ir::FuncRef, isa::CallConv};
use cranelift_frontend::Variable;
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::{ObjectModule, ObjectProduct};

use crate::{
    ast::{parser::AstParser, type_expr::TypeExpr, AstNode, Signature},
    error::{CollectIfErr, ErrorCollector, ErrorContent},
};

use super::{trans_ty, FlatType};

/// Information about a variable
#[derive(Clone, Debug)]
pub(super) struct VarInfo {
    ty: TypeExpr,
    flat_ty: FlatType,
    clif_vars: Range<usize>,
}

impl VarInfo {
    pub fn new(ty: TypeExpr, flat_ty: FlatType, clif_vars: Range<usize>) -> Self {
        Self {
            ty,
            flat_ty,
            clif_vars,
        }
    }

    pub fn offset(&self, offset: usize) -> Variable {
        let id = self.clif_vars.start + offset;
        assert!(id < self.clif_vars.end);
        Variable::new(id)
    }

    pub fn ty(&self) -> &TypeExpr {
        &self.ty
    }

    pub fn flat_ty(&self) -> &FlatType {
        &self.flat_ty
    }

    pub(super) fn clif_vars(&self) -> Range<usize> {
        self.clif_vars.clone()
    }
}

/// Information about a function
#[derive(Clone, Debug)]
pub(super) struct FuncInfo {
    pub name: &'static str,
    pub args: Vec<VarInfo>,
    pub ret_ty: FlatType,
    pub index: u32,
    pub clif_sig: ClifSignature,
    pub sig: Signature,
}

/// Information about the parent loop block, stored inside `LocalContext` as a stack
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

/// Keep track of symbols inside a function
/// Generates a new one for every function
#[derive(Debug)]
pub(super) struct LocalContext {
    imported_funcs: HashMap<&'static str, FuncRef>,
    vars: Vec<HashMap<&'static str, VarInfo>>,
    pub id_counter: usize,
    loops: Vec<LoopInfo>,
    ret_block: Block,
    func_ret_ty: TypeExpr,
    func_ret_ty_flat: FlatType,
}

impl LocalContext {
    pub fn new(
        global: &GlobalContext,
        ret_block: Block,
        args: impl Iterator<Item = (&'static str, VarInfo)>,
        func_ret_ty: TypeExpr,
    ) -> Self {
        let func_ret_ty_flat = trans_ty(global, &func_ret_ty);
        Self {
            imported_funcs: HashMap::new(),
            vars: vec![args.collect()],
            id_counter: 0,
            loops: Vec::new(),
            ret_block,
            func_ret_ty,
            func_ret_ty_flat,
        }
    }

    fn var_stack_top_mut(&mut self) -> &mut HashMap<&'static str, VarInfo> {
        self.vars.last_mut().expect("Local symbol stack is empty")
    }

    fn _var_stack_top(&self) -> &HashMap<&'static str, VarInfo> {
        self.vars.last().expect("Local symbol stack is empty")
    }

    /// Returns a variable if it exists
    pub fn var<'a>(&'a self, name: &str) -> Option<&'a VarInfo> {
        self.vars.iter().rev().find_map(|vars| vars.get(name))
    }

    pub fn enters_block(&mut self) {
        self.vars.push(HashMap::new());
    }

    pub fn leaves_block(&mut self) {
        self.vars.pop();
    }

    /// Called when entering a loop.
    /// Returns the `LoopInfo` object created
    pub fn enters_loop<'a>(&'a mut self, break_block: Block, continue_block: Block) {
        self.loops.push(LoopInfo::new(break_block, continue_block));
        self.enters_block();
    }

    pub fn leaves_loop(&mut self) {
        self.loops.pop();
        self.leaves_block();
    }

    /// Get the parent loop
    pub fn parent_loop(&self) -> Option<&LoopInfo> {
        self.loops.last()
    }

    /// Get a mutable reference to the  parent loop
    pub fn parent_loop_mut(&mut self) -> Option<&mut LoopInfo> {
        self.loops.last_mut()
    }

    /// Creates a new variable and add that to the symbols
    pub fn create_var<'a>(
        &'a mut self,
        global: &GlobalContext,
        name: &'static str,
        ty: TypeExpr,
    ) -> (Range<usize>, &'a FlatType) {
        let var_info = make_var_info(global, &mut self.id_counter, ty);
        self.var_stack_top_mut().insert(name, var_info);
        let var_info = unsafe {
            self.vars
                .get_unchecked(self.vars.len() - 1)
                .get(name)
                .unwrap_unchecked()
        };
        (var_info.clif_vars(), var_info.flat_ty())
    }

    /// Returns the variable of `name`, or exits with an error message if a variable of the
    /// provided name is not found
    pub fn expect_var<'a>(&'a self, name: &str) -> &'a VarInfo {
        self.var(name).unwrap_or_else(|| {
            println!("Variable does not exist: `{}`", name);
            std::process::exit(255);
        })
    }

    /// If a function is already imported, return the index and ref to that function, if not,
    /// execute the closure, add the returned index and ref to the map and return it
    pub fn import_func_if_needed(
        &mut self,
        name: &'static str,
        mut f: impl FnMut() -> FuncRef,
    ) -> FuncRef {
        match self.imported_funcs.entry(name) {
            Entry::Occupied(o) => *o.get(),
            Entry::Vacant(v) => *v.insert(f()),
        }
    }

    /// Get the return block of the function
    pub fn ret_block(&self) -> Block {
        self.ret_block
    }

    pub(super) fn func_ret_ty(&self) -> &TypeExpr {
        &self.func_ret_ty
    }

    pub(super) fn func_ret_ty_flat(&self) -> &FlatType {
        &self.func_ret_ty_flat
    }
}

fn make_var_info(global: &GlobalContext, id_counter: &mut usize, ty: TypeExpr) -> VarInfo {
    let flat_ty = super::trans_ty(global, &ty);
    let var_ids = {
        let start = *id_counter;
        *id_counter += flat_ty.len();
        let end = *id_counter;
        start..end
    };
    VarInfo::new(ty, flat_ty, var_ids)
}

/// Keeps track of global symbols
pub struct GlobalContext {
    /// Map from function name to Id and signature of the function
    funcs: HashMap<&'static str, FuncInfo>,
    pub obj_module: RefCell<ObjectModule>,
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
    pub(self) fn prototype(obj_module: ObjectModule, err_collector: Rc<ErrorCollector>) -> Self {
        Self {
            funcs: HashMap::new(),
            obj_module: RefCell::new(obj_module),
            err_collector,
        }
    }

    pub fn finish(self) -> ObjectProduct {
        self.obj_module.into_inner().finish()
    }

    pub fn compile(self) -> Vec<u8> {
        self.obj_module.into_inner().finish().emit().unwrap()
    }

    /// Get the `FuncInfo` of a function by its name
    pub(super) fn func(&self, name: &str) -> Option<&FuncInfo> {
        self.funcs.get(name)
    }

    /// Add a new function to the symbols and also declare it inside the `ObjectModule`
    /// returns `Err(())` if the function previously exists
    #[must_use]
    pub(self) fn declare_func(
        &mut self,
        name: &'static str,
        sig: Signature,
        index: u32,
        linkage: Linkage,
    ) -> Result<FuncId, ()> {
        let (clif_sig, args, ret_ty) = trans_sig(self, &sig);
        let func_id = self
            .obj_module_mut()
            .declare_function(name, linkage, &clif_sig)
            .map_err(|_| ())?;
        let func_info = FuncInfo {
            name,
            args,
            ret_ty,
            index,
            clif_sig,
            sig,
        };
        match self.funcs.insert(name, func_info) {
            Some(..) => Err(()),
            None => Ok(func_id),
        }
    }

    pub fn obj_module(&self) -> Ref<ObjectModule> {
        self.obj_module.borrow()
    }

    pub fn obj_module_mut(&self) -> RefMut<ObjectModule> {
        self.obj_module.borrow_mut()
    }
}

pub fn build_global_context(
    ast_parser: &mut AstParser,
    obj_module: ObjectModule,
    err_collector: Rc<ErrorCollector>,
) -> GlobalContext {
    let mut global = GlobalContext::prototype(obj_module, err_collector);
    let mut next_func_index = 0u32;
    for item in ast_parser.iter() {
        let item = item.as_ref();
        match item.inner() {
            AstNode::FnDef(function) => {
                let func_index = next_func_index;
                next_func_index += 1;
                let linkage = match function.body {
                    Some(..) => Linkage::Export,
                    None => Linkage::Import,
                };
                global
                    .declare_func(function.name, function.sign.clone(), func_index, linkage)
                    .map_err(|_| ErrorContent::FuncRedef.wrap(item.src_loc()))
                    .collect_err(&global.err_collector);
            }
            _ => ErrorContent::ExprNotAllowedAtTopLevel
                .wrap(item.src_loc())
                .collect_into(&global.err_collector),
        }
    }
    global
}

/// Translate a function signature information to cranelift signature.
/// Returns the clif signature, the flattened argument variables, and the flattened return type.
fn trans_sig(global: &GlobalContext, sig: &Signature) -> (ClifSignature, Vec<VarInfo>, FlatType) {
    let call_conv = CallConv::SystemV;
    let mut clif_sig = ClifSignature::new(call_conv);
    let mut args = Vec::<VarInfo>::with_capacity(sig.args.len());
    clif_sig.params.reserve(sig.args.len());
    let mut id_counter = 0usize;
    for (_, ty) in sig.args.iter() {
        let var_info = make_var_info(global, &mut id_counter, ty.clone());
        var_info
            .flat_ty()
            .fields()
            .map(AbiParam::new)
            .for_each(|t| clif_sig.params.push(t));
        args.push(var_info);
    }
    for ty in trans_ty(global, &sig.ret_type).fields() {
        clif_sig.returns.push(AbiParam::new(ty));
    }
    let ret_ty = super::trans_ty(global, &sig.ret_type);
    (clif_sig, args, ret_ty)
}
