#![allow(unused_imports)]

use std::ops::{Deref, Range};

use crate::{
    ast::{type_expr::TypeExpr, Ast, AstNode, AstNodeRef, Function, MathOpKind, Signature},
    error::{location::SourceLocation, CollectIfErr, ErrorContent},
    mir::{MirFunction, MirObject},
    token::NumValue,
};
use cranelift::prelude::{AbiParam, ExtFuncData, ExternalName, InstBuilder, TrapCode};
use cranelift_codegen::{
    ir::{FuncRef, UserExternalName, UserFuncName},
    settings, verify_function, Context,
};

pub mod context;

use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

pub use cranelift::prelude::{
    types as clif_types, EntityRef, Signature as ClifSignature, Type as ClifType,
    Value as ClifValue,
};

pub use cranelift_codegen::ir::function::Function as ClifFunction;

use self::context::{FuncInfo, GlobalContext};

pub fn make_empty_obj_module(name: &str) -> ObjectModule {
    let isa = cranelift_native::builder()
        .expect("Error getting the native ISA")
        .finish(settings::Flags::new(settings::builder()))
        .unwrap();
    let obj_builder =
        ObjectBuilder::new(isa, name, cranelift_module::default_libcall_names()).unwrap();
    ObjectModule::new(obj_builder)
}

#[allow(unused_variables)]
#[inline]
fn trans_ty(global: &GlobalContext, ty: &TypeExpr, foreach: impl FnMut(ClifType)) {
    todo!()
}

#[allow(unused_variables)]
pub fn compile(global: &mut GlobalContext, mir: &MirObject) {}

#[allow(unused_variables)]
fn compile_function(func_info: &FuncInfo, mir_func: &MirFunction) -> ClifFunction {
    todo!()
}

struct FuncCodeGenerator<'f> {
    clif_func_builder: FunctionBuilder<'f>,
}

impl<'f> std::fmt::Debug for FuncCodeGenerator<'f> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FunctionCodegen").finish_non_exhaustive()
    }
}

impl FuncCodeGenerator<'_> {}
