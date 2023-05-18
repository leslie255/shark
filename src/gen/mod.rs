use crate::{
    ast::{type_expr::TypeExpr, Signature},
    mir::{Block, MirFunction, MirObject, Statement, Terminator, Value},
};
use cranelift::prelude::{AbiParam, Block as ClifBlock, InstBuilder, TrapCode};
use cranelift_codegen::{
    ir::{UserExternalName, UserFuncName},
    isa::CallConv,
    settings, Context,
};

pub mod context;

use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

pub use cranelift::prelude::{
    types as clif_types, EntityRef, Signature as ClifSignature, Type as ClifType,
    Value as ClifValue,
};

pub use cranelift_codegen::ir::function::Function as ClifFunction;

use self::context::{FuncIndex, GlobalContext};

pub fn make_empty_obj_module(name: &str) -> ObjectModule {
    let isa = cranelift_native::builder()
        .expect("Error getting the native ISA")
        .finish(settings::Flags::new(settings::builder()))
        .unwrap();
    let obj_builder =
        ObjectBuilder::new(isa, name, cranelift_module::default_libcall_names()).unwrap();
    ObjectModule::new(obj_builder)
}

fn flatten_ty(global: &GlobalContext, ty: &TypeExpr, mut foreach: impl FnMut(ClifType)) {
    fn r(global: &GlobalContext, ty: &TypeExpr, f: &mut impl FnMut(ClifType)) {
        match ty {
            TypeExpr::INVALID => panic!("INVALID type reachabled"),
            TypeExpr::USize | TypeExpr::ISize => f(clif_types::I64),
            TypeExpr::U128 | TypeExpr::I128 => f(clif_types::I128),
            TypeExpr::U64 | TypeExpr::I64 => f(clif_types::I64),
            TypeExpr::U32 | TypeExpr::I32 => f(clif_types::I32),
            TypeExpr::U16 | TypeExpr::I16 => f(clif_types::I16),
            TypeExpr::U8 | TypeExpr::I8 => f(clif_types::I8),
            TypeExpr::F64 => f(clif_types::F64),
            TypeExpr::F32 => f(clif_types::F32),
            TypeExpr::Char => f(clif_types::I32),
            TypeExpr::Bool => f(clif_types::I8),
            TypeExpr::Ptr(..) | TypeExpr::Ref(..) => f(clif_types::I64),
            TypeExpr::Slice(..) => f(clif_types::I64X2),
            TypeExpr::Array(_, _) => todo!(),
            TypeExpr::Tuple(fields) => fields.iter().for_each(|t| r(global, t, f)),
            TypeExpr::Fn(_, _) => f(clif_types::I64),
            TypeExpr::TypeName(_) => todo!(),
            TypeExpr::Struct => todo!(),
            TypeExpr::Union => todo!(),
            TypeExpr::Enum => todo!(),
            TypeExpr::_UnknownNumeric(_) => todo!(),
            TypeExpr::_Unknown => todo!(),
            TypeExpr::Never => (),
        }
    }
    r(global, ty, &mut foreach)
}

fn translate_sig(global: &GlobalContext, sig: &Signature) -> ClifSignature {
    let mut params = Vec::<AbiParam>::with_capacity(sig.args.len());
    for (_, arg_ty) in &sig.args {
        flatten_ty(global, arg_ty, |clif_ty| {
            params.push(AbiParam::new(clif_ty))
        });
    }

    let mut returns = Vec::<AbiParam>::with_capacity(match &sig.ret_type {
        TypeExpr::Tuple(x) => x.len(),
        _ => 1,
    });
    flatten_ty(global, &sig.ret_type, |clif_ty| {
        returns.push(AbiParam::new(clif_ty))
    });

    ClifSignature {
        params,
        returns,
        call_conv: CallConv::SystemV,
    }
}

pub fn compile(global: &GlobalContext, mir: &MirObject) {
    let mut obj_module = {
        let isa = cranelift_native::builder()
            .expect("Error getting the native ISA")
            .finish(settings::Flags::new(settings::builder()))
            .unwrap();
        let obj_builder =
            ObjectBuilder::new(isa, "output", cranelift_module::default_libcall_names()).unwrap();
        ObjectModule::new(obj_builder)
    };

    let mut func_builder_ctx = FunctionBuilderContext::new();
    for (func_idx, func) in mir.functions.iter_enumerated() {
        compile_function(
            global,
            &mut obj_module,
            &mut func_builder_ctx,
            func_idx,
            func,
        );
    }
}

fn compile_function(
    global: &GlobalContext,
    obj_module: &mut ObjectModule,
    func_builder_ctx: &mut FunctionBuilderContext,
    func_idx: FuncIndex,
    mir_func: &MirFunction,
) {
    let func_info = &global.funcs[func_idx];

    // declare the function in the cranelift object module
    let clif_sig = translate_sig(global, &func_info.sig);
    let func_id = obj_module
        .declare_function(func_info.name, Linkage::Export, &clif_sig)
        .unwrap();
    let mut clif_func = ClifFunction::with_name_signature(
        UserFuncName::User(UserExternalName::new(0, func_idx.0 as u32)),
        clif_sig,
    );

    // codegen
    let mut generator = FuncCodeGenerator::new(func_builder_ctx, &mut clif_func);
    for block in &mir_func.blocks {
        generator.gen_block(block);
    }

    dbg!(&clif_func);

    // add it into the cranelift object module
    let mut ctx = Context::for_function(clif_func);
    obj_module.define_function(func_id, &mut ctx).unwrap();
}

struct FuncCodeGenerator<'f> {
    func_builder: FunctionBuilder<'f>,
}

impl<'f> std::fmt::Debug for FuncCodeGenerator<'f> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FunctionCodegen").finish_non_exhaustive()
    }
}

impl<'f> FuncCodeGenerator<'f> {
    fn new(
        func_builder_ctx: &'f mut FunctionBuilderContext,
        clif_func: &'f mut ClifFunction,
    ) -> Self {
        let func_builder = FunctionBuilder::new(clif_func, func_builder_ctx);
        Self { func_builder }
    }

    fn gen_block(&mut self, block: &Block) {
        let clif_block = self.func_builder.create_block();
        self.func_builder.switch_to_block(clif_block);
        for stmt in &block.body {
            self.gen_stmt(stmt);
        }
        let term = block
            .terminator
            .as_ref()
            .expect("Missing terminator in MIR block");
        self.gen_terminator(term);
    }

    fn gen_terminator(&mut self, term: &Terminator) {
        match term {
            Terminator::Jmp(blockref) => {
                let clif_block = ClifBlock::new(blockref.0);
                self.func_builder.ins().jump(clif_block, &[]);
            }
            Terminator::CondJmp { .. } => todo!(),
            Terminator::Return(val) => {
                let mut clif_vals = Vec::new();
                self.gen_value(val, |v| clif_vals.push(v));
                self.func_builder.ins().return_(&clif_vals);
            }
            Terminator::Unreachable => {
                self.func_builder
                    .ins()
                    .trap(TrapCode::UnreachableCodeReached);
            }
        }
    }

    fn gen_stmt(&mut self, stmt: &Statement) {
        println!("[TODO] skipping codegen for: {:?}", stmt);
    }

    #[allow(unused_mut, unused_variables)]
    fn gen_value(&mut self, val: &Value, mut foreach: impl FnMut(ClifValue)) {
        match val {
            Value::Number(_, _) => todo!(),
            Value::Bool(_) => todo!(),
            Value::Char(_) => todo!(),
            Value::Copy(_) => todo!(),
            Value::Ref(_) => todo!(),
            Value::Void => (),
            Value::Unreachable => panic!("Unreachable reached"),
        }
    }
}
