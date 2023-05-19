use std::{collections::HashMap, fmt::Debug};

use crate::{
    ast::{type_expr::TypeExpr, Signature},
    mir::{Block, MirFunction, MirObject, Statement, Terminator, Value, VarInfo, Variable},
    IndexVecFormatter,
};
use cranelift::prelude::{AbiParam, Block as ClifBlock, InstBuilder, TrapCode};
use cranelift_codegen::{
    ir::{UserExternalName, UserFuncName},
    isa::CallConv,
    settings, Context,
};

pub mod context;

use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable as ClifVariable};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

pub use cranelift::prelude::{
    types as clif_types, EntityRef, Signature as ClifSignature, Type as ClifType,
    Value as ClifValue,
};

pub use cranelift_codegen::ir::function::Function as ClifFunction;
use index_vec::IndexVec;

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
    let mut generator = FuncCodeGenerator::new(global, func_builder_ctx, &mut clif_func, mir_func);
    dbg!(&generator);
    match mir_func.blocks.split_first() {
        Some((first, tail)) => {
            generator.gen_entry_block(first);
            for block in tail {
                generator.gen_block(block);
            }
        }
        None => panic!("reached a MIR function with no blocks"),
    }

    generator.finalize();

    dbg!(&clif_func);

    // add it into the cranelift object module
    let mut ctx = Context::for_function(clif_func);
    obj_module.define_function(func_id, &mut ctx).unwrap();
}

static TUPLE_FIELDS_LABELS: [&'static str; 16] = [
    "_0", "_1", "_2", "_3", "_4", "_5", "_6", "_7", "_8", "_9", "_10", "_11", "_12", "_13", "_14",
    "_15",
];

#[derive(Clone)]
enum Slot {
    Empty,
    Single(ClifVariable),
    Aggregate(Aggregate),
}

impl Debug for Slot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "empty_slot"),
            Self::Single(clif_var) => write!(f, "single_slot({:?})", clif_var),
            Self::Aggregate(aggregate) => {
                write!(f, "aggregate ")?;
                aggregate.fmt(f)
            }
        }
    }
}

#[derive(Clone, Default)]
struct Aggregate(HashMap<&'static str, Slot>);

impl Debug for Aggregate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Default)]
struct VarTable(IndexVec<Variable, Slot>);

impl Debug for VarTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        IndexVecFormatter(&self.0).fmt(f)
    }
}

impl VarTable {
    fn make_slot(
        global: &GlobalContext,
        func_builder: &mut FunctionBuilder,
        ty: &TypeExpr,
        counter: &mut usize,
    ) -> Slot {
        match ty {
            TypeExpr::Tuple(fields) if fields.is_empty() => Slot::Empty,
            TypeExpr::Tuple(fields) => {
                let mut aggregate = Aggregate::default();
                aggregate.0.reserve(fields.len());
                for (i, ty) in fields.iter().enumerate() {
                    let field = TUPLE_FIELDS_LABELS[i];
                    let child = Self::make_slot(global, func_builder, ty, counter);
                    aggregate.0.insert(field, child);
                }
                Slot::Aggregate(aggregate)
            }
            TypeExpr::Array(..) => todo!(),
            TypeExpr::Never => Slot::Empty,
            _ => {
                let clif_ty = match ty {
                    TypeExpr::USize | TypeExpr::ISize => clif_types::I64,
                    TypeExpr::U128 | TypeExpr::I128 => clif_types::I128,
                    TypeExpr::U64 | TypeExpr::I64 => clif_types::I64,
                    TypeExpr::U32 | TypeExpr::I32 => clif_types::I32,
                    TypeExpr::U16 | TypeExpr::I16 => clif_types::I16,
                    TypeExpr::U8 | TypeExpr::I8 => clif_types::I8,
                    TypeExpr::F64 => clif_types::F64,
                    TypeExpr::F32 => clif_types::F32,
                    TypeExpr::Char => clif_types::I32,
                    TypeExpr::Bool => clif_types::I8,
                    TypeExpr::Ptr(..) | TypeExpr::Ref(..) => clif_types::I64,
                    TypeExpr::Slice(..) => clif_types::I64X2,
                    TypeExpr::Fn(_, _) => clif_types::I64,
                    TypeExpr::TypeName(_) => todo!(),
                    TypeExpr::Struct => todo!(),
                    TypeExpr::Union => todo!(),
                    TypeExpr::Enum => todo!(),
                    TypeExpr::_UnknownNumeric(_) => todo!(),
                    TypeExpr::_Unknown => todo!(),
                    TypeExpr::INVALID => panic!("INVALID type reachabled"),
                    TypeExpr::Tuple(..) => unreachable!(),
                    TypeExpr::Array(..) => unreachable!(),
                    TypeExpr::Never => unreachable!(),
                };
                let clif_var = ClifVariable::new(*counter);
                *counter += 1;
                func_builder.declare_var(clif_var, clif_ty);
                Slot::Single(clif_var)
            }
        }
    }
    fn from_vars(
        global: &GlobalContext,
        func_builder: &mut FunctionBuilder,
        vars: &IndexVec<Variable, VarInfo>,
    ) -> Self {
        let mut var_counter = 0usize;
        let slots: IndexVec<Variable, Slot> = vars
            .iter()
            .map(|var_info| Self::make_slot(global, func_builder, &var_info.ty, &mut var_counter))
            .collect();
        Self(slots)
    }
}

struct FuncCodeGenerator<'f> {
    global: &'f GlobalContext,
    func_builder: FunctionBuilder<'f>,
    var_table: VarTable,
}

impl<'f> Debug for FuncCodeGenerator<'f> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FunctionCodegen")
            .field("var_table", &self.var_table)
            .finish_non_exhaustive()
    }
}

impl<'f> FuncCodeGenerator<'f> {
    fn new(
        global: &'f GlobalContext,
        func_builder_ctx: &'f mut FunctionBuilderContext,
        clif_func: &'f mut ClifFunction,
        mir_func: &MirFunction,
    ) -> Self {
        let mut func_builder = FunctionBuilder::new(clif_func, func_builder_ctx);
        let var_table = VarTable::from_vars(global, &mut func_builder, &mir_func.vars);
        Self {
            global,
            func_builder,
            var_table,
        }
    }

    fn finalize(mut self) {
        self.func_builder.seal_all_blocks();
        self.func_builder.finalize();
    }

    fn gen_entry_block(&mut self, block: &Block) {
        let clif_block = self.func_builder.create_block();
        self.func_builder
            .append_block_params_for_function_params(clif_block);
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

    fn gen_value(&mut self, val: &Value, mut foreach: impl FnMut(ClifValue)) {
        match val {
            Value::Number(_, _) => todo!(),
            &Value::Bool(b) => {
                let clif_val = self
                    .func_builder
                    .ins()
                    .iconst(clif_types::I32, i64::from(b));
                foreach(clif_val)
            }
            &Value::Char(c) => {
                let clif_val = self
                    .func_builder
                    .ins()
                    .iconst(clif_types::I32, u32::from(c) as i64);
                foreach(clif_val)
            }
            Value::Copy(_) => todo!(),
            Value::Ref(_) => todo!(),
            Value::Void => (),
            Value::Unreachable => panic!("Unreachable reached"),
        }
    }
}
