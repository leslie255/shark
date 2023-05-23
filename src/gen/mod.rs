use std::{collections::HashMap, fmt::Debug, vec};

use crate::{
    ast::{type_expr::TypeExpr, Signature},
    mir::{
        self, Block, CondKind, MirFunction, MirObject, Place, ProjectionEle, Statement, Terminator,
        Value, VarInfo, Variable,
    },
    IndexVecFormatter,
};
use cranelift::prelude::{
    AbiParam, Block as ClifBlock, ExtFuncData, ExternalName, InstBuilder, TrapCode,
};
use cranelift_codegen::{
    ir::{FuncRef, UserExternalName, UserFuncName},
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

pub fn compile(global: &GlobalContext, mir: &MirObject) -> ObjectModule {
    let mut obj_module = make_empty_obj_module("output");

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

    obj_module
}

fn make_empty_obj_module(name: &str) -> ObjectModule {
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

/// The expanded type of a variable, stored as a tree.
/// For example, a variable of type `(i32, (), (char, bool))` is expanded to:
///
/// ```
/// aggregate {
///     "_0": single_slot(var0),
///     "_1": empty,
///     "_2": aggregate {
///         "_0": single_slot(var1),
///         "_1": single_slot(var2),
///     },
/// }
/// ```
///
/// (Note that the fields of aggregates are not ordered, but they must be continuous)
///
/// A single slot can also be either refering to a variable or value in cranelift, the latter is
/// used in intermediate values
#[derive(Clone)]
enum Slot {
    Empty,
    Single(ClifVariable),
    Aggregate(Aggregate),
}

impl Slot {
    /// Create a slot from a type, accepts a closure that maps every `ClifType` to `ClifVariable`.
    fn from_ty(
        global: &GlobalContext,
        ty: &TypeExpr,
        make_var: &mut impl FnMut(ClifType) -> ClifVariable,
    ) -> Slot {
        match ty {
            TypeExpr::Tuple(fields) if fields.is_empty() => Self::Empty,
            TypeExpr::Tuple(fields) => {
                let mut aggregate = Aggregate::default();
                aggregate.vars.reserve(fields.len());
                for (i, ty) in fields.iter().enumerate() {
                    let field = mir::TUPLE_FIELDS_LABELS[i];
                    let child = Self::from_ty(global, ty, make_var);
                    aggregate.vars.insert(field, child);
                }
                Self::Aggregate(aggregate)
            }
            TypeExpr::Array(..) => todo!(),
            TypeExpr::Never => Self::Empty,
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
                    TypeExpr::TypeName(_)
                    | TypeExpr::Struct
                    | TypeExpr::Union
                    | TypeExpr::Enum
                    | TypeExpr::_UnknownNumeric(_)
                    | TypeExpr::_Unknown => todo!(),
                    TypeExpr::Tuple(..) | TypeExpr::Array(..) | TypeExpr::Never => unreachable!(),
                };
                let clif_var = make_var(clif_ty);
                Self::Single(clif_var)
            }
        }
    }

    fn field<'a>(&'a self, field: &str) -> Option<&'a Self> {
        match self {
            Slot::Empty | Slot::Single(..) => None,
            Slot::Aggregate(agg) => agg.vars.get(field),
        }
    }
}

#[derive(Debug, Clone)]
enum RvalueGenerator<'mir> {
    Empty,
    Val(ClifValue),
    /// TODO
    #[allow(dead_code)]
    ConstTuple(&'mir !),
    Vals(vec::IntoIter<ClifValue>),
}
impl Iterator for RvalueGenerator<'_> {
    type Item = ClifValue;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Empty => None,
            &mut Self::Val(val) => {
                *self = Self::Empty;
                Some(val)
            }
            Self::Vals(iter) => iter.next(),
            _ => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::Empty => (0, Some(0)),
            Self::Val(..) => (1, Some(1)),
            Self::Vals(x) => x.size_hint(),
            Self::ConstTuple(..) => unreachable!(),
        }
    }
}

/// See `Slot` above.
#[derive(Clone, Default)]
struct Aggregate {
    start: u32,
    vars: HashMap<&'static str, Slot>,
}

/// Keeps track of a variables and their slots
#[derive(Clone, Default)]
struct VarTable(IndexVec<Variable, Slot>);

impl VarTable {
    /// Construct a `VarTable` from a list of variables and their types
    fn from_vars(
        global: &GlobalContext,
        func_builder: &mut FunctionBuilder,
        vars: &IndexVec<Variable, VarInfo>,
    ) -> Self {
        let mut slots = IndexVec::<Variable, Slot>::with_capacity(vars.len());

        // counter for creating clif variables
        let mut var_counter = 0u32;

        // iterate through MIR variables
        let mut vars_iter = vars.iter().peekable();

        // set up argument variables
        let clif_block0 = func_builder.create_block();
        func_builder.switch_to_block(clif_block0);
        while let Some(var_info) = vars_iter.next_if(|v| v.is_arg) {
            slots.push(Slot::from_ty(global, &var_info.ty, &mut |clif_ty| {
                let clif_var = ClifVariable::from_u32(var_counter);
                var_counter += 1;
                let arg_val = func_builder.append_block_param(clif_block0, clif_ty);
                func_builder.declare_var(clif_var, clif_ty);
                func_builder.def_var(clif_var, arg_val);
                clif_var
            }));
        }

        // set up other variables
        for var_info in vars_iter {
            slots.push(Slot::from_ty(global, &var_info.ty, &mut |clif_ty| {
                let clif_var = ClifVariable::from_u32(var_counter);
                var_counter += 1;
                func_builder.declare_var(clif_var, clif_ty);
                clif_var
            }));
        }

        Self(slots)
    }

    /// Returns the `Slot` from the variable, panics if variable is out of range
    fn slot<'a>(&'a self, var: Variable) -> &'a Slot {
        &self.0[var]
    }
}

/// Contains states needed for code generation.
/// User of the generator is expected to call `FuncCodeGenerator::new` to contruct the generator,
/// and then call `FuncCodeGenerator::gen_entry_block` to generate the first block,
/// `FuncCodeGenerator::gen_block` to generate the second block, and then
/// `FuncCodeGenerator::finalize` before using the cranelift function.
struct FuncCodeGenerator<'f> {
    #[allow(dead_code)] // will be used in the future to look up typenames
    global: &'f GlobalContext,
    func_builder: FunctionBuilder<'f>,
    var_table: VarTable,
    /// Cranelift requires functions called inside this function to be declared at function head
    imported_funcs: HashMap<FuncIndex, FuncRef>,
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
            imported_funcs: HashMap::default(),
        }
    }

    fn finalize(mut self) {
        self.func_builder.seal_all_blocks();
        self.func_builder.finalize();
    }

    fn gen_entry_block(&mut self, block: &Block) {
        for stmt in &block.body {
            self.gen_stmt(stmt);
        }

        let term = block
            .terminator
            .as_ref()
            .expect("Missing terminator in MIR block");
        self.gen_term(term);
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
        self.gen_term(term);
    }

    fn gen_term(&mut self, term: &Terminator) {
        match term {
            Terminator::Jmp(blockref) => {
                let clif_block = ClifBlock::new(blockref.0);
                self.func_builder.ins().jump(clif_block, &[]);
            }
            Terminator::CondJmp {
                cond,
                target,
                otherwise,
            } => {
                let target = ClifBlock::new(target.0);
                let otherwise = ClifBlock::new(otherwise.0);
                let cond_val = {
                    let mut rval_gen = self.gen_rval(&cond.val);
                    let cond = rval_gen.next().unwrap();
                    assert!(rval_gen.next().is_none());
                    cond
                };
                match cond.cond_kind {
                    CondKind::IfTrue => self.func_builder.ins().brif(
                        cond_val,
                        target,
                        &[],
                        otherwise,
                        &[],
                    ),
                    CondKind::IfFalse => self.func_builder.ins().brif(
                        cond_val,
                        otherwise,
                        &[],
                        target,
                        &[],
                    ),
                };
            }
            Terminator::Return(val) => {
                let clif_vals: Vec<ClifValue> = self.gen_rval(val).collect();
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
        match stmt {
            Statement::Assign(lhs, rhs) => self.gen_assign(lhs, rhs),
            Statement::StaticCall {
                func_idx,
                args,
                result,
            } => self.gen_call(*func_idx, &args, result),
            Statement::DynCall => todo!(),
            Statement::Nop => todo!(),
        }
    }

    fn gen_call(&mut self, func_idx: FuncIndex, args: &[Value], result: &Place) {
        // import function if needed
        let func_ref = match self.imported_funcs.get(&func_idx) {
            Some(&func_ref) => func_ref,
            None => {
                let func_info = &self.global.funcs[func_idx];
                // TODO: translate all signatures in the same pass as global context building
                let clif_sig = translate_sig(self.global, &func_info.sig);
                let sig_ref = self.func_builder.import_signature(clif_sig);
                let name_ref = self
                    .func_builder
                    .func
                    .declare_imported_user_function(UserExternalName::new(0, func_idx.0 as u32));
                let func_ref = self.func_builder.import_function(ExtFuncData {
                    name: ExternalName::User(name_ref),
                    signature: sig_ref,
                    colocated: false,
                });
                self.imported_funcs.insert(func_idx, func_ref);
                func_ref
            }
        };

        // generate arguments
        let mut clif_args = Vec::<ClifValue>::new();
        for arg in args {
            self.gen_rval(arg).collect_into(&mut clif_args);
        }

        // call
        let inst = self.func_builder.ins().call(func_ref, &clif_args);

        // store results into result place
        let call_results = self.func_builder.inst_results(inst);
        match self.solve_place(result) {
            Slot::Empty => (),
            &Slot::Single(clif_var) => {
                assert_eq!(call_results.len(), 1);
                let &clif_val = unsafe { call_results.get_unchecked(0) };
                dbg!(clif_var, clif_val);
                self.func_builder.def_var(clif_var, clif_val);
            }
            Slot::Aggregate(_) => todo!("aggregate as result of function"),
        }
    }

    fn gen_rval<'mir>(&mut self, val: &'mir Value) -> RvalueGenerator<'mir> {
        match val {
            Value::Number(ty, numval) => {
                let clif_ty = match ty {
                    TypeExpr::USize | TypeExpr::ISize => clif_types::I64,
                    TypeExpr::U128 | TypeExpr::I128 => clif_types::I128,
                    TypeExpr::U64 | TypeExpr::I64 => clif_types::I64,
                    TypeExpr::U32 | TypeExpr::I32 => clif_types::I32,
                    TypeExpr::U16 | TypeExpr::I16 => clif_types::I16,
                    TypeExpr::U8 | TypeExpr::I8 => clif_types::I8,
                    TypeExpr::F64 => clif_types::F64,
                    TypeExpr::F32 => clif_types::F32,
                    TypeExpr::_UnknownNumeric(num_ty) => match num_ty.is_int {
                        true => clif_types::I32,
                        false => clif_types::F64,
                    },
                    ty => unreachable!("non-integer type used for numeric const: {:?}", ty),
                };
                let clif_val = match clif_ty {
                    ty if ty.is_int() => self.func_builder.ins().iconst(clif_ty, numval.to_be()),
                    clif_types::F64 => self.func_builder.ins().f64const(numval.as_f().unwrap()),
                    clif_types::F32 => self
                        .func_builder
                        .ins()
                        .f32const(numval.as_f().unwrap() as f32),
                    _ => unreachable!(),
                };
                RvalueGenerator::Val(clif_val)
            }
            &Value::Bool(b) => {
                let clif_val = self.func_builder.ins().iconst(clif_types::I8, i64::from(b));
                RvalueGenerator::Val(clif_val)
            }
            &Value::Char(c) => {
                let clif_val = self
                    .func_builder
                    .ins()
                    .iconst(clif_types::I32, u32::from(c) as i64);
                RvalueGenerator::Val(clif_val)
            }
            Value::Copy(place) => self.copy_place(place),
            Value::Ref(..) => todo!(),
            Value::Void => RvalueGenerator::Empty,
            Value::Unreachable => panic!("Unreachable reached"),
        }
    }

    fn gen_assign(&mut self, lhs_place: &Place, rhs_val: &Value) {
        let lhs_slot = self.solve_place(lhs_place);
        match lhs_slot {
            Slot::Empty => assert!(self.gen_rval(rhs_val).next().is_none()),
            &Slot::Single(clif_var) => {
                let mut rval_gen = self.gen_rval(rhs_val);
                let clif_val = rval_gen.next().unwrap();
                self.func_builder.def_var(clif_var, clif_val);
                assert!(rval_gen.next().is_none());
            }
            Slot::Aggregate(_) => todo!("aggregate as lhs of assign"),
        }
    }

    fn copy_place<'mir>(&mut self, place: &'mir Place) -> RvalueGenerator<'mir> {
        match self.solve_place(place) {
            Slot::Empty => RvalueGenerator::Empty,
            &Slot::Single(var) => RvalueGenerator::Val(self.func_builder.use_var(var)),
            Slot::Aggregate(aggregate) => {
                let start = aggregate.start;
                let len = aggregate.vars.len() as u32;
                let vals: Vec<ClifValue> = (start..start + len)
                    .map(|id| self.func_builder.use_var(ClifVariable::from_u32(id)))
                    .collect();
                RvalueGenerator::Vals(vals.into_iter())
            }
        }
    }

    fn solve_place<'a>(&'a self, place: &Place) -> &'a Slot {
        match place.projections.as_slice() {
            [] => self.var_table.slot(place.local),
            projections => {
                let mut slot = self.var_table.slot(place.local);
                for proj in projections {
                    slot = match proj {
                        ProjectionEle::Deref(_) => todo!(),
                        ProjectionEle::Index(_) => todo!(),
                        ProjectionEle::Field(field) => slot.field(field).unwrap(),
                    };
                }
                slot
            }
        }
    }
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

impl Debug for Aggregate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(start: {}) ", self.start)?;
        self.vars.fmt(f)
    }
}

impl Debug for VarTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        IndexVecFormatter(&self.0).fmt(f)
    }
}

impl<'f> Debug for FuncCodeGenerator<'f> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FunctionCodegen")
            .field("var_table", &self.var_table)
            .finish_non_exhaustive()
    }
}
