use std::slice::Iter;

use crate::{
    ast::{type_expr::TypeExpr, Ast, AstNode, AstNodeRef, Function},
    error::{location::SourceLocation, CollectIfErr, ErrorContent},
};
use cranelift::prelude::{types as clif_types, EntityRef, Type as ClifType};
use cranelift_codegen::{
    ir::{Function as ClifFunction, UserFuncName},
    settings,
};

mod context;
mod typecheck;

use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_object::{ObjectBuilder, ObjectModule};

pub use context::{build_global_context, GlobalContext};

use self::context::LocalContext;

pub fn make_empty_obj_module(name: &str) -> ObjectModule {
    let isa = cranelift_native::builder()
        .expect("Error getting the native ISA")
        .finish(settings::Flags::new(settings::builder()))
        .unwrap();
    let obj_builder =
        ObjectBuilder::new(isa, name, cranelift_module::default_libcall_names()).unwrap();
    ObjectModule::new(obj_builder)
}

#[derive(Clone)]
pub(self) enum CollectiveType {
    Empty,
    Single([ClifType; 1]),
    Multi(Vec<ClifType>),
}

impl std::fmt::Debug for CollectiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl CollectiveType {
    pub fn as_slice(&self) -> &[ClifType] {
        match self {
            CollectiveType::Empty => &[],
            CollectiveType::Single(arr) => arr.as_slice(),
            CollectiveType::Multi(vec) => vec.as_slice(),
        }
    }

    pub fn fields(&self) -> Fields {
        match self {
            CollectiveType::Empty => Fields::Empty,
            &CollectiveType::Single([ty]) => Fields::Single(ty),
            CollectiveType::Multi(x) => Fields::Multi(x.iter()),
        }
    }

    pub fn len(&self) -> usize {
        match self {
            CollectiveType::Empty => 0,
            CollectiveType::Single(..) => 1,
            CollectiveType::Multi(vec) => vec.len(),
        }
    }
}

#[derive(Debug, Clone)]
pub(self) enum Fields<'short> {
    Empty,
    Single(ClifType),
    Multi(Iter<'short, ClifType>),
}
impl Iterator for Fields<'_> {
    type Item = ClifType;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            &mut Fields::Empty => None,
            &mut Fields::Single(x) => {
                *self = Fields::Empty;
                Some(x)
            }
            Fields::Multi(iter) => iter.next().copied(),
        }
    }
}

impl From<ClifType> for CollectiveType {
    fn from(value: ClifType) -> Self {
        Self::Single([value])
    }
}

impl From<Vec<ClifType>> for CollectiveType {
    fn from(value: Vec<ClifType>) -> Self {
        Self::Multi(value)
    }
}

fn trans_ty(global: &GlobalContext, ty: &TypeExpr) -> CollectiveType {
    match ty {
        TypeExpr::U128 | TypeExpr::I128 => clif_types::I128.into(),
        TypeExpr::USize | TypeExpr::ISize | TypeExpr::U64 | TypeExpr::I64 => clif_types::I64.into(),
        TypeExpr::U32 | TypeExpr::I32 => clif_types::I32.into(),
        TypeExpr::U16 | TypeExpr::I16 => clif_types::I16.into(),
        TypeExpr::U8 | TypeExpr::I8 => clif_types::I8.into(),
        TypeExpr::F64 => clif_types::F64.into(),
        TypeExpr::F32 => clif_types::F32.into(),
        TypeExpr::Char => clif_types::I32.into(),
        TypeExpr::Bool => clif_types::I8.into(),
        TypeExpr::Ptr(..) | TypeExpr::Ref(..) => clif_types::R64.into(),
        TypeExpr::Slice(..) => vec![clif_types::R64, clif_types::I64].into(),
        TypeExpr::Array(_, _) => todo!(),
        TypeExpr::Tuple(fields) => match fields.as_slice() {
            [] => CollectiveType::Empty,
            [ty] => trans_ty(global, ty),
            fields => {
                let mut children = Vec::<ClifType>::with_capacity(fields.len());
                for ty in fields {
                    let collective_ty = trans_ty(global, ty);
                    collective_ty.fields().collect_into(&mut children);
                }
                children.into()
            }
        },
        TypeExpr::Fn(_, _) => clif_types::R64.into(),
        TypeExpr::TypeName(_) => todo!(),
        TypeExpr::Struct => todo!(),
        TypeExpr::Union => todo!(),
        TypeExpr::Enum => todo!(),
    }
}

fn gen_expr(global: &GlobalContext, local: &mut LocalContext, node: &AstNode) -> Option<()> {
    todo!()
}

fn gen_block(global: &GlobalContext, local: &mut LocalContext, body: &[AstNodeRef]) -> Option<()> {
    for node in body {
        gen_expr(global, local, node);
    }
    todo!()
}

fn gen_function(global: &mut GlobalContext, func: &Function, loc: SourceLocation) -> Option<()> {
    // make sure the function has a body first
    let body = func
        .body
        .as_ref()
        .ok_or(ErrorContent::FuncWithoutBody.wrap(loc))
        .collect_err(&global.err_collector)?;

    let func_info = global.func(func.name).unwrap();
    let args = func_info.args.clone();
    let mut clif_func = ClifFunction::with_name_signature(
        UserFuncName::user(0, func_info.index),
        func_info.clif_sig.clone(),
    );
    let mut builder = FunctionBuilder::new(&mut clif_func, &mut global.func_builder_ctx);
    let entry_block = {
        let b = builder.create_block();
        builder.switch_to_block(b);
        builder.seal_block(b);
        b
    };
    let ret_block = builder.create_block();
    for arg_var_info in &args {
        for (clif_ty, id) in arg_var_info
            .flat_ty()
            .fields()
            .zip(arg_var_info.clif_vars())
        {
            let val = builder.append_block_param(entry_block, clif_ty);
            let var = Variable::new(id);
            builder.declare_var(var, clif_ty);
            builder.def_var(var, val);
        }
    }
    let mut local = LocalContext::new(
        ret_block,
        func.sign
            .args
            .iter()
            .map(|(name, _)| *name)
            .zip(args.into_iter()),
    );
    local.id_counter = builder.block_params(entry_block).len();

    gen_block(global, &mut local, &body);

    Some(())
}

fn compile(global: &mut GlobalContext, ast: &Ast) {
    for node in &ast.root_nodes {
        let loc = node.src_loc();
        match node.inner() {
            AstNode::FnDef(func) => {
                gen_function(global, func, loc);
            }
            _ => (), // already reported the error in `build_global_context`
        }
    }
}
