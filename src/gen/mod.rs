#![allow(unused_imports)]

use std::ops::{Deref, Range};

use crate::{
    ast::{type_expr::TypeExpr, Ast, AstNode, AstNodeRef, Function, MathOpKind, Signature},
    error::{location::SourceLocation, CollectIfErr, ErrorContent},
    mir::MirObject,
    token::NumValue,
};
use cranelift::prelude::{ExtFuncData, ExternalName, InstBuilder, TrapCode};
use cranelift_codegen::{
    ir::{FuncRef, Function as ClifFunction, UserExternalName, UserFuncName},
    settings, verify_function, Context,
};

mod context;
mod value;

use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

pub use self::context::{build_global_context, GlobalContext};

pub use cranelift::prelude::{
    types as clif_types, EntityRef, Signature as ClifSignature, Type as ClifType,
    Value as ClifValue,
};

use self::value::{FlatType, Value};

pub fn make_empty_obj_module(name: &str) -> ObjectModule {
    let isa = cranelift_native::builder()
        .expect("Error getting the native ISA")
        .finish(settings::Flags::new(settings::builder()))
        .unwrap();
    let obj_builder =
        ObjectBuilder::new(isa, name, cranelift_module::default_libcall_names()).unwrap();
    ObjectModule::new(obj_builder)
}

fn trans_ty(global: &GlobalContext, ty: &TypeExpr) -> FlatType {
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
            [] => FlatType::Empty,
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
        TypeExpr::_Unknown => clif_types::INVALID.into(),
        TypeExpr::Never => FlatType::Empty,
        TypeExpr::_UnknownNumeric(..) => unreachable!(),
        TypeExpr::INVALID => unreachable!(),
    }
}

#[allow(unused_variables)]
pub fn compile(global: &mut GlobalContext, mir: &MirObject) {
    todo!()
}
