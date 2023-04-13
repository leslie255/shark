use std::slice::Iter;

use crate::ast::{type_expr::TypeExpr, Signature};
use cranelift::prelude::{
    types as clif_types, AbiParam, Signature as ClifSignature, Type as ClifType,
};
use cranelift_codegen::isa::CallConv;

mod context;
mod typecheck;

pub use context::{build_global_context, GlobalContext};

#[derive(Debug, Clone)]
pub(self) enum CollectiveType {
    Empty,
    Single([ClifType; 1]),
    Multi(Vec<ClifType>),
}

impl CollectiveType {
    pub fn as_slice(&self) -> &[ClifType] {
        match self {
            CollectiveType::Empty => &[],
            CollectiveType::Single(arr) => arr.as_slice(),
            CollectiveType::Multi(vec) => vec.as_slice(),
        }
    }
    pub fn fields<'short>(&'short self) -> Fields<'short> {
        match self {
            CollectiveType::Empty => Fields::Empty,
            &CollectiveType::Single([ty]) => Fields::Single(ty),
            CollectiveType::Multi(x) => Fields::Multi(x.iter()),
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

fn trans_sig(global: &GlobalContext, sig: &Signature) -> ClifSignature {
    let mut clif_sig = ClifSignature::new(CallConv::SystemV);
    clif_sig.params.reserve(sig.args.len());
    for (_, ty) in sig.args.iter() {
        let collective = trans_ty(global, ty);
        collective
            .fields()
            .map(AbiParam::new)
            .for_each(|t| clif_sig.params.push(t));
    }
    clif_sig
}
