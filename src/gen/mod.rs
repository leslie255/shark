use std::ops::Range;

use crate::{
    ast::{type_expr::TypeExpr, Ast, AstNode, AstNodeRef, Function},
    error::{location::SourceLocation, CollectIfErr, ErrorContent},
    token::NumValue,
};
use cranelift::prelude::InstBuilder;
use cranelift_codegen::{
    ir::{Function as ClifFunction, UserFuncName},
    settings, verify_function, Context,
};

mod context;
mod typecheck;
mod value;

use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

pub use context::{build_global_context, GlobalContext};

pub use cranelift::prelude::{
    types as clif_types, EntityRef, Type as ClifType, Value as ClifValue,
};

use self::{
    context::LocalContext,
    value::{FlatType, Value},
};

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
        TypeExpr::_Unknown => panic!("Calling `trans_ty` on a non-concrete type {{unknown}}"),
        TypeExpr::_SInt => panic!("Calling `trans_ty` on a non-concrete type {{signed integer}}"),
        TypeExpr::_Int => panic!("Calling `trans_ty` on a non-concrete type {{integer}}"),
        TypeExpr::_Float => {
            panic!("Calling `trans_ty` on a non-concrete type {{floating point number}}")
        }
        TypeExpr::Never => FlatType::Empty,
    }
}

fn use_var(builder: &mut FunctionBuilder<'_>, var_range: Range<usize>) -> Value {
    match var_range.len() {
        0 => Value::Empty,
        1 => builder.use_var(Variable::new(var_range.start)).into(),
        _ => var_range
            .map(Variable::new)
            .map(|var| builder.use_var(var))
            .collect::<Vec<ClifValue>>()
            .into(),
    }
}

#[must_use]
fn gen_expr(
    builder: &mut FunctionBuilder<'_>,
    global: &GlobalContext,
    local: &mut LocalContext,
    #[allow(unused_variables)] expect_ty: Option<&TypeExpr>,
    node: AstNodeRef,
) -> Option<(TypeExpr, Value)> {
    match node.inner() {
        &AstNode::Identifier(name) => {
            let var_info = local
                .var(name)
                .ok_or(ErrorContent::UndefinedVar(name).wrap(node.src_loc()))
                .collect_err(&global.err_collector)?;
            let clif_vars = var_info.clif_vars();
            Some((var_info.ty().clone(), use_var(builder, clif_vars)))
        }
        AstNode::Number(num_val) => {
            let ty = match expect_ty {
                Some(TypeExpr::USize) | Some(TypeExpr::ISize) => clif_types::I64,
                Some(TypeExpr::U64) | Some(TypeExpr::I64) => clif_types::I64,
                Some(TypeExpr::U32) | Some(TypeExpr::I32) => clif_types::I32,
                Some(TypeExpr::U16) | Some(TypeExpr::I16) => clif_types::I16,
                Some(TypeExpr::U8) | Some(TypeExpr::I8) => clif_types::I8,
                Some(TypeExpr::F64) => clif_types::F64,
                Some(TypeExpr::F32) => clif_types::F32,
                Some(ty) => {
                    ErrorContent::MismatchdTypes(TypeExpr::_Int, ty.clone())
                        .wrap(node.src_loc())
                        .collect_into(&global.err_collector);
                    return None;
                }
                None => match num_val {
                    // TODO: range checking
                    NumValue::U(..) => clif_types::I64,
                    NumValue::I(..) => clif_types::I64,
                    NumValue::F(..) => clif_types::F64,
                },
            };
            Some((
                expect_ty.cloned().unwrap_or_else(|| match num_val {
                    NumValue::U(..) => TypeExpr::_Int,
                    NumValue::I(..) => TypeExpr::_SInt,
                    NumValue::F(..) => TypeExpr::_Float,
                }),
                match num_val {
                    // TODO: range checking and type checking
                    NumValue::U(..) => builder.ins().iconst(ty, 0),
                    NumValue::I(..) => builder.ins().iconst(ty, 0),
                    NumValue::F(..) => builder.ins().iconst(ty, 0),
                }
                .into(),
            ))
        }
        AstNode::Let(var_name, Some(ty), Some(rhs)) => {
            let (_rhs_ty, rhs_val) = gen_expr(builder, global, local, Some(ty), *rhs)?;
            // TODO: check_ty
            let (clif_vars, flat_ty) = local.create_var(global, var_name, ty.clone());
            for ((var, ty), val) in clif_vars
                .into_iter()
                .map(Variable::new)
                .zip(flat_ty.fields())
                .zip(rhs_val.clif_values())
            {
                builder.declare_var(var, ty);
                builder.def_var(var, val);
            }
            Some((TypeExpr::void(), Value::Empty))
        }
        AstNode::Let(_, None, None) => todo!("type infer"),
        AstNode::Let(_, None, _) => todo!("type infer"),
        node => {
            println!("skipping: {node:?}");
            Some((TypeExpr::void(), Value::Empty))
        }
    }
}

#[must_use]
fn gen_block(
    builder: &mut FunctionBuilder<'_>,
    global: &GlobalContext,
    local: &mut LocalContext,
    body: &[AstNodeRef],
    expect_ty: Option<&TypeExpr>,
) -> Option<(TypeExpr, Value)> {
    match body {
        [] => Some((TypeExpr::void(), Value::Empty)),
        [node] => match node.inner() {
            &AstNode::Tail(node) => gen_expr(builder, global, local, expect_ty, node),
            _ => {
                gen_expr(builder, global, local, None, *node)?;
                Some((TypeExpr::void(), Value::Empty))
            }
        },
        [.., last] => {
            let body = unsafe { body.get_unchecked(0..body.len() - 1) };
            for &node in body {
                gen_expr(builder, global, local, None, node)?;
            }
            match last.inner() {
                &AstNode::Tail(node) => gen_expr(builder, global, local, expect_ty, node),
                _ => {
                    gen_expr(builder, global, local, None, *last)?;
                    Some((TypeExpr::void(), Value::Empty))
                }
            }
        }
    }
}

fn gen_function(
    global: &mut GlobalContext,
    ast_func: &Function,
    loc: SourceLocation,
) -> Option<()> {
    // make sure the function has a body first
    let body = ast_func
        .body
        .as_ref()
        .ok_or(ErrorContent::FuncWithoutBody.wrap(loc))
        .collect_err(&global.err_collector)?;

    let func_info = global.func(ast_func.name).unwrap();
    let args = func_info.args.clone();
    let mut clif_func = ClifFunction::with_name_signature(
        UserFuncName::user(0, func_info.index),
        func_info.clif_sig.clone(),
    );
    let mut func_builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut clif_func, &mut func_builder_context);
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
        ast_func
            .sign
            .args
            .iter()
            .map(|(name, _)| *name)
            .zip(args.into_iter()),
    );
    local.id_counter = builder.block_params(entry_block).len();

    let (block_ty, block_val) = gen_block(
        &mut builder,
        global,
        &mut local,
        &body,
        Some(&ast_func.sign.ret_type),
    )?;

    if !block_ty.is_never() {
        let ret_vals: Vec<ClifValue> = trans_ty(global, &ast_func.sign.ret_type)
            .fields()
            .map(|ty| builder.append_block_param(ret_block, ty))
            .collect();
        builder.ins().jump(ret_block, block_val.as_slice());
        builder.switch_to_block(ret_block);
        builder.seal_block(ret_block);
        builder.ins().return_(ret_vals.as_slice());
    }

    println!("{}", clif_func.display());

    verify_function(&clif_func, global.obj_module().isa()).unwrap();

    let obj_module = &mut *global.obj_module_mut();
    let func_id = obj_module
        .declare_function(ast_func.name, Linkage::Export, &func_info.clif_sig)
        .unwrap();
    let mut ctx = Context::for_function(clif_func);
    obj_module.define_function(func_id, &mut ctx).unwrap();

    Some(())
}

pub fn compile(global: &mut GlobalContext, ast: &Ast) {
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
