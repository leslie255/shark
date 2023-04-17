use std::ops::Range;

use crate::{
    ast::{type_expr::TypeExpr, Ast, AstNode, AstNodeRef, Function, MathOpKind, Signature},
    error::{location::SourceLocation, CollectIfErr, ErrorContent},
    token::NumValue,
};
use cranelift::prelude::{ExtFuncData, ExternalName, InstBuilder, TrapCode};
use cranelift_codegen::{
    ir::{FuncRef, Function as ClifFunction, UserExternalName, UserFuncName},
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
    types as clif_types, EntityRef, Signature as ClifSignature, Type as ClifType,
    Value as ClifValue,
};

use self::{
    context::LocalContext,
    typecheck::type_matches,
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
        TypeExpr::_Unknown => clif_types::INVALID.into(),
        TypeExpr::_Numeric => clif_types::INVALID.into(),
        TypeExpr::_SInt => clif_types::INVALID.into(),
        TypeExpr::_Int => clif_types::INVALID.into(),
        TypeExpr::_Float => clif_types::INVALID.into(),
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

fn gen_imm(
    builder: &mut FunctionBuilder<'_>,
    global: &GlobalContext,
    #[allow(unused_variables)] local: &mut LocalContext,
    expect_ty: Option<&TypeExpr>,
    num_val: NumValue,
    loc: SourceLocation,
) -> Option<(TypeExpr, Value)> {
    let ty = match expect_ty {
        Some(TypeExpr::_Numeric) if num_val.is_int() => clif_types::I64,
        Some(TypeExpr::_Numeric) if num_val.is_f() => clif_types::F64,
        Some(TypeExpr::_Int) | Some(TypeExpr::_SInt) => clif_types::I64,
        Some(TypeExpr::_Unknown) => clif_types::I64,
        Some(TypeExpr::USize) | Some(TypeExpr::ISize) => clif_types::I64,
        Some(TypeExpr::U64) | Some(TypeExpr::I64) => clif_types::I64,
        Some(TypeExpr::U32) | Some(TypeExpr::I32) => clif_types::I32,
        Some(TypeExpr::U16) | Some(TypeExpr::I16) => clif_types::I16,
        Some(TypeExpr::U8) | Some(TypeExpr::I8) => clif_types::I8,
        Some(TypeExpr::F64) => clif_types::F64,
        Some(TypeExpr::F32) => clif_types::F32,
        Some(ty) => {
            ErrorContent::MismatchdTypes(TypeExpr::_Numeric, ty.clone())
                .wrap(loc)
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
            NumValue::U(..) => builder.ins().iconst(ty, num_val.to_be()),
            NumValue::I(..) => builder.ins().iconst(ty, num_val.to_be()),
            NumValue::F(f) => match ty {
                clif_types::F64 => builder.ins().f64const(f),
                clif_types::F32 => builder.ins().f32const(f as f32),
                _ => unreachable!(),
            },
        }
        .into(),
    ))
}

#[must_use]
fn gen_let(
    builder: &mut FunctionBuilder<'_>,
    global: &GlobalContext,
    local: &mut LocalContext,
    lhs: &'static str,
    ty: Option<&TypeExpr>,
    rhs: Option<AstNodeRef>,
) -> Option<()> {
    let rhs = rhs.expect("TODO: variable declaration without initial RHS");
    let (rhs_ty, rhs_val) = gen_expr(builder, global, local, ty, rhs)?;
    let ty = match ty {
        Some(lhs_ty) => {
            if !type_matches(global, lhs_ty, &rhs_ty) {
                ErrorContent::MismatchdTypes(lhs_ty.clone(), rhs_ty.clone())
                    .wrap(rhs.src_loc())
                    .collect_into(&global.err_collector);
                return None;
            }
            lhs_ty.clone()
        }
        None => {
            if rhs_ty.is_concrete() {
                rhs_ty
            } else {
                ErrorContent::NoneConreteTypeAsRhs
                    .wrap(rhs.src_loc())
                    .collect_into(&global.err_collector);
                return None;
            }
        }
    };
    let (clif_vars, flat_ty) = local.create_var(global, lhs, ty);
    for ((var, ty), val) in clif_vars
        .into_iter()
        .map(Variable::new)
        .zip(flat_ty.fields())
        .zip(rhs_val.clif_values())
    {
        builder.declare_var(var, ty);
        builder.def_var(var, val);
    }
    Some(())
}

fn gen_neg(
    builder: &mut FunctionBuilder<'_>,
    global: &GlobalContext,
    local: &mut LocalContext,
    child: AstNodeRef,
) -> Option<(TypeExpr, Value)> {
    let (ty, val) = gen_expr(builder, global, local, Some(&TypeExpr::_Numeric), child)?;
    if !ty.is_any_numeric() {
        ErrorContent::MismatchdTypes(TypeExpr::_Numeric, ty)
            .wrap(child.src_loc())
            .collect_into(&global.err_collector);
        return None;
    }
    let val = val.as_single().unwrap();
    let val = builder.ins().ineg(val);
    Some((ty, val.into()))
}

fn gen_math_op(
    builder: &mut FunctionBuilder,
    global: &GlobalContext,
    local: &mut LocalContext,
    expect_ty: Option<&TypeExpr>,
    opkind: MathOpKind,
    lhs_node: AstNodeRef,
    rhs_node: AstNodeRef,
) -> Option<(TypeExpr, Value)> {
    let (lhs_ty, lhs_val) = gen_expr(builder, global, local, expect_ty, lhs_node)?;
    let (rhs_ty, rhs_val) = gen_expr(builder, global, local, expect_ty, rhs_node)?;
    if !type_matches(global, &lhs_ty, &rhs_ty) {
        ErrorContent::MismatchdTypes(lhs_ty, rhs_ty)
            .wrap(lhs_node.src_loc().join(rhs_node.src_loc()))
            .collect_into(&global.err_collector);
        return None;
    }
    let lhs = lhs_val.as_single().unwrap();
    let rhs = rhs_val.as_single().unwrap();
    let val = if lhs_ty.is_i() {
        match opkind {
            MathOpKind::Add => builder.ins().iadd(lhs, rhs),
            MathOpKind::Sub => builder.ins().isub(lhs, rhs),
            MathOpKind::Mul => builder.ins().imul(lhs, rhs),
            MathOpKind::Div => builder.ins().sdiv(lhs, rhs),
            MathOpKind::Mod => builder.ins().srem(lhs, rhs),
        }
    } else if lhs_ty.is_u() {
        match opkind {
            MathOpKind::Add => builder.ins().iadd(lhs, rhs),
            MathOpKind::Sub => builder.ins().isub(lhs, rhs),
            MathOpKind::Mul => builder.ins().imul(lhs, rhs),
            MathOpKind::Div => builder.ins().udiv(lhs, rhs),
            MathOpKind::Mod => builder.ins().urem(lhs, rhs),
        }
    } else if lhs_ty.is_f() {
        match opkind {
            MathOpKind::Add => builder.ins().fadd(lhs, rhs),
            MathOpKind::Sub => builder.ins().fsub(lhs, rhs),
            MathOpKind::Mul => builder.ins().fmul(lhs, rhs),
            MathOpKind::Div => builder.ins().fdiv(lhs, rhs),
            MathOpKind::Mod => {
                ErrorContent::MismatchdTypes(TypeExpr::_Int, lhs_ty)
                    .wrap(lhs_node.src_loc().join(rhs_node.src_loc()))
                    .collect_into(&global.err_collector);
                return None;
            }
        }
    } else {
        ErrorContent::MismatchdTypes(TypeExpr::_Numeric, lhs_ty)
            .wrap(lhs_node.src_loc().join(rhs_node.src_loc()))
            .collect_into(&global.err_collector);
        return None;
    };
    Some((lhs_ty, val.into()))
}

fn gen_expr(
    builder: &mut FunctionBuilder<'_>,
    global: &GlobalContext,
    local: &mut LocalContext,
    expect_ty: Option<&TypeExpr>,
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
        &AstNode::Number(num_val) => {
            gen_imm(builder, global, local, expect_ty, num_val, node.src_loc())
        }
        AstNode::Let(lhs, ty, rhs) => {
            let ty = ty.as_ref();
            let rhs = rhs.as_ref().copied();
            gen_let(builder, global, local, lhs, ty, rhs)?;
            Some((TypeExpr::void(), Value::Empty))
        }
        AstNode::Call(callee, args) => gen_call(builder, global, local, *callee, &args),
        AstNode::UnaryAdd(..) => {
            ErrorContent::UnaryAdd
                .wrap(node.src_loc())
                .collect_into(&global.err_collector);
            return None;
        }
        &AstNode::UnarySub(child) => gen_neg(builder, global, local, child),
        &AstNode::MathOp(op, l, r) => gen_math_op(builder, global, local, expect_ty, op, l, r),
        node => {
            println!("skipping: {node:?}");
            Some((TypeExpr::void(), Value::Empty))
        }
    }
}

/// Imports an user-defined external function to a function, returns the signature of the imported
/// function and the result `FuncRef`, if the function is already imported, returns the result
/// stored in `local`
fn import_func_if_needed<'g>(
    builder: &mut FunctionBuilder<'_>,
    global: &'g GlobalContext,
    local: &mut LocalContext,
    name: &'static str,
) -> Result<(&'g Signature, FuncRef), ErrorContent> {
    let func_info = global.func(name).ok_or(ErrorContent::FuncNotExist(name))?;
    let func_ref = local.import_func_if_needed(name, || {
        let sig_ref = builder.import_signature((&func_info.clif_sig).clone());
        let name_ref = builder
            .func
            .declare_imported_user_function(UserExternalName::new(0, func_info.index));
        let func_ref = builder.import_function(ExtFuncData {
            name: ExternalName::user(name_ref),
            signature: sig_ref,
            colocated: false,
        });
        func_ref
    });
    Ok((&func_info.sig, func_ref))
}

#[must_use]
fn gen_call(
    builder: &mut FunctionBuilder<'_>,
    global: &GlobalContext,
    local: &mut LocalContext,
    callee: AstNodeRef,
    args: &[AstNodeRef],
) -> Option<(TypeExpr, Value)> {
    let func_name = callee
        .as_identifier()
        .expect("Indirect function calling is not supported yet");
    let (sig, func_ref) = import_func_if_needed(builder, global, local, func_name)
        .map_err(|e| e.wrap(callee.src_loc()))
        .collect_err(&global.err_collector)?;
    let args = if args.len() != sig.args.len() {
        ErrorContent::MismatchedArgsCount(Some(func_name), sig.args.len(), args.len())
            .wrap(callee.src_loc())
            .collect_into(&global.err_collector);
        // still checks if at least all the provided arguments are valid (e.g. if giving a variable
        // that does not exist)
        for &arg in args {
            gen_expr(builder, global, local, None, arg);
        }
        return None;
    } else {
        let mut arg_vals = Vec::<ClifValue>::with_capacity(args.len());
        let mut all_valid = true;
        for (nr, expect_ty) in args.iter().zip(sig.args.iter().map(|(_, t)| t)) {
            match gen_expr(builder, global, local, Some(expect_ty), *nr) {
                Some((ty, val)) => {
                    if !type_matches(global, expect_ty, &ty) {
                        ErrorContent::MismatchdTypes(expect_ty.clone(), ty.clone())
                            .wrap(nr.src_loc())
                            .collect_into(&global.err_collector);
                        all_valid = false;
                    }
                    val.clif_values().for_each(|v| arg_vals.push(v));
                }
                None => all_valid = false,
            }
        }
        if all_valid {
            arg_vals
        } else {
            return None;
        }
    };
    let inst = if sig.ret_type.is_never() {
        builder.ins().call(func_ref, &args);
        builder.ins().trap(TrapCode::UnreachableCodeReached);
        return Some((TypeExpr::Never, Value::Empty));
    } else {
        builder.ins().call(func_ref, &args)
    };
    let result_vals = Value::from(
        builder
            .inst_results(inst)
            .iter()
            .copied()
            .collect::<Vec<ClifValue>>(),
    );
    let result_ty = sig.ret_type.clone();
    Some((result_ty, result_vals))
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
                let x = gen_expr(builder, global, local, None, *node);
                match x {
                    Some((TypeExpr::Never, _)) => return Some((TypeExpr::Never, Value::Empty)),
                    None => return None,
                    _ => Some((TypeExpr::void(), Value::Empty)),
                }
            }
        },
        [.., last] => {
            let body = unsafe { body.get_unchecked(0..body.len() - 1) };
            for &node in body {
                let x = gen_expr(builder, global, local, None, node);
                match x {
                    Some((TypeExpr::Never, _)) => return Some((TypeExpr::Never, Value::Empty)),
                    _ => (),
                }
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
    #[allow(unused_variables)] loc: SourceLocation,
) -> Option<()> {
    // functions without bodies has already been declared by `build_global_context`
    let body = ast_func.body.as_ref()?;

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
        &global,
        ret_block,
        ast_func
            .sign
            .args
            .iter()
            .map(|(name, _)| *name)
            .zip(args.into_iter()),
        ast_func.sign.ret_type.clone(),
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
