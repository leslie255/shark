use std::{collections::HashMap, ops::Deref};

use either::Either::{Left, Right};
use index_vec::IndexVec;

use crate::{
    ast::{
        type_expr::{NumericType, TypeExpr, TYPEEXPR_VOID},
        Ast, AstNode, AstNodeRef, Signature,
    },
    error::{
        location::{SourceLocation, Traced},
        CollectIfErr, ErrorContent,
    },
    gen::GlobalContext,
    token::NumValue,
};

use super::{
    Block, BlockRef, Lvalue, MirFunction, MirObject, Operand, Rvalue, Statement, Terminator,
    VarInfo, Variable,
};

/// Contains states needed for the building of a MIR function.
/// User of the builder is expected to call `MirFuncBuilder::make_signature` to construct this
/// builder, and then feed it with AST nodes by calling `MirFuncBuilder::next_stmt`, and then call
/// `MirFuncBuilder::finish` to finally yield the built `MirFunction`.
#[derive(Debug, Clone)]
struct MirFuncBuilder<'g> {
    /// The global context
    global: &'g GlobalContext,

    /// The MIR function this builder is constructing
    function: MirFunction,

    /// Return type of the function
    ret_ty: TypeExpr,

    /// A "cursor" pointing at the current block that the builder is writing to.
    /// Avoid directly indexing `self.function.blocks`, always use `add_stmt` and `set_term` for
    /// writing to the current block. This is to ensure that:
    ///     1. Existing `StatementRef`s are still valid
    ///     2. (TODO) If a block is early-terminated, `add_stmt` and `set_term` won't actually do anything
    current_block: BlockRef,

    /// If the current block is already early-terminated, no further writing is done on the block,
    /// but we would still want to dry-run the MIR builder on the unreachable code for typechecking.
    is_early_terminated: bool,

    /// Map local variable names to variable ID's, uses a stack structure for entering and exiting
    /// AST blocks.
    /// If a variable is shadowed then it's overwritten.
    locals: Vec<HashMap<&'static str, Variable>>,
}

impl<'g> MirFuncBuilder<'g> {
    /// Initialize the builder
    fn make_signature(global: &'g GlobalContext, sign: &Signature) -> Self {
        let mut vars = IndexVec::<Variable, VarInfo>::with_capacity(sign.args.len());
        let mut locals = Vec::<HashMap<&'static str, Variable>>::new();
        locals.push(HashMap::new());
        for (arg_name, arg_ty) in &sign.args {
            let var_info = VarInfo {
                is_mut: true,
                ty: arg_ty.clone(),
                name: Some(*arg_name),
            };
            let var = vars.push(var_info);
            unsafe {
                locals.get_unchecked_mut(0).insert(*arg_name, var);
            }
        }
        MirFuncBuilder {
            global,
            function: MirFunction {
                blocks: IndexVec::from_iter([Block::default()]),
                vars,
            },
            current_block: BlockRef(0),
            is_early_terminated: false,
            ret_ty: sign.ret_type.clone(),
            locals,
        }
    }

    fn finish(self) -> MirFunction {
        self.function
    }

    /// Feed the builder with the next statement inside the function
    fn next_stmt(&mut self, node: &Traced<AstNode>) {
        let oper = self.convert_expr(node);
        let oper = match oper {
            Some(x) => x,
            None => return,
        };
        if !self.operand_type(&oper).map_or(true, TypeExpr::is_trivial) {
            ErrorContent::UnusedValue
                .wrap(node.src_loc())
                .collect_into(&self.global.err_collector);
            return;
        }
    }

    fn convert_expr(&mut self, node: &Traced<AstNode>) -> Option<Operand> {
        match node.inner() {
            &AstNode::Identifier(id) => {
                // TODO: static variables
                let var = self
                    .find_local(id)
                    .ok_or(ErrorContent::UndefinedVar(id).wrap(node.src_loc()))
                    .collect_err(&self.global.err_collector)?;
                Some(Lvalue::Variable(var).into())
            }
            &AstNode::Number(numval) => {
                let numeric_ty = match numval {
                    NumValue::I(..) => NumericType::default().signed().int(),
                    NumValue::U(..) => NumericType::default().int(),
                    NumValue::F(..) => NumericType::default(),
                };
                let ty = TypeExpr::_UnknownNumeric(numeric_ty);
                Some(Rvalue::Number(ty, numval).into())
            }
            AstNode::String(_) => todo!(),
            &AstNode::Char(c) => Some(Rvalue::Char(c).into()),
            &AstNode::Bool(b) => Some(Rvalue::Bool(b).into()),
            AstNode::Array(_) => todo!(),
            AstNode::MathOp(_, _, _) => todo!(),
            AstNode::BitOp(_, _, _) => todo!(),
            AstNode::BoolOp(_, _, _) => todo!(),
            AstNode::Cmp(_, _, _) => todo!(),
            AstNode::MemberAccess(_, _) => todo!(),
            AstNode::BitNot(_) => todo!(),
            AstNode::BoolNot(_) => todo!(),
            AstNode::UnarySub(_) => todo!(),
            AstNode::UnaryAdd(_) => todo!(),
            AstNode::Call(callee, args) => self.convert_call(&callee, &args),
            AstNode::Let(lhs, ty, rhs) => {
                let stmt = self.convert_let(*lhs, ty.as_ref(), *rhs)?;
                self.add_stmt(stmt);
                None
            }
            &AstNode::Assign(lhs, rhs) => {
                let stmt = self.convert_assign(&lhs, &rhs)?;
                self.add_stmt(stmt);
                None
            }
            AstNode::MathOpAssign(_, _, _) => todo!(),
            AstNode::BitOpAssign(_, _, _) => todo!(),
            AstNode::TakeRef(_) => todo!(),
            AstNode::Deref(_) => todo!(),
            AstNode::Block(_) => todo!(),
            AstNode::FnDef(_) => todo!(),
            AstNode::If(_) => todo!(),
            AstNode::Loop(_) => todo!(),
            AstNode::Return(child) => {
                let result = self.convert_return(child.as_deref(), node.src_loc());
                self.is_early_terminated = true;
                result
            }
            AstNode::Break => todo!(),
            AstNode::Continue => todo!(),
            AstNode::Tail(_) => todo!(),
            AstNode::Typecast(_, _) => todo!(),
            AstNode::TypeDef(_, _) => todo!(),
            AstNode::StructDef(_) => todo!(),
            AstNode::UnionDef(_) => todo!(),
            AstNode::EnumDef(_) => todo!(),
            AstNode::Tuple(_) => todo!(),
        }
    }

    /// Generates a call statement, returns the call results
    fn convert_call(&mut self, callee: &Traced<AstNode>, args: &[AstNodeRef]) -> Option<Operand> {
        let func_name = callee
            .as_identifier()
            .ok_or(ErrorContent::Todo("Indirect function calls").wrap(callee.src_loc()))
            .collect_err(&self.global.err_collector)?;
        let func_sig = &self
            .global
            .func(func_name)
            .ok_or(ErrorContent::FuncNotExist(func_name).wrap(callee.src_loc()))
            .collect_err(&self.global.err_collector)?
            .sig;
        let mut arg_opers = Vec::<Operand>::with_capacity(args.len());
        let result_var = self.function.vars.push(VarInfo {
            is_mut: false,
            ty: func_sig.ret_type.clone(),
            name: None,
        });
        let result_oper = Operand::from(Lvalue::Variable(result_var));
        for arg in args {
            let arg_oper = self.convert_expr(&arg)?;
            arg_opers.push(arg_oper);
        }
        let call_stmt = Statement::StaticCall {
            func_name,
            args: arg_opers,
            result: result_oper.clone(),
        };
        self.add_stmt(call_stmt);
        Some(result_oper)
    }

    /// Generates a `let` statement, returns the statement
    fn convert_let(
        &mut self,
        lhs: AstNodeRef,
        ty: Option<&TypeExpr>,
        rhs: Option<AstNodeRef>,
    ) -> Option<Statement> {
        let name = lhs
            .as_identifier()
            .unwrap_or_else(|| todo!("pattern matched `let`"));

        // Register the variable as type `{unknown}` first before doing anything else.
        // Because in case of early return we would still want subsequent usages of this variable to
        // be considered valid by the type checker.
        let var_info = VarInfo {
            is_mut: true,
            ty: TypeExpr::_Unknown,
            name: Some(name),
        };
        let var = self.function.vars.push(var_info);
        self.locals.last_mut().unwrap().insert(name, var);

        // RHS and type cannot be both absent
        if rhs.is_none() && ty.is_none() {
            ErrorContent::LetNoTypeOrRHS
                .wrap(lhs.src_loc())
                .collect_into(&self.global.err_collector);
            return None;
        }

        let rhs_oper = self.convert_expr(rhs.as_deref()?)?;
        let ty = match ty {
            Some(x) => x.clone(),
            None => {
                let infered = self
                    .operand_type(&rhs_oper)
                    .ok_or(ErrorContent::TypeInferFailed.wrap(lhs.src_loc()))
                    .collect_err(&self.global.err_collector)?;
                if !infered.is_concrete() {
                    ErrorContent::Todo("Partial type infer")
                        .wrap(lhs.src_loc())
                        .collect_into(&self.global.err_collector);
                    return None;
                }
                infered.clone()
            }
        };

        self.function.vars[var].ty = ty;
        Some(Statement::Assign(Lvalue::Variable(var), rhs_oper))
    }

    fn convert_assign(
        &mut self,
        lhs: &Traced<AstNode>,
        rhs: &Traced<AstNode>,
    ) -> Option<Statement> {
        let name = lhs
            .as_identifier()
            .ok_or(ErrorContent::Todo("Pattern-matched `=`").wrap(lhs.src_loc()))
            .collect_err(&self.global.err_collector)?;
        // TODO: static variables
        let var = self
            .find_local(name)
            .ok_or(ErrorContent::UndefinedVar(name).wrap(lhs.src_loc()))
            .collect_err(&self.global.err_collector)?;
        self.locals.last_mut().unwrap().insert(name, var);
        let rhs_oper = self.convert_expr(&rhs)?;
        Some(Statement::Assign(Lvalue::Variable(var), rhs_oper))
    }

    fn convert_return(
        &mut self,
        child: Option<&Traced<AstNode>>,
        return_loc: SourceLocation,
    ) -> Option<Operand> {
        let child = match child {
            Some(x) => x,
            None => {
                if !self.ret_ty.is_void() {
                    ErrorContent::MismatchdTypes(self.ret_ty.clone(), TypeExpr::void())
                        .wrap(return_loc)
                        .collect_into(&self.global.err_collector);
                    return None;
                }
                self.set_term(Terminator::Return(Rvalue::Void.into()));
                return Some(Rvalue::Unreachable.into());
            }
        };
        let oper = self.convert_expr(child)?;
        self.set_term(Terminator::Return(oper));
        Some(Rvalue::Unreachable.into())
    }

    /// Deduce the type of an operand, returns `None` if there is a type error (does not report the
    /// type error)
    fn operand_type<'a>(&'a self, oper: &'a Operand) -> Option<&'a TypeExpr> {
        match &oper.0 {
            Left(lval) => self.lval_type(lval),
            Right(rval) => match rval {
                Rvalue::Number(ty, _) => Some(ty),
                Rvalue::Bool(..) => Some(&TypeExpr::Bool),
                Rvalue::Char(..) => Some(&TypeExpr::Char),
                &Rvalue::CallResult(var) => Some(&self.function.vars[var].ty),
                Rvalue::Void => Some(&TYPEEXPR_VOID),
                Rvalue::Unreachable => Some(&TypeExpr::Never),
            },
        }
    }

    /// Deduce the type of an lvalue, returns `None` if there is a type error (does not report the
    /// type error)
    fn lval_type<'a>(&'a self, lval: &Lvalue) -> Option<&'a TypeExpr> {
        match lval {
            Lvalue::Deref(lval) => match self.lval_type(&lval)? {
                TypeExpr::Ptr(ty) | TypeExpr::Ref(ty) => Some(&ty),
                _ => None,
            },
            &Lvalue::Variable(var) => Some(&self.function.vars[var].ty),
        }
    }

    /// Add a statement to the current block
    fn add_stmt(&mut self, stmt: Statement) {
        if !self.is_early_terminated {
            let i = self.current_block;
            let _ = self.function.blocks[i].body.push(stmt);
        }
    }

    /// Set the terminator for the current block
    fn set_term(&mut self, term: Terminator) {
        if !self.is_early_terminated {
            let i = self.current_block;
            self.function.blocks[i].terminator = Some(term);
        }
    }

    /// Find a local variable from its name
    fn find_local(&self, name: &str) -> Option<Variable> {
        self.locals
            .iter()
            .rev()
            .find_map(|map| map.get(name))
            .copied()
    }
}

pub fn make_mir<'g>(global: &'g GlobalContext, ast: &'g Ast) -> MirObject {
    let mut mir_object = MirObject::default();
    for root_node in &ast.root_nodes {
        let root_node = root_node.deref();
        match root_node.inner() {
            AstNode::FnDef(ast_func) => match &ast_func.body {
                Some(body) => {
                    let mut builder = MirFuncBuilder::make_signature(global, &ast_func.sign);
                    for node in body {
                        builder.next_stmt(&node);
                    }
                    mir_object.functions.push(builder.finish());
                }
                None => ErrorContent::Todo("External functions")
                    .wrap(root_node.src_loc())
                    .collect_into(&global.err_collector),
            },
            _ => ErrorContent::ExprNotAllowedAtTopLevel
                .wrap(root_node.src_loc())
                .collect_into(&global.err_collector),
        }
    }
    mir_object
}
