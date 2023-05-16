use std::{collections::HashMap, ops::Deref};

use either::Either::{Left, Right};
use index_vec::IndexVec;

use crate::{
    ast::{
        type_expr::{NumericType, TypeExpr},
        Ast, AstNode, AstNodeRef, Signature,
    },
    error::{location::Traced, CollectIfErr, ErrorContent},
    gen::GlobalContext,
    token::NumValue,
};

use super::{
    Block, BlockRef, Lvalue, MirFunction, MirObject, Operand, Rvalue, Statement, StatementRef,
    VarInfo, Variable,
};

/// Contains states needed for the building of a MIR function.
/// User of the builder is expected to call `MirFuncBuilder::make_signature` to construct this
/// builder, and then feed it with AST nodes by calling `MirFuncBuilder::next_stmt`, and then call
/// `MirFuncBuilder::finish` to finally yield the built `MirFunction`.
#[derive(Debug, Clone)]
struct MirFuncBuilder<'g> {
    global: &'g GlobalContext,
    function: MirFunction,
    current_block: BlockRef,
    ret_ty: TypeExpr,

    /// Local variables inside a function from their names
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
            AstNode::Call(_, _) => todo!(),
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
            AstNode::Return(_) => todo!(),
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

    fn convert_let(
        &mut self,
        lhs: AstNodeRef,
        ty: Option<&TypeExpr>,
        rhs: Option<AstNodeRef>,
    ) -> Option<Statement> {
        let name = lhs
            .as_identifier()
            .unwrap_or_else(|| todo!("pattern matched `let`"));

        // RHS and type cannot be both absent
        if rhs.is_none() && ty.is_none() {
            // Register the variable as type `{unknown}` and then report error
            let var_info = VarInfo {
                is_mut: true,
                ty: TypeExpr::_Unknown,
                name: Some(name),
            };
            let var = self.function.vars.push(var_info);
            self.locals.last_mut().unwrap().insert(name, var);
            ErrorContent::LetNoTypeOrRHS
                .wrap(lhs.src_loc())
                .collect_into(&self.global.err_collector);
            return None;
        }

        let rhs_oper = || -> Option<Operand> {
            let rhs = rhs.as_deref()?;
            self.convert_expr(rhs)
        }();
        let ty = match ty {
            Some(x) => x.clone(),
            None => {
                let rhs_oper = rhs_oper.as_ref().unwrap();
                let infered = self
                    .operand_type(rhs_oper)
                    .ok_or(ErrorContent::TypeInferFailed.wrap(lhs.src_loc()))
                    .collect_err(&self.global.err_collector)?;
                if !infered.is_concrete() {
                    ErrorContent::Todo("Partial type infer")
                        .wrap(lhs.src_loc())
                        .collect_into(&self.global.err_collector);
                    TypeExpr::_Unknown
                } else {
                    infered.clone()
                }
            }
        };
        let var_info = VarInfo {
            is_mut: true,
            ty: ty.clone(),
            name: Some(name),
        };
        let var = self.function.vars.push(var_info);
        self.locals.last_mut().unwrap().insert(name, var);
        Some(Statement::Assign(Lvalue::Variable(var), rhs_oper?))
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

    /// Deduce the type of an operand, returns `None` if there is a type error (does not report the
    /// type error)
    fn operand_type<'a>(&'a self, oper: &'a Operand) -> Option<&'a TypeExpr> {
        match &oper.0 {
            Left(lval) => self.lval_type(lval),
            Right(rval) => match rval {
                Rvalue::Number(ty, _) => Some(ty),
                Rvalue::Bool(..) => Some(&TypeExpr::Bool),
                Rvalue::Char(..) => Some(&TypeExpr::Char),
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
    fn add_stmt(&mut self, stmt: Statement) -> StatementRef {
        let i = self.current_block;
        self.function.blocks[i].body.push(stmt)
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
