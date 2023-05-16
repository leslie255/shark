use std::{borrow::Cow, collections::HashMap, ops::Deref};

use index_vec::IndexVec;

use crate::{
    ast::{
        type_expr::{NumericType, TypeExpr},
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
    Block, BlockRef, MirFunction, MirObject, Place, ProjectionEle, Statement, Terminator, Value,
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
    ///     2. If a block is early-terminated, `add_stmt` and `set_term` won't actually do anything
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
        if !self.deduce_val_ty(&oper).map_or(true, |t| t.is_trivial()) {
            ErrorContent::UnusedValue
                .wrap(node.src_loc())
                .collect_into(&self.global.err_collector);
            return;
        }
    }

    fn convert_expr(&mut self, node: &Traced<AstNode>) -> Option<Value> {
        match node.inner() {
            &AstNode::Identifier(id) => {
                // TODO: static variables
                let var = self
                    .find_local(id)
                    .ok_or(ErrorContent::UndefinedVar(id).wrap(node.src_loc()))
                    .collect_err(&self.global.err_collector)?;
                Some(Value::Copy(Place::no_projection(var)))
            }
            &AstNode::Number(numval) => {
                let numeric_ty = match numval {
                    NumValue::I(..) => NumericType::default().signed().int(),
                    NumValue::U(..) => NumericType::default().int(),
                    NumValue::F(..) => NumericType::default(),
                };
                let ty = TypeExpr::_UnknownNumeric(numeric_ty);
                Some(Value::Number(ty, numval))
            }
            AstNode::String(_) => todo!(),
            &AstNode::Char(c) => Some(Value::Char(c)),
            &AstNode::Bool(b) => Some(Value::Bool(b)),
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
            AstNode::Ref(node) => self.convert_ref(&node),
            AstNode::Deref(node) => self.convert_deref(&node),
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
    fn convert_call(&mut self, callee: &Traced<AstNode>, args: &[AstNodeRef]) -> Option<Value> {
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
        let mut arg_opers = Vec::<Value>::with_capacity(args.len());
        let result_var = self.make_temp_var(func_sig.ret_type.clone());
        let result_place = Place::no_projection(result_var);
        for arg in args {
            let arg_oper = self.convert_expr(&arg)?;
            arg_opers.push(arg_oper);
        }
        let call_stmt = Statement::StaticCall {
            func_name,
            args: arg_opers,
            result: result_place.clone(),
        };
        self.add_stmt(call_stmt);
        Some(Value::Copy(result_place))
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
                    .deduce_val_ty(&rhs_oper)
                    .ok_or(ErrorContent::TypeInferFailed.wrap(lhs.src_loc()))
                    .collect_err(&self.global.err_collector)?;
                if !infered.is_concrete() {
                    ErrorContent::Todo("Partial type infer")
                        .wrap(lhs.src_loc())
                        .collect_into(&self.global.err_collector);
                    return None;
                }
                infered.into_owned()
            }
        };

        self.function.vars[var].ty = ty;
        Some(Statement::Assign(Place::no_projection(var), rhs_oper))
    }

    fn convert_assign(
        &mut self,
        lhs: &Traced<AstNode>,
        rhs: &Traced<AstNode>,
    ) -> Option<Statement> {
        let lhs_val = self.convert_expr(lhs)?;
        let lhs_place = match lhs_val {
            Value::Copy(place) => place,
            _ => {
                ErrorContent::InvalidAssignLHS
                    .wrap(lhs.src_loc())
                    .collect_into(&self.global.err_collector);
                return None;
            }
        };
        let rhs_oper = self.convert_expr(&rhs)?;
        Some(Statement::Assign(lhs_place, rhs_oper))
    }

    fn convert_return(
        &mut self,
        child: Option<&Traced<AstNode>>,
        return_loc: SourceLocation,
    ) -> Option<Value> {
        let child = match child {
            Some(x) => x,
            None => {
                if !self.ret_ty.is_void() {
                    ErrorContent::MismatchdTypes(self.ret_ty.clone(), TypeExpr::void())
                        .wrap(return_loc)
                        .collect_into(&self.global.err_collector);
                    return None;
                }
                self.set_term(Terminator::Return(Value::Void));
                return Some(Value::Unreachable);
            }
        };
        let oper = self.convert_expr(child)?;
        self.set_term(Terminator::Return(oper));
        Some(Value::Unreachable)
    }

    /// Deduce the type of a `Value`, returns `None` if there is a type error (does not report the
    /// type error)
    fn deduce_val_ty<'a>(&'a self, val: &'a Value) -> Option<Cow<'a, TypeExpr>> {
        match val {
            Value::Number(ty, _) => Some(Cow::Borrowed(ty)),
            Value::Bool(..) => Some(Cow::Owned(TypeExpr::Bool)),
            Value::Char(..) => Some(Cow::Owned(TypeExpr::Char)),
            Value::Copy(place) => self.deduce_place_ty(place),
            Value::Ref(place) => {
                let t = self.deduce_place_ty(place).map(Cow::into_owned)?;
                Some(Cow::Owned(TypeExpr::Ref(Box::new(t))))
            }
            Value::Void => Some(Cow::Owned(TypeExpr::void())),
            Value::Unreachable => Some(Cow::Owned(TypeExpr::Never)),
        }
    }

    /// Deduce the type of a `Place`, returns `None` if there is a type error (does not report the
    /// type error)
    fn deduce_place_ty<'a>(&'a self, place: &Place) -> Option<Cow<'a, TypeExpr>> {
        let base_ty = &self.function.vars[place.local].ty;
        match place.projections.as_slice() {
            [] => Some(Cow::Borrowed(base_ty)),
            projections => {
                let mut ty = base_ty.clone();
                for proj in projections {
                    ty = match proj {
                        ProjectionEle::Deref => match ty {
                            TypeExpr::Ref(ty) => *ty,
                            _ => return None,
                        },
                        ProjectionEle::Index(_) => todo!(),
                        ProjectionEle::Field(_) => todo!(),
                    }
                }
                Some(Cow::Owned(ty))
            }
        }
    }

    /// Creates a unnamed, immutable variable, with a given type
    fn make_temp_var(&mut self, ty: TypeExpr) -> Variable {
        self.function.vars.push(VarInfo {
            is_mut: false,
            ty,
            name: None,
        })
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

    fn convert_ref(&mut self, node: &Traced<AstNode>) -> Option<Value> {
        let val = self.convert_expr(node)?;
        match val {
            Value::Copy(place) => Some(Value::Ref(place)),
            val => {
                let ty = self.deduce_val_ty(&val).unwrap().into_owned();
                let temp_var = self.make_temp_var(ty);
                let temp_var_place = Place::no_projection(temp_var);
                self.add_stmt(Statement::Assign(temp_var_place.clone(), val));
                Some(Value::Ref(temp_var_place))
            }
        }
    }

    fn convert_deref(&mut self, node: &Traced<AstNode>) -> Option<Value> {
        let val = self.convert_expr(node)?;
        let place = match val {
            Value::Copy(mut place) => {
                if self
                    .deduce_place_ty(&place)
                    .map_or(true, |t| !t.is_ref() && !t.is_ptr())
                {
                    ErrorContent::InvalidDeref
                        .wrap(node.src_loc())
                        .collect_into(&self.global.err_collector);
                    return None;
                }
                place.projections.push(ProjectionEle::Deref);
                place
            }
            Value::Ref(place) => place,
            _ => {
                ErrorContent::InvalidDeref
                    .wrap(node.src_loc())
                    .collect_into(&self.global.err_collector);
                return None;
            }
        };
        Some(Value::Copy(place))
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
