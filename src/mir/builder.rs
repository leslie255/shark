use std::{borrow::Cow, collections::HashMap, ops::Deref};

use index_vec::IndexVec;

use crate::{
    ast::{
        pat::{Mutability, Pattern},
        type_expr::{NumericType, TypeExpr},
        AstNode, AstNodeRef, IfExpr,
    },
    error::{
        location::{SourceLocation, Traced},
        CollectIfErr, ErrorContent,
    },
    gen::context::{FuncIndex, FuncInfo, GlobalContext},
    mir,
    token::NumValue,
};

use super::{
    typecheck, Block, BlockRef, CondKind, Condition, MirFunction, MirObject, Place, ProjectionEle,
    Statement, Terminator, Value, VarInfo, Variable,
};

/// Contains states needed for the building of a MIR function.
/// User of the builder is expected to call `MirFuncBuilder::new` to construct this builder, and
/// and then feed it with AST nodes by calling `MirFuncBuilder::next_stmt`, and then call
/// `MirFuncBuilder::finish` to finally yield the built `MirFunction`.
/// The builder uses the `convert_*` functions to recursively visits through the AST to build the
/// MIR. These functions are not meant to be called from outside.
/// The `convert_*` functions return `None` on syntax error or unreachable code, or `Some(value)`
/// for the result value of the expression. In some cases the value is always the same, such as a
/// `let` expression always returns void, but `convert_let` is still in the same format as other
/// `convert_*` functions.
#[derive(Debug, Clone)]
struct MirFuncBuilder<'g> {
    /// The global context
    global: &'g GlobalContext,

    /// The func info from the global context
    func_info: &'g FuncInfo,

    /// The MIR function this builder is constructing
    function: MirFunction,

    /// The source location of the function, used for reporting missing returns
    source_loc: SourceLocation,

    /// A "cursor" pointing at the current block that the builder is writing to.
    /// Avoid directly indexing `self.function.blocks`, always use `add_stmt` and `set_term` for
    /// writing to the current block. This is to ensure that:
    ///     1. Existing `StatementRef`s are still valid
    ///     2. If a block is early-terminated, `add_stmt` and `set_term` won't actually do anything
    current_block: BlockRef,

    /// Map local variable names to variable ID's, uses a stack structure for entering and exiting
    /// AST blocks.
    /// If a variable is shadowed then it's overwritten.
    locals: Vec<HashMap<&'static str, Variable>>,
}

impl<'g> MirFuncBuilder<'g> {
    /// Initialize the builder
    fn new(global: &'g GlobalContext, func_idx: FuncIndex, source_loc: SourceLocation) -> Self {
        let func_info = &global.funcs[func_idx];
        let sig = &func_info.sig;
        let mut vars = IndexVec::<Variable, VarInfo>::with_capacity(sig.args.len());
        let mut locals = Vec::<HashMap<&'static str, Variable>>::new();
        locals.push(HashMap::new());
        for (arg_name, arg_ty) in &sig.args {
            let var_info = VarInfo {
                is_mut: true,
                is_arg: true,
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
            func_info,
            function: MirFunction {
                vars,
                blocks: IndexVec::from_iter([Block::default()]),
            },
            source_loc,
            current_block: BlockRef(0),
            locals,
        }
    }

    fn finish(mut self) -> MirFunction {
        // return check
        match (
            self.current_block().terminator.is_some(),
            self.func_info.sig.ret_type.is_void(),
        ) {
            (true, _) => self.function,
            (false, true) => {
                self.set_term(Terminator::Return(Value::Void));
                self.function
            }
            (false, false) => {
                self.set_term(Terminator::Unreachable);
                ErrorContent::MissingReturn
                    .wrap(self.source_loc)
                    .collect_into(&self.global.err_collector);
                self.function
            }
        }
    }

    /// Feed the builder with the next statement inside the function
    fn next_stmt(&mut self, node: &Traced<AstNode>) {
        self.convert_stmt(node);
    }

    fn convert_stmt(&mut self, node: &Traced<AstNode>) -> Option<Value> {
        let val = self.convert_expr(node)?;
        if val.is_unreachable() {
            return Some(Value::Unreachable);
        }
        if !self.deduce_val_ty(&val).map_or(true, |t| t.is_trivial()) {
            ErrorContent::UnusedValue
                .wrap(node.src_loc())
                .collect_into(&self.global.err_collector);
            self.set_term(Terminator::Unreachable);
            return None;
        }
        Some(Value::Void)
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
            AstNode::Field(parent, child) => self.convert_field(&parent, &child),
            AstNode::BitNot(_) => todo!(),
            AstNode::BoolNot(_) => todo!(),
            AstNode::UnarySub(_) => todo!(),
            AstNode::UnaryAdd(_) => todo!(),
            AstNode::Call(callee, args) => self.convert_call(&callee, &args),
            AstNode::Let(lhs, ty, rhs) => self.convert_let(lhs, ty.as_ref(), *rhs),
            AstNode::Assign(lhs, rhs) => self.convert_assign(&lhs, &rhs),
            AstNode::MathOpAssign(_, _, _) => todo!(),
            AstNode::BitOpAssign(_, _, _) => todo!(),
            &AstNode::Ref(mutability, node) => self.convert_ref(mutability, &node),
            AstNode::Deref(node) => self.convert_deref(&node),
            AstNode::Block(_) => todo!(),
            AstNode::FnDef(_) => todo!(),
            AstNode::If(if_expr) => self.convert_if(if_expr, node.src_loc()),
            AstNode::Loop(_) => todo!(),
            AstNode::Return(child) => self.convert_return(child.as_deref(), node.src_loc()),
            AstNode::Break => todo!(),
            AstNode::Continue => todo!(),
            AstNode::Tail(child) => {
                let val = self.convert_expr(&child);
                match val {
                    Some(Value::Void | Value::Unreachable) | None => val,
                    _ => {
                        ErrorContent::Todo("tails (try adding a semicolon at the end")
                            .wrap(node.src_loc())
                            .collect_into(&self.global.err_collector);
                        self.set_term(Terminator::Unreachable);
                        None
                    }
                }
            }
            AstNode::Typecast(_, _) => todo!(),
            AstNode::TypeDef(_, _) => todo!(),
            AstNode::StructDef(_) => todo!(),
            AstNode::UnionDef(_) => todo!(),
            AstNode::EnumDef(_) => todo!(),
            AstNode::Tuple(_) => todo!(),
        }
    }

    fn convert_field(
        &mut self,
        parent: &Traced<AstNode>,
        child: &Traced<AstNode>,
    ) -> Option<Value> {
        let mut place = match self.convert_expr(parent) {
            Some(Value::Copy(place) | Value::Ref(_, place)) => place,
            None | Some(..) => {
                ErrorContent::InvalidField
                    .wrap(child.src_loc())
                    .collect_into(&self.global.err_collector);
                self.set_term(Terminator::Unreachable);
                return None;
            }
        };
        let field = child
            .as_identifier()
            .ok_or(ErrorContent::InvalidFieldSyntax.wrap(child.src_loc()))
            .collect_err(&self.global.err_collector)?;
        place.projections.push(ProjectionEle::Field(field));
        Some(Value::Copy(place))
    }

    /// Returns the value of the variable that the call results are stored in
    fn convert_call(&mut self, callee: &Traced<AstNode>, args: &[AstNodeRef]) -> Option<Value> {
        let func_name = callee
            .as_identifier()
            .ok_or(ErrorContent::Todo("Indirect function calls").wrap(callee.src_loc()))
            .collect_err(&self.global.err_collector)?;
        let (func_idx, func_info) = self
            .global
            .func(func_name)
            .ok_or(ErrorContent::FuncNotExist(func_name).wrap(callee.src_loc()))
            .collect_err(&self.global.err_collector)?;
        let func_sig = &func_info.sig;
        let mut arg_vals = Vec::<Value>::with_capacity(args.len());
        let result_var = self.make_temp_var(func_sig.ret_type.clone());
        let result_place = Place::no_projection(result_var);

        // check arguments count
        if args.len() != func_sig.args.len() {
            ErrorContent::MismatchedArgsCount(Some(func_name), func_sig.args.len(), args.len())
                .wrap(callee.src_loc())
                .collect_into(&self.global.err_collector);
            self.set_term(Terminator::Unreachable);
            // still dry runs builder on argument nodes
            for arg in args {
                let arg_val = self.convert_expr(&arg)?;
                arg_vals.push(arg_val);
            }
            return None;
        }

        for (i, arg) in args.iter().enumerate() {
            let arg = arg.deref();
            let expect_ty = unsafe { &func_sig.args.get_unchecked(i).1 };
            let arg_val = self.convert_expr(arg)?;
            if !self.typecheck_covary_ty_val(expect_ty, &arg_val, arg.src_loc()) {
                self.set_term(Terminator::Unreachable);
            }
            arg_vals.push(arg_val);
        }

        let call_stmt = Statement::StaticCall {
            func_idx,
            args: arg_vals,
            result: result_place.clone(),
        };
        self.add_stmt(call_stmt);
        Some(Value::Copy(result_place))
    }

    fn convert_let(
        &mut self,
        lhs: &Traced<Pattern>,
        ty: Option<&TypeExpr>,
        rhs: Option<AstNodeRef>,
    ) -> Option<Value> {
        let (mutability, name) = match lhs.inner() {
            Pattern::Var(m, n) => (m, n),
            Pattern::Tuple(..) => todo!(),
        };

        let var_info = VarInfo {
            is_mut: mutability.is_mut(),
            is_arg: false,
            ty: ty.cloned().unwrap_or(TypeExpr::_Unknown),
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

        let rhs = rhs.as_deref()?;
        let rhs_val = self.convert_expr(rhs)?;
        match ty {
            None => {
                let infered = self
                    .deduce_val_ty(&rhs_val)
                    .ok_or(ErrorContent::TypeInferFailed.wrap(lhs.src_loc()))
                    .collect_err(&self.global.err_collector)?
                    .into_owned();
                if !infered.is_concrete() {
                    ErrorContent::Todo("Partial type infer")
                        .wrap(lhs.src_loc())
                        .collect_into(&self.global.err_collector);
                    self.set_term(Terminator::Unreachable);
                }
                self.function.vars[var].ty = infered;
            }
            Some(ty) => {
                if !self.typecheck_covary_ty_val(ty, &rhs_val, rhs.src_loc()) {
                    self.set_term(Terminator::Unreachable);
                }
            }
        }

        self.add_stmt(Statement::Assign(Place::no_projection(var), rhs_val));

        Some(Value::Void)
    }

    fn convert_assign(&mut self, lhs: &Traced<AstNode>, rhs: &Traced<AstNode>) -> Option<Value> {
        let lhs_val = self.convert_expr(lhs)?;
        let rhs_val = self.convert_expr(&rhs)?;
        let lhs_place = match lhs_val {
            Value::Copy(place) => {
                // type check
                let (lhs_ty, lhs_mutable) = self.deduce_place_ty(&place)?;
                if !self.typecheck_covary_ty_val(lhs_ty, &rhs_val, rhs.src_loc()) {
                    self.set_term(Terminator::Unreachable);
                }
                if lhs_mutable.is_const() {
                    ErrorContent::AssignToImmut
                        .wrap(lhs.src_loc())
                        .collect_into(&self.global.err_collector);
                }
                place
            }
            _ => {
                ErrorContent::InvalidAssignLHS
                    .wrap(lhs.src_loc())
                    .collect_into(&self.global.err_collector);
                return None;
            }
        };
        self.add_stmt(Statement::Assign(lhs_place, rhs_val));
        Some(Value::Void)
    }

    fn convert_return(
        &mut self,
        child: Option<&Traced<AstNode>>,
        return_loc: SourceLocation,
    ) -> Option<Value> {
        let child = match child {
            Some(x) => x,
            None => {
                if !self.func_info.sig.ret_type.is_void() {
                    ErrorContent::MismatchdTypes(
                        self.func_info.sig.ret_type.clone(),
                        TypeExpr::void(),
                    )
                    .wrap(return_loc)
                    .collect_into(&self.global.err_collector);
                    return None;
                }
                self.set_term(Terminator::Return(Value::Void));
                return None;
            }
        };
        let val = self.convert_expr(child)?;
        // type check the return value
        {
            let loc = child.src_loc();
            let found_ty = self
                .deduce_val_ty(&val)
                .unwrap_or(Cow::Owned(TypeExpr::_Unknown));
            if !typecheck::type_matches(self.global, &self.func_info.sig.ret_type, &found_ty) {
                ErrorContent::MismatchdTypes(
                    self.func_info.sig.ret_type.clone(),
                    found_ty.into_owned(),
                )
                .wrap(loc)
                .collect_into(&self.global.err_collector);
                self.set_term(Terminator::Unreachable);
            }
        }
        self.set_term(Terminator::Return(val));
        return Some(Value::Unreachable);
    }

    fn convert_ref(&mut self, mutability: Mutability, node: &Traced<AstNode>) -> Option<Value> {
        let val = self.convert_expr(node)?;
        match val {
            Value::Copy(place) => Some(Value::Ref(mutability, place)),
            val => {
                let ty = self.deduce_val_ty(&val).unwrap().into_owned();
                let temp_var = self.make_temp_var(ty);
                let temp_var_place = Place::no_projection(temp_var);
                self.add_stmt(Statement::Assign(temp_var_place.clone(), val));
                Some(Value::Ref(mutability, temp_var_place))
            }
        }
    }

    fn convert_deref(&mut self, node: &Traced<AstNode>) -> Option<Value> {
        let val = self.convert_expr(node)?;
        let place = match val {
            Value::Copy(mut place) => {
                let ty = self.deduce_place_ty(&place).map(|(ty, _)| ty);
                if let Some(TypeExpr::Ref(_, ty) | TypeExpr::Ptr(_, ty)) = ty {
                    place
                        .projections
                        .push(ProjectionEle::Deref(ty.deref().clone()));
                    place
                } else {
                    ErrorContent::InvalidDeref
                        .wrap(node.src_loc())
                        .collect_into(&self.global.err_collector);
                    return None;
                }
            }
            Value::Ref(_, place) => place,
            _ => {
                ErrorContent::InvalidDeref
                    .wrap(node.src_loc())
                    .collect_into(&self.global.err_collector);
                return None;
            }
        };
        Some(Value::Copy(place))
    }

    fn convert_if(&mut self, if_expr: &IfExpr, _src_loc: SourceLocation) -> Option<Value> {
        let mut branches = Vec::<BlockRef>::with_capacity(if_expr.if_blocks.len() + 1);
        let mut diverging_count = 0usize;
        let mut prev_otherwise = self.current_block;
        for (cond_node, body) in &if_expr.if_blocks {
            let cond = self
                .if_condition(&cond_node)
                .unwrap_or(Condition::if_true(Value::Unreachable));
            let target = self.new_block();
            let otherwise = self.new_block();
            self.switch_to_block(prev_otherwise);
            self.set_term(Terminator::CondJmp {
                cond,
                target,
                otherwise,
            });

            self.switch_to_block(target);
            for stmt in body {
                if self
                    .convert_stmt(&stmt)
                    .map_or(true, |val| val.is_unreachable())
                {
                    diverging_count += 1;
                };
            }

            branches.push(target);
            prev_otherwise = otherwise;
        }
        let merged_block = match &if_expr.else_block {
            Some(body) => {
                self.switch_to_block(prev_otherwise);
                for stmt in body {
                    if self
                        .convert_stmt(&stmt)
                        .map_or(true, |val| val.is_unreachable())
                    {
                        diverging_count += 1;
                    };
                }
                branches.push(prev_otherwise);
                self.new_block()
            }
            None => prev_otherwise,
        };
        let branch_count = branches.len();
        for branch in branches {
            self.set_term_for_block(branch, Terminator::Jmp(merged_block));
        }
        self.switch_to_block(merged_block);
        if diverging_count == branch_count && if_expr.else_block.is_some() {
            self.function.blocks[merged_block].terminator = Some(Terminator::Unreachable);
            None
        } else {
            Some(Value::Void) // TODO: block tails
        }
    }

    /// Translates the if condition to an MIR condition
    fn if_condition(&mut self, cond_node: &Traced<AstNode>) -> Option<Condition> {
        let (cond_kind, val) = match cond_node.deref() {
            AstNode::BoolNot(node) => (CondKind::IfFalse, self.convert_expr(node)?),
            _ => (CondKind::IfTrue, self.convert_expr(cond_node)?),
        };
        if !self.typecheck_covary_ty_val(&TypeExpr::Bool, &val, cond_node.src_loc()) {
            self.set_term(Terminator::Unreachable)
        }
        Some(Condition::new(cond_kind, val))
    }

    /// Deduce the type of a `Value`, returns `None` if there is a type error (does not report the
    /// type error)
    fn deduce_val_ty<'a>(&'a self, val: &'a Value) -> Option<Cow<'a, TypeExpr>> {
        match val {
            Value::Number(ty, _) => Some(Cow::Borrowed(ty)),
            Value::Bool(..) => Some(Cow::Owned(TypeExpr::Bool)),
            Value::Char(..) => Some(Cow::Owned(TypeExpr::Char)),
            Value::Copy(place) => self.deduce_place_ty(place).map(|x| Cow::Borrowed(x.0)),
            Value::Ref(mutability, place) => {
                let t = self.deduce_place_ty(place)?.0.clone();
                Some(Cow::Owned(TypeExpr::Ref(*mutability, Box::new(t))))
            }
            Value::Void => Some(Cow::Owned(TypeExpr::void())),
            Value::Unreachable => Some(Cow::Owned(TypeExpr::Never)),
        }
    }

    /// Deduce the type and mutability of a `Place`, returns `None` if there is a type error (does
    /// not report the type error)
    fn deduce_place_ty<'a>(&'a self, place: &'a Place) -> Option<(&'a TypeExpr, Mutability)> {
        let var_info = &self.function.vars[place.local];
        let mut ty = &var_info.ty;
        let mut is_mut = var_info.is_mut;
        for proj in &place.projections {
            match proj {
                ProjectionEle::Deref(target_ty) => {
                    is_mut = match ty {
                        TypeExpr::Ref(m, _) | TypeExpr::Ptr(m, _) => m.is_mut(),
                        _ => return None,
                    };
                    ty = target_ty;
                }
                ProjectionEle::Index(_) => todo!(),
                &ProjectionEle::Field(field) => {
                    ty = match ty {
                        TypeExpr::Tuple(fields) => {
                            let idx = mir::TUPLE_FIELDS_LABELS
                                .iter()
                                .enumerate()
                                .find(|(_, &s)| field == s)?
                                .0;
                            fields.get(idx)?
                        }
                        _ => return None,
                    };
                }
            }
        }
        Some((
            ty,
            if is_mut {
                Mutability::Mutable
            } else {
                Mutability::Const
            },
        ))
    }

    /// Creates a unnamed, immutable variable, with a given type
    fn make_temp_var(&mut self, ty: TypeExpr) -> Variable {
        self.function.vars.push(VarInfo {
            is_mut: false,
            is_arg: false,
            ty,
            name: None,
        })
    }

    /// Add a statement to the current block
    fn add_stmt(&mut self, stmt: Statement) {
        let i = self.current_block;
        let current_block = &mut self.function.blocks[i];
        if current_block.terminator.is_none() {
            let _ = current_block.body.push(stmt);
        }
    }

    /// Set the terminator for the current block
    fn set_term(&mut self, term: Terminator) {
        let i = self.current_block;
        let current_block = &mut self.function.blocks[i];
        if current_block.terminator.is_none() {
            current_block.terminator = Some(term);
        }
    }

    /// Set the terminator for a specified block if it's not already set
    fn set_term_for_block(&mut self, blockr: BlockRef, term: Terminator) {
        let block = &mut self.function.blocks[blockr];
        if block.terminator.is_none() {
            block.terminator = Some(term);
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

    /// For creating a block which has only one predecessor of the current block, use
    /// `new_block_owned_by_current`
    fn new_block(&mut self) -> BlockRef {
        let block = Block::default();
        self.function.blocks.push(block)
    }

    /// Creates a new block which has only one predecessor which is the current block.
    /// If the current block is already unreachable then it propagates to this new block.
    fn _new_block_owned_by_current(&mut self) -> BlockRef {
        let mut block = Block::default();
        if self.current_block().terminator.is_some() {
            block.terminator = Some(Terminator::Unreachable);
        }
        self.function.blocks.push(block)
    }

    fn switch_to_block(&mut self, block: BlockRef) {
        self.current_block = block;
    }

    /// Get an immutable reference to the current block.
    fn current_block(&self) -> &Block {
        let i = self.current_block;
        &self.function.blocks[i]
    }

    /// Performs a co-variant type check.
    /// Generates and reports the error if needed.
    /// Returns false if typecheck not passed
    fn typecheck_covary_ty_val(
        &self,
        expect: &TypeExpr,
        found: &Value,
        loc: SourceLocation,
    ) -> bool {
        let found = self
            .deduce_val_ty(found)
            .unwrap_or(Cow::Owned(TypeExpr::_Unknown));
        if !typecheck::type_matches(self.global, expect, &found) {
            ErrorContent::MismatchdTypes(expect.clone(), found.into_owned())
                .wrap(loc)
                .collect_into(&self.global.err_collector);
            false
        } else {
            true
        }
    }
}

pub fn make_mir<'g>(global: &'g GlobalContext) -> MirObject {
    let mut mir_object = MirObject::default();
    for (func_index, func_info) in global.funcs.iter_enumerated() {
        let root_node = func_info.ast_node.deref();
        let ast_func = root_node.as_fn_def().unwrap();
        let mut builder = MirFuncBuilder::new(global, func_index, root_node.src_loc());
        let body = ast_func
            .body
            .as_ref()
            .unwrap_or_else(|| panic!("TODO: extern functions"));
        for node in body {
            builder.next_stmt(&node);
        }
        mir_object.functions.push(builder.finish());
    }
    mir_object
}
