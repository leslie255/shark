use std::{borrow::Cow, collections::HashMap, ops::Deref};

use index_vec::IndexVec;

use crate::{
    ast::{
        type_expr::{NumericType, TypeExpr},
        Ast, AstNode, AstNodeRef, IfExpr, Signature,
    },
    error::{
        location::{SourceLocation, Traced},
        CollectIfErr, ErrorContent,
    },
    gen::GlobalContext,
    token::NumValue,
};

use super::{
    typecheck, Block, BlockRef, Condition, MirFunction, MirObject, Place, ProjectionEle, Statement,
    Terminator, Value, VarInfo, Variable,
};

/// Contains states needed for the building of a MIR function.
/// User of the builder is expected to call `MirFuncBuilder::make_signature` to construct this
/// builder, and then feed it with AST nodes by calling `MirFuncBuilder::next_stmt`, and then call
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

    /// The MIR function this builder is constructing
    function: MirFunction,

    /// The source location of the function, used for reporting missing returns
    source_loc: SourceLocation,

    /// Return type of the function
    ret_ty: TypeExpr,

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
    fn make_signature(
        global: &'g GlobalContext,
        sign: &Signature,
        source_loc: SourceLocation,
    ) -> Self {
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
            source_loc,
            current_block: BlockRef(0),
            ret_ty: sign.ret_type.clone(),
            locals,
        }
    }

    fn finish(mut self) -> MirFunction {
        // return check
        match (
            self.current_block().terminator.is_some(),
            self.ret_ty.is_void(),
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
            AstNode::MemberAccess(_, _) => todo!(),
            AstNode::BitNot(_) => todo!(),
            AstNode::BoolNot(_) => todo!(),
            AstNode::UnarySub(_) => todo!(),
            AstNode::UnaryAdd(_) => todo!(),
            AstNode::Call(callee, args) => self.convert_call(&callee, &args),
            AstNode::Let(lhs, ty, rhs) => self.convert_let(*lhs, ty.as_ref(), *rhs),
            AstNode::Assign(lhs, rhs) => self.convert_assign(&lhs, &rhs),
            AstNode::MathOpAssign(_, _, _) => todo!(),
            AstNode::BitOpAssign(_, _, _) => todo!(),
            AstNode::Ref(node) => self.convert_ref(&node),
            AstNode::Deref(node) => self.convert_deref(&node),
            AstNode::Block(_) => todo!(),
            AstNode::FnDef(_) => todo!(),
            AstNode::If(if_expr) => self.convert_if(if_expr, node.src_loc()),
            AstNode::Loop(_) => todo!(),
            AstNode::Return(child) => self.convert_return(child.as_deref(), node.src_loc()),
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

    /// Returns the value of the variable that the call results are stored in
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
            self.typecheck_covary(expect_ty, &arg_val, arg.src_loc());
            arg_vals.push(arg_val);
        }

        let call_stmt = Statement::StaticCall {
            func_name,
            args: arg_vals,
            result: result_place.clone(),
        };
        self.add_stmt(call_stmt);
        Some(Value::Copy(result_place))
    }

    fn convert_let(
        &mut self,
        lhs: AstNodeRef,
        ty: Option<&TypeExpr>,
        rhs: Option<AstNodeRef>,
    ) -> Option<Value> {
        let name = lhs
            .as_identifier()
            .unwrap_or_else(|| todo!("pattern matched `let`"));

        let var_info = VarInfo {
            is_mut: true,
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
                self.typecheck_covary(ty, &rhs_val, rhs.src_loc());
            }
        }

        self.add_stmt(Statement::Assign(Place::no_projection(var), rhs_val));

        Some(Value::Void)
    }

    fn convert_assign(&mut self, lhs: &Traced<AstNode>, rhs: &Traced<AstNode>) -> Option<Value> {
        let lhs_val = self.convert_expr(lhs)?;
        let rhs_val = self.convert_expr(&rhs)?;
        self.typecheck_covary_val_val(&lhs_val, &rhs_val, rhs.src_loc());
        let lhs_place = match lhs_val {
            Value::Copy(place) => place,
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
                if !self.ret_ty.is_void() {
                    ErrorContent::MismatchdTypes(self.ret_ty.clone(), TypeExpr::void())
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
            if !typecheck::type_matches(self.global, &self.ret_ty, &found_ty) {
                ErrorContent::MismatchdTypes((&self.ret_ty).clone(), found_ty.into_owned())
                    .wrap(loc)
                    .collect_into(&self.global.err_collector);
                self.set_term(Terminator::Unreachable);
            }
        }
        self.set_term(Terminator::Return(val));
        return None;
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

    fn convert_if(&mut self, if_expr: &IfExpr, _src_loc: SourceLocation) -> Option<Value> {
        let mut branches = Vec::<BlockRef>::with_capacity(if_expr.if_blocks.len() + 1);
        let mut prev_otherwise = self.current_block;
        for (cond_node, body) in &if_expr.if_blocks {
            let cond = self
                .if_condition(&cond_node)
                .unwrap_or(Condition::if_true(Value::Unreachable));
            let target = self.new_block_owned_by_current();
            let otherwise = self.new_block_owned_by_current();
            self.switch_to_block(prev_otherwise);
            self.set_term(Terminator::CondJmp {
                cond,
                target,
                otherwise,
            });

            self.switch_to_block(target);
            for stmt in body {
                self.convert_stmt(&stmt);
            }

            branches.push(target);
            prev_otherwise = otherwise;
        }
        let merged_block = match &if_expr.else_block {
            Some(body) => {
                self.switch_to_block(prev_otherwise);
                for stmt in body {
                    self.convert_stmt(&stmt);
                }
                branches.push(prev_otherwise);
                self.new_block()
            }
            None => prev_otherwise,
        };
        for branch in branches {
            self.set_term_for_block(branch, Terminator::Jmp(merged_block));
        }
        self.switch_to_block(merged_block);
        Some(Value::Void) // TODO: block tails
    }

    /// Translates the if condition to an MIR condition
    fn if_condition(&mut self, cond_node: &Traced<AstNode>) -> Option<Condition> {
        match cond_node.deref() {
            AstNode::BoolNot(node) => {
                let val = self.convert_expr(&node)?;
                Some(Condition::if_false(val))
            }
            _ => {
                let val = self.convert_expr(cond_node)?;
                Some(Condition::if_true(val))
            }
        }
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
    fn new_block_owned_by_current(&mut self) -> BlockRef {
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
    /// Terminates the current block if type check not passed.
    fn typecheck_covary(&mut self, expect: &TypeExpr, found: &Value, loc: SourceLocation) {
        let found = self
            .deduce_val_ty(found)
            .unwrap_or(Cow::Owned(TypeExpr::_Unknown));
        if !typecheck::type_matches(self.global, expect, &found) {
            ErrorContent::MismatchdTypes(expect.clone(), found.into_owned())
                .wrap(loc)
                .collect_into(&self.global.err_collector);
            self.set_term(Terminator::Unreachable);
        }
    }

    /// Performs a co-variant type check between two values.
    /// Generates and reports the error if needed.
    /// Terminates the current block if type check not passed.
    fn typecheck_covary_val_val(&mut self, expect: &Value, found: &Value, loc: SourceLocation) {
        let expect = self
            .deduce_val_ty(expect)
            .unwrap_or(Cow::Owned(TypeExpr::_Unknown));
        let expect: &TypeExpr = &expect;
        let found = found;
        let found = self
            .deduce_val_ty(found)
            .unwrap_or(Cow::Owned(TypeExpr::_Unknown));
        if !typecheck::type_matches(self.global, expect, &found) {
            ErrorContent::MismatchdTypes(expect.clone(), found.into_owned())
                .wrap(loc)
                .collect_into(&self.global.err_collector);
            self.set_term(Terminator::Unreachable);
        };
    }
}

pub fn make_mir<'g>(global: &'g GlobalContext, ast: &'g Ast) -> MirObject {
    let mut mir_object = MirObject::default();
    for root_node in &ast.root_nodes {
        let root_node = root_node.deref();
        match root_node.inner() {
            AstNode::FnDef(ast_func) => match &ast_func.body {
                Some(body) => {
                    let mut builder =
                        MirFuncBuilder::make_signature(global, &ast_func.sign, root_node.src_loc());
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
