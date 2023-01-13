pub mod translator;

use std::{collections::HashMap, fmt::Debug, ops::Deref};

pub(self) use cranelift::codegen::ir::{types as cl_types, types::Type as ClType};

use crate::{ast::type_expr::TypeExpr, error::ErrorContent};

use translator::basic_asttype_to_cltype;

/// - ADT expanded into multiple variables with basic types
/// - Non-direction expressions as function arguments are flattened
/// - If statements are split and flattened
/// - Loops and if statements are marked with block ID
/// - Variables are turned into ID
/// - Boolean logic operators and bitwise operators are no longer differentiated
/// - All typedefs are gone
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum MirNode<'s> {
    Identifier(&'s str),
    Number(&'s str),
    String(Vec<u8>),
    Char(char),
    Bool(bool),
    Array(Vec<u8>),

    VarDef(u64, ClType),
    VarAssign(u64, MirNodeRef<'s>),
    FnCall(&'s str, Vec<MirNodeRef<'s>>),

    Add(MirNodeRef<'s>, MirNodeRef<'s>),
    Sub(MirNodeRef<'s>, MirNodeRef<'s>),
    Mul(MirNodeRef<'s>, MirNodeRef<'s>),
    Div(MirNodeRef<'s>, MirNodeRef<'s>),
    Mod(MirNodeRef<'s>, MirNodeRef<'s>),
    Not(MirNodeRef<'s>, MirNodeRef<'s>),
    And(MirNodeRef<'s>, MirNodeRef<'s>),
    Or(MirNodeRef<'s>, MirNodeRef<'s>),
    Xor(MirNodeRef<'s>, MirNodeRef<'s>),

    Loop(MirLoop<'s>),
    IfThenBreak(MirNodeRef<'s>, u64),
    IfThenContinue(MirNodeRef<'s>, u64),
    If(MirIf<'s>),
    Block(Vec<MirNodeRef<'s>>),

    Break(u64),
    Continue(u64),
    RetVal(MirNodeRef<'s>),
    RetVoid(MirNodeRef<'s>),

    FnDef(MirFnDef<'s>),
    StaticVar(&'s str, MirNodeRef<'s>),
}

/// A loop statement in MIR
#[derive(Debug, Clone)]
pub struct MirLoop<'s> {
    pub block_id: u64,
    pub body: Vec<MirNodeRef<'s>>,
}

/// An if statement in MIR
#[derive(Debug, Clone)]
pub struct MirIf<'s> {
    pub id: u64,
    pub condition: MirNodeRef<'s>,
    pub body: Vec<MirNodeRef<'s>>,
    pub else_block: Option<u64>,
}

/// A function definition in MIR
#[derive(Debug, Clone)]
pub struct MirFnDef<'s> {
    pub name: &'s str,
    pub args: Vec<ClType>,
    pub ret_type: Option<ClType>,
    pub body: MirBlock<'s>,
}

/// An array of MIR nodes, with a header containing information about all the variables defined in
/// this block
#[derive(Debug, Clone, Default)]
pub struct MirBlock<'s> {
    pub body: Vec<MirNodeRef<'s>>,
    /// Information of the variables defined in this block
    pub vars: HashMap<&'s str, MirVarInfo<'s>>,
}

impl<'s> MirBlock<'s> {
    /// Execute a closure for each of the sub var ID in a dot path
    pub fn for_each_id<P: Iterator<Item = &'s str>, F: FnMut(u64, ClType)>(
        &self,
        mut path: P,
        mut f: F,
    ) -> Result<(), ErrorContent<'s>> {
        todo!()
        //fn recursive<'s>(
        //    vars: &HashMap<&'s str, MirVarInfo<'s>>,
        //    current_id: u64,
        //    current_name: &'s str,
        //    current_type: &'s TypeExpr,
        //    path: &mut impl Iterator<Item = &'s str>,
        //    f: &mut impl FnMut(u64, ClType),
        //) -> Result<(), ErrorContent<'s>> {
        //    if let Some(cl_ty) = basic_asttype_to_cltype(var_info.dtype.root(), &var_info.dtype) {
        //        f(current_id, cl_ty);
        //    } else {
        //        use crate::ast::type_expr::TypeExprNode::*;
        //        match current_type.root() {
        //            Slice(_) => {
        //                f(current_id, cl_types::I64);
        //                f(current_id + 1, cl_types::R64);
        //            }
        //            Array(_, _) => todo!("freeform array"),
        //            Tuple(children) => match path.next() {
        //                Some(node) => todo!(),
        //                None => {
        //                    for (i, &child) in children.iter().enumerate() {
        //                        let child = &current_type.pool[child];
        //                        recursive(
        //                            vars,
        //                            current_id + (i as u64),
        //                            child,
        //                            translator::TUPLE_PATHS[i],
        //                            path,
        //                            f,
        //                        )?;
        //                    }
        //                }
        //            },
        //            Fn(_, _) => todo!(),
        //            TypeName(_) => todo!(),
        //            Struct => todo!(),
        //            Union => todo!(),
        //            Enum => todo!(),
        //            _ => unimplemented!(), // already covered by `basic_asttype_to_cltype`
        //        }
        //    }
        //    Ok(())
        //}

        //let root_name = path.next().ok_or(ErrorContent::InvalidMemberAccess)?;
        //let root_id = self
        //    .vars
        //    .get(root_name)
        //    .ok_or(ErrorContent::InvalidMemberAccess)?
        //    .id;
        //recursive(&self.vars, root_id, root_name, &mut path, &mut f)?;
        //Ok(())
    }
}

/// Stores information about a variable
#[derive(Debug, Clone)]
pub struct MirVarInfo<'s> {
    pub id: u64,
    pub dtype: TypeExpr<'s>,
    pub is_mut: bool,
}

impl<'s> From<(u64, TypeExpr<'s>, bool)> for MirVarInfo<'s> {
    fn from((id, dtype, is_mut): (u64, TypeExpr<'s>, bool)) -> Self {
        Self { id, dtype, is_mut }
    }
}

/// A program in MIR
#[derive(Debug, Clone, Default)]
pub struct MirProgram<'s> {
    node_pool: Box<Vec<MirNode<'s>>>,
    pub root_nodes: Vec<MirNodeRef<'s>>,
}

impl<'s> MirProgram<'s> {
    pub fn add_node(&mut self, node: MirNode<'s>) -> MirNodeRef<'s> {
        self.node_pool.push(node);
        let i = self.node_pool.len() - 1;
        MirNodeRef {
            pool: self.node_pool.deref() as *const Vec<MirNode<'s>>,
            i,
        }
    }
}

#[derive(Clone)]
pub struct MirNodeRef<'s> {
    pool: *const Vec<MirNode<'s>>,
    i: usize,
}

impl<'s> Deref for MirNodeRef<'s> {
    type Target = MirNode<'s>;

    fn deref(&self) -> &Self::Target {
        unsafe { (*self.pool).get_unchecked(self.i) }
    }
}

impl Debug for MirNodeRef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.deref().fmt(f)
    }
}
