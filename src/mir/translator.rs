use std::{collections::HashMap, ops::Deref};

use crate::{
    ast::{
        type_expr::{TypeExpr, TypeExprNode},
        Ast, AstNode, FnDef,
    },
    checks::symboltable::{PossibleTypes, SymbolTable},
};

use super::{cl_types, ClType, MirBlock, MirFnDef, MirNode, MirNodeRef, MirProgram, MirVarInfo};

fn basic_asttype_to_cltype<'s>(node: &TypeExprNode<'s>, pool: &TypeExpr<'s>) -> Option<ClType> {
    use TypeExprNode::*;
    match node {
        U128 | I128 => Some(cl_types::I128),
        USize | ISize | U64 | I64 => Some(cl_types::I64),
        U32 | I32 | Char => Some(cl_types::I32),
        U16 | I16 => Some(cl_types::I16),
        U8 | I8 | Bool => Some(cl_types::I8),
        F64 => Some(cl_types::F64),
        F32 => Some(cl_types::F32),
        Ptr(_) | Ref(_) => Some(cl_types::R64),
        &Array(1, t) => basic_asttype_to_cltype(&pool.pool[t], pool),
        &Array(2, t) => basic_asttype_to_cltype(&pool.pool[t], pool).map_or(None, |t| match t {
            cl_types::I32 => Some(cl_types::I32X2),
            cl_types::I64 => Some(cl_types::I64X2),
            cl_types::I128 => Some(cl_types::I128X2),
            cl_types::F32 => Some(cl_types::F32X2),
            cl_types::F64 => Some(cl_types::F64X2),
            _ => None,
        }),
        &Array(4, t) => basic_asttype_to_cltype(&pool.pool[t], pool).map_or(None, |t| match t {
            cl_types::I16 => Some(cl_types::I16X4),
            cl_types::I32 => Some(cl_types::I32X4),
            cl_types::I64 => Some(cl_types::I64X4),
            cl_types::I128 => Some(cl_types::I128X4),
            cl_types::F32 => Some(cl_types::F32X4),
            cl_types::F64 => Some(cl_types::F64X4),
            _ => None,
        }),
        &Array(8, t) => basic_asttype_to_cltype(&pool.pool[t], pool).map_or(None, |t| match t {
            cl_types::I8 => Some(cl_types::I8X8),
            cl_types::I16 => Some(cl_types::I16X8),
            cl_types::I32 => Some(cl_types::I32X8),
            cl_types::I64 => Some(cl_types::I64X8),
            cl_types::F32 => Some(cl_types::F32X8),
            cl_types::F64 => Some(cl_types::F64X8),
            _ => None,
        }),
        &Array(16, t) => basic_asttype_to_cltype(&pool.pool[t], pool).map_or(None, |t| match t {
            cl_types::I8 => Some(cl_types::I8X16),
            cl_types::I16 => Some(cl_types::I16X16),
            cl_types::I32 => Some(cl_types::I32X16),
            cl_types::F32 => Some(cl_types::F32X16),
            _ => None,
        }),
        &Array(32, t) => basic_asttype_to_cltype(&pool.pool[t], pool).map_or(None, |t| match t {
            cl_types::I8 => Some(cl_types::I8X32),
            cl_types::I16 => Some(cl_types::I16X32),
            _ => None,
        }),
        &Array(64, t) => basic_asttype_to_cltype(&pool.pool[t], pool).map_or(None, |t| match t {
            cl_types::I8 => Some(cl_types::I8X64),
            _ => None,
        }),
        Slice(_) | Array(_, _) | Tuple(_) | Fn(_, _) | TypeName(_) | Struct | Union | Enum => None,
    }
}

static TUPLE_PATHS: [&'static str; 32] = [
    "_0", "_1", "_2", "_3", "_4", "_5", "_6", "_7", "_8", "_9", "_10", "_11", "_12", "_13", "_14",
    "_15", "_16", "_17", "_18", "_19", "_20", "_21", "_22", "_23", "_24", "_25", "_26", "_27",
    "_28", "_29", "_30", "_31",
];

/// Flatten a type expression into a list of cranelift data types
///
/// This function will recursively traverse the type expression and call the
/// given handler for each concrete type it finds.
///
/// # Arguments
///
/// * `name` - Name of the variable
/// * `input_ty` - The type expression to flatten
/// * `handler` - The handler to call for each basic type found
fn flatten_type<'s, F: FnMut(&Vec<&'s str>, ClType)>(
    name: &'s str,
    input_ty: &TypeExpr<'s>,
    mut handler: F,
) {
    if input_ty.is_void() {
        return;
    }
    let mut path = vec![name];
    fn recursive<'s, F: FnMut(&Vec<&'s str>, ClType)>(
        path: &mut Vec<&'s str>,
        root: &TypeExprNode<'s>,
        input_ty: &TypeExpr<'s>,
        handler: &mut F,
    ) {
        if root.is_void() {
            return;
        }
        if let Some(cl_ty) = basic_asttype_to_cltype(&root, input_ty) {
            handler(&path, cl_ty);
            return;
        }
        match root {
            &TypeExprNode::Slice(ty) => {
                path.push("size");
                handler(&path, cl_types::I64);
                path.pop();
                handler(&path, cl_types::R64);
            }
            &TypeExprNode::Array(_, _) => todo!("freeform array length"),
            TypeExprNode::Tuple(children) => {
                for (i, child) in children.iter().enumerate() {
                    path.push(TUPLE_PATHS[i]);
                    recursive(path, &input_ty.pool[*child], input_ty, handler);
                    path.pop();
                }
            }
            &TypeExprNode::Fn(_, _) => todo!("function pointers"),
            &TypeExprNode::TypeName(_) => todo!(),
            _ => (), // already covered by the earlier `basic_asttype_to_cltype`
        }
    }

    if let Some(cl_ty) = basic_asttype_to_cltype(input_ty.root(), &input_ty) {
        handler(&path, cl_ty)
    } else {
        recursive(&mut path, &input_ty.root(), &input_ty, &mut handler);
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::type_expr::{TypeExpr, TypeExprNode};

    use super::flatten_type;

    #[test]
    fn test() {
        let t = TypeExpr {
            pool: vec![
                TypeExprNode::I32,
                TypeExprNode::I32,
                TypeExprNode::U128,
                TypeExprNode::Tuple(vec![0, 1, 2]),
            ],
            root: 3,
        };
        flatten_type("x", &t, |path, cl_ty| {
            println!("({path:?}, {cl_ty})");
        });
    }
}

/// convert an AST into a MIR program
///
/// This is the main entry point for the conversion process.
/// It takes an AST and returns a MIR program.
pub fn ast_into_mir<'s>(ast: Ast<'s>) -> MirProgram<'s> {
    let mut mir_program = MirProgram::default();
    let mut symbol_table = SymbolTable::default();
    for n in ast.root_nodes.into_iter() {
        let ast_node = n.inner();
        let mir_node_ref = convert_top_level(&mut mir_program, ast_node, &mut symbol_table);
        mir_program.root_nodes.push(mir_node_ref);
    }
    mir_program
}

pub fn convert_top_level<'s>(
    program: &mut MirProgram<'s>,
    node: &AstNode<'s>,
    symbol_table: &mut SymbolTable<'s>,
) -> MirNodeRef<'s> {
    match node {
        AstNode::FnDef(ast_fn_def) => convert_fn_def(program, ast_fn_def, symbol_table),
        #[allow(unused_variables)]
        AstNode::Let(lhs, dtype, rhs) => {
            todo!("convert static variable `let` into MIR")
        }
        _ => unimplemented!(),
    }
}

fn convert_fn_def<'s>(
    program: &mut MirProgram<'s>,
    ast_fn_def: &FnDef<'s>,
    symbol_table: &mut SymbolTable<'s>,
) -> MirNodeRef<'s> {
    symbol_table.add_fn(ast_fn_def.name, ast_fn_def.sign.clone());
    symbol_table.push_layer();
    let mut context = Context::default();
    let (mut arg_types, mut arg_vars): (Vec<ClType>, HashMap<Vec<&str>, MirVarInfo>) =
        Default::default();
    ast_fn_def.sign.args.iter().for_each(|(name, ty)| {
        symbol_table.add_var(*name, PossibleTypes::Known(ty.clone()));
        flatten_type(name, ty, |path, dtype| {
            let id = context.suggest_new_var_id();
            arg_types.push(dtype);

            let var_info = MirVarInfo {
                id,
                dtype,
                is_mut: false,
            };
            arg_vars.insert(path.clone(), var_info);
        });
    });
    let mut mir_body = MirBlock {
        body: Vec::new(),
        vars: arg_vars,
    };
    if let Some(ast_body) = &ast_fn_def.body {
        for node in ast_body {
            convert_block_body(
                node.deref().inner(),
                symbol_table,
                &mut mir_body,
                &mut context,
            );
        }
    }
    symbol_table.pop_layer();
    let mir_fn_def = MirFnDef {
        name: ast_fn_def.name,
        args: arg_types,
        ret_type: basic_asttype_to_cltype(
            ast_fn_def.sign.ret_type.root(),
            &ast_fn_def.sign.ret_type,
        ),
        body: mir_body,
    };
    let node_ref = program.add_node(MirNode::FnDef(mir_fn_def));
    node_ref
}

fn convert_block_body<'s>(
    node: &AstNode<'s>,
    symbol_table: &mut SymbolTable<'s>,
    target: &mut MirBlock<'s>,
    context: &mut Context,
) {
    #[allow(unused_variables)]
    match node {
        AstNode::Call(callee, args) => todo!(),
        AstNode::Let(lhs, ty, rhs) => {
            let var_id = context.suggest_new_var_id();
            let ty = ty.as_ref().expect("todo: type infer");
            symbol_table.add_var(lhs, PossibleTypes::Known(ty.clone()));
            todo!()
        }
        AstNode::Assign(lhs, rhs) => todo!(),
        AstNode::MathOpAssign(op_kind, lhs, rhs) => todo!(),
        AstNode::BitOpAssign(op_kind, lhs, rhs) => todo!(),
        AstNode::Block(body) => todo!(),
        AstNode::If(if_expr) => todo!(),
        AstNode::Loop(body) => todo!(),
        AstNode::Return(Some(child)) => todo!(),
        AstNode::Return(None) => todo!(),
        AstNode::Break => todo!(),
        AstNode::Continue => todo!(),
        _ => unimplemented!(),
    }
}

/// Context for converting AST into MIR when inside a function
#[derive(Debug, Clone)]
struct Context {
    last_var_id: Option<u64>,
}

impl Default for Context {
    fn default() -> Self {
        Self { last_var_id: None }
    }
}

impl Context {
    fn suggest_new_var_id(&mut self) -> u64 {
        let var_id = self.last_var_id.map_or(0, |i| i + 1);
        self.last_var_id = Some(var_id);
        var_id
    }
}
