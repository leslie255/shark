pub mod builder;
pub mod typecheck;

use std::fmt::Debug;

use index_vec::IndexVec;

use crate::{
    ast::{pat::Mutability, type_expr::TypeExpr},
    gen::context::FuncIndex,
    token::NumValue,
    IndexVecFormatter,
};

pub static TUPLE_FIELDS_LABELS: [&'static str; 16] = [
    "_0", "_1", "_2", "_3", "_4", "_5", "_6", "_7", "_8", "_9", "_10", "_11", "_12", "_13", "_14",
    "_15",
];

#[derive(Clone, Default)]
pub struct MirObject {
    pub functions: IndexVec<FuncIndex, MaybeExternFunction>,
}

#[derive(Clone)]
pub enum MaybeExternFunction {
    Local(MirFunction),
    Extern,
}

impl Debug for MaybeExternFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Local(func) => func.fmt(f),
            Self::Extern => write!(f, "extern"),
        }
    }
}

#[derive(Clone)]
pub struct VarInfo {
    pub is_mut: bool,
    /// the variable is a function arguments
    pub is_arg: bool,
    pub ty: TypeExpr,
    pub name: Option<&'static str>,
}

#[derive(Clone)]
pub struct MirFunction {
    pub vars: IndexVec<Variable, VarInfo>,
    /// Function argument variables must come before other variables
    pub blocks: IndexVec<BlockRef, Block>,
}

#[derive(Clone, Default)]
pub struct Block {
    pub body: IndexVec<StatementRef, Statement>,
    pub terminator: Option<Terminator>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockRef(pub usize);
impl index_vec::Idx for BlockRef {
    fn from_usize(idx: usize) -> Self {
        Self(idx)
    }
    fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone)]
pub enum Statement {
    Assign(Place, Value),
    StaticCall {
        func_idx: FuncIndex,
        args: Vec<Value>,
        result: Place,
    },
    /// TODO
    #[allow(dead_code)]
    DynCall,
    /// Used for deleting a statement
    #[allow(dead_code)]
    Nop,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StatementRef(usize);
impl index_vec::Idx for StatementRef {
    fn from_usize(idx: usize) -> Self {
        Self(idx)
    }
    fn index(self) -> usize {
        self.0
    }
}

/// A place is a memory model for expressions like
/// ```
/// *thing.field[index]
/// ```
///
/// These expressions can be used as LHS of assignments, or they can be also used to yield a value
/// from (a.k.a. converting an lvalue to an rvalue), the latter is represented by wrapping it
/// inside a `Value::Copy` or `Value::Ref` for by-copy or by-ref, respectively.
///
/// A place is made from two parts. A local variable as its root (`local`), and some "decorators"
/// (`projections`) on it.
///
/// In the above example, "`thing`" is an example of `local`, where as the deref operator, field
/// access, indexing, are the `projections`.
///
/// `projections` are stored from inside to outside. So in the above example, the projection stack
/// would be `\[Field("field"), Index(...), Deref\]`.
#[derive(Clone)]
pub struct Place {
    pub local: Variable,
    pub projections: Vec<ProjectionEle>,
}

impl Place {
    pub fn no_projection(local: Variable) -> Self {
        Self {
            local,
            projections: Vec::new(),
        }
    }
}

/// See `Place` above.
#[derive(Debug, Clone)]
pub enum ProjectionEle {
    Deref(TypeExpr),
    #[allow(dead_code)]
    Index(Value),
    #[allow(dead_code)]
    Field(&'static str),
}

/// It's more like an rvalue. It can be a constant, or a yielded value from a `Place` (either by
/// copy or by ref).
#[derive(Clone)]
pub enum Value {
    Number(TypeExpr, NumValue),
    Bool(bool),
    Char(char),
    Copy(Place),
    Ref(Mutability, Place),
    Void,
    Unreachable,
}

impl Value {
    /// Returns `true` if the value is [`Unreachable`].
    ///
    /// [`Unreachable`]: Value::Unreachable
    #[must_use]
    pub fn is_unreachable(&self) -> bool {
        matches!(self, Self::Unreachable)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Variable(pub usize);
impl index_vec::Idx for Variable {
    fn from_usize(idx: usize) -> Self {
        Self(idx)
    }
    fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone)]
pub enum Terminator {
    Jmp(BlockRef),
    CondJmp {
        cond: Condition,
        target: BlockRef,
        otherwise: BlockRef,
    },
    Return(Value),
    Unreachable,
}

#[derive(Clone)]
pub struct Condition {
    pub cond_kind: CondKind,
    pub val: Value,
}

impl Condition {
    pub const fn new(cond_kind: CondKind, val: Value) -> Self {
        Self { cond_kind, val }
    }
    pub const fn if_true(val: Value) -> Self {
        Self {
            cond_kind: CondKind::IfTrue,
            val,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CondKind {
    IfTrue,
    IfFalse,
}

#[derive(Debug, Clone)]
pub struct PromotedConsts {}

impl Debug for BlockRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "block{}", self.0)
    }
}

impl Debug for StatementRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "stmt{}", self.0)
    }
}

impl Debug for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "var{}", self.0)
    }
}

impl Debug for Place {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.projections.as_slice() {
            [] => self.local.fmt(f),
            projections => {
                write!(f, "({:?}", self.local)?;
                for proj in projections {
                    match proj {
                        ProjectionEle::Deref(ty) => write!(f, ".deref(as {:?})", ty)?,
                        ProjectionEle::Index(val) => write!(f, ".index({:?})", val)?,
                        &ProjectionEle::Field(name) => write!(f, ".field({})", name)?,
                    }
                }
                write!(f, ")")
            }
        }
    }
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(ty, num) => write!(f, "val({:?} as {:?})", num, ty),
            Self::Bool(b) => write!(f, "val({})", b),
            Self::Char(ch) => write!(f, "val('{}')", ch.escape_unicode()),
            Self::Copy(place) => write!(f, "copy {:?}", place),
            Self::Ref(mutability, place) => match mutability {
                Mutability::Mutable => write!(f, "ref mut {:?}", place),
                Mutability::Const => write!(f, "ref {:?}", place),
            },
            Self::Void => write!(f, "void"),
            Self::Unreachable => write!(f, "unreachable"),
        }
    }
}

impl Debug for VarInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_mut {
            write!(f, "mut ")?;
        } else {
            write!(f, "const ")?;
        }
        write!(f, "{:?}", self.ty)?;
        if let Some(name) = self.name {
            write!(f, " => {:?}", name)?;
        }
        Ok(())
    }
}

impl Debug for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let terminator: &dyn Debug = match &self.terminator {
            Some(terminator) => terminator,
            None => &DotDotDot,
        };
        f.debug_list()
            .entries(self.body.iter())
            .entry(terminator)
            .finish()
    }
}

impl Debug for MirFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MirFunction")
            .field("vars", &IndexVecFormatter(&self.vars))
            .field("blocks", &IndexVecFormatter(&self.blocks))
            .finish()
    }
}

impl Debug for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Assign(lhs, rhs) => write!(f, "{:?} = {:?}", lhs, rhs),
            Self::StaticCall {
                func_idx,
                args,
                result,
            } => {
                write!(f, "{:?} = static_call {:?}(", result, func_idx)?;
                for arg in args {
                    write!(f, "{:?},", arg)?;
                }
                write!(f, ")")
            }
            Self::DynCall => write!(f, "{{TODO: dyn call}}"),
            Self::Nop => write!(f, "NOP"),
        }
    }
}

impl Debug for CondKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IfTrue => write!(f, "if_true"),
            Self::IfFalse => write!(f, "if_false"),
        }
    }
}

impl Debug for Condition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}({:?})", self.cond_kind, self.val)
    }
}

impl Debug for Terminator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Jmp(target) => write!(f, "jmp {:?}", target),
            Self::CondJmp {
                cond,
                target,
                otherwise,
            } => write!(f, "jmp {:?} ? {:?} : {:?}", cond, target, otherwise),
            Self::Return(val) => write!(f, "ret {:?}", val),
            Self::Unreachable => write!(f, "UNREACHABLE"),
        }
    }
}

struct DotDotDot;
impl Debug for DotDotDot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "...")
    }
}

impl Debug for MirObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MirObject")
            .field("functions", &IndexVecFormatter(&self.functions))
            .finish()
    }
}
