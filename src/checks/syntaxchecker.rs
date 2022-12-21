use crate::{
    ast::AstNode,
    error::{location::Traced, ErrorCollector, ErrorContent},
};

/// Generates a syntax checker function
///
/// The generated function will check that the node is one of the allowed ones,
/// and then execute some additional checks if defined.
///
/// # Example
///
/// ```
/// impl_syntax_checker! {
///     fn_name: check_top_level_node,
///     allowed: AstNode::FnDef(_) | AstNode::StructDef(_),
///     additional_checks: {
///         // additional checks
///     },
/// }
/// ```
///
/// The above example generates the function:
///
/// ```
/// pub fn check_top_level<'src>(
///     node: &Traced<'src, AstNode<'src>>,
///     err_collector: &ErrorCollector<'src>
/// ) {
///     // ...
/// }
/// ```
macro_rules! impl_syntax_checker {
    {fn_name: $fn_name:ident, allowed: $allowed:pat, err: $err:path, additional_checks: $additional_checks:block,} => {
        pub fn $fn_name<'src>(
            node: &Traced<'src, AstNode<'src>>,
            err_collector: &ErrorCollector<'src>,
        ) {
            match node.inner() {
                $allowed => (),
                _ => $err
                    .wrap(node.src_loc())
                    .collect_into(err_collector),
            }
            $additional_checks;
        }
    };
    {fn_name: $fn_name:ident, allowed: $allowed:pat, err: $err:path, additional_checks: $additional_checks:block} => {
        impl_syntax_checker! {fn_name: $fn_name, allowed: $allowed, err: $err, additional_checks: $additional_checks,}
    };
    {fn_name: $fn_name:ident, allowed: $allowed:pat, err: $err:path,} => {
        impl_syntax_checker! {fn_name: $fn_name, allowed: $allowed, err: $err, additional_checks: {},}
    };
    {fn_name: $fn_name:ident, allowed: $allowed:pat, err: $err:path} => {
        impl_syntax_checker! {fn_name: $fn_name, allowed: $allowed, err: $err, additional_checks: {},}
    };
}

impl_syntax_checker! {
    fn_name: check_top_level,
    allowed:
          AstNode::FnDef(..)
        | AstNode::StructDef(..)
        | AstNode::UnionDef(..)
        | AstNode::EnumDef(..)
        | AstNode::TypeDef(..),
    err: ErrorContent::ExprNotAllowedAtTopLevel,
}

impl_syntax_checker! {
    fn_name: check_fn_body,
    allowed:
          AstNode::Call(..)
        | AstNode::Let(..)
        | AstNode::Assign(..)
        | AstNode::MathOpAssign(..)
        | AstNode::BitOpAssign(..)
        | AstNode::Block(..)
        | AstNode::If(..)
        | AstNode::Loop(..)
        | AstNode::Return(..)
        | AstNode::Break
        | AstNode::Continue,
    err: ErrorContent::ExprNotAllowedAsFnBody,
}

impl_syntax_checker! {
    fn_name: check_child,
    allowed:
          AstNode::Identifier(..)
        | AstNode::Number(..)
        | AstNode::String(..)
        | AstNode::Char(..)
        | AstNode::Bool(..)
        | AstNode::Array(..)
        | AstNode::MathOp(..)
        | AstNode::BitOp(..)
        | AstNode::BoolOp(..)
        | AstNode::Cmp(..)
        | AstNode::MemberAccess(..)
        | AstNode::BitNot(..)
        | AstNode::BoolNot(..)
        | AstNode::MinusNum(..)
        | AstNode::PlusNum(..)
        | AstNode::Call(..)
        | AstNode::TakeRef(..)
        | AstNode::Deref(..)
        | AstNode::Typecast(..)
        | AstNode::Tuple(..),
    err: ErrorContent::ExprNotAllowedAsChild,
}
