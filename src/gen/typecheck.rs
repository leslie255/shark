use crate::ast::type_expr::TypeExpr;

use super::GlobalContext;

#[must_use]
pub fn type_matches(global: &GlobalContext, lhs: &TypeExpr, rhs: &TypeExpr) -> bool {
    use TypeExpr::*;
    match (lhs, rhs) {
        (_, Never) => true,
        (USize, USize)
        | (ISize, ISize)
        | (U128, U128)
        | (U64, U64)
        | (U32, U32)
        | (U16, U16)
        | (U8, U8)
        | (I128, I128)
        | (I64, I64)
        | (I32, I32)
        | (I16, I16)
        | (I8, I8)
        | (F64, F64)
        | (F32, F32)
        | (Char, Char)
        | (Bool, Bool) => true,
        (Ptr(lhs), Ptr(rhs)) => type_matches(global, lhs, rhs),
        (Ref(lhs), Ref(rhs)) => type_matches(global, lhs, rhs),
        (Slice(lhs), Slice(rhs)) => type_matches(global, lhs, rhs),
        (Array(lhs_len, _), Array(rhs_len, _)) if lhs_len != rhs_len => false,
        (Array(_, lhs), Array(_, rhs)) => type_matches(global, lhs, rhs),
        (Tuple(lhs), Tuple(rhs)) if lhs.len() != rhs.len() => false,
        (Tuple(lhs), Tuple(rhs)) => {
            for (lhs, rhs) in lhs.iter().zip(rhs.iter()) {
                if !type_matches(global, lhs, rhs) {
                    return false;
                }
            }
            true
        }
        (Fn(l_args, l_ret), Fn(r_args, r_ret)) => {
            // TODO: counter-variance logic
            for (lhs, rhs) in l_args.iter().zip(r_args.iter()) {
                if lhs != rhs {
                    return false;
                }
            }
            l_ret == r_ret
        }
        (TypeName(..), TypeName(..)) => todo!(),
        (TypeName(..), _) => todo!(),
        (_, TypeName(..)) => todo!(),
        (lhs, _Numeric) => lhs.is_u() || lhs.is_i() || lhs.is_f(),
        (lhs, _Int) => lhs.is_u() || lhs.is_i(),
        (lhs, _SInt) => lhs.is_i(),
        (lhs, _Float) => lhs.is_f(),
        _ => false,
    }
}

