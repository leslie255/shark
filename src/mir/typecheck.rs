use crate::{
    ast::{pat::Mutability, type_expr::TypeExpr},
    gen::context::GlobalContext,
};

#[must_use]
pub fn type_matches(global: &GlobalContext, expect: &TypeExpr, found: &TypeExpr) -> bool {
    use TypeExpr::*;
    match (expect, found) {
        (TypeName(..), TypeName(..)) => todo!(),
        (TypeName(..), _) => todo!(),
        (_, TypeName(..)) => todo!(),
        (_, Never) | (_Unknown, _) | (_, _Unknown) => true,
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
        (Ptr(Mutability::Mutable, _), Ptr(Mutability::Const, _)) => false,
        (Ptr(_, lhs), Ptr(_, rhs)) => type_matches(global, lhs, rhs),
        (Ref(Mutability::Mutable, _), Ref(Mutability::Const, _)) => false,
        (Ref(_, lhs), Ref(_, rhs)) => type_matches(global, lhs, rhs),
        (Slice(lhs), Slice(rhs)) => type_matches(global, lhs, rhs),
        (Array(lhs_len, _), Array(rhs_len, _)) if lhs_len != rhs_len => false,
        (Array(_, lhs), Array(_, rhs)) => type_matches(global, lhs, rhs),
        (Tuple(lhs), Tuple(rhs)) if lhs.len() != rhs.len() => false,
        (Tuple(lhs), Tuple(rhs)) => {
            let mut rhs_iter = rhs.iter();
            for lhs in lhs.iter() {
                // we know that lhs and rhs have the same length
                let rhs = unsafe { rhs_iter.next().unwrap_unchecked() };
                if !type_matches(global, lhs, rhs) {
                    return false;
                }
            }
            true
        }
        // tuple of one field is the same as a value due to limitations of the syntax
        (Tuple(lhs), rhs) => match lhs.as_slice() {
            [lhs] => type_matches(global, lhs, rhs),
            _ => false,
        },
        (lhs, Tuple(rhs)) => match rhs.as_slice() {
            [rhs] => type_matches(global, lhs, rhs),
            _ => false,
        },
        (Fn(l_args, l_ret), Fn(r_args, r_ret)) => {
            // TODO: counter-variance logic
            for (lhs, rhs) in l_args.iter().zip(r_args.iter()) {
                if lhs != rhs {
                    return false;
                }
            }
            l_ret == r_ret
        }
        (_UnknownNumeric(expect), _UnknownNumeric(found)) => {
            if expect.is_int && !found.is_int {
                return false;
            }
            if !expect.is_signed && found.is_signed {
                return false;
            }
            true
        }
        (_UnknownNumeric(expect), found) => match (expect.is_int, expect.is_signed) {
            // let x = 255;
            // x = {found};
            (true, false) => found.is_numeric(),
            // let x = -255;
            // x = {found};
            (true, true) => found.is_i() || found.is_f(),
            // let x = 255.1;
            // x = {found};
            (false, _) => found.is_f(),
        },
        (expect, _UnknownNumeric(found)) => match (found.is_int, found.is_signed) {
            // let x: {expect};
            // x = 255;
            (true, false) => expect.is_numeric(),
            // let x: {expect};
            // x = -255;
            (true, true) => expect.is_i() || expect.is_f(),
            // let x: {expect};
            // x = 255.1;
            (false, _) => expect.is_f(),
        },
        _ => false,
    }
}
