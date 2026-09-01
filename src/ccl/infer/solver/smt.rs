use crate::ccl::{Refinement, Type};

pub fn smt_sub(base: &Type, lhs: &[Refinement], rhs: &[Refinement]) -> bool {
    // todo!("Quantify __elem as the `base` type (must be Bool or Int for now) and then check using an smt solver that lhs[base] implies rhs[base].")
    false
}
