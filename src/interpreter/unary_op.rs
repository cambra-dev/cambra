//! UnaryOp operator: unary arithmetic and boolean operations on dataflow values.

use std::iter::repeat_n;

use crate::view::View;

use super::{BaseType, ColumnValue, ColumnView, Extent};

/// Kinds of unary operations supported by the interpreter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOpKind {
    /// Arithmetic negation (`-x`); valid on `Int`.
    Neg,
    /// Boolean negation (`not x`); valid on `Bool`.
    Not,
    /// The `UInt` equal to an `Int` (`int_to_uint(x)`). Panics on a negative operand, which no
    /// `UInt` equals (`Builtin::IntToUint` in `src/ccl/ops.rs`).
    IntToUint,
}

impl UnaryOpKind {
    /// Return the output [`Extent`] for this operation.
    pub fn output_extent(&self, _operand: &Extent) -> Extent {
        match self {
            // Neg always produces Int.
            UnaryOpKind::Neg => Extent::Base(BaseType::Int),
            // Not always produces Bool.
            UnaryOpKind::Not => Extent::Base(BaseType::Bool),
            UnaryOpKind::IntToUint => Extent::Base(BaseType::UInt),
        }
    }
}

/// The empty column that holds the result of `op` over an operand shaped like `operand`.
pub fn unaryop_result_column(op: UnaryOpKind, operand: &ColumnView) -> ColumnValue {
    match op {
        UnaryOpKind::Neg | UnaryOpKind::Not => operand.empty_like(),
        UnaryOpKind::IntToUint => ColumnValue::UInts(Vec::new()),
    }
}

/// `x` as a `UInt`. The type `int_to_uint` gives its result claims that result equals `x`,
/// which no `UInt` does for a negative `x`, so execution stops there.
fn int_to_uint(x: i64) -> u64 {
    u64::try_from(x).unwrap_or_else(|_| panic!("int_to_uint applied to the negative Int {x}"))
}

/// Apply a unary operation element-wise to a column view, appending the result to `out`.
///
/// `out` is a column of the result's element type ([`unaryop_result_column`]). One row is appended per row of the operand.
/// The caller owns the rest of the column's state: it clears the rows it does not keep and
/// reserves room for the new ones, and the call writes each result once into that room.
pub fn apply_unaryop_views(op: UnaryOpKind, operand: &ColumnView, out: &mut ColumnValue) {
    match (op, operand, out) {
        (UnaryOpKind::Neg, ColumnView::Ints(v), ColumnValue::Ints(o)) => match *v {
            View::Slice(values) => o.extend(values.iter().map(|&x| -x)),
            View::Constant { value, len } if len > 0 => o.extend(repeat_n(-*value, len)),
            View::Constant { .. } => {}
        },
        (UnaryOpKind::Not, ColumnView::Bools(v), ColumnValue::Bools(o)) => match *v {
            View::Slice(values) => o.extend(values.iter().map(|&x| !x)),
            View::Constant { value, len } if len > 0 => o.extend(repeat_n(!*value, len)),
            View::Constant { .. } => {}
        },
        (UnaryOpKind::IntToUint, ColumnView::Ints(v), ColumnValue::UInts(o)) => match *v {
            View::Slice(values) => o.extend(values.iter().map(|&x| int_to_uint(x))),
            View::Constant { value, len } if len > 0 => {
                o.extend(repeat_n(int_to_uint(*value), len))
            }
            View::Constant { .. } => {}
        },
        (op, operand, out) => {
            panic!("Unsupported unary op: {op:?} on {operand:?}, into a column {out:?}")
        }
    }
}

/// Apply a unary operation element-wise to a [`ColumnValue`], appending the result to `out`.
pub fn apply_unaryop_into(op: UnaryOpKind, operand: &ColumnValue, out: &mut ColumnValue) {
    match operand.view() {
        Some(view) => apply_unaryop_views(op, &view, out),
        None => panic!("Unsupported unary op: {op:?} on {operand:?}, into a column {out:?}"),
    }
}

/// Apply a unary operation element-wise to a [`ColumnValue`], into a newly allocated column.
///
/// The operand's buffer is not reused.
pub fn apply_unaryop_column(op: UnaryOpKind, operand: &ColumnValue) -> ColumnValue {
    let Some(view) = operand.view() else {
        panic!("Unsupported unary op: {op:?} on {operand:?}")
    };
    let mut out = unaryop_result_column(op, &view);
    apply_unaryop_views(op, &view, &mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The call appends to the caller's column, which the caller has cleared for reuse.
    #[test]
    fn a_unary_result_is_appended_to_the_callers_column() {
        let mut out = ColumnValue::Ints(vec![7; 4]);
        out.clear();
        apply_unaryop_into(UnaryOpKind::Neg, &ColumnValue::Ints(vec![1, -2]), &mut out);
        assert_eq!(out, ColumnValue::Ints(vec![-1, 2]));
        let mut out = ColumnValue::Bools(vec![true; 4]);
        out.clear();
        apply_unaryop_into(
            UnaryOpKind::Not,
            &ColumnValue::Bools(vec![true, false]),
            &mut out,
        );
        assert_eq!(out, ColumnValue::Bools(vec![false, true]));
    }

    #[test]
    fn int_to_uint_converts_a_non_negative_int() {
        let out = apply_unaryop_column(UnaryOpKind::IntToUint, &ColumnValue::Ints(vec![0, 3]));
        assert_eq!(out, ColumnValue::UInts(vec![0, 3]));
    }

    #[test]
    #[should_panic(expected = "int_to_uint applied to the negative Int -1")]
    fn int_to_uint_panics_on_a_negative_int() {
        apply_unaryop_column(UnaryOpKind::IntToUint, &ColumnValue::Ints(vec![2, -1]));
    }
}
