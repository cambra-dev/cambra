//! UnaryOp operator: unary arithmetic and boolean operations on dataflow values.

use super::{BaseType, ColumnValue, Extent};

/// Kinds of unary operations supported by the interpreter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOpKind {
    /// Arithmetic negation (`-x`); valid on `Int`.
    Neg,
    /// Boolean negation (`not x`); valid on `Bool`.
    Not,
}

impl UnaryOpKind {
    /// Return the output [`Extent`] for this operation.
    pub fn output_extent(&self, _operand: &Extent) -> Extent {
        match self {
            // Neg always produces Int.
            UnaryOpKind::Neg => Extent::Base(BaseType::Int),
            // Not always produces Bool.
            UnaryOpKind::Not => Extent::Base(BaseType::Bool),
        }
    }
}

/// Apply a unary operation element-wise to a [`ColumnValue`], appending the result to `out`.
///
/// `out` is a column of the operand's variant. One row is appended per row of the operand. The
/// caller owns the rest of the column's state: it clears the rows it does not keep and reserves
/// room for the new ones, and the call writes each result once into that room.
pub fn apply_unaryop_into(op: UnaryOpKind, operand: &ColumnValue, out: &mut ColumnValue) {
    match (op, operand, out) {
        (UnaryOpKind::Neg, ColumnValue::Ints(v), ColumnValue::Ints(o)) => {
            o.extend(v.iter().map(|&x| -x));
        }
        (UnaryOpKind::Not, ColumnValue::Bools(v), ColumnValue::Bools(o)) => {
            o.extend(v.iter().map(|&x| !x));
        }
        (op, operand, out) => {
            panic!("Unsupported unary op: {op:?} on {operand:?}, into a column {out:?}")
        }
    }
}

/// Apply a unary operation element-wise to a [`ColumnValue`], into a newly allocated column.
///
/// The operand's buffer is not reused.
pub fn apply_unaryop_column(op: UnaryOpKind, operand: &ColumnValue) -> ColumnValue {
    let mut out = operand.empty_like();
    apply_unaryop_into(op, operand, &mut out);
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
}
