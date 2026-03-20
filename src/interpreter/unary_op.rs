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

/// Apply a unary operation element-wise to a [`ColumnValue`].
pub fn apply_unaryop_column(op: UnaryOpKind, operand: ColumnValue) -> ColumnValue {
    match (op, operand) {
        (UnaryOpKind::Neg, ColumnValue::Ints(mut v)) => {
            v.iter_mut().for_each(|x| *x = -*x);
            ColumnValue::Ints(v)
        }
        (UnaryOpKind::Not, ColumnValue::Bools(mut v)) => {
            v.negate();
            ColumnValue::Bools(v)
        }
        (op, operand) => panic!("Unsupported unary op: {op:?} on {operand:?}"),
    }
}
