//! A short-circuit `and` or `or` fused into a scalar program: a [`JunctionFn`] whose operands are
//! `Bool` sub-programs, each tested only on the rows the operands before it leave undecided.
//!
//! A program reads a `JunctionFn` through its `Predicate` instruction, which hands it its captures
//! as a `Case` instruction does. The design is in `src/interpreter/design-operators.md`,
//! "Predicates".

use smol_str::SmolStr;

use super::case::{Captured, Keep, Rows, Split, SubBuffers, SubProgram, without};
use crate::interpreter::RowIndex;

/// Whether a junction holds where every operand holds or where some operand does.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum Junction {
    /// Each operand is tested on the rows the operands before it kept.
    And,
    /// Each operand is tested on the rows the operands before it rejected.
    Or,
}

/// The short-circuit `and` or `or` of `Bool` sub-programs, in source order.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct JunctionFn {
    pub(super) junction: Junction,
    pub(super) operands: Vec<SubProgram>,
}

/// The buffers a [`JunctionFn`] reuses across the blocks of the program holding it.
#[derive(Default)]
pub(super) struct JunctionBuffers {
    /// Under `Or`, the rows no operand so far held on.
    undecided: Rows,
    /// The rows the current operand holds on. Under `Or` no split writes it, and it stays empty.
    taken: Rows,
    /// Scratch for the rows the current operand leaves.
    left: Vec<RowIndex>,
    /// Under `Or`, the rows some operand held on, ascending.
    held: Vec<RowIndex>,
    /// Scratch for [`without`].
    marks: Vec<bool>,
    operands: Vec<SubBuffers>,
    /// The rows where the junction holds on the current block, which `Scratch::junction_block`
    /// reuses across blocks.
    pub(super) rows: Rows,
}

impl JunctionFn {
    /// Whether every capture this junction's operands read is named in `captures`.
    pub(super) fn reads_only<T>(&self, captures: &[(SmolStr, T)]) -> bool {
        self.operands.iter().all(|operand| {
            operand
                .reads
                .iter()
                .all(|name| captures.iter().any(|(n, _)| n == name))
        })
    }

    /// Narrow `rows`, rows of a block of `len` rows, to those where the junction holds.
    pub(super) fn holds(
        &self,
        captures: &[(SmolStr, Captured)],
        len: usize,
        buffers: &mut JunctionBuffers,
        rows: &mut Rows,
    ) {
        let JunctionBuffers {
            undecided,
            taken,
            left,
            held,
            marks,
            operands,
            ..
        } = buffers;
        operands.resize_with(self.operands.len(), SubBuffers::default);
        let operands = self.operands.iter().zip(operands.iter_mut());
        match self.junction {
            // Each operand narrows `rows` to the rows it holds on.
            Junction::And => {
                for (operand, buffers) in operands {
                    if rows.is_empty() {
                        break;
                    }
                    taken.set_empty();
                    let split = Split {
                        rest: rows,
                        taken,
                        left,
                        keep: Keep::Taken,
                    };
                    operand.select(captures, len, split, buffers);
                    std::mem::swap(rows, taken);
                }
            }
            // Each operand narrows `undecided` to the rows it fails on; the junction holds on the
            // rows of `rows` that are not left undecided.
            Junction::Or => {
                undecided.block = rows.block;
                undecided.positions.clone_from(&rows.positions);
                for (operand, buffers) in operands {
                    if undecided.is_empty() {
                        break;
                    }
                    taken.set_empty();
                    let split = Split {
                        rest: undecided,
                        taken,
                        left,
                        keep: Keep::Rest,
                    };
                    operand.select(captures, len, split, buffers);
                    debug_assert!(taken.is_empty(), "an `Or` operand writes only its rest");
                }
                match undecided.positions() {
                    None => rows.set_empty(),
                    Some([]) => {}
                    Some(failed) => {
                        without(rows, len, failed, marks, held);
                        rows.block = false;
                        std::mem::swap(&mut rows.positions, held);
                    }
                }
            }
        }
    }
}
