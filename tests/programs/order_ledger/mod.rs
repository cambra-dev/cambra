//! The operator graph's shape-coverage program: one source carrying every
//! construct the operator pane draws differently.  A UDF called from three
//! sites, a generator UDF fused into its consumer, a loop-carried mutable
//! variable over a concrete induction extent, two transactional mutable
//! variables over `Txn`, a feed written from inside a transaction, and a
//! declarative aggregate over a filtered comprehension.
//!
//! Its value is the inspector rather than the answer: 51 source lines convert
//! to 222 operators, most of them fan-out, constant, and memo plumbing, which
//! makes it the program to read when asking what the graph pane must
//! consolidate.  Adding a construct here changes that count.

use super::common::expect_scalar;

#[test]
fn order_ledger_totals_7750() {
    expect_scalar(include_str!("program.cambra"), "7750");
}
