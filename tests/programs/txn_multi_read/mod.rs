//! A transactional store read at multiple sites per block: each `with begin():`
//! reads `pool` twice, once in the guard and once in the write value.
//!
//! The transact phase substitutes the read-your-writes snapshot at both sites,
//! and the substituted copies must carry freshened, unique `NodeId`s —
//! `tests/inspector_goldens.rs` asserts the dense window that produces.

use super::common::expect_scalar_currently_buggy;

#[test]
fn txn_multi_read_currently_drops_the_guarded_writes() {
    // Correct output: `Function [ 40 ]` — 100 − 10 − 20 − 30, every guard
    // passing. The write sits inside an `if` inside the transaction and does
    // not survive the conditional, so the feed sees the seed value instead.
    expect_scalar_currently_buggy(include_str!("program.cambra"), "Function [ 100 ]");
}
