//! A transactional store read at multiple sites per block: each `with begin():`
//! reads `pool` twice, once in the guard and once in the write value.
//!
//! The transact phase substitutes the read-your-writes snapshot at both sites,
//! and the substituted copies must carry freshened, unique `NodeId`s —
//! `tests/inspector_goldens.rs` asserts the dense window that produces.

use super::common::expect_scalar;

#[test]
fn every_guarded_write_commits() {
    // 100 − 10 − 20 − 30, every guard passing over the snapshot it reads.
    //
    // The program observes `pool` through `await_final` because that is the only
    // terminal read of a mutable variable: a read fed out of a block that does
    // not write `pool` is an as-of read at an arbitrary commit position
    // (`docs/chl-spec.md`, "8.3 Reads"), which the seed satisfies as well as the
    // folded value.
    expect_scalar(include_str!("program.cambra"), "Function [ () -> 40 ]");
}
