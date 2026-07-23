//! Transitive closure as a recursive query — the flagship "Cambra is a
//! database substrate" demo.  `reach` references itself in its own definition
//! (that self-reference is the cycle), and the `Set(...)` annotation is what
//! makes the fixpoint converge: a set dedups, so the union stops growing once
//! no new pair appears (as a list it would be multiset semantics and never
//! terminate).
//!
//! **Currently blocked at parsing.**  The record-term syntax `(src=1, dst=2)`
//! now parses; the next blocker is the `rec` recursive binding — `rec` is not
//! a keyword yet, so `rec reach_comp` reads as two identifiers.  Beyond that
//! lie the `Set(T)` type constructor and the fixpoint semantics.  This pins
//! the `rec` failure; when `rec` is supported, the test goes red and the next
//! blocker gets pinned.
//!
//! Expected output once fully unblocked (the reachable-pair set, sorted):
//! `{(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4)}`.

use super::common::expect_compile_error;

#[test]
fn reachability_currently_blocked_at_parsing() {
    expect_compile_error(include_str!("program.cambra"), "rec reach_comp");
}
