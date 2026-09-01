//! A cart-abandonment timer, and with it the second primitive the
//! durable-execution augmentation needs: a deadline is a source over
//! transactional state.  `clock.due(deadlines)` yields one element per key
//! whose deadline has passed, so scheduling is a write, rescheduling is a
//! write, and cancelling is a delete.  Cancellation is therefore an ordinary
//! transaction and cannot race the fire it cancels, which is the property a
//! separate timer service has to reconstruct at its boundary.
//!
//! `clock.due` takes the mutable variable by reference, under the same
//! downward-only discipline a `Mut(…)` parameter carries
//! (`docs/chl-spec.md`, "8.1 Mutation is explicit: the `:=` operator").  It
//! watches the deadline map's history rather than a snapshot, which is also
//! what keeps it legal: a bare read of a `Txn` variable outside a block is an
//! error (`docs/chl-spec.md`, "8.3 Reads").
//!
//! The 24-hour wait is what makes this durable execution rather than a sleep —
//! nothing about the pending cart may live in a worker's memory across it.
//!
//! **Blocked at lowering**, pinned on `clock.due(deadlines)`: a call in method
//! position is not a named function call, the same shape as `catalog.keys()`
//! and `txn.current_time()` that `docs/chl-spec.md`, "7.1 Aggregates" leaves
//! open.  This program's other own gap has no decided spelling at all: map-entry
//! deletion is written `del deadlines[cart]` here, borrowed from Python, and
//! nothing decides it.  Behind both, shared with the rest of the corpus:
//! `import`, `Feed(…)` forward declarations, subscript assignment targets, and
//! `Map(K, V)` as an annotation.

use super::common::expect_compile_error;

#[test]
fn abandoned_cart_currently_blocked_at_lowering() {
    expect_compile_error(include_str!("program.cambra"), "clock.due(deadlines)");
}
