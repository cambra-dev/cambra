//! The checkout saga — reserve inventory, authorize payment, then advance or
//! compensate — written without an orchestration construct.  The saga is a
//! per-key state machine over transactional state, advanced by one `for` loop
//! per event source, and compensation is an ordinary transaction the machine
//! reaches.
//!
//! What durable execution adds is not the compensating step but the guarantee
//! it runs, and that guarantee decomposes into two things this program assumes:
//! the durability of `checkouts`, which is a property of the history substrate
//! (`src/ccl/design/mutability.md`), and the at-most-once call contract that
//! `external_call` pins.  Nothing is left over.  Retry with backoff is the same
//! observation once more: a failed result writes a new deadline
//! (`abandoned_cart`) and re-dispatches under a new attempt key, so it needs no
//! loop and does not wait on `while` lowering.
//!
//! One totality obligation is worth naming because the checker cannot discharge
//! it today.  `charge_results`' domain is exactly the set of keys dispatched
//! into `charges`, which is exactly the set of keys `checkouts` holds, so
//! `checkouts[id]` is total.  `FullMap`'s earned domain
//! (`docs/chl-spec.md`, "6.3 Direction: collections as functions [Tentative]")
//! is stated for a fixed key set; this one grows, which that section's `[Open]`
//! marker already names as the construction-site question.
//!
//! **Blocked at parsing**, pinned on the entry-pair `for` binder that iterates
//! the result source.  Ahead of it in the same run: the `->` map-literal entry
//! (shared with the storefront), `import`, `with` in value position, and
//! `FullMap(…)` as a type application.

use super::common::expect_compile_error;

#[test]
fn checkout_saga_currently_blocked_at_parsing() {
    expect_compile_error(
        include_str!("program.cambra"),
        "for id -> outcome in charge_results",
    );
}
