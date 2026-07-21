//! A refined transactional store: `Mut(Map(String, {q: Int | q >= 0}), Txn)`
//! states "stock never goes negative" once, in the store's type, and the
//! compiler enforces it on every write path.  The `stock >= qty` guard in
//! `reserve` is what proves the decrement stays non-negative — deleting the
//! guard must make the program ill-typed, not make the store go negative at
//! runtime.  A companion negative test (the guardless variant pinned as a
//! type error) becomes possible the day the refinement machinery lands.
//!
//! This isolates the storefront's oversell invariant: same store type, same
//! guard shape, no HTTP.
//!
//! **Currently blocked at parsing.**  The `->` map-entry pair inside the
//! store's literal is rejected (`->` doesn't parse as an expression; the
//! `:=` binding form itself now parses).  Behind it: the refinement braces
//! and `Mut(..., Txn)` as annotation forms, map lookup, `match`/`case`,
//! `requires Transaction`, `with begin():`, and record terms.  This pins
//! the map-entry parse failure.
//!
//! Expected output once fully unblocked: `some(1)` (5 − 2 − 2, third
//! reservation refused).

use super::common::expect_compile_error;

#[test]
fn nonneg_inventory_currently_blocked_at_parsing() {
    expect_compile_error(
        include_str!("program.cambra"),
        "found '>', expected expression",
    );
}
