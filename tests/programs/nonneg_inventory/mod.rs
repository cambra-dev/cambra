//! A refined transactional store: `Mut(Map(String, {Int where _ >= 0}), Txn)`
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
//! **Currently blocked at parsing.**  The store type's refinement brace and the
//! store literal's `->` entry pair both parse now (`docs/chl-spec.md`,
//! "6.4 Refinement syntax" and "2.4 Atoms"), so the first unsupported construct
//! is `reserve`'s `requires Transaction` clause.  Behind it: `Map(…)` as an
//! annotation form, map lookup, `with begin():`, and record terms.  This pins the
//! `requires` parse failure.
//!
//! Expected output once fully unblocked: `` `some(1) `` (5 − 2 − 2, third
//! reservation refused).

use super::common::expect_compile_error;

#[test]
fn nonneg_inventory_currently_blocked_at_parsing() {
    expect_compile_error(include_str!("program.cambra"), "requires Transaction");
}
