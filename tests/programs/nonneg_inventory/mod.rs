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
//! **Currently blocked at parsing.**  The store type's refinement brace, the
//! store literal's `->` entry pair, and `reserve`'s `requires Transaction` clause
//! all parse now (`docs/chl-spec.md`, "6.4 Refinement syntax", "2.4 Atoms" and
//! "Trait requirements"), so the first unsupported construct is the
//! `assert` statement, which is not lexed.  Behind it: lowering refuses the
//! `requires` clause, then `Map(…)` as an annotation form, map lookup,
//! `with begin():`, and record terms.  This pins the `assert` parse failure.
//!
//! Expected output once fully unblocked: `` `some(1) `` (5 − 2 − 2, third
//! reservation refused).

use super::common::expect_compile_error_past;

#[test]
fn nonneg_inventory_currently_blocked_at_parsing() {
    expect_compile_error_past(
        include_str!("program.cambra"),
        "assert qty > 0",
        "found 'requires'",
    );
}
