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
//! **Currently blocked at lexing.**  The first unsupported construct is the
//! `` ` `` prefix on the `` `some ``/`` `none `` variant tags
//! (`docs/chl-spec.md`, "6.5 Direction: variants [Decided]"), which the lexer
//! rejects outright; because lexing is a whole-file pass it precedes the
//! `->` map-entry pair in the store literal, which is the next blocker and
//! is a parse-level one.  Behind those: the refinement braces (`where` /
//! `_` — "6.4 Direction: refinement syntax [Decided]") and `Mut(..., Txn)`
//! as annotation forms, map lookup, `match`/`case`, `requires Transaction`,
//! `with begin():`, and record terms.  This pins the variant-tag lex
//! failure.
//!
//! Expected output once fully unblocked: `` `some(1) `` (5 − 2 − 2, third
//! reservation refused).

use super::common::expect_compile_error;

#[test]
fn nonneg_inventory_currently_blocked_at_lexing() {
    expect_compile_error(include_str!("program.cambra"), "invalid token");
}
