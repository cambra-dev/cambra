//! Group sales records by region and report the per-region total —
//! the canonical "group by + per-group aggregate" shape.
//!
//! **Currently blocked.**  The natural form
//! `[sum([s.amount for s in g]) for g in groupby(sales, lambda r: r.region)]`
//! — i.e. groupby over records with a projecting inner comprehension —
//! panics during operator conversion because the `curry` combinator isn't
//! yet supported there.  Tracks completing `curry` combinator support in
//! `operator_conversion`.
//!
//! Expected output once unblocked (sorted by key):
//! `Function [ "east" -> 200, "south" -> 75, "west" -> 300 ]`.

use super::common::expect_compile_error;

#[test]
fn groupby_rollup_currently_blocked() {
    expect_compile_error(
        include_str!("program.cambra"),
        "found input for non-combinator curry",
    );
}
