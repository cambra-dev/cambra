//! Group sales records by region and report the per-region total —
//! the canonical "group by + per-group aggregate" shape.
//!
//! The projecting inner comprehension
//! `[sum([s.amount for s in g]) for g in groupby(sales, \r -> r.region)]`
//! reaches operator conversion only through the exponential-eta rule in
//! `src/ccl/simplify.rs`: λ-elimination closes `s.amount` over both the group
//! and the element and re-splits it with `curry`, which operator conversion has
//! no arm for.

use super::common::expect_scalar;

#[test]
fn groupby_rollup() {
    expect_scalar(
        include_str!("program.cambra"),
        r#"Function [ "east" -> 200, "south" -> 75, "west" -> 300 ]"#,
    );
}
