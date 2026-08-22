//! Total each region's large sales — `SELECT region, SUM(amount) … WHERE qty > 2
//! GROUP BY region`, with the filter inside the per-group comprehension.
//!
//! The filter refines the *inner* collection's domain, so the surviving elements
//! differ per group. `Restrict` and `Filter` narrow a single domain and cannot reach
//! inside a partition, so this compiles through `MapFilter`
//! (`src/interpreter/tile_operators/combinators.rs`), which planning inserts at the
//! site where a morphism's codomain refines the collection its domain carries
//! (`src/ccl/planning/map_filter.rs`).
//!
//! Filtering before the group instead — `[s for s in sales if s.qty > 2]`, then
//! `groupby` — is a different program with the same answer here, and it needs none
//! of this: its predicate is closed, so the refinement lands on a let-bound
//! collection's own domain and `wrap_with_iterate` materialises it.

use super::common::expect_scalar;

#[test]
fn groupby_filtered_rollup() {
    expect_scalar(
        include_str!("program.cambra"),
        r#"Function [ "east" -> 150, "south" -> 75, "west" -> 200 ]"#,
    );
}
