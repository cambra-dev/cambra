//! Total each region's large sales, with the filter inside the per-group
//! comprehension.
//!
//! The filter refines the *inner* collection's domain, so the surviving elements
//! differ per group. `Restrict` and `Filter` narrow a single domain and cannot reach
//! inside a partition, so this compiles through `MapFilter`
//! (`src/interpreter/tile_operators/combinators.rs`), which planning inserts at the
//! site where a morphism's codomain refines the collection its domain carries
//! (`src/ccl/planning/map_filter.rs`).
//!
//! No sale in `north` passes the filter, so its group survives the filter holding
//! nothing and `sum` over it answers the identity. Reaching that answer takes a group
//! holding nothing to be representable: two equal `row_starts` are a key whose group is
//! empty (`Tile::DataFunction`), which the filter leaves in place rather than dropping the
//! key and the region with it.
//!
//! That row is also what separates this program from filtering before the group —
//! `[s for s in sales if s.qty > 2]`, then `groupby`. The two agree on every region
//! that keeps a sale, and `north` is in one and not the other: a group the filter
//! empties still has a key, while a region with no surviving sale never partitions.
//! Pre-filtering needs none of this machinery either, its predicate being closed.

use super::common::expect_scalar;

#[test]
fn groupby_filtered_rollup() {
    expect_scalar(
        include_str!("program.cambra"),
        r#"Function [ "east" -> 150, "north" -> 0, "south" -> 75, "west" -> 200 ]"#,
    );
}
