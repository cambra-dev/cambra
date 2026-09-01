//! The analytical mart and the archive, which are the two halves of an ETL path
//! and are not the same kind of thing.
//!
//! The mart is a rollup over the same feed the operational endpoint writes,
//! keyed by day.  There is no pipeline between them because there is no
//! boundary between them, so the outbox, topic, consumer, and loader a
//! conventional stack spends lines on have no counterpart here.  That saving is
//! architectural rather than syntactic, and `docs/REPORT.md` argues both sides
//! of it.
//!
//! The archive is the half that does cross a boundary, and it is the half
//! Cambra cannot write: retention, cold storage, and a reader that is not this
//! program are requirements an in-program view does not meet.  `store.parquet`
//! is therefore a gap, not a saving.
//!
//! **Blocked at lowering**, pinned on the archive sink constructor: a call in
//! method position is not a named function call.  Two further gaps this program
//! owns have no decided surface — an object-storage sink with a partition
//! function, and arithmetic on `Time` (`clock.day`), which today is only a
//! position in the commit order with no algebra
//! (`docs/chl-spec.md`, "6. Types (informal sketch)").  Behind them, shared
//! with the rest of the corpus: `import`, `Feed(…)` declarations, the map
//! comprehension `[k -> v for …]`, and `k -> g` entry-pair iteration of a
//! `groupby` result.

use super::common::expect_compile_error;

#[test]
fn warehouse_export_currently_blocked_at_lowering() {
    expect_compile_error(
        include_str!("program.cambra"),
        r#"store.parquet("s3://warehouse/order-lines", \o -> clock.day(o.time))"#,
    );
}
