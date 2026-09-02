//! One lambda applied at four sites, three at `Int` and one at `Bool` — the two
//! duplication mechanisms in one program.
//!
//! Inference specializes `dup` per type, so the two argument types make two
//! clones; `inline` then duplicates each specialization's body per call site,
//! and the `Int` specialization has three of them — one copy keeps the input
//! ids, the rest are freshened `Replicated` copies tagged `Derived { via:
//! Inline }`. Both fan-outs land in the `post-inference → post-channelize`
//! `paneLinks` window as non-identity edges, pinned whole by the `polymorphic`
//! snapshot fixture and asserted structurally by
//! `tests/inspector_goldens.rs`.

use super::common::expect_scalar;

#[test]
fn polymorphic() {
    expect_scalar(include_str!("program.cambra"), "(1, 1)");
}
