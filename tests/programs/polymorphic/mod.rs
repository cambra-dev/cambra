//! Let-polymorphism and the monomorphization fan-out. `dup` is used at two
//! distinct types, so inference specializes it into two clones and `inline`
//! duplicates each specialization's body at its call site.
//!
//! The pre-inference body `(x, x)` carries a hole that resolves downstream to a
//! *set* of tuple types (`Int` and `Bool`); that fan-out is what makes the
//! inspector's `paneLinks` carry non-identity edges in both the
//! `pre-inference → post-inference` and `post-inference → post-channelize`
//! windows, pinned whole by the `polymorphic` snapshot fixture and asserted
//! structurally by `tests/inspector_goldens.rs`.

use super::common::expect_scalar;

#[test]
fn polymorphic() {
    expect_scalar(include_str!("program.cambra"), "(1, 1)");
}
