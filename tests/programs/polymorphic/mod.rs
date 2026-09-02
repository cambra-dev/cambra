//! Let-polymorphism and the monomorphization fan-out. `dup` is used at two
//! distinct types, so inference specializes it into two clones.
//!
//! The pre-inference body `(x, x)` carries a hole that resolves downstream to a
//! *set* of tuple types (`Int` and `Bool`); that fan-out is what makes the
//! inspector's `paneLinks` carry a non-identity edge, pinned by the
//! `polymorphic` snapshot fixture.

use super::common::expect_scalar;

#[test]
fn polymorphic() {
    expect_scalar(include_str!("program.cambra"), "(1, 1)");
}
