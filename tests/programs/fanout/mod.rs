//! A polymorphic sink constructor — *not* Unix `tee`.  `fanout` returns the
//! writable head of a fan-out pipe: each element fed to the head is
//! duplicated to both downstream sinks.  Polymorphic in the element type with
//! no explicit type parameters (the inner `_`s on `Feed(_)` unify through
//! inference).  Exercises `Feed(_)` types, `<<` feed, and an annotation-only
//! forward declaration (`h: Feed(_)` with no initializer).
//!
//! **Currently blocked.**  `Feed(_)` isn't a supported type-annotation form
//! yet, and the forward declaration doesn't parse.  This pins the
//! unsupported-annotation failure.

use super::common::expect_compile_error;

#[test]
fn fanout_currently_blocked() {
    expect_compile_error(
        include_str!("program.cambra"),
        "unsupported type annotation form",
    );
}
