//! A polymorphic sink constructor — *not* Unix `tee`.  `fanout` returns the
//! writable head of a fan-out pipe: each element fed to the head is
//! duplicated to both downstream sinks.  Polymorphic in the element type with
//! no explicit type parameters (the inner `_`s on `Feed(_)` unify through
//! inference).  Exercises `Feed(_)` types, `<<` feed, and an annotation-only
//! forward declaration (`h: Feed(_)` with no initializer).
//!
//! **Currently blocked.**  `Feed` isn't a supported type constructor yet
//! (type application resolves `List`, `Mut`; `Feed(_)` is rejected), and the
//! annotation-only forward declaration doesn't parse.  This pins the
//! unsupported-`Feed`-type failure.

use super::common::expect_compile_error;

#[test]
fn fanout_currently_blocked() {
    expect_compile_error(
        include_str!("program.cambra"),
        "unknown type application: `Feed(…)`",
    );
}
