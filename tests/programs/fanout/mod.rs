//! A polymorphic sink constructor — *not* Unix `tee`.  `fanout` returns the
//! writable head of a fan-out pipe: each element fed to the head is
//! duplicated to both downstream sinks.  Polymorphic in the element type with
//! no explicit type parameters (the inner `_`s on `Feed(_)` unify through
//! inference).  Exercises `Feed(_)` types, `<<` feed, and an annotation-only
//! forward declaration (`h: Feed(_)` with no initializer).
//!
//! **Currently blocked at `open`.**  No file sink exists yet, and neither does
//! `stdout`.  The fan-out itself compiles: with declared feeds in place of the two
//! sinks it is `a_feed_returned_by_a_function_fans_out` in
//! `tests/it/compilation_pipeline/feeds_cases.rs`.  This pins the missing `open`.

use super::common::expect_compile_error;

#[test]
fn fanout_currently_blocked() {
    expect_compile_error(include_str!("program.cambra"), "Unbound variable: 'open'");
}
