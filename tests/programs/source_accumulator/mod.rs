//! Accumulate stdin lines into a loop-carried mutable variable — the gallery's
//! one program that joins a store to a data source.
//!
//! Driven through a subprocess pipeline (`expect_stdin_program`) like
//! `streaming_echo`, so the real OS stdin file descriptor is exercised and the
//! accumulator settles at EOF rather than on a `TestDataSource` the program
//! never sees.
//!
//! Its operator graph is what `tests/inspector_goldens.rs` asserts: the loop's
//! induction extent is the source's domain, so two `IterateExtent`s read the one
//! source node — the chain that reads the source's values, and the
//! `StoreDenseRead` trigger that folds the accumulator over the same extent.
//! Every other source program in the gallery has only the first.

use super::common::expect_stdin_program;

#[test]
fn source_accumulator_collects_every_line() {
    expect_stdin_program("source_accumulator", "hello\nworld\n", &["hello;world;"]);
}
