//! Stream stdin lines back out with a "> " prefix — minimal demo of the
//! `stdin()` source.
//!
//! Tested via a subprocess pipeline (`expect_stdin_program`) so we drive
//! the real OS stdin file descriptor.  An in-process test with a
//! `TestDataSource` override would dodge exactly the thing we want to
//! exercise.

use super::common::expect_stdin_program;

#[test]
fn streaming_echo() {
    expect_stdin_program("streaming_echo", "hello\nworld\n", &["> hello", "> world"]);
}
