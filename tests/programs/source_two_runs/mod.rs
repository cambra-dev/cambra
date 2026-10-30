//! Two runs of a module that reads `stdin()`. The context holds stdin as one
//! source, and each run's read subscribes to it, so both runs receive every
//! line: `a` and `b` each tag both piped lines.
//!
//! `source_shared` reads stdin twice in one module; this program reads it once
//! in each of two runs of a module. `two_runs_of_a_module_each_read_all_of_its_source`
//! in `tests/it/compilation_pipeline/runs.rs` pins the same claim in-process
//! over a `TestDataSource`.
//!
//! Tested through a subprocess for the same reason `source_shared` is: the
//! in-process path would have to replace the real `StdinDataSource`.

use super::common::expect_stdin_program;

#[test]
fn source_two_runs() {
    expect_stdin_program(
        "source_two_runs",
        "hello\nworld\n",
        &["a hello", "a world", "b hello", "b world"],
    );
}
