//! Two reads of one data source. `stdin()` appears twice, so conversion builds
//! two `MapResultWithSource` readers — but a source is one registered thing, so
//! the operator graph carries one `Source(stdin)` node that both readers share,
//! attributed to both read sites.
//!
//! `streaming_echo` and `fanout` also read a source, but each reads it once, so
//! neither reaches the sharing this program is here for. The wire side is
//! pinned by the `source_shared` snapshot fixture and by
//! `a_source_read_twice_is_one_node_attributed_to_both_reads` in
//! `tests/inspector_goldens.rs`.
//!
//! Tested through a subprocess for the same reason `streaming_echo` is: the
//! in-process path would have to replace the real `StdinDataSource` and so
//! would dodge the file descriptor being exercised.

use super::common::expect_stdin_program;

#[test]
fn source_shared() {
    expect_stdin_program(
        "source_shared",
        "hello\nworld\n",
        &["> hello", "> world", "hello!", "world!"],
    );
}
