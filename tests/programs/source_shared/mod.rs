//! Two reads of one data source. `stdin()` appears twice, so conversion builds
//! two `MapResultWithSource` readers. A source is not a node of the operator
//! graph: each reader reads from an input-free `IterateExtent` over the
//! source's domain, whose tiling names `Source(stdin)`.
//!
//! `streaming_echo` and `fanout` also read a source, but each reads it once, so
//! neither reaches the two reads of one source this program is here for. The wire side is
//! pinned by the `source_shared` case in `web/src/wireValidate.test.ts`.
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
