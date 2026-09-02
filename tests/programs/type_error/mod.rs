//! A deliberate type error: `and` wants `Bool` operands and gets `Int`s.
//!
//! The corpus's one failing program. It is what gives the inspector a degraded
//! payload to serve — source and diagnostics with empty panes and
//! `meta.payloadKind: "failed"` — pinned by the `failed` snapshot fixture.

use super::common::expect_compile_error;

#[test]
fn type_error_is_rejected() {
    expect_compile_error(
        include_str!("program.cambra"),
        "Type mismatch for BinOp: expected Bool, found Int",
    );
}
