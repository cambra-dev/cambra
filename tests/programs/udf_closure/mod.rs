//! A UDF called once, closing over an outer binding — the smallest program in
//! which a call site and a free variable meet.
//!
//! The inspector's canary: its committed snapshot fixture (`arithmetic`) pins
//! the whole wire byte-for-byte, so every `Lit` carrying `: Int` and every
//! `BinOp` showing operator dispatch is checked there.

use super::common::expect_scalar;

#[test]
fn udf_closure() {
    expect_scalar(include_str!("program.cambra"), "13");
}
