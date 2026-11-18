//! A returned Feed read is collection data and cannot be used as a contribution target.
//! `a_module_feed_fans_out` covers module input functions and collection outputs.

use super::common::expect_compile_error;

#[test]
fn a_function_cannot_return_a_fanout_head() {
    expect_compile_error(include_str!("program.cambra"), "feed target");
}
