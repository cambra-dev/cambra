//! The canonical streaming-pipeline shape: transform each element of a
//! string list with a constant prefix.

use super::common::expect_scalar;

#[test]
fn prefix_lines() {
    expect_scalar(
        include_str!("program.cambra"),
        r#"Function [ "> hello", "> world" ]"#,
    );
}
