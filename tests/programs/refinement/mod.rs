//! Two written refinement levels over one base, at an argument that violates
//! one of them.

use super::common::expect_compile_error;

#[test]
fn an_argument_violating_a_level_is_rejected() {
    expect_compile_error(
        include_str!("nested_refinement.cambra"),
        // The two written refinement levels are one refinement set, which CHL writes as one
        // `where` per refinement.
        "expected {{Int where _ != 0} where _ != 1}",
    );
}
