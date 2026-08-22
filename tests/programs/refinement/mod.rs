use super::common::expect_compile_error;

#[test]
fn refinement() {
    expect_compile_error(
        include_str!("nested_refinement.cambra"),
        // The two written refinement levels are one refinement set, so the diagnostic
        // names both refinements at one base rather than a nesting.
        "expected {Int | __elem != 0, __elem != 1}",
    );
}
