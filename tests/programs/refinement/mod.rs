use super::common::expect_compile_error;

#[test]
fn refinement() {
    expect_compile_error(
        include_str!("nested_refinement.cambra"),
        "expected {{Int | __elem != 1} | __elem != 0}",
    );
}
