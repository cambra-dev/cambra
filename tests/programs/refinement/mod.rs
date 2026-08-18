use super::common::{expect_compile_error, expect_scalar};

#[test]
fn refinement() {
    expect_compile_error(include_str!("refined_div_zero.cambra"), "expected {Int | __elem != 0}");
    expect_compile_error(include_str!("nested_refinement.cambra"), "expected {{Int | __elem != 1} | __elem != 0}");
    expect_compile_error(include_str!("complex_refinement.cambra"), "expected {{x: Int, y: Int} | __elem.y != 0}, found {x: 1, y: 0}");
    expect_scalar(include_str!("underscore.cambra"), "3")
}
