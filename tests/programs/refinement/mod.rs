use super::common::{expect_compile_error, expect_scalar};

#[test]
fn refinement() {
    expect_compile_error(include_str!("refined_div_zero.cambra"), "expected {Int | __elem != 0}");
    expect_compile_error(include_str!("nested_refinement.cambra"), "expected {{Int | __elem != 1} | __elem != 0}");
    expect_compile_error(include_str!("complex_refinement.cambra"), "expected {{x: Int, y: Int} | __elem.y != 0}, found {x: 1, y: 0}");
    expect_scalar(include_str!("underscore.cambra"), "3");

}

#[test]
fn refinement_args_pos() {
    // Refinements on later args should be able to reference previous
    // args.  Here, the y refinement can use x.
    expect_scalar("def foo(x: Int, y: { Int where _ < x }):\n    x\n1", "1");
}

#[test]
fn refinement_args_neg() {
    // This should cause type-checking to error due to the unbound "z"
    // in the refinement of y.
    expect_compile_error("def foo(x: Int, y: { Int where _ < z }):\n    x\n3", "[should say something like 'z is unbound']");
}

#[test]
fn refinement_args_neg_2() {
    // This should cause type-checking to error due to the unbound "z"
    // in the refinement of x.
    expect_compile_error("y: Int = 3\nx: { Int where z > y } = 1\nx", "[should say something like 'z is unbound']");
}
