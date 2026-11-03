use indoc::indoc;

use super::helpers::{check_compile_error, check_scalar};

use cambra::interpreter::Value;

/// `int_to_uint`'s result is refined by `int_eq_uint` to equal its argument, so the solver
/// proves two conversions of one `Int` equal. CHL has no `UInt` literal, so the bound is a name.
#[test]
fn int_to_uint_result_equals_its_argument() {
    check_scalar(
        indoc! {r#"
z = int_to_uint(1)
y: {UInt where _ == z} = int_to_uint(1)
y == z
        "#},
        Value::Bool(true),
    )
}

#[test]
fn int_to_uint_of_a_different_int_is_not_equal() {
    check_compile_error(
        indoc! {r#"
z = int_to_uint(1)
y: {UInt where _ == z} = int_to_uint(2)
y
        "#},
        "Annotation mismatch",
    )
}

#[test]
fn int_to_uint_takes_an_int() {
    check_compile_error("int_to_uint(\"one\")", "Type mismatch")
}

#[test]
fn int_to_uint_takes_one_argument() {
    check_compile_error(
        "int_to_uint(1, 2)",
        "`int_to_uint` takes exactly one argument",
    )
}

/// No `UInt` equals a negative `Int`, so the conversion stops execution rather than produce a
/// value its refinement does not admit.
#[test]
#[should_panic(expected = "int_to_uint applied to the negative Int -1")]
fn int_to_uint_of_a_negative_int_panics() {
    check_scalar("int_to_uint(0 - 1)", Value::UInt(0))
}

/// TODO: Compare UInt to UIntRange. Should compile and eval to
/// Bool::true when that is done.
#[test]
fn list_lookup_checked_some() {
    check_compile_error(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(1)] == Option::some(2)
        "#},
        "Type mismatch for checked lookup key: expected 0..3, found UInt",
    )
}

/// TODO: Compare UInt to UIntRange. Should compile and eval to
/// Bool::true when that is done.
#[test]
fn list_lookup_checked_negative() {
    check_compile_error(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(3)] == Option::none
        "#},
        "Type mismatch for checked lookup key: expected 0..3, found UInt",
    )
}

/// TODO: Compare UInt to UIntRange. Should compile and eval to
/// Bool::true when that is done.
#[test]
fn list_lookup_proven() {
    check_compile_error(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(1)]! == 2
        "#},
        "Type mismatch for Apply: expected 0..3, found UInt",
    )
}

/// TODO: Compare UInt to UIntRange. Should type-error, expecting 0..3 and finding UInt@5, when that is done.
#[test]
fn list_lookup_rejected() {
    check_compile_error(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(5)]! == 2
        "#},
        "Type mismatch for Apply: expected 0..3, found UInt",
    )
}
