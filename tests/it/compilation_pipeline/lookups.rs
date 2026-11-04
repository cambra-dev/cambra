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

/// A checked lookup's key is bounded by the range's base, `UInt`, so a key inside the range
/// answers `some`.
#[test]
fn list_lookup_checked_some() {
    check_scalar(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(1)] == Option::some(2)
        "#},
        Value::Bool(true),
    )
}

/// A key outside the range types as a `UInt` and answers `none`.
#[test]
fn list_lookup_checked_negative() {
    check_scalar(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(3)] == Option::none
        "#},
        Value::Bool(true),
    )
}

/// The key's refinement entails the bound `__elem < 3`, so `{UInt | …} <: 0..3` holds.
#[test]
fn list_lookup_proven() {
    check_scalar(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(1)]! == 2
        "#},
        Value::Bool(true),
    )
}

/// The key's refinement refutes the bound, so the proven lookup is rejected.
///
/// TODO: Improve the confusing type error. The type `{UInt | (__int,
/// __elem) ▷ int_eq_uint}` is asserting that the key is equal to the
/// Int passed into `int_to_uint`, namely `5`.  But that's not obvious.
#[test]
fn list_lookup_rejected() {
    check_compile_error(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(5)]! == 2
        "#},
        "Type mismatch for Apply: expected 0..3, found {UInt | (__int, __elem) ▷ int_eq_uint}",
    )
}
