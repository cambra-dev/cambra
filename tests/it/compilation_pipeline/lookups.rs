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

/// The key's refinement refutes the bound, so the proven lookup is rejected. The key's type
/// is `int_to_uint`'s result at the argument `5`.
#[test]
fn list_lookup_rejected() {
    check_compile_error(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(5)]! == 2
        "#},
        "Type mismatch for this call: expected {UInt where _ < 3}, found {UInt where 5 == _}",
    )
}

/// A checked lookup's result is refined by whether the key is present:
/// `{Option(Int) where (k < int_to_uint(3) and not _.is_none()) or (not k < int_to_uint(3) and
/// _.is_none())}`, with `k < int_to_uint(3)` read off `xs`'s domain `0..3`. `k`'s refinement
/// entails it, so the result is `some` and `!` accepts it.
#[test]
fn a_checked_lookup_at_a_present_key_is_some() {
    check_scalar(
        indoc! {r#"
xs = [1,2,3]
k = int_to_uint(1)
r = xs[k]
r!
        "#},
        Value::Int(2),
    )
}

/// `k`'s refinement refutes `k < 3`, so the result is `none`.
#[test]
fn a_checked_lookup_at_an_absent_key_is_none() {
    check_scalar(
        indoc! {r#"
xs = [1,2,3]
k = int_to_uint(3)
r: {Option(Int) where _.is_none()} = xs[k]
r.is_none()
        "#},
        Value::Bool(true),
    )
}

/// `!` demands `some` of a lookup at an absent key, which its refinement refutes.
#[test]
fn unwrapping_a_checked_lookup_at_an_absent_key_is_rejected() {
    check_compile_error(
        indoc! {r#"
xs = [1,2,3]
k = int_to_uint(3)
r = xs[k]
r!
        "#},
        "found {Option(Int) where (k < int_to_uint(3) and not _.is_none() or not k < int_to_uint(3) and _.is_none())}",
    )
}

/// The `some` branch states `xs`'s codomain refinement `_ > 0` of `_.value()`, so the payload of
/// a lookup at a present key meets it.
#[test]
fn a_checked_lookup_payload_meets_the_codomain_refinement() {
    check_scalar(
        indoc! {r#"
n = int_to_uint(3)
xs: {UInt where _ < n} |=> {Int where _ > 0} = [1,2,3]
k = int_to_uint(1)
r = xs[k]
v: {Int where _ > 0} = r!
v
        "#},
        Value::Int(2),
    )
}

/// The codomain's `_ > 0` is all the refinement states about the payload, so `_ > 1` is not
/// proven although the payload at `k` is `2`.
#[test]
fn a_checked_lookup_payload_is_known_only_through_the_codomain_refinement() {
    check_compile_error(
        indoc! {r#"
n = int_to_uint(3)
xs: {UInt where _ < n} |=> {Int where _ > 0} = [1,2,3]
k = int_to_uint(1)
r = xs[k]
v: {Int where _ > 1} = r!
v
        "#},
        "Annotation mismatch",
    )
}
