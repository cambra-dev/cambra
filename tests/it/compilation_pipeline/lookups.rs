use indoc::indoc;
use rstest_log::rstest;

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

/// A nominal type whose instance of `Indexable` states its `Entries`: a subscript reads the
/// function the instance's `entries` answers (`docs/chl-spec.md`, "Subscript and unwrap syntax").
const ROW: &str = indoc! {"
    type Row(D) = D |=> Int
    instance forall (D) Indexable(Row(D)):
        Entries = D |=> Int
        def entries(r):
            r.extract()
"};

/// A checked lookup into a type with a declared instance answers from its `Entries`.
#[rstest]
#[case::a_present_key("r[int_to_uint(1)] == Option::some(20)")]
#[case::an_absent_key("r[int_to_uint(5)] == Option::none")]
fn a_checked_lookup_reads_a_declared_instance(#[case] lookup: &str) {
    check_scalar(
        &format!("{ROW}\nr = Row::new([10, 20, 30])\n{lookup}"),
        Value::Bool(true),
    )
}

/// A proven lookup into a type with a declared instance proves its key against the domain of
/// the instance's `Entries` at the type's arguments.
#[test]
fn a_proven_lookup_proves_its_key_against_a_declared_instance() {
    check_compile_error(
        &format!("{ROW}\nr = Row::new([10, 20, 30])\nr[int_to_uint(5)]! == 20"),
        "Type mismatch for Apply: expected 0..3, found {UInt | (__int, __elem) ▷ int_eq_uint}",
    )
}

/// A subscript requires `Indexable` of its collection's type, which a nominal type without an
/// instance lacks.
#[test]
fn a_type_without_an_indexable_instance_is_not_subscripted() {
    check_compile_error(
        "type Box = Int\nBox::new(3)[int_to_uint(0)]",
        "No Indexable instance for Indexable::entries: operand 1 is Box",
    )
}
