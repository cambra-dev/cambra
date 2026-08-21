use crate::helpers::{check_compile_error, check_scalar};

use cambra::interpreter::Value;

#[test]
fn refinement() {
    check_compile_error(
        include_str!("type_annotations/refined_div_zero.cambra"),
        "expected {Int | __elem != 0}",
    );
    check_compile_error(
        include_str!("type_annotations/complex_refinement.cambra"),
        "expected {{x: Int, y: Int} | __elem.y != 0}, found {x: Int@1, y: Int@0}",
    );
    check_scalar(
        include_str!("type_annotations/underscore.cambra"),
        Value::Int(3),
    )
}

#[test]
fn output_annotation_base() {
    check_scalar(
        "
def foo(a: Int, b: Int) => Int:
    a + b

x = (4,-1)

foo(x)
",
        Value::Int(3),
    )
}

#[test]
fn output_annotation_base_neg() {
    check_compile_error(
        "
def itsa_five(a) => String:
    5

itsa_five(\"dummy_arg\")
",
        "Annotation mismatch: annotated as String, but inferred as Int@5",
    )
}

#[test]
fn output_annotation_ref1() {
    check_scalar(
        "
def itsa_nine(a) => {Int where _ == 9}:
    9

itsa_nine(\"dummy_arg\")
",
        Value::Int(9),
    )
}

#[test]
fn output_annotation_ref2() {
    check_compile_error(
        "
def itsa_nine(a) => {Int where _ == 9}:
    8

itsa_nine(\"dummy_arg\")
",
        "Annotation mismatch: annotated as Int@9, but inferred as Int@8",
    )
}

#[test]
fn function_type_annotation() {
    // A binding annotated with a function type `(Int => Int)` checks against the
    // lambda it binds (a lambda is a compute function, the kind `=>` denotes).
    check_scalar(
        "
f: (Int => Int) = \\x -> x + 1
f(4)
",
        Value::Int(5),
    )
}

#[test]
fn function_type_annotation_refined_codomain() {
    // A refinement nested in the codomain is a `Bool` predicate over `_`, typed
    // through `Type::Fun` like any other annotation refinement. The body `9` is
    // `Int@9`, which discharges `{Int where _ == 9}`.
    check_scalar(
        "
f: (Int => {Int where _ == 9}) = \\x -> 9
f(4)
",
        Value::Int(9),
    )
}

#[test]
fn function_type_annotation_refined_codomain_neg() {
    // The codomain refinement is enforced: a body of `8` does not satisfy
    // `{Int where _ == 9}`.
    check_compile_error(
        "
f: (Int => {Int where _ == 9}) = \\x -> 8
f(4)
",
        "Annotation mismatch",
    )
}

#[test]
fn function_type_in_value_position_is_rejected() {
    // `T => U` names a type; it is annotation-only, not a value.
    check_compile_error(
        "
x = Int => Int
x
",
        "is a function *type*",
    )
}

// This test fails because the output of _ + _ is currently unrefined.
// Once that is fixed, it should fail for the different reason that
// the argument b is not >= 0.
#[test]
fn output_annotation_ref3() {
    check_compile_error(
        "
def sum_up(a: Int, b: {Int where _ >= 0}) => {Int where _ >= a}:
    a + b

x = (3,-1)

sum_up(x)
",
        "Annotation mismatch: annotated as {Int | __elem >= __arg_tuple_0.0}, but inferred as Int",
    )
}
