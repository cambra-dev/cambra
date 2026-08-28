use rstest::rstest;

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

// The refinement body in the output type of `test` should be well
// typed, refering only to `x` which is in its scope.
//
// Currently the test still fails afterward, since `x + 1` does not
// get refined.
#[test]
fn pi_type_scope() {
    check_compile_error(
        "
def test(x: Int) => {Int where _ > x}:
    x + 1

()
",
        "Annotation mismatch: annotated as {Int | __elem > x}, but inferred as Int",
    )
}

// The refinement body in the output type of `test` should fail to
// type, since it refers to `y` which is unbound.
#[test]
fn type_scope_neg() {
    check_compile_error(
        "
def test(x: Int) => {Int where _ > y}:
    x + 1

()
",
        "type inference: Unbound variable: 'y'",
    )
}

// The refinement body in the output type of `test` should be well
// typed, refering to `x` which is in its scope from the input
// argument, and to `y` which is in the outer scope. The body of `x`'s
// refinement can also refer to `y`.
//
// Currently the test still fails afterward, since `x + 3` does not
// get refined.
#[test]
fn type_scope_outer() {
    check_compile_error(
        "
y = 3

def test(x: {{Int where _ != y + y} where _ != y}) => {Int where _ > y + x}:
    x + 3

()
",
        "Annotation mismatch: annotated as {Int | __elem > y + x}, but inferred as Int",
    )
}

#[test]
fn type_refined_input_only1() {
    check_scalar(
        "
def f(x: {Int where True}) => Int:
    x
()
",
        Value::Unit,
    )
}

#[test]
fn type_refined_input_only2() {
    check_scalar(
        "
def f(x: {Int where _ >= _}) => Int:
    x
()
",
        Value::Unit,
    )
}

#[test]
fn type_refined_input_only3() {
    check_scalar(
        "
def f(y: Int, x: {Int where _ == _}):
    x
()
",
        Value::Unit,
    )
}

#[test]
fn type_refined_input_only4() {
    check_scalar(
        "
def f(x: {Int where _ == _}):
    x
()
",
        Value::Unit,
    )
}

// This should succeed eventually, but fails for now since refinements
// are only compared by equality.
#[test]
fn type_refined_input_output() {
    check_compile_error(
        "
def f(x: {Int where _ == _}) => {Int where _ == x}:
    x
()
",
        "Annotation mismatch: annotated as {Int | __elem == x}, but inferred as {Int | __elem == __elem}",
    )
}

// This should succeed eventually, but fails for now since refinements
// are only compared by equality.
#[test]
fn type_refined_output() {
    check_compile_error(
        "
def f(x: Int) => {Int where _ == x}:
    x
()
",
        "Annotation mismatch: annotated as {Int | __elem == x}, but inferred as Int",
    )
}

// The refinement body for `x` should fail to typecheck, since it
// should not be able to refer to itself by `x`, only by `_`.
#[test]
fn type_scope_self() {
    check_compile_error(
        "
def test(x: {Int where x >= 1}) => Int:
    x + 1

()
",
        "type inference: Unbound variable: 'x'",
    )
}

// The refinement body for `x` should fail to typecheck, since the `x`
// inside is refering to the outer scope `x`, which is a `String`.
#[test]
fn type_scope_outer_shadow() {
    check_compile_error(
        "
x = \"Hello\"

def test(x: {Int where _ >= x}) => Int:
    x + 1

()
",
        "No Orderable instance for BinOp: operand 2 is String",
    )
}

#[test]
fn type_binop_mismatch() {
    check_compile_error(
        "
def test(a: String, b: Int):
    a + b

()
",
        "No Addable instance for BinOp: operand 2 is Int, but the only type accepted there is String",
    )
}

/// A parameter's annotation is read in the scope enclosing the binder, so a
/// reference to a parameter resolves outward and not to the parameter. With
/// nothing outside to resolve to it is an ordinary unbound variable, at every
/// shape a parameter list takes: tupled siblings in either order, and the
/// single parameter that can only be naming itself.
///
/// Nothing rejects these earlier. Lowering carries no scope to tell a reference
/// to the parameter apart from one to an enclosing binder of the same name, and
/// a name-based rejection there reports the wrong cause for the shadowing case
/// (`type_scope_outer_shadow`).
#[rstest]
#[case::sibling("def f(a: Int, c: {Int where _ >= a}):\n    c\n\nf\n", "a")]
#[case::sibling_reversed("def f(c: {Int where _ >= a}, a: Int):\n    c\n\nf\n", "a")]
#[case::sibling_of_three("def f(a: Int, b: Int, c: {Int where _ >= b}):\n    c\n\nf\n", "b")]
#[case::own_binder("def f(a: {Int where _ >= a}):\n    a\n\nf\n", "a")]
fn type_annotation_naming_a_parameter_is_unbound(#[case] code: &str, #[case] name: &str) {
    check_compile_error(code, &format!("type inference: Unbound variable: '{name}'"));
}

#[test]
fn refined_add() {
    check_scalar("z: {Int where _ == 1 ^+ 3} = 1 ^+ 3\n()", Value::Unit)
}

#[test]
fn refined_add_let() {
    check_scalar(
        "
def foo(t: Int) => {Int where _ == 1 ^+ 3}:
    x = 1 ^+ 3
    y = x ^+ 2
    y
()
",
        Value::Unit
    )
}

#[test]
fn refined_add_let2() {
    check_scalar(
        "
def foo(t: Int):
    x = t ^+ 3
    x ^+ 2
foo(1)
",
        Value::Int(6)
    )
}

#[test]
fn refined_add_let3() {
    check_scalar(
        "
def foo(t: Int):
    x = 1 ^+ 3
    x
foo(1)
",
        Value::Int(4)
    )
}

#[test]
fn refined_add_let4() {
    check_scalar(
        "
def bar(i: Int):
    i // 2

def foo(t: Int):
    x = bar(t)
    x ^+ 2
foo(2)
",
        Value::Int(3)
    )
}
