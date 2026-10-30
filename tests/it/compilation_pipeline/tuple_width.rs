//! A tuple's width is part of its type, and an open tuple `{A, ..}` is a bound that fixes
//! none (`docs/chl-spec.md`, "Tuple width").

use std::time::Duration;

use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use super::helpers::{check_compile_error, check_scalar};
use super::modules::compile_errors;

#[rstest]
#[timeout(Duration::from_secs(10))]
// A projection requires positions, not a width, so a definition reading one is generic
// over the width each call fixes.
#[case::a_projection_fixes_no_width(
    indoc! {"
        def first(t):
            t.0
        first((1, 2)) + first((10, 20, 30))
    "},
    Value::Int(11),
)]
#[case::an_open_bound_on_a_parameter(
    indoc! {"
        def first(A, t <: {A, ..}) => A:
            t.0
        first((1, 2)) + first((10, 20, 30))
    "},
    Value::Int(11),
)]
#[case::an_open_bound_on_a_type_parameter(
    indoc! {"
        def second(T <: {Int, Int, ..}, t: T) => Int:
            t.1
        second((1, 2)) + second((1, 20, 3))
    "},
    Value::Int(22),
)]
// The binding keeps its value's own type, so a position past the bound's is readable.
#[case::an_open_bound_on_a_binding(
    indoc! {r#"
        x <: {Int, ..} = (1, "a", 3)
        x.2
    "#},
    Value::Int(3),
)]
#[case::an_open_tuple_as_a_tuple_component(
    indoc! {"
        def f(t <: {{Int, ..}, Int}) => Int:
            t.0.0 + t.1
        f(((1, 2, 3), 4))
    "},
    Value::Int(5),
)]
#[case::an_open_tuple_as_a_record_field(
    indoc! {"
        def f(r <: {p: {Int, ..}}) => Int:
            r.p.0
        f((p=(5, 6)))
    "},
    Value::Int(5),
)]
// `A` is in no value parameter's annotation, but in the bound of `T`, which is, so each
// call determines it.
#[case::a_parameter_named_by_an_open_bound(
    indoc! {"
        def tag_first(A, T <: {A, ..}, t: T) => {A, T}:
            (t.0, t)
        p = tag_first((1, 2, 3))
        p.0 + p.1.2
    "},
    Value::Int(4),
)]
// A type parameter's bound is an open tuple only as a whole, so a nested one bounds a type
// parameter of its own, which each call determines through the bound naming it.
#[case::a_nested_open_tuple_behind_a_type_parameter(
    indoc! {"
        def f(B <: {Int, ..}, T <: {B, Int}, t: T) => Int:
            t.0.0 + t.1
        f(((1, 2, 3), 4)) + f(((10,), 20))
    "},
    Value::Int(35),
)]
#[case::an_open_result_behind_a_type_parameter(
    indoc! {"
        def mk(B <: {Int, ..}, F <: Int => B, f: F) => Int:
            f(1).0
        mk(\\x -> (x, x)) + mk(\\x -> (x, 2, 3))
    "},
    Value::Int(2),
)]
// Named, the inner tuple can be the result, at the width the argument has.
#[case::a_named_inner_tuple_keeps_its_width(
    indoc! {"
        def inner(B <: {Int, ..}, R <: {p: B}, r: R) => B:
            r.p
        inner((p=(5, 6, 7))).2
    "},
    Value::Int(7),
)]
fn open_tuples_check_and_run(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// An open tuple is written only after `<:`, where it stays on the right of the check: as
/// the bound, or a tuple or record component or a function's result inside it.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::an_exact_parameter_annotation(indoc! {"
    def first(t: {Int, ..}) => Int:
        t.0
    first((1, 2))
"})]
#[case::a_result_annotation(indoc! {"
    def same(t <: {Int, Int}) => {Int, ..}:
        t
    same((1, 2)).0
"})]
#[case::a_function_domain(indoc! {"
    def ap(f <: {Int, ..} => Int) => Int:
        f((1, 2))
    ap(\\t -> t.0)
"})]
#[case::a_mutable_variable(indoc! {"
    x: Mut({Int, ..}) := (1, 2)
    x.0
"})]
#[case::an_exact_binding(indoc! {"
    x: {Int, ..} = (1, 2)
    x.0
"})]
fn an_open_tuple_is_only_a_bound(#[case] code: &str) {
    check_compile_error(code, "an open tuple `{T, ..}` is a bound, not a type");
}

/// In a type parameter's bound an open tuple is the whole bound: the definition reads a value
/// of the parameter through the bound, so a nested open tuple would type a value.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_record_component(indoc! {"
    def f(R <: {p: {Int, ..}}, r: R) => Int:
        r.p.0
    f((p=(5, 6)))
"})]
#[case::a_tuple_component(indoc! {"
    def f(T <: {{Int, ..}, Int}, t: T) => Int:
        t.0.0
    f(((1, 2), 3))
"})]
#[case::a_position_of_an_open_tuple(indoc! {"
    def f(T <: {{Int, ..}, ..}, t: T) => Int:
        t.0.0
    f(((1, 2), 3))
"})]
#[case::a_function_result(indoc! {"
    def mk(F <: Int => {Int, ..}, f: F) => Int:
        f(1).0
    mk(\\x -> (x, x))
"})]
#[case::a_polymorphic_annotation(indoc! {"
    g: forall (R <: {p: {Int, ..}}) R => Int = \\r -> r.p.0
    g((p=(5, 6)))
"})]
fn a_type_parameter_bound_is_open_only_as_a_whole(#[case] code: &str) {
    check_compile_error(
        code,
        "in a type parameter's bound, an open tuple `{T, ..}` is the whole bound",
    );
}

/// Two tuples of different widths have no common type, so a join of them is refused rather
/// than read as their common positions.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::a_conditional(indoc! {"
    c = 1 > 0
    x = (1, 2) if c else (1, 2, 3)
    x.0
"})]
#[case::a_list(indoc! {"
    xs = [(1, 2), (1, 2, 3)]
    sum([p.0 for p in xs])
"})]
fn tuples_of_two_widths_do_not_join(#[case] code: &str) {
    check_compile_error(
        code,
        "tuples of different widths meet: a 2-tuple and a 3-tuple",
    );
}

/// A type parameter bounded by an open tuple has no width, so the definition cannot take it
/// apart as a tuple of one.
#[test]
fn an_open_bound_is_not_a_tuple_of_one_width() {
    check_compile_error(
        indoc! {"
            def f(T <: {Int, ..}, t: T) => Int:
                a, b = t
                a
            f((1, 2))
        "},
        "an open tuple `{A, ..}` fixes no width",
    );
}

/// A width nothing fixes is reported once per tuple, however many nodes hold its type and
/// however often the program reads it: here a lambda nothing applies, read twice, and an empty
/// list whose elements a comprehension reads.
#[test]
fn a_width_nothing_fixes_is_reported_once_per_tuple() {
    let errors = compile_errors(&LoadedProgram::test(indoc! {"
        fs = [\\t -> (t.0, t.1)]
        xs = []
        ys = [p.0 for p in xs]
        1
    "}));
    assert_eq!(errors.matches("is never fixed").count(), 2, "{errors}");
    assert!(
        errors.contains("{_, _, ..} is never fixed in t:"),
        "{errors}"
    );
    assert!(errors.contains("{_, ..} is never fixed in []:"), "{errors}");
}
