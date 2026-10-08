//! Type parameters, `requires` clauses and polymorphic type annotations
//! (`docs/chl-spec.md`, "6.10 Polymorphic types").
//!
//! The parser recognises each form and lowering refuses it, so these pin the refusal a
//! program reaches today. Each refusal names the form rather than failing to parse.

use indoc::indoc;
use rstest_log::rstest;

use crate::helpers::check_compile_error;

#[rstest]
#[case::type_parameter(
    indoc! {"
        def larger(T, a: T, b: T) => T:
            b if a < b else a

        larger(3, 7)
    "},
    "`T` is a type parameter, since it is capitalized, and type parameters are not supported yet",
)]
#[case::bounded_type_parameter(
    indoc! {"
        def newest(T <: {at: Int}, a: T, b: T) => T:
            a

        newest((at=1), (at=2))
    "},
    "`T` is a type parameter",
)]
#[case::kinded_type_parameter(
    indoc! {"
        def same(T: Type, a: T) => T:
            a

        same(1)
    "},
    "`T` is a type parameter",
)]
#[case::requires_clause(
    indoc! {"
        def add(a, b) requires Addable(Int, Int, Output=Int):
            a + b

        add(1, 2)
    "},
    "a `requires` clause is not supported yet",
)]
#[case::requires_transaction(
    indoc! {"
        def put(k: String) => String requires Transaction:
            k

        put(\"a\")
    "},
    "a `requires` clause is not supported yet",
)]
#[case::polymorphic_annotation(
    indoc! {"
        def larger(a, b):
            b if a < b else a

        bigger: forall (T) {T, T} => T requires Orderable(T, T) = larger
        bigger(3, 7)
    "},
    "polymorphic types `forall (T) …` are not supported yet",
)]
#[case::capitalized_lambda_binder(
    indoc! {"
        f = \\T -> 1
        f(2)
    "},
    "`T` is capitalized, so it names a type, which a lambda does not bind",
)]
#[case::polymorphic_type_as_a_value(
    indoc! {"
        f = forall (T) T => T
        f
    "},
    "`forall (T) V` is a polymorphic *type*",
)]
fn polymorphic_forms_are_refused_at_lowering(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

/// A type parameter on a `def` inside a generator's `for` body reaches the same refusal
/// as one at the top level: the loop body lowers its `def`s on a path of its own.
#[test]
fn a_type_parameter_inside_a_loop_body_is_refused() {
    check_compile_error(
        indoc! {"
            def doubled(xs):
                for x in xs:
                    def twice(T, a: T) => T:
                        a
                    yield twice(x) * 2

            sum(doubled([1, 2]))
        "},
        "`T` is a type parameter",
    );
}
