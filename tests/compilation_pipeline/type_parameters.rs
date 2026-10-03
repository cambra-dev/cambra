//! Type parameters, bounds and polymorphic type annotations (`docs/chl-spec.md`,
//! "6.8 Polymorphic types"; `src/ccl/design/type-parameters.md`).
//!
//! A type parameter is opaque in the definition that declares it, and each use
//! instantiates it at its own types. `requires` clauses are parsed and still refused at
//! lowering, so every case here states its requirements through bounds or needs none.

use std::time::Duration;

use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use crate::helpers::{check_compile_error, check_scalar};

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::used_at_two_types(
    indoc! {r#"
        def first(T, a: T, b: T) => T:
            a
        first(1, 2) == 1 and first("x", "y") == "x"
    "#},
    Value::Bool(true),
)]
#[case::bound_gives_the_body_its_fields(
    indoc! {"
        def at(T <: {at: Int}, a: T) => Int:
            a.at
        at((at=1, sku=2)) + at((at=5))
    "},
    Value::Int(6),
)]
// `U <: T` relates the two, so their join is `T` rather than a collision.
#[case::bound_naming_an_earlier_parameter(
    indoc! {"
        def pick(T, U <: T, c: Bool, a: T, b: U) => T:
            a if c else b
        pick(False, 1, 2)
    "},
    Value::Int(2),
)]
// A value of a bounded parameter's type is a value of its bound's type, so a join with
// another record is their join through the bound. Checked alone: a call reaches the
// interpreter's panic on a conditional over records, as on `main`
// (`tile_operators/mod.rs:453`).
#[case::join_through_a_bound(
    indoc! {"
        def at(T <: {at: Int}, c: Bool, a: T) => Int:
            (a if c else (at=1)).at
        1
    "},
    Value::Int(1),
)]
// Two parameters bounded by one type join at it.
#[case::two_parameters_joined_through_their_bounds(
    indoc! {"
        def pick(T <: Int, U <: Int, c: Bool, a: T, b: U) => Int:
            a if c else b
        pick(False, 1, 2)
    "},
    Value::Int(2),
)]
#[case::generic_calls_generic(
    indoc! {r#"
        def same(T, x: T) => T:
            x
        def twice(U, y: U) => U:
            same(same(y))
        twice(3) == 3 and twice("s") == "s"
    "#},
    Value::Bool(true),
)]
#[case::nested_generic_definition(
    indoc! {r#"
        def outer(T, x: T) => T:
            def inner(U, y: U) => U:
                y
            inner(inner(x))
        outer(1) == 1 and outer("s") == "s"
    "#},
    Value::Bool(true),
)]
#[case::unused(
    indoc! {"
        def first(T, a: T, b: T) => T:
            a
        1
    "},
    Value::Int(1),
)]
#[case::polymorphic_annotation_on_a_name(
    indoc! {"
        def first(T, a: T, b: T) => T:
            a
        pick: \\T -> {T, T} => T = first
        pick(3, 4)
    "},
    Value::Int(3),
)]
#[case::polymorphic_annotation_on_a_lambda_through_an_alias(
    indoc! {r#"
        Same = \T -> T => T
        same: Same = \x -> x
        same(1) == 1 and same("a") == "a"
    "#},
    Value::Bool(true),
)]
// Each binding an alias annotates opens the `Poly` for itself, with parameters of its
// own.
#[case::alias_annotating_two_bindings(
    indoc! {r#"
        Same = \T -> T => T
        a: Same = \x -> x
        b: Same = \y -> y
        a(1) == 1 and b("s") == "s"
    "#},
    Value::Bool(true),
)]
fn type_parameters_check_and_run(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::operator_needs_a_requirement(
    indoc! {"
        def inc(T, x: T) => T:
            x + 1
        inc(1)
    "},
    "No requirement states that `T` is Addable",
)]
#[case::parameter_is_not_its_instantiation(
    indoc! {"
        def to_int(T, x: T) => Int:
            x
        to_int(1)
    "},
    "annotated as Int, but inferred as T",
)]
// Each call substitutes its own types, so only the definition checked with its
// parameters opaque sees this; it is rejected whether or not anything calls it.
#[case::two_parameters_have_no_common_type(
    indoc! {"
        def pick(T, U, c: Bool, a: T, b: U):
            a if c else b
        pick(True, 1, 2)
    "},
    "Conflicting Types: T | U",
)]
#[case::two_parameters_have_no_common_type_unused(
    indoc! {"
        def pick(T, U, c: Bool, a: T, b: U):
            a if c else b
        1
    "},
    "Conflicting Types: T | U",
)]
#[case::parameter_escapes_its_definition(
    indoc! {"
        def outer(g):
            def inner(T, x: T) => T:
                y = g(x)
                x
            inner(1)
        outer(\\v -> v)
    "},
    "Type parameter `T` escapes its definition",
)]
#[case::bound_is_checked_at_the_call(
    indoc! {"
        def at(T <: {at: Int}, a: T) => Int:
            a.at
        at((x=1))
    "},
    "No field .at",
)]
#[case::polymorphic_annotation_on_a_monomorphic_name(
    indoc! {"
        m = 5
        g: \\T -> T = m
        1
    "},
    "annotated as T, but inferred as Int@5",
)]
// The annotation fits the value, so what refuses it is that the name it binds is
// monomorphic.
#[case::polymorphic_annotation_fitting_a_monomorphic_name(
    indoc! {"
        m = 5
        g: \\T -> Int = m
        1
    "},
    "`g` is annotated with a polymorphic type, but its right-hand side is monomorphic",
)]
fn type_parameter_errors(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

/// What lowering refuses, each with the rule it names (`docs/chl-spec.md`, "Type
/// parameters" and "Polymorphic type annotations").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::parameter_no_argument_determines(
    indoc! {"
        def f(T, x) => T:
            x
        f(1)
    "},
    "type parameter `T` appears in no parameter's annotation",
)]
#[case::built_in_name(
    indoc! {"
        def f(Int, x: Int):
            x
        f(1)
    "},
    "`Int` is a built-in type and cannot name a type parameter",
)]
#[case::alias_hiding_a_parameter(
    indoc! {"
        def f(T, x: T) => T:
            T = Int
            x
        f(1)
    "},
    "`T` is a type parameter of the enclosing definition",
)]
#[case::nested_polymorphic_type(
    indoc! {"
        x: List(\\T -> T) = []
        1
    "},
    "a polymorphic type is written only as a whole `let` annotation",
)]
#[case::polymorphic_parameter_type(
    indoc! {"
        def f(g: \\T -> T => T):
            g
        1
    "},
    "a polymorphic type is written only as a whole `let` annotation",
)]
#[case::bounded_polymorphic_annotation(
    indoc! {"
        def id(a):
            a
        g <: \\T -> T => T = id
        1
    "},
    "a polymorphic annotation is exact",
)]
#[case::polymorphic_annotation_on_a_call(
    indoc! {"
        def id(a):
            a
        g: \\T -> T => T = id(id)
        1
    "},
    "a binding annotated with a polymorphic type must be polymorphic",
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
    indoc! {r#"
        def put(k: String) => String requires Transaction:
            k
        put("a")
    "#},
    "a `requires` clause is not supported yet",
)]
#[case::type_parameter_on_a_lambda_value(
    indoc! {"
        f = \\T -> 1
        f(2)
    "},
    "`T` is capitalized, so it is a type parameter, which a lambda value does not take",
)]
fn polymorphic_forms_refused_at_lowering(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
}

/// A generic `def` in a generator's `for` body is lowered on a path of its own, which
/// declares its type parameters as the top-level path does.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_generic_definition_inside_a_loop_body() {
    check_scalar(
        indoc! {"
            def doubled(xs):
                for x in xs:
                    def same(T, a: T) => T:
                        a
                    yield same(x) * 2
            sum(doubled([1, 2]))
        "},
        Value::Int(6),
    );
}
