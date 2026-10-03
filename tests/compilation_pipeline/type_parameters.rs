//! Type parameters, bounds and polymorphic type annotations (`docs/chl-spec.md`,
//! "6.8 Polymorphic types"; `src/ccl/design/type-parameters.md`).
//!
//! A type parameter is opaque in the definition that declares it, and each use
//! instantiates it at its own types. It supports what its bound and its definition's
//! `requires` clause state, and each use satisfies both at its own types.

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
fn type_parameters_check_and_run(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// A `requires` clause states what the body may do with a parameter, and each use
/// satisfies it at its own types (`docs/chl-spec.md`, "Trait requirements").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::comparison(
    indoc! {r#"
        def larger(T, a: T, b: T) => T requires Orderable(T, T):
            b if a < b else a
        larger(3, 7) == 7 and larger("a", "b") == "b"
    "#},
    Value::Bool(true),
)]
#[case::associated_type(
    indoc! {r#"
        def add(T, a: T, b: T) => T requires Addable(T, T, Output=T):
            a + b
        add(1, 2) == 3 and add("a", "b") == "ab"
    "#},
    Value::Bool(true),
)]
// `O` is determined by the requirement, whose operands the arguments determine.
#[case::associated_type_as_its_own_parameter(
    indoc! {"
        def add(A, B, O, a: A, b: B) => O requires Addable(A, B, Output=O):
            a + b
        add(1, 2)
    "},
    Value::Int(3),
)]
#[case::requirement_with_a_base_operand(
    indoc! {"
        def inc(T, x: T) => T requires Addable(T, Int, Output=T):
            x + 1
        inc(4)
    "},
    Value::Int(5),
)]
#[case::unary(
    indoc! {"
        def neg(T, a: T) => T requires Negatable(T, Output=T):
            -a
        neg(5)
    "},
    Value::Int(-5),
)]
// The clause answers the operator over a bounded parameter before the bound does, so
// the sum is a `T`.
#[case::requirement_and_bound(
    indoc! {"
        def add(T <: Int, a: T, b: T) => T requires Addable(T, T, Output=T):
            a + b
        add(1, 2)
    "},
    Value::Int(3),
)]
#[case::generic_calls_generic(
    indoc! {r#"
        def add(T, a: T, b: T) => T requires Addable(T, T, Output=T):
            a + b
        def twice(U, y: U) => U requires Addable(U, U, Output=U):
            add(y, y)
        twice(3) == 6 and twice("s") == "ss"
    "#},
    Value::Bool(true),
)]
// `Equatable` reads products componentwise, so the clause states it of `T` and `U`.
#[case::equatable_over_products(
    indoc! {r#"
        def same(T, U, a: {T, U}, b: {T, U}) => Bool requires Equatable({T, U}, {T, U}):
            a == b
        same((1, "x"), (1, "x"))
    "#},
    Value::Bool(true),
)]
#[case::polymorphic_annotation(
    indoc! {r#"
        bigger: \T -> {T, T} => T requires Orderable(T, T) = \a, b -> b if a < b else a
        bigger("a", "b") == "b"
    "#},
    Value::Bool(true),
)]
fn requirements_check_and_run(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::operator_the_clause_does_not_state(
    indoc! {"
        def larger(T, a: T, b: T) => T requires Addable(T, T, Output=T):
            b if a < b else a
        larger(1, 2)
    "},
    "No requirement states that `T` is Orderable",
)]
#[case::operands_the_clause_does_not_state(
    indoc! {"
        def bad(T, x: T) => T requires Addable(T, T, Output=T):
            x + 1
        bad(4)
    "},
    "operand 2 is Int, but the only type accepted there is T",
)]
#[case::call_failing_a_requirement(
    indoc! {"
        def add(T, a: T, b: T) => T requires Addable(T, T, Output=T):
            a + b
        add(True, False)
    "},
    "No Addable instance",
)]
#[case::call_with_a_product(
    indoc! {"
        def larger(T, a: T, b: T) => T requires Orderable(T, T):
            b if a < b else a
        larger((1, 2), (3, 4))
    "},
    "No Orderable instance",
)]
fn requirement_errors(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
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
    "annotated as \\T -> T, but inferred as Int@5",
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

/// A mismatch against a polymorphic annotation prints the right-hand side's type as
/// polymorphic over the variables it quantifies (`docs/chl-spec.md`, "Polymorphic
/// type annotations"). Each variable is a parameter named in order of first
/// appearance, an upper bound standing beside one is its bound, and a trait
/// obligation on one is a requirement.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::requirement_with_a_concrete_operand(
    indoc! {"
        def inc(a):
            a + 1
        pick: \\T -> T => T = inc
        1
    "},
    "annotated as \\T -> (T ⇒ T), but inferred as \\A -> (A ⇒ Int) requires Addable(A, Int, Output=Int)",
)]
#[case::requirement_over_two_parameters(
    indoc! {"
        def less(a, b):
            a < b
        pick: \\T -> {T, T} => T = less
        1
    "},
    "inferred as \\A, B -> ((A, B) ⇒ Bool) requires Orderable(A, B)",
)]
#[case::requirement_naming_its_output(
    indoc! {"
        def add(a, b):
            a + b
        pick: \\T -> {T, T} => T = add
        1
    "},
    "inferred as \\A, B, C -> ((A, B) ⇒ C) requires Addable(A, B, Output=C)",
)]
#[case::bound_written_inline_where_the_parameter_occurs_once(
    indoc! {"
        def at(a):
            a.at
        pick: \\T -> T => Int = at
        1
    "},
    "inferred as \\A -> ({at: A} ⇒ A)",
)]
#[case::bound_on_a_parameter_occurring_twice(
    indoc! {"
        def both(a):
            (a.at, a)
        pick: \\T -> T => T = both
        1
    "},
    "inferred as \\A <: {at: B}, B -> (A ⇒ (B, A))",
)]
// The notation has no join of a parameter and a concrete type; the printed type
// marks it rather than dropping either side.
#[case::join_the_notation_cannot_write(
    indoc! {"
        def f(c, a):
            a if c else 1
        pick: \\T -> {Bool, T} => T = f
        1
    "},
    "inferred as \\A -> ((Bool, A) ⇒ A ∨ Int@1)",
)]
#[case::lambda_right_hand_side(
    indoc! {"
        pick: \\T -> T => T = \\x -> x + 1
        1
    "},
    "inferred as \\A -> (A ⇒ Int) requires Addable(A, Int, Output=Int)",
)]
fn an_annotation_mismatch_prints_the_inferred_polymorphic_type(
    #[case] code: &str,
    #[case] needle: &str,
) {
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
#[case::requires_transaction(
    indoc! {r#"
        def put(k: String) => String requires Transaction:
            k
        put("a")
    "#},
    "`requires Transaction` is not supported yet",
)]
#[case::unknown_trait(
    indoc! {"
        def f(T, a: T) requires Frobnicable(T):
            a
        1
    "},
    "`Frobnicable` is not a trait",
)]
#[case::wrong_operand_count(
    indoc! {"
        def f(T, a: T) requires Addable(T):
            a
        1
    "},
    "`Addable` is over 2 type(s), and this requirement names 1",
)]
#[case::unknown_associated_type(
    indoc! {"
        def f(T, a: T) requires Orderable(T, T, Output=T):
            a
        1
    "},
    "`Orderable` associates no type named `Output`",
)]
#[case::unsatisfiable_requirement(
    indoc! {"
        def f(T, a: T) => T requires Negatable(String, Output=T):
            a
        1
    "},
    "no instance of `Negatable` accepts (String)",
)]
#[case::requirement_over_a_collection(
    indoc! {"
        def f(T, a: T) => T requires Orderable(List(T), List(T)):
            a
        1
    "},
    "no instance of `Orderable` accepts",
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
