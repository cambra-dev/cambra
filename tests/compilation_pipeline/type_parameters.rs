//! Type parameters, bounds and polymorphic type annotations (`docs/chl-spec.md`,
//! "6.10 Polymorphic types"; `src/ccl/design/type-parameters.md`).
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
// `T: Type` is `T`, and `T: SubtypesOf(B)` is `T <: B` (`docs/chl-spec.md`, "Kinds and
// bounds").
#[case::kinds_written_out(
    indoc! {r#"
        def first(T: Type, a: T, b: T) => T:
            a
        def at(T: SubtypesOf({at: Int}), a: T) => Int:
            a.at
        first("x", "y") == "x" and at((at=1, sku=2)) == 1
    "#},
    Value::Bool(true),
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
// A nested generic definition passes its parameter to a definition declared further
// out. Checked alone, it specializes that definition at its opaque parameter, which
// sits deeper than the callee's own variables.
#[case::nested_generic_calls_an_outer_generic(
    indoc! {r#"
        def same(V, a: V) => V:
            a
        def outer(T, x: T) => T:
            def inner(U, y: U) => U:
                same(y)
            inner(x)
        outer(1) == 1 and outer("a") == "a"
    "#},
    Value::Bool(true),
)]
#[case::nested_generic_calls_an_outer_implicit_generic_unused(
    indoc! {"
        def same(a):
            a
        def outer(x):
            def inner(U, y: U) => U:
                same(y)
            x
        outer(1)
    "},
    Value::Int(1),
)]
// A bound's refinement predicate is typed as the parameter is opened, so a use that
// instantiates it meets a resolved predicate.
#[case::refined_bound(
    indoc! {"
        def pos(T <: {Int where _ > 0}, x: T) => T:
            x
        pos(3)
    "},
    Value::Int(3),
)]
#[case::refined_bound_through_an_alias(
    indoc! {"
        Pos = {Int where _ > 0}
        def pos(T <: Pos, x: T) => Int:
            x
        pos(3)
    "},
    Value::Int(3),
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
        pick: forall (T) {T, T} => T = first
        pick(3, 4)
    "},
    Value::Int(3),
)]
#[case::polymorphic_annotation_on_a_lambda_through_an_alias(
    indoc! {r#"
        Same = forall (T) T => T
        same: Same = \x -> x
        same(1) == 1 and same("a") == "a"
    "#},
    Value::Bool(true),
)]
// Each binding an alias annotates opens the `Poly` for itself, with parameters of its
// own.
#[case::alias_annotating_two_bindings(
    indoc! {r#"
        Same = forall (T) T => T
        a: Same = \x -> x
        b: Same = \y -> y
        a(1) == 1 and b("s") == "s"
    "#},
    Value::Bool(true),
)]
// A refinement's element is bound at its base with the parameter opened, in a value
// parameter's annotation and in a bound.
#[case::refinement_of_a_parameter(
    indoc! {"
        def f(T <: Int, x: {T where _ > 0}) => Int:
            x
        f(3)
    "},
    Value::Int(3),
)]
#[case::refinement_of_a_parameter_in_a_bound(
    indoc! {"
        def f(T <: Int, U <: {T where _ > 0}, a: T, b: U) => Int:
            a
        f(1, 2)
    "},
    Value::Int(1),
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
// `U`'s bound is `T`, which supports nothing; the error names the operand's own
// parameter, not the end of its bound chain.
#[case::operator_on_a_parameter_bounded_by_an_unbounded_one(
    indoc! {"
        def f(T, U <: T, a: T, b: U) => T:
            b + b
        1
    "},
    "No requirement states that `U` is Addable",
)]
#[case::refined_bound_is_checked_at_the_call(
    indoc! {"
        def pos(T <: {Int where _ > 0}, x: T) => Int:
            x
        pos(-1)
    "},
    "found Int@-1",
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
    "cannot pass a value of type parameter `T` to `g`: `g` is declared outside `T`'s \
     definition, so its parameter type cannot depend on `T`",
)]
// A monomorphic binding beside the definition sits at the definition's own level, so the
// parameter reaching it escapes (`src/ccl/design/type-inference.md`, "A monomorphic
// binding's variables sit at its level").
#[case::parameter_escapes_into_a_sibling_feed(
    indoc! {"
        out = defer()
        def put(T, x: T) => T:
            out << x
            x
        put(1)
        out
    "},
    "cannot append a value of type parameter `T` to `out`: `out` is declared outside `T`'s \
     definition, so its element type cannot depend on `T`",
)]
#[case::parameter_escapes_into_a_sibling_binding(
    indoc! {"
        def id(v):
            v
        g = id(\\v -> v)
        def put(T, x: T) => T:
            y = g(x)
            x
        put(1) + g(2)
    "},
    "cannot pass a value of type parameter `T` to `g`",
)]
#[case::parameter_escapes_into_a_sibling_binding_inside_a_definition(
    indoc! {"
        def id(v):
            v
        def outer(z):
            g = id(\\v -> v)
            def put(T, x: T) => T:
                y = g(x)
                x
            put(1) + g(2) + z
        outer(1)
    "},
    "cannot pass a value of type parameter `T` to `g`",
)]
// The base is opened before the element is bound, so the predicate types; the result is
// then not known to be positive.
#[case::refinement_of_a_parameter_in_a_result(
    indoc! {"
        def f(T <: Int, x: T) => {T where _ > 0}:
            x
        f(3)
    "},
    "Annotation mismatch",
)]
// A false rejection: the refinement over the opened parameter is not discharged at the
// use's instantiation, so a positive argument fails the specialization.
#[case::refinement_of_a_parameter_in_a_polymorphic_annotation(
    indoc! {"
        g: forall (T <: Int) {T where _ > 0} => Int = \\x -> x
        g(3)
    "},
    "expected {Int | __elem > 0}, found Int",
)]
// The join of `T` with the enclosing definition's implicit parameter has no type: `x`'s
// type is chosen outside `inner`. Rejected whether or not `outer` is called.
#[case::parameter_joined_with_an_enclosing_implicit_parameter(
    indoc! {"
        def outer(x):
            def inner(T, y: T) => T:
                z = y if True else x
                y
            inner(1)
        outer(2)
    "},
    "Conflicting Types: T | a type chosen outside `T`'s definition",
)]
#[case::parameter_joined_with_an_enclosing_implicit_parameter_uncalled(
    indoc! {"
        def outer(x):
            def inner(T, y: T) => T:
                z = y if True else x
                y
            inner(1)
        1
    "},
    "Conflicting Types: T | a type chosen outside `T`'s definition",
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
        g: forall (T) T = m
        1
    "},
    "annotated as T, but inferred as Int@5",
)]
// The annotation fits the value, so what refuses it is that the name it binds is
// monomorphic.
#[case::polymorphic_annotation_fitting_a_monomorphic_name(
    indoc! {"
        m = 5
        g: forall (T) Int = m
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
#[case::bound_naming_a_later_parameter(
    indoc! {"
        def f(T <: U, U, a: T, b: U) => U:
            b
        1
    "},
    "the bound of `T` names `U`, which is declared after it",
)]
#[case::bound_naming_its_own_parameter(
    indoc! {"
        def f(T <: {next: T}, a: T) => T:
            a
        1
    "},
    "the bound of `T` names `T` itself",
)]
#[case::listing_kind(
    indoc! {"
        def f(T: [Int, String], x: T) => T:
            x
        f(1)
    "},
    "the kind of `T` is `Type` or `SubtypesOf(U)`, also written `T <: U`; no other kind is \
     supported",
)]
#[case::type_as_a_kind(
    indoc! {"
        def f(T: Int, x: T) => T:
            x
        f(1)
    "},
    "the kind of `T` is `Type` or `SubtypesOf(U)`",
)]
#[case::subtypes_of_two_types(
    indoc! {"
        def f(T: SubtypesOf(Int, String), x: T) => T:
            x
        f(1)
    "},
    "`SubtypesOf` takes one type, but it is given 2",
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
        x: List(forall (T) T) = []
        1
    "},
    "a polymorphic type is written only as a whole `let` annotation",
)]
#[case::polymorphic_parameter_type(
    indoc! {"
        def f(g: forall (T) T => T):
            g
        1
    "},
    "a polymorphic type is written only as a whole `let` annotation",
)]
#[case::bounded_polymorphic_annotation(
    indoc! {"
        def id(a):
            a
        g <: forall (T) T => T = id
        1
    "},
    "a bounded polymorphic annotation `g <: forall (T) V` is not supported",
)]
#[case::polymorphic_annotation_on_a_call(
    indoc! {"
        def id(a):
            a
        g: forall (T) T => T = id(id)
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

/// A compared product's components pair by field in one condition per field, freshened with
/// the definition, so each instantiation of a generic component has a condition of its own
/// (`src/ccl/design/type-inference.md`, "A product is answered off the table").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::one_generic_component(
    indoc! {r#"
        def f(y):
            (1, y) == (1, y)
        f(1) and f("a")
    "#},
    Value::Bool(true),
)]
#[case::two_generic_components(
    indoc! {r#"
        def f(x, y):
            (1, x) == (1, y)
        f(1, 1) and f("a", "a")
    "#},
    Value::Bool(true),
)]
#[case::nested_generic_components(
    indoc! {r#"
        def f(x, y):
            ((x, 1), "a") == ((y, 1), "a")
        f(1, 1) and f("a", "a")
    "#},
    Value::Bool(true),
)]
fn a_compared_product_with_a_generic_component(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// Each instantiation is still held to the trait: components of different bases fail.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_compared_product_with_mismatched_generic_components() {
    check_compile_error(
        indoc! {r#"
            def f(x, y):
                (1, x) == (1, y)
            f(1, "a")
        "#},
        "Equatable",
    );
}
