//! Nominal types: `type` declarations and their constructors (`docs/chl-spec.md`,
//! "6.8 Nominal types and methods [Decided]").
//!
//! A nominal value is held as its constructor's name and argument, so a program whose
//! value is one observes the tagged value the constructor built.

use indoc::indoc;

use cambra::ccl::FieldKey;
use cambra::interpreter::Value;

use crate::helpers::{check_compile_error, check_scalar, make_record, make_tuple};

/// A `Value::Union` at the constructor `tag` carrying `inner`.
fn ctor(tag: &str, inner: Value) -> Value {
    Value::Union {
        tag: FieldKey::Name(tag.into()),
        inner: Box::new(inner),
    }
}

#[test]
fn a_constructor_builds_a_value_named_by_its_constructor() {
    check_scalar(
        indoc! {r#"
            type Shape:
                circle(radius: Int)
                rect(w: Int, h: Int)

            Shape::circle(2)
        "#},
        ctor("circle", Value::Int(2)),
    );
}

/// Several parameters are one argument, the tuple of them: `rect` has type
/// `{Int, Int} => Shape`.
#[test]
fn a_constructor_of_several_parameters_takes_their_tuple() {
    check_scalar(
        indoc! {r#"
            type Shape:
                circle(radius: Int)
                rect(w: Int, h: Int)

            Shape::rect(3, 4)
        "#},
        ctor("rect", make_tuple(&[Value::Int(3), Value::Int(4)])),
    );
}

#[test]
fn a_constructor_without_parameters_is_a_value() {
    check_scalar(
        indoc! {r#"
            type Light:
                on
                off

            Light::off
        "#},
        ctor("off", Value::Unit),
    );
}

/// The single-constructor form declares the one constructor `new`.
#[test]
fn the_single_constructor_form_declares_new() {
    check_scalar(
        indoc! {r#"
            type Price = Int

            Price::new(250)
        "#},
        ctor("new", Value::Int(250)),
    );
}

/// An annotation names the type, and a binding of it holds the constructed value.
#[test]
fn an_annotation_names_a_nominal_type() {
    check_scalar(
        indoc! {r#"
            type Shape:
                circle(radius: Int)
                rect(w: Int, h: Int)

            def unit_square(n: Int) => Shape:
                Shape::rect(n, n)

            s: Shape = unit_square(1)
            s
        "#},
        ctor("rect", make_tuple(&[Value::Int(1), Value::Int(1)])),
    );
}

/// A parameterised type's constructor takes its type arguments from its argument.
#[test]
fn a_parameterised_constructor_is_polymorphic() {
    check_scalar(
        indoc! {r#"
            type Box(T):
                boxed(T)

            a: Box(Int) = Box::boxed(1)
            b: Box(String) = Box::boxed("x")
            b
        "#},
        ctor("boxed", Value::String("x".into())),
    );
}

/// A constructor without parameters of a parameterised type takes its type argument from
/// the use, as a polymorphic value.
#[test]
fn a_parameterised_constructor_without_parameters_is_polymorphic() {
    check_scalar(
        indoc! {r#"
            type Maybe(T):
                just(T)
                nothing

            a: Maybe(Int) = Maybe::nothing
            b: Maybe(String) = Maybe::nothing
            a
        "#},
        ctor("nothing", Value::Unit),
    );
}

/// A polymorphic `def` builds a nominal value at each use's type argument.
#[test]
fn a_polymorphic_def_builds_a_nominal_value() {
    check_scalar(
        indoc! {r#"
            type Box(T):
                boxed(T)

            def wrap(T, x: T) => Box(T):
                Box::boxed(x)

            a: Box(Int) = wrap(1)
            b: Box(String) = wrap("s")
            b
        "#},
        ctor("boxed", Value::String("s".into())),
    );
}

/// A constructor is a function value, applied later.
#[test]
fn a_constructor_is_a_function_value() {
    check_scalar(
        indoc! {r#"
            type Shape:
                circle(radius: Int)

            make = Shape::circle
            make(5)
        "#},
        ctor("circle", Value::Int(5)),
    );
}

/// A nominal type is distinct from its representation: a structural variant with the
/// same arm is not a `Shape`, and a `Shape` is not an `Int`.
#[test]
fn a_nominal_type_relates_to_no_other_type() {
    check_compile_error(
        indoc! {r#"
            type Shape:
                circle(radius: Int)

            s: Shape = `circle(1)
            s
        "#},
        "annotated as Shape, but inferred as {`circle{Int where _ == 1}}",
    );
    check_compile_error(
        indoc! {r#"
            type Price = Int

            p: Int = Price::new(3)
            p
        "#},
        "annotated as Int, but inferred as Price",
    );
}

/// A declared nominal type satisfies no trait, not even one its representation does: no
/// arithmetic, no equality, and no grouping by it.
#[test]
fn a_nominal_type_satisfies_no_trait() {
    for (src, needle) in [
        (
            indoc! {r#"
                type Price = Int

                Price::new(3) + 1
            "#},
            "No Addable instance for BinOp: operand 1 is Price",
        ),
        (
            indoc! {r#"
                type Price = Int

                Price::new(3) == Price::new(3)
            "#},
            "No Equatable instance for BinOp: operand 1 is Price",
        ),
        (
            indoc! {r#"
                type K = Int

                xs = [K::new(1), K::new(2)]
                groupby(xs, \k -> k)
            "#},
            "No Equatable instance for BinOp: operand 1 is K",
        ),
    ] {
        check_compile_error(src, needle);
    }
}

/// A nominal value has no fields, even where its representation is a record.
///
/// The spec spells the call `Price::new(amount=3)`, the call's parentheses building the
/// record argument. That form does not parse yet for any call, `f(amount=3)` included, so
/// the record is written as a value.
#[test]
fn a_nominal_value_has_no_fields() {
    check_compile_error(
        indoc! {r#"
            type Price = {amount: Int}

            Price::new((amount=3)).amount
        "#},
        "expected {amount: ?",
    );
}

/// Two nominal types of one shape are two types.
#[test]
fn two_nominal_types_of_one_shape_are_distinct() {
    check_compile_error(
        indoc! {r#"
            type UserId = Int
            type OrderId = Int

            u: UserId = OrderId::new(1)
            u
        "#},
        "annotated as UserId, but inferred as OrderId",
    );
}

/// A covariant parameter relates two applications as its arguments relate.
#[test]
fn a_covariant_parameter_follows_its_argument() {
    check_scalar(
        indoc! {r#"
            type Box(T):
                boxed(T)

            def widen(b: Box({a: Int})) => Box({a: Int}):
                b

            widen(Box::boxed((a=1, b=2)))
        "#},
        ctor(
            "boxed",
            make_record(&[("a", Value::Int(1)), ("b", Value::Int(2))]),
        ),
    );
}

/// A covariant parameter refuses the opposite direction: a `Box({a: Int})` is not a
/// `Box({a: Int, b: Int})`.
#[test]
fn a_covariant_parameter_refuses_a_narrower_argument() {
    check_compile_error(
        indoc! {r#"
            type Box(T):
                boxed(T)

            def narrow(b: Box({a: Int, b: Int})) => Int:
                1

            narrow(Box::boxed((a=1)))
        "#},
        "No field .b for Apply: {a: Int@1} has no such field",
    );
}

// The variance tests below pass a function payload to a `def` that discards it, so they
// check typing only. A function payload a program reads, `h = Handler::on(\r -> r + 1)`,
// fails operator conversion ("const requires an input operator"), as a tuple holding a
// lambda does; no test here runs one.

/// A parameter in a function's domain is contravariant: a handler of `{a: Int}` serves
/// where a handler of `{a: Int, b: Int}` is demanded, and not the other way.
#[test]
fn a_contravariant_parameter_reverses_its_argument() {
    check_scalar(
        indoc! {r#"
            type Handler(T):
                on(T => Int)

            def take(h: Handler({a: Int, b: Int})) => Int:
                1

            take(Handler::on(\r -> r.a))
        "#},
        Value::Int(1),
    );
}

/// A contravariant parameter refuses the covariant direction: a handler that reads `b`
/// does not serve where a handler of `{a: Int}` is demanded.
#[test]
fn a_contravariant_parameter_refuses_a_wider_argument() {
    check_compile_error(
        indoc! {r#"
            type Handler(T):
                on(T => Int)

            def take(h: Handler({a: Int})) => Int:
                1

            take(Handler::on(\r -> r.a + r.b))
        "#},
        "No field .b for Apply: {a: Int} has no such field",
    );
}

/// A parameter inside another nominal type takes that type's variance: `Box`'s `T` is
/// covariant, so `Outer`'s is too.
#[test]
fn a_parameter_inside_another_nominal_type_takes_its_variance() {
    check_scalar(
        indoc! {r#"
            type Box(T):
                boxed(T)

            type Outer(T):
                wrapped(Box(T))

            def take(x: Outer({a: Int})) => Int:
                1

            take(Outer::wrapped(Box::boxed((a=1, b=2))))
        "#},
        Value::Int(1),
    );
}

/// A parameter in both a domain and a codomain is invariant: equating `{a: Int}` with
/// `{a: Int, b: Int}` leaves the field `b` missing from one side.
#[test]
fn an_invariant_parameter_relates_only_equal_arguments() {
    check_compile_error(
        indoc! {r#"
            type Cell(T):
                cell(T, T => T)

            def take(c: Cell({a: Int})) => Int:
                1

            c: Cell({a: Int, b: Int}) = Cell::cell((a=1, b=2), \r -> r)
            take(c)
        "#},
        "has no such field",
    );
}

/// A join of two applications of an invariant type is typed at what both arms accept, or
/// refused with a diagnostic; it never reaches a compiler panic. `Cell`'s `T` occurs at both
/// polarities, so the join's argument has an input side and an output side
/// (`src/ccl/design/nominal-types.md`, "Variance").
#[rstest_log::rstest]
#[case::equal_after_widening(indoc! {r#"
    type Cell(T):
        cell(T, T => T)

    c = 1 > 0
    x = Cell::cell(1, \r -> r) if c else Cell::cell(2, \r -> r + 1)
    7
"#})]
#[case::no_common_argument(indoc! {r#"
    type Cell(T):
        cell(T, T => T)

    c = 1 > 0
    x = Cell::cell((a=1), \r -> r) if c else Cell::cell((a=1, b=2), \r -> r)
    7
"#})]
fn a_join_of_an_invariant_type_reaches_no_compiler_panic(#[case] src: &str) {
    if let Err(payload) = std::panic::catch_unwind(|| crate::helpers::run_pipeline(src)) {
        let msg = payload
            .downcast_ref::<String>()
            .cloned()
            .unwrap_or_default();
        assert!(
            !msg.contains("produced an invalid tree") && !msg.contains("closure bridge"),
            "a compiler panic, not a diagnostic: {msg}"
        );
    }
}

/// An argument at an equality position, here a map's keys, is one type on both sides of a
/// relation, so a join whose arguments differ is refused, as two collections over different
/// domains are.
#[test]
fn a_join_at_different_arguments_of_an_equality_position_is_refused() {
    check_compile_error(
        indoc! {r#"
            type Index(K):
                index(FullMap(K, Int))

            c = 1 > 0
            x = Index::index(map([(1, 10)])) if c else Index::index(map([(2, 20)]))
            7
        "#},
        "Incompatible",
    );
}

/// Two nominal types have no join, and neither has one with a structural type.
#[test]
fn a_nominal_type_joins_with_no_other_type() {
    check_compile_error(
        indoc! {r#"
            type UserId = Int
            type OrderId = Int

            def pick(c: Bool) => Int:
                x = UserId::new(1) if c else OrderId::new(2)
                1

            pick(True)
        "#},
        "Conflicting Types: OrderId | UserId",
    );
    check_compile_error(
        indoc! {r#"
            type UserId = Int

            def pick(c: Bool) => Int:
                x = UserId::new(1) if c else 2
                1

            pick(True)
        "#},
        "Conflicting Types: Int | UserId",
    );
}

/// Two values of one nominal type join to it.
#[test]
fn values_of_one_nominal_type_join_to_it() {
    check_scalar(
        indoc! {r#"
            type Shape:
                circle(radius: Int)
                rect(w: Int, h: Int)

            def pick(c: Bool) => Shape:
                Shape::circle(1) if c else Shape::rect(2, 3)

            pick(False)
        "#},
        ctor("rect", make_tuple(&[Value::Int(2), Value::Int(3)])),
    );
}

/// A nominal value inside a product joins component by component, in a tuple and in a
/// record, whichever arm holds the value.
#[rstest_log::rstest]
#[case::a_tuple_first_arm(
    "(Shape::circle(1), 2) if c else (Shape::dot, 3)",
    make_tuple(&[ctor("circle", Value::Int(1)), Value::Int(2)])
)]
#[case::a_tuple_second_arm(
    "(Shape::circle(1), 2) if not c else (Shape::dot, 3)",
    make_tuple(&[ctor("dot", Value::Unit), Value::Int(3)])
)]
#[case::a_record(
    "(s=Shape::circle(1), n=2) if c else (s=Shape::dot, n=3)",
    make_record(&[("s", ctor("circle", Value::Int(1))), ("n", Value::Int(2))])
)]
fn a_product_of_nominal_values_joins(#[case] join: &str, #[case] expected: Value) {
    let program = indoc! {"
        type Shape:
            circle(Int)
            dot

        c = 1 > 0
    "};
    check_scalar(&format!("{program}{join}\n"), expected);
}

/// An alias may name a nominal type, and a constructor's parameter type may name an alias
/// declared anywhere in the module.
#[test]
fn aliases_and_nominal_types_name_each_other() {
    check_scalar(
        indoc! {r#"
            type Order:
                placed(Cents)

            Cents = Int
            Placed = {Order, Cents}

            p: Placed = (Order::placed(5), 5)
            p.0
        "#},
        ctor("placed", Value::Int(5)),
    );
}

/// A refinement on a constructor's parameter is discharged where the constructor is
/// called.
#[test]
fn a_constructor_discharges_its_refinement() {
    check_scalar(
        indoc! {r#"
            type Price = {Int where _ >= 0}

            Price::new(3)
        "#},
        ctor("new", Value::Int(3)),
    );
    check_compile_error(
        indoc! {r#"
            type Price = {Int where _ >= 0}

            Price::new(-3)
        "#},
        "expected {Int | __elem >= 0}, found Int@-3",
    );
}

#[test]
fn declaration_errors_name_what_is_wrong() {
    for (src, needle) in [
        (
            indoc! {r#"
                type Tree:
                    leaf
                    node(Tree, Tree)

                Tree::leaf
            "#},
            "`Tree` reaches itself",
        ),
        (
            indoc! {r#"
                type A:
                    a(B)
                    stop
                type B:
                    b(A)

                A::stop
            "#},
            "`A` reaches itself through its constructors' parameter types (A → B → A)",
        ),
        (
            indoc! {r#"
                type Price = Int
                Price = Int

                1
            "#},
            "`Price` is declared by a `type` in this module",
        ),
        (
            indoc! {r#"
                type Box(Int):
                    boxed(Int)

                1
            "#},
            "`Int` is a built-in type and cannot name a type parameter",
        ),
        (
            indoc! {r#"
                type Pair(T, T):
                    pair(T)

                1
            "#},
            "type parameter `T` is declared twice",
        ),
        (
            indoc! {r#"
                type Box:
                    boxed(_)

                1
            "#},
            "a constructor's parameter type is written in full",
        ),
        (
            indoc! {r#"
                type Box(T):
                    empty

                Box::empty
            "#},
            "type parameter `T` of `Box` appears in no constructor",
        ),
        // A declaration naming one that failed reports the first failure alone.
        (
            indoc! {r#"
                type A(T) = Int
                type B = A(Int)

                1
            "#},
            "type parameter `T` of `A` appears in no constructor",
        ),
        (
            indoc! {r#"
                type Shape:
                    circle(Int)
                    circle(Int)

                Shape::circle(1)
            "#},
            "declares the constructor `circle` twice",
        ),
        (
            indoc! {r#"
                type Shape:
                    circle(Int)
                type Shape:
                    square(Int)

                Shape::circle(1)
            "#},
            "`Shape` is declared twice",
        ),
        (
            indoc! {r#"
                type Map = Int

                1
            "#},
            "`Map` is a built-in type",
        ),
        (
            indoc! {r#"
                def f(x):
                    type Inner = Int
                    x

                f(1)
            "#},
            "a `type` is declared at a module's top level",
        ),
        (
            indoc! {r#"
                def f(x: Int) => Int:
                    y = x
                    type Inner = Int

                f(1)
            "#},
            "a `type` is declared at a module's top level",
        ),
        (
            indoc! {r#"
                x = 1
                type Price = Int
            "#},
            "`type Price` binds no value, so it cannot end a module",
        ),
        (
            indoc! {r#"
                limit = 10
                type Rate = {Int where _ <= limit}

                Rate::new(3)
            "#},
            "names `limit`; naming a module binding there is not supported yet",
        ),
    ] {
        check_compile_error(src, needle);
    }
}

/// A name declared twice is reported at the second declaration, with the first labelled.
#[test]
fn a_repeated_declaration_names_the_first() {
    for (src, needle) in [
        (
            indoc! {r#"
                type Shape:
                    circle(Int)
                type Shape:
                    square(Int)

                Shape::circle(1)
            "#},
            "first declared here",
        ),
        (
            indoc! {r#"
                type Shape:
                    circle(Int)
                    circle(Int)

                Shape::circle(1)
            "#},
            "first declared here",
        ),
        (
            indoc! {r#"
                type Price = Int
                Price = Int

                1
            "#},
            "declared by the `type` here",
        ),
    ] {
        check_compile_error(src, needle);
    }
}

#[test]
fn constructor_use_errors_name_what_is_wrong() {
    for (src, needle) in [
        (
            indoc! {r#"
                type Light:
                    on
                    off

                Light::on()
            "#},
            "is a value and not a function",
        ),
        (
            indoc! {r#"
                type Shape:
                    rect(w: Int, h: Int)

                Shape::rect(1)
            "#},
            "`Shape::rect` takes 2 arguments, got 1",
        ),
        (
            indoc! {r#"
                type Shape:
                    rect(w: Int, h: Int)

                Shape::square(1)
            "#},
            "`Shape` declares no constructor `square`",
        ),
        (
            indoc! {r#"
                type Box(T):
                    boxed(T)

                b: Box = Box::boxed(1)
                b
            "#},
            "`Box` takes 1 type argument, got 0",
        ),
    ] {
        check_compile_error(src, needle);
    }
}

/// A nullary constructor's type argument is determined by the use, and a join with a
/// sibling of the same type is one: `Opt::none` joined with `Opt::some(1)` is an `Opt(Int)`,
/// whichever arm it is (`docs/chl-spec.md`, "6.8 Nominal types and methods \[Decided\]").
#[rstest_log::rstest]
#[case::the_value_arm_first("Opt::some(1) if c else Opt::none", ctor("some", Value::Int(1)))]
#[case::the_nullary_arm_first("Opt::none if c else Opt::some(1)", ctor("none", Value::Unit))]
fn a_join_determines_a_nullary_constructors_argument(#[case] join: &str, #[case] expected: Value) {
    let program = indoc! {"
        type Opt(T):
            some(value: T)
            none

        c = 1 > 0
    "};
    check_scalar(&format!("{program}{join}\n"), expected);
}

/// With nothing to determine it, a nullary constructor's argument is an unresolved type at
/// the use.
#[test]
fn a_nullary_constructor_nothing_determines_is_unresolved() {
    check_compile_error(
        indoc! {r#"
            type Opt(T):
                some(value: T)
                none

            Opt::none
        "#},
        "Unresolved inference variable",
    );
}

/// A collection given to a constructor is compiled as a component of the value: a literal,
/// and a `box` entering the described sum the declaration states.
#[test]
fn a_collection_payload_compiles() {
    check_scalar(
        indoc! {"
            type Arr = Array(3, Int)
            type Bag(T) = List(T)
            a = Arr::new([1, 2, 3])
            b = Bag::new(box([1, 2, 3]))
            7
        "},
        Value::Int(7),
    );
}
