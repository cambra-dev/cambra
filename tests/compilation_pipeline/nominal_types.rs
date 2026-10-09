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
        "Shape",
    );
    check_compile_error(
        indoc! {r#"
            type Price = Int

            p: Int = Price::new(3)
            p
        "#},
        "Price",
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
        "UserId",
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
        "b",
    );
}

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
        "UserId",
    );
    check_compile_error(
        indoc! {r#"
            type UserId = Int

            def pick(c: Bool) => Int:
                x = UserId::new(1) if c else 2
                1

            pick(True)
        "#},
        "UserId",
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
        "Price::new",
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
                type Box(T):
                    empty

                Box::empty
            "#},
            "type parameter `T` of `Box` appears in no constructor",
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
