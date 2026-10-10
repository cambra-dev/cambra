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

// ---------------------------------------------------------------------------
// Taking a value apart: `match` arms and constructor patterns
// ---------------------------------------------------------------------------

#[test]
fn a_match_dispatches_on_the_constructor() {
    check_scalar(
        indoc! {r#"
            type Shape:
                circle(radius: Int)
                rect(w: Int, h: Int)

            def area(s: Shape) => Int:
                match s:
                    case Shape::circle(r):
                        r * r * 3
                    case Shape::rect(w, h):
                        w * h

            area(Shape::rect(3, 4)) + area(Shape::circle(2))
        "#},
        Value::Int(24),
    );
}

/// The arms name the scrutinee's type, so the scrutinee needs no annotation.
#[test]
fn a_constructor_arm_determines_the_scrutinee_type() {
    check_scalar(
        indoc! {r#"
            type Light:
                on
                off

            def lit(l):
                match l:
                    case Light::on:
                        1
                    case Light::off:
                        0

            lit(Light::on)
        "#},
        Value::Int(1),
    );
}

/// `case _:` covers the constructors no arm names, and `_` declines a parameter.
#[test]
fn a_default_arm_and_an_ignored_parameter() {
    check_scalar(
        indoc! {r#"
            type Shape:
                circle(radius: Int)
                rect(w: Int, h: Int)
                empty

            def width(s: Shape) => Int:
                match s:
                    case Shape::rect(w, _):
                        w
                    case _:
                        0

            width(Shape::rect(5, 9)) + width(Shape::empty)
        "#},
        Value::Int(5),
    );
}

/// A parameterised type's arm binds its parameter at the scrutinee's argument.
#[test]
fn a_parameterised_arm_binds_at_the_argument() {
    check_scalar(
        indoc! {r#"
            type Maybe(T):
                just(T)
                nothing

            def or_zero(m: Maybe(Int)) => Int:
                match m:
                    case Maybe::just(v):
                        v
                    case Maybe::nothing:
                        0

            or_zero(Maybe::just(7)) + or_zero(Maybe::nothing)
        "#},
        Value::Int(7),
    );
}

/// A type with one constructor is taken apart by assignment, and the binder keeps the
/// constructor's refinement.
#[test]
fn a_single_constructor_type_destructures_by_assignment() {
    check_scalar(
        indoc! {r#"
            type Price = {Int where _ >= 0}

            def half(n: {Int where _ >= 0}) => Int:
                n // 2

            p = Price::new(10)
            Price::new(c) = p
            half(c)
        "#},
        Value::Int(5),
    );
}

#[test]
fn a_record_payload_destructures_and_projects() {
    check_scalar(
        indoc! {r#"
            type Price = {amount: Int}

            Price::new(r) = Price::new((amount=3))
            r.amount
        "#},
        Value::Int(3),
    );
}

#[test]
fn match_errors_name_what_is_wrong() {
    for (src, needle) in [
        (
            indoc! {r#"
                type Shape:
                    circle(radius: Int)
                    rect(w: Int, h: Int)

                def area(s: Shape) => Int:
                    match s:
                        case Shape::circle(r):
                            r

                area(Shape::circle(1))
            "#},
            "`match` over `Shape` has no arm for `Shape::rect`",
        ),
        (
            indoc! {r#"
                type Shape:
                    circle(radius: Int)
                    rect(w: Int, h: Int)

                def area(s: Shape) => Int:
                    match s:
                        case Shape::rect(w):
                            w
                        case _:
                            0

                area(Shape::circle(1))
            "#},
            "declares 2 parameters, so its pattern binds 2; this one binds 1",
        ),
        (
            indoc! {r#"
                type Light:
                    on
                    off

                def lit(l: Light) => Int:
                    match l:
                        case Light::on(x):
                            1
                        case _:
                            0

                lit(Light::on)
            "#},
            "`Light::on` declares no parameters, so its pattern takes no parentheses",
        ),
        (
            indoc! {r#"
                type Light:
                    on
                    off

                def lit(l: Light) => Int:
                    match l:
                        case Light::on:
                            1
                        case `off:
                            0

                lit(Light::on)
            "#},
            "mixes variant tags and constructors",
        ),
        (
            indoc! {r#"
                type Light:
                    on
                    off
                type Door:
                    open
                    shut

                def lit(l: Light) => Int:
                    match l:
                        case Light::on:
                            1
                        case Door::open:
                            0

                lit(Light::on)
            "#},
            "names constructors of `Light` and of `Door`",
        ),
        (
            indoc! {r#"
                type Shape:
                    circle(radius: Int)
                    rect(w: Int, h: Int)

                Shape::circle(r) = Shape::circle(1)
                r
            "#},
            "`Shape` declares 2 constructors, so a pattern naming one of them can fail",
        ),
        (
            indoc! {r#"
                type Light:
                    on
                    off
                type Door:
                    open
                    shut

                def lit(l: Light) => Int:
                    match l:
                        case Door::open:
                            1
                        case _:
                            0

                lit(Light::on)
            "#},
            "Type mismatch for Case scrutinee: expected Door, found Light",
        ),
        (
            indoc! {r#"
                type Light:
                    on
                    off

                def lit(l: Light) => Int:
                    match l:
                        case Light::on:
                            1
                        case Light::on:
                            2
                        case _:
                            0

                lit(Light::on)
            "#},
            "`match` has two `case Light::on` arms",
        ),
        (
            indoc! {r#"
                type Light:
                    on
                    off
                type Door:
                    on
                    shut

                def lit(l: Light) => Int:
                    match l:
                        case Light::on:
                            1
                        case Door::on:
                            2
                        case _:
                            0

                lit(Light::on)
            "#},
            "names constructors of `Light` and of `Door`",
        ),
        (
            indoc! {r#"
                def lit(l):
                    match l:
                        case Lamp::on:
                            1
                        case _:
                            0

                lit(1)
            "#},
            "`Lamp` is not a nominal type this module declares",
        ),
        (
            indoc! {r#"
                type Light:
                    on
                    off

                def lit(l: Light) => Int:
                    match l:
                        case Light::dim:
                            1
                        case _:
                            0

                lit(Light::on)
            "#},
            "`Light` declares no constructor `dim`",
        ),
        (
            indoc! {r#"
                type Price = Int

                for Price::new(c) in [Price::new(1)]:
                    c
                1
            "#},
            "a constructor pattern takes a value apart only in a plain `=` assignment",
        ),
        (
            indoc! {r#"
                def f(x):
                    match x:
                        case shop::Shape::circle(r):
                            r
                        case _:
                            0

                f(1)
            "#},
            "the qualified type `shop::Shape` is not supported yet",
        ),
    ] {
        check_compile_error(src, needle);
    }
}

/// The single-constructor form declares `extract`, which answers the constructor's
/// argument, and is a function value too.
#[test]
fn extract_answers_the_single_constructors_argument() {
    check_scalar(
        indoc! {r#"
            type Price = {amount: Int}

            p = Price::new((amount=3))
            get = Price::extract
            Price::extract(p).amount + get(p).amount
        "#},
        Value::Int(6),
    );
    check_scalar(
        indoc! {r#"
            type Wrap(T) = T

            Wrap::extract(Wrap::new(4)) + 1
        "#},
        Value::Int(5),
    );
}

/// Only the single-constructor form declares `extract`.
#[test]
fn a_constructor_list_declares_no_extract() {
    check_compile_error(
        indoc! {r#"
            type Shape:
                circle(radius: Int)

            Shape::extract(Shape::circle(1))
        "#},
        "`Shape` declares no constructor `extract`",
    );
}

/// An arm's binder shadows an outer binding of the same name, a transactional mutable
/// variable included, whose read outside a `with begin():` block would otherwise be refused.
#[test]
fn a_constructor_arms_binder_shadows_an_outer_name() {
    check_scalar(
        indoc! {r#"
            type Shape:
                circle(radius: Int)

            r: Mut(Int, Txn) := 0
            def radius(s: Shape) => Int:
                match s:
                    case Shape::circle(r):
                        r

            radius(Shape::circle(4))
        "#},
        Value::Int(4),
    );
}
