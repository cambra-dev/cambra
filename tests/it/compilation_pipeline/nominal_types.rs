//! Nominal types: `type` declarations and their constructors (`docs/chl-spec.md`,
//! "6.8 Nominal types and methods [Decided]").
//!
//! A nominal value is held as its constructor's name and argument, so a program whose
//! value is one observes the tagged value the constructor built.

use indoc::indoc;

use cambra::ccl::FieldKey;
use cambra::interpreter::Value;

use super::helpers::{check_compile_error, check_scalar, make_record, make_tuple};

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
    if let Err(payload) = std::panic::catch_unwind(|| super::helpers::run_pipeline(src)) {
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
/// declared above it.
#[test]
fn aliases_and_nominal_types_name_each_other() {
    check_scalar(
        indoc! {r#"
            Cents = Int

            type Order:
                placed(Cents)

            Placed = {Order, Cents}

            p: Placed = (Order::placed(5), 5)
            p.0
        "#},
        ctor("placed", Value::Int(5)),
    );
}

/// A constructor's parameter type may name a refined alias. The constructor is bound
/// outside the alias's declaration, so its predicate names no binding (`src/ccl/design/ir.md`,
/// "Type aliases resolve where they are declared").
#[test]
fn a_constructor_parameter_may_name_a_refined_alias() {
    check_scalar(
        indoc! {r#"
            Count = {Int where _ >= 0}

            type Stock:
                held(Count)

            def restock(n: Count) => Stock:
                Stock::held(n)

            restock(2)
        "#},
        ctor("held", Value::Int(2)),
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
            "`Shape` declares no constructor or function `square`",
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

/// A constructor of several parameters destructures by assignment into one name per
/// parameter, `_` declining one, at the top level and in a `def`.
#[test]
fn a_constructor_of_several_parameters_destructures_by_assignment() {
    check_scalar(
        indoc! {r#"
            type Pair:
                pair(Int, Int)

            def diff(p: Pair) => Int:
                Pair::pair(a, b) = p
                a - b

            Pair::pair(x, y) = Pair::pair(3, 4)
            Pair::pair(_, z) = Pair::pair(5, 6)
            x * y + z + diff(Pair::pair(9, 4))
        "#},
        Value::Int(23),
    );
}

/// A destructuring assignment in a loop body that writes a mutable variable binds its
/// A destructuring assignment inside a transaction block binds per-transaction locals, as
/// `x = 𝑣` does there.
#[test]
fn a_destructuring_assignment_in_a_transaction() {
    check_scalar(
        indoc! {r#"
            type Price = Int

            c: Mut(Int, Txn) := 0
            with begin():
                Price::new(x) = Price::new(3)
                c := c + x
            await_final(c)
        "#},
        Value::Int(3),
    );
}

/// names for the rest of the iteration, as `x = e` does.
#[test]
fn a_destructuring_assignment_in_a_loop_that_accumulates() {
    check_scalar(
        indoc! {r#"
            type Price = Int

            type Pair:
                pair(Int, Int)

            total := 0
            for p in [Pair::pair(1, 2), Pair::pair(3, 4)]:
                Pair::pair(a, b) = p
                Price::new(c) = Price::new(a * b)
                total := total + c
            total
        "#},
        Value::Int(14),
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
                type Pair:
                    pair(Int, Int)

                match Pair::pair(1, 2):
                    case Pair::pair(a, a):
                        a
            "#},
            "`a` is bound twice in the pattern `Pair::pair(…)`",
        ),
        (
            indoc! {r#"
                type Pair:
                    pair(Int, Int)

                Pair::pair(a, a) = Pair::pair(1, 2)
                a
            "#},
            "`a` is bound twice in the pattern `Pair::pair(…)`",
        ),
        // A nominal value is not a variant, and a variant is not a nominal value, though
        // the one is represented as the other.
        (
            indoc! {r#"
                type Light:
                    on
                    off

                match Light::on:
                    case `on:
                        1
                    case `off:
                        0
            "#},
            "Type mismatch for Case scrutinee: expected {`off{",
        ),
        (
            indoc! {r#"
                type Light:
                    on
                    off

                match `on(()):
                    case Light::on:
                        1
                    case Light::off:
                        0
            "#},
            "expected Light, found {`on}",
        ),
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
        "`Shape` declares no constructor or function `extract`",
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

// ---------------------------------------------------------------------------
// Associated functions and methods
// ---------------------------------------------------------------------------

#[test]
fn an_associated_function_is_reached_through_its_type() {
    check_scalar(
        indoc! {r#"
            type Price = Int

            def Price::of_cents(c: Int) => Price:
                Price::new(c)

            make = Price::of_cents
            Price::extract(Price::of_cents(250)) + Price::extract(make(5))
        "#},
        Value::Int(255),
    );
}

/// A method is an associated function whose first parameter is `self`, called on a
/// value of its type or through the type.
#[test]
fn a_method_is_called_on_its_receiver() {
    check_scalar(
        indoc! {r#"
            type Price = Int

            def Price::cents(self) => Int:
                Price::extract(self)

            def Price::discounted(self, pct: Int) => Price:
                Price::new(self.cents() - self.cents() * pct // 100)

            p = Price::new(200)
            p.discounted(10).cents() + Price::cents(p)
        "#},
        Value::Int(380),
    );
}

#[test]
fn extract_is_a_method() {
    check_scalar(
        indoc! {r#"
            type Price = {amount: Int}

            Price::new((amount=3)).extract().amount
        "#},
        Value::Int(3),
    );
}

/// Two types may each declare a method of one name; the receiver's type picks.
#[test]
fn the_receiver_picks_among_same_named_methods() {
    check_scalar(
        indoc! {r#"
            type Shape:
                circle(radius: Int)
                rect(w: Int, h: Int)

            type Price = Int

            def Shape::size(self) => Int:
                match self:
                    case Shape::circle(r):
                        r
                    case Shape::rect(w, h):
                        w * h

            def Price::size(self) => Int:
                self.extract()

            Shape::rect(2, 3).size() + Price::new(10).size()
        "#},
        Value::Int(16),
    );
}

/// An `impl` block declares a parameterised type's methods with its parameters bound once,
/// and one method calls another through `self`.
#[test]
fn an_impl_block_binds_the_types_parameters() {
    check_scalar(
        indoc! {r#"
            type Maybe(T):
                just(T)
                nothing

            impl Maybe(T):
                def or_else(self, d: T) => T:
                    match self:
                        case Maybe::just(v):
                            v
                        case Maybe::nothing:
                            d

                def unwrap_or(self, d: T) => T:
                    self.or_else(d)

            m: Maybe(Int) = Maybe::just(7)
            n: Maybe(Int) = Maybe::nothing
            m.or_else(0) + n.unwrap_or(5)
        "#},
        Value::Int(12),
    );
}

/// A receiver's type is known from what precedes the call: a loop variable's from its
/// source, a mutable variable's from its declaration, and a parameter's from the
/// annotation the method's `def` writes on `self` outside an `impl` block.
#[test]
fn a_receivers_type_comes_from_what_precedes_the_call() {
    check_scalar(
        indoc! {r#"
            type Price = Int

            def Price::cents(self) => Int:
                self.extract()

            total := 0
            for p in [Price::new(1), Price::new(2)]:
                total := total + p.cents()
            total
        "#},
        Value::Int(3),
    );
    check_scalar(
        indoc! {r#"
            type Price = Int

            s: Mut(Price) := Price::new(1)
            for i in [1, 2]:
                s := Price::new(i)
            s.extract()
        "#},
        Value::Int(2),
    );
    check_scalar(
        indoc! {r#"
            type Box(T):
                boxed(T)

            def Box::get(T, self: Box(T)) => T:
                match self:
                    case Box::boxed(v):
                        v

            Box::boxed(5).get()
        "#},
        Value::Int(5),
    );
}

/// A comprehension's clauses precede its element, so a generator's source gives the
/// element's receiver its type, in a guard and through a nested generator too.
#[test]
fn a_comprehensions_clauses_type_its_elements_receiver() {
    check_scalar(
        indoc! {r#"
            type Price = Int

            def Price::cents(self) => Int:
                self.extract()

            ps = [Price::new(1), Price::new(2), Price::new(3)]
            a = sum([p.cents() for p in ps if p.cents() > 1])
            b = sum([p.cents() * q.cents() for p in ps for q in [Price::new(10)]])
            a + b
        "#},
        Value::Int(65),
    );
}

/// A method call holds every type's same-named method as a candidate, and only the chosen
/// one is emitted: another type's method declared after the call is no error.
#[test]
fn an_unchosen_candidate_declared_later_is_no_error() {
    check_scalar(
        indoc! {r#"
            type A = Int
            type B = Int

            def A::m(self) => Int:
                1

            def f(a: A) => Int:
                a.m()

            def B::m(self) => Int:
                2

            f(A::new(1))
        "#},
        Value::Int(1),
    );
}

#[test]
fn method_errors_name_what_is_wrong() {
    for (src, needle) in [
        (
            indoc! {r#"
                type Price = Int

                def Price::cents(self) => Int:
                    self.extract()

                def f(T, x: T) => Int:
                    x.cents()

                f(Price::new(1))
            "#},
            "`T` is not a nominal type, so it has no methods",
        ),
        (
            indoc! {r#"
                type Price = Int

                def Price::cents(self) => Int:
                    self.extract()

                Price::new(1).cents(2)
            "#},
            "`Price::cents` takes 0 arguments after `self`, got 1",
        ),
        (
            indoc! {r#"
                type Price = Int

                def Price::plus(self, n: Int) => Int:
                    self.extract() + n

                Price::new(1).plus()
            "#},
            "`Price::plus` takes 1 argument after `self`, got 0",
        ),
        (
            indoc! {r#"
                type Price = Int

                Price::new(1).extract(2)
            "#},
            "`Price::extract` takes 0 arguments after `self`, got 1",
        ),
        (
            indoc! {r#"
                type A = Int

                def f(a: A) => Int:
                    a.m()

                def A::m(self) => Int:
                    1

                f(A::new(1))
            "#},
            "Unbound variable: 'A::m'",
        ),
        (
            indoc! {r#"
                type Price = Int

                def Price::cents(self) => Int:
                    self.extract()

                def total(p):
                    p.cents()

                total(Price::new(1))
            "#},
            "nothing before the call determines that type; annotate the receiver",
        ),
        (
            indoc! {r#"
                type Price = Int

                def Price::cents(self) => Int:
                    self.extract()

                r = (cents=1)
                r.cents()
            "#},
            "is not a nominal type, so it has no methods",
        ),
        (
            indoc! {r#"
                type Price = Int
                type Cost = Int

                def Price::cents(self) => Int:
                    self.extract()

                Cost::new(1).cents()
            "#},
            "`Cost` has no method `cents`",
        ),
        (
            indoc! {r#"
                type Price = Int

                Price::new(1).cents()
            "#},
            "no type this module declares has a method `cents`",
        ),
        (
            indoc! {r#"
                type Price = Int

                def Price::new(c: Int) => Price:
                    Price::new(c)

                1
            "#},
            "`Price::new` is already declared",
        ),
        (
            indoc! {r#"
                type Price = Int

                def Price::a(self) => Int:
                    1

                impl Price:
                    def a(self) => Int:
                        2

                1
            "#},
            "first declared here",
        ),
        (
            indoc! {r#"
                type Price = Int

                def Price::zero() => Price:
                    Price::new(0)

                1
            "#},
            "`Price::zero` declares no parameters",
        ),
        (
            indoc! {r#"
                type Box(T):
                    boxed(T)

                def Box::get(self) => Int:
                    1

                1
            "#},
            "`self` of `Box::get` needs its type",
        ),
        (
            indoc! {r#"
                def Lamp::on(self) => Int:
                    1

                1
            "#},
            "`Lamp` is not a nominal type this module declares",
        ),
        (
            indoc! {r#"
                type Price = Int

                def f(x):
                    def Price::g(self) => Int:
                        1
                    x

                f(1)
            "#},
            "an associated function is declared at a module's top level",
        ),
        (
            indoc! {r#"
                type A = Int
                type B = Int

                def A::size(self) => Int:
                    1
                def B::size(self) => Int:
                    2

                def pick(c: Bool):
                    if c:
                        A::new(1)
                    else:
                        B::new(1)

                pick(True).size()
            "#},
            "is called on a value stated to be both",
        ),
        (
            indoc! {r#"
                type Box(T):
                    boxed(T)

                impl Box:
                    def get(self) => Int:
                        1

                1
            "#},
            "`Box` takes 1 type parameter, and `impl Box` names 0",
        ),
        (
            indoc! {r#"
                type Price = Int
                type Cost = Int

                impl Price:
                    def Cost::f(self) => Int:
                        1

                1
            "#},
            "a `def` in `impl Price:` belongs to `Price`",
        ),
        (
            indoc! {r#"
                type Price = Int

                def Price::add(self, total: Mut(Int)) => Int:
                    1

                1
            "#},
            "an associated function with a pass-by-reference parameter is not supported yet",
        ),
        (
            indoc! {r#"
                type Price = Int

                impl Price:
                    def a(self) => Int:
                        self.b()
                    def b(self) => Int:
                        self.a()

                1
            "#},
            "call each other in a cycle",
        ),
        (
            indoc! {r#"
                type Price = Int

                impl Price:
                    def a(self) => Int:
                        self.a()

                1
            "#},
            "`Price::a` calls itself; a function does not reach itself",
        ),
        (
            indoc! {r#"
                type A = Int
                type B = Int

                impl A:
                    def f(self: B) => Int:
                        1

                1
            "#},
            "`self` of `A::f` is the `A` the block declares functions of, and takes no \
             annotation",
        ),
        (
            indoc! {r#"
                type Price = Int

                def Price::f(self: Price) => Int:
                    1

                1
            "#},
            "`self` of `Price::f` is a `Price`, and takes no annotation",
        ),
        (
            indoc! {r#"
                type Box(T) = T

                def Box::f(T, self: Box(Int)) => Int:
                    1

                1
            "#},
            "`self` of `Box::f` is `Box` at type parameters of the function's own, each named \
             once: `self: Box(T)`",
        ),
        (
            indoc! {r#"
                type Price = Int

                def Price::f(x: Int, self) => Int:
                    1

                1
            "#},
            "`self` of `Price::f` is not its first parameter",
        ),
        (
            indoc! {r#"
                t = (\x -> x + 1, 2)
                t.0(1)
            "#},
            "`.0(…)` calls a method, and `0` is a position, which names no method; the function \
             element 0 holds is called as `(t.0)(…)`",
        ),
        (
            indoc! {r#"
                r = (f=\x -> x + 1)
                r.f(1)
            "#},
            "no type this module declares has a method `f`; the function a field holds is \
             called as `(r.f)(…)`",
        ),
    ] {
        check_compile_error(src, needle);
    }
}

/// The functions of an `impl` block reach each other in any order.
#[test]
fn an_impl_blocks_functions_reach_each_other() {
    check_scalar(
        indoc! {r#"
            type Price = Int

            impl Price:
                def doubled(self) => Int:
                    self.cents() * 2
                def cents(self) => Int:
                    self.extract()

            Price::new(21).doubled()
        "#},
        Value::Int(42),
    );
}

/// What states a receiver's type before its call, which is what resolves the call
/// (`src/ccl/design/nominal-types.md`, "Method calls"): the receiver's own expression, a
/// binding's definition, a parameter's annotation, a function's declared result, a
/// comprehension's source, and an earlier call of the chain. A use after the call does not.
#[test]
fn what_states_a_receivers_type_before_its_call() {
    check_scalar(
        indoc! {r#"
            type Price = Int

            impl Price:
                def cents(self) => Int:
                    self.extract()
                def plus(self, n: Int) => Price:
                    Price::new(self.cents() + n)

            def of(c: Int) => Price:
                Price::new(c)

            def cents_of(p: Price) => Int:
                p.cents()

            p = Price::new(1)
            each = sum([q.cents() for q in [Price::new(10), Price::new(20)]])
            chained = Price::new(0).plus(5000).cents()
            Price::new(100).cents() + p.cents() + cents_of(p) + of(1000).cents() + each + chained
        "#},
        Value::Int(6132),
    );
    for src in [
        indoc! {r#"
            type Price = Int

            def Price::cents(self) => Int:
                self.extract()

            f = \x -> x.cents()
            f(Price::new(1))
        "#},
        indoc! {r#"
            type Price = Int

            def Price::cents(self) => Int:
                self.extract()

            def g(p) => Int:
                p.cents()

            g(Price::new(1))
        "#},
    ] {
        check_compile_error(src, "nothing before the call determines that type");
    }
}

/// A call that only its receiver's type resolves reaches a function the block declares
/// after the caller, whichever order the block declares them in.
#[test]
fn a_call_its_receiver_resolves_reaches_a_later_function() {
    for a_block in [
        indoc! {r#"
            impl A:
                def y(self, b: B) => Int:
                    b.x()
                def x(self, b: B) => Int:
                    self.y(b) + 10
        "#},
        indoc! {r#"
            impl A:
                def x(self, b: B) => Int:
                    self.y(b) + 10
                def y(self, b: B) => Int:
                    b.x()
        "#},
    ] {
        let src = format!(
            "{}{a_block}\nA::new(1).x(B::new(2))\n",
            indoc! {r#"
                type A = Int
                type B = Int

                impl B:
                    def x(self) => Int:
                        1
                    def y(self) => Int:
                        2

            "#}
        );
        check_scalar(&src, Value::Int(11));
    }
}

/// A function of a block with type parameters is polymorphic to the block's other functions,
/// each call at its own types.
#[test]
fn a_blocks_generic_function_is_polymorphic_to_its_siblings() {
    check_scalar(
        indoc! {r#"
            type Price = Int

            impl Price:
                def both(self) => Int:
                    self.pick(self.cents(), 0) if self.pick(True, False) else 0
                def pick(T, self, a: T, b: T) => T:
                    a
                def cents(self) => Int:
                    self.extract()

            Price::new(7).both()
        "#},
        Value::Int(7),
    );
}

/// Two functions of a block that each call the other's name on another type's value do not
/// call each other: each call resolves by its receiver, here to `B`'s methods.
#[test]
fn same_named_calls_on_another_type_are_no_cycle() {
    check_scalar(
        indoc! {r#"
            type A = Int
            type B = Int

            impl B:
                def x(self) => Int:
                    1
                def y(self) => Int:
                    2

            impl A:
                def x(self, b: B) => Int:
                    b.y()
                def y(self, b: B) => Int:
                    b.x()

            A::new(1).x(B::new(2)) * 10 + A::new(1).y(B::new(2))
        "#},
        Value::Int(21),
    );
}

/// A method may call the same-named method of another type.
#[test]
fn a_method_delegates_to_another_types_same_named_method() {
    check_scalar(
        indoc! {r#"
            type Price = Int
            type Order = Price

            def Price::size(self) => Int:
                self.extract()

            impl Order:
                def size(self) => Int:
                    self.extract().size() + 1

            Order::new(Price::new(4)).size()
        "#},
        Value::Int(5),
    );
}

// ---------------------------------------------------------------------------
// The compiler-provided `Option`
// ---------------------------------------------------------------------------

/// `Option(T)` is a nominal type the compiler provides, built by `Option::some` and
/// `Option::none` and taken apart by arms naming them.
#[test]
fn option_is_built_and_matched_by_its_constructors() {
    check_scalar(
        indoc! {r#"
            def or_zero(o: Option(Int)) => Int:
                match o:
                    case Option::some(v):
                        v
                    case Option::none:
                        0

            wrap = Option::some
            or_zero(Option::some(4)) + or_zero(Option::none) + or_zero(wrap(3))
        "#},
        Value::Int(7),
    );
}

/// A checked lookup answers an `Option` of the value type.
#[test]
fn a_checked_lookup_answers_an_option() {
    check_scalar(
        indoc! {r#"
            m = map([(1, 10), (2, 20)])
            a: Option(Int) = m[1]?
            match a:
                case Option::some(v):
                    v
                case Option::none:
                    0
        "#},
        Value::Int(10),
    );
}

/// `Option::is_none` is a method the compiler provides with `Option`.
#[test]
fn option_declares_is_none() {
    check_scalar(
        indoc! {r#"
            m = map([(1, 10)])
            (m[2]?.is_none(), Option::is_none(m[1]?))
        "#},
        make_tuple(&[Value::Bool(true), Value::Bool(false)]),
    );
}

/// `.is_none()` as an `if` condition: the `match` it is puts a value-selecting `Case`'s form in
/// the gate predicate of each of the `if`'s arms.
#[rstest_log::rstest]
#[case::absent("1 if m[2]?.is_none() else 0", Value::Int(1))]
#[case::present("1 if m[1]?.is_none() else 0", Value::Int(0))]
#[case::elif(
    "5 if m[1]?.is_none() else (7 if m[4]?.is_none() else 9)",
    Value::Int(7)
)]
#[case::conjunction("1 if m[2]?.is_none() and 2 > 1 else 0", Value::Int(1))]
#[case::per_element(
    "sum([100 if m[k]?.is_none() else k for k in [1, 2, 3]])",
    Value::Int(104)
)]
fn is_none_as_a_condition(#[case] tail: &str, #[case] expected: Value) {
    check_scalar(&format!("m = map([(1, 10), (3, 30)])\n{tail}"), expected);
}

/// A type declaring its own `is_none` keeps it beside `Option`'s: each `.is_none()` call
/// resolves by its receiver's type.
#[test]
fn a_type_s_own_is_none_beside_option_s() {
    check_scalar(
        indoc! {r#"
            type Light:
                on
                off

            def Light::is_none(self) => Bool:
                match self:
                    case Light::on:
                        False
                    case Light::off:
                        True

            m = map([(1, 10)])
            (Light::off.is_none(), m[1]?.is_none(), Light::on.is_none(), m[2]?.is_none())
        "#},
        make_tuple(&[
            Value::Bool(true),
            Value::Bool(false),
            Value::Bool(false),
            Value::Bool(true),
        ]),
    );
}

#[test]
fn option_errors_name_what_is_wrong() {
    for (src, needle) in [
        (
            indoc! {r#"
                x: Option(Int) = `some(1)
                x
            "#},
            "annotated as Option(Int), but inferred as {`some{Int where _ == 1}}",
        ),
        (
            indoc! {r#"
                x: Option(Int) = `some(1)
                x
            "#},
            "hint: `Option` is a nominal type, not a variant: build one with `Option::some(v)`",
        ),
        (
            indoc! {r#"
                m = map([(1, 10)])
                match m[1]?:
                    case `some(v):
                        v
                    case `none:
                        0
            "#},
            "and match one with `case Option::some(v):` and `case Option::none:`",
        ),
        (
            indoc! {r#"
                type Option(T):
                    some(T)

                1
            "#},
            "`Option` is a built-in type and cannot be given another meaning",
        ),
        (
            indoc! {r#"
                def Option::get(T, self: Option(T), d: T) => T:
                    d

                1
            "#},
            "`Option` is a built-in type, so this module declares no associated function of it",
        ),
        (
            indoc! {r#"
                x: Option = Option::none
                x
            "#},
            "`Option` takes 1 type argument, got 0",
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

/// A boxed payload is the collection it boxes when it is taken back out.
#[test]
fn a_boxed_payload_reads_back_as_its_collection() {
    check_scalar(
        indoc! {"
            type Bag(T) = List(T)
            sum(Bag::extract(Bag::new(box([1, 2, 3]))))
        "},
        Value::Int(6),
    );
}

/// A chain of `.extract()` calls on a value nested ten deep, each call specializing `extract`
/// at the next type down.
///
/// Each call's result is read through every bound its variable has gathered, and
/// constraining one variable below another copies the lower one's bounds onto it, so
/// compaction reaches one variable along many paths: it reads each once per walk. And each
/// specialization's pin crosses into the clones earlier ones pinned, so extrusion copies
/// them, once per walk rather than once per edge. Either one per path took several times as
/// long at each call as at the one before.
#[test]
fn a_chain_of_extracts_on_a_deeply_nested_value() {
    let start = std::time::Instant::now();
    check_scalar(
        indoc! {"
            type One(T) = T
            c0 = 1
            c1 = One::new(c0)
            c2 = One::new(c1)
            c3 = One::new(c2)
            c4 = One::new(c3)
            c5 = One::new(c4)
            c6 = One::new(c5)
            c7 = One::new(c6)
            c8 = One::new(c7)
            c9 = One::new(c8)
            c10 = One::new(c9)
            c10.extract().extract().extract().extract().extract().extract().extract().extract().extract().extract()
        "},
        Value::Int(1),
    );
    // A debug build compiles this in a few seconds, and CI's runner in about ten; per path,
    // it took over a minute.
    assert!(
        start.elapsed() < std::time::Duration::from_secs(30),
        "compiling took {:?}",
        start.elapsed()
    );
}
