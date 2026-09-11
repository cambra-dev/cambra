//! Type-alias statements: `Name = <type expression>` (`docs/chl-spec.md`,
//! "6.7 Type-alias statements").
//!
//! An alias names an existing type, so every case here pins *interchangeability*:
//! the alias is accepted where the type it names is, and rejected where that type
//! would be.

use indoc::indoc;

use crate::helpers::{check_compile_error, check_scalar};

use cambra::ccl::BaseType;
use cambra::ccl::lower::{RESERVED_TYPE_NAMES, is_builtin_type_name};
use cambra::interpreter::Value;

#[test]
fn alias_of_a_base_type_annotates_a_binding() {
    check_scalar(
        indoc! {r#"
            MyInt = Int

            x: MyInt = 4
            x + 1
        "#},
        Value::Int(5),
    );
}

#[test]
fn alias_annotates_def_params_and_output() {
    check_scalar(
        indoc! {r#"
            Cents = Int

            def add(a: Cents, b: Cents) => Cents:
                a + b

            add((4, -1))
        "#},
        Value::Int(3),
    );
}

/// An alias is not a nominal type: a value typed by the aliased type flows into
/// the alias's position and back out, with no conversion anywhere.
#[test]
fn alias_and_its_type_are_interchangeable() {
    check_scalar(
        indoc! {r#"
            MyInt = Int

            def as_alias(a: Int) => MyInt:
                a

            def as_base(a: MyInt) => Int:
                a

            y: Int = as_base(as_alias(7))
            y
        "#},
        Value::Int(7),
    );
}

/// Two aliases of one type are the same type, which is what "structural, not
/// nominal" buys: nothing distinguishes them at a boundary.
#[test]
fn two_aliases_of_one_type_are_one_type() {
    check_scalar(
        indoc! {r#"
            Cents = Int
            Pennies = Int

            def widen(a: Cents) => Pennies:
                a

            z: Cents = widen(6)
            z
        "#},
        Value::Int(6),
    );
}

#[test]
fn alias_of_a_record_type() {
    check_scalar(
        indoc! {r#"
            Item = {price: Int, cost: Int}

            def margin(i: Item) => Int:
                i.price - i.cost

            margin((price=10, cost=4))
        "#},
        Value::Int(6),
    );
}

/// A refinement carried by an alias reaches the signature exactly as the brace
/// form would: the predicate is discharged against the body, not weakened by the
/// name.
#[test]
fn alias_of_a_refinement_type_carries_its_predicate() {
    check_scalar(
        indoc! {r#"
            Nine = {Int where _ == 9}

            def itsa_nine(a) => Nine:
                9

            itsa_nine("dummy_arg")
        "#},
        Value::Int(9),
    );
}

/// A refined alias is lowered once and its predicate substituted at each use, so
/// two uses share one predicate term. A hand-written annotation never produces
/// that sharing, which is why the two-use case is pinned separately.
#[test]
fn a_refined_alias_used_twice_shares_one_predicate() {
    check_scalar(
        indoc! {r#"
            Nine = {Int where _ == 9}

            def left(a) => Nine:
                9

            def right(a) => Nine:
                9

            left("x") + right("y")
        "#},
        Value::Int(18),
    );
}

#[test]
fn alias_of_a_refinement_type_rejects_a_violating_body() {
    check_compile_error(
        indoc! {r#"
            Nine = {Int where _ == 9}

            def itsa_nine(a) => Nine:
                8

            itsa_nine("dummy_arg")
        "#},
        "Annotation mismatch",
    );
}

#[test]
fn alias_of_a_refinement_type_rejects_a_violating_argument() {
    check_compile_error(
        indoc! {r#"
            NonZero = {Int where _ != 0}

            def refined_div(left: Int, right: NonZero):
                left // right

            refined_div(2, 0)
        "#},
        "expected {Int | __elem != 0}",
    );
}

/// An alias is a type expression's name, so it reads as a type *argument* too.
#[test]
fn alias_as_a_type_argument() {
    check_scalar(
        indoc! {r#"
            Cents = Int

            xs: List(Cents) = box([1, 2, 3])
            sum(xs)
        "#},
        Value::Int(6),
    );
}

/// An alias's right-hand side is itself a type expression, so it may name aliases
/// declared above it.
#[test]
fn alias_built_from_another_alias() {
    check_scalar(
        indoc! {r#"
            Cents = Int
            Item = {price: Cents}
            Priced = Item

            def price_of(i: Priced) => Cents:
                i.price

            price_of((price=9,))
        "#},
        Value::Int(9),
    );
}

#[test]
fn alias_of_a_function_type() {
    check_scalar(
        indoc! {r#"
            Unary = (Int => Int)

            f: Unary = \x -> x * 3
            f(5)
        "#},
        Value::Int(15),
    );
}

#[test]
fn alias_of_a_variant_type() {
    check_scalar(
        indoc! {r#"
            Maybe = {`some{Int} | `none}

            def unwrap_or_zero(m: Maybe) => Int:
                match m:
                    case `some(v):
                        v
                    case `none:
                        0

            unwrap_or_zero(`some(8))
        "#},
        Value::Int(8),
    );
}

/// An alias is scoped to the block it sits in, so one declared in a `def` body is
/// gone at the end of it.
#[test]
fn alias_declared_in_a_def_body_does_not_escape() {
    check_compile_error(
        indoc! {r#"
            def inner(a: Int) => Int:
                Local = Int
                b: Local = a
                b

            c: Local = inner(1)
            c
        "#},
        "unknown type annotation: Local",
    );
}

/// An alias in an inner block shadows a same-named outer one for that block, and
/// the outer one is back afterwards.
#[test]
fn inner_alias_shadows_an_outer_one() {
    check_scalar(
        indoc! {r#"
            T = Int

            def tagged(a: T) => T:
                T = String
                label: T = "count"
                a

            d: T = tagged(5)
            d
        "#},
        Value::Int(5),
    );
}

/// Source order holds an alias's right-hand side to the aliases above it, so a
/// self-reference has nothing to resolve against.
#[test]
fn self_referential_alias_is_rejected() {
    check_compile_error(
        indoc! {r#"
            Loop = Loop

            x: Loop = 1
            x
        "#},
        "unknown type annotation: Loop",
    );
}

#[test]
fn alias_naming_a_later_alias_is_rejected() {
    check_compile_error(
        indoc! {r#"
            A = B
            B = Int

            x: A = 1
            x
        "#},
        "unknown type annotation: B",
    );
}

#[test]
fn rebinding_a_built_in_type_name_is_rejected() {
    check_compile_error(
        indoc! {r#"
            Int = String

            x: Int = "hi"
            x
        "#},
        "`Int` is a built-in type and cannot be given another meaning",
    );
}

/// Every name the refusal reads, refused. The base types come from
/// `BaseType::keyword` and the rest from `RESERVED_TYPE_NAMES`, which is the same
/// pair `is_builtin_type_name` consults, so this cannot drift from what it pins.
#[test]
fn builtin_type_names_are_refused() {
    let base = [
        BaseType::Int,
        BaseType::UInt,
        BaseType::String,
        BaseType::Bool,
        BaseType::Unit,
    ]
    .map(|b| b.keyword());
    for name in base
        .iter()
        .copied()
        .chain(RESERVED_TYPE_NAMES.iter().copied())
    {
        assert!(
            is_builtin_type_name(name),
            "`{name}` is listed here but not refused by `is_builtin_type_name`"
        );
        check_compile_error(
            &format!("{name} = Int\n\nx: Int = 1\nx\n"),
            &format!("`{name}` is a built-in type and cannot be given another meaning"),
        );
    }
}

#[test]
fn declaring_one_alias_twice_in_a_block_is_rejected() {
    check_compile_error(
        indoc! {r#"
            A = Int
            A = String

            x: A = 1
            x
        "#},
        "is declared twice in this block",
    );
}

/// The case of the name is the whole discriminator, so a capitalized target is
/// read as a type whatever sits on the right.
#[test]
fn a_term_on_the_right_of_a_capitalized_name_is_rejected() {
    check_compile_error(
        indoc! {r#"
            Five = 5

            x: Int = 1
            x
        "#},
        "declares a type alias and its right-hand side must be a type",
    );
}

/// A capitalized name is bound only by an alias, so every other statement form
/// rejects one and says so.
#[test]
fn a_capitalized_mutable_binder_is_rejected() {
    check_compile_error(
        indoc! {r#"
            Acc := 0

            for i in [1, 2, 3]:
                Acc += i

            Acc
        "#},
        "is capitalized, so it names a type, not a value",
    );
}

#[test]
fn a_capitalized_loop_target_is_rejected() {
    check_compile_error(
        indoc! {r#"
            total := 0

            for I in [1, 2, 3]:
                total += I

            total
        "#},
        "is capitalized, so it names a type, not a value",
    );
}

/// An alias leaves no trace in the lowered program: reading a type name as a term
/// is an unbound name, not a value.
#[test]
fn an_alias_name_is_not_a_value() {
    check_compile_error(
        indoc! {r#"
            MyInt = Int

            MyInt
        "#},
        "Unbound variable: 'MyInt'",
    );
}

/// A loop body is a block, so it declares aliases like any other.
#[test]
fn alias_declared_in_a_loop_body() {
    check_scalar(
        indoc! {r#"
            total := 0

            for i in [1, 2, 3]:
                Step = Int
                n: Step = i
                total += n

            total
        "#},
        Value::Int(6),
    );
}

#[test]
fn alias_declared_in_a_loop_body_does_not_escape() {
    check_compile_error(
        indoc! {r#"
            total := 0

            for i in [1, 2, 3]:
                Step = Int
                total += i

            leftover: Step = total
            leftover
        "#},
        "unknown type annotation: Step",
    );
}

/// A transactional mutable variable's value type is an ordinary type position,
/// so an alias stands where the type it names does. `Mut(V, Txn)` is read by
/// `pre_register_txn_decls`, which runs at block entry, so this is what pins the
/// alias declaration ahead of it.
#[test]
fn alias_is_the_value_type_of_a_transactional_variable() {
    check_scalar(
        indoc! {r#"
            Cents = Int

            balance: Mut(Cents, Txn) := 0

            for i in [1, 2, 3]:
                with begin():
                    balance := balance + i

            await_final(balance)
        "#},
        Value::Int(6),
    );
}

#[test]
fn alias_is_the_value_type_of_a_transactional_variable_in_a_nested_block() {
    check_scalar(
        indoc! {r#"
            def run(xs) => Int:
                Cents = Int
                balance: Mut(Cents, Txn) := 0
                for i in xs:
                    with begin():
                        balance := balance + i
                await_final(balance)

            run([1, 2, 3])
        "#},
        Value::Int(6),
    );
}

/// A `with begin():` body is a block too, so an alias statement is one of its
/// statements and leaves the transaction unchanged. The block admits no annotated
/// local binding, so nothing inside it yet reads the name.
#[test]
fn alias_declared_in_a_transaction_body() {
    check_scalar(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100

            for r in [10, 20, 30]:
                with begin():
                    Amount = Int
                    pool := pool - r

            await_final(pool)
        "#},
        Value::Int(40),
    );
}

#[test]
fn alias_declared_in_a_transaction_body_does_not_escape() {
    check_compile_error(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100

            for r in [10]:
                with begin():
                    Amount = Int
                    pool := pool - r

            leftover: Amount = 1
            leftover
        "#},
        "unknown type annotation: Amount",
    );
}
