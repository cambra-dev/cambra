use indoc::indoc;

use super::helpers::{check_compile_error, check_scalar, check_sink, check_sink_error};

use cambra::interpreter::Value;

/// `int_to_uint`'s result is refined by `int_eq_uint` to equal its argument, so the solver
/// proves two conversions of one `Int` equal. CHL has no `UInt` literal, so the bound is a name.
#[test]
fn int_to_uint_result_equals_its_argument() {
    check_scalar(
        indoc! {r#"
z = int_to_uint(1)
y: {UInt where _ == z} = int_to_uint(1)
y == z
        "#},
        Value::Bool(true),
    )
}

#[test]
fn int_to_uint_of_a_different_int_is_not_equal() {
    check_compile_error(
        indoc! {r#"
z = int_to_uint(1)
y: {UInt where _ == z} = int_to_uint(2)
y
        "#},
        "Annotation mismatch",
    )
}

#[test]
fn int_to_uint_takes_an_int() {
    check_compile_error("int_to_uint(\"one\")", "Type mismatch")
}

#[test]
fn int_to_uint_takes_one_argument() {
    check_compile_error(
        "int_to_uint(1, 2)",
        "`int_to_uint` takes exactly one argument",
    )
}

/// No `UInt` equals a negative `Int`, so the conversion stops execution rather than produce a
/// value its refinement does not admit.
#[test]
#[should_panic(expected = "int_to_uint applied to the negative Int -1")]
fn int_to_uint_of_a_negative_int_panics() {
    check_scalar("int_to_uint(0 - 1)", Value::UInt(0))
}

/// A checked lookup's key is bounded by the range's base, `UInt`, so a key inside the range
/// answers `some`.
#[test]
fn list_lookup_checked_some() {
    check_scalar(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(1)] == Option::some(2)
        "#},
        Value::Bool(true),
    )
}

/// A key outside the range types as a `UInt` and answers `none`.
#[test]
fn list_lookup_checked_negative() {
    check_scalar(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(3)] == Option::none
        "#},
        Value::Bool(true),
    )
}

/// The key's refinement entails the bound `__elem < 3`, so `{UInt | …} <: 0..3` holds.
#[test]
fn list_lookup_proven() {
    check_scalar(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(1)]! == 2
        "#},
        Value::Bool(true),
    )
}

/// `!` demands that the key `int_to_uint(5)` lie in `xs`'s domain `0..3`, which it does not.
#[test]
fn list_lookup_rejected() {
    check_compile_error(
        indoc! {r#"
xs = [1,2,3]
xs[int_to_uint(5)]! == 2
        "#},
        "Type mismatch for this call: expected {UInt where _ < 3}, found {UInt where 5 == _}",
    )
}

/// A checked lookup's result is refined by the judgment `k : 0..3` on `xs`'s domain, and `!`
/// demands it of `k`'s type, which `k`'s refinement meets.
#[test]
fn a_checked_lookup_at_a_present_key_is_some() {
    check_scalar(
        indoc! {r#"
xs = [1,2,3]
k = int_to_uint(1)
r = xs[k]
r!
        "#},
        Value::Int(2),
    )
}

/// `k`'s refinement refutes the judgment `k : 0..3`, so the result is `none`.
#[test]
fn a_checked_lookup_at_an_absent_key_is_none() {
    check_scalar(
        indoc! {r#"
xs = [1,2,3]
k = int_to_uint(3)
r: {Option(Int) where _.is_none()} = xs[k]
r.is_none()
        "#},
        Value::Bool(true),
    )
}

/// `!` demands of a lookup's key that it lie in the domain, which an absent key does not.
#[test]
fn unwrapping_a_checked_lookup_at_an_absent_key_is_rejected() {
    check_compile_error(
        indoc! {r#"
xs = [1,2,3]
k = int_to_uint(3)
r = xs[k]
r!
        "#},
        "expected {UInt where _ < 3}, found {UInt where 3 == _}",
    )
}

/// The answer's payload is typed at `xs`'s codomain, `{Int where _ > 0}`, so the payload of a
/// lookup at a present key meets it.
#[test]
fn a_checked_lookup_payload_meets_the_codomain_refinement() {
    check_scalar(
        indoc! {r#"
n = int_to_uint(3)
xs: {UInt where _ < n} |=> {Int where _ > 0} = [1,2,3]
k = int_to_uint(1)
r = xs[k]
v: {Int where _ > 0} = r!
v
        "#},
        Value::Int(2),
    )
}

/// The codomain's `_ > 0` is all the refinement states about the payload, so `_ > 1` is not
/// proven although the payload at `k` is `2`.
#[test]
fn a_checked_lookup_payload_is_known_only_through_the_codomain_refinement() {
    check_compile_error(
        indoc! {r#"
n = int_to_uint(3)
xs: {UInt where _ < n} |=> {Int where _ > 0} = [1,2,3]
k = int_to_uint(1)
r = xs[k]
v: {Int where _ > 1} = r!
v
        "#},
        "Annotation mismatch",
    )
}

/// An `Int` key is no key of a list, so the checked lookup is rejected, and so is a `!` of it,
/// whose binder is left with no definition to discharge.
#[test]
fn unwrapping_a_lookup_whose_key_does_not_type_reports_the_key() {
    for program in [
        indoc! {r#"
xs = [10, 20, 30]
xs[0]!
        "#},
        indoc! {r#"
xs = [10, 20, 30]
r = xs[0]
r!
        "#},
    ] {
        check_compile_error(
            program,
            "Type mismatch for checked lookup key: expected UInt, found Int",
        )
    }
}

/// `!` on a lookup at a lambda parameter bounds the parameter by the collection's domain, as
/// the application `xs(i)` does: `f` is `0..3 ⇒ Int`
/// (`src/ccl/design/collections.md`, "The checked lookup's refinement").
#[test]
fn a_proven_lookup_at_a_lambda_parameter_bounds_the_parameter() {
    check_scalar(
        indoc! {r#"
            xs = [1, 2, 3]
            f = \i -> xs[i]!
            f(int_to_uint(1))
        "#},
        Value::Int(2),
    )
}

/// A call of a function holding a proven lookup at its parameter must pass a present key.
#[test]
fn a_proven_lookup_at_a_lambda_parameter_rejects_an_absent_key() {
    check_compile_error(
        indoc! {r#"
            xs = [1, 2, 3]
            f = \i -> xs[i]!
            f(int_to_uint(5))
        "#},
        "expected {UInt where _ < 3}, found {UInt where 5 == _}",
    )
}

/// The demand `!` makes waits on the collection's domain, so a proven lookup is accepted into a
/// collection whose value type is unresolved when the lookup is emitted.
#[test]
#[ignore = "TODO: inference does not terminate: the payload variable takes `Option::value`'s dependent result as a bound"]
fn a_proven_lookup_into_a_mutable_list() {
    check_sink(
        indoc! {r#"
            xs := [1, 2, 3]
            out = test_sink()
            out << xs[int_to_uint(1)]!
        "#},
        "[() -> 2]",
    )
}

/// The inner lookup's collection is the outer lookup's answer, unresolved when the inner one is
/// emitted.
#[test]
#[ignore = "TODO: inference does not terminate: the payload variable takes `Option::value`'s dependent result as a bound"]
fn a_nested_proven_lookup() {
    check_sink(
        indoc! {r#"
            xss = [[1, 2], [3, 4]]
            out = test_sink()
            out << xss[int_to_uint(1)]![int_to_uint(0)]!
        "#},
        "[() -> 3]",
    )
}

/// A proven lookup whose value is a list, bound before it is consumed. Refinement erasure
/// rewrites the unwrap of the lookup into the application `int_to_uint(1) ▷ xss`, which converts
/// for a list-valued codomain.
#[test]
fn a_proven_lookup_of_a_row_of_a_list_of_lists() {
    check_sink(
        indoc! {r#"
            xss = [[1, 2], [3, 4]]
            r = xss[int_to_uint(1)]!
            out = test_sink()
            out << sum(r)
        "#},
        "[() -> 7]",
    )
}

// The proven lookups below fail although the key is present. Each test pins the current failure;
// when a failure is fixed, the test is rewritten to check the value.

/// TODO: Accept a proven lookup at a literal key of a collection built from its keys.
///
/// `!` demands that the key's type lie in the collection's domain, as the application `c(k)`
/// does, and each of these domains rejects a literal key's singleton. A `map(…)` or `set(…)`
/// domain states its keys as a list membership, which the solver does not decide. A
/// comprehension's domain joins with the key's singleton and the join narrows a data domain. A
/// filter's domain carries the filter's predicate. A `Map` annotation makes the collection a sum,
/// whose domain is its witness's.
#[test]
fn a_proven_lookup_into_a_collection_built_from_its_keys_is_rejected() {
    for (program, found) in [
        (
            indoc! {r#"
                m = map([1 -> 10, 2 -> 20])
                m[1]!
            "#},
            "expected {Int where _ in [1, 2]}, found {Int where _ == 1}",
        ),
        (
            indoc! {r#"
                m = map(["a" -> 10, "b" -> 20])
                k = "b"
                m[k]!
            "#},
            "expected {String where _ in [\"a\", \"b\"]}, found {String where _ == \"b\"}",
        ),
        (
            indoc! {r#"
                s = set([1, 2])
                s[1]!
            "#},
            "expected {Int where _ in [1, 2]}, found {Int where _ == 1}",
        ),
        (
            indoc! {r#"
                xs = [1, 2, 3]
                ys = [x + 1 for x in xs]
                ys[int_to_uint(0)]!
            "#},
            "Conflicting Domains: UInt vs {UInt where _ < 3}",
        ),
        (
            indoc! {r#"
                xs = [1, 2, 3]
                ys = [x for x in xs if x > 1]
                ys[int_to_uint(1)]!
            "#},
            "expected {{UInt where 1 == _} where xs[_]! > 1}, found {UInt where 1 == _}",
        ),
        (
            indoc! {r#"
                m: Map(Int, Int) = box(map([1 -> 10, 2 -> 20]))
                m[1]!
            "#},
            "expected ‹outer keys›, found {Int where _ == 1}",
        ),
    ] {
        check_compile_error(program, found);
    }
}

/// TODO: Refine a key by the `if` condition that guards its proven lookup.
///
/// An `if` condition does not refine the names it tests, so `i < int_to_uint(3)` in the guard
/// does not reach the lookup in its branch.
#[test]
fn a_proven_lookup_under_a_bound_guard_is_rejected() {
    check_compile_error(
        indoc! {r#"
            xs = [1, 2, 3]
            def f(i: UInt) => Int:
                if i < int_to_uint(3):
                    xs[i]!
                else:
                    0
            f(int_to_uint(1))
        "#},
        "expected {UInt where _ < 3}, found UInt",
    )
}

/// TODO: Accept a proven lookup at keys drawn from a list whose every key is present.
///
/// Inference accepts the edge from `i` to `xs`'s domain `0..3`, since each key in the list is
/// below 3, and then resolves `i` at the list's value type `UInt`, which the post-inference check
/// rejects. The application `xs(i)` meets the same edge and fails the same way.
#[test]
#[should_panic(
    expected = "post-inference produced an invalid tree: [Type mismatch for this call: expected \
                {UInt where _ < 3}, found UInt"
)]
fn a_proven_lookup_at_keys_drawn_from_a_key_list_fails_the_post_inference_check() {
    check_scalar(
        indoc! {r#"
            xs = [10, 20, 30]
            sum([xs[i]! for i in [int_to_uint(0), int_to_uint(2)]])
        "#},
        Value::Int(40),
    )
}

/// TODO: Parse `in`, and accept a proven lookup under a true `k in m.keys()`.
///
/// `docs/chl-spec.md`, "Membership expressions [Decided]" accepts `m[k]!` under a true
/// `k in m.keys()`. The parser does not accept `in` as an expression.
#[test]
fn a_proven_lookup_under_an_in_guard_does_not_parse() {
    check_compile_error(
        indoc! {r#"
            m = map([1 -> 10, 2 -> 20])
            k = 1
            if k in m.keys():
                m[k]!
            else:
                0
        "#},
        "found 'in'",
    )
}

/// TODO: Bind a map's keys in `for k -> v in m`, and accept `m[k]!` at them.
///
/// `docs/chl-spec.md`, "4.6 `for` — iteration" accepts `m[k]!` for a key from `for k -> v in m`.
/// Iterating a map binds its values, so the pattern's projection `.0` does not apply.
#[test]
fn a_proven_lookup_at_a_key_from_iterating_the_map_is_rejected() {
    check_compile_error(
        indoc! {r#"
            m = map([1 -> 10, 2 -> 20])
            sum([m[k]! for k -> v in m])
        "#},
        "Type mismatch for projection `.0`: expected {‹?1›, ..}, found Int",
    )
}

/// TODO: Accept a nested proven lookup `xss[i]![j]!`.
///
/// The outer lookup's answer type is unresolved when the inner lookup is emitted, so the inner
/// one reports that it needs the collection's type.
#[test]
fn a_nested_proven_lookup_is_rejected() {
    check_compile_error(
        indoc! {r#"
            xss = [[1, 2], [3, 4]]
            xss[int_to_uint(1)]![int_to_uint(0)]!
        "#},
        "is not resolved yet",
    )
}

/// TODO: Accept a proven lookup into a mutable list.
///
/// A mutable variable's value type is unresolved when the lookup is emitted.
#[test]
fn a_proven_lookup_into_a_mutable_list_is_rejected() {
    check_compile_error(
        indoc! {r#"
            xs := [1, 2, 3]
            xs[int_to_uint(1)]!
        "#},
        "is not resolved yet",
    )
}

/// TODO: Keep a proven lookup into a transactional array valid through post-transact.
///
/// A proven lookup into a transactional array inside a block type-checks, and the post-transact
/// check rejects the `match` that `!` lowers to, because it no longer proves the answer is not
/// `Option::none`.
#[test]
#[should_panic(
    expected = "post-transact produced an invalid tree: [`match` over `Option` has no \
                           arm for `Option::none`"
)]
fn a_proven_lookup_into_a_transactional_array_fails_post_transact() {
    check_scalar(
        indoc! {r#"
            xs: Mut(Array(3, Int), Txn) := [1, 2, 3]
            n: Mut(Int, Txn) := 0
            for r in [1]:
                with begin():
                    n := xs[int_to_uint(1)]!
            await_final(n)
        "#},
        Value::Int(2),
    )
}

/// TODO: Refine a `UInt` sum, so a proven lookup at one is accepted.
///
/// `int_to_uint(1) + int_to_uint(1)` is typed `UInt`, unrefined, so the key does not lie in
/// `xs`'s domain `0..3`.
#[test]
fn a_proven_lookup_at_a_uint_sum_is_rejected() {
    check_sink_error(
        indoc! {r#"
            xs = [1, 2, 3]
            out = test_sink()
            out << xs[int_to_uint(1) + int_to_uint(1)]!
        "#},
        "expected {UInt where _ < 3}, found UInt",
    )
}
