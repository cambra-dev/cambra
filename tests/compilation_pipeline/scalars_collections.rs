//! Scalars and basic collections: literals, arithmetic, comparisons, boolean
//! ops, collection union (`++`), let bindings, augmented assignment, and tuples.

use std::time::Duration;

use bit_set::BitSet;
use cambra::interpreter::{ColumnValue, Predicate, Tile, Value};
use rstest_log::rstest;

use cambra::ccl::TagMap;

use crate::helpers::*;

// ---------------------------------------------------------------------------
// Literals
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("2", Value::Int(2))]
#[case(r#""hello""#, Value::String("hello".into()))]
#[case("True", Value::Bool(true))]
fn test_literals(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// Type annotations use the capitalized primitive names and parenthesised type
// application / brace-delimited structural types (see the CHL spec's
// "Direction: term/type syntax split [Decided]").
#[rstest]
#[timeout(Duration::from_secs(10))]
// Capitalized primitive.
#[case("x: Int = 5\nx", Value::Int(5))]
// Record type `(name=T, …)`.
#[case("p: {a: Int, b: Int} = (a=1, b=2)\np.a", Value::Int(1))]
// Tuple type `{T, U}` (colon-free brace group).
#[case("t: {Int, Bool} = (1, True)\nt.0", Value::Int(1))]
fn test_type_annotation_forms(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("[]", Tile::SealedFunction { domain: ColumnValue::UInts(vec![]), codomain: Box::new(Tile::Scalar(ColumnValue::Units(0))), domain_predicate: Predicate::True, deleted: BitSet::new() })]
#[case("[1, 2]", make_int_list(&[1, 2]))]
// A `List(_)` annotation lowers the wildcard to a `Hole` element type
// (inferred), so the annotation is accepted and unifies with the list literal.
#[case("x: List(_) = box([1, 2, 3])\nx", make_int_list(&[1, 2, 3]))]
// The element type can also be spelled concretely: `List(Int)`.
#[case("x: List(Int) = box([1, 2, 3])\nx", make_int_list(&[1, 2, 3]))]
// `Array(n, T)` = `[0, n) ⤇ T`: a static index range, so the length rides the
// domain (`UIntRange(3)`) rather than being inferred.
#[case(r"
x: Array(3, Int) = [1, 2, 3]
x", make_int_list(&[1, 2, 3]))]
// `Collection(T)` = `Σ (D: Any). D ⤇ T`, the whole-domain-witness sum — the ⊤ of the
// kind order. The annotation is only the annotation: the value still runs as the
// concrete list, because the witness is resolved statically before op-conversion.
#[case(r"
x: Collection(Int) = box([1, 2, 3])
x", make_int_list(&[1, 2, 3]))]
#[case(r"
x: Collection(_) = box([1, 2, 3])
x", make_int_list(&[1, 2, 3]))]
fn test_list_literals(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// A UDF parameter annotated as an abstract collection is a *consumer* of a whole
// collection, not a per-element map body. At a concrete call site the UDF inlines and
// beta-reduces, so the abstract witness resolves to the argument's concrete domain and
// the body compiles. Without the `Type::Sigma` arm in `inline::is_iterable_domain` the
// UDF is left un-inlined and the abstract Σ strands at op-conversion.
//
// That inlining is also why a *runtime* witness is not yet reachable from source: it is
// what monomorphizes the parameter back to something op-conversion can iterate
// (`src/ccl/design/collections.md`, "Realizing a conditional collection").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    r"
def f(c: Collection(Int)):
    sum(c)
f(box([1, 2, 3]))",
    Value::Int(6)
)]
#[case(
    r"
def f(c: Collection(Int)):
    sum(c)
f(box([10, 20]))",
    Value::Int(30)
)]
// A `List(Int)` param — the `UIntRanges` kind — resolves the same way.
#[case(
    r"
def f(c: List(Int)):
    sum(c)
f(box([1, 2, 3]))",
    Value::Int(6)
)]
#[case(
    r"
def f(c: List(Int)):
    sum(c)
f(box([10, 20, 30]))",
    Value::Int(60)
)]
fn test_collection_param_consumed(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("2 + 3", Value::Int(5))]
#[case("4 * 5", Value::Int(20))]
#[case("4 - 5", Value::Int(-1))]
#[case("1 + 2 - 3 * 4", Value::Int(-9))]
#[case("1 + 2 * 3 - 4", Value::Int(3))]
#[case("1 + 2 * (3 - 4)", Value::Int(-1))]
#[case("7 // 2", Value::Int(3))]
fn test_arithmetic(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Comparisons
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("1 == 1", Value::Bool(true))]
#[case("'a' == 'b'", Value::Bool(false))]
#[case("1 != 1", Value::Bool(false))]
#[case("'a' != 'b'", Value::Bool(true))]
#[case("2 > 1", Value::Bool(true))]
#[case("'a' < 'b'", Value::Bool(true))]
#[case("True != False", Value::Bool(true))]
#[case("True == True", Value::Bool(true))]
fn test_compare(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Boolean operations
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("True & True", Value::Bool(true))]
#[case("True | False", Value::Bool(true))]
#[case("True ^ True", Value::Bool(false))]
#[case("True and False", Value::Bool(false))]
#[case("True or False", Value::Bool(true))]
fn test_bool_ops(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Collection union (`++`)
// ---------------------------------------------------------------------------

/// `[1, 2, 3] ++ [4, 5]` produces a SealedFunction with a discriminated-union
/// domain and the concatenated integer codomains.
#[rstest]
#[case(
    "[1, 2, 3] ++ [4, 5]",
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 0, 0, 1, 1], vec![
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1]),
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 4, 5]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
#[case(
    "x = [1, 2]; x ++ x ++ x",
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 0, 1, 1, 2, 2], vec![
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),

            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 1, 2, 1, 2]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
#[case(
    "x = [1, 2]; y = x ++ x ++ x; y",
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 0, 1, 1, 2, 2], vec![
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),

            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 1, 2, 1, 2]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
#[case("sum([1] ++ [2])", Tile::Scalar(ColumnValue::Ints(vec![3])))]
#[case("sum([1 for y in [1] ++ [2]])", Tile::Scalar(ColumnValue::Ints(vec![2])))]
#[case("sum([1 for y in [1] ++ [2] ++ [3]])", Tile::Scalar(ColumnValue::Ints(vec![3])))]
#[case("sum([1] ++ [2] ++ [3])", Tile::Scalar(ColumnValue::Ints(vec![6])))]
fn test_unions(#[case] code: &str, #[case] expected: Tile) {
    let result = run_pipeline(code);
    assert_eq!(result, expected);
}

// ---------------------------------------------------------------------------
// Let bindings
// ---------------------------------------------------------------------------
//
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("x = 2; x", Value::Int(2))]
#[case("x = 2; y = x; y", Value::Int(2))]
#[case("x = 2; y = x; y + x + 1", Value::Int(5))]
fn test_let_bindings(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Augmented assignment
// ---------------------------------------------------------------------------
#[rstest]
#[timeout(Duration::from_secs(10))]
// `+=` and friends are mutable writes: the target must be introduced mutable with
// `:=` (a `+=` to a plain `=` binding is a "not a mutable" error, never a shadow).
#[case("x := 0\nx += 1\nx", Value::Int(1))]
#[case("x := 10\nx -= 3\nx", Value::Int(7))]
#[case("x := 2\nx *= 5\nx", Value::Int(10))]
#[case("x := 7\nx //= 2\nx", Value::Int(3))]
// Chained augmented assignments accumulate correctly.
#[case("x := 0\nx += 1\nx += 2\nx", Value::Int(3))]
// Mix of an immutable `=` binding and a mutable `+=`: the plain local `y` is read
// into the mutable-variable update. (A pre-mutation *snapshot* of the mutable variable — `y: Int = x`
// before `x += 4` — is deliberately not tested here: a top-level mutable read
// currently resolves to the mutable variable's final value, so point-in-time snapshots are
// a separate concern from this write-lowering path.)
#[case("x := 0\ny = 10\nx += y\nx", Value::Int(10))]
fn test_augmented_assignment(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// More Let bindings
// ---------------------------------------------------------------------------
#[rstest]
#[timeout(Duration::from_secs(10))]
// A comprehension bound to a name, then iterated by a second comprehension. The binding
// is collection-valued, so what the body reads is a data function rather than a scalar —
// the shape the `let`-in-`lambda` rule and kind inference had to reach before this could
// compile without first-class functions.
#[case("x = [x for x in [1,2,3]]; [y for y in x]", make_int_list(&[1,2,3]))]
fn test_let_nonscalar(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Tuples / record fields
// ---------------------------------------------------------------------------
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    "('a', 1)",
    make_tuple(&[Value::String("a".into()), Value::Int(1)])
)]
#[case("('a', 1).0", Value::String("a".into()))]
#[case("('a', 1).1", Value::Int(1))]
#[case("x = ('a', 1); x.0", Value::String("a".into()))]
// A positional key and a named one are the same operation, so they compose freely.
#[case("r = (p=('a', 1), q=2); r.p.1", Value::Int(1))]
#[case("t = ((1, 2), 3); t.0.1", Value::Int(2))]
fn test_tuples(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// A conditional collection consumed by `sum` (`sum([1,2] if c else [1,2,3])`)
// type-checks as a Σ (via the `Σ <: Fun` subtyping rule) and *compiles* via
// value-`Case` fan-out — see `conditionals.rs` for the end-to-end
// compile-and-run coverage.
