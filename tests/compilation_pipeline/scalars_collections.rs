//! Scalars and basic collections: literals, arithmetic, comparisons, boolean
//! ops, collection union (`++`), let bindings, augmented assignment, and tuples.

use std::time::Duration;

use bit_set::BitSet;
use cambra::interpreter::{ColumnValue, Predicate, Tile, Value};
use rstest_log::rstest;

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

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("[]", Tile::SealedFunction { domain: ColumnValue::UInts(vec![]), codomain: Box::new(Tile::Scalar(ColumnValue::Units(0))), domain_predicate: Predicate::True, deleted: BitSet::new() })]
#[case("[1, 2]", make_int_list(&[1, 2]))]
// A `List[_]` annotation lowers the wildcard to a `Hole` element type
// (inferred), so the annotation is accepted and unifies with the list literal.
#[case("x: List[_] = [1, 2, 3]\nx", make_int_list(&[1, 2, 3]))]
// The element type can also be spelled concretely: `List[int]`.
#[case("x: List[int] = [1, 2, 3]\nx", make_int_list(&[1, 2, 3]))]
fn test_list_literals(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
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
        domain: ColumnValue::Union {
            tags: vec![0, 0, 0, 1, 1],
            variants: vec![
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1]),
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 4, 5]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
#[case(
    "x = [1, 2]; x ++ x ++ x",
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 0, 1, 1, 2, 2],
            variants: vec![
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),

            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 1, 2, 1, 2]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
#[case(
    "x = [1, 2]; y = x ++ x ++ x; y",
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 0, 1, 1, 2, 2],
            variants: vec![
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),
                ColumnValue::UInts(vec![0, 1]),

            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 1, 2, 1, 2]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
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
// into the mutable-variable update. (A pre-mutation *snapshot* of the mutable variable — `y: int = x`
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
#[case("x = [x for x in [1,2,3]]; [y for y in x]", make_int_list(&[1,2,3]))]
#[ignore = "need first class functions for this let"]
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
#[case("('a', 1)[0]", Value::String("a".into()))]
#[case("('a', 1)[1]", Value::Int(1))]
#[case("x = ('a', 1); x[0]", Value::String("a".into()))]
fn test_tuples(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

// ---------------------------------------------------------------------------
// Conditional-collection coproduct: the safety chokepoint
// ---------------------------------------------------------------------------

/// A control-flow join of two differently-sized collections types as a
/// **coproduct** over both extents (an `Index`-tagged `Variant` of data
/// functions — `Type::extent_coproduct`; see collections.md). This lays only
/// the *type-level* coproduct (formation + the `Variant <: Fun` consume rule,
/// so it can be consumed at the type level); *compiling* it — the value-`Case`
/// fan-out that eliminates it into a union of restricts — lands with
/// value-`Case` compilation. Until then a coproduct-consuming program must be
/// rejected **cleanly** (a returned compile error, never a panic and never a
/// silent miscompile). The value-`Case` is caught at lambda elimination — the
/// natural not-yet-implemented boundary value-`Case` compilation graduates.
/// This pins the contract end-to-end: it type-checks, then fails to compile
/// without crashing.
#[test]
fn conditional_collection_rejected_cleanly() {
    use cambra::ccl::context::{GlobalContext, compile_program};
    use cambra::interpreter::Consumer;
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let errs = compile_program(&mut ctx, "sum([1, 2] if True else [1, 2, 3])", consumer)
        .err()
        .expect("a coproduct-consuming program must fail to compile, not miscompile or panic");
    let rendered = format!("{errs:?}");
    assert!(
        rendered.contains("lambda elimination") && rendered.contains("Case"),
        "expected a clean value-Case not-yet-compilable rejection, got:\n{rendered}"
    );
}
