//! List and generator comprehensions: basic mappings, let capture, tuple
//! bodies, filters, and UDFs used inside / containing comprehension filters.

use std::collections::HashMap;
use std::time::Duration;

use bit_set::BitSet;
use cambra::interpreter::{ColumnValue, Predicate, Tile, Value, tuple_field};
use rstest_log::rstest;

use crate::helpers::*;

// ---------------------------------------------------------------------------
// Basic list comprehensions
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("[x for x in [10, 20]]", make_int_list(&[10, 20]))]
#[case("[42 for x in [10, 20]]", make_int_list(&[42, 42]))]
#[case("[y for y in [x for x in [10, 20]]]", make_int_list(&[10, 20]))]
#[case("[x + 2 for x in [10, 20]]", make_int_list(&[12, 22]))]
// Nested *filtered* comprehensions (filter over a filtered comprehension). At
// depth ≥3 this used to panic in lambda-elim: a refinement predicate carrying a
// nested refinement over `__elem` made `is_free` mis-report the (bound) element
// binder as free, tripping the "value-dependent dependent function" guard.
#[case("[a for a in [b for b in [1, 2, 3, 4] if b < 3] if a < 3]", make_int_list(&[1, 2]))]
#[case(
    "[a for a in [b for b in [c for c in [1, 2, 3, 4] if c < 3] if b < 3] if a < 3]",
    make_int_list(&[1, 2])
)]
fn test_comprehensions(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Comprehensions with let capture
// ---------------------------------------------------------------------------
//
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("y = 5; [x + y for x in [10, 20]]", make_int_list(&[15, 25]))]
#[case("y = 1; z = [1,2,3]; [x + y for x in z]", make_int_list(&[2, 3, 4]))]
#[case("y = 1; z = [(1, 'a'),(2, 'b'),(3, 'c')]; [x.0 + y for x in z]", make_int_list(&[2, 3, 4]))]
fn test_comprehensions_let_capture(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Comprehensions with tuple body
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("[(y, y).1 for y in [10, 20]]", make_int_list(&[10, 20]))]
#[case("[y.0 for y in [(10, 'a'), (20, 'b')]]", make_int_list(&[10, 20]))]
#[case(
    "[(y, 100) for y in [(10, 'a'), (20, 'b')]]",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![0, 1]),
        codomain: Box::new(Tile::Record(HashMap::from([
            (
                tuple_field(0),
                Tile::Scalar(ColumnValue::Records(HashMap::from([
                    (tuple_field(0), ColumnValue::Ints(vec![10, 20])),
                    (
                        tuple_field(1),
                        ColumnValue::Strings(vec![
                            "a".into(),
                            "b".into(),
                        ]),
                    ),
                ]))),
            ),
            (tuple_field(1), Tile::Scalar(ColumnValue::Ints(vec![100, 100]))),
        ]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
fn test_comprehensions_tuple_body(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Filtered comprehensions
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("[x for x in [1, 2, 3] if x < 0]", make_int_list(&[]))]
#[case("[x for x in [1, 2, 3] if x > 0]", make_int_list(&[1, 2, 3]))]
#[case("[x for x in [1, 2, 3] if x > 10]", make_int_list(&[]))]
#[case(
    "[x for x in [1, 2, 3] if x == 2]",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![1]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
#[case(
    "[x for x in [1, 2, 3, 4, 5] if x > 1 if x < 5]",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![1, 2, 3]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3, 4]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
fn test_comprehensions_filtered(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// A *let-bound* (and therefore generalized) UDF referenced from inside a
// filter predicate. The predicate's `f(x)` use lives inside the cast-target
// refinement, not the main expression tree — exercising the coalesce walk's
// specialization of uses reachable only through refinement predicates.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_udf_used_inside_filter_predicate() {
    let code = "f = \\x -> x > 1\n[x for x in [1, 2, 3] if f(x)]";
    check_tile(
        code,
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
    );
}

// The dual of the test above: the generalized definition itself *contains*
// the filter, so the specialization clone carries a cast-target refinement.
// Exercises `freshen_expr_types`' predicate-cell de-aliasing for anchored
// (cast-target) predicates.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_udf_containing_filter() {
    let code = "f = \\xs -> [x for x in xs if x > 1]\nf([1, 2, 3])";
    check_tile(
        code,
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
    );
}

// ---------------------------------------------------------------------------
// Generator expressions — equivalent to list comprehensions
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("(x for x in [10, 20])", make_int_list(&[10, 20]))]
#[case("(x + 2 for x in [10, 20])", make_int_list(&[12, 22]))]
fn test_generator_expressions(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// Filtered generator expression — parity with filtered list comp.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    "(x for x in [1, 2, 3, 4, 5] if x > 2)",
    Tile::SealedFunction {
        domain: ColumnValue::UInts(vec![2, 3, 4]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![3, 4, 5]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
fn test_generator_expression_filtered(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

/// Three filtered-comprehension shapes that do not compile. All three **predate the
/// dependent-sum work** — each reproduces unchanged on `main` — and none involves a `box`,
/// a `Σ`, or a witness. They are recorded here because they are otherwise easy to
/// re-diagnose as sum fallout when they surface beside `sums.rs`'s
/// `a_filter_over_a_boxed_source_is_applied`, which they resemble and are unrelated to.
///
/// Each fails loudly, which is why they are recorded rather than fixed here:
///
/// - a **let-bound filtered comprehension, filtered again** panics with `no entry found for
///   key`. Inlining the inner comprehension into the generator
///   (`test_filtered_comprehension_over_a_filtered_literal` below) works, so the binding is
///   what breaks it;
/// - a **filter over a same-domain conditional** fails the post-planning typecheck: the
///   `cast` above the realized union still says `[0, 1]`, where the union's domain is
///   `{[0, 1] | π̂₀} | {[0, 1] | π̂₁}`. Wrapping the realization in a `Realize` that asserts
///   the pre-realization type gets past that — and then reaches the *second* wall, which is
///   the interesting one: the filter's predicate holds its own copy of the source, so it
///   holds the `Case`, and nothing replaces it. Realization deliberately does not fire
///   inside a predicate, and the per-leg discharge that stands in for it there is keyed on
///   a **witness** — which this conditional, being same-domain and unboxed, does not have.
///   The same rewrite would serve (under leg 𝑖 the conditional *is* `armᵢ`); what is
///   missing is a way to identify the source without a witness to name it. Asserting
///   unconditionally is *not* the fix on its own — it breaks
///   `test_value_case_same_domain_collection_result`, where the realized union is the
///   program's own result and the assertion re-imposes a domain the result no longer has;
/// - a **filtered comprehension as a loop source** fails the post-planning typecheck on the
///   `Transact` it becomes.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    r"
x = [z for z in [1, 2, 3] if z > 1]
sum([y for y in x if y < 3])",
    Value::Int(2)
)]
#[case(
    r"
c: Bool = True
sum([y for y in ([1, 5] if c else [3, 4]) if y > 2])",
    Value::Int(5)
)]
#[case(
    r"
x = [1, 2, 3]
total := 0
for y in [z for z in x if z > 1]:
    total += y
total",
    Value::Int(5)
)]
#[ignore = "pre-existing on main, unrelated to sums: a re-filtered let binding, a filter \
            over a same-domain conditional, and a filtered loop source; measured 2026-08-11"]
fn filtered_comprehension_shapes_that_do_not_compile(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// The inlined counterpart of the let-bound case above — filtering a filtered comprehension
/// works when the inner one sits directly in the generator. Pins that the binding, not the
/// nesting, is what the case above trips over.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_filtered_comprehension_over_a_filtered_literal() {
    check_scalar(
        "sum([y for y in [z for z in [1, 2, 3] if z > 1] if y < 3])",
        Value::Int(2),
    );
}
