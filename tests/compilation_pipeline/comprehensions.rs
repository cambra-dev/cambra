//! List and generator comprehensions: basic mappings, let capture, tuple
//! bodies, filters, and UDFs used inside / containing comprehension filters.

use std::collections::HashMap;
use std::time::Duration;

use bit_set::BitSet;
use cambra::interpreter::{ColumnValue, Predicate, Tile, Value, tuple_field};
use indoc::indoc;
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

/// A **filtered comprehension as a loop source**. Recorded here as a shape that failed the
/// post-planning typecheck on the `Transact` it becomes; it compiles now that a compiled
/// refinement predicate is declared the column it is, the `Transact`'s own filter having
/// been the predicate that met its source at the incomparable kind.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_filtered_comprehension_drives_a_mutation_loop() {
    check_scalar(
        indoc! {r"
            x = [1, 2, 3]
            total := 0
            for y in [z for z in x if z > 1]:
                total += y
            total"},
        Value::Int(5),
    );
}

/// A filtered-comprehension shape that does not compile. It **predates the dependent-sum
/// work** — it reproduces unchanged on `main` — and involves no `box`, `Σ`, or witness. It
/// is recorded here because it is otherwise easy to re-diagnose as sum fallout when it
/// surfaces beside `sums.rs`'s `a_filter_over_a_boxed_source_is_applied`, which it resembles
/// and is unrelated to.
///
/// It fails loudly, which is why it is recorded rather than fixed here: a **filter over a
/// same-domain conditional** fails the post-planning typecheck: the
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
///   program's own result and the assertion re-imposes a domain the result no longer has.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Pinned on the failure rather than deferred: an `#[ignore]` reports the same green whether
// the gap closed, regressed, or went away, and nothing runs ignored tests here.
#[should_panic(expected = "CCL node Case")]
fn a_filter_over_a_same_domain_conditional_does_not_compile() {
    check_scalar(
        indoc! {r"
            c: Bool = True
            sum([y for y in ([1, 5] if c else [3, 4]) if y > 2])"},
        Value::Int(5),
    );
}

/// A **let-bound filtered comprehension, filtered again.** Recorded above as a shape that
/// panicked with `no entry found for key`; it compiles now, and the pair with
/// `test_filtered_comprehension_over_a_filtered_literal` below keeps both placements of the
/// inner comprehension covered.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn test_refiltered_let_bound_comprehension() {
    check_scalar(
        indoc! {r"
            x = [z for z in [1, 2, 3] if z > 1]
            sum([y for y in x if y < 3])"},
        Value::Int(2),
    );
}

/// A **correlated** inner comprehension — its body reads the outer binder, so each outer row
/// gets its own inner pass. `lambda_elim` writes that as `curry(𝑔)` over the outer stream,
/// where `𝑔` takes the pair of the outer value and the inner element, and op-conversion pairs
/// them (`src/interpreter/design-operators.md`, "A correlated inner comprehension").
///
/// The **uncorrelated** case is beside it because it compiles by a different route and always
/// did: a body closing over nothing outer leaves a `const`, computed once and broadcast.
///
/// One case reaches op-conversion with its `curry` intact, which is the second of the two
/// routes a correlated site has and the only coverage of it:
/// `body_ignores_the_inner_element`. Deleting either route drops a program the other does
/// not serve.
#[rstest]
#[timeout(Duration::from_secs(10))]
// 1*(1+2+3) + 2*(1+2+3).
#[case::correlated("sum([sum([v * r for v in [1, 2, 3]]) for r in [1, 2]])", 18)]
// A **collection** source, whose domain no extent describes: 1*(1+2) + 2*(1+2).
#[case::collection_source(
    "c = map([(\"a\", 1), (\"b\", 2)])\nsum([sum([v * r for v in c]) for r in [1, 2]])",
    9
)]
// A correlated **filter** beside a correlated body, the filter riding the pair it filters
// (`src/ccl/planning/correlated.rs`): 1*(2+3) + 2*3.
#[case::correlated_filter("sum([sum([v * r for v in [1, 2, 3] if v > r]) for r in [1, 2]])", 11)]
// A filter reading only the element, beside a body that reads the outer binder. It rides
// the same pair: the refinement is on the pair domain either way, so leaving it there
// applies it nowhere — which answered 18 rather than 15. 1*(2+3) + 2*(2+3).
#[case::uncorrelated_filter("sum([sum([v * r for v in [1, 2, 3] if v > 1]) for r in [1, 2]])", 15)]
// Both together, the correlated one narrowing further: 1*(2+3) + 2*3.
#[case::both_filters(
    "sum([sum([v * r for v in [1, 2, 3] if v > 1 if v > r]) for r in [1, 2]])",
    11
)]
// (1+2+3) twice, the inner sum shared.
#[case::uncorrelated("sum([sum([v for v in [1, 2, 3]]) for r in [1, 2]])", 12)]
// The outer binder outside the inner comprehension: 1*6 + 2*6, by the same broadcast.
#[case::outer_binder_outside("sum([r * sum([v for v in [1, 2, 3]]) for r in [1, 2]])", 18)]
// A body that reads the outer binder and **never applies the inner source**, so `𝑔` is a
// projection with no source in it for planning to name. It compiles by the second route —
// op-conversion reading the domain off the type — which nothing else here covers: 3*(1+2).
#[case::body_ignores_the_inner_element("sum([sum([r for v in [1, 2, 3]]) for r in [1, 2]])", 9)]
fn a_correlated_inner_comprehension_runs_per_outer_row(#[case] program: &str, #[case] total: i64) {
    check_scalar(program, Value::Int(total));
}

/// A correlated inner comprehension with **no aggregate over it**: the pairing is the whole
/// compilation, and the curried tile is the answer.
///
/// Every other case here sums, which hides that `MapAggregate` is a consumer rather than a
/// requirement — `Product` emits a collection per row, and a comprehension that yields one
/// keeps it.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_correlated_inner_comprehension_without_an_aggregate() {
    // `r` ranges over [1, 2] and `v` over [1, 2], so row `r` holds [r, 2r].
    check_tile(
        "[[v * r for v in [1, 2]] for r in [1, 2]]",
        Tile::curried_function(
            ColumnValue::UInts(vec![0, 1]),
            ColumnValue::UInts(vec![0, 2]),
            ColumnValue::UInts(vec![0, 1, 0, 1]),
            ColumnValue::Ints(vec![1, 2, 2, 4]),
            Predicate::True,
            BitSet::new(),
        ),
    );
}

/// The same over a **collection** source, whose keys are the inner domain.
///
/// Read as a set of `(row, key, value)` triples: a map carries its entries in its own order,
/// and what the pairing decides is the grouping rather than the order within a group.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_correlated_comprehension_without_an_aggregate_over_a_collection() {
    let tile = run_pipeline(indoc! {r#"
        c = map([("a", 1), ("b", 2)])
        [[v * r for v in c] for r in [1, 2]]
    "#});
    let Tile::CurriedFunction {
        domain1,
        offsets,
        domain2,
        codomain,
        ..
    } = tile
    else {
        panic!("a comprehension yielding a collection per row tiles as a curried function")
    };
    let groups = domain1.len();
    let mut got: Vec<(usize, Value, Value)> = Vec::new();
    for g in 0..groups {
        let start = offsets.index_at(g).as_uint();
        let end = if g + 1 < groups {
            offsets.index_at(g + 1).as_uint()
        } else {
            domain2.len()
        };
        for j in start..end {
            got.push((g, domain2.index_at(j), codomain.index_at(j)));
        }
    }
    got.sort_by_key(|(g, k, _)| (*g, format!("{k:?}")));
    assert_eq!(
        got,
        vec![
            (0, Value::String("a".into()), Value::Int(1)),
            (0, Value::String("b".into()), Value::Int(2)),
            (1, Value::String("a".into()), Value::Int(2)),
            (1, Value::String("b".into()), Value::Int(4)),
        ]
    );
}

/// An outer comprehension that yields a collection while its inner one aggregates — the
/// aggregate is inside, so the answer is a stream rather than a scalar.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_correlated_inner_aggregate_under_a_collection_result() {
    // 1*(1+2) and 2*(1+2).
    check_tile(
        "[sum([v * r for v in [1, 2]]) for r in [1, 2]]",
        make_int_list(&[3, 6]),
    );
}

/// A **map comprehension whose body never reads the element** does not compile, with or
/// without an enclosing comprehension.
///
/// Nothing here is about correlation or nesting: this one-line program fails, and so does
/// the base branch's, which has none of the correlated work. A body that reads the element
/// applies the collection, which is what puts it in the term
/// (`sum([v for v in c])` answers 3). A body that does not leaves the collection reachable
/// only through its domain's carried `collection_contains`, which op-conversion meets as a
/// non-combinator handed an input.
///
/// The correlated form fails too and reports differently — reading the domain off the type
/// answers the unbounded key type — which is why the message, not just the failure, is
/// pinned here.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[should_panic(expected = "non-combinator collection_contains")]
fn a_map_comprehension_that_ignores_the_element_does_not_compile() {
    check_scalar(
        indoc! {r#"
            c = map([("a", 1), ("b", 2)])
            sum([1 for v in c])
        "#},
        // One per entry.
        Value::Int(2),
    );
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

/// A **correlated filter beside a correlated body** — the inner comprehension's filter and
/// its body both read the outer binder.
///
/// Eliminating the lambda zips two morphisms of which the second is the dependent one, so
/// the pair binds what that one names. The filter reaches that binder because its predicate
/// is re-based onto the pair; without that, planning refuses the `__pair` uid the predicate
/// names, a uid minted fresh per elimination being no value function.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_correlated_filter_beside_a_correlated_body() {
    check_scalar(
        "sum([sum([v * r for v in [1, 2, 3] if v > r]) for r in [1, 2]])",
        Value::Int(11),
    );
}

/// A correlated inner comprehension **inside a transaction**, where the outer binder is the
/// transaction's own row. Nothing about it is transactional: the same pairing serves it as
/// serves a bare nested comprehension, which is why a list source works here before a
/// collection source does anywhere.
#[rstest]
#[timeout(Duration::from_secs(10))]
// 1*(1+2+3) + 2*(1+2+3).
#[case::list_source("sum([v * r for v in [1, 2, 3]])", 18)]
// Over a collection, whose domain comes from the data: 1*(1+2) + 2*(1+2).
#[case::collection_source("sum([v * r for v in c])", 9)]
fn a_correlated_comprehension_runs_inside_a_transaction(
    #[case] comprehension: &str,
    #[case] total: i64,
) {
    check_scalar(
        &format!(
            indoc! {r#"
                c = map([("a", 1), ("b", 2)])
                n: Mut(Int, Txn) := 0
                for r in [1, 2]:
                    with begin():
                        n := n + {}
                await_final(n)
            "#},
            comprehension
        ),
        Value::Int(total),
    );
}

/// A transactional collection read **as a collection**, once per transaction.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::one_transaction("[1]", 3)]
#[case::three_transactions("[1, 2, 3]", 9)]
fn a_value_binder_reads_a_transactional_map(#[case] rows: &str, #[case] total: i64) {
    check_scalar(
        &format!(
            indoc! {r#"
                m: Mut(Map(String, Int), Txn) := box(map([("a", 1), ("b", 2)]))
                n: Mut(Int, Txn) := 0
                for r in {}:
                    with begin():
                        n := n + sum([v for v in m])
                await_final(n)
            "#},
            rows
        ),
        Value::Int(total),
    );
}

/// A correlated filter **inside a transaction**, where the rows arrive one at a time. The
/// predicate and the input are pulled from separate branches of the pairs, so the predicate
/// answers for entries whose rows the input has not delivered, and `Filter` reads its mask
/// positionally. It refuses rather than reading the mask across the misalignment, which
/// drops the wrong entries silently, or answering empty, which waits for an alignment that
/// is not coming.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[should_panic(expected = "needs its predicate and its rows in step")]
fn a_correlated_filter_inside_a_transaction_does_not_compile() {
    check_scalar(
        indoc! {r"
            n: Mut(Int, Txn) := 0
            for r in [1, 2]:
                with begin():
                    n := n + sum([v * r for v in [1, 2, 3] if v > r])
            await_final(n)
        "},
        // 1*(2+3) + 2*3.
        Value::Int(11),
    );
}

/// A correlated filter whose **body reads nothing outer**. The outer binder appears in the
/// filter alone, so it is free only in the type: lambda elimination takes the Pi-const arm
/// and the site never becomes the pair the re-basing rewrite reads. The rewrite for this is
/// a sibling of that one rather than an extension of it.
/// A correlated filter with **no aggregate over it** does not compile, where the same filter
/// under a `sum` does (`a_correlated_inner_comprehension_runs_per_outer_row`,
/// `correlated_filter`). Lambda elimination leaves two spellings of the one predicate — one
/// naming `r`, one the iteration record it was closed over — and the post-pass tree check
/// rejects the pair before planning re-bases either.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[should_panic(expected = "post-lambda-elim produced an invalid tree")]
fn a_correlated_filter_without_an_aggregate_does_not_compile() {
    check_tile(
        "[[v * r for v in [1, 2, 3] if v > r] for r in [1, 2]]",
        // `[[1, 2], [2, 4, 6]]` if it compiled.
        make_int_list(&[]),
    );
}

/// A correlated filter whose **body** reads nothing outer never forms a pair, so the
/// re-basing above has nothing to re-base.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[should_panic(expected = "unrecognised Var")]
fn a_correlated_filter_over_an_uncorrelated_body_does_not_compile() {
    check_scalar(
        "sum([sum([v for v in [1, 2, 3] if v > r]) for r in [1, 2]])",
        // (2+3) + 3.
        Value::Int(8),
    );
}

/// A correlated filter over a **collection** source. This one is not about correlation: a
/// filtered comprehension over a collection does not compile with a name binder and no
/// outer row either, because the restrict chain planning builds for the filter also tries
/// to compile the domain's carried `collection_contains`.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[should_panic(expected = "an iteration site is a collection")]
fn a_correlated_filter_over_a_collection_does_not_compile() {
    check_scalar(
        indoc! {r"
            c = map([(1, 10), (2, 20)])
            sum([sum([v * r for v in c if v > r]) for r in [1, 2]])
        "},
        // 1*(10+20) + 2*(10+20).
        Value::Int(90),
    );
}
