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
    Tile::data_function(ColumnValue::UInts(vec![0, 1]), Box::new(Tile::Record(HashMap::from([
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
        ]))), Predicate::True, BitSet::new())
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
    Tile::data_function(ColumnValue::UInts(vec![1]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![2]))), Predicate::True, BitSet::new())
)]
#[case(
    "[x for x in [1, 2, 3, 4, 5] if x > 1 if x < 5]",
    Tile::data_function(ColumnValue::UInts(vec![1, 2, 3]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3, 4]))), Predicate::True, BitSet::new())
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
        Tile::data_function(
            ColumnValue::UInts(vec![1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3]))),
            Predicate::True,
            BitSet::new(),
        ),
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
        Tile::data_function(
            ColumnValue::UInts(vec![1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3]))),
            Predicate::True,
            BitSet::new(),
        ),
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
    Tile::data_function(ColumnValue::UInts(vec![2, 3, 4]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![3, 4, 5]))), Predicate::True, BitSet::new())
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

/// A **filtered inner comprehension over the outer row**, which the filter narrows.
///
/// The inner source is the outer binder, so the filter's refinement reads it, and
/// `lambda_elim` moves it onto the pair the curried morphism takes. The narrowing then lives
/// only in the curry's type. A bare element (`v for v in r`) reduces that curry to `map(id)`,
/// and an element function (`v * 2`) to `map(𝑔)`, the control that kept its filter all
/// along. Unfiltered, these answer 10, 20 and 10.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::bare_element("sum([sum([v for v in r if v > 1]) for r in [[1, 2], [3, 4]]])", 9)]
#[case::element_function(
    "sum([sum([v * 2 for v in r if v > 1]) for r in [[1, 2], [3, 4]]])",
    18
)]
#[case::over_a_group(
    indoc! {r"
        g = groupby([1, 2, 3, 4], \v -> v // 2)
        sum([sum([x for x in grp if x > 1]) for grp in g])
    "},
    9
)]
fn a_filtered_inner_comprehension_over_the_outer_row_keeps_its_filter(
    #[case] program: &str,
    #[case] total: i64,
) {
    check_scalar(program, Value::Int(total));
}

/// A filtered inner comprehension over a **projection of the outer row** does not compile.
/// The filter reads the row while the collection it narrows is the projection, and no type
/// relates the two, so the post-elimination type check rejects the program. Pinned as it
/// fails; it answers 9.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_filtered_inner_comprehension_over_a_projected_row_does_not_compile() {
    check_compile_error(
        "sum([sum([v for v in r.xs if v > 1]) for r in [(xs=[1, 2]), (xs=[3, 4])]])",
        "post-lambda-elim produced an invalid tree",
    );
}

/// The same with **no outer aggregate**, so the narrowed collection per row is the answer's
/// row: `[1, 2]` keeps `2`, and `[3, 4]` keeps both.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_filtered_inner_comprehension_per_row_without_an_outer_aggregate() {
    check_tile(
        "[sum([v for v in r if v > 1]) for r in [[1, 2], [3, 4]]]",
        make_int_list(&[2, 7]),
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

/// A transactional map read back after a keyed write in the same block: the comprehension's
/// source is the `insert` result rather than a store read (`src/ccl/design/optimization.md`,
/// "A generator over a sum composes with its source"). Each transaction writes `b := 10` and
/// then sums `{a: 1, b: 10}`.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::identity("v", 22)]
#[case::element_function("v * 2", 44)]
fn a_transactional_map_reads_back_after_a_keyed_write(#[case] element: &str, #[case] total: i64) {
    check_scalar(
        &format!(
            indoc! {r#"
                m: Mut(Map(String, Int), Txn) := box(map([("a", 1)]))
                n: Mut(Int, Txn) := 0
                for r in [1, 2]:
                    with begin():
                        m["b"] := 10
                        n := n + sum([{} for v in m])
                await_final(n)
            "#},
            element
        ),
        Value::Int(total),
    );
}

/// A collection-valued field of a transactional record, iterated inside a transaction.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_value_binder_reads_a_collection_field_of_a_transactional_record() {
    check_scalar(
        indoc! {r#"
            s: Mut({a: Int, b: Map(String, Int)}, Txn) := (a=5, b=box(map([("x", 1), ("y", 2)])))
            n: Mut(Int, Txn) := 0
            for r in [1, 2, 3]:
                with begin():
                    n := n + sum([v for v in s.b])
            await_final(n)
        "#},
        Value::Int(9),
    );
}

/// A nested collection literal is a **level per nesting**, so a chain of aggregates collapses
/// one level each to reach the integers.
///
/// The literal builds the table it denotes rather than a column of materialized maps, so
/// nothing opens a level on the way in — the levels are there from the start.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::depth_two("sum([sum([v for v in xs]) for xs in [[1, 2], [3, 4]]])", 10)]
#[case::depth_three(
    "sum([sum([sum([v for v in ys]) for ys in xs]) for xs in [[[1, 2], [3, 4]]]])",
    10
)]
#[case::depth_four(
    "sum([sum([sum([sum([v for v in zs]) for zs in ys]) for ys in xs]) \
     for xs in [[[[1, 2], [3, 4]]]]])",
    10
)]
fn a_nested_collection_literal_is_a_level_per_nesting(#[case] program: &str, #[case] total: i64) {
    check_scalar(program, Value::Int(total));
}

/// `Sole` and `Drain` fold a collection whole, so the adapter leaves one materialized.
///
/// `map()` collapses each key's group with `Sole`, and a value that is itself a collection
/// is the element that fold yields — opening it would hand `Sole` the keys instead.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::map_of_collections(
    indoc! {r#"
        mm = map([("a", [1, 2]), ("b", [3, 4])])
        sum([sum([v for v in vs]) for vs in mm])
    "#},
    10
)]
fn a_whole_collection_fold_keeps_its_element_materialized(
    #[case] program: &str,
    #[case] total: i64,
) {
    check_scalar(program, Value::Int(total));
}

/// A filtered comprehension's source rides the cast-target refinement as well
/// as the term, and the two copies are compared structurally. A `Let` outside
/// the comprehension is read freely by the predicate copy, so `inline`'s
/// list-element move has to reach both: rewriting the term alone leaves
/// `[1, 3, 5]` under a type still describing `[1, a, 5]`, which op-conversion
/// rejects as a non-constant element.
#[test]
fn a_let_outside_a_filtered_comprehension_moves_into_both_copies_of_its_source() {
    check_scalar(
        indoc! {r#"
            a = 3
            sum([x for x in [1, a, 5] if x > 2])
        "#},
        Value::Int(8),
    )
}
/// A **correlated** inner comprehension — its body reads the outer binder, so each outer row
/// gets its own inner pass. `lambda_elim` writes that as `curry(𝑔)` over the outer collection,
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
    indoc! {r#"
        c = map([("a", 1), ("b", 2)])
        sum([sum([v * r for v in c]) for r in [1, 2]])
    "#},
    9
)]
// A correlated **filter** beside a correlated body, the filter riding the pair it filters
// (`src/ccl/planning/correlated.rs`): 1*(2+3) + 2*3.
#[case::correlated_filter("sum([sum([v * r for v in [1, 2, 3] if v > r]) for r in [1, 2]])", 11)]
// A filter reading only the element, beside a body that reads the outer binder. It lifts to
// the pair like a correlated one, because neither inner-source builder narrows the inner
// domain itself — leaving it on the component answers 18 rather than 15. 1*(2+3) + 2*(2+3).
#[case::uncorrelated_filter("sum([sum([v * r for v in [1, 2, 3] if v > 1]) for r in [1, 2]])", 15)]
// Both together. The element-only bound is the one that bites at `r = 1`, so dropping
// either filter changes the answer — unlike `v > 1` beside `v > r`, where `v > r` implies
// it at every `r` and the case would pass with the first filter gone. 1*3 + 2*3.
#[case::both_filters(
    "sum([sum([v * r for v in [1, 2, 3] if v > 2 if v > r]) for r in [1, 2]])",
    9
)]
// (1+2+3) twice, the inner sum shared.
#[case::uncorrelated("sum([sum([v for v in [1, 2, 3]]) for r in [1, 2]])", 12)]
// The outer binder outside the inner comprehension: 1*6 + 2*6, by the same broadcast.
#[case::outer_binder_outside("sum([r * sum([v for v in [1, 2, 3]]) for r in [1, 2]])", 18)]
// A body that reads the outer binder and **never applies the inner source**, so `𝑔` is a
// projection with no source in it for planning to name. It compiles by the second route —
// op-conversion reading the domain off the type — which nothing else here covers: 3*(1+2).
#[case::body_ignores_the_inner_element("sum([sum([r for v in [1, 2, 3]]) for r in [1, 2]])", 9)]
// The same route with a filter, element-only and correlated: the inner domain is read off
// the type and the filter rides the pair. 2 * (1 + 2), then 2 * 1 + 1 * 2.
#[case::body_ignores_the_inner_element_filtered(
    "sum([sum([r for v in [1, 2, 3] if v > 1]) for r in [1, 2]])",
    6
)]
#[case::body_ignores_the_inner_element_correlated_filter(
    "sum([sum([r for v in [1, 2, 3] if v > r]) for r in [1, 2]])",
    4
)]
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
        Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                ColumnValue::UInts(vec![0, 2]),
                ColumnValue::UInts(vec![0, 1, 0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 2, 4]))),
                Predicate::False,
                BitSet::new(),
            )),
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
    let levels = tile.key_levels();
    let [(_, outer), (_, inner)] = levels.as_slice() else {
        panic!("one level per comprehension, so two here; got {levels:?}")
    };
    let Tile::Scalar(values) = tile.deepest_values() else {
        panic!(
            "the values are one per innermost entry, got {:?}",
            tile.deepest_values()
        )
    };
    let Tile::DataFunction {
        codomain: groups, ..
    } = &tile
    else {
        panic!("a comprehension yielding a collection per row tiles as a collection")
    };
    let mut got: Vec<(usize, Value, Value)> = Vec::new();
    for g in 0..outer.len() {
        let (start, end) = groups.row_run(g);
        for j in start..end {
            got.push((g, inner.index_at(j), values.index_at(j)));
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

/// Correlated nesting at **depth three and four**. Each pairing appends one level and each
/// aggregate removes one, so a comprehension nested 𝑛 deep pairs 𝑛−1 times and folds 𝑛 times
/// (`src/interpreter/design-operators.md`, "A correlated inner comprehension").
#[rstest]
#[timeout(Duration::from_secs(10))]
// 1*(1+2+3) + 2*(1+2+3).
#[case::depth_2("sum([sum([v * r for v in [1, 2, 3]]) for r in [1, 2]])", 18)]
// (1+2)³, each level contributing its own factor.
#[case::depth_3(
    "sum([sum([sum([v * r * q for v in [1, 2]]) for r in [1, 2]]) for q in [1, 2]])",
    27
)]
// (1+2)⁴ — the depth is not bounded, so a fourth level needs no further change.
#[case::depth_4(
    "sum([sum([sum([sum([a * b * c * d for a in [1, 2]]) for b in [1, 2]]) for c in [1, 2]]) for d in [1, 2]])",
    81
)]
// A collection as the innermost source, whose domain comes from the data rather than
// from an extent, nests the same way.
#[case::depth_3_collection(
    indoc! {r#"
        m = map([("a", 1), ("b", 2)])
        sum([sum([sum([v * r * q for v in m]) for r in [1, 2]]) for q in [1, 2]])
    "#},
    27
)]
// An inner comprehension that reads nothing outer still broadcasts, one level down.
#[case::depth_3_partial(
    "sum([sum([sum([v for v in [1, 2]]) * r for r in [1, 2]]) for q in [1, 2]])",
    18
)]
// A correlated filter at depth three. The inner sum's domain is filtered per row, and its
// type says so by naming the binder of the pair the outer site merged `q` and `r` into.
// Each filter reads a different level: `q = 1` keeps 2 + 3 and `q = 2` keeps 3, so
// (1·5 + 2·3)·(1 + 2) = 33, and by symmetry the same over `r`.
#[case::depth_3_filter_on_the_outermost(
    "sum([sum([sum([v * r * q for v in [1, 2, 3] if v > q]) for r in [1, 2]]) for q in [1, 2]])",
    33
)]
#[case::depth_3_filter_on_the_middle(
    "sum([sum([sum([v * r * q for v in [1, 2, 3] if v > r]) for r in [1, 2]]) for q in [1, 2]])",
    33
)]
// Both levels at once, which only `q = r = 1` passes at 3.
#[case::depth_3_filter_on_both(
    "sum([sum([sum([v * r * q for v in [1, 2, 3] if v > r + q]) for r in [1, 2]]) for q in [1, 2]])",
    3
)]
// Two pairings above the filtered one: (1·5 + 2·3)·3·3.
#[case::depth_4_filter(
    "sum([sum([sum([sum([v * s * r * q for v in [1, 2, 3] if v > q]) for s in [1, 2]]) \
     for r in [1, 2]]) for q in [1, 2]])",
    99
)]
// A body that never applies the inner source, so the domain is read off the type, and the
// filter on it rides the pair one level down: `r` counts 2 elements at `q = 1` and 1 at
// `q = 2`, so (1 + 2)·3.
#[case::depth_3_filter_body_ignores_the_inner_element(
    "sum([sum([sum([r for v in [1, 2, 3] if v > q]) for q in [1, 2]]) for r in [1, 2]])",
    9
)]
fn a_correlated_comprehension_nests_to_any_depth(#[case] program: &str, #[case] total: i64) {
    check_scalar(program, Value::Int(total));
}

/// A correlated comprehension whose **outer row is itself a collection**, a `groupby` group.
/// `Product` appends its level beneath the innermost level of the tile it is handed, and a
/// group's own elements are such a level, so the pairing lands beneath them and the product
/// reaches `BinOp(*)` one level too deep. Pinned as it fails. The groups are `[1]`, `[2, 3]`
/// and `[4]`, so it answers `3 × (1 + 5 + 4)` = 30.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[should_panic(expected = "a level reaching it is a shape error")]
fn a_correlated_comprehension_over_collection_valued_rows() {
    check_scalar(
        indoc! {r"
            g = groupby([1, 2, 3, 4], \v -> v // 2)
            sum([sum([x * sum(v) for x in [1, 2]]) for v in g])
        "},
        Value::Int(30),
    );
}

/// Nesting **with no aggregate at any level**: three comprehensions leave three domain
/// levels, which is the tile shape rather than a fold of it.
///
/// The depth cases above all sum at every level, so each `Product` is consumed by a
/// `MapAggregate` that collapses the level it just added. Here nothing collapses, and the
/// levels stand.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_correlated_comprehension_nests_without_an_aggregate() {
    // `q`, `r` and `v` each range over [1, 2], and the innermost entry is their product.
    check_tile(
        "[[[v * r * q for v in [1, 2]] for r in [1, 2]] for q in [1, 2]]",
        Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                ColumnValue::UInts(vec![0, 2]),
                ColumnValue::UInts(vec![0, 1, 0, 1]),
                Box::new(Tile::grouped(
                    ColumnValue::UInts(vec![0, 2, 4, 6]),
                    ColumnValue::UInts(vec![0, 1, 0, 1, 0, 1, 0, 1]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![
                        1, 2, 2, 4, 2, 4, 4, 8,
                    ]))),
                    Predicate::False,
                    BitSet::new(),
                )),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        ),
    );
}

/// A correlated filter **inside a transaction**, where the rows arrive one at a time. The
/// predicate and the input are pulled from separate branches of the pairs, so the predicate
/// answers for entries whose rows the input has not delivered yet. `Filter` reads its mask
/// positionally, and an input with nothing in it is already filtered — it hands the rows
/// back and the next pull finds the two in step. A non-empty input at a different count is
/// the misalignment it still refuses, rather than reading the mask across it (which drops
/// the wrong entries silently) or answering empty (which waits for an alignment that is not
/// coming).
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_correlated_filter_inside_a_transaction() {
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

/// A correlated inner comprehension over a **map** whose body never reads the element is
/// refused by name. Its body never applies the source, so planning has none to name, and
/// the inner domain is read off the type, where a map's keys are a present-key proof over
/// the whole key type rather than anything enumerable.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_correlated_comprehension_over_an_unnamed_map_source_is_unsupported() {
    check_compile_error(
        indoc! {r#"
            c = map([("a", 1), ("b", 2)])
            sum([sum([r for v in c]) for r in [1, 2]])
        "#},
        "source is a collection planning did not name",
    );
}

/// A correlated filter with **no aggregate over it** does not compile, where the same filter
/// under a `sum` does (`a_correlated_inner_comprehension_runs_per_outer_row`,
/// `correlated_filter`). The one predicate ends up spelled two ways — the term reads the outer
/// list through the iteration record, while the copy in the type reads it through a `let` —
/// and lambda elimination's check that a node keeps its type rejects the pair:
///
/// ```text
/// (__iter_record: [0, 1]) ⤇ ({[0, 2] | … v > (let __anf = [1, 2] in __iter_record ▷ __anf)} ⤇ Int)
/// (__iter_record: [0, 1]) ⤇ ({[0, 2] | … v > __iter_record ▷ ((id, [1, 2] ▷ const) ▷ zip ≫ apply)} ⤇ Int)
/// ```
///
/// That check is `debug_assertions`-gated. Without it the tree reaches the post-lambda-elim
/// wall, which reports the same disagreement as a collection-domain mismatch.
///
/// The fault is below the re-basing rewrite rather than in it: the rewrite that reaches one
/// occurrence does not reach the other (`refinements-dependent-projection-of-a-refined-pair`
/// in the issue tracker).
#[rstest]
#[timeout(Duration::from_secs(10))]
#[cfg_attr(
    debug_assertions,
    should_panic(expected = "lambda elimination changed a node's type")
)]
#[cfg_attr(
    not(debug_assertions),
    should_panic(expected = "Type mismatch for collection domain")
)]
fn a_correlated_filter_without_an_aggregate_does_not_compile() {
    check_tile(
        "[[v * r for v in [1, 2, 3] if v > r] for r in [1, 2]]",
        // `[[2, 3], [6]]` if it compiled.
        make_int_list(&[]),
    );
}

/// A correlated filter whose **body** reads nothing outer. The outer binder appears in the
/// filter alone, so it is free only in the type: lambda elimination takes the Pi-const arm
/// and the site never becomes the pair the re-basing rewrite reads. The rewrite for this is
/// a sibling of that one rather than an extension of it.
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

/// A correlated filter over a **collection** source, where the domain carries a present-key
/// `collection_contains` beside the program's own filter.
///
/// The two are different kinds of refinement and `lambda_elim` separates them: the carried
/// proof stays on the inner binder, where the lookup in the body reads it, and the filter
/// lifts onto the pair to be applied. Compiling both as terms instead fails to compile.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_correlated_filter_over_a_collection() {
    check_scalar(
        indoc! {r"
            c = map([(1, 10), (2, 20)])
            sum([sum([v * r for v in c if v > r]) for r in [1, 2]])
        "},
        // 1*(10+20) + 2*(10+20).
        Value::Int(90),
    );
}

/// A collection that is **empty** folds to the aggregate's identity, and the row it belongs
/// to keeps its place.
///
/// Read as a collection, because a scalar sum cannot tell an absent row from a row that folds
/// to `0`. A curried tile's offsets are
/// non-decreasing, so a row whose collection holds nothing keeps its group and holds nothing
/// ([design-operators.md, "A correlated inner comprehension"](src/interpreter/design-operators.md#a-correlated-inner-comprehension)).
#[rstest]
#[timeout(Duration::from_secs(10))]
// `r = 1` keeps `v = 2`; `r = 2` keeps nothing, and its row stays, holding the identity.
#[case::one_row_emptied("[sum([v * r for v in [1, 2] if v > r]) for r in [1, 2]]", &[2, 0])]
// Neither row keeps anything, so both fold to the identity rather than leaving no rows.
#[case::every_row_emptied("[sum([v * r for v in [1, 2] if v > r * 10]) for r in [1, 2]]", &[0, 0])]
fn an_emptied_row_keeps_its_place(#[case] program: &str, #[case] expected: &[i64]) {
    check_tile(program, make_int_list(expected));
}
