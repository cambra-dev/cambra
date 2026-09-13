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
/// where `𝑔` takes the pair of the outer value and the inner position, and op-conversion pairs
/// them (`src/interpreter/design-operators.md`, "A correlated inner comprehension").
///
/// The **uncorrelated** case is beside it because it compiles by a different route and always
/// did: a body closing over nothing outer leaves a `const`, computed once and broadcast.
#[rstest]
#[timeout(Duration::from_secs(10))]
// 1*(1+2+3) + 2*(1+2+3).
#[case::correlated("sum([sum([v * r for v in [1, 2, 3]]) for r in [1, 2]])", 18)]
// A **collection** source, whose positions no extent describes: 1*(1+2) + 2*(1+2).
#[case::collection_source(
    "c = map([(\"a\", 1), (\"b\", 2)])\nsum([sum([v * r for v in c]) for r in [1, 2]])",
    9
)]
// The same, binding the entry: the value comes back through the proven lookup, per row.
#[case::collection_entry_value(
    "c = map([(\"a\", 1), (\"b\", 2)])\nsum([sum([v * r for k -> v in c]) for r in [1, 2]])",
    9
)]
// And reading the key: 1*(1+2) + 2*(1+2) over the keys 1 and 2.
#[case::collection_entry_key(
    "c = map([(1, 10), (2, 20)])\nsum([sum([k * r for k -> v in c]) for r in [1, 2]])",
    9
)]
// A correlated **filter** beside a correlated body, the filter riding the pair it filters
// (`src/ccl/planning/correlated.rs`): 1*(2+3) + 2*3.
#[case::correlated_filter("sum([sum([v * r for v in [1, 2, 3] if v > r]) for r in [1, 2]])", 11)]
// (1+2+3) twice, the inner sum shared.
#[case::uncorrelated("sum([sum([v for v in [1, 2, 3]]) for r in [1, 2]])", 12)]
// The outer binder outside the inner comprehension: 1*6 + 2*6, by the same broadcast.
#[case::outer_binder_outside("sum([r * sum([v for v in [1, 2, 3]]) for r in [1, 2]])", 18)]
fn a_correlated_inner_comprehension_runs_per_outer_row(#[case] program: &str, #[case] total: i64) {
    check_scalar(program, Value::Int(total));
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

// ---------------------------------------------------------------------------
// Entry iteration — `for k -> v in m`
// ---------------------------------------------------------------------------

// A two-tuple binder iterates a collection's **entries**: the key and the value it
// stores, rather than the value alone (`docs/chl-spec.md`, "4.6 `for` — iteration").
// The generator's source becomes the collection's keys and the value comes back
// through the proven lookup the key's own domain discharges
// (`src/ccl/lower/entries.rs`).
//
// Both spellings are one target — `k -> v` *is* `(k, v)` (`docs/chl-spec.md`,
// "2.4 Atoms") — so the arrow buys readability at the iteration site and nothing
// below the parser distinguishes them. Pinned as one case each so a divergence
// would fail rather than go unnoticed.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::arrow("sum([k * v for k -> v in m])")]
#[case::parenthesised("sum([k * v for (k, v) in m])")]
fn an_entry_binder_reads_the_key_and_the_value(#[case] comprehension: &str) {
    check_scalar(
        &format!("m = map([(1, 10), (2, 20)])\n{comprehension}"),
        // 1*10 + 2*20.
        Value::Int(50),
    );
}

/// A key the body never reads is still bound. Nothing downstream has to know
/// whether it was used — the source is the collection's keys either way, and the
/// value is looked up at each of them — so the iteration is the same one the
/// reading case gets.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_entry_binders_key_may_go_unread() {
    check_scalar(
        r#"m = map([("a", 1), ("b", 2)])
sum([v for k -> v in m])"#,
        Value::Int(3),
    );
}

/// A **compound key**, taken apart — which the storefront's cart
/// (`Map({AccountId, Ticker}, Int)`) and every other product-keyed collection
/// need. The key a generator binds is the collection's own present-key domain, a
/// refined product whose component types the constraint graph learns only once the
/// collection resolves, so each projection's codomain is monomorphized from the key
/// flowing in (`src/ccl/design/type-inference.md`, "Apply is one-way"). Both
/// spellings are one program below the binder — lowering writes `k.0` for the
/// pattern — and both are pinned so a divergence fails rather than going unnoticed.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::pattern("sum([a + b + v for (a, b) -> v in m])")]
#[case::written_out("sum([k.0 + k.1 + v for k -> v in m])")]
fn an_entry_binder_takes_a_compound_key_apart(#[case] comprehension: &str) {
    check_scalar(
        &format!("m = map([((1, 2), 5), ((3, 4), 7)])\n{comprehension}"),
        // (1+2+5) + (3+4+7).
        Value::Int(22),
    );
}

/// An **annotated `Map(𝐾, 𝑉)`** as the source — a sum over its key domain
/// (`src/ccl/design/collections.md`, "The six collection types"), which is the
/// collection type every declared map has. The key binder lands on the witness,
/// because that is what the keys of a sum are: the keys of whichever candidate it
/// took. Using one as a `𝐾` is what its kind says it is
/// (`src/ccl/design/type-inference.md`, "Type kind containment"), so the key reads
/// and multiplies here exactly as a plain map's does.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_entry_binder_reads_an_annotated_maps_entries() {
    check_scalar(
        "m: Map(Int, Int) = box(map([(1, 10), (2, 20)]))\nsum([k * v for k -> v in m])",
        // 1*10 + 2*20.
        Value::Int(50),
    );
}

/// A `Set(𝐾)` is `Map(𝐾, unit)`, so its entry is `(𝐾, unit)` and the projection
/// to the key is lossless — which is the whole reason entry iteration can be
/// uniform across collection types while `Set` and `Map` remain the one pair the
/// kind does not separate (`src/ccl/design/collections.md`, "Telling `Set` and
/// `Map` apart [Open]"). Iterating a set's entries is how a program reaches its
/// keys today.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn a_sets_entry_is_its_key_and_unit() {
    check_scalar(
        "s = set([1, 2, 3])\nsum([k for k -> u in s])",
        Value::Int(6),
    );
}

/// Entry iteration inside a `with begin():` block, over a collection the block
/// does **not** own. The block contributes nothing to the iteration — the
/// comprehension is an ordinary value computed per transaction — which is what
/// makes this the boundary case worth pinning beside
/// `an_entry_binder_over_a_transactional_map_is_not_reachable` below: the
/// block is not what blocks that one, the transactional *source* is.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn an_entry_binder_reads_a_plain_map_inside_a_block() {
    check_scalar(
        indoc! {r"
            m = map([(1, 10), (2, 20)])
            n: Mut(Int, Txn) := 0
            for r in [1]:
                with begin():
                    n := n + sum([k * v for k -> v in m])
            await_final(n)
        "},
        Value::Int(50),
    );
}

/// An entry is a key and a value and nothing else, so a binder with any other
/// arity names a component the collection does not have. Refused at lowering,
/// where the message can say what the binder is *for*, rather than left to fail
/// as an unresolvable projection in inference.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::three("m = map([(1, 10)])\nsum([a for (a, b, c) in m])")]
#[case::one("m = map([(1, 10)])\nsum([a for (a,) in m])")]
fn an_entry_binder_takes_exactly_two_components(#[case] code: &str) {
    check_compile_error(code, "exactly two components");
}

// --- What entry iteration does not reach yet -------------------------------
//
// Each case below is a *source* or *key shape* entry iteration cannot serve, and
// each fails for a reason upstream of the binder — the binder lowers identically
// in all of them. Pinned on the failure rather than deferred: an `#[ignore]`
// reports the same green whether the gap closed, regressed, or went away, which
// is the convention the conditional-source case above already follows.
//
// The common cause of the first four is that an entry-iterating site is sourced
// from the collection's keys (`m ▷ map_domain`), which puts the collection in a
// **combinator argument** position it is not reached in anywhere else. Each one
// names a capability that position needs and the compiler does not have.

/// A **list literal** as the source. `map_domain` compiles its argument with no
/// upstream input, and a bare list literal is an iteration site that planning
/// only ever gives a source to when something downstream asks for one — so the
/// literal arrives at op-conversion unsourced. Entry iteration over a list is the
/// index/value pair, which is well-defined and worth having; what is missing is
/// planning seeding a combinator's collection argument.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[should_panic(expected = "list literal reached op-conversion without an input")]
fn an_entry_binder_over_a_list_literal_is_not_reachable() {
    check_scalar("sum([v for i -> v in [10, 20, 30]])", Value::Int(60));
}

/// A **`groupby` result** as the source, which is what the storefront rollup
/// `[k -> agg(g) for k -> g in groupby(c, key)]` needs. A group-by's codomain
/// *depends* on its key (`src/ccl/design/collections.md`, "`groupby`'s exact
/// type"), and re-viewing it at its keys carries that dependency through a
/// position whose binder is not in scope — the escape the telescope invariant
/// rejects.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[should_panic(expected = "open bound recorded on")]
fn an_entry_binder_over_a_groupby_is_not_reachable() {
    check_scalar(
        r"g = groupby([1, 2, 3, 4], \x -> x // 2)
sum([k for k -> grp in g])",
        Value::Int(3),
    );
}

/// A **second generator** beside an entry-iterating one. The entry generator's
/// source and its lookup read the same collection at two positions, and the
/// filtered reading one of them acquires does not equate with the unfiltered
/// reading the other keeps — a data domain being invariant, that is a mismatch
/// rather than a widening.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[should_panic(expected = "post-inference produced an invalid tree")]
fn an_entry_binder_beside_a_second_generator_is_not_reachable() {
    check_scalar(
        "m = map([(1, 10)])\nsum([k * v * x for k -> v in m for x in [1, 2]])",
        Value::Int(30),
    );
}

/// A **filtered** entry comprehension. The filter refines the site's domain, and
/// a map's domain already carries the present-key membership predicate — a term
/// that is carried and never executed (`src/ccl/ops.rs`,
/// `Builtin::CollectionContains`) — so the restrict chain planning builds for the
/// filter tries to compile it too. This one is not about entry iteration at all:
/// the same comprehension with a plain value binder fails identically, which is
/// what the second case pins.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::entry_binder("sum([v for k -> v in m if v > 10])")]
#[case::value_binder("sum([v for v in m if v > 10])")]
#[should_panic(expected = "non-combinator collection_contains")]
fn a_filtered_comprehension_over_a_map_is_not_reachable(#[case] comprehension: &str) {
    check_scalar(
        &format!("m = map([(1, 10), (2, 20)])\n{comprehension}"),
        Value::Int(20),
    );
}

/// A correlated inner comprehension **inside a transaction**, where the outer binder is the
/// transaction's own row. Nothing about it is transactional: the same pairing serves it as
/// serves a bare nested comprehension, which is why a list source works here before a
/// collection source does anywhere.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[rstest]
#[timeout(Duration::from_secs(10))]
// 1*(1+2+3) + 2*(1+2+3).
#[case::list_source("sum([v * r for v in [1, 2, 3]])", 18)]
// Over a collection, whose positions come from the data: 1*(1+2) + 2*(1+2).
#[case::collection_source("sum([v * r for k -> v in c])", 9)]
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
///
/// Two things meet here. The source is a mutable variable at a function position, which is
/// a value position, so the mention reads through to the map inside the handle. And the
/// store holds that map *materialized* — one map value per commit, which is the shape a
/// keyed read already uses — while an aggregate iterates, so op-conversion opens it into a
/// collection per row (`src/interpreter/design-operators.md`, "Reading a collection held
/// per row").
///
/// One transaction and several are both pinned: a per-row collection is complete as soon
/// as its row arrives, and it is that per-row finality — not the domain closing — that
/// lets each transaction's aggregate settle while the store stays live.
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

/// A transactional map read through an **entry** binder — the shape all four of the
/// storefront/demo entry-iteration sites take. It types: `map_domain` takes a
/// *consumer's* collection, which a `Mut` wrapping one satisfies, so the source is the
/// map's key domain and the value comes back through the proven lookup, exactly as over
/// a plain map.
///
/// What it meets is in `lambda_elim`: the point-free rewrite curries the comprehension's
/// body, and the curried type does not carry the Σ binder its domain names, so the
/// witness is free at the pass boundary. That is about rebuilding a sum-typed function,
/// not about transactions — the binder comes from the `Map(𝐾, 𝑉)` inside the `Mut`, and
/// the same rewrite over a plain map has no binder to carry.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[should_panic(expected = "free witness reference")]
fn an_entry_binder_over_a_transactional_map_is_not_reachable() {
    check_scalar(
        indoc! {r#"
            m: Mut(Map(String, Int), Txn) := box(map([("a", 1), ("b", 2)]))
            n: Mut(Int, Txn) := 0
            for r in [1]:
                with begin():
                    n := n + sum([v for k -> v in m])
            await_final(n)
        "#},
        Value::Int(3),
    );
}

/// A **filtered** entry comprehension over a transactional map. The filter's predicate and
/// the map's key domain land on one variable: `σ` is what the `Mut` wraps, `Int` is what
/// the predicate types its element at, and structural inference will not join the two.
///
/// Neither half of the entry binder escapes it — filtering on the key and filtering on the
/// value report the same collision — so what the filter meets is the entry comprehension
/// itself rather than which of its two binders the predicate names.
///
/// Three neighbours place it. Dropping the filter types
/// ([`an_entry_binder_over_a_transactional_map_is_not_reachable`] gets as far as
/// `lambda_elim`); dropping the entry binder fails elsewhere, on a scope violation naming
/// the map; and the same filtered comprehension over a **plain** map types and reaches
/// op-conversion ([`a_filtered_comprehension_over_a_map_is_not_reachable`]).
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::on_the_key("sum([q for a -> q in m if a == 1])")]
#[case::on_the_value("sum([q for a -> q in m if q > 10])")]
#[should_panic(expected = "Conflicting Types: Int | σ")]
fn a_filtered_entry_comprehension_over_a_transactional_map_is_not_reachable(
    #[case] comprehension: &str,
) {
    check_scalar(
        &format!(
            indoc! {r"
                m: Mut(Map(Int, Int), Txn) := box(map([(1, 10), (2, 20)]))
                n: Mut(Int, Txn) := 0
                for r in [1]:
                    with begin():
                        n := n + {}
                await_final(n)
            "},
            comprehension
        ),
        Value::Int(20),
    );
}

/// Entry iteration in **statement** position. The binder is read off the target
/// and the body opened exactly as a comprehension's is
/// (`src/ccl/lower/entries.rs`), so the two positions agree by construction
/// rather than by two implementations happening to match — which is what this
/// pins, because the program still does not compile.
///
/// What it meets is not the binder. A `for` over a collection with an
/// accumulator is an induction loop, whose source must be indexed by *iteration
/// position*, and a map's positions are its keys. The name binder fails on the
/// same program at the same message, which is the case beside it.
///
/// Before this change the entry binder was refused at lowering — "only simple
/// name targets are supported" — so what moved is that the two binders now reach
/// the same wall, and closing that wall closes both.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::entry_binder("for k -> v in m:\n    acc += k * v")]
#[case::name_binder("for v in m:\n    acc += v")]
#[should_panic(expected = "must be indexed by iteration position")]
fn a_for_statement_over_a_map_is_not_reachable(#[case] loop_stmt: &str) {
    check_scalar(
        &format!("m = map([(1, 10), (2, 20)])\nacc := 0\n{loop_stmt}\nacc"),
        Value::Int(50),
    );
}
