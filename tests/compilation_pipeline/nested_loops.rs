//! Nested `for` loops with mutable variables — a recurrence per position of the loop
//! around it.
//!
//! The cases are grouped by the feature each one crosses nesting with, because what a
//! nested recurrence has to get right is composition: the same rule applies at every
//! level (seed from the enclosing accumulator's previous value, write back the inner
//! final), and a case that needs its own rule says the representation is wrong.
//!
//! Every case states the value it must answer, including the five that do not compile
//! yet, because computing a value afterwards would let the implementation choose its own.
//! Those five **pin the error they reach** rather than being ignored: a pinned failure
//! catches a change in how a case fails, which an ignored one cannot.
//!
//! Two of the five are the nest's own — a `with begin():` inside one has no commit site
//! the carrier keys. The other three are not about nesting at all, and each gives the
//! program without a nested loop that fails the same way.

use std::time::Duration;

use cambra::interpreter::Value;
use indoc::indoc;
use rstest_log::rstest;

use crate::helpers::*;

// ---------------------------------------------------------------------------
// The base cases: what nesting means
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// (1+2+3) × (1+2). The inner source names nothing outer.
#[case::independent(
    indoc! {r"
        total := 0
        for x in [1, 2, 3]:
            for y in [1, 2]:
                total += x * y
        total
    "},
    18
)]
// The inner source **is** the outer element — the case a product domain cannot express,
// because each outer row carries its own inner domain.
#[case::inner_source_is_the_outer_element(
    indoc! {r"
        total := 0
        for xs in [[1, 2], [3, 4]]:
            for x in xs:
                total += x
        total
    "},
    10
)]
// 1×(1+2+3) + 2×(1+2+3): the body reads the outer binder.
#[case::correlated_body(
    indoc! {r"
        total := 0
        for r in [1, 2]:
            for v in [1, 2, 3]:
                total += v * r
        total
    "},
    18
)]
fn a_nested_loop_accumulates(#[case] program: &str, #[case] total: i64) {
    check_scalar(program, Value::Int(total));
}

// ---------------------------------------------------------------------------
// Depth: the rule applies per level, not per depth
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(20))]
// (1+2)³.
#[case::depth_three(
    indoc! {r"
        total := 0
        for x in [1, 2]:
            for y in [1, 2]:
                for z in [1, 2]:
                    total += x * y * z
        total
    "},
    27
)]
// (1+2)⁴ — a fourth level needs no fourth rule.
#[case::depth_four(
    indoc! {r"
        total := 0
        for w in [1, 2]:
            for x in [1, 2]:
                for y in [1, 2]:
                    for z in [1, 2]:
                        total += w * x * y * z
        total
    "},
    81
)]
// Dependent at every level. Rectangular on purpose: a jagged nested literal needs
// `box`, which is a collection-domain question and not a nesting one.
#[case::depth_three_dependent(
    indoc! {r"
        total := 0
        for xss in [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]:
            for xs in xss:
                for x in xs:
                    total += x
        total
    "},
    36
)]
fn nesting_is_unbounded(#[case] program: &str, #[case] total: i64) {
    check_scalar(program, Value::Int(total));
}

// ---------------------------------------------------------------------------
// Accumulators at different depths in one nest
// ---------------------------------------------------------------------------

/// Two accumulators whose histories have **different domains** in one loop nest: `a`
/// over the outer positions, `b` over the inner ones. They cannot share a carrier, so
/// this is what says a nest is several carriers rather than one carrier with a wider
/// key set. `a` counts 3 outer rows, `b` sums 10+20 three times.
#[test]
fn accumulators_at_two_depths_keep_their_own_domains() {
    check_scalar(
        indoc! {r"
            a := 0
            b := 0
            for x in [1, 2, 3]:
                a += 1
                for y in [10, 20]:
                    b += y
            a * 1000 + b
        "},
        Value::Int(3090),
    );
}

/// Jagged inner sources, so a flattened iteration of fixed width would answer
/// differently. Answers 21 once it compiles.
///
/// Rows of differing length are of differing type, so the collection is a sum and its
/// domain is a witness — the iteration source
/// `iterating_a_witness_domained_collection_is_unimplemented` pins as missing. Nesting
/// and jaggedness are both beside the point: a *single* loop over any boxed source
/// (`total := 0; for x in box([1, 2]): total += x`) trips the same post-letrec
/// witness-scope assertion, because the accumulator's history binds over the
/// collection's own domain and so sits outside the scope of the binder that domain
/// names. `sums.rs` pins that one as
/// `iterating_a_witness_domained_collection_in_a_loop_is_unimplemented`; this case adds
/// a level of nesting to it and reaches the same assertion.
#[test]
#[cfg_attr(
    not(debug_assertions),
    ignore = "the message is from inference's debug-only witness-scope check"
)]
fn jagged_inner_sources_need_a_witness_domained_source() {
    check_compile_error(
        indoc! {r"
            total := 0
            for xs in box([box([1]), box([2, 3]), box([4, 5, 6])]):
                for x in xs:
                    total += x
            total
        "},
        "free witness reference",
    );
}

/// A mutable variable introduced **between** the loops. Its history is over the inner
/// positions at each outer one, and it is read once per outer row after the inner loop —
/// which is the inner carrier's own final read. It needs no rule of its own: the
/// introduction seeds the read-your-writes environment and the inner fold replaces that
/// entry with its final read.
#[test]
fn a_mutable_variable_may_be_introduced_between_the_loops() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2]:
                inner := 0
                for y in [10, 20]:
                    inner += y
                total += inner
            total
        "},
        Value::Int(60),
    );
}

// ---------------------------------------------------------------------------
// Crossed with the write forms
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// A conditional write inside the inner loop: y = 2 only, so (1+2+3) × 2.
#[case::conditional_inner_write(
    indoc! {r"
        total := 0
        for x in [1, 2, 3]:
            for y in [1, 2]:
                if y > 1:
                    total += x * y
        total
    "},
    12
)]
// A conditional on the **outer** binder, gating a whole inner loop.
#[case::conditional_around_the_inner_loop(
    indoc! {r"
        total := 0
        for x in [1, 2, 3]:
            if x > 1:
                for y in [10, 20]:
                    total += y
        total
    "},
    60
)]
// `-=` folds by the same recurrence: 100 - (1+2+3) - (1+2+3).
#[case::subtracting(
    indoc! {r"
        total := 100
        for x in [1, 2]:
            for y in [1, 2, 3]:
                total -= y
        total
    "},
    88
)]
// `*=` is a recurrence like any other — it is only unexpressible as a *fold*.
#[case::multiplying(
    indoc! {r"
        total := 1
        for x in [1, 2]:
            for y in [2, 3]:
                total *= y
        total
    "},
    36
)]
// Last-write-wins across the whole nest.
#[case::overwriting(
    indoc! {r"
        s := 0
        for x in [1, 2]:
            for y in [10, 20]:
                s := y
        s
    "},
    20
)]
// The body reads the accumulator it writes — a scan, which a recurrence expresses and
// an aggregate does not. Positions in order: 1, 4, 9, 20.
#[case::reads_what_it_writes(
    indoc! {r"
        total := 0
        for x in [1, 2]:
            for y in [1, 2]:
                total += total + y
        total
    "},
    20
)]
fn a_nested_loop_carries_any_write_law(#[case] program: &str, #[case] total: i64) {
    check_scalar(program, Value::Int(total));
}

// ---------------------------------------------------------------------------
// Crossed with the collection features
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// A map as the inner source: (1+2) × (1+2).
#[case::map_inner_source(
    indoc! {r#"
        m = map([("a", 1), ("b", 2)])
        total := 0
        for x in [1, 2]:
            for v in m:
                total += v * x
        total
    "#},
    9
)]
// A comprehension as the inner source, filtered: (2+3) × 2.
#[case::filtered_comprehension_inner_source(
    indoc! {r"
        total := 0
        for x in [1, 2]:
            for y in [z for z in [1, 2, 3] if z > 1]:
                total += y
        total
    "},
    10
)]
// A comprehension inside the inner loop's body, reading both binders.
#[case::comprehension_in_the_inner_body(
    indoc! {r"
        total := 0
        for x in [1, 2]:
            for y in [1, 2]:
                total += sum([x * y * k for k in [1, 2]])
        total
    "},
    27
)]
// The outer source is itself a comprehension over a map, so the outer loop's positions
// are the map's keys. It reaches the engine like any other nest now that a store carries
// the domain it was driven at rather than enumerating one from its type.
#[case::comprehension_outer_source(
    indoc! {r#"
        m = map([("a", 1), ("b", 2)])
        total := 0
        for x in [v * 10 for v in m]:
            for y in [1, 2]:
                total += x * y
        total
    "#},
    90
)]
fn a_nested_loop_composes_with_collections(#[case] program: &str, #[case] total: i64) {
    check_scalar(program, Value::Int(total));
}

/// A record field as the inner source, where the rows' fields hold collections of
/// **differing length**. Answers 9 once it compiles.
///
/// Refused before the nest is reached, and by the literal alone: the element join of
/// `[(n=1, xs=[1, 2]), (n=2, xs=[3])]` narrows a collection domain, which a collection's
/// domain being its data forbids. Give the two rows the same length and the same nest
/// runs, so what this pins is jaggedness rather than a collection-valued field — the
/// same gap `jagged_inner_sources_need_a_witness_domained_source` reaches from the
/// iteration side.
#[test]
fn a_collection_valued_field_of_differing_lengths_is_refused() {
    check_compile_error(
        indoc! {r"
            rows = [(n=1, xs=[1, 2]), (n=2, xs=[3])]
            total := 0
            for r in rows:
                for x in r.xs:
                    total += x * r.n
            total
        "},
        "collection domains have no common answer",
    );
}

// ---------------------------------------------------------------------------
// Crossed with the other carrier
// ---------------------------------------------------------------------------

/// A nested loop whose inner body writes a **transactional** mutable variable is
/// refused, and the refusal is pinned because the alternative is a wrong answer rather
/// than a loud one.
///
/// A commit site is keyed on the loop enclosing it — `transact_phase` strips each
/// `Begin` against that one loop — and the accumulator scan does not enter a `with`
/// block, so an inner loop around a transaction contributes no accumulator and its own
/// iteration is simply lost. The program then commits one outer row's writes and
/// answers 30 where 60 is right. When a nested carrier keys its own commit sites this
/// becomes a value test expecting 60.
#[test]
fn a_nested_loop_around_a_transaction_is_refused() {
    check_compile_error(
        indoc! {r"
            t: Mut(Int, Txn) := 0
            for x in [1, 2]:
                for y in [10, 20]:
                    with begin():
                        t := t + y
            await_final(t)
        "},
        "a `with begin():` transaction inside a nested `for` is not supported",
    );
}

/// The same transaction one level out, which is what the refusal above points at: a
/// single loop around a commit site sequences it, and the answer is the sum of its
/// writes.
#[test]
fn a_flat_loop_around_a_transaction_still_commits() {
    check_scalar(
        indoc! {r"
            t: Mut(Int, Txn) := 0
            for y in [10, 20]:
                with begin():
                    t := t + y
            await_final(t)
        "},
        Value::Int(30),
    );
}

/// A nested loop inside a generator: the yields collect over the outer domain while the
/// inner recurrence runs per outer row, so 30 after the first row and 60 after the
/// second.
///
/// A generator's yield rides the enclosing decision, so the record the fields attach to
/// sits under the `letrec` the inner carrier binds — which is why `attach_feed_fields`
/// descends through a `letrec` as it does through a `let`.
#[test]
fn a_nested_loop_inside_a_generator_yields_per_outer_row() {
    check_scalar(
        indoc! {r"
            def g(k):
                total := 0
                for x in [1, 2]:
                    for y in [10, 20]:
                        total += y
                    yield total
            sum([v for v in g(0)])
        "},
        Value::Int(90),
    );
}

// ---------------------------------------------------------------------------
// Crossed with feeds and the commit carrier
// ---------------------------------------------------------------------------
//
// A loop body may carry induction accumulators, a commit site and feeds together, so a
// nest has to keep all three working at once rather than one at a time. These are the
// mixtures, and they are what says the three compose rather than merely coexisting.

/// A feed from inside the nest. Its tap is site-domained — one value per iteration of
/// the writer's own source — so in a nest the site is the nest, and `out` carries one
/// value per innermost position: 10, 30, 40, 60.
///
/// The feed rides the enclosing decision as a tap holding the inner history's own tap,
/// which is one collection per enclosing position, and the channel flattens that to the
/// pair of positions it was fed at. Everything between carries a collection as a value:
/// the tap's arm materializes one and its projection opens one.
#[test]
fn a_feed_inside_a_nest_taps_every_innermost_position() {
    check_scalar(
        indoc! {r"
            out = defer()
            total := 0
            for x in [1, 2]:
                for y in [10, 20]:
                    total += y
                    out << total
            sum([v for v in out])
        "},
        Value::Int(140),
    );
}

/// A statement after the inner loop. Nothing requires an inner `for` to be its body's
/// last statement, which is what lets the between-the-loops shape be written at all —
/// the value the inner loop leaves is read by the statements that follow it.
#[test]
fn a_statement_may_follow_the_inner_loop() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2]:
                for y in [10, 20]:
                    total += y
                total += 1
            total
        "},
        Value::Int(62),
    );
}

/// The commit carrier meeting an induction accumulator inside one nest: the block reads
/// `cnt`, which advances at the outer level, so the decision needs a cross-domain read
/// at a position the nest names rather than a single loop's. Refused with the rest of
/// the transactional nest cases; the value is what it should answer — 100 − (10+20)·1 −
/// (10+20)·2.
#[test]
fn a_commit_site_reading_an_outer_accumulator_is_refused() {
    check_compile_error(
        indoc! {r"
            pool: Mut(Int, Txn) := 100
            cnt := 0
            for x in [1, 2]:
                cnt += 1
                for y in [10, 20]:
                    with begin():
                        pool := pool - y * cnt
            await_final(pool)
        "},
        "a `with begin():` transaction inside a nested `for` is not supported",
    );
}

// ---------------------------------------------------------------------------
// Where the inner run starts: seed against carry
// ---------------------------------------------------------------------------
//
// A nested accumulator restarts at each enclosing row from **where the enclosing one had
// got to**, and carries within the row. In the base cases those two are the same number:
// the enclosing writer writes back exactly the inner final, so a row's seed equals the
// previous row's last value and an engine that carried instead of reseeding would answer
// correctly. Every case here writes the shared accumulator **between** the loops, which
// is what makes the seed differ from the carry, and each states the wrong answer its
// own confusion would give.

/// The plain case: `+= 10` between the loops, so each inner run starts 10 above where the
/// last one ended. 0 →10→11→13, then 13 →23→24→26.
///
/// Seeding from the carry instead would skip the enclosing write and answer 16.
#[test]
fn a_write_between_the_loops_seeds_each_inner_run() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2]:
                total += 10
                for y in [1, 2]:
                    total += y
            total
        "},
        Value::Int(26),
    );
}

/// The same, with a conditional inner write whose **first position of each row aborts**.
/// A carry records no change there, so the row's opening value exists only as its seed:
/// 10 (abort) →12→15, then 25 (abort) →27→30.
///
/// Folding the aborted boundary back to the previous row's last *change* answers 20.
#[test]
fn a_write_between_the_loops_survives_a_conditional_inner() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2]:
                total += 10
                for y in [1, 2, 3]:
                    if y > 1:
                        total += y
            total
        "},
        Value::Int(30),
    );
}

/// A row whose inner loop **writes nothing at all**: its guard fires for no position, so
/// the row contributes only the enclosing write. 10 →12 (y=2 passes), then 22 → 22.
///
/// The second row's final is its seed, which appears in no changelog — the decisive case
/// for what an inner run with no writes leaves behind. Carrying answers 12.
#[test]
fn a_row_whose_inner_writes_nothing_keeps_its_seed() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2]:
                total += 10
                for y in [1, 2]:
                    if y > x:
                        total += y
            total
        "},
        Value::Int(22),
    );
}

/// An inner source with **no positions at all**, so no row of the nest runs one. Every
/// enclosing row still answers, at the value the accumulator carried into it.
///
/// Distinct from [`a_row_whose_inner_writes_nothing_keeps_its_seed`], where the row runs
/// positions and writes at none of them: the carrier opens a row there. Here it opens
/// none, so the inner history holds no row at all and the trailing read answers from its
/// default — which is why that read takes its rows from the default rather than from the
/// history it reduces.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Nothing else in the body, so the answer is the accumulator's own init.
#[case::the_nest_alone(
    indoc! {r"
        total := 0
        for x in [1, 2]:
            for y in [z for z in [1, 2] if z > 5]:
                total += y
        total
    "},
    0
)]
// A write between the loops, so each row contributes it and nothing else.
#[case::a_write_between_the_loops(
    indoc! {r"
        total := 0
        for x in [1, 2]:
            for y in [z for z in [1, 2] if z > 5]:
                total += y
            total += 1
        total
    "},
    2
)]
fn an_inner_source_with_no_positions_answers_from_the_seed(
    #[case] program: &str,
    #[case] total: i64,
) {
    check_scalar(program, Value::Int(total));
}

/// The same at **depth three**, where the innermost source runs nothing. The rule is the
/// same at every level, so a carrier that opened no row still says which of its rows will
/// gain no position — and every walk that rebuilds a level carries that statement,
/// including the ones whose base case is a level with no rows at all.
#[rstest]
#[timeout(Duration::from_secs(20))]
// Nothing between the loops: every level contributes its seed, so the answer is the init.
#[case::the_nest_alone(
    indoc! {r"
        total := 0
        for x in [1, 2]:
            for y in [1, 2]:
                for z in [k for k in [1, 2] if k > 5]:
                    total += z
        total
    "},
    0
)]
// A write between the innermost two loops, once per middle row: 2 × 2 × 1.
#[case::a_write_between_the_inner_loops(
    indoc! {r"
        total := 0
        for x in [1, 2]:
            for y in [1, 2]:
                for z in [k for k in [1, 2] if k > 5]:
                    total += z
                total += 1
        total
    "},
    4
)]
fn an_empty_innermost_source_answers_from_the_seed_at_depth_three(
    #[case] program: &str,
    #[case] total: i64,
) {
    check_scalar(program, Value::Int(total));
}

/// Two nests in sequence, the first of which runs no inner position. The second is an
/// ordinary nest, so what this adds is that a carrier that opened no row leaves the one
/// after it unaffected.
#[test]
fn a_nest_that_runs_nothing_is_followed_by_one_that_runs() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2]:
                for y in [z for z in [1, 2] if z > 5]:
                    total += y
            for a in [1, 2]:
                for b in [10, 20]:
                    total += b
            total
        "},
        Value::Int(60),
    );
}

/// A conditional **around** the inner loop, so one enclosing row runs no inner positions
/// whatever its guard would have said. 10, then 20 →21→23, then 33 →34→36.
#[test]
fn a_skipped_inner_loop_keeps_the_write_between_the_loops() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2, 3]:
                total += 10
                if x > 1:
                    for y in [1, 2]:
                        total += y
            total
        "},
        Value::Int(36),
    );
}

/// A **refinement** on the inner source beside a between-the-loops write: the filter
/// decides which positions exist, the write decides where the run starts, and the two are
/// independent. 100 →102→105, then 205 →207→210.
#[test]
fn a_filtered_inner_source_beside_a_write_between_the_loops() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2]:
                total += 100
                for y in [z for z in [1, 2, 3] if z > 1]:
                    total += y
            total
        "},
        Value::Int(210),
    );
}

/// A refinement on the **outer** source crossed with a conditional inner write, so the
/// enclosing positions are sparse *and* the inner ones are. x is 2 then 3, y is 2 then 3:
/// 2×2 + 2×3 + 3×2 + 3×3.
#[test]
fn a_filtered_outer_source_with_a_conditional_inner_write() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [z for z in [1, 2, 3] if z > 1]:
                for y in [1, 2, 3]:
                    if y > 1:
                        total += x * y
            total
        "},
        Value::Int(25),
    );
}

// ---------------------------------------------------------------------------
// Crossed with conditionals, refined sources, and compound element types
// ---------------------------------------------------------------------------
//
// Three shapes that have tripped similar work: a conditional interleaved between the
// loops, a refinement on an iteration source, and an element that is a record or tuple
// rather than a scalar.

/// Inner loops in **both legs** of a conditional, so a branch decision carries a
/// recurrence. A branch decision is `(let | letrec)* in {commit, writes}` for that
/// reason — the shape `decision_writes` reads and `wrap_decision_variant` wraps. 100 for
/// the first row, 10+20 for each of the others.
#[test]
fn inner_loops_in_both_legs_of_a_conditional() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2, 3]:
                if x > 1:
                    for y in [10, 20]:
                        total += y
                else:
                    for y in [100]:
                        total += y
            total
        "},
        Value::Int(160),
    );
}

/// A mutable variable introduced inside a conditional branch and accumulated by an inner
/// loop in that branch — the introduction, the branch and the nest at once. `y` restarts
/// at 0 on each row the guard admits, the inner loop folds it, and the statement after it
/// reads that row's final.
#[test]
fn a_branch_introduced_variable_is_accumulated_by_an_inner_loop() {
    check_scalar(
        indoc! {r"
            t := 0
            for i in [1, 2]:
                if i > 1:
                    y := 0
                    for k in [10, 20]:
                        y += k
                    t += y
            t
        "},
        Value::Int(30),
    );
}

/// A refinement on the **outer** source: the nest iterates what survives the filter,
/// (2+3) × (10+20).
#[test]
fn a_filtered_outer_source() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [z for z in [1, 2, 3] if z > 1]:
                for y in [10, 20]:
                    total += x * y
            total
        "},
        Value::Int(150),
    );
}

/// A **per-iteration binding** made in the outer body and read by the inner loop.
/// Answers 72 once it compiles: `a` is 2 then 4, over inner elements 10 and 20.
///
/// A `Let` is where sharing is decided — op-conversion compiles one into a fan-out so
/// several uses draw on one operator — so the binding cannot be inlined into the inner
/// carrier's components: a collection-valued one would become several tiles over
/// unrelated domains, and a non-recomputable one would be built twice. It has to stay a
/// binding, which means the machinery has to know *which* iteration it is aligned to.
///
/// `a` is aligned to the outer iteration and read where the input is the inner collection,
/// so op-conversion lifts it over the inner keys beneath each outer row before reading it
/// (`LetBinding::depth`, `lift_into_iteration`).
#[test]
fn a_per_iteration_binding_read_by_the_inner_loop() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2]:
                a = x * 2
                for y in [10, 20]:
                    total += a + y
            total
        "},
        Value::Int(72),
    );
}

/// A refinement on the **inner** source that reads the outer binder — a correlated
/// filter, so the inner domain differs per outer row and is narrower than the collection
/// it filters. Answers 8 once it compiles: 2+3, then 3, then nothing.
///
/// Nesting is not what breaks: a correlated filter with no aggregate over it,
/// `[[v for v in [1, 2, 3] if v > r] for r in [1, 2]]`, fails the same way with no loop
/// in the program. `comprehensions.rs` covers each half — `case::correlated_filter`
/// filters but sums, `a_correlated_inner_comprehension_without_an_aggregate` keeps the
/// collection but does not filter — and crossing them is what has no coverage. The
/// aggregate is what hides it: `sum` consumes the inner collection, so its refined
/// domain never has to survive as a value type.
///
/// **The defect** is one rule: a function type whose codomain references a Pi binder it
/// does not name. Here the writer's parameter is a refined pair whose predicate relates
/// its components, so projecting the position component drops the predicate — it names
/// the *other* component — while the cast that establishes the filtered domain states it
/// against the parameter. Making that projection dependent reproduces the cast's domain
/// exactly and carries the program to 8, but a dependent type on a value node's slot
/// flows into every type derived from it, and four sites derive one without the binder:
/// `ccl_utils::typed_compose`, `lambda_elim::arm_compose`, `simplify`'s exponential-beta
/// mint (which says so in its own comment) and `planning::loops` reading a curried
/// history's codomain unopened. Fixing them one at a time does not converge — the groupby
/// partition shape exercises the same derivations — so the rule has to be applied
/// consistently rather than patched. A correlated predicate also reads the enclosing
/// binder in its *term*, which `planning::predicates` rejects by assertion as breaking
/// the value-function property its structural producer/consumer match rests on; that
/// invariant has to be restated before the case can land.
#[test]
fn a_correlated_filter_on_the_inner_source() {
    check_compile_error(
        indoc! {r"
            total := 0
            for x in [1, 2, 3]:
                for y in [z for z in [1, 2, 3] if z > x]:
                    total += y
            total
        "},
        "Type mismatch for Compose[1]",
    );
}

/// A tuple element in the inner source, read by field rather than whole.
#[test]
fn a_tuple_element_in_the_inner_source() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2]:
                for p in [(10, 1), (20, 2)]:
                    total += p.0 * x
            total
        "},
        Value::Int(90),
    );
}

/// A **tuple-valued accumulator** carried across the nest, so the recurrence's value
/// type is compound rather than scalar: the sum of the inner elements beside a count of
/// the positions.
#[test]
fn a_tuple_accumulator_across_a_nest() {
    check_scalar(
        indoc! {r"
            acc := (0, 0)
            for x in [1, 2]:
                for y in [10, 20]:
                    acc := (acc.0 + y, acc.1 + 1)
            acc.0 * 100 + acc.1
        "},
        Value::Int(6004),
    );
}

/// An empty source at **any** level of a nest of **any** depth. What each fix for the
/// empty case states is per level — the drive's completion over `0..=standing`, the empty
/// carrier over every entry of its `complete`, the reduction's meet over `0..=rows` — so a
/// fourth level needs no fourth rule here either. These are what say so.
#[rstest]
#[timeout(Duration::from_secs(30))]
// Depth four, innermost empty: each of 2×2×2 middle rows contributes its `+= 1`.
#[case::d4_innermost_empty(
    indoc! {r"
        total := 0
        for w in [1, 2]:
            for x in [1, 2]:
                for y in [1, 2]:
                    for z in [k for k in [1, 2] if k > 5]:
                        total += z
                    total += 1
        total
    "},
    8
)]
// Depth four, innermost empty, nothing else in any body.
#[case::d4_innermost_empty_bare(
    indoc! {r"
        total := 0
        for w in [1, 2]:
            for x in [1, 2]:
                for y in [1, 2]:
                    for z in [k for k in [1, 2] if k > 5]:
                        total += z
        total
    "},
    0
)]
// Depth three, the **middle** source empty, so the innermost never runs.
#[case::d3_middle_empty(
    indoc! {r"
        total := 0
        for x in [1, 2]:
            for y in [k for k in [1, 2] if k > 5]:
                for z in [1, 2]:
                    total += z
            total += 1
        total
    "},
    2
)]
// Depth three, the **outermost** source empty.
#[case::d3_outer_empty(
    indoc! {r"
        total := 0
        for x in [k for k in [1, 2] if k > 5]:
            for y in [1, 2]:
                for z in [1, 2]:
                    total += z
        total
    "},
    0
)]
// Depth four, non-empty, with a write between every pair of loops.
#[case::d4_writes_between_every_level(
    indoc! {r"
        total := 0
        for w in [1, 2]:
            total += 100
            for x in [1, 2]:
                total += 10
                for y in [1, 2]:
                    total += 1
                    for z in [1, 2]:
                        total += z
        total
    "},
    272
)]
fn an_empty_source_at_any_level_answers_from_the_seed(#[case] program: &str, #[case] total: i64) {
    check_scalar(program, Value::Int(total));
}

/// A per-iteration binding read **further in than it was made**, at every arrangement of
/// depths. Its tile is keyed by the iteration it was compiled over, so a reference running
/// over a deeper one reads it spread across the keys beneath each of its rows — once per
/// iteration between the two, which is why a fourth level needs no fourth rule.
#[rstest]
#[timeout(Duration::from_secs(30))]
// Bound at the outermost body, read two levels in.
#[case::outer_binding_read_at_depth_three(
    indoc! {r"
        total := 0
        for x in [1, 2]:
            a = x * 2
            for y in [1, 2]:
                for z in [10, 20]:
                    total += a + z
        total
    "},
    144
)]
// Bound in the middle body, read one level in.
#[case::middle_binding_read_at_depth_three(
    indoc! {r"
        total := 0
        for x in [1, 2]:
            for y in [1, 2]:
                b = y * 10
                for z in [1, 2]:
                    total += b + z
        total
    "},
    132
)]
// One at each level, each read at the innermost.
#[case::a_binding_at_every_level(
    indoc! {r"
        total := 0
        for x in [1, 2]:
            a = x * 100
            for y in [1, 2]:
                b = y * 10
                for z in [1, 2]:
                    total += a + b + z
        total
    "},
    1332
)]
// Bound at the outermost, read at depth four.
#[case::outer_binding_read_at_depth_four(
    indoc! {r"
        total := 0
        for w in [1, 2]:
            a = w * 2
            for x in [1, 2]:
                for y in [1, 2]:
                    for z in [1, 2]:
                        total += a + z
        total
    "},
    72
)]
fn a_binding_is_lifted_into_the_iteration_that_reads_it(#[case] program: &str, #[case] total: i64) {
    check_scalar(program, Value::Int(total));
}

/// A write between the loops with the inner loop always run — three rows of `total += 10`
/// and three inner runs of `1 + 2`.
///
/// The arithmetic `a_skipped_inner_loop_keeps_the_write_between_the_loops` is measured
/// against: skipping one row's inner run takes 3 off this.
#[test]
fn a_write_between_the_loops_runs_once_per_enclosing_row() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2, 3]:
                total += 10
                for y in [1, 2]:
                    total += y
            total
        "},
        Value::Int(39),
    );
}

/// The same with a guard around the inner loop that every row passes, so the guard decides
/// which rows run and nothing else.
#[test]
fn a_guard_every_row_passes_leaves_the_nest_unchanged() {
    check_scalar(
        indoc! {r"
            total := 0
            for x in [1, 2, 3]:
                total += 10
                if x > 0:
                    for y in [1, 2]:
                        total += y
            total
        "},
        Value::Int(39),
    );
}
