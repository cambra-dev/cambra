//! The differential: what the compiler computes against what the differential interpreter
//! says the program means.
//!
//! Both sides are observed the same way — through a sink — so the comparison is over what
//! each sink received, not over a returned value. Agreement is **keyed and unordered**: a
//! collection's keys are part of its value (a filter keeps its survivors' positions, a
//! group-by is keyed by the group key), and the order entries arrive in is not.
//!
//! A case the two are known to disagree on pins both answers, so a change to either side
//! fails the pin.

#[path = "support/differential.rs"]
mod differential;

use chl_interp::{Collection, Value};
use differential::{Compiled, run_compiled, run_interpreted};
use indoc::indoc;
use rstest::rstest;

/// What sink `out` observed under the compiler, for a program it compiles and completes.
fn compiled(source: &str) -> Value {
    match run_compiled(source) {
        Compiled::Value(v) => v,
        other => panic!("the compiled program produced no value: {other}"),
    }
}

/// What sink `out` observed under the differential interpreter.
fn interpreted(source: &str) -> Value {
    run_interpreted(source).expect("the interpreter ran")
}

/// Assert the two sides agree on `source`.
fn agree(source: &str) {
    let (c, i) = (compiled(source), interpreted(source));
    assert_eq!(
        c, i,
        "compiler and interpreter disagree\n  compiled:    {c}\n  interpreted: {i}\n  program:\n{source}"
    );
}

/// A boxed conditional chosen once and observed by its keys. Realization unions one gated leg
/// per arm, and the value is the leg holding rows, keyed by its own keys
/// (`src/ccl/design/collections.md`, "Compiling a conditional collection").
#[rstest]
#[case::fed_to_the_sink(indoc! {r#"
    out = test_sink()
    out << (box([1, 2]) if 2 > 1 else box([3, 4, 5]))
"#})]
#[case::the_second_arm_fed_to_the_sink(indoc! {r#"
    c: Bool = False
    out = test_sink()
    out << (box([1, 2]) if c else box([3, 4, 5]))
"#})]
#[case::a_loop_source(indoc! {r#"
    out = test_sink()
    for q in (box([1, 2]) if 2 > 1 else box([3, 4, 5])):
        out << q
"#})]
#[case::a_record_field(indoc! {r#"
    out = test_sink()
    r = (xs=(box([1, 2]) if 2 > 1 else box([3, 4, 5])), n=1)
    out << sum(r.xs)
"#})]
fn a_boxed_conditional_keyed_by_its_arm(#[case] source: &str) {
    agree(source);
}

/// A conditional collection whose condition reads the row: each row takes its own arm. Lambda
/// elimination fans the rows out by the arms' gates, and each leg broadcasts its arm; boxed
/// arms keep their `box`, since the union's codomain binds a witness per row
/// (`src/ccl/design/collections.md`, "A conditional chosen per row").
#[rstest]
#[case::same_domain_arms_in_a_loop(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        out << sum([1, 2] if i > 1 else [3, 4])
"#})]
#[case::boxed_arms_in_a_loop(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        out << sum(box([1, 2]) if i > 1 else box([3, 4, 5]))
"#})]
#[case::boxed_arms_as_a_comprehension_element(indoc! {r#"
    out = test_sink()
    out << [(box([1, 2]) if x > 1 else box([3])) for x in [1, 2]]
"#})]
#[case::same_domain_arms_in_a_comprehension(indoc! {r#"
    out = test_sink()
    out << [sum([1, 2] if x > 1 else [3, 4]) for x in [1, 2]]
"#})]
#[case::an_elif_chain(indoc! {r#"
    out = test_sink()
    for i in [1, 2, 3]:
        out << sum(box([1]) if i == 1 else box([2, 2]) if i == 2 else box([3, 3, 3]))
"#})]
#[case::into_an_accumulator(indoc! {r#"
    acc := 0
    for i in [1, 2]:
        acc := acc + sum(box([1, 2]) if i > 1 else box([3, 4, 5]))
    out = test_sink()
    out << acc
"#})]
#[case::iterated_by_a_comprehension(indoc! {r#"
    out = test_sink()
    out << [sum([y * 10 for y in (box([1, 2]) if x > 1 else box([3]))]) for x in [1, 2]]
"#})]
// A filter's predicate is planned as a lifted term, so a conditional in it reads the row the
// same way.
#[case::in_a_filter_reading_the_loop(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        out << sum([x for x in [1, 2, 3, 4, 5, 6, 7, 8] if x > sum(box([1, 2]) if i > 1 else box([3, 4, 5]))])
"#})]
#[case::in_a_filter_reading_the_element(indoc! {r#"
    out = test_sink()
    out << sum([x for x in [1, 2, 3, 4, 5, 6, 7, 8] if x > sum([1, 2] if x > 4 else [3, 4])])
"#})]
fn a_conditional_chosen_per_row(#[case] source: &str) {
    agree(source);
}

/// A feed crossing `let`s between its target and itself: each is discharged on the edge
/// into the target, so a row naming one compiles (`src/ccl/design/type-inference.md`, "A
/// contribution crosses the binders after its target").
#[rstest]
#[case::a_let_before_the_feed(indoc! {r#"
    out = test_sink()
    xs = [1, 2, 3]
    out << [v for v in xs if v > 1]
"#})]
#[case::a_constant_let_inside_a_loop(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        k = 1
        out << [v for v in [1, 2, 3] if v > k]
"#})]
#[case::a_let_before_a_loop(indoc! {r#"
    out = test_sink()
    xs = [1, 2, 3]
    for r in [1, 2]:
        out << [v for v in xs if v > 1]
"#})]
fn a_feed_crossing_a_let(#[case] source: &str) {
    agree(source);
}

/// A `def` feeding a handle declared outside it, called from the top level or a loop. The
/// handle's element type stands at the level the handle is bound at, so the parameter
/// written into it stays monomorphic and the channel receives what each call passes. Each
/// call site feeds from its own place.
#[rstest]
#[case::called_once(indoc! {r#"
    out = test_sink()
    def f(y):
        out << y
    f(1)
"#})]
#[case::called_in_a_loop(indoc! {r#"
    out = test_sink()
    def f(y):
        out << y
    for r in [1, 2]:
        f(r)
"#})]
#[case::a_row_constant_in_the_parameter(indoc! {r#"
    out = test_sink()
    def f(y):
        out << [v + y for v in [1, 2, 3]]
    for r in [1, 2]:
        f(r)
"#})]
// Each call site is its own place, as two `<<` statements are.
#[case::called_twice(indoc! {r#"
    out = test_sink()
    def f(y):
        out << y
    f(1)
    f(2)
"#})]
#[case::called_once_and_from_a_loop(indoc! {r#"
    out = test_sink()
    def f(y):
        out << y
    out << 0
    f(0)
    for r in [1, 2]:
        f(r)
"#})]
#[case::called_through_another_def(indoc! {r#"
    out = test_sink()
    def f(y):
        out << y
    def g(z):
        f(z)
        f(z + 10)
    g(1)
"#})]
fn a_def_feeding_a_handle_declared_outside_it(#[case] source: &str) {
    agree(source);
}

/// Rows whose keys vary with a loop around the feed. The channel is keyed by the loops'
/// positions and each row is typed at its own position, the loop variable read as the
/// source's value there (`src/ccl/design/type-inference.md`, "A history's value may depend on
/// its position").
#[rstest]
#[case::filtered_by_the_loop_variable(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        out << [v for v in [1, 2, 3] if v > r]
"#})]
#[case::grouped_by_the_loop_variable(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        out << [sum(g) for g in groupby([1, 2, 3, 4], \e -> e // i)]
"#})]
#[case::through_a_let_of_the_loop_variable(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        k = r
        out << [v for v in [1, 2, 3] if v > k]
"#})]
#[case::through_a_let_computed_from_it(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        m = r + 1
        out << [v for v in [1, 2, 3] if v > m]
"#})]
#[case::under_a_filtered_loop(indoc! {r#"
    out = test_sink()
    for r in [1, 2, 3]:
        if r > 1:
            out << [v for v in [1, 2, 3] if v > r]
"#})]
#[case::over_a_named_source(indoc! {r#"
    xs = [1, 2]
    out = test_sink()
    for r in xs:
        out << [v for v in [1, 2, 3] if v > r]
"#})]
#[case::read_back_through_a_defer(indoc! {r#"
    o = defer()
    for r in [1, 2]:
        o << [v for v in [1, 2, 3] if v > r]
    out = test_sink()
    out << sum([sum(row) for row in o])
"#})]
#[case::yielded_by_a_generator(indoc! {r#"
    def rows(xs):
        for x in xs:
            yield [v for v in [1, 2, 3] if v > x]
    out = test_sink()
    out << sum([sum(r) for r in rows([1, 2])])
"#})]
#[case::under_two_loops_reading_the_outer(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [10, 20]:
            out << [v for v in [1, 2, 3] if v > i]
"#})]
#[case::under_two_loops_reading_both(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [1, 2]:
            out << [v for v in [1, 2, 3] if v > i + j]
"#})]
#[case::under_three_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [1, 2]:
            for k in [1, 2]:
                out << [v for v in [1, 2, 3, 4] if v > i + j - k]
"#})]
fn rows_keyed_by_the_loops_around_the_feed(#[case] source: &str) {
    agree(source);
}

/// A nest whose inner loop ranges over keys chosen by the outer loop's value. The feed is
/// keyed by the dependent tuple of the two positions (`src/ccl/design/type-inference.md`,
/// "4.8 Dependent tuples").
#[rstest]
#[case::a_value_fed(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z + i for z in [1, 2, 3] if z > i]:
            out << j
"#})]
#[case::rows_reading_the_inner_variable(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            out << [v for v in [1, 2, 3] if v > j]
"#})]
#[case::rows_over_an_inner_source_reading_the_outer(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z + i for z in [1, 2, 3] if z > i]:
            out << [v for v in [1, 2, 3, 4, 5] if v > j]
"#})]
#[case::an_aggregate_per_row(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            out << sum([v for v in [1, 2, 3] if v > j])
"#})]
#[case::a_third_loop_over_independent_keys(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            for k in [1, 2]:
                out << j + k
"#})]
#[case::a_chain_of_three_dependent_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            for k in [w for w in [1, 2, 3, 4] if w > j]:
                out << k
"#})]
#[case::rows_under_three_dependent_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            for k in [w for w in [1, 2, 3, 4] if w > j]:
                out << [v for v in [1, 2, 3, 4, 5] if v > k]
"#})]
#[case::a_chain_of_four_dependent_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            for k in [w for w in [1, 2, 3, 4] if w > j]:
                for m in [u for u in [1, 2, 3, 4, 5] if u > k]:
                    out << m
"#})]
#[case::only_the_third_loop_dependent(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [1, 2]:
            for k in [w for w in [1, 2, 3, 4] if w > i + j]:
                out << k
"#})]
fn a_feed_under_a_dependent_nest(#[case] source: &str) {
    agree(source);
}

/// Boxed rows fed from a loop, each row's keys depending on the loop variable. The row's
/// filter is a domain the loop's writer builds from the variable, so elimination pairs the
/// variable with the row (`src/ccl/design/type-inference.md`, "A refinement on a collection's
/// domain is data"). Read downstream, each row is a sum whose candidate leaves the loop under
/// the feed's exits, which the kind edge carrying it records.
#[rstest]
#[case::to_a_sink(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        out << box([v for v in [1, 2, 3] if v > r])
"#})]
#[case::read_by_a_comprehension(indoc! {r#"
    o = defer()
    for r in [1, 2]:
        o << box([v for v in [1, 2, 3] if v > r])
    out = test_sink()
    out << sum([sum(b) for b in o])
"#})]
#[case::read_by_a_loop(indoc! {r#"
    o = defer()
    for r in [1, 2]:
        o << box([v for v in [1, 2, 3] if v > r])
    out = test_sink()
    for b in o:
        out << sum(b)
"#})]
fn boxed_rows_fed_from_a_loop(#[case] source: &str) {
    agree(source);
}

/// A feed under a loop that also writes a mutable variable. The loop is a recurrence, one
/// decision per position, and a fed row whose keys depend on the loop variable makes the
/// decision depend on the position, so the history of decisions is keyed by it
/// (`src/ccl/design/type-inference.md`, "A history's value may depend on its position").
#[rstest]
#[case::rows_reading_the_loop_variable(indoc! {r#"
    t := 0
    out = test_sink()
    for r in [1, 2]:
        t += r
        out << [v for v in [1, 2, 3] if v > r]
"#})]
#[case::fed_under_a_condition(indoc! {r#"
    t := 0
    out = test_sink()
    for r in [1, 2, 3]:
        t += r
        if r > 1:
            out << [v for v in [1, 2, 3] if v > r]
"#})]
#[case::rows_reading_both_loops_of_a_nest(indoc! {r#"
    t := 0
    out = test_sink()
    for i in [1, 2]:
        for j in [1, 2]:
            t += j
            out << [v for v in [1, 2, 3, 4] if v > i + j]
"#})]
fn a_feed_under_a_loop_writing_a_mutable_variable(#[case] source: &str) {
    agree(source);
}

/// A binding made in a loop body and read inside a comprehension nested in it. The binding
/// holds one value per row of the loop, and the comprehension runs a level further in, so the
/// read lifts it over the keys beneath each row.
#[rstest]
#[case::as_a_filter_bound(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        m = r + 1
        out << sum([v for v in [1, 2, 3] if v > m])
"#})]
#[case::in_the_element(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        m = r + 1
        out << [v + m for v in [1, 2, 3]]
"#})]
fn a_loop_binding_read_by_a_nested_comprehension(#[case] source: &str) {
    agree(source);
}

/// Rows filtered by the outer binder of a comprehension, with no aggregate over them: each
/// row keeps its own keys.
#[rstest]
#[case::filtered_by_the_outer_binder(indoc! {r#"
    out = test_sink()
    out << [[v for v in [1, 2, 3] if v > r] for r in [1, 2]]
"#})]
#[case::reading_it_in_the_element(indoc! {r#"
    out = test_sink()
    out << [[v * r for v in [1, 2, 3] if v > r] for r in [1, 2]]
"#})]
#[case::filtered_by_a_computation_on_it(indoc! {r#"
    out = test_sink()
    out << [[v for v in [1, 2, 3] if v > r + 1] for r in [1, 2]]
"#})]
fn correlated_rows_without_an_aggregate(#[case] source: &str) {
    agree(source);
}

#[test]
fn a_scalar_feed() {
    agree(indoc! {r#"
        out = test_sink()
        out << 1 + 2
    "#});
}

#[test]
fn arithmetic() {
    agree(indoc! {r#"
        out = test_sink()
        out << (2 + 3) * 4 - 1
    "#});
}

#[test]
fn a_let_binding() {
    agree(indoc! {r#"
        x = 7
        y = x * 3
        out = test_sink()
        out << y
    "#});
}

#[test]
fn a_loop_contributes_per_iteration() {
    agree(indoc! {r#"
        out = test_sink()
        for x in [1, 2, 3]:
            out << x * 10
    "#});
}

#[test]
fn a_record_feed() {
    agree(indoc! {r#"
        out = test_sink()
        out << (a=1, b=2)
    "#});
}

#[test]
fn a_string_feed() {
    agree(indoc! {r#"
        out = test_sink()
        out << "hi"
    "#});
}

#[test]
fn a_bool_feed() {
    agree(indoc! {r#"
        out = test_sink()
        out << 1 < 2
    "#});
}

#[test]
fn a_variant_feed() {
    agree(indoc! {r#"
        out = test_sink()
        out << `some(1)
    "#});
}

/// A collection fed at a site that does not iterate is one element, under that site's one key
/// (`docs/chl-spec.md`, "3.7 Feed operator `<<`").
#[test]
fn a_collection_feed_is_one_element() {
    agree(indoc! {r#"
        out = test_sink()
        out << [x * 2 for x in [1, 2, 3]]
    "#});
}

// These fold a comprehension's result to a scalar before it reaches a sink. They reach the
// comprehension, filter, group-by and field-access machinery through that route.

#[test]
fn a_comprehension_with_a_filter() {
    agree(indoc! {r#"
        out = test_sink()
        out << sum([x * 2 for x in [1, 2, 3, 4] if x > 2])
    "#});
}

#[test]
fn a_record_field_in_a_comprehension() {
    agree(indoc! {r#"
        sales = [
            (region="east", amount=1),
            (region="west", amount=2),
        ]
        out = test_sink()
        out << sum([s.amount for s in sales])
    "#});
}

#[test]
fn a_groupby_rollup() {
    agree(indoc! {r#"
        sales = [
            (region="east", amount=1),
            (region="west", amount=2),
            (region="east", amount=3),
        ]
        out = test_sink()
        out << sum([sum([s.amount for s in g]) for g in groupby(sales, \r -> r.region)])
    "#});
}

/// A comprehension inside a loop that reads the loop variable: the correlated case.
#[test]
fn a_correlated_comprehension() {
    agree(indoc! {r#"
        out = test_sink()
        for x in [1, 2, 3]:
            out << sum([y * x for y in [1, 2]])
    "#});
}

#[test]
fn a_chained_comparison() {
    agree(indoc! {r#"
        out = test_sink()
        n = 2
        out << 1 < n < 3
    "#});
}

#[test]
fn an_annotated_binding() {
    agree(indoc! {r#"
        x: Int = 7
        out = test_sink()
        out << x + 1
    "#});
}

#[test]
fn an_augmented_write_in_a_loop() {
    agree(indoc! {r#"
        acc := 0
        for i in [1, 2, 3]:
            acc += i
        out = test_sink()
        out << acc
    "#});
}

/// A filter reading both binders of a nested loop, inside the loop's write. The filter's
/// predicate and its rows reach each enclosing position separately, so a pull can hold rows
/// whose answers have not arrived.
#[test]
fn a_filter_reading_both_nested_binders() {
    agree(indoc! {r#"
        acc := 0
        for i in [1, 2]:
            for q in [1, 2, 3]:
                acc := acc + sum([z * i * q for z in [1, 2, 3] if z > i - q])
        out = test_sink()
        out << acc
    "#});
}

/// The forms a nested loop's write reads its two binders through, read through a sink so the
/// scheduler drives the nest a position at a time. The filters are the forms the nest's own
/// tests (`tests/compilation_pipeline/nested_loops.rs`) do not reach: a filter's predicate
/// and its rows arrive at each enclosing position separately.
#[rstest]
#[case::a_filter_on_the_outer_binder("sum([z for z in [1, 2, 3] if z > i])")]
#[case::a_filter_on_the_inner_binder_beside_an_outer_body(
    "sum([z * i for z in [1, 2, 3] if z > q])"
)]
#[case::a_filter_on_both_binders_beside_a_closed_body("sum([z for z in [1, 2, 3] if z > i - q])")]
#[case::a_ternary_on_both_binders("(i if q > 1 else q)")]
#[case::a_power_of_the_outer_binder("i ** 2 + q")]
#[case::a_nested_comprehension_reading_both_binders(
    "sum([sum([w * z * i for w in [1, 2]]) for z in [1, 2] if z >= q - 1])"
)]
fn a_nested_write_reads_its_binders(#[case] term: &str) {
    agree(&format!(
        indoc! {r#"
            acc := 0
            for i in [1, 2]:
                for q in [1, 2, 3]:
                    acc := acc + {}
            out = test_sink()
            out << acc
        "#},
        term
    ));
}

/// A feed under nested loops is keyed by the position of every loop around it
/// (`docs/chl-spec.md`, "8.4 Feeds are the second form of mutability"), whether the loops
/// only feed or the outer one carries a mutable variable.
#[rstest]
#[case::two_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [10, 20]:
            out << i + j
"#})]
#[case::three_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [10, 20]:
            for k in [100, 200]:
                out << i + j + k
"#})]
#[case::a_filtered_inner_loop(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [10, 20]:
            if j > i * 10:
                out << i + j
"#})]
#[case::a_binding_between_the_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        m = i * 100
        for j in [10, 20]:
            out << m + j
"#})]
#[case::feeds_at_two_depths(indoc! {r#"
    o = defer()
    for i in [1, 2]:
        o << i
        for j in [10, 20]:
            o << i + j
    out = test_sink()
    out << sum(o)
"#})]
#[case::a_constant_value(indoc! {r#"
    o = defer()
    for i in [1, 2]:
        for j in [10, 20]:
            o << 7
    out = test_sink()
    out << sum(o)
"#})]
#[case::a_feed_only_loop_in_an_accumulator_loop(indoc! {r#"
    t := 0
    out = test_sink()
    for i in [1, 2]:
        t += i
        for j in [10, 20]:
            out << j + i
"#})]
#[case::a_filtered_feed_only_loop_in_an_accumulator_loop(indoc! {r#"
    t := 0
    out = test_sink()
    for i in [1, 2]:
        t += i
        for j in [10, 20]:
            if j > 10:
                out << j + t
"#})]
#[case::two_feed_only_loops_in_an_accumulator_loop(indoc! {r#"
    t := 0
    o = defer()
    for i in [1, 2]:
        t += i
        for j in [10, 20]:
            o << j
            m = j + t
            for k in [1, 2]:
                o << m + k
    out = test_sink()
    out << t + sum(o)
"#})]
#[case::a_feed_under_three_accumulator_loops(indoc! {r#"
    t := 0
    out = test_sink()
    for i in [1, 2]:
        for j in [10, 20]:
            for k in [1, 2]:
                t += k
                out << t + i + j
"#})]
fn a_feed_under_nested_loops(#[case] source: &str) {
    agree(source);
}

/// A group-by under a loop whose key reads the loop's binder. The groups' keys differ per
/// iteration, so the group-by is a dependent family: for each loop position, the keys the
/// key function produces there (`src/ccl/design/type-inference.md`, "4.8 Dependent
/// tuples").
#[rstest]
#[case::every_key_is_the_binder(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        out << sum([sum([s for s in g]) for g in groupby([1, 1, 2], \e -> i)])
"#})]
#[case::the_group_count_varies(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        out << sum([1 for g in groupby([1, 2, 3], \e -> e // i)])
"#})]
#[case::each_group_aggregated(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        out << sum([sum(g) for g in groupby([1, 1, 2], \e -> i)])
"#})]
#[case::the_group_and_the_binder_both_read(indoc! {r#"
    out = test_sink()
    for i in [1, 2, 3]:
        out << sum([max(g) * i for g in groupby([1, 2, 3, 4], \e -> e // i)])
"#})]
#[case::a_filter_in_the_key_reads_the_binder(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        out << sum([sum(g) for g in groupby([1, 1, 2], \e -> sum([z for z in [1, 2, 3] if z > i]))])
"#})]
fn a_group_by_whose_key_reads_the_loop_binder(#[case] source: &str) {
    agree(source);
}

/// A group-by whose key function computes its key with a nested collection, a union, or a
/// conditional. The key function appears in the key domain's predicate and in the partition's,
/// and each copy's nested refinements read that copy's own parameter.
#[rstest]
#[case::a_filter_reading_the_element(indoc! {r#"
    out = test_sink()
    out << sum([sum(g) for g in groupby([1, 1, 2], \e -> sum([z for z in [1, 2, 3] if z > e]))])
"#})]
#[case::a_nested_group_by(indoc! {r#"
    out = test_sink()
    out << sum([sum(g) for g in groupby([1, 1, 2],
        \e -> sum([sum(h) for h in groupby([1, 1, 2], \f -> f)]))])
"#})]
#[case::a_conditional_on_the_element(indoc! {r#"
    out = test_sink()
    out << sum([sum(g) for g in groupby([1, 1, 2], \e -> (e if e > 1 else 0))])
"#})]
#[case::a_union(indoc! {r#"
    out = test_sink()
    out << sum([sum(g) for g in groupby([1, 1, 2], \e -> sum([1, 2] ++ [3, 4]))])
"#})]
#[case::a_conditional_collection(indoc! {r#"
    c: Bool = True
    out = test_sink()
    out << sum([sum(g) for g in groupby([1, 2, 3, 4], \e -> e // sum(box([1, 2]) if c else box([3, 4, 5])))])
"#})]
fn a_group_by_whose_key_computes_with_a_collection(#[case] source: &str) {
    agree(source);
}

/// A conditional element of a comprehension nested in another comprehension or under a loop,
/// reading the enclosing binder, or reading a mutable variable.
#[rstest]
#[case::reading_the_outer_binder(indoc! {r#"
    out = test_sink()
    out << sum([sum([(w if w > 3 else 0) for z in [1, 2]]) for w in [3, 4]])
"#})]
#[case::gating_on_the_inner_binder(indoc! {r#"
    out = test_sink()
    out << sum([sum([(w if z > 1 else z) for z in [1, 2]]) for w in [3, 4]])
"#})]
#[case::under_a_loop(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        out << sum([(i if q > 1 else q) for q in [1, 2, 3]])
"#})]
#[case::reading_a_mutable_variable(indoc! {r#"
    x := 3
    out = test_sink()
    out << sum([x ^+ i if i > 1 else 0 for i in [1, 2, 3]])
"#})]
fn a_conditional_element_reading_an_enclosing_binder(#[case] source: &str) {
    agree(source);
}

/// A generator called in a filter or a group-by key: its body stays in the predicate until
/// planning lifts the predicate or the key out of it, which channelizes it.
#[rstest]
#[case::in_a_filter(indoc! {r#"
    def triples(hxs):
        for hx in hxs:
            yield hx * 3
    out = test_sink()
    out << sum([x for x in [1, 4, 7] if max(triples([1, 2])) > x + 1])
"#})]
#[case::in_a_key(indoc! {r#"
    def triples(hxs):
        for hx in hxs:
            yield hx * 3
    out = test_sink()
    out << sum([sum(g) for g in groupby([1, 1, 2], \e -> max(triples([1, 2])) // e)])
"#})]
#[case::in_a_key_under_a_loop(indoc! {r#"
    def triples(hxs):
        for hx in hxs:
            yield hx * 3
    out = test_sink()
    for i in [1, 2]:
        out << sum([sum(g) for g in groupby([1, 1, 2], \e -> max(triples([1, 2])) * i)])
"#})]
fn a_generator_called_in_a_predicate(#[case] source: &str) {
    agree(source);
}

/// A filter whose predicate aggregates a comprehension filtered by the outer element: the
/// predicate runs as a correlated site of its own.
#[test]
fn a_filter_aggregating_a_correlated_comprehension() {
    agree(indoc! {r#"
        out = test_sink()
        out << sum([x for x in [1, 2, 3] if sum([z for z in [1, 2, 3] if z > x]) > 1])
    "#});
}

/// A two-clause comprehension whose value reads neither binder.
#[test]
fn a_constant_two_clause_comprehension() {
    agree(indoc! {r#"
        out = test_sink()
        out << sum([7 for i in [1, 2] for q in [10, 20]])
    "#});
}

/// A loop over a map literal. The map is a collection keyed by its keys, and its value at a key
/// is the one pair whose key it is, read through a `const` whose type depends on that key.
#[test]
fn a_loop_over_a_map_literal() {
    agree(indoc! {r#"
        out = test_sink()
        for q in map([("a", 1), ("b", 2)]):
            out << q
    "#});
}

/// A mutable variable the inner loop's body introduces, restarting at its seed at every
/// position of both loops, beside an accumulator both loops carry.
#[test]
fn a_mutable_variable_introduced_in_a_nested_loops_body() {
    agree(indoc! {r#"
        acc := 0
        for i in [1, 2]:
            for q in [1, 2, 3]:
                y := sum([z for z in [1, 2, 3] if z > i - q])
                y += i * q
                acc += y
        out = test_sink()
        out << acc
    "#});
}

/// Group keys compared through the loop key, rather than folded away by an aggregate.
/// Inference panics: the group key binder `__gb_k` escapes into a bound outside its scope.
/// Pinned at the interpreter's answer and the compiler's panic.
#[test]
#[should_panic(expected = "open bound recorded")]
fn a_loop_over_groups_panics_in_inference() {
    let source = indoc! {r#"
        sales = [
            (region="east", amount=1),
            (region="west", amount=2),
            (region="east", amount=3),
        ]
        out = test_sink()
        for g in groupby(sales, \r -> r.region):
            out << sum([s.amount for s in g])
    "#};
    assert_eq!(
        interpreted(source).to_string(),
        r#"["east" -> 4, "west" -> 2]"#
    );
    compiled(source);
}

/// A site that never fires still makes the channel a union, because the tagging is fixed
/// by the program text.
#[test]
fn an_untaken_feed_site_still_tags_the_channel() {
    agree(indoc! {r#"
        out = test_sink()
        for x in [1, 2]:
            out << x
        for y in [x for x in [1] if x > 5]:
            out << y
    "#});
}

// ---------------------------------------------------------------------------
// The rest of the constructs.
// ---------------------------------------------------------------------------

#[test]
fn a_match_on_a_variant() {
    agree(indoc! {r#"
        x = `some(7)
        y = match x:
            case `some(v):
                v + 1
            case `none:
                0
        out = test_sink()
        out << y
    "#});
}

#[test]
fn a_match_selecting_the_payload_less_arm() {
    agree(indoc! {r#"
        x = `none
        y = match x:
            case `some(v):
                v + 1
            case `none:
                0
        out = test_sink()
        out << y
    "#});
}

#[test]
fn a_user_function() {
    agree(indoc! {r#"
        def double(n):
            n * 2

        out = test_sink()
        out << double(21)
    "#});
}

#[test]
fn a_function_closing_over_an_outer_binding() {
    agree(indoc! {r#"
        base = 10

        def bump(n):
            n + base

        out = test_sink()
        out << bump(3)
    "#});
}

#[test]
fn a_mutation_loop_accumulator() {
    agree(indoc! {r#"
        acc := 0
        for i in [1, 2, 3, 4, 5]:
            acc := acc + i
        out = test_sink()
        out << acc
    "#});
}

#[test]
fn a_tuple_and_its_components() {
    agree(indoc! {r#"
        out = test_sink()
        t = (3, 4)
        out << t.0 + t.1
    "#});
}

#[test]
fn max_over_a_comprehension() {
    agree(indoc! {r#"
        out = test_sink()
        out << max([x * x for x in [1, 2, 3]])
    "#});
}

#[test]
fn a_collection_union_folded_to_a_scalar() {
    agree(indoc! {r#"
        out = test_sink()
        out << sum([1, 2] ++ [3, 4])
    "#});
}

#[test]
fn an_if_else_in_expression_position() {
    agree(indoc! {r#"
        out = test_sink()
        n = 5
        out << (n * 2 if n > 3 else 0)
    "#});
}

#[test]
fn a_generator_pipeline() {
    agree(indoc! {r#"
        def positives(xs):
            for x in xs:
                if x > 0:
                    yield x

        def squared(xs):
            for x in xs:
                yield x * x

        out = test_sink()
        out << max(squared(positives([-3, 4, -1, 2, 5, -7])))
    "#});
}

#[test]
fn a_defer_channel_read_back() {
    agree(indoc! {r#"
        ch = defer()
        for x in [1, 2, 3]:
            ch << x * 2
        out = test_sink()
        out << sum(ch)
    "#});
}

/// A checked lookup answers `` `some `` for a key the map has and `` `none `` for one it
/// lacks.
#[test]
fn a_checked_lookup_on_a_map() {
    agree(indoc! {r#"
        m = map([("a", 1)])
        r = m["a"]?
        s = m["b"]?
        out = test_sink()
        out << r
        out << s
    "#});
}

/// A function body ending in `if`/`else` denotes its taken branch's value.
#[test]
fn a_function_ending_in_a_conditional() {
    agree(indoc! {r#"
        def sign(n):
            if n > 0:
                1
            else:
                0
        out = test_sink()
        out << sign(5) + sign(-5)
    "#});
}

#[test]
fn a_function_ending_in_a_match() {
    agree(indoc! {r#"
        def f(v):
            match v:
                case `some(x):
                    x
                case `none:
                    0
        out = test_sink()
        out << f(`some(4))
    "#});
}

/// A call resolves its function where the caller was defined, so a later `def` of the same
/// name does not reach it.
#[test]
fn a_function_is_resolved_where_its_caller_is_defined() {
    agree(indoc! {r#"
        def g(n):
            n + 1
        def f(n):
            g(n)
        def g(n):
            n + 100
        out = test_sink()
        out << f(0)
    "#});
}

/// A parameter named like a channel shadows it.
#[test]
fn a_parameter_shadows_a_channel() {
    agree(indoc! {r#"
        ch = defer()
        out = test_sink()
        for c in [1]:
            ch << c
        def h(ch):
            ch + 1
        out << h(10)
    "#});
}

/// A loop over a filtered comprehension runs at its survivors' positions, and each
/// contribution is keyed by the position its element had.
#[test]
fn a_filter_keeps_its_survivors_positions() {
    agree(indoc! {r#"
        out = test_sink()
        for y in [x for x in [1, 2, 3, 4] if x > 2]:
            out << y
    "#});
}

// ---------------------------------------------------------------------------
// Transactions. A block is one commit record, at the next commit time or none at all, and
// a reply fed inside it is indexed by that commit time rather than by the iteration.
// ---------------------------------------------------------------------------

#[test]
fn an_in_block_reply_per_commit() {
    agree(indoc! {r#"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in [10, 20, 30]:
            with begin():
                pool := pool - r
                out << pool
    "#});
}

/// A guard no path takes is a denial: no write, no reply, no commit time.
///
/// Agreement compares commit times by rank, which cannot see a single reply's time, so the
/// compiled side's raw time is pinned too.
#[test]
fn a_denied_block_takes_no_commit_time() {
    let source = indoc! {r#"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in [70, 50]:
            with begin():
                if pool >= r:
                    pool := pool - r
                    out << pool
    "#};
    agree(source);
    assert_eq!(compiled(source).to_string(), "[t1 -> 30]");
}

/// Commit times are dense: the denied iteration leaves no gap.
///
/// Agreement compares commit times by rank, which cannot see a gap, so the compiled side's
/// raw times are pinned too.
#[test]
fn commit_times_are_dense_across_a_denial() {
    let source = indoc! {r#"
        out = test_sink()
        q: Mut(Int, Txn) := 0
        for r in [0, 1, 2]:
            with begin():
                if r != 0:
                    q := r + 1
                    out << q
    "#};
    agree(source);
    assert_eq!(compiled(source).to_string(), "[t1 -> 2, t2 -> 3]");
}

#[test]
fn a_terminal_read_of_a_transactional_store() {
    agree(indoc! {r#"
        pool: Mut(Int, Txn) := 100
        for r in [10, 20, 30]:
            with begin():
                pool := pool - r
        out = test_sink()
        out << await_final(pool)
    "#});
}

/// A loop whose body overwrites an accumulator with a value that reads neither the
/// accumulator nor the loop item. The decision is a constant, so the snapshot scaffold and
/// the source term are both gone by recognition and the writer's extent is all that is left
/// of its source.
#[test]
fn a_loop_overwriting_an_accumulator_with_a_constant() {
    agree(indoc! {r#"
        acc := 1
        for i in [1, 2]:
            acc := 7
        out = test_sink()
        out << acc
    "#});
}

/// A constant write beside an accumulating one. The decision reads `b` and the item, so it is
/// not constant, and the loop's one writer keeps its snapshot.
#[test]
fn a_constant_and_an_accumulating_writer_in_one_loop() {
    agree(indoc! {r#"
        a := 1
        b := 0
        for i in [1, 2, 3]:
            a := 7
            b := b + i
        out = test_sink()
        out << a * 100 + b
    "#});
}

/// A constant reached through a local binding in the body is still a constant decision.
#[test]
fn a_constant_overwrite_through_a_local() {
    agree(indoc! {r#"
        acc := 1
        for i in [1, 2]:
            y = 3
            acc := y
        out = test_sink()
        out << acc
    "#});
}

/// A constant written through a `Mut` parameter: inlining leaves the constant decision a
/// write in the loop body would have.
#[test]
fn a_constant_overwrite_through_a_mut_parameter() {
    agree(indoc! {r#"
        def fw(c: Mut(Int)):
            c := 5
        c := 0
        for x in [1, 2]:
            fw(c)
        out = test_sink()
        out << c
    "#});
}

/// Two accumulators, both written constantly, so the loop's one writer reads no snapshot.
#[test]
fn two_accumulators_both_written_with_constants() {
    agree(indoc! {r#"
        a := 1
        b := 10
        for i in [1, 2]:
            a := 7
            b := 9
        out = test_sink()
        out << a + b
    "#});
}

/// The same overwrite over a source filtered to nothing. The writer's extent is then a
/// declared superset of the positions the source has; the extent's refinement becomes a
/// `restrict` on the source, so no position survives and the accumulator keeps its seed
/// rather than taking the write.
#[test]
fn a_constant_overwrite_over_an_empty_filtered_source() {
    agree(indoc! {r#"
        acc := 1
        for i in [z for z in [1, 2] if z > 9]:
            acc := 7
        out = test_sink()
        out << acc
    "#});
}

/// Filtered to one survivor out of three: the loop body runs once, at the surviving
/// position, and the sink is keyed by it. A writer reading every declared position would
/// feed three.
#[test]
fn a_constant_overwrite_over_a_filtered_source_runs_once_per_survivor() {
    agree(indoc! {r#"
        out = test_sink()
        acc := 1
        for i in [z for z in [1, 2, 3] if z > 2]:
            acc := 7
            out << acc
    "#});
}

/// The transactional half: a `with begin():` block whose write reads nothing, over a source
/// filtered to nothing. No block runs, so no commit lands and the terminal read is the seed.
#[test]
fn a_constant_transactional_write_over_an_empty_filtered_source() {
    agree(indoc! {r#"
        pool: Mut(Int, Txn) := 100
        for r in [z for z in [1, 2] if z > 9]:
            with begin():
                pool := 7
        out = test_sink()
        out << await_final(pool)
    "#});
}

/// The same write over a source filtered to two survivors of three: a block runs once per
/// survivor, keyed by its own commit, and none runs at the filtered position.
#[test]
fn a_constant_transactional_write_runs_once_per_survivor() {
    agree(indoc! {r#"
        pool: Mut(Int, Txn) := 100
        out = test_sink()
        for r in [z for z in [1, 2, 3] if z != 2]:
            with begin():
                pool := 7
                out << 7
    "#});
}

/// A terminal read inside a conditional's test. The test compiles to a refinement predicate
/// on the branch domain, so the read sits in a type slot rather than in the term, and loop
/// recognition's rewrite of transactional reads has to reach it there.
#[test]
fn a_terminal_read_in_a_conditional_test() {
    agree(indoc! {r#"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in [1, 2]:
            with begin():
                pool := pool - r
        out << (1 if await_final(pool) > 90 else 0)
    "#});
}

/// The same read with threshold 98: the seed (100) and the value between the commits (99)
/// clear it, and the final value (97) does not. So the two sides agree on the other branch only
/// when the predicate reads the final value, and a dropped predicate disagrees too.
#[test]
fn a_terminal_read_in_a_conditional_test_not_taken() {
    agree(indoc! {r#"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in [1, 2]:
            with begin():
                pool := pool - r
        out << (1 if await_final(pool) > 98 else 0)
    "#});
}

/// Read-your-writes: a read after a write in the same block sees it.
#[test]
fn read_your_writes_within_a_block() {
    agree(indoc! {r#"
        out = test_sink()
        n: Mut(Int, Txn) := 1
        for i in [1, 2]:
            with begin():
                n := n * 10
                out << n + 1
    "#});
}

#[test]
fn two_stores_written_in_one_block() {
    agree(indoc! {r#"
        out = test_sink()
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 100
        for x in [1, 2]:
            with begin():
                a := a + x
                b := b - x
                out << a * 1000 + b
    "#});
}

/// Two writer sites on one store. Their commits are unordered (`docs/chl-spec.md`, "8.5
/// Ordering and concurrency"), so the interpreter refuses to judge the program; the compiler
/// picks an order, and this checks only that it runs the program to completion.
#[test]
fn two_writer_sites_on_one_store_are_not_judged() {
    let source = indoc! {r#"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in [10]:
            with begin():
                pool := pool - r
                out << pool
        for r in [5]:
            with begin():
                pool := pool - r
                out << pool
    "#};
    compiled(source);
    let refusal = run_interpreted(source).expect_err("the interpreter refuses");
    assert!(refusal.contains("more than one `with` block"), "{refusal}");
}

/// Two stores, each written by its own loop. The two sides number commits differently, and a
/// reply channel's keys have type `Txn`, so the comparison matches them by commit order.
#[test]
fn two_writer_sites_on_two_stores_agree_up_to_commit_time_numbering() {
    agree(indoc! {r#"
        out = test_sink()
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for r in [1, 2]:
            with begin():
                a := a + r
        for r in [10, 20]:
            with begin():
                b := b + r
                out << b
    "#});
}

#[test]
fn a_function_writing_through_a_mut_parameter() {
    agree(indoc! {r#"
        def bump(c: Mut(Int)):
            c += 1

        n := 1
        bump(n)
        bump(n)
        out = test_sink()
        out << n
    "#});
}

/// A function captures the values of free names at its definition (`docs/chl-spec.md`, "4.1
/// `def` — function definition"), so a later write to a captured mutable variable does not
/// reach it. The compiler reads the variable's latest value instead. Pinned at both answers.
#[test]
fn a_captured_mutable_variable_is_read_late() {
    let source = indoc! {r#"
        c := 1

        def f(n):
            n + c

        c := 5
        out = test_sink()
        out << f(0)
    "#};
    assert_eq!(compiled(source).to_string(), "[() -> 5]");
    assert_eq!(interpreted(source).to_string(), "[() -> 1]");
}

/// A user function named like a builtin shadows it: the nearest binding wins
/// (`docs/chl-spec.md`, "3.2 Names"). The compiler calls the builtin. Pinned at both answers.
#[test]
fn a_user_function_named_like_a_builtin_is_ignored() {
    let source = indoc! {r#"
        def sum(xs):
            7

        out = test_sink()
        out << sum([1, 2])
    "#};
    assert_eq!(compiled(source).to_string(), "[() -> 3]");
    assert_eq!(interpreted(source).to_string(), "[() -> 7]");
}

/// A channel fed from two places is a union of them, so its keys are tagged by which
/// place fed them. One site leaves the keys bare, which is why every single-site case
/// above compares without tags.
#[test]
fn two_feed_sites_tag_their_keys() {
    agree(indoc! {r#"
        out = test_sink()
        for x in [1, 2]:
            out << x
        for y in [10, 20]:
            out << y
    "#});
}

/// Aggregating a mutable collection that a keyed write has touched.
#[test]
fn aggregating_a_keyed_written_store() {
    agree(indoc! {r#"
        m: Mut(Map(String, Int)) := box(map([("a", 1)]))
        for k in ["b", "c"]:
            m[k] := 9
        out = test_sink()
        out << sum(m)
    "#});
}

/// The same store, aggregated without a keyed write, agrees.
#[test]
fn a_seeded_mutable_collection_aggregates() {
    agree(indoc! {r#"
        m: Mut(Map(String, Int)) := box(map([("a", 1), ("b", 2)]))
        out = test_sink()
        out << sum(m)
    "#});
}

/// The comprehension binder keeps division in the runtime rather than constant folding it.
#[rstest::rstest]
#[case("7", "2", 3)]
#[case("-7", "2", -4)]
#[case("7", "-2", -4)]
#[case("-7", "-2", 3)]
#[case("6", "-2", -3)]
#[case("0", "-2", 0)]
#[case("-9223372036854775807 - 1", "3", -3_074_457_345_618_258_603)]
#[case("1", "-9223372036854775807 - 1", -1)]
fn signed_floor_division_agrees(
    #[case] dividend: &str,
    #[case] divisor: &str,
    #[case] expected: i64,
) {
    let source = format!(
        indoc! {r#"
        out = test_sink()
        out << sum([x // ({divisor}) for x in [{dividend}]])
    "#},
        divisor = divisor,
        dividend = dividend
    );
    let expected = Value::Collection(Collection::from_entries(vec![(
        Value::Unit,
        Value::Int(expected),
    )]));
    assert_eq!(compiled(&source), expected);
    assert_eq!(interpreted(&source), expected);
}

/// A constant whole-collection write in a loop body replaces the collection at each iteration.
#[test]
fn a_constant_whole_collection_write_in_a_loop() {
    agree(indoc! {r#"
        out = test_sink()
        c := [1, 2]
        for i in [1, 2]:
            c := [3, 4]
        out << sum(c)
    "#});
}

/// The same write through a `Mut` parameter, to a map.
#[test]
fn a_constant_whole_map_write_through_a_mut_parameter() {
    agree(indoc! {r#"
        def put(m: Mut(Map(Int, Int))):
            m := box(map([(5, 50), (6, 60)]))
        m: Mut(Map(Int, Int)) := box(map([(1, 10), (2, 20)]))
        for x in [3, 4]:
            put(m)
        out = test_sink()
        out << sum(m)
    "#});
}
