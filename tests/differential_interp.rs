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

/// A collection fed at a site that does not iterate nests under that site's one key. The
/// compiler splices it into the channel instead: channelize takes the channel's domain from
/// the contribution's own domain. Pinned at both answers.
#[test]
fn a_collection_feed_lands_flat() {
    let source = indoc! {r#"
        out = test_sink()
        out << [x * 2 for x in [1, 2, 3]]
    "#};
    let list = |xs: &[i64]| {
        Value::Collection(Collection::from_list(
            xs.iter().map(|x| Value::Int(*x)).collect(),
        ))
    };
    assert_eq!(compiled(source), list(&[2, 4, 6]));
    assert_eq!(
        interpreted(source),
        Value::Collection(Collection::from_entries(vec![(
            Value::Unit,
            list(&[2, 4, 6])
        )]))
    );
}

// A fed collection lands flat (see `a_collection_feed_lands_flat`), so these fold a
// comprehension's result to a scalar before it reaches a sink. They reach the comprehension,
// filter, group-by and field-access machinery through that route.

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

/// A comprehension inside a loop that reads the loop variable does not convert (the
/// correlated case). Pinned at the compiler's error.
#[test]
fn a_correlated_comprehension_does_not_compile() {
    let source = indoc! {r#"
        out = test_sink()
        for x in [1, 2, 3]:
            out << sum([y * x for y in [1, 2]])
    "#};
    // The interpreter has no trouble with it; the compiler is what stops.
    assert_eq!(interpreted(source).to_string(), "[3, 6, 9]");
    match run_compiled(source) {
        Compiled::Rejected(err) => assert!(
            err.contains("non-combinator curry"),
            "expected the curry conversion error, got: {err}"
        ),
        other => panic!("expected the compiler to reject a correlated comprehension, got {other}"),
    }
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

/// The same read against a threshold only the final value, 97, fails to clear: the seed, 100,
/// and the value between the commits, 99, both clear it. So the two sides agree on the other
/// branch only when the predicate reads the final value, and a dropped predicate disagrees
/// too.
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

/// Aggregating a mutable collection that a keyed write has touched panics in `Aggregate`
/// with `expected a collection, got Scalar(Variants([]))`. Minimised: the same store
/// aggregates fine with no write, and a plain map literal aggregates fine, so the keyed
/// write is what breaks it. Pinned at the interpreter's answer and the compiler's panic.
#[test]
#[should_panic(expected = "Aggregate expected a collection")]
fn aggregating_a_keyed_written_store_panics() {
    let source = indoc! {r#"
        m: Mut(Map(String, Int)) := box(map([("a", 1)]))
        for k in ["b", "c"]:
            m[k] := 9
        out = test_sink()
        out << sum(m)
    "#};
    assert_eq!(
        interpreted(source),
        Value::Collection(Collection::from_entries(vec![(
            Value::Unit,
            Value::Int(19)
        )]))
    );
    compiled(source);
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

/// `//` is floor division (`docs/chl-spec.md`, "3.3 Arithmetic and logical operators"). The
/// runtime's integer kernel (`src/scalar_ops.rs`) truncates toward zero instead, which
/// differs when the operands' signs differ. Pinned at both answers.
#[test]
fn floor_division_with_a_negative_divisor_truncates() {
    let source = indoc! {r#"
        out = test_sink()
        n = -2
        out << 7 // n
    "#};
    let at_unit =
        |v: i64| Value::Collection(Collection::from_entries(vec![(Value::Unit, Value::Int(v))]));
    assert_eq!(compiled(source), at_unit(-3));
    assert_eq!(interpreted(source), at_unit(-4));
}
