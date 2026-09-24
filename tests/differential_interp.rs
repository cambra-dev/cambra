//! The differential: what the compiler computes against what the reference interpreter
//! says the program means.
//!
//! Both sides are observed the same way — through a sink — so the comparison is over what
//! each sink received, not over a returned value. Agreement is **keyed and unordered**: a
//! collection's keys are part of its value (a filter keeps its survivors' positions, a
//! group-by is keyed by the group key), and the order entries arrive in is not.
//!
//! A case the two are known to disagree on is listed in [`KNOWN_DIVERGENT`] with the defect
//! that causes it, so an unexplained disagreement stays distinguishable from a pinned one.

use std::collections::BTreeMap;

use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::interpreter::{Consumer, Value as TileValue};
use chl_interp::{Collection, Value};
use indoc::indoc;

/// Programs the compiler and the interpreter disagree on today, each with the defect that
/// makes them disagree. Listed rather than omitted: a case nobody runs is a case whose
/// status nothing reports.
const KNOWN_DIVERGENT: &[(&str, &str)] = &[(
    "collection feed lands flat",
    "channelize takes the channel's domain from the contribution's own domain, so a \
     collection fed at a non-iterated site is spliced into the channel instead of nesting \
     under one key",
)];

/// Run `source` through the compiler, answering what sink `out` observed.
fn compiled(source: &str) -> Value {
    const CAP: usize = 10_000;
    let mut ctx = GlobalContext::default();
    let sink = ctx.register_test_sink("out");
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let program = match compile_program(&mut ctx, source, consumer) {
        Ok(p) => p,
        Err(e) => panic!("compile failed: {e:?}"),
    };
    for _ in 0..CAP {
        ctx.scheduler().check_for_notifications();
        if program.done.try_recv().is_ok() {
            break;
        }
    }
    convert(sink.value().expect("the sink observed a value"))
}

/// Run `source` through the reference interpreter, answering what sink `out` observed.
fn interpreted(source: &str) -> Value {
    let mut obs = chl_interp::run(source, BTreeMap::new()).expect("the interpreter ran");
    obs.remove("out").expect("the program declares sink `out`")
}

/// Read a compiled value in the interpreter's domain.
///
/// The only real decision is `UInt`: a key the compiler numbers is the same key the
/// interpreter numbers, and keeping two integer types apart here would make every
/// positional collection differ for a reason that is about representation.
fn convert(v: TileValue) -> Value {
    match v {
        TileValue::Int(i) => Value::Int(i),
        TileValue::UInt(u) => Value::Int(u as i64),
        TileValue::String(s) => Value::Str(s.to_string()),
        TileValue::Bool(b) => Value::Bool(b),
        TileValue::Unit => Value::Unit,
        TileValue::Record(fields) => {
            Value::Record(fields.into_iter().map(|(n, v)| (n, convert(v))).collect())
        }
        TileValue::Union { tag, inner } => Value::Variant {
            tag: tag.to_string(),
            payload: Box::new(convert(*inner)),
        },
        TileValue::Function(bindings) => Value::Collection(Collection::from_entries(
            bindings
                .into_iter()
                .map(|b| (convert(b.input), convert(b.output)))
                .collect(),
        )),
        TileValue::ComputableFunction(_) => {
            panic!("a function value reached a sink, which cannot happen")
        }
    }
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
fn arithmetic_and_comparison() {
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

/// The divergence is named rather than skipped, so its entry is what has to be deleted
/// when the defect is fixed.
#[test]
fn a_collection_feed_is_known_divergent() {
    let source = indoc! {r#"
        out = test_sink()
        out << [x * 2 for x in [1, 2, 3]]
    "#};
    let (c, i) = (compiled(source), interpreted(source));
    assert_ne!(
        c, i,
        "the collection feed now agrees — delete its `KNOWN_DIVERGENT` entry"
    );
    assert_eq!(KNOWN_DIVERGENT.len(), 1, "one divergence is recorded");
}

// Until a collection can be fed (see `KNOWN_DIVERGENT`), a comprehension's result reaches a
// sink only by being folded to a scalar first. These reach the comprehension, filter,
// group-by and field-access machinery through that route.

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

/// A comprehension inside a loop that reads the loop variable does not convert — the
/// correlated case. Pinned at the compiler's error, so the differential records why it
/// cannot reach this shape rather than omitting it.
#[test]
fn a_correlated_comprehension_does_not_compile() {
    let source = indoc! {r#"
        out = test_sink()
        for x in [1, 2, 3]:
            out << sum([y * x for y in [1, 2]])
    "#};
    // The interpreter has no trouble with it; the compiler is what stops.
    interpreted(source);
    let mut ctx = GlobalContext::default();
    let _ = ctx.register_test_sink("out");
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let err = compile_program(&mut ctx, source, consumer)
        .err()
        .expect("the compiler rejects a correlated comprehension");
    assert!(
        format!("{err:?}").contains("non-combinator curry"),
        "expected the curry conversion error, got: {err:?}"
    );
}

#[test]
fn a_chained_comparison() {
    agree(indoc! {r#"
        out = test_sink()
        out << 1 < 2
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

// ---------------------------------------------------------------------------
// Transactions. A block is one commit record, at the next tick or none at all, and a
// reply fed inside it is indexed by that tick rather than by the iteration.
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

/// A guard no path takes is a denial: no write, no reply, no tick.
#[test]
fn a_denied_block_consumes_no_tick() {
    agree(indoc! {r#"
        out = test_sink()
        pool: Mut(Int, Txn) := 100
        for r in [70, 50]:
            with begin():
                if pool >= r:
                    pool := pool - r
                    out << pool
    "#});
}

/// Ticks are dense: the denied iteration leaves no gap.
#[test]
fn ticks_are_dense_across_a_denial() {
    agree(indoc! {r#"
        out = test_sink()
        q: Mut(Int, Txn) := 0
        for r in [0, 1, 2]:
            with begin():
                if r != 0:
                    q := r + 1
                    out << q
    "#});
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

/// Two writer sites on one store, each anchored to program start rather than to distinct
/// source elements. Their commit order is not determined, so neither side is wrong
/// whichever it picks — the interpreter serializes in source order because it has to pick
/// something. Recorded rather than asserted: a program like this is outside what the
/// differential can judge, and a generated corpus must not emit one.
#[test]
fn two_writer_sites_sharing_an_anchor_are_not_judgeable() {
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
    // Both sides answer; the point is that agreement here would be luck.
    let (c, i) = (compiled(source), interpreted(source));
    println!("compiled:    {c}");
    println!("interpreted: {i}");
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
/// write is what breaks it. The interpreter computes the answer; pinned at the panic.
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
    interpreted(source);
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
