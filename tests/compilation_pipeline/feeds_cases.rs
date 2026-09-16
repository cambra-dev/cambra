//! Feed (`<<`, `<<=`) and define operators on `defer()` channels, plus the
//! multi-arm `if/elif`-with-feeds known-gap test.

use std::time::Duration;

use bit_set::BitSet;
use cambra::ccl::context::{GlobalContext, compile_program, render_errors};
use cambra::interpreter::{ColumnValue, Consumer, Predicate, Tile, Value};
use rstest_log::rstest;

use cambra::ccl::TagMap;
use indoc::indoc;

use crate::helpers::*;

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::feed_list("x = defer(); x <<= [1,2,3]; x", make_int_list(&[1, 2, 3]))]
#[case::feed_scalar_to_defer("x = defer(); x << 1; x", Tile::function(ColumnValue::Units(1), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1]))), Predicate::True, BitSet::new()))]
// An accumulator spelled like the tap its own loop's feed rides. The regression
// these pin: a tap was named `to_<defer>_<n>`, which is a spelling user code can
// write, and the tap and the accumulator share one decision record — so the
// record's last writer won and the accumulator's read resolved to the reply's
// value (`300` here, in release; an internal panic in debug). Taps are now minted
// into the double-underscore namespace user code cannot bind
// (`Name::defer_tap_field`).
#[case::accumulator_spelled_like_its_tap(
r#"to_o_0 := 0
o = defer()
for l in [1, 2, 3]:
    to_o_0 := to_o_0 + l
    o << l * 100
to_o_0"#, Tile::Scalar(ColumnValue::Ints(vec![6])))]
// The same for a tap's `__fire` companion, which shares the record too.
#[case::accumulator_spelled_like_its_taps_fire_gate(
r#"to_o_0__fire := 0
o = defer()
for l in [1, 2, 3]:
    to_o_0__fire := to_o_0__fire + l
    if l > 1:
        o << l * 100
to_o_0__fire"#, Tile::Scalar(ColumnValue::Ints(vec![6])))]
#[case::feed_in_comprehension("x = defer(); [x << i for i in [1,2,3]]; x", make_int_list(&[1, 2, 3]))]
#[case::feed_in_for_loop(
r#"x = defer()
for i in [1,2,3]:
  x << i
x"#, make_int_list(&[1, 2, 3]))]
// Two feeds inside one read-only `with begin():` block: the letrec phase's
// feed-only path emits one `Feed` per feed, each mapping the same loop source, so
// the source lands at two live positions and must be freshened per placement — a
// bare clone trips the `post-letrec-run` id-uniqueness boundary.
#[case::two_feeds_in_readonly_txn_loop(
r#"x = defer()
y = defer()
for i in [1,2,3]:
  with begin():
    x << i
    y << i
x"#, make_int_list(&[1, 2, 3]))]
// Filter-feed inside a defer: `if cond: d << v` in a loop lowers to a
// refined-source channel whose domain carries the bare predicate
// `__elem ▷ source ▷ (λ p → guard)` (the same element form a filtered
// comprehension `[v for p in source if guard]` builds), so planning reifies it
// into an `IterateExtent` + `Restrict` and only guard-passing indices reach
// the channel.
#[case::feed_with_if(
r#"x = defer()
for i in [0,1,2,3]:
  if i // 2 == 0:
    x << i
x"#, make_int_list(&[0, 1]))]
#[case::chained_defers_1(
r#"x = defer()
y = defer()
x <<= y
y <<= [0, 1]
x"#, make_int_list(&[0, 1]))]
#[case::chained_defers_2(
r#"x = defer()
y = defer()
x <<= [0, 1]
y <<= x
y"#, make_int_list(&[0, 1]))]
// Cross-cluster defer reference: `y` and `x` are separated by an
// intervening non-Defer `let some_var = 5`, and `y` depends on `x`
// (via define).  The channelize pass must topologically order the defers
// across the intervening let so `x` is bound before `y`.
#[case(
r#"x = defer()
some_var = 5
y = defer()
x <<= [0, 1]
y <<= x
y"#, make_int_list(&[0, 1]))]
// Symmetric case: x depends on y across the intervening let.
#[case(
r#"x = defer()
some_var = 5
y = defer()
x <<= y
y <<= [0, 1]
x"#, make_int_list(&[0, 1]))]
#[case::two_feeds(
r#"x = defer()
x << 1
x << 2
x"#,
    Tile::function(ColumnValue::positional_union(&[0, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2]))), Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])), BitSet::new()))]
#[case::scalar_and_loop_feeds(
r#"x = defer()
x << 1
for i in [1, 2, 3]:
    x << i
x"#,
    Tile::function(ColumnValue::positional_union(&[0, 1, 1, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1, 2, 3]))), Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])), BitSet::new()))]
// Three feed sites: locks down N-ary union construction beyond N=2.
#[case::three_feeds(
r#"x = defer()
x << 1
x << 2
x << 3
x"#,
    Tile::function(ColumnValue::positional_union(&[0, 1, 2], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))), Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True, Predicate::True])), BitSet::new()))]
// Identical feed values still produce distinct variant tags.
#[case::identical_feeds(
r#"x = defer()
x << 1
x << 1
x"#,
    Tile::function(ColumnValue::positional_union(&[0, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1]))), Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])), BitSet::new()))]
#[case::feed_via_alias(
r#"
x = defer()
y = x
for i in [1,2,3]:
  y << i
y"#, make_int_list(&[1, 2, 3]))]
#[case::feed_via_double_alias(
r#"
x = defer()
y = x
z = y
for i in [1,2,3]:
  z << i
z"#, make_int_list(&[1, 2, 3]))]
#[case::return_defer_from_func(
r#"
def f(n):
  x = defer()
  x
y = f(10)
for i in [1,2,3]:
  y << i
y"#, make_int_list(&[1, 2, 3]))]
#[case::defer_through_identity_funcs(
r#"
def f(x):
  x
x = defer()
for i in [1,2,3]:
  y = f(f(x))
  y << i
x"#, make_int_list(&[1, 2, 3]))]
#[case::alias_inside_loop(
r#"
x = defer()
for i in [1,2,3]:
  y = x
  y << i
x"#, make_int_list(&[1, 2, 3]))]
#[case::feed_internal_and_external(
r#"
def f(n):
  x = defer()
  x << n
  x
y = f(10)
for i in [1,2,3]:
  y << i
y"#, Tile::function(ColumnValue::positional_union(&[0, 1, 1, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 1, 2, 3]))), Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])), BitSet::new()))]
#[case::multiple_func_feeds(
r#"
def f(n):
  x = defer()
  x << n
  x
def g(c):
  c << 100
  c
y = g(f(10))
for i in [1,2,3]:
  y << i
y"#, Tile::function(ColumnValue::positional_union(&[0, 1, 2, 2, 2], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 100, 1, 2, 3]))), Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True, Predicate::True])), BitSet::new()))]
#[case::union_of_complex_defers(
r#"
def f(n):
  x = defer()
  x << n
  x
def g(c):
  c << 100
  c
y = g(f(10))
for i in [1,2,3]:
  y << i
y ++ y"#, Tile::function(ColumnValue::positional_union(&[0, 0, 0, 0, 0, 1, 1, 1, 1, 1], vec![
                ColumnValue::positional_union(&[0, 1, 2, 2, 2], vec![
                        ColumnValue::Units(1),
                        ColumnValue::Units(1),
                        ColumnValue::UInts(vec![0, 1, 2]),
                    ]),
                ColumnValue::positional_union(&[0, 1, 2, 2, 2], vec![
                        ColumnValue::Units(1),
                        ColumnValue::Units(1),
                        ColumnValue::UInts(vec![0, 1, 2]),
                    ]),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 100, 1, 2, 3, 10, 100, 1, 2, 3]))), Predicate::Union(TagMap::from_positional(vec![
            Predicate::Union(TagMap::from_positional(vec![
                Predicate::True,
                Predicate::True,
                Predicate::True,
            ])),
            Predicate::Union(TagMap::from_positional(vec![
                Predicate::True,
                Predicate::True,
                Predicate::True,
            ])),
        ])), BitSet::new()))]
// A feed, a rebind, a second feed: an interleaved body with no accumulator, which
// only the one grammar admits. `x = i` and `x = x + i` are per-iteration immutable
// rebinds, so `x` is `i` at the first feed and `2i` at the second.
#[case(
    r#"
o = defer()
for i in [1, 2, 3]:
    x = i
    o << x
    x = x + i
    o << x * 10
o"#,
    Tile::function(ColumnValue::positional_union(&[0, 0, 0, 1, 1, 1], vec![
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1, 2]),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 20, 40, 60]))), Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])), BitSet::new())
)]
// Pass-by-reference writer that *feeds before it writes*: `o << c` precedes
// `c += 1` in the writer body, inlined per iteration. The Feed-headed spliced
// body left a `unit; unit` tail on the loop spine that `transform_chain` once
// rejected; it now drops the no-op units and reads `x` before each write, so
// the channel latches 0, 1, 2 (the pre-write values) over the three iterations.
#[case::pbr_feed_before_write(
r#"
def fw(c: Mut(Int), o: Feed(Int)):
  o << c
  c += 1
x := 0
out = defer()
for i in [1, 2, 3]:
  fw(x, out)
out"#, make_int_list(&[0, 1, 2]))]
// The same writer with its parameters **swapped**, which is a different typing problem
// rather than a different spelling. The mutable variable is now the second argument, and a call
// is curried, so the applied function's type at that argument is the fresh variable
// `apply` minted — the pass-by-reference contribution has to be read off the head of
// the spine or it is never recorded, leaving `x` claiming its seed and failing the
// invariance check against `Mut(Int)`.
#[case::pbr_mut_var_after_feed(
r#"
def fw(o: Feed(Int), c: Mut(Int)):
  o << c
  c += 1
x := 0
out = defer()
for i in [1, 2, 3]:
  fw(out, x)
out"#, make_int_list(&[0, 1, 2]))]
fn test_feed_and_define_operators(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

/// Multi-arm `if`/`elif` inside a for-loop body, feeding the defer in some
/// arms and not others. Each feeding arm fans out to its own refined-source
/// channel — arm `i`'s source restricted to the element predicate
/// `gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ` (encoding `Case`'s "first matching guard wins"), the arm's
/// value composed on top (`refined_source ≫ (λ p → vᵢ)`) — and the channels are
/// unioned via `++`. Iterations matching no feeding arm contribute nothing
/// (no placeholder), so the two-arm `if g: d << v` shape is just the
/// one-feeding-arm case ([`try_extract_fanout_feed`] /
/// [`synthesize_arm_predicate`] in `channelize`).
///
/// For the program below: `x == 1` fires arm 0 (`10`), `x == 2` fires arm 1
/// (`40`), and `x == 3` matches neither, so the channel is `[10, 40]`.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn multi_arm_if_elif_feeds_fan_out() {
    let code = r#"d = defer()
for x in [1, 2, 3]:
    if x == 1:
        d << x * 10
    elif x == 2:
        d << x * 20
d"#;
    // Two feeding arms → two refined-source channels unioned via `++`: arm 0
    // (`x == 1`) restricts `[1,2,3]` to index {0} yielding `10`; arm 1
    // (`x == 2 ∧ ¬(x == 1)`) restricts to index {1} yielding `40`; `x == 3`
    // matches neither. The `++` gives a tagged-union domain, exactly as the
    // `two_feeds` case above.
    check_tile(
        code,
        Tile::function(
            ColumnValue::positional_union(
                &[0, 1],
                vec![ColumnValue::UInts(vec![0]), ColumnValue::UInts(vec![1])],
            ),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 40]))),
            Predicate::Union(TagMap::from_positional(vec![
                Predicate::True,
                Predicate::True,
            ])),
            BitSet::new(),
        ),
    );
}

/// An `if/else` where **both arms feed** a pure-feed loop (no accumulator). The
/// `else` is an ordinary trailing arm (guard `true`, first-match predicate
/// `¬(i < 2)`), so it fans out as its own refined-source channel — `channelize`
/// refines the *source* domain per arm (a shared `Int` codomain), rather than
/// leaving the guard on a `Unit` gated lift. As a function: 0 ↦ 0, 1 ↦ 1,
/// 2 ↦ 100, 3 ↦ 100.
#[rstest]
#[timeout(Duration::from_secs(10))]
fn if_else_both_feed_fan_out() {
    let code = r#"o = defer()
for i in [0, 1, 2, 3]:
    if i < 2:
        o << i
    else:
        o << 100
o"#;
    check_tile(
        code,
        Tile::function(
            ColumnValue::positional_union(
                &[0, 0, 1, 1],
                vec![
                    ColumnValue::UInts(vec![0, 1]),
                    ColumnValue::UInts(vec![2, 3]),
                ],
            ),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 1, 100, 100]))),
            Predicate::Union(TagMap::from_positional(vec![
                Predicate::True,
                Predicate::True,
            ])),
            BitSet::new(),
        ),
    );
}

/// A **comprehension over a feed channel**, which applies the channel: the channel's read
/// view is the data function the comprehension's source position holds.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::bare("sum([x for x in out])", 3)]
#[case::mapped("sum([x * 2 for x in out])", 6)]
fn a_comprehension_reads_a_feed_channel(#[case] read: &str, #[case] expected: i64) {
    check_scalar(
        &format!(
            indoc! {r"
                out = defer()
                for v in [1, 2]:
                    with begin():
                        out << v
                {}
            "},
            read
        ),
        Value::Int(expected),
    );
}

/// A **filtered** comprehension over a channel, which the argument check admits and
/// `channelize` then stops. The filter refines the comprehension's source domain and that
/// domain is the channel's, so a `ChanDom` sits inside the refinement's predicate — where
/// channelize's erasure never reaches, because `Type::walk_children_mut` visits a
/// `Type::Refinement`'s base and not its predicate. The post-channelize check then reports
/// the residue at `__elem`.
///
/// The unfiltered reads beside it place it: what the filter meets is the channel domain
/// surviving into a predicate, not anything about applying a channel.
#[test]
fn a_filtered_comprehension_over_a_feed_channel_fails_at_channelize() {
    check_compile_error(
        indoc! {r"
            out = defer()
            for v in [1, 2]:
                with begin():
                    out << v
            sum([x for x in out if x > 1])
        "},
        "channel domain chan(out) survived channelize at `__elem`",
    );
}

/// The same read with **no transaction** around the contribution. `with begin():` decides
/// how the channel is fed, not how it is read, so the comprehension applies the same read
/// view either way.
#[test]
fn a_comprehension_reads_a_feed_channel_fed_outside_a_transaction() {
    check_scalar(
        indoc! {r"
            out = defer()
            for v in [1, 2]:
                out << v
            sum([x for x in out])
        "},
        Value::Int(3),
    );
}

/// A feed, an ordinary statement, a second feed: an interleaved loop body with no
/// accumulator. Every position lowers through [`lower_for_body_stmt`], so the first
/// feed is an effect sequenced before the rest rather than a non-terminal statement to
/// reject. Each program here is a lowering error on the base, in the `<<` spelling and
/// in the `yield` spelling alike.
#[rstest]
#[timeout(Duration::from_secs(10))]
// One deferred collection.
#[case(
    indoc! {r#"
        o = defer()
        for i in [1, 2]:
            o << i
            t = i * 10
            o << t
        sum(o)
    "#},
    Value::Int(33)
)]
// Two, so the statement between the feeds separates a feed to each. The reads are
// weighted apart, so a fan-out routing an arm's values into the wrong one fails here.
#[case(
    indoc! {r#"
        a = defer()
        b = defer()
        for i in [1, 2]:
            a << i
            t = i * 10
            b << t
        sum(a) * 100 + sum(b)
    "#},
    Value::Int(330)
)]
// The `yield` spelling of the first, inside a generator function.
#[case(
    indoc! {r#"
        def g(xs):
            for i in xs:
                yield i
                t = i * 10
                yield t
        sum(g([1, 2]))
    "#},
    Value::Int(33)
)]
// Two `yield`s in one iteration with nothing between them.
#[case(
    indoc! {r#"
        def g(xs):
            for i in xs:
                yield i
                yield i * 10
        sum(g([1, 2]))
    "#},
    Value::Int(33)
)]
fn interleaved_feeds_in_a_loop_body(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// What a for-loop body's non-final position keeps out. A binding and a feed are the
/// whole of what a non-final statement may be (`docs/chl-spec.md`, "4. Statement
/// semantics"): an `if`, a `match` and a nested `for` are the body's value and stay
/// last, and a mutable variable is not introduced inside a body at any spelling.
///
/// The three conditional forms compile past lowering without this rejection and fail
/// deeper — an `if` and a nested `for` on the post-channelize typecheck, a `match` on
/// `PartialFeedCaseUnsupported`, which names the wrong cause. `channelize`'s fan-out
/// dispatches on a bare `Case` at the lambda body, and one sequenced under an
/// `ExprStmt` is not one.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    indoc! {r#"
        o = defer()
        for i in [1, 2, 3]:
            if i > 1:
                o << i
            o << 100
        sum(o)
    "#},
    "only assignments, function definitions, `<<` feeds and `yield`"
)]
#[case(
    indoc! {r#"
        o = defer()
        for m in [`a(2), `b(3)]:
            match m:
                case `a(n):
                    o << n
                case `b(k):
                    o << k
            o << 100
        sum(o)
    "#},
    "only assignments, function definitions, `<<` feeds and `yield`"
)]
#[case(
    indoc! {r#"
        o = defer()
        for i in [1, 2]:
            for j in [10, 20]:
                o << i * j
            o << i
        sum(o)
    "#},
    "only assignments, function definitions, `<<` feeds and `yield`"
)]
// A bare call, and a `return`: neither binds nor feeds.
#[case(
    indoc! {r#"
        def bump(x):
            x + 1
        o = defer()
        for i in [1, 2]:
            bump(i)
            o << i
        sum(o)
    "#},
    "only assignments, function definitions, `<<` feeds and `yield`"
)]
#[case(
    indoc! {r#"
        o = defer()
        for i in [1, 2]:
            return i
            o << i
        sum(o)
    "#},
    "only assignments, function definitions, `<<` feeds and `yield`"
)]
// A mutable variable introduced in the body, at all three spellings — one rejection,
// because whether the introduction carries an annotation says nothing about which
// construct it is.
#[case(
    indoc! {r#"
        o = defer()
        for i in [1, 2]:
            t := i * 2
            o << i
        sum(o)
    "#},
    "`t` is a mutable variable introduced inside a for-loop body"
)]
#[case(
    indoc! {r#"
        o = defer()
        for i in [1, 2]:
            t: Mut(Int) := i * 2
            o << i
        sum(o)
    "#},
    "`t` is a mutable variable introduced inside a for-loop body"
)]
#[case(
    indoc! {r#"
        o = defer()
        for i in [1, 2]:
            t: Mut(Int) = i * 2
            o << i
        sum(o)
    "#},
    "`t` is a mutable variable introduced inside a for-loop body"
)]
fn a_non_final_loop_body_statement_is_a_binding_or_a_feed(
    #[case] code: &str,
    #[case] needle: &str,
) {
    check_compile_error(code, needle);
}

/// The last statement is the body's value, so the forms that are not one are rejected
/// there by the terminal's own message. Reached only last: a non-final position admits
/// a narrower set, which the rejection above names.
#[test]
fn a_loop_body_ends_in_a_value() {
    check_compile_error(
        indoc! {r#"
            o = defer()
            for i in [1, 2]:
                o << i
                return i
            sum(o)
        "#},
        "for-loop body must end in a yield, `<<` feed, nested for, if-guard, or match",
    );
}

/// `<<=` sets a channel's read view outright, so its RHS must be a collection
/// (a `Fun`). A scalar RHS is rejected by typing — the discipline that keeps
/// every feed history a genuine collection `domain ⤇ value` (scalar values belong
/// in a plain `let` binding or a `:=` mutable variable, not a feed channel).
#[rstest]
#[timeout(Duration::from_secs(1))]
fn scalar_define_into_defer_is_rejected() {
    let code = "x = defer()\nx <<= 1\nx";
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let result = compile_program(&mut ctx, code, consumer);
    assert!(
        result.is_err(),
        "a scalar defined into a feed channel must be a type error"
    );
}

/// Type errors in defer programs are reported against the *user's* program
/// shape: inference now runs before `channelize`, so the rendered
/// message must not leak channelize artifacts (floated parameters, `__to_<defer>`
/// record fields, channel unions, scope-out bindings).
#[rstest]
#[timeout(Duration::from_secs(1))]
fn defer_type_errors_render_against_user_shape() {
    let code = r#"x = defer()
x << 1
x << "s"
x"#;
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let errs = match compile_program(&mut ctx, code, consumer) {
        Ok(_) => panic!("an Int and a String fed into one defer must be a type error"),
        Err(e) => e,
    };
    let rendered = render_errors(&errs, "<defer-error-shape-test>", code);
    assert!(
        rendered.contains("Int") && rendered.contains("String"),
        "expected the conflicting element types in the message, got:\n{rendered}"
    );
    for artifact in [
        "__floated",
        "to_x",
        "__scope_out",
        "⊎",
        "Copair",
        "DisjointJoin",
    ] {
        assert!(
            !rendered.contains(artifact),
            "channelize artifact `{artifact}` leaked into a user-facing type error:\n{rendered}"
        );
    }
}

/// Assert `code` fails to compile with a rendered error containing `needle`.
fn expect_feed_error(code: &str, needle: &str) {
    let mut ctx = GlobalContext::default();
    let errs = match compile_program(&mut ctx, code, Box::new(|| {})) {
        Ok(_) => panic!("expected a compile error containing {needle:?}; program compiled"),
        Err(e) => e,
    };
    let rendered = render_errors(&errs, "<feed-reject-test>", code);
    assert!(
        rendered.contains(needle),
        "expected error to contain {needle:?}; got:\n{rendered}"
    );
}

/// Two `<<=` defines for one defer channel: a channel's collection is set once, so a
/// second define is rejected (`DeferError::MultipleDefinitions`).
#[test]
fn multiple_defines_rejected() {
    expect_feed_error(
        "x = defer()\nx <<= [1]\nx <<= [2]\nx",
        "multiple definitions",
    );
}

/// Mixing a `<<` feed and a `<<=` define on one defer is rejected — a channel is
/// either fed incrementally or set wholesale, not both
/// (`DeferError::FeedsAndDefinesMixed`).
#[test]
fn feeds_and_define_mixed_rejected() {
    expect_feed_error(
        "x = defer()\nx << 1\nx <<= [2]\nx",
        "both feeds and a define",
    );
}

/// A bare `defer()` that is never bound to a name (so nothing feeds or defines
/// it) leaves an unbound handle — rejected (`DeferError::UnboundDeferHandle`).
#[test]
fn unbound_defer_handle_rejected() {
    expect_feed_error("defer()", "unbound defer handle");
}
