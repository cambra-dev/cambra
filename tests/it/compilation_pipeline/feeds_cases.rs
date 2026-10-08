//! Feed (`<<`, `<<=`) and define operators on declared `Feed(_)` channels, plus the
//! multi-arm `if/elif`-with-feeds known-gap test.

use std::time::Duration;

use bit_set::BitSet;
use cambra::ccl::context::{GlobalContext, compile_program, render_errors};
use cambra::ccl::load::LoadedProgram;
use cambra::interpreter::{ColumnValue, Consumer, Predicate, Tile, Value};
use rstest_log::rstest;

use cambra::ccl::TagMap;
use indoc::indoc;

use super::helpers::*;

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::feed_list("x: Feed(_); x <<= [1,2,3]; x", make_int_list(&[1, 2, 3]))]
#[case::a_scalar_feed("x: Feed(_); x << 1; x", Tile::data_function(ColumnValue::Units(1), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1]))), Predicate::True, BitSet::new()))]
// An accumulator spelled like the tap its own loop's feed rides. The regression
// these pin: a tap was named `to_<defer>_<n>`, which is a spelling user code can
// write, and the tap and the accumulator share one decision record — so the
// record's last writer won and the accumulator's read resolved to the reply's
// value (`300` here, in release; an internal panic in debug). Taps are now minted
// into the double-underscore namespace user code cannot bind
// (`Name::defer_tap_field`).
#[case::accumulator_spelled_like_its_tap(
r#"to_o_0 := 0
o: Feed(_)
for l in [1, 2, 3]:
    to_o_0 := to_o_0 + l
    o << l * 100
to_o_0"#, Tile::Scalar(ColumnValue::Ints(vec![6])))]
// The same for a tap's `__fire` companion, which shares the record too.
#[case::accumulator_spelled_like_its_taps_fire_gate(
r#"to_o_0__fire := 0
o: Feed(_)
for l in [1, 2, 3]:
    to_o_0__fire := to_o_0__fire + l
    if l > 1:
        o << l * 100
to_o_0__fire"#, Tile::Scalar(ColumnValue::Ints(vec![6])))]
#[case::feed_in_comprehension("x: Feed(_); [x << i for i in [1,2,3]]; x", make_int_list(&[1, 2, 3]))]
#[case::feed_in_for_loop(
r#"x: Feed(_)
for i in [1,2,3]:
  x << i
x"#, make_int_list(&[1, 2, 3]))]
// Two feeds inside one read-only `with begin():` block: the letrec phase's
// feed-only path emits one `Feed` per feed, each mapping the same loop source, so
// the source lands at two live positions and must be freshened per placement — a
// bare clone trips the `post-letrec-run` id-uniqueness boundary.
#[case::two_feeds_in_readonly_txn_loop(
r#"x: Feed(_)
y: Feed(_)
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
r#"x: Feed(_)
for i in [0,1,2,3]:
  if i // 2 == 0:
    x << i
x"#, make_int_list(&[0, 1]))]
#[case::chained_feeds_1(
r#"x: Feed(_)
y: Feed(_)
x <<= y
y <<= [0, 1]
x"#, make_int_list(&[0, 1]))]
#[case::chained_feeds_2(
r#"x: Feed(_)
y: Feed(_)
x <<= [0, 1]
y <<= x
y"#, make_int_list(&[0, 1]))]
// Cross-cluster defer reference: `y` and `x` are separated by an
// intervening non-Defer `let some_var = 5`, and `y` depends on `x`
// (via define).  The channelize pass must topologically order the defers
// across the intervening let so `x` is bound before `y`.
#[case(
r#"x: Feed(_)
some_var = 5
y: Feed(_)
x <<= [0, 1]
y <<= x
y"#, make_int_list(&[0, 1]))]
// Symmetric case: x depends on y across the intervening let.
#[case(
r#"x: Feed(_)
some_var = 5
y: Feed(_)
x <<= y
y <<= [0, 1]
x"#, make_int_list(&[0, 1]))]
#[case::two_feeds(
r#"x: Feed(_)
x << 1
x << 2
x"#,
    Tile::data_function(ColumnValue::positional_union(&[0, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2]))), Predicate::over_every_tag(TagMap::from_positional(vec![Predicate::True, Predicate::True])), BitSet::new()))]
#[case::scalar_and_loop_feeds(
r#"x: Feed(_)
x << 1
for i in [1, 2, 3]:
    x << i
x"#,
    Tile::data_function(ColumnValue::positional_union(&[0, 1, 1, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1, 2, 3]))), Predicate::over_every_tag(TagMap::from_positional(vec![Predicate::True, Predicate::True])), BitSet::new()))]
// Three feed sites: locks down N-ary union construction beyond N=2.
#[case::three_feeds(
r#"x: Feed(_)
x << 1
x << 2
x << 3
x"#,
    Tile::data_function(ColumnValue::positional_union(&[0, 1, 2], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))), Predicate::over_every_tag(TagMap::from_positional(vec![Predicate::True, Predicate::True, Predicate::True])), BitSet::new()))]
// Identical feed values still produce distinct variant tags.
#[case::identical_feeds(
r#"x: Feed(_)
x << 1
x << 1
x"#,
    Tile::data_function(ColumnValue::positional_union(&[0, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1]))), Predicate::over_every_tag(TagMap::from_positional(vec![Predicate::True, Predicate::True])), BitSet::new()))]
#[case::feed_via_alias(
r#"
x: Feed(_)
y = x
for i in [1,2,3]:
  y << i
y"#, make_int_list(&[1, 2, 3]))]
#[case::feed_via_double_alias(
r#"
x: Feed(_)
y = x
z = y
for i in [1,2,3]:
  z << i
z"#, make_int_list(&[1, 2, 3]))]
#[case::return_defer_from_func(
r#"
def f(n):
  x: Feed(_)
  x
y = f(10)
for i in [1,2,3]:
  y << i
y"#, make_int_list(&[1, 2, 3]))]
#[case::defer_through_identity_funcs(
r#"
def f(x):
  x
x: Feed(_)
for i in [1,2,3]:
  y = f(f(x))
  y << i
x"#, make_int_list(&[1, 2, 3]))]
#[case::alias_inside_loop(
r#"
x: Feed(_)
for i in [1,2,3]:
  y = x
  y << i
x"#, make_int_list(&[1, 2, 3]))]
#[case::feed_internal_and_external(
r#"
def f(n):
  x: Feed(_)
  x << n
  x
y = f(10)
for i in [1,2,3]:
  y << i
y"#, Tile::data_function(ColumnValue::positional_union(&[0, 1, 1, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 1, 2, 3]))), Predicate::over_every_tag(TagMap::from_positional(vec![Predicate::True, Predicate::True])), BitSet::new()))]
#[case::multiple_func_feeds(
r#"
def f(n):
  x: Feed(_)
  x << n
  x
def g(c):
  c << 100
  c
y = g(f(10))
for i in [1,2,3]:
  y << i
y"#, Tile::data_function(ColumnValue::positional_union(&[0, 1, 2, 2, 2], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 100, 1, 2, 3]))), Predicate::over_every_tag(TagMap::from_positional(vec![Predicate::True, Predicate::True, Predicate::True])), BitSet::new()))]
#[case::union_of_complex_defers(
r#"
def f(n):
  x: Feed(_)
  x << n
  x
def g(c):
  c << 100
  c
y = g(f(10))
for i in [1,2,3]:
  y << i
y ++ y"#, Tile::data_function(ColumnValue::positional_union(&[0, 0, 0, 0, 0, 1, 1, 1, 1, 1], vec![
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
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 100, 1, 2, 3, 10, 100, 1, 2, 3]))), Predicate::over_every_tag(TagMap::from_positional(vec![
            Predicate::over_every_tag(TagMap::from_positional(vec![
                Predicate::True,
                Predicate::True,
                Predicate::True,
            ])),
            Predicate::over_every_tag(TagMap::from_positional(vec![
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
o: Feed(_)
for i in [1, 2, 3]:
    x = i
    o << x
    x = x + i
    o << x * 10
o"#,
    Tile::data_function(ColumnValue::positional_union(&[0, 0, 0, 1, 1, 1], vec![
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1, 2]),
            ]), Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 20, 40, 60]))), Predicate::over_every_tag(TagMap::from_positional(vec![Predicate::True, Predicate::True])), BitSet::new())
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
out: Feed(_)
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
out: Feed(_)
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
    let code = r#"d: Feed(_)
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
        Tile::data_function(
            ColumnValue::positional_union(
                &[0, 1],
                vec![ColumnValue::UInts(vec![0]), ColumnValue::UInts(vec![1])],
            ),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 40]))),
            Predicate::over_every_tag(TagMap::from_positional(vec![
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
    let code = r#"o: Feed(_)
for i in [0, 1, 2, 3]:
    if i < 2:
        o << i
    else:
        o << 100
o"#;
    check_tile(
        code,
        Tile::data_function(
            ColumnValue::positional_union(
                &[0, 0, 1, 1],
                vec![
                    ColumnValue::UInts(vec![0, 1]),
                    ColumnValue::UInts(vec![2, 3]),
                ],
            ),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 1, 100, 100]))),
            Predicate::over_every_tag(TagMap::from_positional(vec![
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
                out: Feed(_)
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

/// A **filtered** comprehension over a channel. The filter refines the comprehension's
/// source domain and that domain is the channel's, so a `ChanDom` sits inside the
/// refinement's predicate — which `Type::walk_children_mut` does not reach, visiting a
/// `Type::Refinement`'s base and not its predicate. `erase_chan_domains_in_predicates`
/// reaches it, gated on a read-only scan so a program with nothing to erase keeps its
/// node ids.
///
/// Three shapes are pinned. The first filters on a value the channel carries. The second
/// names a `let` bound outside the loop, which the erasure has to close over the same way
/// the main tree's substitution does. The third filters a read that is itself filtered, so
/// the refinement the eraser enters sits on an already-refined channel domain.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::literal("sum([x for x in out if x > 1])", 2)]
#[case::names_an_outer_let("sum([x for x in out if x > n])", 2)]
#[case::over_a_filtered_read("sum([x for x in [y for y in out if y > 0] if x > 1])", 2)]
fn a_filtered_comprehension_reads_a_feed_channel(#[case] read: &str, #[case] expected: i64) {
    let feed = indoc! {r"
        n = 1
        out: Feed(_)
        for v in [1, 2]:
            with begin():
                out << v
    "};
    check_scalar(&format!("{feed}{read}"), Value::Int(expected));
}

/// The same filtered read **bound to a name** before it is consumed. The binding's
/// declared type is a slot `walk_children_mut` does not reach either, so the erasure
/// covers the binder slots alongside a node's own type and its annotation; without that
/// the channel domain survives in the binding's predicate and channelize's own
/// `assert_no_type_residue` reports it.
#[test]
fn a_let_bound_filtered_comprehension_reads_a_feed_channel() {
    check_scalar(
        indoc! {r"
            out: Feed(_)
            for v in [1, 2]:
                with begin():
                    out << v
            c = [x for x in out if x > 1]
            sum(c)
        "},
        Value::Int(2),
    );
}

/// The same read with **no transaction** around the contribution. `with begin():` decides
/// how the channel is fed, not how it is read, so the comprehension applies the same read
/// view either way.
#[test]
fn a_comprehension_reads_a_feed_channel_fed_outside_a_transaction() {
    check_scalar(
        indoc! {r"
            out: Feed(_)
            for v in [1, 2]:
                out << v
            sum([x for x in out])
        "},
        Value::Int(3),
    );
}

/// Two deferred collections fed from **complementary arms** of one conditional, in a
/// loop with no accumulator. The `Case` fans out once per defer: each pass extracts its
/// own arms into refined-source channels and leaves the sibling's arms standing
/// (`residual_after_fanout` in `channelize`), so an arm feeding the other defer is a
/// non-feeding arm for this one.
///
/// Each channel is read on its own, so the pinned domain is the source restriction the
/// arm earned — `good` takes index 0 and `bad` index 1 in the `match`, and the reverse
/// in the `if`. A fan-out routing an arm's values into the sibling's channel fails here,
/// which a symmetric read of the two would not.
///
/// Both spellings are listed because they reach the fan-out by different routes: a
/// `match`'s arms carry patterns and an `if`'s carry guards. The loop carries no
/// accumulator, which is what leaves the per-arm channel as the only representation of
/// this feed (`src/ccl/design/mutability.md`, "Value-selecting `Case` and conditional
/// induction writes (partially implemented)").
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::match_good("good", &[0u64], &[2i64])]
#[case::match_bad("bad", &[1], &[3])]
fn two_defers_fed_from_complementary_match_arms(
    #[case] read: &str,
    #[case] domain: &[u64],
    #[case] codomain: &[i64],
) {
    let code = format!(
        indoc! {r#"
            good: Feed(_)
            bad: Feed(_)
            for m in [`a(2), `b(3)]:
                match m:
                    case `a(n):
                        good << n
                    case `b(k):
                        bad << k
            {}
        "#},
        read
    );
    check_tile(
        &code,
        Tile::data_function(
            ColumnValue::UInts(domain.to_vec()),
            Box::new(Tile::Scalar(ColumnValue::Ints(codomain.to_vec()))),
            Predicate::True,
            BitSet::new(),
        ),
    );
}

/// The `if`/`else` spelling of [`two_defers_fed_from_complementary_match_arms`].
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::if_good("good", &[1u64], &[2i64])]
#[case::if_bad("bad", &[0], &[1])]
fn two_defers_fed_from_complementary_if_arms(
    #[case] read: &str,
    #[case] domain: &[u64],
    #[case] codomain: &[i64],
) {
    let code = format!(
        indoc! {r#"
            good: Feed(_)
            bad: Feed(_)
            for i in [1, 2]:
                if i > 1:
                    good << i
                else:
                    bad << i
            {}
        "#},
        read
    );
    check_tile(
        &code,
        Tile::data_function(
            ColumnValue::UInts(domain.to_vec()),
            Box::new(Tile::Scalar(ColumnValue::Ints(codomain.to_vec()))),
            Predicate::True,
            BitSet::new(),
        ),
    );
}

/// A `case _:` default arm feeding the second defer. `tag_case_to_guard_case` gives a
/// default arm the trailing `true` guard rather than a `variant_is` test, so its channel
/// covers the complement of every named arm — two of the three elements here — and the
/// residual keeps the default arm for the named arm's pass to leave alone.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::named_arm("a", &[0u64], &[1i64])]
#[case::default_arm("b", &[1, 2], &[7, 7])]
fn a_default_arm_feeds_its_own_defer(
    #[case] read: &str,
    #[case] domain: &[u64],
    #[case] codomain: &[i64],
) {
    let code = format!(
        indoc! {r#"
            a: Feed(_)
            b: Feed(_)
            for m in [`x(1), `y(2), `z(4)]:
                match m:
                    case `x(n):
                        a << n
                    case _:
                        b << 7
            {}
        "#},
        read
    );
    check_tile(
        &code,
        Tile::data_function(
            ColumnValue::UInts(domain.to_vec()),
            Box::new(Tile::Scalar(ColumnValue::Ints(codomain.to_vec()))),
            Predicate::True,
            BitSet::new(),
        ),
    );
}

/// Three shapes the per-defer pass admits once it admits two complementary arms. Each
/// read is weighted apart from the others, so a value landing in the wrong channel
/// changes the answer.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Three defers off one conditional: the pass runs once per defer, and the third finds
// the first two's arms already `Unit` in the residual.
#[case(
    indoc! {r#"
        a: Feed(_)
        b: Feed(_)
        c: Feed(_)
        for i in [1, 2, 3]:
            if i == 1:
                a << i
            elif i == 2:
                b << i * 10
            else:
                c << i * 100
        sum(a) * 10000 + sum(b) * 100 + sum(c)
    "#},
    Value::Int(12300)
)]
// One defer fed from non-contiguous arms, with the sibling's arm between them: its two
// channels union, and the arm in between keeps its guard in their predicates.
#[case(
    indoc! {r#"
        a: Feed(_)
        b: Feed(_)
        for i in [1, 2, 3]:
            if i == 1:
                a << i
            elif i == 2:
                b << i
            else:
                a << i
        sum(a) * 10 + sum(b)
    "#},
    Value::Int(42)
)]
// A read of the first defer between the loop and the program's value, which puts the
// two defers in separate clusters.
#[case(
    indoc! {r#"
        a: Feed(_)
        b: Feed(_)
        for i in [1, 2]:
            if i > 1:
                a << i
            else:
                b << i
        t = sum(a)
        t * 10 + sum(b)
    "#},
    Value::Int(21)
)]
fn more_defers_off_one_conditional(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
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
        o: Feed(_)
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
        a: Feed(_)
        b: Feed(_)
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
        o: Feed(_)
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
        o: Feed(_)
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
        o: Feed(_)
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
        o: Feed(_)
        for i in [1, 2]:
            bump(i)
            o << i
        sum(o)
    "#},
    "only assignments, function definitions, `<<` feeds and `yield`"
)]
#[case(
    indoc! {r#"
        o: Feed(_)
        for i in [1, 2]:
            return i
            o << i
        sum(o)
    "#},
    "only assignments, function definitions, `<<` feeds and `yield`"
)]
// A mutable variable introduced in a **generator** body, at both `:=` spellings — one
// rejection, because whether the introduction carries an annotation says nothing about
// which construct it is. A mutation loop's body carries one; the yield path lowers its
// statements without a recurrence, so this one has nothing to sequence it.
#[case(
    indoc! {r#"
        o: Feed(_)
        for i in [1, 2]:
            t := i * 2
            o << i
        sum(o)
    "#},
    "`t` is a mutable variable introduced inside a for-loop body"
)]
#[case(
    indoc! {r#"
        o: Feed(_)
        for i in [1, 2]:
            t: Mut(Int) := i * 2
            o << i
        sum(o)
    "#},
    "`t` is a mutable variable introduced inside a for-loop body"
)]
// The `=` spelling is rejected for its **operator** instead, which is the answer
// wherever it is written: a mutable variable is introduced solely with `:=`.
#[case(
    indoc! {r#"
        o: Feed(_)
        for i in [1, 2]:
            t: Mut(Int) = i * 2
            o << i
        sum(o)
    "#},
    "use `:=` instead"
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
            o: Feed(_)
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
    let code = "x: Feed(_)\nx <<= 1\nx";
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let result = compile_program(&mut ctx, &LoadedProgram::test(code), consumer);
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
    let code = r#"x: Feed(_)
x << 1
x << "s"
x"#;
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let loaded = LoadedProgram::from_text("<defer-error-shape-test>", code);
    let errs = match compile_program(&mut ctx, &loaded, consumer) {
        Ok(_) => panic!("an Int and a String fed into one defer must be a type error"),
        Err(e) => e,
    };
    let rendered = render_errors(&errs, loaded.sources());
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
    let loaded = LoadedProgram::from_text("<feed-reject-test>", code);
    let errs = match compile_program(&mut ctx, &loaded, Box::new(|| {})) {
        Ok(_) => panic!("expected a compile error containing {needle:?}; program compiled"),
        Err(e) => e,
    };
    let rendered = render_errors(&errs, loaded.sources());
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
        "x: Feed(_)\nx <<= [1]\nx <<= [2]\nx",
        "multiple definitions",
    );
}

/// Mixing a `<<` feed and a `<<=` define on one defer is rejected — a channel is
/// either fed incrementally or set wholesale, not both
/// (`DeferError::FeedsAndDefinesMixed`).
#[test]
fn feeds_and_define_mixed_rejected() {
    expect_feed_error(
        "x: Feed(_)\nx << 1\nx <<= [2]\nx",
        "both feeds and a define",
    );
}

/// A generator whose feed both feeds and defines.
const FEEDS_AND_DEFINES: &str = indoc! {r#"
    def g(n):
        x: Feed(Int)
        x << n
        x <<= [2]
        x
"#};

/// A generator whose feed defines twice.
const DEFINES_TWICE: &str = indoc! {r#"
    def g(n):
        x: Feed(Int)
        x <<= [n]
        x <<= [2]
        x
"#};

/// A generator whose feed neither feeds nor defines.
const NEITHER: &str = indoc! {r#"
    def g(n):
        x: Feed(Int)
        x
"#};

/// An error in a generator's feed is the program's wherever the generator is
/// called. A call in a filter or a group-by key leaves the block in a refinement predicate,
/// and channelize reports its error as it reports one in the tree.
#[rstest]
#[case::mixed_in_the_tree(FEEDS_AND_DEFINES, "max(g(1))", "both feeds and a define")]
#[case::mixed_in_a_filter(
    FEEDS_AND_DEFINES,
    "sum([q for q in [1, 2] if max(g(q)) > 0])",
    "both feeds and a define"
)]
#[case::mixed_in_a_key(
    FEEDS_AND_DEFINES,
    r"sum([sum(h) for h in groupby([1, 2], \e -> max(g(e)))])",
    "both feeds and a define"
)]
#[case::defined_twice_in_a_filter(
    DEFINES_TWICE,
    "sum([q for q in [1, 2] if max(g(q)) > 0])",
    "multiple definitions"
)]
#[case::neither_in_a_filter(
    NEITHER,
    "sum([q for q in [1, 2] if max(g(q)) > 0])",
    "has no feed or define"
)]
fn a_defer_error_in_a_predicate_is_a_compile_error(
    #[case] generator: &str,
    #[case] call: &str,
    #[case] needle: &str,
) {
    let code = format!("{generator}\n{call}\n");
    expect_feed_error(&code, needle);
    expect_feed_error(&code, "feed error");
}

/// Feeding something that is not a feed is a type error (`docs/chl-spec.md`, "3.7 Feed
/// operator `<<`"): a collection bound by `=`, and one passed to a function that feeds its
/// parameter, annotated or not. So is a binding of a feed type whose value is a collection,
/// fed or not.
#[rstest]
#[case::a_collection(
    "x = [1, 2, 3]\nx << 4\nsum(x)\n",
    "feed target of feed(x, 4) must be a feed handle (a feed handle is required here, but the \
     value is not one)"
)]
#[case::a_collection_annotated_as_a_feed(
    "x: Feed(Int) = [1, 2, 3]\nx << 4\nsum(x)\n",
    "annotated as Feed(Int), but inferred as Array(3, Int)"
)]
#[case::a_feed_binding_of_a_collection_never_fed(
    "x: Feed(Int) = [1, 2, 3]\nsum(x)\n",
    "annotated as Feed(Int), but inferred as Array(3, Int)"
)]
#[case::a_collection_passed_to_a_feed_parameter(
    "def g(o: Feed(Int)):\n    o << 5\ng([1, 2])\n1\n",
    "a feed handle is required here, but the value is not one"
)]
#[case::a_collection_passed_to_an_unannotated_parameter(
    "def g(o, x):\n    o << x\ng([1], 2)\n1\n",
    "a feed handle is required here, but the value is not one"
)]
fn feeding_what_is_not_a_feed_is_a_type_error(#[case] code: &str, #[case] needle: &str) {
    check_compile_error(code, needle);
    check_compile_error(code, "type inference error");
}

/// A feed taken out of a tuple that holds a computed value does not reach its declaration, so
/// feeding it is refused rather than dropped (`docs/chl-spec.md`, "A deferred collection inside
/// a data structure \[Open\]").
#[test]
fn feeding_a_feed_out_of_a_data_structure_is_refused() {
    check_compile_error(
        "xs = [1, 2]\nout: Feed(_)\nout << 1\nt = (sum(xs), out)\na, o = t\no << a\nsum(out)\n",
        "this feeds a feed taken out of a data structure",
    );
}

/// TODO: Support refined writes to vars used with feeds.
#[test]
fn refined_write_used_with_feed() {
    check_compile_error(
        indoc! {r#"
x: Mut({Int where _ >= 0}) := 0
o: Feed(_)
for p in [1,2,3]:
    o << x
    x := x ^+ 1
    o << x
x
        "#},
        "a feed whose rows depend on a mutable variable its loop writes is not supported yet",
    )
}

/// TODO: Support mut reads in refined ops used with feeds.
#[test]
fn refined_read_used_with_feed() {
    check_compile_error(
        indoc! {r#"
x := 0
o: Feed(_)
for p in [1, 2, 3]:
    y = x ^+ 1
    o << y
    x += 1
o
        "#},
        "a feed whose rows depend on a mutable variable its loop writes is not supported yet",
    )
}

#[test]
fn let_binding_into_feed() {
    check_scalar(
        indoc! {r#"
out: Feed(_)
x := 0
for i in [1, 2, 3]:
  if i > 1:
    a = i + 1
    out << a
    x += a
"#},
        Value::Unit,
    )
}

/// A loop that feeds `events` and counts, below a reader of `events`.
///
/// Channelize binds the channel above its first reader, `total`, which sits
/// above the loop's `letrec __hist`, so the channel
/// `__hist ≫ … ≫ .__to_events_0 ≫ …` refers to `__hist` outside its scope and
/// op conversion rejects it. With `total` bound below the loop it compiles.
/// Once channelize places the channel below the loop history it captures, this
/// returns `9` and the `should_panic` comes off.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Pinned on the failure rather than deferred: an `#[ignore]` reports the same green whether
// the gap closed, regressed, or went away, and nothing runs ignored tests here.
#[should_panic(expected = "unrecognised Var(__hist) in λ-free CCL")]
fn loop_feeds_a_channel_read_above_it() {
    check_scalar(
        indoc! {"
            events: Feed(_)
            total = sum([e for e in events])
            fed := 0
            for x in [1, 2, 3]:
                events << x
                fed += 1
            total + fed
        "},
        Value::Int(9),
    );
}

/// A loop that feeds `events` and adds `total`, the sum of `events`, on each
/// iteration. The program has no cycle: a read of a feed is the whole
/// collection (`docs/chl-spec.md`, "8.4 Feeds are the second form of
/// mutability"), and effects are ordered only by data dependencies
/// (`docs/chl-spec.md`, "Evaluation order is unspecified"). The values fed to
/// `events` are the `x`s, which read neither `fed` nor `total`, so `total` is
/// `6`, `fed` is `3 × 6 = 18`, and the program returns `24`.
///
/// Channelize places this channel as it does in
/// `loop_feeds_a_channel_read_above_it`, and op conversion rejects it the same
/// way. Moving `total` below the loop does not apply here, because the loop
/// reads `total`.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Pinned on the failure, as `loop_feeds_a_channel_read_above_it` is.
#[should_panic(expected = "unrecognised Var(__hist) in λ-free CCL")]
fn loop_adds_the_total_of_its_own_feed() {
    check_scalar(
        indoc! {"
            events: Feed(_)
            total = sum([e for e in events])
            fed := 0
            for x in [1, 2, 3]:
                events << x
                fed += total
            total + fed
        "},
        Value::Int(24),
    );
}

/// A declaration with no value introduces a feed, which its feeds and its `<<=` give a value,
/// at any depth: at the top level, in a loop body and in a function body.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case("out: Feed(_); out << 1; out << 2; sum(out)", 3)]
#[case(
    indoc! {"
        out: Feed(Int)
        for x in [1, 2, 3]:
            out << x * 10
        sum(out)
    "},
    60
)]
#[case("out: Feed(_); out <<= [1, 2, 3]; sum(out)", 6)]
#[case(
    indoc! {"
        def totals(xs):
            t: Feed(_)
            t << sum(xs)
            t
        rs = [1, 2, 3, 4]
        ts = totals(rs)
        for x in rs:
            ts << x
        max(ts)
    "},
    10
)]
// A loop body's declaration is a feed per iteration, in a loop that feeds and in one that
// writes a mutable variable. The feed's value may read a binding below the declaration.
#[case(
    indoc! {"
        out: Feed(_)
        for x in [1, 2]:
            h: Feed(_)
            h << x * 10
            out << sum(h)
        sum(out)
    "},
    30
)]
#[case(
    indoc! {"
        n := 0
        for x in [1, 2]:
            h: Feed(_)
            m = x * 2
            h << m
            n += sum(h)
        n
    "},
    6
)]
// A function body's declaration is a feed per call.
#[case(
    indoc! {"
        def tens(x):
            t: Feed(_)
            t << x * 10
            t
        sum(tens(1)) + sum(tens(2))
    "},
    30
)]
fn a_declared_feed_is_fed(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A feed a loop's body declares is fed from one place in the iteration, which may sit under
/// a condition, in an inner loop, or in a called function: each iteration builds its own
/// collection.
#[rstest]
#[case::under_an_if(
    indoc! {"
        n := 0
        for x in [1, 2, 3]:
            h: Feed(_)
            if x > 1:
                h << x
            n += sum(h)
        n
    "},
    5
)]
#[case::through_a_call_under_an_if(
    indoc! {"
        def g(o, x):
            o << x
        n := 0
        for x in [1, 2, 3]:
            h: Feed(_)
            if x > 1:
                g(h, x)
            n += sum(h)
        n
    "},
    5
)]
#[case::from_an_inner_loop(
    indoc! {"
        n := 0
        for x in [1, 2, 3]:
            h: Feed(_)
            for y in [1, 2]:
                h << x * y
            n += sum(h)
        n
    "},
    18
)]
#[case::under_an_if_in_an_inner_loop(
    indoc! {"
        n := 0
        for x in [1, 2, 3]:
            h: Feed(_)
            for y in [1, 2]:
                if y > 1:
                    h << x * y
            n += sum(h)
        n
    "},
    12
)]
#[case::from_an_inner_loop_under_an_if(
    indoc! {"
        n := 0
        for x in [1, 2, 3]:
            h: Feed(_)
            if x > 1:
                for y in [1, 2]:
                    h << x * y
            n += sum(h)
        n
    "},
    15
)]
#[case::from_an_inner_loop_in_a_call(
    indoc! {"
        def g(o, x):
            for y in [1, 2]:
                o << x * y
        n := 0
        for x in [1, 2, 3]:
            h: Feed(_)
            g(h, x)
            n += sum(h)
        n
    "},
    18
)]
#[case::in_a_loop_that_feeds(
    indoc! {"
        out: Feed(_)
        for x in [1, 2, 3]:
            h: Feed(_)
            h << x * 2
            out << sum(h)
        sum(out)
    "},
    12
)]
fn a_feed_a_loop_body_declares_is_fed_from_one_place(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A feed a loop's body declares and feeds from two places, both arms of an `if` included,
/// unions two collections that vary with the iteration, which is refused as `[a] ++ [b]` in a
/// loop body is.
#[rstest]
#[case::twice_in_a_loop_that_feeds(indoc! {"
    out: Feed(_)
    for x in [1, 2]:
        h: Feed(_)
        h << x
        h << x * 10
        out << sum(h)
    sum(out)
"})]
#[case::twice_in_a_loop_that_writes(indoc! {"
    n := 0
    for x in [1, 2]:
        h: Feed(_)
        h << x
        h << x * 10
        n += sum(h)
    n
"})]
#[case::in_both_arms_of_an_if(indoc! {"
    n := 0
    for x in [1, 2, 3]:
        h: Feed(_)
        if x > 1:
            h << x
        else:
            h << 100
        n += sum(h)
    n
"})]
fn a_feed_a_loop_body_declares_fed_from_two_places_is_refused(#[case] code: &str) {
    check_compile_error(
        code,
        "is fed in two places in one iteration, which unions two collections that vary with \
         the iteration",
    );
}

/// `defer()`, which declarations replaced, is refused naming what replaces it.
#[test]
fn defer_names_the_declaration_that_replaces_it() {
    check_compile_error(
        "x = defer()\nx << 1\nsum(x)\n",
        "`defer()` no longer introduces a feed: declare one with no value, `x: Feed(T)`",
    );
}

/// The declared value type is the element type every contribution has.
#[test]
fn a_declared_feed_takes_its_value_type() {
    check_compile_error(
        "out: Feed(String); out << 1; out",
        "Type mismatch for contribution to feed(out, 1)",
    );
}

/// A `Feed(…)` annotation states a feed wherever a binder takes one: a parameter of a
/// function of one or several parameters, and an annotated binding.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    indoc! {"
        def g(o: Feed(Int)):
            o << 5
        out: Feed(_)
        g(out)
        sum(out)
    "},
    5
)]
#[case(
    indoc! {"
        def g(o: Feed(Int), x):
            o << x
        out: Feed(_)
        g(out, 4)
        g(out, 3)
        sum(out)
    "},
    7
)]
#[case("out: Feed(_); o: Feed(Int) = out; o << 3; sum(out)", 3)]
fn a_feed_annotation_states_a_feed(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// A parameter is fed as the handle it is bound to is, with no annotation: in a function of
/// several parameters, called in a loop, and passed on to another function's parameter.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    indoc! {"
        def g(o, x):
            o << x
        out: Feed(_)
        g(out, 4)
        g(out, 3)
        sum(out)
    "},
    7
)]
#[case(
    indoc! {"
        def g(o, x):
            o << x + 1
        out: Feed(_)
        for x in [1, 2]:
            g(out, x)
        sum(out)
    "},
    5
)]
#[case(
    indoc! {"
        def g(o, x):
            o << x
        def h(o, x):
            g(o, x)
        out: Feed(_)
        h(out, 3)
        sum(out)
    "},
    3
)]
fn an_unannotated_parameter_is_fed(#[case] code: &str, #[case] expected: i64) {
    check_scalar(code, Value::Int(expected));
}

/// The north-star `fanout` with declared feeds in place of its two sinks: a function
/// declares a feed, fans what it receives out to two feed parameters, and returns it.
#[test]
fn a_feed_returned_by_a_function_fans_out() {
    check_scalar(
        indoc! {"
            def fanout(a, b):
                h: Feed(_)
                for x in h:
                    a << x
                    b << x
                h

            o1: Feed(_)
            o2: Feed(_)
            out: Feed(_) = fanout(o1, o2)
            for line in [1, 2, 3]:
                out << line
            sum(o1) * 10 + sum(o2)
        "},
        Value::Int(66),
    );
}

/// A feed crossing `let`s between its target and itself: each is discharged on the edge
/// into the target, so a row naming one compiles (`src/ccl/design/type-inference.md`, "A
/// contribution crosses the binders after its target").
#[rstest]
#[case::a_let_before_the_feed(indoc! {r#"
    out = test_sink()
    xs = [1, 2, 3]
    out << [v for v in xs if v > 1]
"#}, "[() -> [1 -> 2, 2 -> 3]]")]
#[case::a_constant_let_inside_a_loop(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        k = 1
        out << [v for v in [1, 2, 3] if v > k]
"#}, "[[1 -> 2, 2 -> 3], [1 -> 2, 2 -> 3]]")]
#[case::a_let_before_a_loop(indoc! {r#"
    out = test_sink()
    xs = [1, 2, 3]
    for r in [1, 2]:
        out << [v for v in xs if v > 1]
"#}, "[[1 -> 2, 2 -> 3], [1 -> 2, 2 -> 3]]")]
// A mutable variable declared between the channel and the feed is one variable, so the
// edge keeps its name; the filter's read of it is named by a binder of its own.
#[case::a_mutable_variable_declared_after_the_channel(indoc! {r#"
    out = test_sink()
    acc := 1
    out << [z for z in [1, 2, 3] if z > acc]
"#}, "[() -> [1 -> 2, 2 -> 3]]")]
fn a_feed_crossing_a_let(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
}

/// A feed crossing a generic `let` that its row's filter calls. The crossing discharges the
/// `let` to its generalized definition, whose type slots no use instantiates, so the row's
/// type keeps them past channelize. Pinned on that failure as a known gap: the residue check
/// is debug-only, and without it the post-channelize tree check fails on the same slots.
#[test]
#[cfg_attr(
    debug_assertions,
    should_panic(expected = "type residue survived channelize")
)]
#[cfg_attr(
    not(debug_assertions),
    should_panic(expected = "post-channelize produced an invalid tree")
)]
fn a_feed_crossing_a_generic_let() {
    check_sink(
        indoc! {r#"
            out = test_sink()
            f = \x -> x
            out << [v for v in [1, 2, 3] if f(v) > 1]
        "#},
        "[() -> [1 -> 2, 2 -> 3]]",
    );
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
"#}, "[() -> 1]")]
#[case::called_in_a_loop(indoc! {r#"
    out = test_sink()
    def f(y):
        out << y
    for r in [1, 2]:
        f(r)
"#}, "[1, 2]")]
#[case::a_row_constant_in_the_parameter(indoc! {r#"
    out = test_sink()
    def f(y):
        out << [v + y for v in [1, 2, 3]]
    for r in [1, 2]:
        f(r)
"#}, "[[2, 3, 4], [3, 4, 5]]")]
// Each call site is its own place, as two `<<` statements are.
#[case::called_twice(indoc! {r#"
    out = test_sink()
    def f(y):
        out << y
    f(1)
    f(2)
"#}, "[`0(()) -> 1, `1(()) -> 2]")]
#[case::called_once_and_from_a_loop(indoc! {r#"
    out = test_sink()
    def f(y):
        out << y
    out << 0
    f(0)
    for r in [1, 2]:
        f(r)
"#}, "[`0(()) -> 0, `1(()) -> 0, `2(0) -> 1, `2(1) -> 2]")]
#[case::called_through_another_def(indoc! {r#"
    out = test_sink()
    def f(y):
        out << y
    def g(z):
        f(z)
        f(z + 10)
    g(1)
"#}, "[`0(()) -> 1, `1(()) -> 11]")]
fn a_def_feeding_a_handle_declared_outside_it(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
}

/// A feed's element type is the join of every contribution, and a feed contributes once per
/// value of the binders between the target and the feed (`src/ccl/design/type-inference.md`,
/// "A contribution crosses the binders after its target"). Where the target's key determines
/// a binder, a row reads it at the key (`rows_keyed_by_the_loops_around_the_feed`). Where it does not, rows whose keys depend on the
/// binder have no join, so the program is refused naming it: a `def` parameter, and a target
/// fed from two places, whose key does not say which place a row came from.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::filtered_by_a_parameter(indoc! {r#"
    o: Feed(_)
    def f(y):
        o << [v for v in [1, 2, 3] if v > y]
    for r in [1, 2]:
        f(r)
    o
"#}, "`y`")]
// The `let` is joined over because its definition reads `y`, and the message names `y`.
#[case::through_a_let_of_a_parameter(indoc! {r#"
    o: Feed(_)
    def f(y):
        k = y
        o << [v for v in [1, 2, 3] if v > k]
    f(1)
    o
"#}, "`y`")]
// One call is refused as well: the `def` is inferred once, for every call.
#[case::filtered_by_a_parameter_of_a_def_called_once(indoc! {r#"
    o: Feed(_)
    def f(y):
        o << [v for v in [1, 2, 3] if v > y]
    f(1)
    o
"#}, "`y`")]
// A pattern's binder takes one value per evaluation of its `match`, and is joined over.
#[case::filtered_by_a_pattern_binder(indoc! {r#"
    o: Feed(_)
    v = `some(1)
    match v:
        case `some(x):
            o << [z for z in [1, 2, 3] if z > x]
        case `none(_):
            o << [z for z in [1, 2, 3]]
    o
"#}, "`x`")]
#[case::fed_from_two_loops(indoc! {r#"
    o: Feed(_)
    for r in [1, 2]:
        o << [v for v in [1, 2, 3] if v > r]
    for q in [1]:
        o << [v for v in [1, 2, 3] if v > q]
    o
"#}, "`r`")]
// The loop writes `t`, so the filter reads it once per iteration, and the message spells the
// read's binder as the variable it reads.
#[case::filtered_by_a_mutable_variable_the_loop_writes(indoc! {r#"
    o: Feed(_)
    t := 0
    for r in [1, 2]:
        t += r
        o << [v for v in [1, 2, 3] if v > t]
    o
"#}, "`t`")]
fn rows_whose_keys_vary_with_a_binder_have_no_join(#[case] code: &str, #[case] binder: &str) {
    check_compile_error(code, &format!("depend on {binder}"));
}

/// A function whose parameter's refinement varies with a joined binder has no join either: the
/// join of the functions accepts only what each accepts, and dropping the refinement would narrow
/// the parameter rather than widen it (`src/ccl/design/type-inference.md`, "A contribution
/// crosses the binders after its target").
#[test]
fn functions_whose_parameter_varies_with_a_binder_have_no_join() {
    check_compile_error(
        indoc! {r#"
            o: Feed(_)
            for r in [1, 2]:
                xs = [v for v in [1, 2, 3] if v > r]
                o << (\i -> xs[i])
            o
        "#},
        "the parameter of a function written to a feed or mutable variable depends on `r`",
    );
}

/// One contribution with no join is reported once, though every node whose type reaches the
/// target meets it.
#[test]
fn a_contribution_with_no_join_is_reported_once() {
    let code = indoc! {r#"
        o: Feed(_)
        def f(y):
            o << [v for v in [1, 2, 3] if v > y]
        f(1)
        o
    "#};
    let loaded = LoadedProgram::from_text("<no-join-once-test>", code);
    let errs = match compile_program(&mut GlobalContext::default(), &loaded, Box::new(|| {})) {
        Ok(_) => panic!("rows whose keys vary with a `def` parameter have no join"),
        Err(e) => e,
    };
    let rendered = render_errors(&errs, loaded.sources());
    assert_eq!(
        rendered.matches("the keys of a collection").count(),
        1,
        "{rendered}"
    );
}

/// A loop's position keys the rows of a target fed from one place. Fed from two, the target
/// is refused as any join over the loop variable is, and the message names the other place.
#[test]
fn a_target_fed_from_two_places_names_the_other() {
    let code = indoc! {r#"
        o: Feed(_)
        for r in [1, 2]:
            o << [v for v in [1, 2, 3] if v > r]
        for q in [1]:
            o << [v for v in [1, 2, 3] if v > q]
        o
    "#};
    let sources = LoadedProgram::from_text("<two-places-test>", code);
    let errs = match compile_program(&mut GlobalContext::default(), &sources, Box::new(|| {})) {
        Ok(_) => panic!("rows keyed by a loop's position need a target fed from one place"),
        Err(e) => e,
    };
    let rendered = render_errors(&errs, sources.sources());
    assert!(
        rendered.contains("this target is fed from more than one")
            && rendered.contains("the target is also fed here"),
        "{rendered}"
    );
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
"#}, "[[1 -> 2, 2 -> 3], [2 -> 3]]")]
#[case::grouped_by_the_loop_variable(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        out << [sum(g) for g in groupby([1, 2, 3, 4], \e -> e // i)]
"#}, "[[1 -> 1, 2 -> 2, 3 -> 3, 4 -> 4], [1, 5, 4]]")]
#[case::through_a_let_of_the_loop_variable(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        k = r
        out << [v for v in [1, 2, 3] if v > k]
"#}, "[[1 -> 2, 2 -> 3], [2 -> 3]]")]
#[case::through_a_let_computed_from_it(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        m = r + 1
        out << [v for v in [1, 2, 3] if v > m]
"#}, "[[2 -> 3], []]")]
#[case::under_a_filtered_loop(indoc! {r#"
    out = test_sink()
    for r in [1, 2, 3]:
        if r > 1:
            out << [v for v in [1, 2, 3] if v > r]
"#}, "[1 -> [2 -> 3], 2 -> []]")]
#[case::over_a_named_source(indoc! {r#"
    xs = [1, 2]
    out = test_sink()
    for r in xs:
        out << [v for v in [1, 2, 3] if v > r]
"#}, "[[1 -> 2, 2 -> 3], [2 -> 3]]")]
// The source's filter is read at each key through the binding, and planned in one copy of
// the row's type only: the two compare as one predicate.
#[case::over_a_named_filtered_source(indoc! {r#"
    xs = [x for x in [1, 2, 3] if x > 1]
    out = test_sink()
    for r in xs:
        out << [v for v in [1, 2, 3, 4] if v > r]
"#}, "[1 -> [2 -> 3, 3 -> 4], 2 -> [3 -> 4]]")]
#[case::read_back_through_a_defer(indoc! {r#"
    o: Feed(_)
    for r in [1, 2]:
        o << [v for v in [1, 2, 3] if v > r]
    out = test_sink()
    out << sum([sum(row) for row in o])
"#}, "[() -> 8]")]
#[case::yielded_by_a_generator(indoc! {r#"
    def rows(xs):
        for x in xs:
            yield [v for v in [1, 2, 3] if v > x]
    out = test_sink()
    out << sum([sum(r) for r in rows([1, 2])])
"#}, "[() -> 8]")]
#[case::under_two_loops_reading_the_outer(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [10, 20]:
            out << [v for v in [1, 2, 3] if v > i]
"#}, "[(_0: 0, _1: 0) -> [1 -> 2, 2 -> 3], (_0: 0, _1: 1) -> [1 -> 2, 2 -> 3], (_0: 1, _1: 0) -> [2 -> 3], (_0: 1, _1: 1) -> [2 -> 3]]")]
#[case::under_two_loops_reading_both(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [1, 2]:
            out << [v for v in [1, 2, 3] if v > i + j]
"#}, "[(_0: 0, _1: 0) -> [2 -> 3], (_0: 0, _1: 1) -> [], (_0: 1, _1: 0) -> [], (_0: 1, _1: 1) -> []]")]
#[case::under_three_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [1, 2]:
            for k in [1, 2]:
                out << [v for v in [1, 2, 3, 4] if v > i + j - k]
"#}, "[(_0: 0, _1: 0, _2: 0) -> [1 -> 2, 2 -> 3, 3 -> 4], (_0: 0, _1: 0, _2: 1) -> [1, 2, 3, 4], (_0: 0, _1: 1, _2: 0) -> [2 -> 3, 3 -> 4], (_0: 0, _1: 1, _2: 1) -> [1 -> 2, 2 -> 3, 3 -> 4], (_0: 1, _1: 0, _2: 0) -> [2 -> 3, 3 -> 4], (_0: 1, _1: 0, _2: 1) -> [1 -> 2, 2 -> 3, 3 -> 4], (_0: 1, _1: 1, _2: 0) -> [3 -> 4], (_0: 1, _1: 1, _2: 1) -> [2 -> 3, 3 -> 4]]")]
fn rows_keyed_by_the_loops_around_the_feed(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
}

/// Rows keyed by the loops that fed them, read back by a `for` loop, are refused: the loop
/// types its element at a row that reads the position, which nothing binds over the loop's
/// body. A comprehension over the same rows compiles (`read_back_through_a_defer`).
#[test]
fn keyed_rows_read_back_by_a_loop_are_refused() {
    check_compile_error(
        indoc! {r#"
            o: Feed(_)
            for r in [1, 2]:
                o << [v for v in [1, 2, 3] if v > r]
            out: Feed(_)
            for row in o:
                out << sum(row)
            sum(out)
        "#},
        "a `for` loop over a collection whose rows depend on their position",
    );
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
"#}, "[(_0: 0, _1: 1) -> 3, (_0: 0, _1: 2) -> 4, (_0: 1, _1: 2) -> 5]")]
#[case::rows_reading_the_inner_variable(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            out << [v for v in [1, 2, 3] if v > j]
"#}, "[(_0: 0, _1: 1) -> [2 -> 3], (_0: 0, _1: 2) -> [], (_0: 1, _1: 2) -> []]")]
#[case::rows_over_an_inner_source_reading_the_outer(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z + i for z in [1, 2, 3] if z > i]:
            out << [v for v in [1, 2, 3, 4, 5] if v > j]
"#}, "[(_0: 0, _1: 1) -> [3 -> 4, 4 -> 5], (_0: 0, _1: 2) -> [4 -> 5], (_0: 1, _1: 2) -> []]")]
#[case::an_aggregate_per_row(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            out << sum([v for v in [1, 2, 3] if v > j])
"#}, "[(_0: 0, _1: 1) -> 3, (_0: 0, _1: 2) -> 0, (_0: 1, _1: 2) -> 0]")]
#[case::a_third_loop_over_independent_keys(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            for k in [1, 2]:
                out << j + k
"#}, "[(_0: 0, _1: 1, _2: 0) -> 3, (_0: 0, _1: 1, _2: 1) -> 4, (_0: 0, _1: 2, _2: 0) -> 4, (_0: 0, _1: 2, _2: 1) -> 5, (_0: 1, _1: 2, _2: 0) -> 4, (_0: 1, _1: 2, _2: 1) -> 5]")]
#[case::a_chain_of_three_dependent_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            for k in [w for w in [1, 2, 3, 4] if w > j]:
                out << k
"#}, "[(_0: 0, _1: 1, _2: 2) -> 3, (_0: 0, _1: 1, _2: 3) -> 4, (_0: 0, _1: 2, _2: 3) -> 4, (_0: 1, _1: 2, _2: 3) -> 4]")]
#[case::rows_under_three_dependent_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            for k in [w for w in [1, 2, 3, 4] if w > j]:
                out << [v for v in [1, 2, 3, 4, 5] if v > k]
"#}, "[(_0: 0, _1: 1, _2: 2) -> [3 -> 4, 4 -> 5], (_0: 0, _1: 1, _2: 3) -> [4 -> 5], (_0: 0, _1: 2, _2: 3) -> [4 -> 5], (_0: 1, _1: 2, _2: 3) -> [4 -> 5]]")]
#[case::a_chain_of_four_dependent_loops(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [z for z in [1, 2, 3] if z > i]:
            for k in [w for w in [1, 2, 3, 4] if w > j]:
                for m in [u for u in [1, 2, 3, 4, 5] if u > k]:
                    out << m
"#}, "[(_0: 0, _1: 1, _2: 2, _3: 3) -> 4, (_0: 0, _1: 1, _2: 2, _3: 4) -> 5, (_0: 0, _1: 1, _2: 3, _3: 4) -> 5, (_0: 0, _1: 2, _2: 3, _3: 4) -> 5, (_0: 1, _1: 2, _2: 3, _3: 4) -> 5]")]
#[case::only_the_third_loop_dependent(indoc! {r#"
    out = test_sink()
    for i in [1, 2]:
        for j in [1, 2]:
            for k in [w for w in [1, 2, 3, 4] if w > i + j]:
                out << k
"#}, "[(_0: 0, _1: 0, _2: 2) -> 3, (_0: 0, _1: 0, _2: 3) -> 4, (_0: 0, _1: 1, _2: 3) -> 4, (_0: 1, _1: 0, _2: 3) -> 4]")]
fn a_feed_under_a_dependent_nest(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
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
"#}, "[[1 -> 2, 2 -> 3], [2 -> 3]]")]
#[case::read_by_a_comprehension(indoc! {r#"
    o: Feed(_)
    for r in [1, 2]:
        o << box([v for v in [1, 2, 3] if v > r])
    out = test_sink()
    out << sum([sum(b) for b in o])
"#}, "[() -> 8]")]
#[case::read_by_a_loop(indoc! {r#"
    o: Feed(_)
    for r in [1, 2]:
        o << box([v for v in [1, 2, 3] if v > r])
    out = test_sink()
    for b in o:
        out << sum(b)
"#}, "[5, 3]")]
#[case::filtered_through_a_binding_in_the_loop(indoc! {r#"
    out = test_sink()
    for r in [1, 2]:
        n = r + 1
        out << box([v for v in [1, 2, 3, 4] if v > n])
"#}, "[[2 -> 3, 3 -> 4], [3 -> 4]]")]
#[case::filtered_through_a_binding_and_read(indoc! {r#"
    o: Feed(_)
    for r in [1, 2]:
        n = r + 1
        o << box([v for v in [1, 2, 3, 4] if v > n])
    out = test_sink()
    out << sum([sum(b) for b in o])
"#}, "[() -> 11]")]
fn boxed_rows_fed_from_a_loop(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
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
"#}, "[[1 -> 2, 2 -> 3], [2 -> 3]]")]
#[case::fed_under_a_condition(indoc! {r#"
    t := 0
    out = test_sink()
    for r in [1, 2, 3]:
        t += r
        if r > 1:
            out << [v for v in [1, 2, 3] if v > r]
"#}, "[1 -> [2 -> 3], 2 -> []]")]
#[case::rows_reading_both_loops_of_a_nest(indoc! {r#"
    t := 0
    out = test_sink()
    for i in [1, 2]:
        for j in [1, 2]:
            t += j
            out << [v for v in [1, 2, 3, 4] if v > i + j]
"#}, "[(_0: 0, _1: 0) -> [2 -> 3, 3 -> 4], (_0: 0, _1: 1) -> [3 -> 4], (_0: 1, _1: 0) -> [3 -> 4], (_0: 1, _1: 1) -> []]")]
fn a_feed_under_a_loop_writing_a_mutable_variable(#[case] source: &str, #[case] expected: &str) {
    check_sink(source, expected);
}
