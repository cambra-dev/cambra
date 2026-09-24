//! Feed (`<<`, `<<=`) and define operators on `defer()` channels, plus the
//! multi-arm `if/elif`-with-feeds known-gap test.

use std::time::Duration;

use bit_set::BitSet;
use cambra::ccl::context::{GlobalContext, Phase, compile_program, compile_to, render_errors};
use cambra::ccl::symbolic::symbolic_typed;
use cambra::interpreter::{ColumnValue, Consumer, Predicate, Tile, Value};
use rstest_log::rstest;

use cambra::ccl::TagMap;
use indoc::indoc;

use crate::helpers::*;

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::feed_list("x = defer(); x <<= [1,2,3]; x", make_int_list(&[1, 2, 3]))]
#[case::feed_scalar_to_defer("x = defer(); x << 1; x", Tile::SealedFunction { domain: ColumnValue::Units(1), codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1]))), domain_predicate: Predicate::True, deleted: BitSet::new() })]
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
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
#[case::scalar_and_loop_feeds(
r#"x = defer()
x << 1
for i in [1, 2, 3]:
    x << i
x"#,
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 1, 1, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1, 2, 3]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
// Three feed sites: locks down N-ary union construction beyond N=2.
#[case::three_feeds(
r#"x = defer()
x << 1
x << 2
x << 3
x"#,
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 1, 2], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
// Identical feed values still produce distinct variant tags.
#[case::identical_feeds(
r#"x = defer()
x << 1
x << 1
x"#,
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
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
y"#, Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 1, 1, 1], vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 1, 2, 3]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
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
y"#, Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 1, 2, 2, 2], vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 100, 1, 2, 3]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
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
y ++ y"#, Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 0, 0, 0, 0, 1, 1, 1, 1, 1], vec![
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
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 100, 1, 2, 3, 10, 100, 1, 2, 3]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![
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
        ])),
        deleted: BitSet::new(),
    })]
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
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 0, 0, 1, 1, 1], vec![
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1, 2]),
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 20, 40, 60]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    }
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
        Tile::SealedFunction {
            domain: ColumnValue::positional_union(
                &[0, 1],
                vec![ColumnValue::UInts(vec![0]), ColumnValue::UInts(vec![1])],
            ),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 40]))),
            domain_predicate: Predicate::Union(TagMap::from_positional(vec![
                Predicate::True,
                Predicate::True,
            ])),
            deleted: BitSet::new(),
        },
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
        Tile::SealedFunction {
            domain: ColumnValue::positional_union(
                &[0, 0, 1, 1],
                vec![
                    ColumnValue::UInts(vec![0, 1]),
                    ColumnValue::UInts(vec![2, 3]),
                ],
            ),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 1, 100, 100]))),
            domain_predicate: Predicate::Union(TagMap::from_positional(vec![
                Predicate::True,
                Predicate::True,
            ])),
            deleted: BitSet::new(),
        },
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
        out = defer()
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
            out = defer()
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
            out = defer()
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
#[case::match_good("good", &[0usize], &[2i64])]
#[case::match_bad("bad", &[1], &[3])]
fn two_defers_fed_from_complementary_match_arms(
    #[case] read: &str,
    #[case] domain: &[usize],
    #[case] codomain: &[i64],
) {
    let code = format!(
        indoc! {r#"
            good = defer()
            bad = defer()
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
        Tile::SealedFunction {
            domain: ColumnValue::UInts(domain.to_vec()),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(codomain.to_vec()))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
    );
}

/// The `if`/`else` spelling of [`two_defers_fed_from_complementary_match_arms`].
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::if_good("good", &[1usize], &[2i64])]
#[case::if_bad("bad", &[0], &[1])]
fn two_defers_fed_from_complementary_if_arms(
    #[case] read: &str,
    #[case] domain: &[usize],
    #[case] codomain: &[i64],
) {
    let code = format!(
        indoc! {r#"
            good = defer()
            bad = defer()
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
        Tile::SealedFunction {
            domain: ColumnValue::UInts(domain.to_vec()),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(codomain.to_vec()))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
    );
}

/// A `case _:` default arm feeding the second defer. `tag_case_to_guard_case` gives a
/// default arm the trailing `true` guard rather than a `variant_is` test, so its channel
/// covers the complement of every named arm — two of the three elements here — and the
/// residual keeps the default arm for the named arm's pass to leave alone.
#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::named_arm("a", &[0usize], &[1i64])]
#[case::default_arm("b", &[1, 2], &[7, 7])]
fn a_default_arm_feeds_its_own_defer(
    #[case] read: &str,
    #[case] domain: &[usize],
    #[case] codomain: &[i64],
) {
    let code = format!(
        indoc! {r#"
            a = defer()
            b = defer()
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
        Tile::SealedFunction {
            domain: ColumnValue::UInts(domain.to_vec()),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(codomain.to_vec()))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
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
        a = defer()
        b = defer()
        c = defer()
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
        a = defer()
        b = defer()
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
        a = defer()
        b = defer()
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

// ---------------------------------------------------------------------------
// A feed nests: one contribution per feed site, holding whatever was fed
// ---------------------------------------------------------------------------

/// The post-channelize shape of `code`, as `symbolic_typed` renders it.
fn channelized(code: &str) -> String {
    let tree = compile_to(code, Phase::Channelize)
        .unwrap_or_else(|errs| panic!("compiling {code:?} to channelize: {errs:?}"));
    symbolic_typed(&tree)
}

/// A `<<` of a collection is **one** contribution holding that collection, so the
/// channel is unit-keyed and its value is the collection: `Unit ⤇ ([0, 2] ⤇ Int)`.
///
/// `channelize` used to read the fed value's shape to decide whether to lift it,
/// and a collection value looks exactly like the per-position contribution stream
/// `mut_elim::hoist_feeds` builds out of an in-loop feed. Taking this one for that
/// bound the channel at the collection's *own* extent — `[0, 2] ⤇ Int`, three
/// contributions of one `Int` — while every read of the handle stayed typed at the
/// `chan(out) ⤇ ([0, 2] ⤇ Int)` inference recorded. The binder and its reference
/// then disagreed by one level, which no wall reported.
#[test]
fn a_collection_feed_is_one_contribution_holding_the_collection() {
    let out = channelized("out = defer()\nout << [2, 4, 6]\nout\n");
    assert!(
        out.contains("letrec out : (Unit ⤇ ([0, 2] ⤇ Int))"),
        "expected a unit-keyed channel holding the collection, got:\n{out}"
    );
    assert!(
        !out.contains("letrec out : ([0, 2] ⤇ Int)"),
        "the channel must not take the collection's own extent, got:\n{out}"
    );
}

/// Two collection feeds are two contributions, so the channel is the union of two
/// unit-keyed sites — not the two collections' extents joined.
#[test]
fn two_collection_feeds_are_two_contributions() {
    let out = channelized("out = defer()\nout << [1, 2]\nout << [3, 4]\nout\n");
    assert!(
        out.contains("letrec out : (Unit | Unit ⤇ ([0, 1] ⤇ Int))"),
        "expected two unit-keyed sites over the collection, got:\n{out}"
    );
}

/// The contrast, and what the value's shape alone cannot distinguish: an in-loop
/// feed that `mut_elim::hoist_feeds` moved out carries the loop's history — a
/// contribution *per position* — so its own domain **is** the site set and it must
/// not be lifted. Same `Type::Fun` shape as the case above, opposite meaning; the
/// handle's contribution type is what tells them apart.
#[test]
fn a_hoisted_in_loop_feed_keeps_its_positions_as_sites() {
    let out = channelized(indoc! {r#"
        total := 0
        out = defer()
        for item in [1, 2, 3]:
            total += item
            out << [total, total]
        out
    "#});
    assert!(
        out.contains("letrec out : ([0, 2] ⤇ ([0, 1] ⤇ Int))"),
        "expected one contribution per loop position, got:\n{out}"
    );
}

/// A scalar feed is unchanged: one contribution holding a scalar.
#[test]
fn a_scalar_feed_is_one_unit_keyed_contribution() {
    let out = channelized("out = defer()\nout << 3\nout\n");
    assert!(
        out.contains("letrec out : (Unit ⤇ Int@3)"),
        "expected a unit-keyed scalar contribution, got:\n{out}"
    );
}

/// `<<=` is the contrasting *user-level* operator: a define sets the channel to the
/// collection wholesale, so `x <<= [1, 2, 3]` stays the flat three-element channel
/// that `feed_list` above pins. Nesting is what `<<` means, not what a defer means.
#[test]
fn a_define_sets_the_channel_wholesale_rather_than_nesting() {
    let out = channelized("x = defer()\nx <<= [1, 2, 3]\nx\n");
    assert!(
        out.contains("letrec x : ([0, 2] ⤇ Int)"),
        "expected a define to set the channel flat, got:\n{out}"
    );
}

/// **Pinned gap.** The nested channel is well-typed and reaches op-conversion, which
/// cannot yet build a collection sitting in a codomain. Not specific to feeds: a bare
/// nested list literal is refused there too (below), so what this pins is the wall the
/// corrected shape now reaches rather than anything the feed path owes.
///
/// Before the fix this program ran and returned the *flattened* three-element
/// collection, which is the wrong answer rather than a missing one.
#[test]
fn a_nested_collection_stops_at_op_conversion() {
    check_compile_error(
        "x = defer(); x << [2, 4, 6]; x",
        "list literal reached op-conversion without an input",
    );
}

/// A collection inside a collection with no feed anywhere, which is what makes the
/// case above op-conversion's gap rather than the feed path's. Op-conversion rejects
/// it on the way in (a list element must be a constant) instead of on the way out,
/// so the message differs; what the two share is that neither builds.
#[test]
fn a_bare_nested_list_stops_at_op_conversion_too() {
    check_compile_error("[[1, 2], [3, 4]]", "a list element must be a constant");
}
