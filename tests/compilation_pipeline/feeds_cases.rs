//! Feed (`<<`, `<<=`) and define operators on `defer()` channels, plus the
//! multi-arm `if/elif`-with-feeds known-gap test.

use std::time::Duration;

use bit_set::BitSet;
use cambra::ccl::context::{GlobalContext, compile_program, render_errors};
use cambra::interpreter::{ColumnValue, Consumer, Predicate, Tile};
use rstest_log::rstest;

use crate::helpers::*;

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case::simple_feed("x = defer(); x <<= 1; x", Tile::Scalar(ColumnValue::Ints(vec![1])))]
#[case::two_defers_arithmetic("x = defer(); y = defer(); x <<= 1; y <<= 2; x + y", Tile::Scalar(ColumnValue::Ints(vec![3])))]
#[case::feed_list("x = defer(); x <<= [1,2,3]; x", make_int_list(&[1, 2, 3]))]
#[case::feed_scalar_to_defer("x = defer(); x << 1; x", Tile::SealedFunction { domain: ColumnValue::Units(1), codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1]))), domain_predicate: Predicate::True, deleted: BitSet::new() })]
#[case::feed_in_comprehension("x = defer(); [x << i for i in [1,2,3]]; x", make_int_list(&[1, 2, 3]))]
#[case::feed_in_for_loop(
r#"x = defer()
for i in [1,2,3]:
  x << i
x"#, make_int_list(&[1, 2, 3]))]
#[ignore = "known failing inference case with predicates"]
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
// (via define).  The desugar pass must topologically order the defers
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
        domain: ColumnValue::Union {
            tags: vec![0, 1],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
#[case::scalar_and_loop_feeds(
r#"x = defer()
x << 1
for i in [1, 2, 3]:
    x << i
x"#,
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 1, 1, 1],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1, 2, 3]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
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
        domain: ColumnValue::Union {
            tags: vec![0, 1, 2],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
// Identical feed values still produce distinct variant tags.
#[case::identical_feeds(
r#"x = defer()
x << 1
x << 1
x"#,
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 1],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 1]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
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
        domain: ColumnValue::Union {
            tags: vec![0, 1, 1, 1],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 1, 2, 3]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
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
        domain: ColumnValue::Union {
            tags: vec![0, 1, 2, 2, 2],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2])
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 100, 1, 2, 3]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
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
        domain: ColumnValue::Union {
            tags: vec![0, 0, 0, 0, 0, 1, 1, 1, 1, 1],
            variants: vec![
                ColumnValue::Union {
                    tags: vec![0, 1, 2, 2, 2],
                    variants: vec![
                        ColumnValue::Units(1),
                        ColumnValue::Units(1),
                        ColumnValue::UInts(vec![0, 1, 2]),
                    ],
                },
                ColumnValue::Union {
                    tags: vec![0, 1, 2, 2, 2],
                    variants: vec![
                        ColumnValue::Units(1),
                        ColumnValue::Units(1),
                        ColumnValue::UInts(vec![0, 1, 2]),
                    ],
                },
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 100, 1, 2, 3, 10, 100, 1, 2, 3]))),
        domain_predicate: Predicate::Union(vec![
            Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
            Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
        ]),
        deleted: BitSet::new(),
    })]
#[ignore] // TODO this should work, but our filters on supported exprs in loops are too restrictive
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
        domain: ColumnValue::Union {
            tags: vec![0, 0, 0, 1, 1, 1],
            variants: vec![
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1, 2]),
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 1, 3, 10, 30, 60]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    }
)]
fn test_feed_and_define_operators(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

/// Multi-arm `if/elif` inside a for-loop body, with feeds in some
/// branches and not others.  Pins the *first* gap that blocks this
/// pattern from working end-to-end.
///
/// # Stacked gaps
///
/// 1. **Lowering** (current failure point).  `lower_generator_for`
///    rejects `elif` inside a generator-for-loop body — the multi-arm
///    Case form never gets constructed from CHL source today.  Until
///    this restriction is lifted, the desugar-pass gaps below are
///    unreachable via real CHL programs.
///
/// 2. **`desugar_defers::empty_channel` typecheck mismatch.**  Once
///    lowering accepts `elif`, the lambda body becomes
///    `Case { g_0 → Feed(d, v_0); g_1 → Feed(d, v_1); true → Unit }`.
///    `extract_for_defer`'s Case-arm fan-out wraps each arm's
///    terminal in `Record({result, to_d: <channel>})`, where the
///    no-feed arm publishes `empty_channel()` (currently `Lit::Unit`).
///    Feeding arms publish a typed scalar (e.g. `Var(x) : Int`).
///    Inference rejects the Case because `Unit` doesn't unify with
///    `Int` across arms.  This is purely a typecheck failure — even
///    if we patched the type (e.g. via a synthesized
///    `TypedExprNode::EmptyValue` with fresh `Type::Infer`), the
///    runtime semantics in (3) below would still be wrong.
///
/// 3. **Runtime semantics — the no-feed arm leaks a placeholder
///    value into the stream.**  Even with the type mismatch fixed,
///    the Case fan-out produces a per-iteration `to_d` value for
///    *every* iteration, including ones where the implicit
///    `true → unit` arm fires.  For the example below the resulting
///    `d` channel stream would be `[10, 40, <placeholder for x=3>]`
///    when the user expects `[10, 40]`.
///
/// # The proper fix: refinement-based fan-out
///
/// The right solution generalizes the existing
/// [`try_extract_filter_feed`] (which handles the two-arm
/// `if cond: d << x` shape) to N arms.  For each arm `i` with feeds,
/// build a *refined source* whose predicate is
/// `¬g_0 ∧ ¬g_1 ∧ … ∧ ¬g_{i-1} ∧ g_i` (encoding Case's "first
/// matching guard wins" semantics).  Each arm contributes
/// `refined_source ≫ (λ p → feed_value)` to the cluster channel
/// via `++`.  Arms without feeds contribute nothing.  This makes
/// gaps (2) and (3) disappear together — no empty-channel
/// placeholder is needed because empty arms don't produce a
/// contribution at all.
///
/// Tracked as tech debt: "Generalize filter-pattern recognition".
///
/// # Test behaviour
///
/// Asserts the program fails to compile, regardless of *which*
/// stage produces the error.  When a future change lifts gap (1),
/// this test will likely start surfacing gap (2) — and when the
/// refinement-based fan-out lands, the `expect_err` flip will
/// signal it's time to convert this into a success assertion.
///
/// The realistic two-arm `if cond: d << x` shape compiles cleanly
/// via [`try_extract_filter_feed`]; see the existing case in
/// [`test_feed_and_define_operators`].
#[test]
fn multi_arm_case_with_some_feeding_branches_is_a_known_gap() {
    let code = r#"d = defer()
for x in [1, 2, 3]:
    if x == 1:
        d << x * 10
    elif x == 2:
        d << x * 20
d"#;
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let result = compile_program(&mut ctx, code, consumer);
    let err = match result {
        Ok(_) => panic!(
            "multi-arm case with feeds in some branches should fail today — \
             if this is no longer the case, walk through the stacked-gap doc \
             on this test and convert to a success assertion with the expected \
             Tile (e.g. [10, 40] for the example above)"
        ),
        Err(e) => e,
    };
    let rendered = render_errors(&err, "<multi-arm-feed-test>", code);
    assert!(
        !rendered.is_empty(),
        "expected non-empty rendered error message"
    );
}
