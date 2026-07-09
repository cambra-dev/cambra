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
#[case::feed_list("x = defer(); x <<= [1,2,3]; x", make_int_list(&[1, 2, 3]))]
#[case::feed_scalar_to_defer("x = defer(); x << 1; x", Tile::SealedFunction { domain: ColumnValue::Units(1), codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1]))), domain_predicate: Predicate::True, deleted: BitSet::new() })]
#[case::feed_in_comprehension("x = defer(); [x << i for i in [1,2,3]]; x", make_int_list(&[1, 2, 3]))]
#[case::feed_in_for_loop(
r#"x = defer()
for i in [1,2,3]:
  x << i
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
            domain: ColumnValue::Union {
                tags: vec![0, 1],
                variants: vec![ColumnValue::UInts(vec![0]), ColumnValue::UInts(vec![1])],
            },
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 40]))),
            domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
            deleted: BitSet::new(),
        },
    );
}

/// `<<=` sets a channel's whole stream, so its RHS must be a collection
/// (a `Fun`). A scalar RHS is rejected by typing — the discipline that keeps
/// every feed history a genuine `domain ⇒ value` stream (scalar values belong
/// in a plain `let` binding or a `:=` register, not a feed channel).
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
/// message must not leak desugar artifacts (floated parameters, `to_<defer>`
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
    for artifact in ["__floated", "to_x", "__scope_out", "⊎", "CollectionUnion"] {
        assert!(
            !rendered.contains(artifact),
            "desugar artifact `{artifact}` leaked into a user-facing type error:\n{rendered}"
        );
    }
}
