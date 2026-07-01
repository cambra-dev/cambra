//! Mutation loops: loop-carried accumulators, multi-accumulator loops, and
//! feeds interleaved with mutations.

use std::collections::HashMap;
use std::time::Duration;

use bit_set::BitSet;
use cambra::interpreter::{ColumnValue, Predicate, Tile};
use rstest_log::rstest;

use crate::helpers::*;

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    r#"
x = 0
for i in [1, 2, 3]:
    x += i
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![6]))
)]
#[case(
    r#"
x = 0
for i in []:
    x += 1
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![0]))
)]
#[case(
    r#"
x = 0
for i in [1, 2, 3]:
    x = x + i + 1
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![9]))
)]
#[case(
    r#"
x = 0
o = defer()
for i in [1, 2, 3]:
    x = x + i
    o << x
o"#,
    make_int_list(&[1,3,6])
)]
#[case(
    r#"
x = 0
o = defer()
o << x
for i in [1, 2, 3]:
    x = x + i
    o << x
for j in [4, 5]:
    x = x + j
    o << x
o"#,
    Tile::SealedFunction {
        // Tags map each domain entry to its source variant: index 0 (pre-loop
        // feed of `x = 0`) → variant 0; indices 1-3 (loop1 running sums) →
        // variant 1; indices 4-5 (loop2 running sums) → variant 2.
        domain: ColumnValue::Union {
            tags: vec![0, 1, 1, 1, 2, 2],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1]),
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 1, 3, 6, 10, 15]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    })]
// Pre-mutation let `y = x + 1` introduces a non-trivial let that survives
// lambda_elim as `(let y = … in …) ▷ const` (the loop body doesn't depend
// on `i`).  This exercises the const-of-function shortcut in op-conversion
// — without it, op-conversion tries to const-lift a function-tiled value.
#[case(
    r#"
x = 0
for i in [1, 2, 3]:
    y = x + 1
    x = y * 2
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![14]))
)]
// As above, but `y` depends on `i` so the source list survives.  This
// gives a Compose `[1,2,3] ≫ (let y = … in (y, 2) ▷ mul)` — the let is
// nested inside the iteration, and its `bound_expr` `(x, i) ▷ add`
// captures both the cyclic accumulator (function-tiled) and the per-i
// stream.
#[case(
    r#"
x = 0
for i in [1, 2, 3]:
    y = x + i
    x = y * 2
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![22]))
)]
#[case(
    r#"
x = 1
y = 0
for i in [1, 2, 3]:
    y = y + i
    x = x * i
(x, y, x + y)"#,
    Tile::Record(HashMap::from([
        ("_0".into(), Tile::Scalar(ColumnValue::Ints(vec![6]))),
        ("_1".into(), Tile::Scalar(ColumnValue::Ints(vec![6]))),
        ("_2".into(), Tile::Scalar(ColumnValue::Ints(vec![12]))),
    ]))
)]
// Multi-accumulator mutation loop combined with a feed.  Per-iter values:
//   iter 0 (i=1): y=0+1=1, x=1*1=1, feed: 1+1=2
//   iter 1 (i=2): y=1+2=3, x=1*2=2, feed: 2+3=5
//   iter 2 (i=3): y=3+3=6, x=2*3=6, feed: 6+6=12
#[case(
    r#"
x = 1
y = 0
o = defer()
for i in [1, 2, 3]:
    y = y + i
    x = x * i
    o << x + y
o"#,
    make_int_list(&[2, 5, 12])
)]
// Multi-accumulator loop with a pre-mutation feed that observes both
// previous-iteration accumulator values.  Per-iter values:
//   iter 0 (i=1): feed prev: 1+10=11; x=1+1=2, y=10*1=10
//   iter 1 (i=2): feed prev: 2+10=12; x=2+2=4, y=10*2=20
//   iter 2 (i=3): feed prev: 4+20=24; x=4+3=7, y=20*3=60
#[case(
    r#"
x = 1
y = 10
o = defer()
for i in [1, 2, 3]:
    o << x + y
    x = x + i
    y = y * i
o"#,
    make_int_list(&[11, 12, 24])
)]
// Two feeds to the same defer within a single mutation loop — exercises
// the lifted-feed lowering in `lower_mutation_loop`.  Each feed must be
// computed against the per-iteration accumulator value, *not* used as the
// accumulator update itself.  Per-iter values:
//   iter 0: x = 0+1 = 1, feeds: 1, 1+100 = 101
//   iter 1: x = 1+2 = 3, feeds: 3, 103
//   iter 2: x = 3+3 = 6, feeds: 6, 106
// The two feeds form variants 0 and 1 of the resulting union.
#[case(
    r#"
x = 0
o = defer()
for i in [1, 2, 3]:
    x = x + i
    o << x
    o << x + 100
o"#,
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 0, 0, 1, 1, 1],
            variants: vec![
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1, 2]),
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 3, 6, 101, 103, 106]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    }
)]
// Feeds in every part of the loop body: a pre-loop feed, an in-loop
// pre-mutation feed (which sees the previous-iteration accumulator
// value), and an in-loop post-mutation feed (which sees the freshly
// updated accumulator).  Per-iter values:
//   iter 0 (i=1): prev_x=0 → feed_pre=0; x=0+1=1; feed_post=1*10=10
//   iter 1 (i=2): prev_x=1 → feed_pre=1; x=1+2=3; feed_post=3*10=30
//   iter 2 (i=3): prev_x=3 → feed_pre=3; x=3+3=6; feed_post=6*10=60
#[case(
    r#"
x = 0
o = defer()
o << x
for i in [1, 2, 3]:
    o << x
    x = x + i
    o << x * 10
o"#,
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: vec![0, 1, 1, 1, 2, 2, 2],
            variants: vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1, 2]),
            ],
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 0, 1, 3, 10, 30, 60]))),
        domain_predicate: Predicate::Union(vec![Predicate::True, Predicate::True, Predicate::True]),
        deleted: BitSet::new(),
    }
)]
#[ignore] // TODO support nested loops with mutations.
#[case(
    r#"
x = 0
for i in [1, 2]:
    for j in [10, 20]:
        x = x + i + j
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![33]))
)]
#[ignore] // TODO support nested loops with mutations.
#[case(
    r#"
x = 0
o = defer()
for i in [1, 2]:
    for j in [10, 20]:
        x = x + i + j
        o << x
o"#,
    Tile::Scalar(ColumnValue::Strings(vec!["TODO".into()]))
)]
fn test_mutability(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}
