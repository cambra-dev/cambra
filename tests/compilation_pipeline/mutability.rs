//! Mutation loops: loop-carried accumulators, multi-accumulator loops, and
//! feeds interleaved with mutations.

use std::collections::HashMap;
use std::time::Duration;

use bit_set::BitSet;
use indoc::indoc;

use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program, render_errors};
use cambra::interpreter::{ColumnValue, Consumer, Predicate, Tile, Value};
use rstest_log::rstest;

use cambra::ccl::TagMap;

use crate::helpers::*;

#[rstest]
#[timeout(Duration::from_secs(10))]
#[case(
    r#"
x := 0
for i in [1, 2, 3]:
    x += i
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![6]))
)]
// A mutable variable seeded from a **computed** expression rather than a literal.
//
// Every other case here seeds from a bare literal, which is a weaker exercise of the
// mutable variable law than it looks: a projection *selects*, so `r.a` carries the field's
// refinement into the seed, and the mutable variable's value type is right only because the
// loop's writes join with it. A seed contributes verbatim and the join is the lattice's
// — the intersection over every contribution — so the refinement drops out here and the
// mutable variable types as `Mut(Int)`.
#[case(
    r#"
r = (a=0, b=9)
x := r.a
for i in [1, 2, 3]:
    x += i
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![6]))
)]
// The same seed with **no writes at all**. The join has one member, so the mutable variable
// keeps its seed's refinement — and that is correct, since it really does hold that
// value at every position. Nothing pre-emptively widens it.
#[case(
    r#"
r = (a=7, b=9)
x := r.a
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![7]))
)]
// A mutable variable whose only write goes **through a `Mut` parameter**. The write is not
// lexically visible at `x`, so the join needs the call itself to contribute: passing a
// mutable variable to a `Mut(V)` parameter means the callee may write any `V` there.
//
// Without that contribution the mutable variable's value type was left claiming its seed
// (`{Int | __elem == 0}`) while the parameter demanded `Mut(Int)`, and since `Mut` is
// invariant the call was rejected outright. The ordinary application edges cannot supply
// it — `apply` records `arg <: d` against a *fresh variable*, so a `Mut` argument meets
// an `Infer` and takes the deliberate deref arm, which is right for a bare read
// (`cnt + 1`) and drops the handle here.
#[case(
    r#"
def fw(c: Mut(Int)):
  c += 1
x := 0
for i in [1, 2, 3]:
  fw(x)
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![3]))
)]
// The same contribution at an argument position that is **not the first**. A call is
// curried, and `apply` types each application as a fresh variable, so the type of the
// function being applied says nothing about this parameter — the contribution has to
// come off the head of the spine (`parameter_type`). Reading it off the applied type
// instead covers `fw(x, n)` and silently skips this, which then fails the invariance
// check against `Mut(Int)` because the mutable variable still claims its seed.
#[case(
    r#"
def fw(n: Int, c: Mut(Int)):
  c += n
x := 0
for i in [1, 2, 3]:
  fw(2, x)
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![6]))
)]
// Two mutable variables in one call: every argument position is walked, not just one.
#[case(
    r#"
def fw(a: Mut(Int), b: Mut(Int)):
  a += 1
  b += 2
x := 0
y := 0
for i in [1, 2, 3]:
  fw(x, y)
(x, y)"#,
    Tile::Record(HashMap::from([
        ("_0".into(), Tile::Scalar(ColumnValue::Ints(vec![3]))),
        ("_1".into(), Tile::Scalar(ColumnValue::Ints(vec![6]))),
    ]))
)]
// A mutable variable reaching its writer through *two* calls. The inner call's contribution is
// `Mut(Int)`'s value against the outer parameter's, so the mutable variable's join closes over
// the whole forwarding chain rather than just the frame it was named in.
#[case(
    r#"
def inner(c: Mut(Int)):
  c += 1
def outer(n: Int, c: Mut(Int)):
  inner(c)
x := 0
for i in [1, 2, 3]:
  outer(7, x)
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![3]))
)]
// The `:=` operator marks mutability syntactically — a bare `x := 0` induction
// accumulator (no `Mut(…)` annotation) written with `x := x + i`.
#[case(
    r#"
x := 0
for i in [1, 2, 3]:
    x := x + i
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![6]))
)]
// The accumulator's value type can be spelled concretely: `Mut(Int)`
// annotates the binding at `Int` (checked against init and updates).
#[case(
    r#"
x: Mut(Int) := 0
for i in [1, 2, 3]:
    x += i
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![6]))
)]
#[case(
    r#"
x := 0
for i in []:
    x += 1
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![0]))
)]
#[case(
    r#"
x := 0
for i in [1, 2, 3]:
    x := x + i + 1
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![9]))
)]
#[case(
    r#"
x := 0
o = defer()
for i in [1, 2, 3]:
    x := x + i
    o << x
o"#,
    make_int_list(&[1,3,6])
)]
#[case(
    r#"
x := 0
o = defer()
o << x
for i in [1, 2, 3]:
    x := x + i
    o << x
for j in [4, 5]:
    x := x + j
    o << x
o"#,
    Tile::SealedFunction {
        // Tags map each domain entry to its source variant: index 0 (pre-loop
        // feed of `x = 0`) → variant 0; indices 1-3 (loop1 running sums) →
        // variant 1; indices 4-5 (loop2 running sums) → variant 2.
        domain: ColumnValue::positional_union(&[0, 1, 1, 1, 2, 2], vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1]),
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 1, 3, 6, 10, 15]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    })]
// Pre-mutation let `y = x + 1` introduces a non-trivial let that survives
// lambda_elim as `(let y = … in …) ▷ const` (the loop body doesn't depend
// on `i`).  This exercises the const-of-function shortcut in op-conversion
// — without it, op-conversion tries to const-lift a function-tiled value.
#[case(
    r#"
x := 0
for i in [1, 2, 3]:
    y = x + 1
    x := y * 2
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
x := 0
for i in [1, 2, 3]:
    y = x + i
    x := y * 2
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![22]))
)]
#[case(
    r#"
x := 1
y := 0
for i in [1, 2, 3]:
    y := y + i
    x := x * i
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
x := 1
y := 0
o = defer()
for i in [1, 2, 3]:
    y := y + i
    x := x * i
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
x := 1
y := 10
o = defer()
for i in [1, 2, 3]:
    o << x + y
    x := x + i
    y := y * i
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
x := 0
o = defer()
for i in [1, 2, 3]:
    x := x + i
    o << x
    o << x + 100
o"#,
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 0, 0, 1, 1, 1], vec![
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1, 2]),
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 3, 6, 101, 103, 106]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])),
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
x := 0
o = defer()
o << x
for i in [1, 2, 3]:
    o << x
    x := x + i
    o << x * 10
o"#,
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 1, 1, 1, 2, 2, 2], vec![
                ColumnValue::Units(1),
                ColumnValue::UInts(vec![0, 1, 2]),
                ColumnValue::UInts(vec![0, 1, 2]),
            ]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 0, 1, 3, 10, 30, 60]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    }
)]
// Pass-by-reference `Mut` param, driven by a loop: `bump(c)` writes its
// pass-by-ref mutable variable on each iteration. `bump(cnt)` inlines to `MutWrite(cnt,
// cnt + 1)`, and the letrec phase reads the hidden write off the `For` marker
// as an accumulator recurrence: 0 → 1 → 2 → 3 over [1, 2, 3].
#[case(
    r#"
def bump(c: Mut(Int)):
    c += 1
cnt: Mut(Int) := 0
for x in [1, 2, 3]:
    bump(cnt)
cnt"#,
    Tile::Scalar(ColumnValue::Ints(vec![3]))
)]
// The same pass-by-ref writer applied once, outside any loop: the inlined
// `MutWrite(cnt, cnt + 1)` normalizes to a shadowing `let`, so `cnt` reads 1.
#[case(
    r#"
def bump(c: Mut(Int)):
    c += 1
cnt: Mut(Int) := 0
bump(cnt)
cnt"#,
    Tile::Scalar(ColumnValue::Ints(vec![1]))
)]
// Two independent mutation loops of *different* domain lengths, both read in
// one trailing expression. `a` accumulates over [0,1] (→ 2), `b` over [0,2]
// (100 → 103). Regression: combining the two extracted finals must wait for
// *both* loops to converge — the shorter loop (`a`) converging first must not
// declare the whole result terminal and read `b` as an empty (→ 0) arm.
#[case(
    r#"
a := 0
b := 100
for x in [1, 2]:
    a += 1
for x in [1, 2, 3]:
    b += 1
a * 1000 + b"#,
    Tile::Scalar(ColumnValue::Ints(vec![2103]))
)]
// As above, but the longer loop reads the shorter loop's final mutable-variable value:
// `b += a` broadcasts `a` (= 2) across [0,2]: 100 → 102 → 104 → 106.
// Broadcasting the not-yet-converged `a` must yield an empty (non-terminal)
// contribution, not panic on a `repeat`-of-empty.
#[case(
    r#"
a := 0
b := 100
for x in [1, 2]:
    a += 1
for x in [1, 2, 3]:
    b += a
a * 1000 + b"#,
    Tile::Scalar(ColumnValue::Ints(vec![2106]))
)]
// A pass-by-ref writer whose body is *two* statements, applied once outside a
// loop. Inlining splices `ExprStmt(ExprStmt(cnt := cnt+1, cnt := cnt+2), cnt)`;
// flat-spine normalization un-nests it so both writes land on the spine.
#[case(
    r#"
def bump2(c: Mut(Int)):
    c += 1
    c += 2
cnt: Mut(Int) := 0
bump2(cnt)
cnt"#,
    Tile::Scalar(ColumnValue::Ints(vec![3]))
)]
// A pass-by-ref writer applied in *value* position (`y = bump(cnt)`). Inlining
// binds `y` to a bare `MutWrite`; flat-spine normalization hoists the write onto
// the spine (its value is `unit`), so the mutable-variable advance reaches the trailing read.
#[case(
    r#"
def bump(c: Mut(Int)):
    c += 1
cnt: Mut(Int) := 0
y = bump(cnt)
cnt"#,
    Tile::Scalar(ColumnValue::Ints(vec![1]))
)]
// A top-level mutable write followed by a read: the terminal-write path shadows
// `cnt` so the read observes the advanced value.
#[case(
    r#"
cnt := 0
cnt += 1
cnt"#,
    Tile::Scalar(ColumnValue::Ints(vec![1]))
)]
// I1(b): a non-`Mut` annotated local (`y: Int = …`) inside a mutation-loop
// body lowers as an ordinary per-iteration annotated `let`, not rejected.
// Per iter: y = 2·i; acc += y over [1,2,3] → 2+4+6 = 12.
#[case(
    r#"
acc := 0
for i in [1, 2, 3]:
    y: Int = i * 2
    acc += y
acc"#,
    Tile::Scalar(ColumnValue::Ints(vec![12]))
)]
#[ignore] // TODO support nested loops with mutations.
#[case(
    r#"
x := 0
for i in [1, 2]:
    for j in [10, 20]:
        x := x + i + j
x"#,
    Tile::Scalar(ColumnValue::Ints(vec![33]))
)]
// A **conditional feed** riding an accumulator loop: the `o << i` fires only on
// the guard's route, so the tap stream carries just the fired positions (loop
// positions 1, 2 where i = 20, 30). `transform_chain` gives the feed a
// `to_o__fire` gate; the `InductionStore` omits the tap from a non-firing
// position's delta, and `StoreDenseRead` (non-carry) reads only fired positions.
#[case(
    r#"
o = defer()
cnt := 0
for i in [10, 20, 30]:
    cnt := cnt + 1
    if i > 15:
        o << i
o"#,
    Tile::SealedFunction {
        domain: ColumnValue::from_uints(vec![1, 2]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![20, 30]))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
)]
// A **conditional write** with an unconditional feed after it: `cnt` increments
// only when `i > 15`, and `o << cnt` fires every position. The post-`if` feed
// duplicates onto both paths (mutually exclusive guards), so the tap rides two
// disjoint fire routes: positions 1, 2 (guard held → cnt 1, 2) and position 0
// (carry → cnt 0). As a function that is 0 ↦ 0, 1 ↦ 1, 2 ↦ 2.
#[case(
    r#"
o = defer()
cnt := 0
for i in [10, 20, 30]:
    if i > 15:
        cnt := cnt + 1
    o << cnt
o"#,
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 0, 1], vec![ColumnValue::from_uints(vec![1, 2]), ColumnValue::from_uints(vec![0])]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 0]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    }
)]
// A full `if/else` write with a trailing feed: each position takes exactly one
// arm (`i < 2` → `x += i`, else `x += 100`) and feeds the post-arm `x`. The two
// arms partition the loop domain, so the tap rides two disjoint routes. As a
// function: 0 ↦ 0, 1 ↦ 1, 2 ↦ 101, 3 ↦ 201.
#[case(
    r#"
o = defer()
x := 0
for i in [0, 1, 2, 3]:
    if i < 2:
        x := x + i
    else:
        x := x + 100
    o << x
o"#,
    Tile::SealedFunction {
        domain: ColumnValue::positional_union(&[0, 0, 1, 1], vec![ColumnValue::from_uints(vec![0, 1]), ColumnValue::from_uints(vec![2, 3])]),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 1, 101, 201]))),
        domain_predicate: Predicate::Union(TagMap::from_positional(vec![Predicate::True, Predicate::True])),
        deleted: BitSet::new(),
    }
)]
#[ignore] // TODO support nested loops with mutations.
#[case(
    r#"
x := 0
o = defer()
for i in [1, 2]:
    for j in [10, 20]:
        x := x + i + j
        o << x
o"#,
    Tile::Scalar(ColumnValue::Strings(vec!["TODO".into()]))
)]
fn test_mutability(#[case] code: &str, #[case] expected: Tile) {
    check_tile(code, expected);
}

// ---------------------------------------------------------------------------
// Second-class `Mut` discipline (`src/ccl/design/mutability.md`, "No aliasing:
// `Mut` values are second-class (downward-only)"). A mutable value must stay
// traceable to one introduction: it may only be a bare variable reference
// (rule 1), never nested in a composite type or returned from a function
// (rule 2). There is no rule about an unannotated binding holding a `Mut`: only
// a `MutDecl` and a pass-by-reference param can bind one.
// ---------------------------------------------------------------------------

/// Compile `code`, expect failure, and assert the rendered errors contain
/// `needle`.
fn expect_mut_discipline_error(code: &str, needle: &str) {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let errs = match compile_program(&mut ctx, code, consumer) {
        Ok(_) => panic!(
            "expected a Mut-discipline error containing {needle:?}, but the program compiled"
        ),
        Err(e) => e,
    };
    let rendered = render_errors(&errs, "<mut-discipline-test>", code);
    assert!(
        rendered.contains(needle),
        "expected a Mut-discipline error containing {needle:?}, got:\n{rendered}"
    );
}

/// Compile `code`, expect failure, and assert the rendered errors contain
/// `needle`. The kind-agnostic sibling of [`expect_mut_discipline_error`], for
/// surface diagnostics that surface at lowering or channelization.
fn expect_compile_error(code: &str, needle: &str) {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let errs = match compile_program(&mut ctx, code, consumer) {
        Ok(_) => panic!("expected a compile error containing {needle:?}, but the program compiled"),
        Err(e) => e,
    };
    let rendered = render_errors(&errs, "<compile-error-test>", code);
    assert!(
        rendered.contains(needle),
        "expected a compile error containing {needle:?}, got:\n{rendered}"
    );
}

/// A `+=` (or `:=` write) to a plain `=` binding is rejected: writes require a
/// mutable variable, they never mean shadowing. Introduce the mutable variable with `:=`.
///
/// This is also what pins the *skipped* half of the write rule. A target that is not
/// a mutable variable
/// gets **no** type constraint at all — the diagnosis belongs to the mutability
/// discipline, and a type error raised at the write would pre-empt it with a worse
/// message. The write's own demand is exercised by
/// [`write_of_the_wrong_type_is_rejected_against_the_mut_vars_value_type`].
#[test]
fn augmented_assignment_to_non_mutable_rejected() {
    expect_mut_discipline_error("x = 0\nx += 1\nx", "not a mutable variable");
}

/// The same rejection when the target's binder is **gone by the time the check runs**.
///
/// `def f(…)` binds a generalized `let`, and coalesce rebuilds a generalized `let` as the
/// chain of its per-use specializations — an empty chain, and no binder at all, when the
/// only mention of `f` is the write. The write survives naming a binder that no longer
/// exists, so a check keyed on "the binder says it is not mutable" finds nothing to
/// object to. A write target must *resolve to a mutable binder*, and an absent one
/// satisfies that no better than an immutable one does.
///
/// The program has to leave `f` otherwise unread: a later `f + 1` is an ordinary type
/// error against the function type, and inference reports that before the discipline
/// check runs at all.
#[test]
fn a_write_to_a_binder_monomorphization_dropped_is_rejected() {
    expect_mut_discipline_error(
        indoc! {r#"
        def f(v):
            v + 1
        f := 10
        1
    "#},
        "not a mutable variable",
    );
}

/// The other half: when the target *is* a mutable variable, the write is demanded
/// against the variable's real value type — the demand is not relaxed to buy diagnostic ordering.
/// `Mut(Int)` genuinely demands `Int` of every write.
#[test]
fn write_of_the_wrong_type_is_rejected_against_the_mut_vars_value_type() {
    expect_compile_error(
        indoc! {r#"
            x: Mut(Int) := 0
            for i in [1]:
                x := "s"
            x
        "#},
        "write to mutable variable `x`",
    );
}

/// `Mut(…)` takes one or two type arguments (`Mut(V)` or `Mut(V, Txn)`); three
/// is rejected at lowering.
#[test]
fn mut_annotation_with_too_many_arguments_rejected() {
    expect_compile_error(
        "x: Mut(Int, Txn, Int) := 0\nx",
        "takes one or two arguments",
    );
}

/// The only explicit `Mut` sequencing domain is `Txn`; any other second argument
/// (`Mut(V, Foo)`) is rejected — omit it (`Mut(V)`) to infer a loop's induction
/// domain.
#[test]
fn mut_annotation_with_non_txn_domain_rejected() {
    expect_compile_error(
        "x: Mut(Int, Foo) := 0\nx",
        "only explicit `Mut` sequencing domain is `Txn`",
    );
}

/// A mutable variable *declared inside* a for-loop body (rather than before it) is
/// rejected: its sequencing domain is the loop's own iteration extent, so the body
/// would carry a nested recurrence the unified phase has no domain for.
///
/// Rejected at **every spelling**, because whether the introduction carries a type
/// annotation says nothing about whether it introduces a mutable variable. Gating on the
/// annotation instead accepted the bare `y := 0` — which then fell back to a
/// per-iteration shadowing `let`, silently discarding each update at the iteration
/// boundary, the very thing `:=` exists to avoid. (The spellings are the ones a
/// `:=` binder accepts at all — see `mut_decl_annotation_is_exact_and_is_a_mut`.)
#[rstest]
#[case::annotated_mut(indoc! {r#"
    t := 0
    for i in [1, 2, 3]:
        y: Mut(Int) := i
        t += y
    t
"#})]
#[case::bare(indoc! {r#"
    t := 0
    for i in [1, 2, 3]:
        y := i
        t += y
    t
"#})]
#[case::annotated_txn(indoc! {r#"
    t := 0
    for i in [1, 2, 3]:
        y: Mut(Int, Txn) := i
        t += y
    t
"#})]
fn register_declared_inside_loop_rejected(#[case] code: &str) {
    expect_compile_error(code, "introduced inside a for-loop body");
}

/// An annotation on a `:=` binder is **exact** and is a **`Mut(…)`**. Both halves
/// are rejections rather than reinterpretations, and they share one diagnostic
/// because they share one remedy.
///
/// A plain value type names the wrong thing — `y: Int := 0` binds `y` at
/// `Mut(Int, D)`, not at `Int`, so reading the annotation as the value type would
/// make `:` mean something at a `:=` binder that it means at no other. And `<:`
/// claims nothing `:` does not: `Type::History` is invariant in both payloads, so
/// the only type below `Mut(V, D)` is `Mut(V, D)` itself.
#[rstest]
#[case::bare_value_exact("y: Int := 0\ny")]
#[case::bare_value_bounded("y <: Int := 0\ny")]
#[case::mut_bounded("y <: Mut(Int) := 0\ny")]
#[case::mut_txn_bounded("y <: Mut(Int, Txn) := 0\ny")]
fn mut_decl_annotation_is_exact_and_is_a_mut(#[case] code: &str) {
    expect_compile_error(code, "is not a valid mutable-variable annotation");
}

/// The remedy the diagnostic names is the one that compiles, in both the plain and
/// the transactional case — the rejection is not hiding a second problem.
#[test]
fn the_exact_mut_spelling_the_diagnostic_names_compiles() {
    check_scalar(
        indoc! {r#"
            y: Mut(Int) := 0
            y += 5
            y
        "#},
        cambra::interpreter::Value::Int(5),
    );
}

/// A `Mut(…)` annotation is exact wherever it is written, so the same invariance
/// argument rejects a bounded pass-by-reference parameter.
#[test]
fn a_bounded_mut_param_is_rejected() {
    expect_compile_error(
        indoc! {r#"
            def bump(c <: Mut(Int)):
                c := c + 1
            cnt: Mut(Int) := 0
            for i in [1, 2, 3]:
                bump(cnt)
            cnt
        "#},
        "invariant in its value type",
    );
}

/// `op=` inside a for-loop body is a **mutable write**, so a target that is not a
/// mutable variable declared before the loop is a type error rather than a rebind —
/// the spec's *"a `+=` to an immutable binding is a type error, not a silent
/// rebind"*.
///
/// The fallback this replaces was a per-iteration shadowing `let`, wrong twice over:
/// the update is discarded at the iteration boundary, and since `op=` reads the old
/// value, each iteration read the binding's *initial* value rather than the running
/// one. It is the `op=` half of the same hole the `:=` rejection above closes.
#[rstest]
#[case::body_local(indoc! {r#"
    t := 0
    for i in [1, 2, 3]:
        y = 0
        y += i
        t += y
    t
"#})]
#[case::iteration_variable(indoc! {r#"
    t := 0
    for i in [1, 2, 3]:
        i += 1
        t += i
    t
"#})]
// The generator path (a `yield` body with no loop-carried writes) reaches its own
// statement lowering, and had the same fallback.
#[case::generator_body(
    indoc! {r#"
        def g(xs):
            for x in xs:
                y = 0
                y += x
                yield y
        g([1, 2, 3])
    "#}
)]
fn aug_assign_to_a_non_mutable_inside_a_loop_is_rejected(#[case] code: &str) {
    expect_compile_error(code, "is not a mutable variable");
}

/// The immutable counterpart still works, and is what the rejection above points
/// at: a per-iteration value binds with `=`.
#[test]
fn per_iteration_value_binding_inside_a_loop_is_allowed() {
    check_scalar(
        indoc! {r#"
            t := 0
            for i in [1, 2, 3]:
                y = i
                t += y
            t
        "#},
        cambra::interpreter::Value::Int(6),
    );
}

/// A `Mut(…)` annotation with the immutable `=` operator is contradictory —
/// `Mut` introduces a mutable variable, which is `:=`'s job. Rejected at lowering, pointing
/// at `:=`.
#[test]
fn mut_annotation_with_plain_equals_is_rejected() {
    expect_compile_error("x: Mut(Int) = 0\nx", "use `:=` instead");
}

/// A plain `=` to a mutable variable bound outside a loop is a mistaken accumulator: `=`
/// binds immutably, so it would be a per-iteration shadow that silently discards
/// each update. Rejected pointing at `:=` — including when the loop is the
/// block's *final* statement (the position that once slipped past the guard and
/// compiled to a silent no-op).
#[test]
fn plain_equals_to_outer_mutable_in_final_loop_is_rejected() {
    let code = "cnt := 0\nfor i in [1, 2, 3]:\n    cnt = cnt + 1\n    i";
    expect_compile_error(code, "binds immutably");
}

/// A reference *cycle* among defer channels (`x <<= y; y <<= x`) has no
/// well-founded solution — channels carry no guard — so it is rejected rather
/// than looped on.
#[test]
fn cross_channel_cycle_is_rejected() {
    let code = "x = defer()\ny = defer()\nx <<= y\ny <<= x\nx";
    expect_compile_error(code, "mutually recursive cycle");
}

/// `b = a` off a mutable **reads** it — a value snapshot, exactly as `a + 1` or
/// `f(a)` read it. There is no alias to reject, because a `Let` cannot bind a
/// mutable variable: only `MutDecl` (`:=`) and a pass-by-reference `Mut` parameter can, so
/// the copy is an ordinary value binding by construction.
#[test]
fn plain_assignment_off_a_mutable_is_a_value_read() {
    check_scalar(
        indoc! {r#"
            a := 0
            a += 5
            b = a
            b
        "#},
        cambra::interpreter::Value::Int(5),
    );
}

/// And the copy is *not* mutable, so writing through it is rejected — which is
/// what used to need rule 3, and now falls out of the write-target check. The
/// error names the write (the actual mistake) rather than the binding.
#[test]
fn writing_through_a_value_copy_of_a_mutable_is_rejected() {
    expect_mut_discipline_error(
        indoc! {r#"
        a := 0
        b = a
        b += 1
        b
    "#},
        "not a mutable variable",
    );
}

/// A mutable variable's **value type is invariant** across a pass-by-reference boundary:
/// the callee's declared value type may be neither narrower nor wider than the
/// caller's mutable variable.
///
/// Narrowing is the unsound direction and the reason invariance exists. If
/// `Mut({a: Int, b: Int})` could flow into a `Mut({a: Int})` parameter, the callee's
/// `r := (a=5)` would drop a field the caller's declaration still promises, and the
/// caller's later `x.b` would type-check against a value that no longer has it.
///
/// Both directions are rejected today, but *not* by one rule. At an argument position
/// the deref coercion fires first — `apply` records `arg <: ?d` against a fresh
/// variable, so a mutable variable meets an `Infer` and reads through — which means the
/// `(History, History)` invariance rule never runs there. Narrowing is caught instead
/// by the write contribution (`emit::contribute_pbr_writes`, `param_value <:
/// arg_value`) and widening by the ordinary application edge. These tests pin the
/// *property* so that consolidating those mechanisms cannot quietly drop it.
#[test]
fn a_mut_vars_value_type_is_invariant_across_a_mut_parameter() {
    // Narrowing: the callee would drop `b`, and the diagnostic names that field —
    // `.b` is the whole of what makes this unsound, so it is a sharper needle than
    // the kind of error it happens to be reported as.
    expect_compile_error(
        indoc! {r#"
            def narrow(r: Mut({a: Int})):
                r := (a=5)
            x: Mut({a: Int, b: Int}) := (a=1, b=2)
            for i in [1]:
                narrow(x)
            x.b
        "#},
        ".b",
    );
    // Widening: the callee would demand a field the mutable variable does not have — again
    // `.b`, from the other side.
    expect_compile_error(
        indoc! {r#"
            def wide(r: Mut({a: Int, b: Int})):
                r := (a=5, b=6)
            x: Mut({a: Int}) := (a=1)
            for i in [1]:
                wide(x)
            x.a
        "#},
        ".b",
    );
}

/// The equal-width case still works, which is what makes the two rejections above a
/// statement about *variance* rather than about pass-by-reference being broken.
#[test]
fn an_equal_width_mut_parameter_still_accepts_a_mut_var() {
    check_scalar(
        indoc! {r#"
            def bump(r: Mut(Int)):
                r += 1
            x: Mut(Int) := 0
            for i in [1, 2, 3]:
                bump(x)
            x
        "#},
        cambra::interpreter::Value::Int(3),
    );
}

/// A type refinement cannot depend on a mutable variable — a **staging** limitation,
/// deliberately reported rather than worked around.
///
/// A comprehension filter's predicate rides the domain type as a refinement, so
/// filtering on a mutable variable produces a type mentioning it. A `let` binder can be
/// discharged into the type it is lifted out of, because the binder *is* its bound
/// expression; a mutable variable has no such term *at the point closure is demanded*. That is
/// the whole obstacle: closure is required during coalesce, and `mut_elim` — several
/// passes later — is what compiles a write-free mutable variable into a `let` and a written one
/// into trailing `let x_final = final_or_default(…)` bindings. The naming exists; it
/// just arrives too late to discharge with.
///
/// Lifting it is scoped rather than impossible (see
/// [`InferError::MutableInRefinedType`](cambra::ccl::infer::InferError)), with one
/// genuinely hard sub-case left over: a comprehension inside the loop that writes the
/// mutable variable, where the value is per-iteration and a predicate — riding a type — has no
/// position to depend on.
///
/// Reading it into an immutable first does **not** help today, which is why the message
/// offers no workaround: discharging `[k ↦ x]` puts the mutable variable's name straight back
/// into the predicate.
///
/// Before this was reported here it tripped `check_scope_valid`, a debug-only
/// regression net documented as never firing on a well-typed program — so a *release*
/// build had no check at all and reached the pre-channelize wall with a surviving mutable
/// type.
#[rstest]
#[case::direct(indoc! {r#"
    x := 2
    ys = [i for i in [1, 2, 3] if i < x]
    ys
"#})]
#[case::through_a_copy(indoc! {r#"
    x := 2
    k = x
    ys = [i for i in [1, 2, 3] if i < k]
    ys
"#})]
#[case::after_writes(
    indoc! {r#"
        x := 0
        for i in [1, 2]:
            x += i
        k = x
        ys = [j for j in [1, 2, 3] if j < k]
        ys
    "#}
)]
fn a_refinement_cannot_depend_on_a_mutable(#[case] code: &str) {
    expect_compile_error(code, "depends on the mutable variable");
}

/// Rule 2: a function may not return a `Mut` — the mutable-variable reference would
/// escape where its writer set is no longer statically known.
#[test]
fn rule2_function_returning_mut_is_rejected() {
    expect_mut_discipline_error("x := 0\nf = \\z -> x\nf", "inside a composite type");
}

/// The escape is rejected **however many tail positions sit between the function
/// boundary and the read**, which is not free: a tail position reports its
/// continuation's *value*, so an intervening statement or binding derefs the handle
/// out of the enclosing node's type. Rule 2 therefore asks what the body *denotes*
/// rather than what its root node is stamped with.
///
/// Without that, inserting a line changed the verdict — and not to an acceptance but
/// to a compiler panic, since the lambda's stamped codomain (`Int`) then disagreed
/// with its body's own type (`Mut(Int, ?d)`) at the post-inference consistency wall.
#[rstest]
#[case::through_a_binding(indoc! {r#"
    def f(c: Mut(Int)):
        y = 1
        c
    x := 0
    f(x)
"#})]
#[case::through_a_statement(indoc! {r#"
    def f(c: Mut(Int)):
        c += 1
        c
    x := 0
    f(x)
"#})]
#[case::through_a_mut_var_introduction(indoc! {r#"
    def f(c: Mut(Int)):
        z := 1
        c
    x := 0
    f(x)
"#})]
// A mutable variable does not escape its own introduction either: returning one declared
// *inside* the function is the same escape as returning a parameter.
#[case::its_own_mut_var(indoc! {r#"
    def g(n):
        z := n
        z
    g(5)
"#})]
#[case::its_own_mut_var_through_a_binding(indoc! {r#"
    def g(n):
        z := n
        y = 2
        z
    g(5)
"#})]
fn rule2_is_not_evaded_by_a_tail_position(#[case] code: &str) {
    expect_mut_discipline_error(code, "inside a composite type");
}

/// The complement, and why the rule cannot simply refuse to deref a tail: a program
/// whose own tail reads its accumulator yields that accumulator's **value**. Nothing
/// escapes — there is no function boundary — so the deref is what makes the ordinary
/// case work, and the check above is what keeps it from covering for an escape.
#[test]
fn a_programs_tail_read_of_its_accumulator_is_a_value() {
    check_scalar(
        indoc! {r#"
            x := 0
            for i in [1, 2, 3]:
                x += i
            y = 1
            x
        "#},
        cambra::interpreter::Value::Int(6),
    );
}

/// Rule 1: an argument to a `Mut` parameter must be a bare variable reference,
/// so a *conditional* selecting between two mutable variables — which one would
/// the callee's write target? — is rejected. The check reads the argument node,
/// not its type: a conditional over two mutable variables reads their *values* (a
/// mutable read derefs into the arms' join, as it does into a tuple element), so
/// there is no `Mut` on the selection itself to key on.
#[test]
fn rule1_selected_mut_argument_is_rejected() {
    expect_mut_discipline_error(
        "def bump(c: Mut(Int)):\n    c += 1\nx := 0\ny := 1\nbump(x if True else y)\nx",
        "bare variable reference",
    );
}

/// The dual of rule 2's tuple rejection: a tuple of *bare mutable reads* is a
/// tuple of their **values** (reads deref in composite positions), so its
/// type is `(int, int)` with no `Mut` nested — it compiles cleanly. (`case_09`
/// exercises the running result end-to-end; this pins that the discipline pass
/// itself does not reject it.)
#[test]
fn tuple_of_mut_reads_compiles_as_values() {
    let code = "x := 1\ny := 0\nfor i in [1, 2, 3]:\n    y := y + i\n    x := x * i\n(x, y)";
    let mut ctx = GlobalContext::default();
    compile_program(&mut ctx, code, Box::new(|| {})).unwrap_or_render("<tuple-mut-reads>", code);
}

/// A top-level mutable write as the program's *final* statement — no trailing
/// read. Flat-spine normalization terminalizes the bare `MutWrite` to
/// `ExprStmt(MutWrite, unit)`, so the program is `Unit`-valued (the mutable variable's
/// final state is simply unobserved) and compiles rather than tripping the
/// strict-typecheck wall the raw bare-final write used to hit.
#[test]
fn final_mutable_write_with_no_read_compiles_as_unit() {
    let code = "cnt := 0\ncnt += 1";
    let mut ctx = GlobalContext::default();
    compile_program(&mut ctx, code, Box::new(|| {}))
        .unwrap_or_render("<final-mutable-write>", code);
}

/// I1(a): a `Mut(…)` accumulator loop as the program's *final* statement, with
/// no trailing read, is a valid mutation loop — `lower_final_stmt` now mirrors
/// `lower_middle_stmt`'s mutation-loop dispatch (continuation `Unit`) instead
/// of routing to the generator-for fallback, whose "must end in a yield/feed"
/// rejection produced a confusing error here. The loop's final value is simply
/// unobserved (`Unit`), so the program compiles.
#[test]
fn final_mutation_loop_with_no_read_compiles_as_unit() {
    let code = "total := 0\nfor i in [1, 2, 3]:\n    total += i";
    let mut ctx = GlobalContext::default();
    compile_program(&mut ctx, code, Box::new(|| {}))
        .unwrap_or_render("<final-mutation-loop>", code);
}

// ===== Bottom-PR review regressions: Mut scoping / guards =====
#[test]
fn mut_registry_does_not_leak_into_a_shadowing_param() {
    check_scalar(
        "n: Mut(Int) := 0\ndef h(n: Int):\n    n = n + 1\n    n\nh(10)",
        cambra::interpreter::Value::Int(11),
    );
}
#[test]
fn mut_collection_as_for_source_derefs() {
    check_scalar(
        "xs := [1, 2, 3]\ntotal := 0\nfor i in xs:\n    total := total + i\ntotal",
        cambra::interpreter::Value::Int(6),
    );
}
// Multi-parameter pass-by-reference: a `Mut` parameter alongside a plain one is
// curried into a chain of named lambdas (a `Mut` param must stay a named binder
// so inlining renames its `MutWrite` target to the caller's mutable variable) and inlined
// at the call site. The plain parameter rides the same call.
#[test]
fn multi_param_pass_by_ref_assign_works() {
    check_scalar(
        "def add_to(c: Mut(Int), amt: Int):\n    c := c + amt\ncnt: Mut(Int) := 0\nadd_to(cnt, 5)\ncnt",
        cambra::interpreter::Value::Int(5),
    );
}
#[test]
fn multi_param_pass_by_ref_augassign_works() {
    check_scalar(
        "def f(c: Mut(Int), d: Int):\n    c += d\ncnt: Mut(Int) := 0\nf(cnt, 7)\ncnt",
        cambra::interpreter::Value::Int(7),
    );
}
#[test]
fn mut_arg_must_be_a_mutable_not_a_plain_value() {
    expect_mut_discipline_error(
        "x = 7\ndef bump(c: Mut(Int)):\n    c := c + 1\nbump(x)\nx",
        "mutable variable",
    );
}
// A mutable variable passed to a *non*-`Mut` parameter is read by value (its
// current value is copied in) — the callee cannot write it back. The parameter
// annotation is a plain checking-mode declaration here, so the mutable variable's value
// type must match it.
#[test]
fn nonmut_param_reads_mut_arg_current_value() {
    check_scalar(
        "cnt: Mut(Int) := 5\ndef g(a: Int):\n    a + 1\ng(cnt)",
        cambra::interpreter::Value::Int(6),
    );
}
// The enforced annotation has force even when the argument is a mutable
// variable: a `String` parameter rejects an `Int` mutable variable's value. Before
// parameter annotations were carried through lowering this compiled — the
// annotation was silently dropped and `a` inferred `Int` from the argument.
#[test]
fn nonmut_param_annotation_enforced_against_mut_arg() {
    expect_compile_error(
        "cnt: Mut(Int) := 0\ndef g(a: String):\n    a\ng(cnt)",
        "mismatch",
    );
}
// Pass-by-reference sibling of the above: a `Mut(Int)` mutable variable cannot bind a
// `Mut(String)` parameter — the value types must agree across the `(Mut, Mut)`
// edge. (This path is unchanged by parameter-annotation enforcement; the `Mut`
// annotation always seeded the binder type. Pinned here because nothing else
// covers a `Mut` value-type clash at a call site.)
#[test]
fn mut_param_value_type_must_match_mut_arg() {
    expect_compile_error(
        "cnt: Mut(Int) := 0\ndef g(c: Mut(String)):\n    c := \"x\"\ng(cnt)\ncnt",
        "mismatch",
    );
}
#[test]
fn single_param_pass_by_ref_still_works() {
    check_scalar(
        "cnt: Mut(Int) := 0\ndef bump(c: Mut(Int)):\n    c := c + 1\nbump(cnt)\ncnt",
        cambra::interpreter::Value::Int(1),
    );
}
// Regression: a pass-by-reference writer that computes an *intermediate* binding
// before its mutable write (`tmp = c + 1; c := tmp`). Inlining splices the body as
// a `Let`-headed chain; `flatten_spine`'s hoist must lift the intermediate onto
// the statement spine alongside the write. Before the fix the write stayed
// trapped in the bound expression — silently returning `0` in value position and
// panicking ("marker survived") inside a loop.
#[test]
fn pass_by_ref_writer_with_intermediate_value_position() {
    check_scalar(
        "def f(c: Mut(Int)):\n    tmp = c + 1\n    c := tmp\ncnt: Mut(Int) := 0\ny = f(cnt)\ncnt",
        cambra::interpreter::Value::Int(1),
    );
}
#[test]
fn pass_by_ref_writer_with_intermediate_in_loop() {
    check_scalar(
        "def f(c: Mut(Int)):\n    tmp = c + 1\n    c := tmp\ncnt: Mut(Int) := 0\nfor i in [1, 2, 3]:\n    y = f(cnt)\ncnt",
        cambra::interpreter::Value::Int(3),
    );
}
// The writer applied as a *bare statement* (not `y = …`) with several
// intermediates: the body splices as a `Let`-chain in *effect* position, which
// `flatten_spine` must lift out of the `ExprStmt` effect too. 0 → +11 per iter.
#[test]
fn pass_by_ref_writer_with_intermediates_bare_statement_loop() {
    check_scalar(
        "def f(c: Mut(Int)):\n    a = c + 1\n    b = a + 10\n    c := b\ncnt: Mut(Int) := 0\nfor i in [1, 2, 3]:\n    f(cnt)\ncnt",
        cambra::interpreter::Value::Int(33),
    );
}
/// A bare `_` declares nothing, so `b: _ = a` is exactly `b = a`: a value read,
/// and writing through it is rejected the same way. This needed a special case
/// while the deref-copy was keyed on the annotation; now an initializer that is a mutable variable
/// reads through before any annotation is consulted, so `_` needs none.
#[test]
fn wildcard_annotated_copy_of_a_mutable_is_a_value_read() {
    check_scalar(
        indoc! {r#"
            a: Mut(Int) := 0
            a += 5
            b: _ = a
            b
        "#},
        cambra::interpreter::Value::Int(5),
    );
    expect_mut_discipline_error(
        indoc! {r#"
            a: Mut(Int) := 0
            b: _ = a
            b += 1
            b
        "#},
        "not a mutable variable",
    );
}
#[test]
fn typed_deref_copy_of_mut_still_works() {
    check_scalar(
        "a: Mut(Int) := 5\nb: Int = a\nb",
        cambra::interpreter::Value::Int(5),
    );
}

/// A deref-copy is a **snapshot at its position**, not an alias of the mutable variable: a
/// later write must not change the copied value. `x := 1; y: Int = x; x += 4; y`
/// is `1` (the value when `y` is bound), not `5`. Regression for the alias
/// inliner substituting `y → x` past a `MutWrite` — which reads the mutable variable's
/// post-write value — because the write is a `MutWrite`, not a `let` shadow the
/// rebind guard recognized. (The single-write `typed_deref_copy` above passes
/// even aliased, since the mutable variable never changes; this is the case that exposes
/// it.)
#[test]
fn deref_copy_snapshots_the_value_at_its_position() {
    check_scalar(
        "x: Mut(Int) := 1\ny: Int = x\nx += 4\ny",
        cambra::interpreter::Value::Int(1),
    );
}

/// The complements pinning positional semantics: the mutable read *after* the
/// write is the post-write value, and a trailing read of the mutable variable itself is its
/// final value.
#[test]
fn mutable_reads_are_positional() {
    check_scalar(
        "x: Mut(Int) := 1\nx += 4\ny: Int = x\ny",
        cambra::interpreter::Value::Int(5),
    );
    check_scalar(
        "x: Mut(Int) := 1\ny: Int = x\nx += 4\nx",
        cambra::interpreter::Value::Int(5),
    );
}

/// A deref-copy is a plain value, so copying it again is fine: `z = y` where
/// `y: Int = x` must compile (not trip the rule-3 "unannotated `Mut` alias"
/// error). Regression for the deref-copy being bound at the mutable type, which
/// made `y` a `Mut` alias in the type system and misfired the discipline on a
/// binding the user declared `Int`.
#[test]
fn deref_copy_is_a_value_not_a_mutable_alias() {
    check_scalar(
        "x: Mut(Int) := 1\ny: Int = x\nz = y\nz",
        cambra::interpreter::Value::Int(1),
    );
}

/// A mutable variable passed to a **value** parameter reads, and the read carries the mutable variable's
/// value type all the way through inlining.
///
/// The mutable variable is unwritten, so its value type is still its seed's singleton
/// (`Mut({Int | __elem == 5}, ?d)`), and a parameter whose type is left to inference takes
/// that refinement, because the call site is typed against the dereferenced value.
/// Beta-reduction then has to discharge a refinement demanded of the value against an
/// argument node still stamped with the handle: the `Mut` survives on the bare `Var` for
/// the phase to find the read. Reading through the handle is what makes the two
/// comparable; comparing the stamp directly asks a handle to entail a fact about a value
/// and trips `inline`'s entailment assert.
///
/// The last two cases are the surrounding ones that reach the same parameter *without* a
/// refinement, so a future narrowing of the read shows up as a difference between the
/// cases rather than as silence. Each is a distinct reason for the singleton not to
/// arrive: an exact annotation is a specialization boundary that fixes the domain at
/// `Int`, and a use demanding `Int` widens an inferred parameter. A **bounded**
/// annotation is not one of them — it constrains without fixing, so it lands on the
/// singleton exactly as no annotation does.
#[rstest]
#[case::unannotated(indoc! {r#"
    def id(v):
        v
    x := 5
    id(x)
"#})]
#[case::bounded(indoc! {r#"
    def id(v <: Int):
        v
    x := 5
    id(x)
"#})]
#[case::exact(indoc! {r#"
    def id(v: Int):
        v
    x := 5
    id(x)
"#})]
#[case::widened_by_use(indoc! {r#"
    def inc(v):
        v + 1
    x := 4
    inc(x)
"#})]
fn a_mut_var_passed_to_a_value_parameter_reads_its_value(#[case] code: &str) {
    check_scalar(code, cambra::interpreter::Value::Int(5));
}

/// The same read from *inside* the loop that writes the mutable variable — the combination the
/// cases above leave out. The value type is the join over seed and writes, so no
/// singleton survives and it is not the refinement branch that carries this one; what it
/// pins is that a mutable variable still reaches a UDF as a per-iteration read.
#[test]
fn a_mut_var_read_through_a_udf_inside_its_own_loop() {
    check_scalar(
        indoc! {r#"
            def id(v):
                v
            x := 5
            for i in [1, 2, 3]:
                x += id(x)
            x
        "#},
        cambra::interpreter::Value::Int(40),
    );
}

/// Writing a deref-copy is rejected — `y: Int = x` is immutable, so `y += 1` is
/// the "not a mutable variable" error, never a silent mutable write. Regression for a
/// write-site demand coalescing the `Int`-declared `y`'s `.ty` to `Mut` and the
/// write-target check trusting `.ty` over the annotation.
#[test]
fn write_to_deref_copy_rejected() {
    expect_mut_discipline_error(
        "x: Mut(Int) := 1\ny: Int = x\ny += 1\ny",
        "not a mutable variable",
    );
}

#[test]
fn genuine_mutable_still_accumulates() {
    check_scalar(
        "x: Mut(Int) := 0\nfor i in [1, 2, 3]:\n    x += i\nx",
        cambra::interpreter::Value::Int(6),
    );
}

// ---------------------------------------------------------------------------
// Curried-vs-tupled call-shape scoping (`mut_param_fns`). A `def` with a
// pass-by-reference `Mut` parameter lowers curried; every other `def` lowers
// tupled. The registry keying that choice is block-scoped and last-def-wins,
// so a `Mut`-param `def` cannot force the curried shape onto a same-named
// non-`Mut` `def`/call in a sibling/enclosing scope or after a redefinition.
// ---------------------------------------------------------------------------

/// Regression: a non-`Mut` `def` that redefines an earlier `Mut`-param `def` of
/// the same name in one block must lower its calls *tupled* (last definition
/// wins). Before the fix the earlier `Mut` registration stuck, so `f(10, 20)`
/// lowered curried (`20 ▷ (10 ▷ f)`) against a 2-tuple lambda — a miscompile.
#[test]
fn non_mut_redef_shadows_mut_param_fn_lowers_tupled() {
    check_scalar(
        "def f(c: Mut(Int)):\n    c += 1\ndef f(a, b):\n    a + b\nf(10, 20)",
        cambra::interpreter::Value::Int(30),
    );
}

/// Regression: a `Mut`-param `def` local to a nested scope (here a function
/// body) must not leak its curried call shape to a same-named top-level `def`.
/// Statement blocks lower right-to-left, so the top-level `bump(3, 4)` call is
/// lowered *after* `outer`'s body registers a nested `Mut`-param `bump`; without
/// block-scoping the leak made that call lower curried against the 2-tuple
/// top-level `bump`. `r = bump(3,4) = 7`; `outer(100)` bumps `y` once then adds
/// 100 → 101; total 108.
#[test]
fn nested_mut_param_fn_does_not_leak_to_outer_same_named_call() {
    check_scalar(
        "def bump(a, b):\n    a + b\nr = bump(3, 4)\ndef outer(z):\n    def bump(c: Mut(Int)):\n        c += 1\n    y: Mut(Int) := 0\n    bump(y)\n    y + z\nr + outer(100)",
        cambra::interpreter::Value::Int(108),
    );
}

/// Regression: a pass-by-reference writer loop as the program's *final*
/// statement (its mutable-variable value unobserved) must lower — mirroring the same loop
/// in middle position. Before the fix `lower_final_stmt` lacked the hidden-writer
/// fallback and rejected it with "must end in a yield/feed".
#[test]
fn trailing_hidden_writer_loop_compiles() {
    let code = "def bump(c: Mut(Int)):\n    c += 1\ncnt: Mut(Int) := 0\nfor x in [1, 2, 3]:\n    bump(cnt)";
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let result = compile_program(&mut ctx, code, consumer);
    assert!(
        result.is_ok(),
        "expected a trailing hidden-writer loop to compile, got:\n{}",
        result
            .err()
            .map(|e| render_errors(&e, "<test>", code))
            .unwrap_or_default()
    );
}

// ---------------------------------------------------------------------------
// Compound (tuple / record) mutable variables
//
// A mutable variable holds one `Value`, so a tuple/record accumulator is a boxed
// `Scalar(Record)` in the changelog, while a tuple/record *literal* compiles to
// a struct-of-arrays `Record` tiling. The two representations are reconciled at
// the mutable variable boundaries (`read_initial_scalar` seeding, `flat_merge` decision
// values, `ExtractFinal` extent-match) via `scalar_tile_to_column_value` /
// `column_value_to_tile`. These pin that a compound induction accumulator folds,
// reads-its-own-writes, and carries correctly.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Unconditional: the whole tuple is overwritten each step → final write (3, 3).
#[case(r"
acc := (0, 0)
for i in [1, 2, 3]:
    acc := (i, i)
acc", make_tuple(&[Value::Int(3), Value::Int(3)]))]
// Read-your-writes across both fields: acc.0 = 0+1+2+3 = 6, acc.1 = 10+1+2+3 = 16.
#[case(r"
acc := (0, 10)
for i in [1, 2, 3]:
    acc := (acc.0 + i, acc.1 + i)
acc", make_tuple(&[Value::Int(6), Value::Int(16)]))]
// Single-arm conditional write to a tuple: fires at i>1 → final (3, 3).
#[case(r"
acc := (0, 0)
for i in [1, 2, 3]:
    if i > 1:
        acc := (i, i)
acc", make_tuple(&[Value::Int(3), Value::Int(3)]))]
// if/else both arms write different tuples: i=3 → i>2 arm → (3, 30).
#[case(r"
acc := (0, 0)
for i in [1, 2, 3]:
    if i > 2:
        acc := (i, i * 10)
    else:
        acc := (i, i)
acc", make_tuple(&[Value::Int(3), Value::Int(30)]))]
// Trailing carries: writes at i<3 (1,2), carries at 3,4,5 → final (2, 2).
#[case(r"
acc := (0, 0)
for i in [1, 2, 3, 4, 5]:
    if i < 3:
        acc := (i, i)
acc", make_tuple(&[Value::Int(2), Value::Int(2)]))]
// Heterogeneous tuple (Int, String).
#[case(r#"
acc := (0, "a")
for i in [1, 2]:
    acc := (i, "b")
acc"#, make_tuple(&[Value::Int(2), Value::String("b".into())]))]
// Three-tuple.
#[case(r"
acc := (0, 0, 0)
for i in [1, 2, 3]:
    acc := (i, i * 2, i * 3)
acc", make_tuple(&[Value::Int(3), Value::Int(6), Value::Int(9)]))]
// Named record mutable variable.
#[case(r"
acc := (x=0, y=0)
for i in [1, 2, 3]:
    acc := (x=i, y=i + i)
acc", make_record(&[("x", Value::Int(3)), ("y", Value::Int(6))]))]
fn test_compound_mut_var(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// Projecting a field off the final tuple accumulator: `acc.0` after the loop.
#[test]
fn test_compound_mut_var_field_read() {
    check_scalar(
        r"
acc := (0, 0)
for i in [1, 2, 3]:
    acc := (acc.0 + i, acc.1)
acc.0",
        Value::Int(6),
    );
}

/// A nested tuple `((i, i), i)` — `scalar_tile_to_column_value` /
/// `column_value_to_tile` recurse through the nested record.
#[test]
fn test_compound_mut_var_nested() {
    check_scalar(
        r"
acc := ((0, 0), 0)
for i in [1, 2]:
    acc := ((i, i), i)
acc",
        make_tuple(&[make_tuple(&[Value::Int(2), Value::Int(2)]), Value::Int(2)]),
    );
}

/// Nested `for` loops remain unsupported. The mutable variable machinery is why this
/// matters: a fresh `:=` inside a loop body can only be a *sequential* mutable variable
/// (the degenerate domain) precisely because there is no inner loop for it to
/// accumulate over. If nested loops were ever admitted without also teaching the
/// phase about a cross-iteration mutable variable declared inside a loop, that reasoning
/// would silently stop holding — so the rejection is pinned here, next to what
/// depends on it.
#[test]
fn nested_for_loops_stay_rejected() {
    expect_compile_error(
        indoc! {r#"
            s := 0
            for x in [1, 2]:
                for y in [10, 20]:
                    s += y
            s
        "#},
        "for-loop body",
    );
}

/// A `Lambda` param may still bind a mutable variable — that is pass-by-reference, where
/// the mutable variable genuinely crosses a function boundary. Pinned because `emit_let`
/// now reads through an initializer that is a mutable variable, and widening that to argument
/// positions would silently turn every `Mut` parameter into a value copy: the
/// callee would write a snapshot and the caller would observe nothing.
#[test]
fn a_mut_param_still_binds_a_mut_var() {
    check_scalar(
        indoc! {r#"
            def bump(c: Mut(Int)):
                c += 1
            x := 0
            bump(x)
            x
        "#},
        cambra::interpreter::Value::Int(1),
    );
}
