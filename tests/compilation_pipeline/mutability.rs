//! Mutation loops: loop-carried accumulators, multi-accumulator loops, and
//! feeds interleaved with mutations.

use std::collections::HashMap;
use std::time::Duration;

use bit_set::BitSet;
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
// (rule 2), and an unannotated binding may not have `Mut` type (rule 3).
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
#[test]
fn augmented_assignment_to_non_mutable_rejected() {
    expect_mut_discipline_error("x = 0\nx += 1\nx", "not a mutable variable");
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

/// A `:=` accumulator *declared inside* a for-loop body (rather than before it)
/// is rejected: the accumulator's recurrence spans the whole loop, so its
/// declaration must precede the loop.
#[test]
fn accumulator_declared_inside_loop_rejected() {
    expect_compile_error(
        "for i in [1, 2, 3]:\n    y: Mut(Int) := 0\n    y += i\ny",
        "accumulator declaration inside a for-loop body is not",
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

/// Rule 3: an unannotated copy of a mutable variable (`b = a`) aliases it — rejected, to
/// force the author to disambiguate a value copy (`b: Int = a`) from seeding a
/// new mutable variable (`b: Mut(Int) := a`).
#[test]
fn rule3_unannotated_mut_alias_is_rejected() {
    expect_mut_discipline_error("a := 0\nb = a\nb", "not annotated `Mut`");
}

/// Rule 2: a function may not return a `Mut` — the mutable-variable reference would
/// escape where its writer set is no longer statically known.
#[test]
fn rule2_function_returning_mut_is_rejected() {
    expect_mut_discipline_error("x := 0\nf = \\z -> x\nf", "inside a composite type");
}

/// Rule 1: an argument to a `Mut` parameter must be a bare variable reference,
/// so a *conditional* selecting between two mutable variables — which one would
/// the callee's write target? — is rejected. The check reads the argument node,
/// not its type: a conditional over two registers reads their *values* (a
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
// annotation is a plain checking-mode declaration here, so the register's value
// type must match it.
#[test]
fn nonmut_param_reads_mut_arg_current_value() {
    check_scalar(
        "cnt: Mut(Int) := 5\ndef g(a: Int):\n    a + 1\ng(cnt)",
        cambra::interpreter::Value::Int(6),
    );
}
// The enforced annotation has force even when the argument is a mutable
// variable: a `String` parameter rejects an `Int` register's value. Before
// parameter annotations were carried through lowering this compiled — the
// annotation was silently dropped and `a` inferred `Int` from the argument.
#[test]
fn nonmut_param_annotation_enforced_against_mut_arg() {
    expect_compile_error(
        "cnt: Mut(Int) := 0\ndef g(a: String):\n    a\ng(cnt)",
        "mismatch",
    );
}
// Pass-by-reference sibling of the above: a `Mut(Int)` register cannot bind a
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
#[test]
fn wildcard_annotated_mut_alias_rejected() {
    expect_mut_discipline_error("a: Mut(Int) := 0\nb: _ = a\nb", "not annotated `Mut`");
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
// Compound (tuple / record) mutable registers
//
// A register holds one `Value`, so a tuple/record accumulator is a boxed
// `Scalar(Record)` in the changelog, while a tuple/record *literal* compiles to
// a struct-of-arrays `Record` tiling. The two representations are reconciled at
// the register boundaries (`read_initial_scalar` seeding, `flat_merge` decision
// values, `ExtractLast` extent-match) via `scalar_tile_to_column_value` /
// `column_value_to_tile`. These pin that a compound induction accumulator folds,
// reads-its-own-writes, and carries correctly.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Unconditional: the whole tuple is overwritten each step → last write (3, 3).
#[case(r"
acc := (0, 0)
for i in [1, 2, 3]:
    acc := (i, i)
acc", make_tuple(&[Value::Int(3), Value::Int(3)]))]
// Read-your-writes across both fields: acc.0 = 0+1+2+3 = 6, acc.1 = 10+1+2+3 = 16.
#[case(r"
acc := (0, 10)
for i in [1, 2, 3]:
    acc := (acc[0] + i, acc[1] + i)
acc", make_tuple(&[Value::Int(6), Value::Int(16)]))]
// Single-arm conditional write to a tuple: fires at i>1 → last (3, 3).
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
// Named record register.
#[case(r"
acc := (x=0, y=0)
for i in [1, 2, 3]:
    acc := (x=i, y=i + i)
acc", make_record(&[("x", Value::Int(3)), ("y", Value::Int(6))]))]
fn test_compound_register(#[case] code: &str, #[case] expected: Value) {
    check_scalar(code, expected);
}

/// Projecting a field off the final tuple accumulator: `acc[0]` after the loop.
#[test]
fn test_compound_register_field_read() {
    check_scalar(
        r"
acc := (0, 0)
for i in [1, 2, 3]:
    acc := (acc[0] + i, acc[1])
acc[0]",
        Value::Int(6),
    );
}

/// A nested tuple `((i, i), i)` — `scalar_tile_to_column_value` /
/// `column_value_to_tile` recurse through the nested record.
#[test]
fn test_compound_register_nested() {
    check_scalar(
        r"
acc := ((0, 0), 0)
for i in [1, 2]:
    acc := ((i, i), i)
acc",
        make_tuple(&[make_tuple(&[Value::Int(2), Value::Int(2)]), Value::Int(2)]),
    );
}
