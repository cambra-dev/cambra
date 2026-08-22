//! Transactional stores (`Mut(V, Txn)` + `with begin():`) — the commit-operator
//! path. Batch (finite-loop and standalone) single-variable transactions run
//! end-to-end: `x: Mut(V, Txn)` folds into a commit store shared with the mutable variables
//! some block relates it to, and each `with begin():` block is a writer.
//!
//! **Reading a mutable variable: two constructs, and the difference is what these tests
//! assert.** A mutable variable read *fed out* of a `with begin():` block is an as-of read
//! at the reading transaction's (arbitrary) commit position, indexed by the reading loop —
//! compiled to `AsOf` uniformly, whether that loop is a live `DataSource` stream, a finite
//! loop, or a standalone read's synthesized singleton. Each position latches at its own
//! arrival, so such a read has no assertable value unless the program orders the arrival
//! after the commits. `await_final(x)` is the **terminal** read: `x`'s final committed
//! value once every writer has drained, compiled to `ExtractFinal` over the key's
//! commit-value stream, and it consumes `x`. The batch tests below read their result with
//! `await_final`, which is what makes a scalar-valued expected tile a *semantic*
//! assertion.
//!
//! Translated from the prototype's transaction suite (its `txn x = e` introducer
//! is the `x: Mut(V, Txn) := e` annotation here).

use std::cell::RefCell;
use std::rc::Rc;
use std::time::Duration;

use bit_set::BitSet;
use bit_vec::BitVec;
use cambra::ccl::Type;
use cambra::ccl::context::{CompileResultExt, GlobalContext, compile_program, render_errors};
use cambra::interpreter::{
    BaseType, ColumnValue, Consumer, Extent, Predicate, TestDataSource, Tile, Value,
};
use rstest_log::rstest;
use smol_str::SmolStr;

use cambra::ccl::TagMap;

use crate::helpers::*;
use indoc::{formatdoc, indoc};

/// Assert `code` fails to compile with an error whose rendering contains
/// `needle` (pins the specific failure).
fn check_compile_error(code: &str, needle: &str) {
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let err = match compile_program(&mut ctx, code, consumer) {
        Ok(_) => panic!("expected a compile error containing {needle:?}; program compiled"),
        Err(e) => e,
    };
    let rendered = render_errors(&err, "<transactional-test>", code);
    assert!(
        rendered.contains(needle),
        "expected compile error to contain {needle:?}; got:\n{rendered}"
    );
}

// NOTE — **`await_final` pins when these reads happen, not the order the commits
// land in.** The read is semantic: it waits for completeness, so the value it reports
// is the store's last, not whichever one the scheduler happened to leave visible. It
// supplies no commit order, and these programs pin none either: a literal-list loop
// leaves the order to the engine's serialization
// (`drain_start`). The only context that pins commit order is a loop over a live
// external stream (a `DataSource`), where real arrival order is a denotational
// anchor. These blocks depend only on program start (no source arrival, no
// cross-transaction data dependence), and program start is a single event that
// imposes no order *among* the blocks it triggers — so the event model *defines*
// their commit order as mutually unordered, and the engine may serialize them any
// way, correct under all of them. That is the contract, not a defect; see
// `src/ccl/design/mutability.md` "Ordering and concurrency".
//
// So an expected value here is pinned exactly when the body is order-insensitive.
// Commutative draws (`pool := pool - r`) are: every serialization agrees, and the
// assertion is a real one. A body whose outcome differs per serialization has no
// single answer to assert, which is why `grant_deny_two_writers_single_commit`
// asserts a disjunction rather than a number.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Single writer draws down a pool: 100 − 10 − 20 − 30 = 40.
#[case::counter(
    indoc! {r#"
        pool: Mut(Int, Txn) := 100
        for r in [10, 20, 30]:
            with begin():
                pool := pool - r
        await_final(pool)
    "#},
    40
)]
// Two writers over one mutable variable: the operator serializes + retries, conserving the
// total: 100 − 30 − 40 = 30.
#[case::two_writers(
    indoc! {r#"
        pool: Mut(Int, Txn) := 100
        for r in [30]:
            with begin():
                pool := pool - r
        for r in [40]:
            with begin():
                pool := pool - r
        await_final(pool)
    "#},
    30
)]
// Multi-statement body: a leading `let fee`, a guard, then the write. A: 100 − 33
// = 67; B: 67 ≥ 44 → 67 − 44 = 23.
#[case::multi_stmt(
    indoc! {r#"
        pool: Mut(Int, Txn) := 100
        for r in [30]:
            with begin():
                fee = r // 10
                if pool >= r + fee:
                    pool := pool - r - fee
        for r in [40]:
            with begin():
                fee = r // 10
                if pool >= r + fee:
                    pool := pool - r - fee
        await_final(pool)
    "#},
    23
)]
// Computed (non-literal) init `sum([40,30,30]) = 100`, read from an acyclic init
// operator at tick 0; one writer draws 60 → 40.
#[case::computed_init(
    indoc! {r#"
        pool: Mut(Int, Txn) := sum([40, 30, 30])
        for r in [60]:
            with begin():
                pool := pool - r
        await_final(pool)
    "#},
    40
)]
// Writer source bound *after* the mutable variable declaration (`reqs` between `pool` and
// the loop). The mutable variable letrec is spliced below every source binding, so the
// writer's `Var(reqs)` is in scope — previously this crashed with an internal
// unrecognised-variable error. 100 − 10 − 20 − 30 = 40.
#[case::source_bound_after_store(
    indoc! {r#"
        pool: Mut(Int, Txn) := 100
        reqs = [10, 20, 30]
        for r in reqs:
            with begin():
                pool := pool - r
        await_final(pool)
    "#},
    40
)]
// A single standalone transaction (no enclosing `for`): one commit over a
// synthesized singleton source: 100 − 10 = 90.
#[case::standalone_single(
    indoc! {r#"
        pool: Mut(Int, Txn) := 100
        with begin():
            pool := pool - 10
        await_final(pool)
    "#},
    90
)]
// Two standalone transactions in sequence: two commits on one clock → 70.
#[case::standalone_sequential(
    indoc! {r#"
        pool: Mut(Int, Txn) := 100
        with begin():
            pool := pool - 10
        with begin():
            pool := pool - 20
        await_final(pool)
    "#},
    70
)]
// A standalone transaction composes with loop-based ones on the shared mutable variable:
// 100 − 1 − 10 − 20 = 69.
#[case::standalone_then_loop(
    indoc! {r#"
        pool: Mut(Int, Txn) := 100
        with begin():
            pool := pool - 1
        for r in [10, 20]:
            with begin():
                pool := pool - r
        await_final(pool)
    "#},
    69
)]
// Two writers, each drawing several amounts, over one mutable variable. The operator
// serializes + retries across all four commits; subtraction conserves the
// total regardless of interleaving: 100 − 10 − 20 − 5 − 15 = 50.
#[case::multi_writer_contention(
    indoc! {r#"
        pool: Mut(Int, Txn) := 100
        for r in [10, 20]:
            with begin():
                pool := pool - r
        for r in [5, 15]:
            with begin():
                pool := pool - r
        await_final(pool)
    "#},
    50
)]
// Three writers on one mutable variable compose the same as one: 100 − 10 − 20 − 30 = 40.
#[case::three_writers(
    indoc! {r#"
        pool: Mut(Int, Txn) := 100
        for r in [10]:
            with begin():
                pool := pool - r
        for r in [20]:
            with begin():
                pool := pool - r
        for r in [30]:
            with begin():
                pool := pool - r
        await_final(pool)
    "#},
    40
)]
// Two writers contend for a pool too small for both draws: whichever the
// operator serializes first commits (pool → 40); the other re-reads 40, fails
// `40 >= 60`, and denies. Order-independent final: 40.
#[case::multi_writer_grant_deny(
    indoc! {r#"
        pool: Mut(Int, Txn) := 100
        for r in [60]:
            with begin():
                if pool >= r:
                    pool := pool - r
        for r in [60]:
            with begin():
                if pool >= r:
                    pool := pool - r
        await_final(pool)
    "#},
    40
)]
// Semantic change: the deny guard is no longer transaction-scoped. A spine
// (unconditional) write beside an `if` commits unconditionally (`commit = p ∨
// true → true`), so the spine write lands even when the guard is false. Here the
// spine `x := x + 1` commits (x → 101) though `if x > 1000` never fires — under
// the old transaction-scoped deny, a false guard would have denied the whole
// transaction and left x = 100.
#[case::spine_write_commits_beside_false_guard(
    indoc! {r#"
        x: Mut(Int, Txn) := 100
        with begin():
            x := x + 1
            if x > 1000:
                x := x + 10
        await_final(x)
    "#},
    101
)]
fn test_transactional_stores(#[case] code: &str, #[case] expected: i64) {
    check_tile(code, Tile::Scalar(ColumnValue::Ints(vec![expected])));
}

// ---------------------------------------------------------------------------
// Multiple variables in one transaction + read-your-writes (multi-key mutable variable)
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Both keys read at completion (`await_final(a)`, `await_final(b)`) — one
// consistent view of the finished mutable variable, with no dependence on where a sample
// would have landed. `a` and `b` update atomically each iteration: a := sum([1,2,3]) = 6, b := sum of
// squares = 14 → a*100 + b := 614.
#[case::multi_var(
    indoc! {r#"
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for x in [1, 2, 3]:
            with begin():
                a := a + x
                b := b + x * x
        await_final(a) * 100 + await_final(b)
    "#},
    614
)]
// Cross-variable read: `b = b + a` reads `a`'s snapshot before `a = a + x`, so a
// runs 5,6,8 → b := 19, a ends 11 → 1119.
#[case::multi_var_cross_read(
    indoc! {r#"
        a: Mut(Int, Txn) := 5
        b: Mut(Int, Txn) := 0
        for x in [1, 2, 3]:
            with begin():
                b := b + a
                a := a + x
        await_final(a) * 100 + await_final(b)
    "#},
    1119
)]
// Read-your-writes across keys: `b = a` after `a = a + x` sees the new `a`. a:
// 0→1→3→6, b: 1,3,6 → final a=6, b=6 → 606.
#[case::read_your_writes_cross_key(
    indoc! {r#"
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for x in [1, 2, 3]:
            with begin():
                a := a + x
                b := a
        await_final(a) * 100 + await_final(b)
    "#},
    606
)]
// Same key written twice: the second `a = a + 1` reads the first write's value.
// x=10: 0→10→11; x=20: 11→31→32 → 32.
#[case::read_your_writes_same_key(
    indoc! {r#"
        a: Mut(Int, Txn) := 0
        for x in [10, 20]:
            with begin():
                a := a + x
                a := a + 1
        await_final(a)
    "#},
    32
)]
// Read-only mutable variable key: `limit` is read in the guard but written nowhere. x=10
// commits (10 ≤ 25); 20/30 denied → total := 10.
#[case::multi_var_readonly_key(
    indoc! {r#"
        limit: Mut(Int, Txn) := 25
        total: Mut(Int, Txn) := 0
        for x in [10, 20, 30]:
            with begin():
                if total + x <= limit:
                    total := total + x
        await_final(total)
    "#},
    10
)]
// Two writers touching *disjoint* keys — no footprint overlap, so neither ever
// invalidates the other. `a` = 1+2 = 3, `b` = 10+20 = 30 → 3*100 + 30 = 330.
#[case::multi_writer_disjoint_keys(
    indoc! {r#"
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for x in [1, 2]:
            with begin():
                a := a + x
        for y in [10, 20]:
            with begin():
                b := b + y
        await_final(a) * 100 + await_final(b)
    "#},
    330
)]
// Two writers with *overlapping* footprints: writer 1 writes {a, b}, writer 2
// writes {b, c}. The shared `b` forces serialization, but the sums are
// order-independent: a := 3, b := 1+2+10+20 = 33, c := 30 → 3*10000 + 33*100 + 30
// = 33330.
#[case::multi_writer_overlapping_keys(
    indoc! {r#"
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        c: Mut(Int, Txn) := 0
        for x in [1, 2]:
            with begin():
                a := a + x
                b := b + x
        for y in [10, 20]:
            with begin():
                b := b + y
                c := c + y
        await_final(a) * 10000 + await_final(b) * 100 + await_final(c)
    "#},
    33330
)]
// Three keys updated atomically per transaction, all read together under one
// snapshot: a := sum = 6, b := sum of squares = 14, c := count = 3 → 6*10000 +
// 14*100 + 3 = 61403.
#[case::read_three_vars_one_snapshot(
    indoc! {r#"
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        c: Mut(Int, Txn) := 0
        for x in [1, 2, 3]:
            with begin():
                a := a + x
                b := b + x * x
                c := c + 1
        await_final(a) * 10000 + await_final(b) * 100 + await_final(c)
    "#},
    61403
)]
fn test_multi_variable_transactions(#[case] code: &str, #[case] expected: i64) {
    check_tile(code, Tile::Scalar(ColumnValue::Ints(vec![expected])));
}

// ---------------------------------------------------------------------------
// Per-commit progress feeds (`out << e` *inside* the block)
// ---------------------------------------------------------------------------

/// A per-commit reply stream: `values` indexed by 1-based commit tick (the
/// commit engine allocates ticks starting at 1, exactly as the prototype did —
/// `u1 -> …`). A feed inside a `with begin():` block produces one entry per
/// *committed* transaction, so a denied commit contributes no tick.
fn commit_stream(ticks: &[usize], values: &[i64]) -> Tile {
    Tile::SealedFunction {
        domain: ColumnValue::UInts(ticks.to_vec()),
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(values.to_vec()))),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
}

/// Drive a program whose result is an `await_final` read and return the `Value` it
/// settles on. A compound (tuple/record) mutable variable reads back boxed
/// (`Scalar(Record)`) or struct-of-arrays depending on the read path; both fold to
/// the same `Value` through `scalar_tile_to_column_value`, so this asserts on the
/// *value* rather than the (path-dependent) tile shape.
fn final_mut_var_value(code: &str) -> Value {
    use cambra::interpreter::tile_operators::scalar_tile_to_column_value;
    let tile = run_pipeline(code);
    let column = scalar_tile_to_column_value(tile);
    assert_eq!(
        column.len(),
        1,
        "a final mutable variable value is one value"
    );
    column.index_at(0)
}

// ---------------------------------------------------------------------------
// Compound (tuple / record) transactional mutable variables
//
// A `Mut({Int, Int}, Txn)` / `Mut({x: Int}, Txn)` mutable variable holds one compound
// `Value`; the commit-store path already threads it (it shares the induction
// path's `read_initial_scalar` seeding and boxes/unboxes at the value-Case
// decision merge). Enabling it needed only the tuple/record *type annotation*
// forms in `lower_type_annotation`.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Unconditional tuple mutable variable: (100,0) −10/+10 → (90,10) −20/+20 → (70,30).
#[case(indoc! {r#"
    p: Mut({Int, Int}, Txn) := (100, 0)
    for r in [10, 20]:
        with begin():
            p := (p.0 - r, p.1 + r)
    await_final(p)
"#}, make_tuple(&[Value::Int(70), Value::Int(30)]))]
// Conditional tuple write with a deny: r=60 commits (100≥60 → (40,60)); r=60 again
// denies (40≥60 false) → stays (40,60).
#[case(indoc! {r#"
    p: Mut({Int, Int}, Txn) := (100, 0)
    for r in [60, 60]:
        with begin():
            if p.0 >= r:
                p := (p.0 - r, p.1 + r)
    await_final(p)
"#}, make_tuple(&[Value::Int(40), Value::Int(60)]))]
// if/else both arms write a tuple: r=3 → r>2 arm → (3, 30).
#[case(indoc! {r#"
    p: Mut({Int, Int}, Txn) := (0, 0)
    for r in [1, 2, 3]:
        with begin():
            if r > 2:
                p := (r, r * 10)
            else:
                p := (r, r)
    await_final(p)
"#}, make_tuple(&[Value::Int(3), Value::Int(30)]))]
// Named record mutable variable.
#[case(r"
p: Mut({x: Int, y: Int}, Txn) := (x=100, y=0)
for r in [10, 20]:
    with begin():
        p := (x=p.x - r, y=p.y + r)
await_final(p)", make_record(&[("x", Value::Int(70)), ("y", Value::Int(30))]))]
// Mixed multi-key store: a scalar key `s` and a tuple key `p`, atomic per commit.
// s = 10+20 = 30; p = (70, 30); both read at completion.
#[case(indoc! {r#"
    s: Mut(Int, Txn) := 0
    p: Mut({Int, Int}, Txn) := (100, 0)
    for r in [10, 20]:
        with begin():
            s := s + r
            p := (p.0 - r, p.1 + r)
    (await_final(s), await_final(p))
"#}, make_tuple(&[Value::Int(30), make_tuple(&[Value::Int(70), Value::Int(30)])]))]
fn test_compound_txn_mut_var(#[case] code: &str, #[case] expected: Value) {
    assert_eq!(final_mut_var_value(code), expected);
}

/// A field projected off a tuple transactional mutable variable's completion read.
#[test]
fn test_compound_txn_mut_var_field() {
    assert_eq!(
        final_mut_var_value(indoc! {r#"
                p: Mut({Int, Int}, Txn) := (100, 0)
                for r in [10, 20]:
                    with begin():
                        p := (p.0 - r, p.1 + r)
                await_final(p).0
            "#}),
        Value::Int(70),
    );
}

/// `out << pool` *inside* the block reports each transaction's committed
/// (read-your-writes) value: `pool - r` after the write — 90, 70, 40 over commit
/// ticks 1, 2, 3. The feed rides the writer decision as a `to_out` tap,
/// committed atomically with the mutable variable write and read back as a per-commit
/// value-stream (commit-tick-indexed). Contrast `await_final(pool)` (one scalar, the
/// completed 40) and a *fed-out* read `with begin(): out << pool` (an as-of sample
/// latched to that read's own commit position) — three different constructs over the
/// same store.
#[test]
fn progress_feed_inside_tx() {
    check_tile(
        indoc! {r#"
            out = defer()
            pool: Mut(Int, Txn) := 100
            for r in [10, 20, 30]:
                with begin():
                    pool := pool - r
                    out << pool
            out
        "#},
        commit_stream(&[1, 2, 3], &[90, 70, 40]),
    );
}

/// A denied transaction contributes no reply — the feed tap rides `commit`, so
/// the engine appends nothing for a `commit: false` decision. 70 commits (pool →
/// 30, reply 30); 50 fails `30 >= 50` → deny, no tick. So `out` is [30] at tick
/// 1 alone.
#[test]
fn progress_feed_grant_deny() {
    check_tile(
        indoc! {r#"
            out = defer()
            pool: Mut(Int, Txn) := 100
            for r in [70, 50]:
                with begin():
                    if pool >= r:
                        pool := pool - r
                        out << pool
            out
        "#},
        commit_stream(&[1], &[30]),
    );
}

// ---------------------------------------------------------------------------
// Value types: a transactional mutable variable holds any base value, not just int
// ---------------------------------------------------------------------------

/// A `bool`-valued transactional mutable variable: both writers set `flag = True`, so the
/// completion read reports `True`.
#[test]
fn bool_valued_store() {
    check_tile(
        indoc! {r#"
            flag: Mut(Bool, Txn) := False
            for x in [1, 2]:
                with begin():
                    flag := True
            await_final(flag)
        "#},
        Tile::Scalar(ColumnValue::Bools(BitVec::from_elem(1, true))),
    );
}

/// A `str`-valued transactional mutable variable: the final commit sets `name = "bob"`.
#[test]
fn string_valued_store() {
    check_tile(
        indoc! {r#"
            name: Mut(String, Txn) := "init"
            for x in [1, 2]:
                with begin():
                    name := "bob"
            await_final(name)
        "#},
        Tile::Scalar(ColumnValue::Strings(vec![SmolStr::new("bob")])),
    );
}

// ---------------------------------------------------------------------------
// Multiple reply feeds from one transaction
// ---------------------------------------------------------------------------

/// One writer feeds *two* distinct reply streams inside the same block; the
/// program returns both as a tuple. Each rides the writer decision as its own
/// `to_<defer>` tap and is read back per commit tick: `a` = 1,3,6 and `b` (sum
/// of squares) = 1,5,14 over commit ticks 1,2,3.
#[test]
fn two_reply_feeds_one_transaction() {
    check_tile(
        indoc! {r#"
            outa = defer()
            outb = defer()
            a: Mut(Int, Txn) := 0
            b: Mut(Int, Txn) := 0
            for x in [1, 2, 3]:
                with begin():
                    a := a + x
                    b := b + x * x
                    outa << a
                    outb << b
            (outa, outb)
        "#},
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![1, 2, 3]),
            codomain: Box::new(Tile::tuple(vec![
                Tile::Scalar(ColumnValue::Ints(vec![1, 3, 6])),
                Tile::Scalar(ColumnValue::Ints(vec![1, 5, 14])),
            ])),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
    );
}

/// A reply feed under **one arm of cross-key routing**: the feed `out << x` sits
/// inside `if x >= 2` (which writes `a`), while the `else` writes `b`. Both arms
/// write, so *every* iteration commits — but the feed must fire only on its own
/// route (`x >= 2`), not on the sibling `else` route's commit. The tap carries a
/// `__fire` gate the engine honors, so over `[1, 2, 3]` (commit ticks 1, 2, 3)
/// `out` receives 2 and 3 (ticks 2, 3) — not a value at tick 1. (Without the
/// gate the tap would over-fire on every commit.)
#[test]
fn reply_feed_under_one_route_does_not_overfire() {
    check_tile(
        indoc! {r#"
            a: Mut(Int, Txn) := 0
            b: Mut(Int, Txn) := 0
            out = defer()
            for x in [1, 2, 3]:
                with begin():
                    if x >= 2:
                        a := a + x
                        out << x
                    else:
                        b := b + x
            out
        "#},
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![2, 3]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
    );
}

/// **Both arms feed** in a *committing* block: each arm writes the mutable variable `a`
/// and replies on `out`. Both taps ride the same commit but must fire only on
/// their own route — each carries its own `__fire` gate. x=1 → else (a += 100,
/// out << 0); x=2 → if (a += 2, out << 2); x=3 → if (a += 3, out << 3). Every
/// position commits (both arms write), so `out` is [0, 2, 3] over domain [0,1,2].
#[test]
fn both_arms_feed_in_committing_block() {
    check_tile(
        indoc! {r#"
            a: Mut(Int, Txn) := 0
            out = defer()
            for x in [1, 2, 3]:
                with begin():
                    if x >= 2:
                        a := a + x
                        out << x
                    else:
                        a := a + 100
                        out << 0
            out
        "#},
        // Both taps fan out into a tagged-union channel (each fires on its own
        // route): variant 0 is the `if` arm (x=2,3 → 2,3), variant 1 the `else`
        // (x=1 → 0). Same union shape as the read-only both-arms reply, over the
        // committing-block feed indexing (cf. `reply_feed_under_one_route`).
        Tile::SealedFunction {
            domain: ColumnValue::positional_union(
                &[0, 0, 1],
                vec![ColumnValue::UInts(vec![2, 3]), ColumnValue::UInts(vec![1])],
            ),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3, 0]))),
            domain_predicate: Predicate::Union(TagMap::from_positional(vec![
                Predicate::True,
                Predicate::True,
            ])),
            deleted: BitSet::new(),
        },
    );
}

/// **Read-your-writes of a conditionally-written key, after the `Case`.** The
/// spine feed `out << a` reads `a`'s post-`Case` value: the written value on the
/// guard path, the carry (prior committed value) on the deny path. `a := a + 10`
/// under `if x >= 2`, then `out << a`. x=1 → deny → a carries 0 → out 0; x=2 →
/// a = 10 → out 10; x=3 → a = 20 → out 20. The spine feed commits every position.
#[test]
fn ryw_of_conditionally_written_key_after_case() {
    check_tile(
        indoc! {r#"
            a: Mut(Int, Txn) := 0
            out = defer()
            for x in [1, 2, 3]:
                with begin():
                    if x >= 2:
                        a := a + 10
                    out << a
            out
        "#},
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![1, 2, 3]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 10, 20]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
    );
}

/// A **conditional feed in a read-only `with begin():` block** — a conditional
/// reply that reads a mutable variable (`if r > 1: resp << pool`). The block commits no
/// mutable variable, so the reply is a filtered as-of read: `channelize` fans the guard-
/// `Case` out into a refined-source channel (the same path a non-transactional
/// `if r > 1: resp << r` takes), rather than the feed-only hoist which handles
/// only straight-line replies. `pool` is never written, so its as-of value is its
/// init (100), replied at the guard-passing positions (r = 2, 3 → domain 1, 2).
#[test]
fn conditional_reply_in_readonly_block() {
    check_tile(
        indoc! {r#"
            resp = defer()
            pool: Mut(Int, Txn) := 100
            for r in [1, 2, 3]:
                with begin():
                    if r > 1:
                        resp << pool
            resp
        "#},
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![100, 100]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
    );
}

/// An `if/else` conditional reply in a read-only `with begin():` block: both arms
/// feed, so the fan-out refines the source on each arm (the `else` with predicate
/// `¬(r > 1)`) — the read-only-block counterpart of the pure-feed `if/else`
/// fan-out. As a function: r=1 → 0 (else), r=2 → 2, r=3 → 3 (both variants).
#[test]
fn conditional_if_else_reply_in_readonly_block() {
    check_tile(
        indoc! {r#"
            resp = defer()
            pool := 100
            for r in [1, 2, 3]:
                with begin():
                    if r > 1:
                        resp << r
                    else:
                        resp << 0
            resp
        "#},
        Tile::SealedFunction {
            domain: ColumnValue::positional_union(
                &[0, 0, 1],
                vec![ColumnValue::UInts(vec![1, 2]), ColumnValue::UInts(vec![0])],
            ),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![2, 3, 0]))),
            domain_predicate: Predicate::Union(TagMap::from_positional(vec![
                Predicate::True,
                Predicate::True,
            ])),
            deleted: BitSet::new(),
        },
    );
}

// ---------------------------------------------------------------------------
// Multiple writers feeding one defer
// ---------------------------------------------------------------------------

/// Assert a per-commit reply stream is *some* valid serialization of a pool
/// drawdown: one reply per commit, and — since all draws are positive so the
/// pool strictly decreases with each commit — the reply values sorted
/// descending are the running pool, whose successive decrements from `initial`
/// are a permutation of `draws`. This is order-independent: the round-robin
/// commit drain may serialize the (conflicting) draws in any order, so the exact
/// value at each tick is schedule-dependent, but every draw commits exactly once
/// and the pool is conserved.
fn assert_drawdown_replies(tile: &Tile, initial: i64, draws: &[i64]) {
    let Tile::SealedFunction { codomain, .. } = tile else {
        panic!("expected a SealedFunction reply stream, got {tile:?}");
    };
    let Tile::Scalar(ColumnValue::Ints(vals)) = codomain.as_ref() else {
        panic!("expected an Ints reply codomain, got {codomain:?}");
    };
    assert_eq!(vals.len(), draws.len(), "one reply per committed draw");
    let mut sorted = vals.clone();
    sorted.sort_unstable_by(|a, b| b.cmp(a)); // descending = running pool in commit order
    let mut decrements = Vec::with_capacity(sorted.len());
    let mut prev = initial;
    for v in &sorted {
        decrements.push(prev - v);
        prev = *v;
    }
    decrements.sort_unstable();
    let mut expected = draws.to_vec();
    expected.sort_unstable();
    assert_eq!(
        decrements, expected,
        "each draw committed exactly once (any serialization); replies {vals:?}"
    );
}

/// Two writers both feed `out` (the reply of each transaction's committed
/// value). Each writer's reply appears at its own commit tick, unioned across
/// the two sites. (Regression: this used to smear writer 1's value forward onto
/// writer 2's tick via carry-forward.) The two draws conflict on the pool, so
/// the round-robin drain may serialize them either way — asserted as a valid
/// drawdown rather than a fixed per-tick stream.
#[test]
fn multi_writer_single_defer_feed() {
    // Two writers each reply their committed pool value. They conflict on `pool`,
    // so the round-robin drain may serialize them in either order — the per-tick
    // values are schedule-dependent, but both draws commit exactly once and the
    // pool is conserved (final 70).
    let tile = run_pipeline(indoc! {r#"
            out = defer()
            pool: Mut(Int, Txn) := 100
            for r in [10]:
                with begin():
                    pool := pool - r
                    out << pool
            for r in [20]:
                with begin():
                    pool := pool - r
                    out << pool
            out
        "#});
    assert_drawdown_replies(&tile, 100, &[10, 20]);
}

/// Three writers feeding one defer: one reply per commit at its own tick,
/// unioned across the three sites (any serialization — see the two-writer case).
#[test]
fn three_writers_single_defer_feed() {
    // Three writers, one reply per commit. Order is schedule-dependent (they
    // conflict on `pool`); the invariant is one commit per draw and conservation
    // (final 40 = 100 − 10 − 20 − 30).
    let tile = run_pipeline(indoc! {r#"
            out = defer()
            pool: Mut(Int, Txn) := 100
            for r in [10]:
                with begin():
                    pool := pool - r
                    out << pool
            for r in [20]:
                with begin():
                    pool := pool - r
                    out << pool
            for r in [30]:
                with begin():
                    pool := pool - r
                    out << pool
            out
        "#});
    assert_drawdown_replies(&tile, 100, &[10, 20, 30]);
}

/// Two conflicting guarded draws (70 and 50) from a pool of 100. Whichever the
/// round-robin drain serializes first commits; the other then reads the reduced
/// pool and denies (100−70=30 < 50, and 100−50=50 < 70). So exactly one commits
/// and the final pool is 30 or 50 — schedule-dependent but always a single
/// valid, non-negative outcome. (A fixed declaration-order engine always gave
/// 30; under round-robin fairness either serialization is admissible.)
/// `await_final` is what makes the read report a *settled* value rather than
/// whichever position the scheduler left visible — but it supplies no commit order,
/// which is why the assertion is a disjunction and not a number.
#[test]
fn grant_deny_two_writers_single_commit() {
    let tile = run_pipeline(indoc! {r#"
            pool: Mut(Int, Txn) := 100
            for r in [70]:
                with begin():
                    if pool >= r:
                        pool := pool - r
            for r in [50]:
                with begin():
                    if pool >= r:
                        pool := pool - r
            await_final(pool)
        "#});
    let Tile::Scalar(ColumnValue::Ints(vals)) = &tile else {
        panic!("expected a scalar final value, got {tile:?}");
    };
    assert_eq!(vals.len(), 1, "one final value");
    assert!(
        vals[0] == 30 || vals[0] == 50,
        "exactly one draw committed; pool = {}",
        vals[0]
    );
}

// Sustained contention: two writers each draw ten times from one pool, every
// draw conflicting on `pool`. Each pull one writer commits and the other goes
// stale and retries at the advanced frontier — so the losing writer re-proposes
// its stuck item many times over the run. This exercises the writer's
// superseded-proposal reclamation (`TransactWriterProducer::drop_superseded`):
// its retained window stays O(1) instead of accumulating one proposal per
// retry, and the round-robin drain keeps either writer from starving. The test
// asserts the order-independent invariant — all twenty draws commit, conserving
// the pool at 1000 − 20 = 980 — and the 10s timeout would catch an unbounded
// blow-up. (The `drop_superseded` debug-assert also validates the window
// invariant throughout.)
#[test]
fn sustained_contention_conserves_pool() {
    let ones = "[1, 1, 1, 1, 1, 1, 1, 1, 1, 1]";
    let code = formatdoc! {"
        pool: Mut(Int, Txn) := 1000
        for r in {ones}:
            with begin():
                pool := pool - r
        for r in {ones}:
            with begin():
                pool := pool - r
        await_final(pool)
    "};
    check_tile(&code, Tile::Scalar(ColumnValue::Ints(vec![980])));
}

// ---------------------------------------------------------------------------
// `await_final`: the terminal read
//
// The cases above use it as their result, so its ordinary path is covered
// throughout. What is pinned here is what makes it a different read from a
// fed-out one, and the rules that make "final" well-defined.
// ---------------------------------------------------------------------------

/// **The point of the primitive.** The same mutable variable, read both ways in one program:
/// a fed-out read inside a `with begin():` block samples an arbitrary commit position,
/// and `await_final` reports the completed value.
///
/// Only the completion read's value is asserted. The as-of half is asserted to be
/// *present* and not to be anything in particular — that is the difference between the
/// two constructs, and pinning its number would pin whichever sample the scheduler
/// happened to leave visible.
#[test]
fn await_final_and_as_of_read_the_same_mut_var() {
    let code = indoc! {r#"
        out = defer()
        pool: Mut(Int, Txn) := 100
        for r in [10, 20]:
            with begin():
                pool := pool - r
        with begin():
            out << pool
        (sum(out), await_final(pool))
    "#};
    let Tile::Record(fields) = run_pipeline(code) else {
        panic!("expected a record of both reads")
    };
    // 100 − 10 − 20 = 70, and it is the *completed* value, not a sample of it.
    assert_eq!(
        fields.get("_1"),
        Some(&Tile::Scalar(ColumnValue::Ints(vec![70])))
    );
    assert!(
        fields.get("_0").is_some_and(|t| !t.is_empty()),
        "the as-of read resolves to some sample"
    );
}

/// A completeness read stays one **inside a reading loop**. Broadcast over a
/// two-element loop, `await_final(pool)` is the same settled 70 at both positions: the
/// loop indexes the broadcast, not the mutable variable, so the as-of rewrite (which
/// fires on a mutable variable read a reading loop indexes) must not claim it.
///
/// The values separate the two compilations: an as-of sample latches at each position's
/// arrival, so a rewritten read would report the seed (101, 102) rather than 71 and 72.
#[test]
fn await_final_broadcast_over_a_reading_loop_stays_final() {
    check_tile(
        indoc! {r#"
            out = defer()
            pool: Mut(Int, Txn) := 100
            for r in [10, 20]:
                with begin():
                    pool := pool - r
            for q in [1, 2]:
                out << await_final(pool) + q
            out
        "#},
        commit_stream(&[0, 1], &[71, 72]),
    );
}

/// A **bound** await, read inside a feed loop — the shape that separates the two reads
/// by *term* rather than by position. `channelize` closes the channel over the bindings
/// its contribution names, so `let f = ⟨read⟩` is copied in directly above the broadcast:
/// the shape the as-of rewrite matches. The rewrite claims only `as_of_read`, so `f`
/// stays the completed 90 at both positions. Spelled `final_or_default`, as an as-of read
/// once was, it would be matched instead and each position would latch its own arrival —
/// the seed, reporting 101 and 102.
#[test]
fn await_final_bound_then_read_in_a_feed_loop_stays_final() {
    check_tile(
        indoc! {r#"
            out = defer()
            pool: Mut(Int, Txn) := 100
            for r in [10]:
                with begin():
                    pool := pool - r
            f = await_final(pool)
            for q in [1, 2]:
                out << f + q
            out
        "#},
        commit_stream(&[0, 1], &[91, 92]),
    );
}

/// Bound to a name and used downstream: the await need not be the program's tail.
/// The letrec splice moves above the `let` that reads the history binding, which is
/// what keeps `hist_pool` in scope there.
#[test]
fn await_final_bound_then_computed_with() {
    check_tile(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100
            for r in [10, 20, 30]:
                with begin():
                    pool := pool - r
            final = await_final(pool)
            final * 2
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![80])),
    );
}

/// Every transaction denies, so nothing is ever committed and the final value is
/// the seed — `final_or_default`'s default, which is what the CHL spec means by
/// "or the initializer if it was never committed".
#[test]
fn await_final_of_an_all_deny_history_is_the_seed() {
    check_tile(
        indoc! {r#"
            pool: Mut(Int, Txn) := 5
            for r in [10, 20]:
                with begin():
                    if pool >= r:
                        pool := pool - r
            await_final(pool)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![5])),
    );
}

/// A mutable variable **no writer touches** has no commit history at all, so its final
/// value is statically its seed. Distinct from the all-deny case above: there a
/// commit store exists and reports nothing, here there is no store to build.
#[test]
fn await_final_of_a_writer_free_mut_var_is_the_seed() {
    check_tile(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100
            await_final(pool)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![100])),
    );
}

/// A writer-free mutable variable **alongside** writers: `spare` is a key of no site, so it
/// gets no history binding even though a commit store is built for `pool`. Its await
/// resolves to its seed, and `pool`'s to the store's final — the two paths in one
/// program. 100 − 10 = 90, then `90 * 100 + 7`.
#[test]
fn await_final_mixes_a_writer_free_mut_var_with_a_written_one() {
    check_tile(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100
            spare: Mut(Int, Txn) := 7
            for r in [10]:
                with begin():
                    pool := pool - r
            await_final(pool) * 100 + await_final(spare)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![9007])),
    );
}

/// A later block that **writes the awaited mutable variable** extends a history the await
/// already reduced. This is the linearity rule reaching a `MutWrite` target, not a
/// blanket ban on blocks after an await — see
/// `await_final_permits_a_later_block_on_another_mut_var` for the shape that is fine.
#[test]
fn write_to_awaited_mut_var_in_a_later_block_rejected() {
    check_compile_error(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100
            for r in [10]:
                with begin():
                    pool := pool - r
            f = await_final(pool)
            for r in [1]:
                with begin():
                    pool := pool - r
            f
        "#},
        "unreferenceable after `await_final(pool)`",
    );
}

/// A later block that **reads** the awaited mutable variable is the same violation reaching a
/// `Var` in the writer body.
#[test]
fn read_of_awaited_mut_var_in_a_later_block_rejected() {
    check_compile_error(
        indoc! {r#"
            a: Mut(Int, Txn) := 100
            b: Mut(Int, Txn) := 0
            for r in [10]:
                with begin():
                    a := a - r
            f = await_final(a)
            for r in [1]:
                with begin():
                    b := b + a
            f
        "#},
        "unreferenceable after `await_final(a)`",
    );
}

/// **A block after an await is otherwise fine.** It commits another mutable variable, so
/// it touches nothing the await consumed; it joins the same store, which the
/// await was always going to wait for. `a` = 100 - 10 = 90, `b` = 5 -> 9005.
#[test]
fn await_final_permits_a_later_block_on_another_mut_var() {
    check_tile(
        indoc! {r#"
            a: Mut(Int, Txn) := 100
            b: Mut(Int, Txn) := 0
            for r in [10]:
                with begin():
                    a := a - r
            fa = await_final(a)
            for r in [5]:
                with begin():
                    b := b + r
            fa * 100 + await_final(b)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![9005])),
    );
}

/// A writer's iteration source bound **after** an await, which the splice has to keep
/// above the letrec while the await's read rides below it. `b` = 1 + 2 = 3 -> 9003.
#[test]
fn await_final_permits_a_later_writer_source_binding() {
    check_tile(
        indoc! {r#"
            a: Mut(Int, Txn) := 100
            b: Mut(Int, Txn) := 0
            for r in [10]:
                with begin():
                    a := a - r
            fa = await_final(a)
            reqs = [1, 2]
            for r in reqs:
                with begin():
                    b := b + r
            fa * 100 + await_final(b)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![9003])),
    );
}

/// An **induction** accumulator seeded from an await: a different recurrence, so there
/// is no cycle. 100 - 10 - 20 = 70, then 70 + 1 + 2 = 73.
#[test]
fn induction_accumulator_seeded_from_an_await() {
    check_tile(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100
            for r in [10, 20]:
                with begin():
                    pool := pool - r
            x := await_final(pool)
            for i in [1, 2]:
                x := x + i
            x
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![73])),
    );
}

/// The await **consumes** the mutable variable, which is what closes its writer set and so
/// makes "final" a fixed value. A second await is a reference to a consumed
/// mutable variable.
#[test]
fn awaiting_a_mut_var_twice_rejected() {
    check_compile_error(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100
            for r in [10]:
                with begin():
                    pool := pool - r
            await_final(pool) + await_final(pool)
        "#},
        "unreferenceable after `await_final(pool)`",
    );
}

/// Consumption also covers a **pass-by-reference argument**, the one mutable variable mention
/// lowering's read gate lets through (a `Mut`-typed argument is a bare `Var` by rule).
/// Inlining beta-reduces it into the callee body, where it becomes the write the
/// occurrence check finds — which is why that check runs post-inline.
#[test]
fn by_ref_pass_after_await_final_rejected() {
    check_compile_error(
        indoc! {r#"
            def draw(p: Mut(Int, Txn), amt: Int):
                with begin():
                    p := p - amt

            pool: Mut(Int, Txn) := 100
            draw(pool, 10)
            f = await_final(pool)
            draw(pool, 20)
            f
        "#},
        "unreferenceable after `await_final(pool)`",
    );
}

/// Inside a block, the await would wait on the very history that block extends. A
/// block's mutable variable read is the bare snapshot, and that is its only read.
#[test]
fn await_final_inside_a_block_rejected() {
    check_compile_error(
        indoc! {r#"
            out = defer()
            pool: Mut(Int, Txn) := 100
            for r in [10]:
                with begin():
                    pool := pool - r
            with begin():
                out << await_final(pool)
            out
        "#},
        "would wait on the commit history that block extends",
    );
}

/// An induction accumulator has no commit history — its final value is read by
/// naming it after its loop, which is the trailing induction read.
#[test]
fn await_final_of_an_induction_accumulator_rejected() {
    check_compile_error(
        indoc! {r#"
            x := 0
            for i in [1, 2, 3]:
                x := x + i
            await_final(x)
        "#},
        "is not a transactional mutable variable",
    );
}

/// **Phase separation** — drain one transaction, seed the next from its final value.
/// The shape a single program-wide store made impossible: `b`'s seed names `a`'s
/// completion, so with one store `b`'s tick-0 value would await the store `b` itself
/// writes. No block mentions `a` and `b` together, so they partition into two stores
/// and the dependency is an ordinary one-way edge between two letrecs — `hist_a` bound
/// outside, `hist_b`'s seed reading it. `a` reaches 1 + 1 = 2, seeding `b`, which
/// reaches 3.
#[test]
fn a_mut_var_seeded_from_another_store_s_final_value() {
    let code = indoc! {r#"
        a: Mut(Int, Txn) := 1
        for r in [1]:
            with begin():
                a := a + r
        b: Mut(Int, Txn) := await_final(a)
        for r in [1]:
            with begin():
                b := b + r
        await_final(b)
    "#};
    assert_eq!(commit_stores(code), vec!["Txn[a]", "Txn[b]"]);
    check_tile(code, Tile::Scalar(ColumnValue::Ints(vec![3])));
}

/// Phase separation through a writer's **iteration source** rather than a seed: the
/// second transaction runs over an extent computed from the first's final value. Same
/// two-store partition, so the source is an ordinary read of a completed store. `a`
/// drains to 100 - 10 = 90, so `reqs` is `[91, 92]` and `b` reaches 183.
#[test]
fn a_writer_source_computed_from_another_store_s_final_value() {
    let code = indoc! {r#"
        a: Mut(Int, Txn) := 100
        b: Mut(Int, Txn) := 0
        for r in [10]:
            with begin():
                a := a - r
        fa = await_final(a)
        reqs = [x + fa for x in [1, 2]]
        for r in reqs:
            with begin():
                b := b + r
        await_final(b)
    "#};
    assert_eq!(commit_stores(code), vec!["Txn[a]", "Txn[b]"]);
    check_tile(code, Tile::Scalar(ColumnValue::Ints(vec![183])));
}

/// A refusal, and what reaching one takes: the await must reach a writer of its **own**
/// store. The first block relates `a` and `b` (it writes both), so they share a store, and
/// the second block commits into that same store while its decision depends on `a`'s
/// completion. One store is one recurrence, so the value cannot re-enter it.
///
/// Note the shape the sibling key is doing work for: `b := b + fa` cannot name `a`
/// directly, because `await_final` consumes its mutable variable (`check_await_final_linearity`)
/// and would reject the mention first. A store-mate is the only way to reach back in, which
/// is why the check is wider than the rule it enforces —
/// `a_block_writing_only_a_read_only_store_mate_of_an_await_rejected` is that width at its
/// widest, with no block writing both variables at all.
#[test]
fn writer_body_depending_on_its_own_store_s_await_rejected() {
    check_compile_error(
        indoc! {r#"
            a: Mut(Int, Txn) := 100
            b: Mut(Int, Txn) := 0
            for r in [10]:
                with begin():
                    a := a - r
                    b := b + r
            fa = await_final(a)
            for r in [1]:
                with begin():
                    b := b + fa
            await_final(b)
        "#},
        "body depends on `await_final(a)`",
    );
}

/// The same cycle through a writer's **iteration source** — the block's extent, rather
/// than its decision, would await the store it commits into.
#[test]
fn writer_source_depending_on_its_own_store_s_await_rejected() {
    check_compile_error(
        indoc! {r#"
            a: Mut(Int, Txn) := 100
            b: Mut(Int, Txn) := 0
            for r in [10]:
                with begin():
                    a := a - r
                    b := b + r
            fa = await_final(a)
            reqs = [x + fa for x in [1, 2]]
            for r in reqs:
                with begin():
                    b := b + r
            await_final(b)
        "#},
        "iteration source depends on `await_final(a)`",
    );
}

/// And through a **seed**: `c` joins `a`'s store (its block reads store-mate `b`) while
/// its tick-0 value awaits that store's completion.
#[test]
fn a_seed_depending_on_its_own_store_s_await_rejected() {
    check_compile_error(
        indoc! {r#"
            a: Mut(Int, Txn) := 100
            b: Mut(Int, Txn) := 0
            for r in [10]:
                with begin():
                    a := a - r
                    b := b + r
            c: Mut(Int, Txn) := await_final(a)
            for r in [1]:
                with begin():
                    c := c + b
            await_final(c)
        "#},
        "seed of transactional mutable variable `c` depends on `await_final(a)`",
    );
}

/// The same cycle **laundered through an induction accumulator's in-loop write**.
/// `acc`'s seed is a constant, so the taint enters only at `acc := acc + fa` — a name
/// acquires a value by being written, not just by being introduced, and the cycle is
/// the same one whichever way the await reaches the writer's decision.
#[test]
fn writer_body_depending_on_an_await_laundered_through_an_accumulator_rejected() {
    check_compile_error(
        indoc! {r#"
            a: Mut(Int, Txn) := 100
            b: Mut(Int, Txn) := 0
            for r in [10]:
                with begin():
                    a := a - r
                    b := b + r
            fa = await_final(a)
            acc := 0
            for x in [1, 2]:
                acc := acc + fa
            for r in [1]:
                with begin():
                    b := b + acc
            await_final(b)
        "#},
        "body depends on `await_final(a)`",
    );
}

/// **The refusal is checked per store; the rule it enforces is stated per variable.**
/// Nothing a writer of `a` needs may depend on `await_final(a)`; what is checked is that
/// nothing a writer of `a`'s store needs does. No block here writes both variables. The
/// one thing relating them is a block that reads `a` while writing `b`, the partition
/// being over `reads ∪ writes`, and `a`'s only writer drains before the await, so per-key
/// closure settles `await_final(a)` and the last block writes `b` alone. The per-variable
/// rule permits this program; the check refuses it, because one store is one recurrence
/// and a value read out of it cannot feed a writer back into it.
///
/// Splitting a store at a key's closure point would lift the refusal, so this test fails
/// when it narrows. The mechanism is in `src/ccl/design/mutability.md`, "`await_final`".
#[test]
fn a_block_writing_only_a_read_only_store_mate_of_an_await_rejected() {
    check_compile_error(
        indoc! {r#"
            a: Mut(Int, Txn) := 100
            b: Mut(Int, Txn) := 0
            for r in [10]:
                with begin():
                    a := a - r
            for r in [1]:
                with begin():
                    b := b + a
            fa = await_final(a)
            for r in [1]:
                with begin():
                    b := b + fa
            await_final(b)
        "#},
        "body depends on `await_final(a)`",
    );
}

// ---------------------------------------------------------------------------
// Commit-store partitioning
//
// A program gets one commit store per set of mutable variables some `with begin():`
// block relates — not one store for the whole program. These assert the
// partition end to end, on the planned graph rather than only on values: two
// programs can agree on every number and differ in how many stores they built.
// ---------------------------------------------------------------------------

/// The `Transact` carriers in a planned program, as `domain[keys]`, **outermost
/// first**. Reads the *structure* the value tests cannot see — a `Txn` domain is a
/// commit store, an extent domain an induction loop, and the order is the nesting.
fn stores_in(ast: &cambra::ccl::Expr) -> Vec<String> {
    fn walk(e: &cambra::ccl::Expr, out: &mut Vec<String>) {
        if let cambra::ccl::TypedExprNode::Transact { keys, domain, .. } = &e.node {
            out.push(format!(
                "{domain}[{}]",
                keys.iter()
                    .map(|k| k.name.base().to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ));
        }
        e.walk_children(|c| walk(c, out));
    }
    let mut out = Vec::new();
    walk(ast, &mut out);
    out
}

/// [`stores_in`] for a program that registers no data source.
fn commit_stores(code: &str) -> Vec<String> {
    let mut ctx = GlobalContext::default();
    let (ast, _) = run_pipeline_with_ctx(&mut ctx, code);
    stores_in(&ast)
}

/// Two mutable variables written by separate blocks, with no block mentioning them
/// together, have no operation relating them — so they get their own stores, and their
/// own commit clocks, and their own completion.
/// `mut_vars_read_together_share_a_store` is this program plus the one thing that does
/// relate them: a block reading both.
#[test]
fn unrelated_mut_vars_get_separate_stores() {
    let code = indoc! {r#"
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for x in [1, 2]:
            with begin():
                a := a + x
        for y in [10, 20]:
            with begin():
                b := b + y
        (await_final(a), await_final(b))
    "#};
    assert_eq!(commit_stores(code), vec!["Txn[a]", "Txn[b]"]);
    check_tile(
        code,
        Tile::Record(std::collections::HashMap::from([
            ("_0".into(), Tile::Scalar(ColumnValue::Ints(vec![3]))),
            ("_1".into(), Tile::Scalar(ColumnValue::Ints(vec![30]))),
        ])),
    );
}

/// **Atomicity holds the store together.** One block writing both keys means they
/// advance at one commit tick, so they stay one store however the program is
/// otherwise shaped.
#[test]
fn registers_written_in_one_block_share_a_store() {
    let code = indoc! {r#"
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for x in [1, 2]:
            with begin():
                a := a + x
                b := b - x
        await_final(a) * 100 + await_final(b)
    "#};
    assert_eq!(commit_stores(code), vec!["Txn[a,b]"]);
    check_tile(code, Tile::Scalar(ColumnValue::Ints(vec![297])));
}

/// **Snapshot consistency** holds a store together too, and writes alone do not show it:
/// nothing writes both mutable variables, but one block reads both, latching them at a
/// single frontier, so they must come from one history record. The writers are
/// exactly those of `unrelated_mut_vars_get_separate_stores` — only this read is added.
///
/// The read stays a `with begin():` block because it *is* the subject; what is dropped is
/// any assertion on the value it feeds. That value is an as-of sample at the reading
/// transaction's arbitrary commit position, so pinning a number would pin a scheduling
/// artifact.
#[test]
fn mut_vars_read_together_share_a_store() {
    let code = indoc! {r#"
        out = defer()
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for x in [1, 2]:
            with begin():
                a := a + x
        for y in [10, 20]:
            with begin():
                b := b + y
        with begin():
            out << a * 100 + b
        out
    "#};
    assert_eq!(commit_stores(code), vec!["Txn[a,b]"]);
}

/// A mutable variable a *writing* block reads to decide its commit is read at that commit's
/// snapshot, so the read alone pulls it into the store — no write to `limit` is
/// needed. (`limit` is never written, so it is a read-only key of the store. The key
/// order is the block's footprint order, which is where the guard reads them, not the
/// declaration order.)
#[test]
fn a_mut_var_read_by_a_writing_block_joins_its_store() {
    let code = indoc! {r#"
        limit: Mut(Int, Txn) := 25
        total: Mut(Int, Txn) := 0
        for x in [10, 20]:
            with begin():
                if total + x <= limit:
                    total := total + x
        await_final(total)
    "#};
    assert_eq!(commit_stores(code), vec!["Txn[total,limit]"]);
    check_tile(code, Tile::Scalar(ColumnValue::Ints(vec![10])));
}

/// A mutable variable **no block writes** is not a store key. Nothing can advance it, so its
/// history is constant at its seed and reading it costs a key to learn what the
/// declaration already says — it keeps its introduction on the spine and relates
/// nothing, which is why `lim` neither joins `tot`'s store nor forms one of its own.
/// (Contrast `a_mut_var_read_by_a_writing_block_joins_its_store`, whose unwritten
/// `limit` *is* a key: a **writing** block reads it, so it is read at that block's
/// commit snapshot.)
///
/// The read-only block is required — it is the only way an unwritten mutable variable reaches
/// a footprint at all — so the fed value is an arbitrary as-of sample and is not
/// asserted. The store list is what this test owns.
#[test]
fn a_mut_var_no_block_writes_is_not_a_store_key() {
    let code = indoc! {r#"
        out = defer()
        lim: Mut(Int, Txn) := 5
        tot: Mut(Int, Txn) := 0
        for x in [1, 2]:
            with begin():
                tot := tot + x
        with begin():
            out << tot + lim
        out
    "#};
    assert_eq!(commit_stores(code), vec!["Txn[tot]"]);
}

/// A defer fed **inside** a store is consumed inside it. The tap that carries `out`
/// is bound by the store's own body, so a consumer left above the letrec would name a
/// binding that does not exist there. The consumption is a `let` rather than the tail
/// expression on purpose: a tail is placed by the walk's base case, so only a
/// statement exercises the level assignment.
#[test]
fn a_defer_fed_inside_a_store_is_consumed_inside_it() {
    let code = indoc! {r#"
        out = defer()
        a: Mut(Int, Txn) := 0
        for x in [1, 2]:
            with begin():
                a := a + x
                out << a
        t = sum(out)
        t
    "#};
    check_tile(code, Tile::Scalar(ColumnValue::Ints(vec![4])));
}

/// The same, for the feed of a **read-only** block. That block is unwrapped onto the
/// spine, so its feed survives as an effect statement and is carried into the store it
/// reads — and an effect statement that feeds a defer is therefore something a later
/// statement can depend on, even though it binds nothing.
///
/// The defect this pins was a *compile* failure (`as_of source must be a bare store
/// mutable variable read`), so compiling and evaluating is the assertion; the fed value is an
/// arbitrary as-of sample and is not pinned.
#[test]
fn a_defer_fed_by_a_read_only_block_is_consumed_inside_its_store() {
    let code = indoc! {r#"
        out = defer()
        a: Mut(Int, Txn) := 0
        for x in [1, 2]:
            with begin():
                a := a + x
        with begin():
            out << a
        t = sum(out)
        t
    "#};
    assert_eq!(commit_stores(code), vec!["Txn[a]"]);
}

/// A **cross-domain induction read** alongside a second, unrelated store, pinning the
/// nesting: `cnt` is an induction accumulator a commit decision reads, so its letrec has
/// to be outside the store that reads it. With two stores to be outside of, the fold
/// stays **outermost**, wrapping the whole nest rather than interleaving — which is why
/// the carriers come out induction-first. `a` accumulates 1 + 2 = 3 as `cnt` reaches 2;
/// `b` is untouched by any of it.
#[test]
fn a_cross_domain_read_coexists_with_a_second_store() {
    let code = indoc! {r#"
        cnt := 0
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for x in [1, 2]:
            cnt := cnt + 1
            with begin():
                a := a + cnt
        for y in [10, 20]:
            with begin():
                b := b + y
        (await_final(a), await_final(b))
    "#};
    assert_eq!(commit_stores(code), vec!["[0, 1][cnt]", "Txn[a]", "Txn[b]"]);
    check_tile(
        code,
        Tile::Record(std::collections::HashMap::from([
            ("_0".into(), Tile::Scalar(ColumnValue::Ints(vec![3]))),
            ("_1".into(), Tile::Scalar(ColumnValue::Ints(vec![30]))),
        ])),
    );
}

/// **Phase separation through a writer's iteration source.** The extent of `b`'s block
/// is computed from `a`'s final value, so the source binding is carried into `a`'s store
/// and `b`'s letrec — nested inside it — reads it there. Legal, and the shape the
/// nesting order exists for: `a`'s writers all precede the await, so `a`'s store is
/// always the outer one.
#[test]
fn a_writer_source_may_be_computed_from_an_earlier_store_s_await() {
    let code = indoc! {r#"
        a: Mut(Int, Txn) := 100
        for r in [10]:
            with begin():
                a := a - r
        fa = await_final(a)
        reqs = [x + fa for x in [1, 2]]
        b: Mut(Int, Txn) := 0
        for r in reqs:
            with begin():
                b := b + r
        await_final(b)
    "#};
    assert_eq!(commit_stores(code), vec!["Txn[a]", "Txn[b]"]);
    check_tile(code, Tile::Scalar(ColumnValue::Ints(vec![183])));
}

/// A cross-domain accumulator that itself **depends on an await** does not go
/// outermost. `acc` is seeded from `await_final(a)`, so its letrec has to be inside
/// `a`'s store — while still being outside `b`'s store, which reads it. The store list
/// is the assertion: the induction carrier sits *between* the two commit stores rather
/// than wrapping both.
///
/// The two demands cannot conflict. `a`'s writers all precede the await (a later
/// mention is rejected by linearity) and `b`'s block follows the accumulator's loop, so
/// `a`'s keys always occur first and `b`'s store is always the inner one; and the two
/// cannot be one store, which is the cycle `check_store_acyclicity` rejects.
#[test]
fn a_cross_domain_accumulator_depending_on_an_await_nests_inside_that_store() {
    let code = indoc! {r#"
        a: Mut(Int, Txn) := 100
        for r in [10]:
            with begin():
                a := a - r
        acc := await_final(a)
        for x in [1, 2]:
            acc := acc + 1
        b: Mut(Int, Txn) := 0
        for r in [1]:
            with begin():
                b := b + acc
        await_final(b)
    "#};
    assert_eq!(commit_stores(code), vec!["Txn[a]", "[0, 1][acc]", "Txn[b]"]);
    check_tile(code, Tile::Scalar(ColumnValue::Ints(vec![92])));
}

/// A finite mutable variable completes even though an unrelated one never does.
///
/// `b` is driven by a live source that never ends, so `await_final(b)` cannot resolve —
/// correctly, since there is no final value to report. `a`'s writers are a finite loop,
/// so its completion read resolves, unlike `b`'s. The companion
/// `a_finite_mut_var_completes_despite_a_live_writer_it_shares_a_block_with` is the
/// same claim where the two are keys of one store, which is the harder half.
///
/// The two halves of the reply are the assertion: one settles, the other stays
/// unresolved, in the same program and the same pull.
#[test]
fn a_finite_mut_var_completes_despite_a_live_unrelated_writer() {
    let code = indoc! {r#"
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for x in [1, 2]:
            with begin():
                a := a + x
        for req in source1():
            with begin():
                b := b + req
        (await_final(a), await_final(b))
    "#};

    let mut ctx = GlobalContext::default();
    let src = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_source(src.clone());
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
    assert_eq!(stores_in(&compiled.ast), vec!["Txn[a]", "Txn[b]"]);
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();
    let ug = producer.tiling().universal_guard();

    // One request arrives, and the source is left **open** — no
    // terminal yield predicate — so `b`'s writer never drains.
    src.borrow_mut()
        .add_data(&[(Value::UInt(0), Value::Int(100))]);
    ctx.scheduler().check_for_notifications();
    let mut result = producer.get(ug.clone());
    for _ in 0..64 {
        result = producer.get(ug.clone());
    }

    let Tile::Record(fields) = &result else {
        panic!("expected a record of both replies, got {result:?}");
    };
    assert_eq!(
        fields.get("_0"),
        Some(&Tile::Scalar(ColumnValue::Ints(vec![3]))),
        "the finite mutable variable's completion read must settle; got {result:?}"
    );
    assert!(
        fields.get("_1").is_some_and(Tile::is_empty),
        "the live mutable variable has no final value to report; got {result:?}"
    );
}

/// The same claim where the two variables are **keys of one store**: a block writes both,
/// so they share a commit clock, and `b` then gets a second writer off a live source.
/// Nothing can write `a` after the finite loop drains, so `await_final(a)` settles —
/// completion is a property of `a`'s own writers, not of every writer that commits
/// alongside it (the CHL spec, "`await_final`").
///
/// This is the case store-level completion got wrong: `Txn[a,b]` is one store, one
/// `terminal` flag, and that flag stays false forever because `b`'s writer is live. The
/// store-count assertion is what pins the two variables together — without it the
/// program could pass by being partitioned rather than by closing per key.
#[test]
fn a_finite_mut_var_completes_despite_a_live_writer_it_shares_a_block_with() {
    let code = indoc! {r#"
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for x in [1, 2]:
            with begin():
                a := a + x
                b := b + x
        for req in source1():
            with begin():
                b := b + req
        (await_final(a), await_final(b))
    "#};

    let mut ctx = GlobalContext::default();
    let src = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_source(src.clone());
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
    assert_eq!(
        stores_in(&compiled.ast),
        vec!["Txn[a,b]"],
        "the shared block must put both keys in one store, or this tests nothing"
    );
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();
    let ug = producer.tiling().universal_guard();

    src.borrow_mut()
        .add_data(&[(Value::UInt(0), Value::Int(100))]);
    ctx.scheduler().check_for_notifications();
    let mut result = producer.get(ug.clone());
    for _ in 0..64 {
        result = producer.get(ug.clone());
    }

    let Tile::Record(fields) = &result else {
        panic!("expected a record of both replies, got {result:?}");
    };
    assert_eq!(
        fields.get("_0"),
        Some(&Tile::Scalar(ColumnValue::Ints(vec![3]))),
        "`a`'s writers have all drained, so its completion read must settle even though \
         its store-mate `b` is still committing; got {result:?}"
    );
    assert!(
        fields.get("_1").is_some_and(Tile::is_empty),
        "`b` still has a live writer, so it has no final value to report; got {result:?}"
    );
}

/// A key a block only **reads** has a statically empty write history, so its terminal read
/// is its seed — settled even while a live writer keeps that store open.
///
/// `{reads ∪ writes}` is one store (`src/ccl/design/mutability.md`, "How many commit stores
/// a program has"), so `limit` shares `total`'s commit clock though nothing writes `limit`.
/// `resolve_writer_free_awaits` gates on the **write** footprints for exactly this reason:
/// gated on footprint keys instead, `limit` would reach a runtime completion read and wait
/// on a store that never closes. The store-count assertion pins the two keys together —
/// without it the program could pass by being partitioned instead.
#[test]
fn a_read_only_mentioned_key_completes_while_a_live_writer_runs() {
    let code = indoc! {r#"
        total: Mut(Int, Txn) := 0
        limit: Mut(Int, Txn) := 100
        for req in source1():
            with begin():
                total := total + req + limit
        await_final(limit)
    "#};

    let mut ctx = GlobalContext::default();
    let src = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_source(src.clone());
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
    assert_eq!(
        stores_in(&compiled.ast),
        vec!["Txn[total,limit]"],
        "the read must put both keys in one store, or this tests nothing"
    );
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();
    let ug = producer.tiling().universal_guard();

    src.borrow_mut()
        .add_data(&[(Value::UInt(0), Value::Int(5))]);
    ctx.scheduler().check_for_notifications();
    let mut result = producer.get(ug.clone());
    for _ in 0..64 {
        result = producer.get(ug.clone());
    }
    assert_eq!(
        result,
        Tile::Scalar(ColumnValue::Ints(vec![100])),
        "nothing writes `limit`, so its terminal read is its initializer even though \
         `total`'s live writer keeps the store open; got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Read rules and rejected shapes
// ---------------------------------------------------------------------------

/// A transactional mutable variable may be read only inside a `with begin():` block, and
/// that is permanent rather than a current limitation (the CHL spec, "8.3 Reads"). The
/// diagnostic names both legal reads: wrap it in a block, or `await_final` it.
#[test]
fn bare_txn_read_outside_tx_rejected() {
    check_compile_error(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100
            with begin():
                pool := pool - 10
            pool
        "#},
        "read transactional variable `pool` inside a `with begin():` block",
    );
}

/// The gate follows a `Mut(_, Txn)` **parameter** into the callee: a by-reference pass is
/// the one mention lowering lets through, and it hands the callee a mutable variable in
/// its own right, so a read of it there obeys the same rule. Reading only inside a block
/// is permanent (the CHL spec, "8.3 Reads"), so it holds through a function boundary as
/// well as at the top level.
#[test]
fn bare_read_of_a_mut_param_outside_a_block_rejected() {
    check_compile_error(
        indoc! {r#"
            def draw(p: Mut(Int, Txn), amt):
                before = p
                with begin():
                    p := p - amt
            pool: Mut(Int, Txn) := 100
            draw(pool, 10)
            await_final(pool)
        "#},
        "read transactional variable `p` inside a `with begin():` block",
    );
}

/// A *computed* live cross-endpoint read (`resp << latest + 1`) compiles: the
/// pre-lambda-elim as-of-read rewrite turns it into `as_of(…) ≫ (λ x → x + 1)`,
/// whose reply lambda the elim pass point-frees. Running the rewrite before
/// lambda-elim is what keeps the reply a liftable lambda rather than a
/// point-free `const`.
#[test]
fn computed_live_cross_endpoint_read_compiles() {
    let code = indoc! {r#"
        set_reqs, set_resps = http_serve("0", "POST", "/s")
        get_reqs, get_resps = http_serve("0", "GET", "/g")
        latest: Mut(Int, Txn) := 0
        for msg in set_reqs:
            with begin():
                latest := latest + 1
            set_resps << "ok"
        for req in get_reqs:
            with begin():
                get_resps << latest + 1

    "#};
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    compile_program(&mut ctx, code, consumer)
        .expect("a computed live cross-endpoint read should compile to an as-of join");
}

/// A live cross-endpoint read that combines the *request element* with a mutable variable
/// read (`resp << a + req`) compiles: the as-of-read rewrite turns it into
/// `zip((trigger, as_of(store))) ≫ (λ (req, snap) → e)`, pairing each request with
/// its mutable variable snapshot. The end-to-end value is checked in
/// `live_reply_combines_request_and_store`.
#[test]
fn live_read_combining_request_and_store_compiles() {
    let code = indoc! {r#"
        set_reqs, set_resps = http_serve("0", "POST", "/set")
        get_reqs, get_resps = http_serve("0", "GET", "/get")
        a: Mut(String, Txn) := "a0"
        for msg in set_reqs:
            with begin():
                a := msg
            set_resps << "ok\n"
        for req in get_reqs:
            with begin():
                get_resps << a + req

    "#};
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    compile_program(&mut ctx, code, consumer).expect(
        "a live reply combining the request with a mutable variable read should compile to a zip read",
    );
}

/// End-to-end live check of the request-plus-variable reply (3b): a batch loop
/// commits the mutable variable to 60, then a **live** source drives replies
/// `resps << store + req`, each pairing the request with the store's as-of snapshot
/// — the `zip((trigger, as_of)) ≫ (λ (req, s) → req + s)` shape driven incrementally.
///
/// The requests are delivered only after the store has drained, which is what makes
/// 65 and 75 assertable: an as-of read latches at its position's arrival, so a request
/// arriving mid-drain would legally observe 0, 10 or 30 instead.
#[test]
fn live_reply_combines_request_and_store() {
    use cambra::ccl::context::CompileResultExt;
    use cambra::ccl::{BaseType, Type};
    use cambra::interpreter::{Extent, TestDataSource, Value, sort_sealed_function_by_domain};
    use std::cell::RefCell;
    use std::rc::Rc;

    let code = indoc! {r#"
        resps = defer()
        store: Mut(Int, Txn) := 0
        for r in [10, 20, 30]:
            with begin():
                store := store + r
        for req in source1():
            with begin():
                resps << store + req
        resps
    "#};
    let mut ctx = GlobalContext::default();
    let src = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_source(src.clone());
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();

    // Drain the commit store first, with no request present: the reader pulls the
    // store on every `get`, and the writer's self-re-arm steps one commit per pull.
    for _ in 0..16 {
        producer.get(producer.tiling().universal_guard());
        ctx.scheduler().check_for_notifications();
    }

    src.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(5)),
        (Value::UInt(1), Value::Int(15)),
    ]);
    src.borrow_mut().set_yield_predicate(Predicate::True);
    ctx.scheduler().check_for_notifications();

    let mut result = producer.get(producer.tiling().universal_guard());
    let mut n = 0;
    while !result.is_terminal() && n < 64 {
        result = producer.get(producer.tiling().universal_guard());
        n += 1;
    }
    result.compact();
    let _ = n;
    assert_eq!(
        sort_sealed_function_by_domain(result),
        sort_sealed_function_by_domain(make_int_list(&[65, 75])),
    );
}

/// The retired `with tx():` marker is rejected; the marker is `begin()`.
#[test]
fn old_tx_marker_rejected() {
    check_compile_error(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100
            with tx():
                pool := pool - 10
        "#},
        "begin()",
    );
}

/// Nested transactions are rejected.
#[test]
fn nested_transactions_rejected() {
    check_compile_error(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100
            with begin():
                with begin():
                    pool := pool - 1
        "#},
        "nested",
    );
}

/// An `if`/`else` inside a `with begin():` block **routes** across keys: each
/// arm's writes are scoped to its path, and the transaction commits
/// unconditionally (both arms write). Over `[1, 2, 3]`: x=1 → else → b += 1;
/// x=2 → a += 2; x=3 → a += 3. Final a = 5, b = 1 — read via the mutable variable carry
/// (`get_prev_txn`), each iteration one commit.
#[test]
fn tx_if_else_routes_across_keys() {
    check_tile(
        indoc! {r#"
            a: Mut(Int, Txn) := 0
            b: Mut(Int, Txn) := 0
            for x in [1, 2, 3]:
                with begin():
                    if x >= 2:
                        a := a + x
                    else:
                        b := b + x
            await_final(a) + await_final(b)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![6])),
    );
}

/// **Absolute** (non-RMW) conditional writes routing across keys: each arm sets
/// its key outright (`a := 5`, not `a := a + x`), so neither key is read in the
/// block. The key an arm does *not* write must still **carry** its prior
/// committed value — which is only expressible as that key's read snapshot, so
/// `collect_footprint` finalizes each conditionally-written key into the read set
/// (a plain write-only key would have no snapshot to carry). Over `[1, 2, 3]`:
/// x=1 → else → b := 6 (a carries 0); x=2, x=3 → a := 5 (b carries 6). Final
/// a = 5, b = 6, so `out << a + b` = 11.
#[test]
fn tx_if_else_absolute_writes_route_across_keys() {
    check_tile(
        indoc! {r#"
            a: Mut(Int, Txn) := 0
            b: Mut(Int, Txn) := 0
            for x in [1, 2, 3]:
                with begin():
                    if x >= 2:
                        a := 5
                    else:
                        b := 6
            await_final(a) + await_final(b)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![11])),
    );
}

/// An `elif` chain (no `else`) inside a transaction: first-match per position,
/// the trailing implicit arm the deny (a position matching no guard does not
/// commit). `a := 0`, over `[3, 2, 1]`: x=3 → `if` → a += 3; x=2 → `elif` →
/// a += 1; x=1 → neither → deny. Final a = 4, which `await_final` reports whatever
/// order the three positions commit in.
#[test]
fn tx_if_elif_first_match() {
    check_tile(
        indoc! {r#"
            a: Mut(Int, Txn) := 0
            for x in [3, 2, 1]:
                with begin():
                    if x >= 3:
                        a := a + x
                    elif x >= 2:
                        a := a + 1
            await_final(a)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![4])),
    );
}

/// The same chain **leading with a deny**: `x=1` matches no guard, so the first
/// transaction commits nothing and the store's first commit lands at a later position.
/// `await_final` reports 4 regardless, because it reduces the whole history rather than
/// sampling it — the ordering of commits within the store never reaches the value.
#[test]
fn tx_if_elif_leading_deny() {
    check_tile(
        indoc! {r#"
            a: Mut(Int, Txn) := 0
            for x in [1, 2, 3]:
                with begin():
                    if x >= 3:
                        a := a + x
                    elif x >= 2:
                        a := a + 1
            await_final(a)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![4])),
    );
}

/// Multiple sibling `if cond:` guards in one block: each scopes only its own
/// write, and the transaction commits on the disjunction of the write paths (a
/// write under a passing guard is no longer dropped when an unrelated guard
/// fails — the path-scoped deny semantics). Over `[5]`: `a >= 0` holds → a += 5;
/// `r > 100` fails → b carries. Final a = 5.
#[test]
fn multiple_if_guards_route_independently() {
    check_tile(
        indoc! {r#"
            a: Mut(Int, Txn) := 0
            b: Mut(Int, Txn) := 0
            for r in [5]:
                with begin():
                    if a >= 0:
                        a := a + r
                    if r > 100:
                        b := b + r
            await_final(a)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![5])),
    );
}

/// `Txn` is never inferred: a transactional mutable variable must be spelled
/// `Mut(V, Txn)`. A fully-inferred bare `:=` mutable variable is an *induction* accumulator, so
/// writing it inside a `with begin():` block is rejected — the block did not
/// silently promote it to a `Txn` mutable variable.
#[test]
fn txn_domain_never_inferred() {
    check_compile_error(
        indoc! {r#"
            x := 0
            with begin():
                x := x + 1
            x
        "#},
        "`x` is written inside a `with begin():` block that commits no transactional mutable variable",
    );
}

/// C2: an induction accumulator (`Mut(…)`, non-`Txn`) written inside a `with
/// begin():` block is rejected at lowering — `transact_phase` folds only
/// transactional writes, so an induction write would be silently swallowed
/// (a block-local shadow that dies at block end, computing `[0, 0, …]`).
#[test]
fn induction_write_inside_begin_block_rejected() {
    check_compile_error(
        indoc! {r#"
            cnt: Mut(Int) := 0
            with begin():
                cnt := cnt + 1
            cnt
        "#},
        "`cnt` is written inside a `with begin():` block that commits no transactional mutable variable",
    );
}

/// A *guarded* induction write in a **mixed** block — one that *does* commit a
/// transactional mutable variable — is rejected. `check_no_induction_only_transactions`
/// passes (the block commits `total`), but the guarded `cnt += 1` is not liftable
/// by `partition_spine` and would be silently dropped from the decision record.
/// A dedicated pre-check (`check_no_guarded_induction_write_in_block`) catches it.
#[test]
fn guarded_induction_write_in_mixed_block_rejected() {
    check_compile_error(
        indoc! {r#"
            total: Mut(Int, Txn) := 0
            cnt: Mut(Int) := 0
            for x in [1, 2, 3]:
                with begin():
                    total := total + x
                    if x >= 2:
                        cnt := cnt + 1
            cnt
        "#},
        "guarded induction write in a transaction block is not supported",
    );
}

/// C3: a write to a transactional mutable variable *outside* any `with begin():` block
/// is rejected (write-side mirror of the read gate). Otherwise it becomes a plain
/// sequential `let` shadow that silently hides every committed value.
#[test]
fn out_of_block_txn_write_rejected() {
    check_compile_error(
        indoc! {r#"
            store: Mut(Int, Txn) := 100
            store := 50
            0
        "#},
        "write transactional variable `store`",
    );
}

/// C3, by-reference flavor: a `Mut(_, Txn)` writer body that assigns its mutable variable
/// *without* a `with begin():` block is rejected at lowering of the body.
#[test]
fn by_ref_txn_write_without_block_rejected() {
    check_compile_error(
        indoc! {r#"
            store: Mut(Int, Txn) := 0
            def w(p: Mut(Int, Txn)):
                p := 50
            w(store)
            0
        "#},
        "write transactional variable `p`",
    );
}

/// C4: a by-reference transactional writer *called inside* a `with begin():`
/// block is a nested transaction — post-inline the callee's own transaction
/// `For` lands in the outer block, where the phase would otherwise silently
/// absorb it. Rejected on the inlined tree (the textual nested-`with` check
/// cannot see a transaction reached via a call).
#[test]
fn txn_writer_called_inside_block_rejected() {
    check_compile_error(
        indoc! {r#"
            out = defer()
            pool: Mut(Int, Txn) := 100
            def do_it(p: Mut(Int, Txn)):
                with begin():
                    p := p - 10
            with begin():
                pool := pool - 5
                y = do_it(pool)
            with begin():
                out << pool
            out
        "#},
        "nested",
    );
}

/// PR-2 registry leak (same class as PR-1's mutable-registry leak): a
/// `Mut(_, Txn)` mutable variable declared *inside* a `def` body must not leak into the
/// transactional registry and falsely gate a like-spelled top-level local. The
/// def-body scope snapshots and restores *both* mutable variable registries, so `v`
/// outside `f` is an ordinary local (assignable, readable).
#[test]
fn txn_mut_var_in_def_body_does_not_leak_to_outer_local() {
    check_scalar(
        indoc! {r#"
            def f(x):
                v: Mut(Int, Txn) := 0
                x
            v = 5
            v
        "#},
        cambra::interpreter::Value::Int(5),
    );
}

/// The `with t = begin():` transaction handle is rejected at lowering (not yet
/// implemented): binding it and referencing the commit time inside the block
/// would otherwise silently resolve to an outer `t` or fail opaquely.
#[test]
fn transaction_handle_binding_rejected() {
    check_compile_error(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100
            for r in [10]:
                with t = begin():
                    pool := pool - r
        "#},
        "transaction handle is not supported yet",
    );
}

/// C5: the out-of-block read gate applies to a bare mutable variable passed as an
/// argument to an *ordinary* function (only a `Mut`-parameter callee accepts a
/// bare mutable variable pass and bypasses the gate). `f(store)` reads the mutable variable
/// outside a block, so it is rejected.
#[test]
fn bare_mut_var_arg_to_ordinary_fn_is_gated() {
    check_compile_error(
        indoc! {r#"
            store: Mut(Int, Txn) := 0
            def f(x):
                x + 1
            f(store)
        "#},
        "read transactional variable `store`",
    );
}

// ---------------------------------------------------------------------------
// A variable's identity is the `Mut(_, Txn)` type on the α-unique binding, not the
// surface base name — so a local variable merely *spelled* like a mutable variable is
// not confused for it (A1: a compiler panic; A2: a spurious rejection).
// ---------------------------------------------------------------------------

/// A1 regression (no panic): a comprehension whose loop variable is *spelled*
/// like the mutable variable (`[store for store in [1, 2, 3]]`) must not be swept into
/// the transaction footprint — the comprehension var is a distinct α-unique
/// binder. Before the fix, base-name footprint collection matched it, then
/// panicked looking for its (non-existent) mutable variable `let`. The mutable variable write is
/// `store = store - sum([1, 2, 3])` = 100 − 6 = 94, read back by the trailing
/// read-only transaction (a live as-of read at position 0).
#[test]
fn like_named_comprehension_var_does_not_panic() {
    check_tile(
        indoc! {r#"
            store: Mut(Int, Txn) := 100
            for r in [10]:
                with begin():
                    store := store - sum([store for store in [1, 2, 3]])
            await_final(store)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![94])),
    );
}

/// A2 regression (no false rejection): a loop target *spelled* like a mutable variable
/// (`for store in [1, 2, 3]`) is a genuine local, not an out-of-block store
/// read. Before the fix, the base-name read gate rejected `store` inside the
/// loop even though no transaction is present. The loop feeds `store + 1` per
/// iteration → `[2, 3, 4]` at loop positions `[0, 1, 2]`; the mutable variable itself is
/// never written, so `transact_phase` is a no-op on it.
#[test]
fn like_named_loop_var_is_not_a_store_read() {
    check_tile(
        indoc! {r#"
            out = defer()
            store: Mut(Int, Txn) := 0
            for store in [1, 2, 3]:
                out << store + 1
            out
        "#},
        make_int_list(&[2, 3, 4]),
    );
}

/// Stage-1 interop: one loop carries BOTH a per-iteration transaction (the
/// mutable variable `store`, written in the block) AND a sibling induction accumulator
/// (`cnt`, written outside the block), with a reply reading the accumulator. The
/// two run on independent domains — `cnt` sequences on the request loop, `store`
/// on the commit order — so the reply `resps << cnt` yields the induction
/// running total `[1, 2, 3]`, request-indexed, regardless of the commit clock.
#[test]
fn mixed_txn_and_induction_reply_reads_accumulator() {
    check_tile(
        indoc! {r#"
            resps = defer()
            store: Mut(Int, Txn) := 0
            cnt: Mut(Int) := 0
            for r in [10, 20, 30]:
                with begin():
                    store := store + r
                cnt := cnt + 1
                resps << cnt
            resps
        "#},
        make_int_list(&[1, 2, 3]),
    );
}

/// Stage-1 interop, mutable variable side: the mutable variable accumulates transactionally across
/// the same mixed loop (0 + 10 + 20 + 30 = 60), read back by a trailing
/// read-only transaction, while the sibling induction `cnt` advances
/// independently and does not join the atomic commit.
#[test]
fn mixed_txn_and_induction_store_accumulates() {
    check_tile(
        indoc! {r#"
            store: Mut(Int, Txn) := 0
            cnt: Mut(Int) := 0
            for r in [10, 20, 30]:
                with begin():
                    store := store + r
                cnt := cnt + 1
            await_final(store)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![60])),
    );
}

/// Stage-2 interop: the induction write sits *physically inside* the `with
/// begin():` block (`store := store + r; cnt := cnt + 1`), the literal
/// worked-example form. `transact_phase` partitions the block by mutable variable domain —
/// the mutable variable write forms the commit decision; the induction `cnt` write is
/// lifted onto the enclosing loop as its own recurrence — so the result matches
/// the sibling form: `resps << cnt` yields the request-indexed running total.
#[test]
fn mixed_txn_and_induction_write_inside_block() {
    check_tile(
        indoc! {r#"
            resps = defer()
            store: Mut(Int, Txn) := 0
            cnt: Mut(Int) := 0
            for r in [10, 20, 30]:
                with begin():
                    store := store + r
                    cnt := cnt + 1
                resps << cnt
            resps
        "#},
        make_int_list(&[1, 2, 3]),
    );
}

/// Stage-2 interop, mutable variable side: with the induction write inside the block, the
/// mutable variable still accumulates transactionally (0 + 10 + 20 + 30 = 60) and the
/// lifted induction `cnt` stays out of the atomic commit.
#[test]
fn mixed_txn_and_induction_write_inside_block_store_accumulates() {
    check_tile(
        indoc! {r#"
            store: Mut(Int, Txn) := 0
            cnt: Mut(Int) := 0
            for r in [10, 20, 30]:
                with begin():
                    store := store + r
                    cnt := cnt + 1
            await_final(store)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![60])),
    );
}

/// Stage-3 cross-domain read: a commit decision reads an induction accumulator at
/// its request position (`store := store + cnt` inside the block). The accumulator
/// is threaded through the writer source (a `zip` of the loop iter and `cnt`'s
/// per-position view) and the commit engine co-iterates it — so `cnt` = 1,2,3 and
/// the mutable variable accumulates 0 + 1 + 2 + 3 = 6. `cnt` sequences on the request loop
/// (its own domain), independent of the commit clock.
#[test]
fn commit_decision_reads_induction_accumulator() {
    check_tile(
        indoc! {r#"
            store: Mut(Int, Txn) := 0
            cnt: Mut(Int) := 0
            for r in [10, 20, 30]:
                cnt := cnt + 1
                with begin():
                    store := store + cnt
            await_final(store)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![6])),
    );
}

/// Cross-domain read, **broadcast** side: the commit decision reads an induction
/// accumulator written by a *different, completed* loop (`cnt` accumulates over
/// `[1,2,3]` → 3; the txn loop over `[10,20]` reads it). Unlike the co-indexed
/// case above (same loop → request-indexed `zip`), a different loop's accumulator
/// has no per-request correspondence, so its final value is broadcast into every
/// transaction. Observed via an **in-block** (commit-ordered) reply — not a
/// trailing read, which is an arbitrary as-of sample — so the committed values
/// are deterministic: `pool` draws down `100 → 97 → 94` over commit ticks 1, 2.
/// Exercises the writer's deferred-wakeup convergence: the broadcast `cnt`'s
/// `ExtractFinal` is empty until its loop's own cycle drains, so the writer
/// re-arms itself on the wakeup queue each not-ready pull rather than deadlocking
/// on the stalled commit frontier; the in-block reply demands each commit and
/// drives that convergence.
#[test]
fn commit_decision_reads_cross_loop_accumulator_broadcast() {
    check_tile(
        indoc! {r#"
            cnt := 0
            for i in [1, 2, 3]:
                cnt := cnt + 1
            out = defer()
            pool: Mut(Int, Txn) := 100
            for r in [10, 20]:
                with begin():
                    pool := pool - cnt
                    out << pool
            out
        "#},
        commit_stream(&[1, 2], &[97, 94]),
    );
}

/// A broadcast reader racing a second writer. Writer A reads a completed sibling
/// loop's `cnt` (broadcast — converges over several pulls); writer B draws eagerly
/// and commits *while A is still waiting*, advancing the store frontier mid-wait.
/// This exercises the frontier-change-during-not-ready path: A's pending
/// body-input row was pushed at the pre-commit frontier, so on the advanced
/// frontier the writer re-pushes at the new snapshot and the stale row is orphaned
/// (compacted on commit) — the value read is the *current* snapshot, not the stale
/// one. Observed via in-block replies (which serialization commits first is
/// arbitrary), so asserted as a valid drawdown: both draws — `cnt`(3) and 5 —
/// commit exactly once, conserving the pool (final 92).
#[test]
fn broadcast_read_races_a_second_writer() {
    let tile = run_pipeline(indoc! {r#"
            cnt := 0
            for i in [1, 2, 3]:
                cnt := cnt + 1
            out = defer()
            pool: Mut(Int, Txn) := 100
            for r in [10]:
                with begin():
                    pool := pool - cnt
                    out << pool
            for r in [5]:
                with begin():
                    pool := pool - r
                    out << pool
            out
        "#});
    assert_drawdown_replies(&tile, 100, &[3, 5]);
}

/// Broadcast off a finite **async** (data-source) sibling loop. `cnt` counts a
/// `TestDataSource`'s three elements — a loop that converges only as
/// the source's data arrives (via scheduler notifications), not synchronously.
/// The txn decision reads `cnt`'s value (broadcast, 3), observed via an in-block
/// reply — one commit, `pool = 100 − 3 = 97` at commit tick 1. This is the case
/// the old in-`get` pump could not handle (it spun without yielding to the
/// scheduler); the deferred-wakeup path drives it — each not-ready pull re-arms
/// the writer, and `check_for_notifications` delivers both the source's data and
/// the writer's wakeups until the sibling loop (and the commit) resolve. Driven
/// exactly as `src/main.rs` does — notification-gated, re-pull to terminal.
#[test]
fn broadcast_off_async_source_sibling_loop() {
    let code = indoc! {r#"
        cnt := 0
        for x in src():
            cnt := cnt + 1
        out = defer()
        pool: Mut(Int, Txn) := 100
        for r in [10]:
            with begin():
                pool := pool - cnt
                out << pool
        out
    "#};
    let mut ctx = GlobalContext::default();
    let src = Rc::new(RefCell::new(TestDataSource::new(
        "src",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    src.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(1)),
        (Value::UInt(1), Value::Int(2)),
        (Value::UInt(2), Value::Int(3)),
    ]);
    // A *complete* finite source: all keys available, no more coming — so the
    // sibling loop terminates and `cnt`'s final (3) is decided.
    src.borrow_mut().set_yield_predicate(Predicate::True);
    ctx.register_source(src.clone());

    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
    let mut producer = compiled
        .main_mut()
        .and_then(|o| o.producer.take())
        .expect("program has a `main` output");
    let universal = producer.tiling().universal_guard();

    // Notification-gated re-pull to terminal, bounded so a lost-wakeup regression
    // fails loudly instead of hanging.
    let mut result = producer.get(universal.clone());
    let mut iters = 0usize;
    while !result.is_terminal() {
        iters += 1;
        assert!(iters < 1024, "async-source broadcast did not converge");
        ctx.scheduler().check_for_notifications();
        result = producer.get(universal.clone());
    }
    result.compact();
    assert_eq!(result, commit_stream(&[1], &[97]));
}

/// Stage-3 cross-domain read, reply side: the same loop reads `cnt` in the commit
/// decision *and* replies with it outside the block. The reply rides the induction
/// domain (request-indexed → `[1,2,3]`) while the mutable variable accumulates to 6.
#[test]
fn commit_decision_reads_induction_accumulator_with_reply() {
    check_tile(
        indoc! {r#"
            resps = defer()
            store: Mut(Int, Txn) := 0
            cnt: Mut(Int) := 0
            for r in [10, 20, 30]:
                cnt := cnt + 1
                with begin():
                    store := store + cnt
                resps << cnt
            resps
        "#},
        make_int_list(&[1, 2, 3]),
    );
}

/// Stage-3 commit-ordered/gated reply (in-block feed): a reply *inside* the block
/// rides the commit record as a tap (commit-tick-indexed, like `progress_feed_in_tx`),
/// so it is sequenced after the commit and — the gating half — a *denied*
/// transaction replies nothing. Here `pool` starts at 100 and `r = 70, 50, 20`
/// draws down; `r = 50` fails `pool >= r` (pool is 30) so its transaction denies.
/// The reply reads the induction counter `cnt` (a Stage-3 cross-domain read inside
/// the tap): `cnt` advances 1,2,3 on the request loop regardless of commit, but
/// only the two *committed* iterations reply — values `[1, 3]` at commit ticks 1,2.
#[test]
fn commit_gated_reply_reading_induction_counter() {
    check_tile(
        indoc! {r#"
            resps = defer()
            pool: Mut(Int, Txn) := 100
            cnt: Mut(Int) := 0
            for r in [70, 50, 20]:
                cnt := cnt + 1
                with begin():
                    if pool >= r:
                        pool := pool - r
                        resps << cnt
            resps
        "#},
        commit_stream(&[1, 2], &[1, 3]),
    );
}

/// Stage-3 commit-ordered reply that commits every iteration: the in-block reply
/// reads the induction counter `cnt` (cross-domain, via the writer co-iteration)
/// and — since no transaction denies — every request replies, values `[1, 2, 3]`
/// at commit ticks 1,2,3. The mutable variable accumulates alongside; this is the worked
/// example's `incr` endpoint in finite-batch form (reply riding the commit,
/// reading the counter).
#[test]
fn commit_ordered_reply_reading_induction_counter() {
    check_tile(
        indoc! {r#"
            resps = defer()
            store: Mut(Int, Txn) := 0
            cnt: Mut(Int) := 0
            for r in [10, 20, 30]:
                cnt := cnt + 1
                with begin():
                    store := store + r
                    resps << cnt
            resps
        "#},
        commit_stream(&[1, 2, 3], &[1, 2, 3]),
    );
}

/// In-block reply with an interspersed deny: the reply tap `resp << q` rides the
/// writer *decision*, so a denied transaction (`r == 0`, guard false) contributes
/// no tick and no reply, while each committing position emits its
/// read-your-writes value densely. This is the exact reply-path contract (a
/// read-your-writes stream, not an arbitrary as-of sample) and must be preserved
/// exactly under the consumer-driven store: r=0 denies, r=1 commits q:=2 (tick 1),
/// r=2 commits q:=3 (tick 2) → `resp` = [2, 3] over commit ticks [1, 2].
#[test]
fn in_block_reply_with_deny_is_dense() {
    check_tile(
        indoc! {r#"
            resp = defer()
            q: Mut(Int, Txn) := 0
            for r in [0, 1, 2]:
                with begin():
                    if r != 0:
                        q := r + 1
                        resp << q
            resp
        "#},
        commit_stream(&[1, 2], &[2, 3]),
    );
}

/// Live-store progress past an interior deny. A finite writer accumulates `total`
/// with a middle deny (`[10, 0, 20]`: total 0→10, r=0 denies, →30), and a **live**
/// request stream reads `total + req` as an as-of read latched at each request's
/// arrival. The consumer-driven store steps past the deny under the writer's own
/// self-re-arm (no reader-side drive-to-fixpoint), so **every request is served** (no
/// freeze — one reply per request), and the request delivered *after* the writer
/// completes observes the **post-deny** commit (`total = 30`) — which the old
/// producer-side `drive_store_to_fixpoint` stopped short of (a deny stalls the
/// frontier, so the drive returned the pre-deny `total = 10` and a request latching
/// then froze there).
///
/// The two requests arrive at different times because that is the only thing an as-of
/// read's value follows. The first arrives before the writer has drained, so its
/// observation is asserted only to be **non-decreasing** and a member of the committed
/// set; a specific value there would pin whichever commit the schedule happened to
/// reach. The completed value has a name of its own (`await_final`).
#[test]
fn live_read_progresses_past_deny() {
    use cambra::interpreter::sort_sealed_function_by_domain;

    let code = indoc! {r#"
        resps = defer()
        total: Mut(Int, Txn) := 0
        for r in [10, 0, 20]:
            with begin():
                if r != 0:
                    total := total + r
        for req in source1():
            with begin():
                resps << total + req
        resps
    "#};
    let mut ctx = GlobalContext::default();
    let src = Rc::new(RefCell::new(TestDataSource::new(
        "source1",
        Type::Base(BaseType::Int),
        Extent::Base(BaseType::Int),
    )));
    ctx.register_source(src.clone());
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    let mut compiled = compile_program(&mut ctx, code, consumer).unwrap_or_render("<test>", code);
    let mut producer = compiled.main_mut().unwrap().producer.take().unwrap();
    let ug = producer.tiling().universal_guard();

    // Request 0 (req = 100) arrives first and latches whatever the store has then.
    src.borrow_mut()
        .add_data(&[(Value::UInt(0), Value::Int(100))]);
    src.borrow_mut()
        .set_yield_predicate(Predicate::LessThanEq(Value::from(0usize)));
    ctx.scheduler().check_for_notifications();
    let mut result = producer.get(ug.clone());

    // Drive the cyclic store — with its interior deny — to completion, then deliver
    // request 1 (req = 200). Arrival order is what makes its observation assertable:
    // it latches after the writer has drained.
    for _ in 0..32 {
        result = producer.get(ug.clone());
        ctx.scheduler().check_for_notifications();
    }
    src.borrow_mut()
        .add_data(&[(Value::UInt(1), Value::Int(200))]);
    src.borrow_mut().set_yield_predicate(Predicate::True);
    ctx.scheduler().check_for_notifications();
    for _ in 0..32 {
        result = producer.get(ug.clone());
    }
    result.compact();

    let result = sort_sealed_function_by_domain(result);
    let Tile::SealedFunction {
        domain, codomain, ..
    } = &result
    else {
        panic!("expected a SealedFunction reply stream, got {result:?}");
    };
    let Tile::Scalar(ColumnValue::Ints(vals)) = codomain.as_ref() else {
        panic!("expected an Ints reply codomain, got {codomain:?}");
    };
    // No freeze: both requests are served.
    assert_eq!(domain.len(), 2, "both requests served (no freeze)");
    assert_eq!(vals.len(), 2);
    // The observed `total` per request (reply − its req value). Requests carried
    // req = 100 at position 0 and req = 200 at position 1.
    let observed_total: Vec<i64> = vec![vals[0] - 100, vals[1] - 200];
    // Every observed total is a committed member of {0, 10, 30}.
    for t in &observed_total {
        assert!(
            [0, 10, 30].contains(t),
            "observed total {t} must be a committed value in {{0, 10, 30}}"
        );
    }
    // A monotone accumulator sampled at arrival is non-decreasing across requests.
    assert!(
        observed_total[0] <= observed_total[1],
        "later request observes a value >= the earlier one, got {observed_total:?}"
    );
    // The request delivered after the writer completed observes the post-deny commit —
    // the store stepped past the interior deny (which the old drive-to-fixpoint stalled
    // on).
    assert_eq!(
        observed_total[1], 30,
        "the request arriving after the writer drained observes total 30 (past the r=0 deny)"
    );
}

/// Cross-function transactional writer: `def transfer(src, dst, amt)` writes two
/// `Mut(_, Txn)` mutable variables inside one `with begin():` block. Inlining
/// beta-reduces the call so the writes name the caller's `a`/`b` bindings, which
/// `collect_txn_mut_vars` finds on the inlined, typed tree (the whole point of
/// keying mutable variable identity by the `Mut(_, Txn)` type, not a base name). After
/// `transfer(a, b, 30)`: `a` = 100 − 30 = 70, `b` = 0 + 30 = 30 — the trailing
/// read-only transaction reads `a + b` = 100, the conserved total.
#[test]
fn cross_function_transfer_conserves_total() {
    check_tile(
        indoc! {r#"
            def transfer(src: Mut(Int, Txn), dst: Mut(Int, Txn), amt):
                with begin():
                    src := src - amt
                    dst := dst + amt
            a: Mut(Int, Txn) := 100
            b: Mut(Int, Txn) := 0
            transfer(a, b, 30)
            await_final(a) + await_final(b)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![100])),
    );
}

// A heterogeneous multi-key mutable variable: a `Mut(String, Txn)` and a
// `Mut(Int, Txn)` committed together in one block. Regression for the
// variable-wide value extent (`build_commit_store`), which is the union of the
// distinct per-key extents rather than whichever key was iterated last —
// reading either key returns its own type. `label` is declared first, so a
// last-key-wins extent would be `int`, yet the string read must still yield a
// string.
#[test]
fn heterogeneous_multi_key_store_reads_string_key() {
    check_tile(
        indoc! {r#"
            label: Mut(String, Txn) := "init"
            count: Mut(Int, Txn) := 0
            for x in [1, 2, 3]:
                with begin():
                    count := count + x
                    label := "seen"
            await_final(label)
        "#},
        Tile::Scalar(ColumnValue::Strings(vec![SmolStr::new("seen")])),
    );
}

// ---------------------------------------------------------------------------
// commit|abort decision variant: off-path partial op + interleaving
// ---------------------------------------------------------------------------

/// **An off-path partial op does not fault.** A guarded `//` in a
/// conditional transaction write: `if d != 0: acc := acc // d`. The divisor `d`
/// starts at 3 and is zeroed on the first commit, so the second request's guard
/// (`d != 0`, read on the snapshot) is false — an `` `abort ``. The write value `acc
/// // d` rides the lazy `⧺ filter_values(d != 0) ≫ (acc // d)` arm the value-`Case`
/// compiles to, so the division is evaluated only where its guard holds — never at
/// the `d == 0` position. Were the partial op evaluated off-path it would panic on
/// divide-by-zero. First commit: `acc := 100 // 3 = 33` (and `d := 0`); the second
/// aborts, so `acc` stays 33.
///
/// Off-path safety depends on the guard reading the value it protects. Because
/// the lazy `filter_values` union never evaluates the off-path arm, a guard that
/// reads the protected mutable variable (`d != 0`) suppresses the fault. An item-only
/// guard (`if r != 0`) that does *not* read the divisor offers no protection and
/// correctly still faults — that is sound semantics (a guard that doesn't guard
/// the dangerous term), not a limitation; item-only guards otherwise commit and
/// deny normally.
#[test]
fn txn_off_path_guarded_division_does_not_fault() {
    check_tile(
        indoc! {r#"
            d: Mut(Int, Txn) := 3
            acc: Mut(Int, Txn) := 100
            for r in [1, 2]:
                with begin():
                    if d != 0:
                        acc := acc // d
                        d := d - 3
            await_final(acc)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![33])),
    );
}

/// **Interleaved two-writer commit/abort through the store.** Two writer
/// sites on the *same* mutable variable `pool` interleave committing and aborting
/// decisions: `10`/`20` always fit (`` `commit ``), `200`/`300` never do (`` `abort ``).
/// The variant decision flows through the commit-`Store` codomain — each writer's
/// `` {`commit{writes} | `abort} `` stream folds into the shared changelog — and the
/// trailing `get_prev_txn` read reads back the conserved value `100 - 10 - 20 =
/// 70`. The *result* is order-independent by construction — the two commits always
/// fit and the two aborts never do — but note this test exercises only the single
/// interleaving the store's round-robin `drain_start` rotation produces at runtime,
/// not an enumeration of schedules.
#[test]
fn interleaved_two_writer_commit_abort_through_store() {
    check_tile(
        indoc! {r#"
            pool: Mut(Int, Txn) := 100
            for r in [10, 200]:
                with begin():
                    if pool >= r:
                        pool := pool - r
            for r in [20, 300]:
                with begin():
                    if pool >= r:
                        pool := pool - r
            await_final(pool)
        "#},
        Tile::Scalar(ColumnValue::Ints(vec![70])),
    );
}
