//! Transactional stores (`Mut(V, Txn)` + `with begin():`) — the commit-operator
//! path. Batch (finite-loop and standalone) single-variable transactions run
//! end-to-end: `x: Mut(V, Txn)` folds into one shared commit store, each `with
//! begin():` block is a writer. A transactional register is read only inside a
//! `with begin():` block; the batch tests read a value with a trailing standalone
//! read-only transaction (`out = defer(); …; with begin(): out << x`) and assert
//! the fed stream. Every fed-out register read compiles to `AsOf` — an as-of read
//! at the reading transaction's (arbitrary) commit position, indexed by the
//! reading loop — uniformly, whether the reading loop is a live `DataSource`
//! stream, a finite loop, or the standalone read's synthesized singleton. There
//! is no terminal/"final" register read; the trailing standalone read's `out` is
//! the one-element as-of stream at position 0, which under the batch scheduler
//! observes the drained store (a scheduling coincidence, not a promise).
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

// NOTE — these batch programs are *ordering-undefined*, and every expected value
// below is a **timing accident of the current single-threaded engine**, not a
// pinned semantics. A transaction's meaning depends on the commit order, but
// nothing in these programs pins it: a literal-list loop and the synthesized
// standalone singleton leave the order to the engine's serialization
// (`drain_start`), not the program. The only context that *pins* commit order is a
// loop over a live external stream (a `DataSource`), where real arrival order is a
// denotational anchor. These blocks depend only on program start (no source
// arrival, no cross-transaction data dependence), and program start is a single
// event that imposes no order *among* the blocks it triggers — so the event model
// *defines* their commit order as mutually unordered, and the engine may serialize
// them any way, correct under all of them. That is the contract, not a defect; see
// `src/ccl/design/mutability.md` "Ordering and concurrency".
//
// So these are effectively **engine tests**: they assert what one particular
// serialization produces. They would not survive a concurrent scheduler — reorder
// the drain and a different admissible answer appears — and the engine has its own
// direct `CommitEngine` unit tests besides. `multi_writer_grant_deny` looks
// order-independent only because it asserts the final pool, not *which* writer
// succeeded.
//
// TODO(await_final): every trailing `with begin(): out << <register>` in this file
// carries an inline `# TODO(await_final)` marking the same thing at the offending
// line — it reads the register with an arbitrary as-of sample (latched to the
// singleton trigger at that read's own commit position, so `out` is the one-element
// stream at position 0) and observes the drained store only because the
// single-threaded scheduler happens to run it last. The designed `await_final`
// primitive is the real terminal read (`src/ccl/design/mutability.md`
// "await_final"): once it exists, rewrite each of those reads as
// `await_final(<register>)` and the assertions become semantic rather than
// scheduling artifacts.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Single writer draws down a pool: 100 − 10 − 20 − 30 = 40.
#[case::counter(
    indoc! {r#"
        out = defer()
        pool: Mut(Int, Txn) := 100
        for r in [10, 20, 30]:
            with begin():
                pool := pool - r
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << pool
        out
    "#},
    40
)]
// Two writers over one register: the operator serializes + retries, conserving the
// total: 100 − 30 − 40 = 30.
#[case::two_writers(
    indoc! {r#"
        out = defer()
        pool: Mut(Int, Txn) := 100
        for r in [30]:
            with begin():
                pool := pool - r
        for r in [40]:
            with begin():
                pool := pool - r
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << pool
        out
    "#},
    30
)]
// Multi-statement body: a leading `let fee`, a guard, then the write. A: 100 − 33
// = 67; B: 67 ≥ 44 → 67 − 44 = 23.
#[case::multi_stmt(
    indoc! {r#"
        out = defer()
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
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << pool
        out
    "#},
    23
)]
// Computed (non-literal) init `sum([40,30,30]) = 100`, read from an acyclic init
// operator at tick 0; one writer draws 60 → 40.
#[case::computed_init(
    indoc! {r#"
        out = defer()
        pool: Mut(Int, Txn) := sum([40, 30, 30])
        for r in [60]:
            with begin():
                pool := pool - r
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << pool
        out
    "#},
    40
)]
// Writer source bound *after* the register declaration (`reqs` between `pool` and
// the loop). The register letrec is spliced below every source binding, so the
// writer's `Var(reqs)` is in scope — previously this crashed with an internal
// unrecognised-variable error. 100 − 10 − 20 − 30 = 40.
#[case::source_bound_after_store(
    indoc! {r#"
        out = defer()
        pool: Mut(Int, Txn) := 100
        reqs = [10, 20, 30]
        for r in reqs:
            with begin():
                pool := pool - r
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << pool
        out
    "#},
    40
)]
// A single standalone transaction (no enclosing `for`): one commit over a
// synthesized singleton source: 100 − 10 = 90.
#[case::standalone_single(
    indoc! {r#"
        out = defer()
        pool: Mut(Int, Txn) := 100
        with begin():
            pool := pool - 10
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << pool
        out
    "#},
    90
)]
// Two standalone transactions in sequence: two commits on one clock → 70.
#[case::standalone_sequential(
    indoc! {r#"
        out = defer()
        pool: Mut(Int, Txn) := 100
        with begin():
            pool := pool - 10
        with begin():
            pool := pool - 20
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << pool
        out
    "#},
    70
)]
// A standalone transaction composes with loop-based ones on the shared register:
// 100 − 1 − 10 − 20 = 69.
#[case::standalone_then_loop(
    indoc! {r#"
        out = defer()
        pool: Mut(Int, Txn) := 100
        with begin():
            pool := pool - 1
        for r in [10, 20]:
            with begin():
                pool := pool - r
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << pool
        out
    "#},
    69
)]
// Two writers, each drawing several amounts, over one register. The operator
// serializes + retries across all four commits; subtraction conserves the
// total regardless of interleaving: 100 − 10 − 20 − 5 − 15 = 50.
#[case::multi_writer_contention(
    indoc! {r#"
        out = defer()
        pool: Mut(Int, Txn) := 100
        for r in [10, 20]:
            with begin():
                pool := pool - r
        for r in [5, 15]:
            with begin():
                pool := pool - r
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << pool
        out
    "#},
    50
)]
// Three writers on one register compose the same as one: 100 − 10 − 20 − 30 = 40.
#[case::three_writers(
    indoc! {r#"
        out = defer()
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
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << pool
        out
    "#},
    40
)]
// Two writers contend for a pool too small for both draws: whichever the
// operator serializes first commits (pool → 40); the other re-reads 40, fails
// `40 >= 60`, and denies. Order-independent final: 40.
#[case::multi_writer_grant_deny(
    indoc! {r#"
        out = defer()
        pool: Mut(Int, Txn) := 100
        for r in [60]:
            with begin():
                if pool >= r:
                    pool := pool - r
        for r in [60]:
            with begin():
                if pool >= r:
                    pool := pool - r
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << pool
        out
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
        out = defer()
        x: Mut(Int, Txn) := 100
        with begin():
            x := x + 1
            if x > 1000:
                x := x + 10
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << x
        out
    "#},
    101
)]
fn test_transactional_stores(#[case] code: &str, #[case] expected: i64) {
    check_tile(code, commit_stream(&[0], &[expected]));
}

// ---------------------------------------------------------------------------
// Multiple variables in one transaction + read-your-writes (multi-key register)
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// A single trailing read-only transaction reads *both* keys under one snapshot
// (`out << a * 100 + b`) — one consistent view of the finished register.
// `a` and `b` update atomically each iteration: a := sum([1,2,3]) = 6, b := sum of
// squares = 14 → a*100 + b := 614.
#[case::multi_var(
    indoc! {r#"
        out = defer()
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for x in [1, 2, 3]:
            with begin():
                a := a + x
                b := b + x * x
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << a * 100 + b
        out
    "#},
    614
)]
// Cross-variable read: `b = b + a` reads `a`'s snapshot before `a = a + x`, so a
// runs 5,6,8 → b := 19, a ends 11 → 1119.
#[case::multi_var_cross_read(
    indoc! {r#"
        out = defer()
        a: Mut(Int, Txn) := 5
        b: Mut(Int, Txn) := 0
        for x in [1, 2, 3]:
            with begin():
                b := b + a
                a := a + x
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << a * 100 + b
        out
    "#},
    1119
)]
// Read-your-writes across keys: `b = a` after `a = a + x` sees the new `a`. a:
// 0→1→3→6, b: 1,3,6 → final a=6, b=6 → 606.
#[case::read_your_writes_cross_key(
    indoc! {r#"
        out = defer()
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for x in [1, 2, 3]:
            with begin():
                a := a + x
                b := a
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << a * 100 + b
        out
    "#},
    606
)]
// Same key written twice: the second `a = a + 1` reads the first write's value.
// x=10: 0→10→11; x=20: 11→31→32 → 32.
#[case::read_your_writes_same_key(
    indoc! {r#"
        out = defer()
        a: Mut(Int, Txn) := 0
        for x in [10, 20]:
            with begin():
                a := a + x
                a := a + 1
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << a
        out
    "#},
    32
)]
// Read-only register key: `limit` is read in the guard but written nowhere. x=10
// commits (10 ≤ 25); 20/30 denied → total := 10.
#[case::multi_var_readonly_key(
    indoc! {r#"
        out = defer()
        limit: Mut(Int, Txn) := 25
        total: Mut(Int, Txn) := 0
        for x in [10, 20, 30]:
            with begin():
                if total + x <= limit:
                    total := total + x
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << total
        out
    "#},
    10
)]
// Two writers touching *disjoint* keys — no footprint overlap, so neither ever
// invalidates the other. `a` = 1+2 = 3, `b` = 10+20 = 30 → 3*100 + 30 = 330.
#[case::multi_writer_disjoint_keys(
    indoc! {r#"
        out = defer()
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        for x in [1, 2]:
            with begin():
                a := a + x
        for y in [10, 20]:
            with begin():
                b := b + y
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << a * 100 + b
        out
    "#},
    330
)]
// Two writers with *overlapping* footprints: writer 1 writes {a, b}, writer 2
// writes {b, c}. The shared `b` forces serialization, but the sums are
// order-independent: a := 3, b := 1+2+10+20 = 33, c := 30 → 3*10000 + 33*100 + 30
// = 33330.
#[case::multi_writer_overlapping_keys(
    indoc! {r#"
        out = defer()
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
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << a * 10000 + b * 100 + c
        out
    "#},
    33330
)]
// Three keys updated atomically per transaction, all read together under one
// snapshot: a := sum = 6, b := sum of squares = 14, c := count = 3 → 6*10000 +
// 14*100 + 3 = 61403.
#[case::read_three_vars_one_snapshot(
    indoc! {r#"
        out = defer()
        a: Mut(Int, Txn) := 0
        b: Mut(Int, Txn) := 0
        c: Mut(Int, Txn) := 0
        for x in [1, 2, 3]:
            with begin():
                a := a + x
                b := b + x * x
                c := c + 1
        # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
        with begin():
            out << a * 10000 + b * 100 + c
        out
    "#},
    61403
)]
fn test_multi_variable_transactions(#[case] code: &str, #[case] expected: i64) {
    check_tile(code, commit_stream(&[0], &[expected]));
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

/// Drive a program whose result is a single trailing-commit read and return the
/// committed `Value` at position 0. A compound (tuple/record) register reads back
/// boxed (`Scalar(Record)`) or struct-of-arrays depending on the read path; both
/// fold to the same `Value` through `scalar_tile_to_column_value`, so this asserts
/// on the *value* rather than the (path-dependent) tile shape.
fn trailing_commit_value(code: &str) -> Value {
    use cambra::interpreter::tile_operators::scalar_tile_to_column_value;
    let Tile::SealedFunction {
        domain, codomain, ..
    } = run_pipeline(code)
    else {
        panic!("expected a commit stream");
    };
    assert_eq!(domain.len(), 1, "expected exactly one trailing commit");
    scalar_tile_to_column_value(*codomain).index_at(0)
}

// ---------------------------------------------------------------------------
// Compound (tuple / record) transactional registers
//
// A `Mut({Int, Int}, Txn)` / `Mut({x: Int}, Txn)` register holds one compound
// `Value`; the commit-store path already threads it (it shares the induction
// path's `read_initial_scalar` seeding and boxes/unboxes at the value-Case
// decision merge). Enabling it needed only the tuple/record *type annotation*
// forms in `lower_type_annotation`.
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// Unconditional tuple register: (100,0) −10/+10 → (90,10) −20/+20 → (70,30).
#[case(indoc! {r#"
    out = defer()
    p: Mut({Int, Int}, Txn) := (100, 0)
    for r in [10, 20]:
        with begin():
            p := (p[0] - r, p[1] + r)
    with begin():
        out << p
    out
"#}, make_tuple(&[Value::Int(70), Value::Int(30)]))]
// Conditional tuple write with a deny: r=60 commits (100≥60 → (40,60)); r=60 again
// denies (40≥60 false) → stays (40,60).
#[case(indoc! {r#"
    out = defer()
    p: Mut({Int, Int}, Txn) := (100, 0)
    for r in [60, 60]:
        with begin():
            if p[0] >= r:
                p := (p[0] - r, p[1] + r)
    with begin():
        out << p
    out
"#}, make_tuple(&[Value::Int(40), Value::Int(60)]))]
// if/else both arms write a tuple: r=3 → r>2 arm → (3, 30).
#[case(indoc! {r#"
    out = defer()
    p: Mut({Int, Int}, Txn) := (0, 0)
    for r in [1, 2, 3]:
        with begin():
            if r > 2:
                p := (r, r * 10)
            else:
                p := (r, r)
    with begin():
        out << p
    out
"#}, make_tuple(&[Value::Int(3), Value::Int(30)]))]
// Named record register.
#[case(r"
out = defer()
p: Mut({x: Int, y: Int}, Txn) := (x=100, y=0)
for r in [10, 20]:
    with begin():
        p := (x=p.x - r, y=p.y + r)
with begin():
    out << p
out", make_record(&[("x", Value::Int(70)), ("y", Value::Int(30))]))]
// Mixed multi-key store: a scalar key `s` and a tuple key `p`, atomic per commit.
// s = 10+20 = 30; p = (70, 30); trailing read `(s, p)`.
#[case(indoc! {r#"
    out = defer()
    s: Mut(Int, Txn) := 0
    p: Mut({Int, Int}, Txn) := (100, 0)
    for r in [10, 20]:
        with begin():
            s := s + r
            p := (p[0] - r, p[1] + r)
    with begin():
        out << (s, p)
    out
"#}, make_tuple(&[Value::Int(30), make_tuple(&[Value::Int(70), Value::Int(30)])]))]
fn test_compound_txn_register(#[case] code: &str, #[case] expected: Value) {
    assert_eq!(trailing_commit_value(code), expected);
}

/// A field projected off a tuple transactional register in the trailing read.
#[test]
fn test_compound_txn_register_field() {
    assert_eq!(
        trailing_commit_value(indoc! {r#"
                out = defer()
                p: Mut({Int, Int}, Txn) := (100, 0)
                for r in [10, 20]:
                    with begin():
                        p := (p[0] - r, p[1] + r)
                with begin():
                    out << p[0]
                out
            "#}),
        Value::Int(70),
    );
}

/// `out << pool` *inside* the block reports each transaction's committed
/// (read-your-writes) value: `pool - r` after the write — 90, 70, 40 over commit
/// ticks 1, 2, 3. The feed rides the writer decision as a `to_out` tap,
/// committed atomically with the register write and read back as a per-commit
/// value-stream (commit-tick-indexed). Contrast a *trailing* standalone read-only
/// transaction `with begin(): out << pool` (an as-of read latched to the singleton
/// trigger at that read's own commit position — one value at position 0, the
/// drained 40 under the batch scheduler) — a different construct.
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
// Value types: a transactional register holds any base value, not just int
// ---------------------------------------------------------------------------

/// A single-element scalar stream over `domain` — the shape of a trailing
/// read-only transaction's reply for a non-int register.
fn scalar_stream(domain: &[usize], codomain: ColumnValue) -> Tile {
    Tile::SealedFunction {
        domain: ColumnValue::UInts(domain.to_vec()),
        codomain: Box::new(Tile::Scalar(codomain)),
        domain_predicate: Predicate::True,
        deleted: BitSet::new(),
    }
}

/// A `bool`-valued transactional register: both writers set `flag = True`; the
/// trailing read observes the committed `True`.
#[test]
fn bool_valued_store() {
    check_tile(
        indoc! {r#"
            out = defer()
            flag: Mut(Bool, Txn) := False
            for x in [1, 2]:
                with begin():
                    flag := True
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << flag
            out
        "#},
        scalar_stream(&[0], ColumnValue::Bools(BitVec::from_elem(1, true))),
    );
}

/// A `str`-valued transactional register: the last commit sets `name = "bob"`.
#[test]
fn string_valued_store() {
    check_tile(
        indoc! {r#"
            out = defer()
            name: Mut(String, Txn) := "init"
            for x in [1, 2]:
                with begin():
                    name := "bob"
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << name
            out
        "#},
        scalar_stream(&[0], ColumnValue::Strings(vec![SmolStr::new("bob")])),
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

/// **Both arms feed** in a *committing* block: each arm writes the register `a`
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
/// reply that reads a register (`if r > 1: resp << pool`). The block commits no
/// register, so the reply is a filtered live read: `channelize` fans the guard-
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
/// Like every trailing read in this file (see the `TODO(await_final)` inline),
/// that the read sees *either* settled value rather than the seed is the
/// single-threaded scheduler's doing, not a guarantee about relative order.
#[test]
fn grant_deny_two_writers_single_commit() {
    let tile = run_pipeline(indoc! {r#"
            out = defer()
            pool: Mut(Int, Txn) := 100
            for r in [70]:
                with begin():
                    if pool >= r:
                        pool := pool - r
            for r in [50]:
                with begin():
                    if pool >= r:
                        pool := pool - r
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << pool
            out
        "#});
    let Tile::SealedFunction { codomain, .. } = &tile else {
        panic!("expected a reply stream, got {tile:?}");
    };
    let Tile::Scalar(ColumnValue::Ints(vals)) = codomain.as_ref() else {
        panic!("expected Ints codomain, got {codomain:?}");
    };
    assert_eq!(vals.len(), 1, "one trailing read");
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
        out = defer()
        pool: Mut(Int, Txn) := 1000
        for r in {ones}:
            with begin():
                pool := pool - r
        for r in {ones}:
            with begin():
                pool := pool - r
        with begin():
            out << pool
        out
    "};
    check_tile(&code, commit_stream(&[0], &[980]));
}

// ---------------------------------------------------------------------------
// Read rules and rejected shapes
// ---------------------------------------------------------------------------

/// A transactional register may be read only inside a `with begin():` block; a
/// bare read outside one is rejected with a hint to wrap it in a block.
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

/// A *computed* live cross-endpoint read (`resp << last + 1`) compiles: the
/// pre-lambda-elim live-read rewrite turns it into `as_of(…) ≫ (λ x → x + 1)`,
/// whose reply lambda the elim pass point-frees. Running the rewrite before
/// lambda-elim is what keeps the reply a liftable lambda rather than a
/// point-free `const`.
#[test]
fn computed_live_cross_endpoint_read_compiles() {
    let code = indoc! {r#"
        set_reqs, set_resps = http_serve("0", "POST", "/s")
        get_reqs, get_resps = http_serve("0", "GET", "/g")
        last: Mut(Int, Txn) := 0
        for msg in set_reqs:
            with begin():
                last := last + 1
            set_resps << "ok"
        for req in get_reqs:
            with begin():
                get_resps << last + 1

    "#};
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    compile_program(&mut ctx, code, consumer)
        .expect("a computed live cross-endpoint read should compile to an as-of join");
}

/// A live cross-endpoint read that combines the *request element* with a register
/// read (`resp << a + req`) compiles: the live-read rewrite turns it into
/// `zip((trigger, as_of(store))) ≫ (λ (req, snap) → e)`, pairing each request with
/// its register snapshot. The end-to-end value is checked in
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
        "a live reply combining the request with a register read should compile to a zip read",
    );
}

/// End-to-end live check of the request-plus-register reply (3b): a batch loop
/// commits the register to 60, then a **live** source drives replies
/// `resps << store + req`. Each reply pairs the request with the store's as-of
/// snapshot (60, after the batch commits), so requests 5 and 15 yield 65 and 75 —
/// the `zip((trigger, as_of)) ≫ (λ (req, s) → req + s)` shape driven incrementally.
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
/// x=2 → a += 2; x=3 → a += 3. Final a = 5, b = 1 — read via the register carry
/// (`get_prev_txn`), each iteration one commit.
#[test]
fn tx_if_else_routes_across_keys() {
    check_tile(
        indoc! {r#"
            a: Mut(Int, Txn) := 0
            b: Mut(Int, Txn) := 0
            out = defer()
            for x in [1, 2, 3]:
                with begin():
                    if x >= 2:
                        a := a + x
                    else:
                        b := b + x
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << a + b
            out
        "#},
        commit_stream(&[0], &[6]),
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
            out = defer()
            for x in [1, 2, 3]:
                with begin():
                    if x >= 2:
                        a := 5
                    else:
                        b := 6
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << a + b
            out
        "#},
        commit_stream(&[0], &[11]),
    );
}

/// An `elif` chain (no `else`) inside a transaction: first-match per position,
/// the trailing implicit arm the deny (a position matching no guard does not
/// commit). `a := 0`, over `[3, 2, 1]`: x=3 → `if` → a += 3; x=2 → `elif` →
/// a += 1; x=1 → neither → deny. Final a = 4. (The loop leads with a committing
/// position so the trailing as-of read observes the drained store — a leading
/// *deny* delays the first commit past that read's position-0 sample.)
#[test]
fn tx_if_elif_first_match() {
    check_tile(
        indoc! {r#"
            a: Mut(Int, Txn) := 0
            out = defer()
            for x in [3, 2, 1]:
                with begin():
                    if x >= 3:
                        a := a + x
                    elif x >= 2:
                        a := a + 1
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << a
            out
        "#},
        commit_stream(&[0], &[4]),
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
            out = defer()
            for r in [5]:
                with begin():
                    if a >= 0:
                        a := a + r
                    if r > 100:
                        b := b + r
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << a
            out
        "#},
        commit_stream(&[0], &[5]),
    );
}

/// `Txn` is never inferred: a transactional register must be spelled
/// `Mut(V, Txn)`. A fully-inferred bare `:=` mutable variable is an *induction* accumulator, so
/// writing it inside a `with begin():` block is rejected — the block did not
/// silently promote it to a `Txn` register.
#[test]
fn txn_domain_never_inferred() {
    check_compile_error(
        indoc! {r#"
            x := 0
            with begin():
                x := x + 1
            x
        "#},
        "`x` is written inside a `with begin():` block that commits no transactional register",
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
        "`cnt` is written inside a `with begin():` block that commits no transactional register",
    );
}

/// A *guarded* induction write in a **mixed** block — one that *does* commit a
/// transactional register — is rejected. `check_no_induction_only_transactions`
/// passes (the block commits `reg`), but the guarded `cnt += 1` is not liftable
/// by `partition_spine` and would be silently dropped from the decision record.
/// A dedicated pre-check (`check_no_guarded_induction_write_in_block`) catches it.
#[test]
fn guarded_induction_write_in_mixed_block_rejected() {
    check_compile_error(
        indoc! {r#"
            reg: Mut(Int, Txn) := 0
            cnt: Mut(Int) := 0
            for x in [1, 2, 3]:
                with begin():
                    reg := reg + x
                    if x >= 2:
                        cnt := cnt + 1
            cnt
        "#},
        "guarded induction write in a transaction block is not supported",
    );
}

/// C3: a write to a transactional register *outside* any `with begin():` block
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

/// C3, by-reference flavor: a `Mut(_, Txn)` writer body that assigns its register
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
/// `Mut(_, Txn)` register declared *inside* a `def` body must not leak into the
/// transactional registry and falsely gate a like-spelled top-level local. The
/// def-body scope snapshots and restores *both* register registries, so `reg`
/// outside `f` is an ordinary local (assignable, readable).
#[test]
fn txn_register_in_def_body_does_not_leak_to_outer_local() {
    check_scalar(
        indoc! {r#"
            def f(x):
                reg: Mut(Int, Txn) := 0
                x
            reg = 5
            reg
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

/// C5: the out-of-block read gate applies to a bare register passed as an
/// argument to an *ordinary* function (only a `Mut`-parameter callee accepts a
/// bare register pass and bypasses the gate). `f(store)` reads the register
/// outside a block, so it is rejected.
#[test]
fn bare_register_arg_to_ordinary_fn_is_gated() {
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
// Register identity is the `Mut(_, Txn)` type on the α-unique binding, not the
// surface base name — so a local variable merely *spelled* like a register is
// not confused for it (A1: a compiler panic; A2: a spurious rejection).
// ---------------------------------------------------------------------------

/// A1 regression (no panic): a comprehension whose loop variable is *spelled*
/// like the register (`[store for store in [1, 2, 3]]`) must not be swept into
/// the transaction footprint — the comprehension var is a distinct α-unique
/// binder. Before the fix, base-name footprint collection matched it, then
/// panicked looking for its (non-existent) register `let`. The register write is
/// `store = store - sum([1, 2, 3])` = 100 − 6 = 94, read back by the trailing
/// read-only transaction (a live as-of read at position 0).
#[test]
fn like_named_comprehension_var_does_not_panic() {
    check_tile(
        indoc! {r#"
            out = defer()
            store: Mut(Int, Txn) := 100
            for r in [10]:
                with begin():
                    store := store - sum([store for store in [1, 2, 3]])
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << store
            out
        "#},
        commit_stream(&[0], &[94]),
    );
}

/// A2 regression (no false rejection): a loop target *spelled* like a register
/// (`for store in [1, 2, 3]`) is a genuine local, not an out-of-block store
/// read. Before the fix, the base-name read gate rejected `store` inside the
/// loop even though no transaction is present. The loop feeds `store + 1` per
/// iteration → `[2, 3, 4]` at loop positions `[0, 1, 2]`; the register itself is
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
/// register `store`, written in the block) AND a sibling induction accumulator
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

/// Stage-1 interop, register side: the register accumulates transactionally across
/// the same mixed loop (0 + 10 + 20 + 30 = 60), read back by a trailing
/// read-only transaction, while the sibling induction `cnt` advances
/// independently and does not join the atomic commit.
#[test]
fn mixed_txn_and_induction_store_accumulates() {
    check_tile(
        indoc! {r#"
            out = defer()
            store: Mut(Int, Txn) := 0
            cnt: Mut(Int) := 0
            for r in [10, 20, 30]:
                with begin():
                    store := store + r
                cnt := cnt + 1
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << store
            out
        "#},
        commit_stream(&[0], &[60]),
    );
}

/// Stage-2 interop: the induction write sits *physically inside* the `with
/// begin():` block (`store := store + r; cnt := cnt + 1`), the literal
/// worked-example form. `transact_phase` partitions the block by register domain —
/// the register write forms the commit decision; the induction `cnt` write is
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

/// Stage-2 interop, register side: with the induction write inside the block, the
/// register still accumulates transactionally (0 + 10 + 20 + 30 = 60) and the
/// lifted induction `cnt` stays out of the atomic commit.
#[test]
fn mixed_txn_and_induction_write_inside_block_store_accumulates() {
    check_tile(
        indoc! {r#"
            out = defer()
            store: Mut(Int, Txn) := 0
            cnt: Mut(Int) := 0
            for r in [10, 20, 30]:
                with begin():
                    store := store + r
                    cnt := cnt + 1
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << store
            out
        "#},
        commit_stream(&[0], &[60]),
    );
}

/// Stage-3 cross-domain read: a commit decision reads an induction accumulator at
/// its request position (`store := store + cnt` inside the block). The accumulator
/// is threaded through the writer source (a `zip` of the loop iter and `cnt`'s
/// per-position view) and the commit engine co-iterates it — so `cnt` = 1,2,3 and
/// the register accumulates 0 + 1 + 2 + 3 = 6. `cnt` sequences on the request loop
/// (its own domain), independent of the commit clock.
#[test]
fn commit_decision_reads_induction_accumulator() {
    check_tile(
        indoc! {r#"
            out = defer()
            store: Mut(Int, Txn) := 0
            cnt: Mut(Int) := 0
            for r in [10, 20, 30]:
                cnt := cnt + 1
                with begin():
                    store := store + cnt
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << store
            out
        "#},
        commit_stream(&[0], &[6]),
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
/// `ExtractLast` is empty until its loop's `Recurse` drains, so the writer
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
/// `TestDataSource`'s three elements — a loop whose `Recurse` converges only as
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
/// domain (request-indexed → `[1,2,3]`) while the register accumulates to 6.
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
/// at commit ticks 1,2,3. The register accumulates alongside; this is the worked
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
/// self-re-arm (no reader-side drive-to-fixpoint), so **every request is served**
/// (no freeze — one reply per request) and a request delivered after the writer
/// completes observes the **post-deny** commit (`total = 30`), which the old
/// producer-side `drive_store_to_fixpoint` stopped short of (a deny stalls the
/// frontier, so the drive returned the pre-deny `total = 10` and a request latching
/// then froze there). Observations are asserted **non-decreasing** (a monotone
/// accumulator sampled at arrival) and members of the committed set — never a
/// specific "final" value.
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

    // Two requests (req = 100 at position 0, req = 200 at position 1); drive the
    // cyclic store — with its interior deny — to completion.
    src.borrow_mut().add_data(&[
        (Value::UInt(0), Value::Int(100)),
        (Value::UInt(1), Value::Int(200)),
    ]);
    src.borrow_mut().set_yield_predicate(Predicate::True);
    ctx.scheduler().check_for_notifications();
    let mut result = producer.get(ug.clone());
    for _ in 0..64 {
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
    // The later request observes the post-deny commit — the store stepped past the
    // interior deny (which the old drive-to-fixpoint stalled on).
    assert_eq!(
        observed_total[1], 30,
        "the post-writer request observes the drained total 30 (past the r=0 deny)"
    );
}

/// Cross-function transactional writer: `def transfer(src, dst, amt)` writes two
/// `Mut(_, Txn)` registers inside one `with begin():` block. Inlining
/// beta-reduces the call so the writes name the caller's `a`/`b` bindings, which
/// `collect_txn_registers` finds on the inlined, typed tree (the whole point of
/// keying register identity by the `Mut(_, Txn)` type, not a base name). After
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
            out = defer()
            a: Mut(Int, Txn) := 100
            b: Mut(Int, Txn) := 0
            transfer(a, b, 30)
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << a + b
            out
        "#},
        commit_stream(&[0], &[100]),
    );
}

// A heterogeneous multi-key register: a `Mut(String, Txn)` and a
// `Mut(Int, Txn)` committed together in one block. Regression for the
// register-wide value extent (`build_commit_store`), which is the union of the
// distinct per-key extents rather than whichever key was iterated last —
// reading either key returns its own type. `label` is declared first, so a
// last-key-wins extent would be `int`, yet the string read must still yield a
// string.
#[test]
fn heterogeneous_multi_key_store_reads_string_key() {
    check_tile(
        indoc! {r#"
            out = defer()
            label: Mut(String, Txn) := "init"
            count: Mut(Int, Txn) := 0
            for x in [1, 2, 3]:
                with begin():
                    count := count + x
                    label := "seen"
            # TODO(await_final): arbitrary as-of read — sees the drained store only by single-threaded timing.
            with begin():
                out << label
            out
        "#},
        Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![0]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Strings(vec![SmolStr::new(
                "seen",
            )]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        },
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
/// reads the protected register (`d != 0`) suppresses the fault. An item-only
/// guard (`if r != 0`) that does *not* read the divisor offers no protection and
/// correctly still faults — that is sound semantics (a guard that doesn't guard
/// the dangerous term), not a limitation; item-only guards otherwise commit and
/// deny normally.
#[test]
fn txn_off_path_guarded_division_does_not_fault() {
    check_tile(
        indoc! {r#"
            out = defer()
            d: Mut(Int, Txn) := 3
            acc: Mut(Int, Txn) := 100
            for r in [1, 2]:
                with begin():
                    if d != 0:
                        acc := acc // d
                        d := d - 3
            with begin():
                out << acc
            out
        "#},
        commit_stream(&[0], &[33]),
    );
}

/// **Interleaved two-writer commit/abort through the store.** Two writer
/// sites on the *same* register `pool` interleave committing and aborting
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
            out = defer()
            pool: Mut(Int, Txn) := 100
            for r in [10, 200]:
                with begin():
                    if pool >= r:
                        pool := pool - r
            for r in [20, 300]:
                with begin():
                    if pool >= r:
                        pool := pool - r
            with begin():
                out << pool
            out
        "#},
        commit_stream(&[0], &[70]),
    );
}
