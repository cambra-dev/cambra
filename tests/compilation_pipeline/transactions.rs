//! Transactional stores (`Mut[V, Txn]` + `with begin():`) — the commit-operator
//! path. Batch (finite-loop and standalone) single-variable transactions run
//! end-to-end: `x: Mut[V, Txn]` folds into one shared commit store, each `with
//! begin():` block is a writer. A transactional register is read only inside a
//! `with begin():` block; the batch tests read the final value with a trailing
//! standalone read-only transaction (`out = defer(); …; with begin(): out << x`)
//! and assert the fed stream — a live as-of read latched to the singleton trigger
//! after the writes commit, so `out` is a one-element stream `[final]` at
//! position 0. Translated from the prototype's transaction suite (its `txn x = e`
//! introducer is the `x: Mut[V, Txn] := e` annotation here).

use std::time::Duration;

use bit_set::BitSet;
use bit_vec::BitVec;
use cambra::ccl::context::{GlobalContext, compile_program, render_errors};
use cambra::interpreter::{ColumnValue, Consumer, Predicate, Tile};
use rstest_log::rstest;
use smol_str::SmolStr;

use crate::helpers::*;

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

// The final committed value is read by a trailing standalone read-only
// transaction (`with begin(): out << pool`) and fed to `out` — a live as-of read
// latched to the singleton trigger once the writes commit, so `out` is the
// one-element stream `[final]` at position 0.
#[rstest]
#[timeout(Duration::from_secs(10))]
// Single writer draws down a pool: 100 − 10 − 20 − 30 = 40.
#[case::counter(
    "out = defer()\npool: Mut[int, Txn] := 100\nfor r in [10, 20, 30]:\n    with begin():\n        pool := pool - r\nwith begin():\n    out << pool\nout",
    40
)]
// Two writers over one store: the operator serializes + retries, conserving the
// total: 100 − 30 − 40 = 30.
#[case::two_writers(
    "out = defer()\npool: Mut[int, Txn] := 100\nfor r in [30]:\n    with begin():\n        pool := pool - r\nfor r in [40]:\n    with begin():\n        pool := pool - r\nwith begin():\n    out << pool\nout",
    30
)]
// Conditional grant/deny: 70 commits (pool → 30); 50 tried against 30, `30 >= 50`
// is false → denies (no negative pool). Final 30.
#[case::grant_deny(
    "out = defer()\npool: Mut[int, Txn] := 100\nfor r in [70]:\n    with begin():\n        if pool >= r:\n            pool := pool - r\nfor r in [50]:\n    with begin():\n        if pool >= r:\n            pool := pool - r\nwith begin():\n    out << pool\nout",
    30
)]
// Multi-statement body: a leading `let fee`, a guard, then the write. A: 100 − 33
// = 67; B: 67 ≥ 44 → 67 − 44 = 23.
#[case::multi_stmt(
    "out = defer()\npool: Mut[int, Txn] := 100\nfor r in [30]:\n    with begin():\n        fee = r // 10\n        if pool >= r + fee:\n            pool := pool - r - fee\nfor r in [40]:\n    with begin():\n        fee = r // 10\n        if pool >= r + fee:\n            pool := pool - r - fee\nwith begin():\n    out << pool\nout",
    23
)]
// Computed (non-literal) init `sum([40,30,30]) = 100`, read from an acyclic init
// operator at tick 0; one writer draws 60 → 40.
#[case::computed_init(
    "out = defer()\npool: Mut[int, Txn] := sum([40, 30, 30])\nfor r in [60]:\n    with begin():\n        pool := pool - r\nwith begin():\n    out << pool\nout",
    40
)]
// Writer source bound *after* the store declaration (`reqs` between `pool` and
// the loop). The store letrec is spliced below every source binding, so the
// writer's `Var(reqs)` is in scope — previously this crashed with an internal
// unrecognised-variable error. 100 − 10 − 20 − 30 = 40.
#[case::source_bound_after_store(
    "out = defer()\npool: Mut[int, Txn] := 100\nreqs = [10, 20, 30]\nfor r in reqs:\n    with begin():\n        pool := pool - r\nwith begin():\n    out << pool\nout",
    40
)]
// A single standalone transaction (no enclosing `for`): one commit over a
// synthesized singleton source: 100 − 10 = 90.
#[case::standalone_single(
    "out = defer()\npool: Mut[int, Txn] := 100\nwith begin():\n    pool := pool - 10\nwith begin():\n    out << pool\nout",
    90
)]
// Two standalone transactions in sequence: two commits on one clock → 70.
#[case::standalone_sequential(
    "out = defer()\npool: Mut[int, Txn] := 100\nwith begin():\n    pool := pool - 10\nwith begin():\n    pool := pool - 20\nwith begin():\n    out << pool\nout",
    70
)]
// A standalone transaction composes with loop-based ones on the shared store:
// 100 − 1 − 10 − 20 = 69.
#[case::standalone_then_loop(
    "out = defer()\npool: Mut[int, Txn] := 100\nwith begin():\n    pool := pool - 1\nfor r in [10, 20]:\n    with begin():\n        pool := pool - r\nwith begin():\n    out << pool\nout",
    69
)]
// Two writers, each drawing several amounts, over one store. The operator
// serializes + retries across all four commits; subtraction conserves the
// total regardless of interleaving: 100 − 10 − 20 − 5 − 15 = 50.
#[case::multi_writer_contention(
    "out = defer()\npool: Mut[int, Txn] := 100\nfor r in [10, 20]:\n    with begin():\n        pool := pool - r\nfor r in [5, 15]:\n    with begin():\n        pool := pool - r\nwith begin():\n    out << pool\nout",
    50
)]
// Three writers on one store compose the same as one: 100 − 10 − 20 − 30 = 40.
#[case::three_writers(
    "out = defer()\npool: Mut[int, Txn] := 100\nfor r in [10]:\n    with begin():\n        pool := pool - r\nfor r in [20]:\n    with begin():\n        pool := pool - r\nfor r in [30]:\n    with begin():\n        pool := pool - r\nwith begin():\n    out << pool\nout",
    40
)]
// Two writers contend for a pool too small for both draws: whichever the
// operator serializes first commits (pool → 40); the other re-reads 40, fails
// `40 >= 60`, and denies. Order-independent final: 40.
#[case::multi_writer_grant_deny(
    "out = defer()\npool: Mut[int, Txn] := 100\nfor r in [60]:\n    with begin():\n        if pool >= r:\n            pool := pool - r\nfor r in [60]:\n    with begin():\n        if pool >= r:\n            pool := pool - r\nwith begin():\n    out << pool\nout",
    40
)]
fn test_transactional_stores(#[case] code: &str, #[case] expected: i64) {
    check_tile(code, commit_stream(&[0], &[expected]));
}

// ---------------------------------------------------------------------------
// Multiple variables in one transaction + read-your-writes (multi-key store)
// ---------------------------------------------------------------------------

#[rstest]
#[timeout(Duration::from_secs(10))]
// A single trailing read-only transaction reads *both* keys under one snapshot
// (`out << a * 100 + b`) — one consistent view of the finished store.
// `a` and `b` update atomically each iteration: a := sum([1,2,3]) = 6, b := sum of
// squares = 14 → a*100 + b := 614.
#[case::multi_var(
    "out = defer()\na: Mut[int, Txn] := 0\nb: Mut[int, Txn] := 0\nfor x in [1, 2, 3]:\n    with begin():\n        a := a + x\n        b := b + x * x\nwith begin():\n    out << a * 100 + b\nout",
    614
)]
// Cross-variable read: `b = b + a` reads `a`'s snapshot before `a = a + x`, so a
// runs 5,6,8 → b := 19, a ends 11 → 1119.
#[case::multi_var_cross_read(
    "out = defer()\na: Mut[int, Txn] := 5\nb: Mut[int, Txn] := 0\nfor x in [1, 2, 3]:\n    with begin():\n        b := b + a\n        a := a + x\nwith begin():\n    out << a * 100 + b\nout",
    1119
)]
// Read-your-writes across keys: `b = a` after `a = a + x` sees the new `a`. a:
// 0→1→3→6, b: 1,3,6 → final a=6, b=6 → 606.
#[case::read_your_writes_cross_key(
    "out = defer()\na: Mut[int, Txn] := 0\nb: Mut[int, Txn] := 0\nfor x in [1, 2, 3]:\n    with begin():\n        a := a + x\n        b := a\nwith begin():\n    out << a * 100 + b\nout",
    606
)]
// Same key written twice: the second `a = a + 1` reads the first write's value.
// x=10: 0→10→11; x=20: 11→31→32 → 32.
#[case::read_your_writes_same_key(
    "out = defer()\na: Mut[int, Txn] := 0\nfor x in [10, 20]:\n    with begin():\n        a := a + x\n        a := a + 1\nwith begin():\n    out << a\nout",
    32
)]
// Read-only store key: `limit` is read in the guard but written nowhere. x=10
// commits (10 ≤ 25); 20/30 denied → total := 10.
#[case::multi_var_readonly_key(
    "out = defer()\nlimit: Mut[int, Txn] := 25\ntotal: Mut[int, Txn] := 0\nfor x in [10, 20, 30]:\n    with begin():\n        if total + x <= limit:\n            total := total + x\nwith begin():\n    out << total\nout",
    10
)]
// Two writers touching *disjoint* keys — no footprint overlap, so neither ever
// invalidates the other. `a` = 1+2 = 3, `b` = 10+20 = 30 → 3*100 + 30 = 330.
#[case::multi_writer_disjoint_keys(
    "out = defer()\na: Mut[int, Txn] := 0\nb: Mut[int, Txn] := 0\nfor x in [1, 2]:\n    with begin():\n        a := a + x\nfor y in [10, 20]:\n    with begin():\n        b := b + y\nwith begin():\n    out << a * 100 + b\nout",
    330
)]
// Two writers with *overlapping* footprints: writer 1 writes {a, b}, writer 2
// writes {b, c}. The shared `b` forces serialization, but the sums are
// order-independent: a := 3, b := 1+2+10+20 = 33, c := 30 → 3*10000 + 33*100 + 30
// = 33330.
#[case::multi_writer_overlapping_keys(
    "out = defer()\na: Mut[int, Txn] := 0\nb: Mut[int, Txn] := 0\nc: Mut[int, Txn] := 0\nfor x in [1, 2]:\n    with begin():\n        a := a + x\n        b := b + x\nfor y in [10, 20]:\n    with begin():\n        b := b + y\n        c := c + y\nwith begin():\n    out << a * 10000 + b * 100 + c\nout",
    33330
)]
// Three keys updated atomically per transaction, all read together under one
// snapshot: a := sum = 6, b := sum of squares = 14, c := count = 3 → 6*10000 +
// 14*100 + 3 = 61403.
#[case::read_three_vars_one_snapshot(
    "out = defer()\na: Mut[int, Txn] := 0\nb: Mut[int, Txn] := 0\nc: Mut[int, Txn] := 0\nfor x in [1, 2, 3]:\n    with begin():\n        a := a + x\n        b := b + x * x\n        c := c + 1\nwith begin():\n    out << a * 10000 + b * 100 + c\nout",
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

/// `out << pool` *inside* the block reports each transaction's committed
/// (read-your-writes) value: `pool - r` after the write — 90, 70, 40 over commit
/// ticks 1, 2, 3. The feed rides the writer decision as a `to_out` tap,
/// committed atomically with the register write and read back as a per-commit
/// value-stream (commit-tick-indexed). Contrast a *trailing* standalone read-only
/// transaction `with begin(): out << pool` (a live as-of read latched to the
/// singleton trigger — the final value 40 at position 0) — a different construct.
#[test]
fn progress_feed_inside_tx() {
    check_tile(
        "out = defer()\npool: Mut[int, Txn] := 100\nfor r in [10, 20, 30]:\n    with begin():\n        pool := pool - r\n        out << pool\nout",
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
        "out = defer()\npool: Mut[int, Txn] := 100\nfor r in [70, 50]:\n    with begin():\n        if pool >= r:\n            pool := pool - r\n            out << pool\nout",
        commit_stream(&[1], &[30]),
    );
}

// ---------------------------------------------------------------------------
// Value types: a transactional store holds any base value, not just int
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
        "out = defer()\nflag: Mut[bool, Txn] := False\nfor x in [1, 2]:\n    with begin():\n        flag := True\nwith begin():\n    out << flag\nout",
        scalar_stream(&[0], ColumnValue::Bools(BitVec::from_elem(1, true))),
    );
}

/// A `str`-valued transactional register: the last commit sets `name = "bob"`.
#[test]
fn string_valued_store() {
    check_tile(
        "out = defer()\nname: Mut[str, Txn] := \"init\"\nfor x in [1, 2]:\n    with begin():\n        name := \"bob\"\nwith begin():\n    out << name\nout",
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
        "outa = defer()\noutb = defer()\na: Mut[int, Txn] := 0\nb: Mut[int, Txn] := 0\nfor x in [1, 2, 3]:\n    with begin():\n        a := a + x\n        b := b + x * x\n        outa << a\n        outb << b\n(outa, outb)",
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

// ---------------------------------------------------------------------------
// Multiple writers feeding one defer
// ---------------------------------------------------------------------------

/// A reply stream fed by several writers: each writer contributes one
/// commit-tick entry as its own union variant — the design's `++` union across
/// sites. Each variant is the singleton `[tick] -> [value]` the writer committed
/// (a reply tap is a per-commit event, so a writer contributes *only* its own
/// commit tick — no carry-forward across the other writers' ticks).
fn multi_writer_reply(ticks_and_values: &[(usize, i64)]) -> Tile {
    Tile::SealedFunction {
        domain: ColumnValue::Union {
            tags: (0..ticks_and_values.len()).collect(),
            variants: ticks_and_values
                .iter()
                .map(|(t, _)| ColumnValue::UInts(vec![*t]))
                .collect(),
        },
        codomain: Box::new(Tile::Scalar(ColumnValue::Ints(
            ticks_and_values.iter().map(|(_, v)| *v).collect(),
        ))),
        domain_predicate: Predicate::Union(vec![Predicate::True; ticks_and_values.len()]),
        deleted: BitSet::new(),
    }
}

/// Two writers both feed `out` (the reply of each transaction's committed
/// value). They serialize on the shared pool — commit 1 draws 10 (→90), commit 2
/// draws 20 (→70) — and each writer's reply appears at *its own* commit tick:
/// `{1 -> 90, 2 -> 70}`, unioned across the two sites. (Regression: this used to
/// smear writer 1's 90 forward onto writer 2's tick via carry-forward.)
#[test]
fn multi_writer_single_defer_feed() {
    check_tile(
        "out = defer()\npool: Mut[int, Txn] := 100\nfor r in [10]:\n    with begin():\n        pool := pool - r\n        out << pool\nfor r in [20]:\n    with begin():\n        pool := pool - r\n        out << pool\nout",
        multi_writer_reply(&[(1, 90), (2, 70)]),
    );
}

/// Three writers feeding one defer: one reply per commit at its own tick —
/// `{1 -> 90, 2 -> 70, 3 -> 40}`, unioned across the three sites.
#[test]
fn three_writers_single_defer_feed() {
    check_tile(
        "out = defer()\npool: Mut[int, Txn] := 100\nfor r in [10]:\n    with begin():\n        pool := pool - r\n        out << pool\nfor r in [20]:\n    with begin():\n        pool := pool - r\n        out << pool\nfor r in [30]:\n    with begin():\n        pool := pool - r\n        out << pool\nout",
        multi_writer_reply(&[(1, 90), (2, 70), (3, 40)]),
    );
}

// ---------------------------------------------------------------------------
// Read rules and rejected shapes
// ---------------------------------------------------------------------------

/// A transactional register may be read only inside a `with begin():` block; a
/// bare read outside one is rejected with a hint to wrap it in a block.
#[test]
fn bare_txn_read_outside_tx_rejected() {
    check_compile_error(
        "pool: Mut[int, Txn] := 100\nwith begin():\n    pool := pool - 10\npool",
        "read transactional variable `pool` inside a `with begin():` block",
    );
}

/// A *computed* live cross-endpoint read (`resp << last + 1`) compiles: the
/// pre-lambda-elim live-read rewrite turns it into `as_of(…) ≫ (λ x → x + 1)`,
/// whose reply lambda the elim pass point-frees. (When the rewrite ran *after*
/// lambda-elim it faced a point-free `const` it could not lift, so a computed
/// live read was rejected outright — the old `check_live_reads_resolved`
/// band-aid.)
#[test]
fn computed_live_cross_endpoint_read_compiles() {
    let code = "set_reqs, set_resps = http_serve(\"0\", \"POST\", \"/s\")\n\
                get_reqs, get_resps = http_serve(\"0\", \"GET\", \"/g\")\n\
                last: Mut[int, Txn] := 0\n\
                for msg in set_reqs:\n    with begin():\n        last := last + 1\n    set_resps << \"ok\"\n\
                for req in get_reqs:\n    with begin():\n        get_resps << last + 1\n";
    let mut ctx = GlobalContext::default();
    let consumer: Box<dyn Consumer> = Box::new(|| {});
    compile_program(&mut ctx, code, consumer)
        .expect("a computed live cross-endpoint read should compile to an as-of join");
}

/// A live cross-endpoint read that combines the *request element* with a store
/// read (`resp << store + req`) is rejected with a clear error rather than
/// compiled to a silent hang. The response is a function of both the request loop
/// and the store, which needs a `zip(trigger, as_of)` shape (not yet
/// implemented); the rewrite leaves it, so one register would stay a
/// never-terminating terminal read. (A store-only read — single register,
/// computed, or a multi-register snapshot — is supported.)
#[test]
fn live_read_combining_request_and_store_rejected() {
    check_compile_error(
        "set_reqs, set_resps = http_serve(\"0\", \"POST\", \"/set\")\n\
         get_reqs, get_resps = http_serve(\"0\", \"GET\", \"/get\")\n\
         a: Mut[str, Txn] := \"a0\"\n\
         for msg in set_reqs:\n    with begin():\n        a := msg\n    set_resps << \"ok\\n\"\n\
         for req in get_reqs:\n    with begin():\n        get_resps << a + req\n",
        "combines the request with a transactional register",
    );
}

/// The retired `with tx():` marker is rejected; the marker is `begin()`.
#[test]
fn old_tx_marker_rejected() {
    check_compile_error(
        "pool: Mut[int, Txn] := 100\nwith tx():\n    pool := pool - 10",
        "begin()",
    );
}

/// Nested transactions are rejected.
#[test]
fn nested_transactions_rejected() {
    check_compile_error(
        "pool: Mut[int, Txn] := 100\nwith begin():\n    with begin():\n        pool := pool - 1",
        "nested",
    );
}

/// An `else` branch inside a `with begin():` block is rejected with a clear
/// diagnostic (not a compiler panic): the guard model supports only a bare `if
/// cond:` deny guard. `else`-with-writes would need conditional per-key write
/// values with unconditional commit — a distinct, unsettled semantics.
#[test]
fn tx_if_else_with_writes_rejected() {
    check_compile_error(
        "a: Mut[int, Txn] := 0\nb: Mut[int, Txn] := 0\nfor x in [1, 2, 3]:\n    with begin():\n        if x >= 2:\n            a := a + x\n        else:\n            b := b + x",
        "`else` branch inside a `with begin():` block is not supported",
    );
}

/// Likewise an `elif` chain inside a transaction is rejected gracefully.
#[test]
fn tx_if_elif_rejected() {
    check_compile_error(
        "a: Mut[int, Txn] := 0\nfor x in [1, 2, 3]:\n    with begin():\n        if x >= 3:\n            a := a + x\n        elif x >= 2:\n            a := a + 1",
        "`elif` inside a `with begin():` block is not supported",
    );
}

/// C2: an induction accumulator (`Mut[…]`, non-`Txn`) written inside a `with
/// begin():` block is rejected at lowering — `transact_phase` folds only
/// transactional writes, so an induction write would be silently swallowed
/// (a block-local shadow that dies at block end, computing `[0, 0, …]`).
#[test]
fn induction_write_inside_begin_block_rejected() {
    check_compile_error(
        "cnt: Mut[int] := 0\nwith begin():\n    cnt := cnt + 1\ncnt",
        "induction store `cnt`",
    );
}

/// C3: a write to a transactional register *outside* any `with begin():` block
/// is rejected (write-side mirror of the read gate). Otherwise it becomes a plain
/// sequential `let` shadow that silently hides every committed value.
#[test]
fn out_of_block_txn_write_rejected() {
    check_compile_error(
        "store: Mut[int, Txn] := 100\nstore := 50\n0",
        "write transactional variable `store`",
    );
}

/// C3, by-reference flavor: a `Mut[_, Txn]` writer body that assigns its register
/// *without* a `with begin():` block is rejected at lowering of the body.
#[test]
fn by_ref_txn_write_without_block_rejected() {
    check_compile_error(
        "store: Mut[int, Txn] := 0\ndef w(p: Mut[int, Txn]):\n    p := 50\nw(store)\n0",
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
        "out = defer()\npool: Mut[int, Txn] := 100\ndef do_it(p: Mut[int, Txn]):\n    with begin():\n        p := p - 10\nwith begin():\n    pool := pool - 5\n    y = do_it(pool)\nwith begin():\n    out << pool\nout",
        "nested",
    );
}

/// PR-2 registry leak (same class as PR-1's mutable-registry leak): a
/// `Mut[_, Txn]` register declared *inside* a `def` body must not leak into the
/// transactional registry and falsely gate a like-spelled top-level local. The
/// def-body scope snapshots and restores *both* store registries, so `reg`
/// outside `f` is an ordinary local (assignable, readable).
#[test]
fn txn_register_in_def_body_does_not_leak_to_outer_local() {
    check_scalar(
        "def f(x):\n    reg: Mut[int, Txn] := 0\n    x\nreg = 5\nreg",
        cambra::interpreter::Value::Int(5),
    );
}

/// The `with t = begin():` transaction handle is rejected at lowering (not yet
/// implemented): binding it and referencing the commit time inside the block
/// would otherwise silently resolve to an outer `t` or fail opaquely.
#[test]
fn transaction_handle_binding_rejected() {
    check_compile_error(
        "pool: Mut[int, Txn] := 100\nfor r in [10]:\n    with t = begin():\n        pool := pool - r",
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
        "store: Mut[int, Txn] := 0\ndef f(x):\n    x + 1\nf(store)",
        "read transactional variable `store`",
    );
}

// ---------------------------------------------------------------------------
// Store identity is the `Mut[_, Txn]` type on the α-unique binding, not the
// surface base name — so a local variable merely *spelled* like a register is
// not confused for it (A1: a compiler panic; A2: a spurious rejection).
// ---------------------------------------------------------------------------

/// A1 regression (no panic): a comprehension whose loop variable is *spelled*
/// like the register (`[store for store in [1, 2, 3]]`) must not be swept into
/// the transaction footprint — the comprehension var is a distinct α-unique
/// binder. Before the fix, base-name footprint collection matched it, then
/// panicked looking for its (non-existent) store `let`. The register write is
/// `store = store - sum([1, 2, 3])` = 100 − 6 = 94, read back by the trailing
/// read-only transaction (a live as-of read at position 0).
#[test]
fn like_named_comprehension_var_does_not_panic() {
    check_tile(
        "out = defer()\nstore: Mut[int, Txn] := 100\nfor r in [10]:\n    with begin():\n        store := store - sum([store for store in [1, 2, 3]])\nwith begin():\n    out << store\nout",
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
        "out = defer()\nstore: Mut[int, Txn] := 0\nfor store in [1, 2, 3]:\n    out << store + 1\nout",
        make_int_list(&[2, 3, 4]),
    );
}

/// Cross-function transactional writer: `def transfer(src, dst, amt)` writes two
/// `Mut[_, Txn]` registers inside one `with begin():` block. Inlining
/// beta-reduces the call so the writes name the caller's `a`/`b` bindings, which
/// `collect_txn_stores` finds on the inlined, typed tree (the whole point of
/// keying store identity by the `Mut[_, Txn]` type, not a base name). After
/// `transfer(a, b, 30)`: `a` = 100 − 30 = 70, `b` = 0 + 30 = 30 — the trailing
/// read-only transaction reads `a + b` = 100, the conserved total.
#[test]
fn cross_function_transfer_conserves_total() {
    check_tile(
        "def transfer(src: Mut[int, Txn], dst: Mut[int, Txn], amt):\n    with begin():\n        src := src - amt\n        dst := dst + amt\nout = defer()\na: Mut[int, Txn] := 100\nb: Mut[int, Txn] := 0\ntransfer(a, b, 30)\nwith begin():\n    out << a + b\nout",
        commit_stream(&[0], &[100]),
    );
}
