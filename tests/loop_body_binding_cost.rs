//! A loop body's bindings must not be copied into their reads.
//!
//! `mut_elim` rewrites a mutation loop into a writer body over a snapshot
//! parameter. A binding the body introduces is kept as a binding wherever it is
//! read at the writer's own domain, and sunk into the domain-restricted regions
//! that read it otherwise (`src/ccl/mut_elim.rs`'s `sink_prefix`). Inlining it
//! into each read instead costs a factor of two per binding on the chain
//! `aₖ = aₖ₋₁ + aₖ₋₁`, whose every binding reads the one before it twice.
//!
//! Tree size is the probe rather than wall-clock: it is deterministic, so the
//! guard is a hard bound instead of a timing threshold. The claim is the growth
//! and not an absolute size — doubling the chain's length may at most double the
//! tree — so the bound survives any change to what a writer body costs per node.

use cambra::ccl::Expr;
use cambra::ccl::context::{Phase, compile_to};

/// `a0 … a{depth}`, each reading its predecessor twice, placed in `body` where
/// it writes `{chain}` and reads `a{depth}` at `{last}`.
fn loop_with_chain(depth: usize, indent: &str, before: &str, after: &str) -> String {
    let mut chain = format!("{indent}a0 = i + 1\n");
    for k in 1..=depth {
        chain.push_str(&format!("{indent}a{k} = a{p} + a{p}\n", p = k - 1));
    }
    format!(
        "{before}{chain}{indent}{after}",
        after = after.replace("{last}", &format!("a{depth}"))
    )
}

/// Nodes in the tree `mut_elim` emits.
fn writer_size(code: &str) -> usize {
    fn size(e: &Expr) -> usize {
        let mut n = 1;
        e.walk_children(|c| n += size(c));
        n
    }
    size(&compile_to(code, Phase::Letrec).expect("the program compiles"))
}

/// The chain lengths the bound compares. A regression is exponential in the
/// difference, so 5 to 10 separates a linear writer from an inlined one by a
/// factor of 32 while keeping the failing run small enough to report.
const SHORT: usize = 5;
const LONG: usize = 10;

#[track_caller]
fn assert_linear_in_chain_length(shape: &str, build: impl Fn(usize) -> String) {
    let short = writer_size(&build(SHORT));
    let long = writer_size(&build(LONG));
    assert!(
        long <= 2 * short,
        "{shape}: a chain of {LONG} bindings emits {long} nodes against {short} for one of \
         {SHORT} — the loop body's bindings are being copied into their reads"
    );
}

#[test]
fn a_chain_on_the_loop_spine_stays_linear() {
    assert_linear_in_chain_length("spine", |d| {
        loop_with_chain(d, "  ", "x := 0\nfor i in [1, 2, 3]:\n", "x += {last}\nx\n")
    });
}

#[test]
fn a_chain_read_under_a_guard_stays_linear() {
    // The write is a value-`Case` arm, which compiles to a domain restrict: the
    // bindings travel into the arm rather than being inlined into it.
    assert_linear_in_chain_length("guarded write", |d| {
        loop_with_chain(
            d,
            "  ",
            "x := 0\nfor i in [1, 2, 3]:\n",
            "if i > 1:\n    x += {last}\n  x += 1\nx\n",
        )
    });
}

#[test]
fn a_chain_inside_a_guard_stays_linear() {
    assert_linear_in_chain_length("guarded chain", |d| {
        loop_with_chain(
            d,
            "    ",
            "x := 0\nfor i in [1, 2, 3]:\n  if i > 1:\n",
            "x += {last}\nx\n",
        )
    });
}

#[test]
fn a_chain_read_by_a_feed_stays_linear() {
    assert_linear_in_chain_length("feed", |d| {
        loop_with_chain(
            d,
            "  ",
            "out = defer()\nx := 0\nfor i in [1, 2, 3]:\n",
            "out << {last}\n  x += {last}\nout\n",
        )
    });
}

#[test]
fn a_chain_in_a_read_only_block_stays_linear() {
    // The accumulator-free path: each feed leaves the chain for a map of its own
    // (`transform_feed_only_loop`), taking its bindings with it.
    assert_linear_in_chain_length("read-only `with begin():` block", |d| {
        loop_with_chain(
            d,
            "        ",
            "pool: Mut(Int, Txn) := 100\nout = defer()\nfor i in [1, 2, 3]:\n    with begin():\n",
            "out << {last} + pool\nout\n",
        )
    });
}
