//! A loop body's bindings must not be copied into their reads.
//!
//! `mut_elim` rewrites a mutation loop, and `transact_phase` a `with begin():`
//! block, into a writer body over a snapshot parameter. A binding the body
//! introduces is kept as a binding and read where it stands, except that an inner
//! loop's writer takes a copy of the bindings it reads (`src/ccl/mut_elim.rs`'s
//! `sink_prefix`). Inlining its value into each read instead costs a factor of
//! two per binding on the chain `aₖ = aₖ₋₁ + aₖ₋₁`, whose every binding reads the
//! one before it twice.
//!
//! Tree size is the probe rather than wall-clock: it is deterministic, so the
//! guard is a hard bound instead of a timing threshold. The claim is the growth
//! and not an absolute size — doubling the chain's length may at most double the
//! tree — so the bound survives any change to what a writer body costs per node.

use cambra::ccl::context::{Phase, compile_to};
use cambra::ccl::{Expr, TypedExprNode};

/// `a0 … a{depth}`, each reading its predecessor twice, placed between `before`
/// and `after`, which reads `a{depth}` at `{last}`.
fn loop_with_chain(depth: usize, indent: &str, before: &str, after: &str) -> String {
    loop_with_chain_of(
        "a0 = i + 1",
        "a{k} = a{p} + a{p}",
        depth,
        indent,
        before,
        after,
    )
}

/// [`loop_with_chain`] with `first` binding `a0` and `step` binding `a{k}` from
/// `a{p}`, its predecessor.
fn loop_with_chain_of(
    first: &str,
    step: &str,
    depth: usize,
    indent: &str,
    before: &str,
    after: &str,
) -> String {
    let mut chain = format!("{indent}{first}\n");
    for k in 1..=depth {
        let line = step
            .replace("{k}", &k.to_string())
            .replace("{p}", &(k - 1).to_string());
        chain.push_str(&format!("{indent}{line}\n"));
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
    let loaded = cambra::ccl::load::LoadedProgram::test(code);
    size(&compile_to(&loaded, Phase::Letrec).expect("the program compiles"))
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
            "out: Feed(_)\nx := 0\nfor i in [1, 2, 3]:\n",
            "out << {last}\n  x += {last}\nout\n",
        )
    });
}

#[test]
fn a_chain_read_inside_a_comprehension_stays_linear() {
    // The comprehension reads the bindings where they stand, under its map.
    assert_linear_in_chain_length("comprehension", |d| {
        loop_with_chain(
            d,
            "  ",
            "x := 0\nfor i in [1, 2, 3]:\n",
            "x += sum([z + {last} for z in [1, 2, 3]])\nx\n",
        )
    });
}

#[test]
fn a_chain_seeding_an_inner_loop_stays_linear() {
    // The inner loop's seed reads the written value's binding where it stands.
    assert_linear_in_chain_length("inner loop's seed", |d| {
        loop_with_chain(
            d,
            "  ",
            "x := 0\nfor i in [1, 2, 3]:\n",
            "x := {last}\n  for j in [1, 2]:\n    x += j\nx\n",
        )
    });
}

#[test]
fn a_chain_of_sums_stays_linear() {
    // Each sum reads the one before it twice, inside its comprehension.
    assert_linear_in_chain_length("sums", |d| {
        loop_with_chain_of(
            "a0 = sum([z + i for z in [1, 2]])",
            "a{k} = sum([z + a{p} + a{p} for z in [1, 2]])",
            d,
            "  ",
            "x := 0\nfor i in [1, 2, 3]:\n",
            "x += {last}\nx\n",
        )
    });
}

#[test]
fn a_chain_of_writing_if_values_stays_linear() {
    // Each `if` writes in one branch and yields a value reading the last one twice: the
    // walk merges the value as it does a variable, rather than copying what follows the
    // `if` into each branch.
    assert_linear_in_chain_length("writing `if` values", |d| {
        loop_with_chain_of(
            "a0 = i + 1",
            "a{k} = if i > 1:\n          acc += 1\n          a{p} + a{p}\n      else:\n          a{p}",
            d,
            "  ",
            "acc := 0\nfor i in [1, 2, 3]:\n",
            "acc += {last}\nacc\n",
        )
    });
}

#[test]
fn a_chain_of_writing_if_values_in_a_writing_block_stays_linear() {
    assert_linear_in_chain_length("writing `if` values in a `with begin():` block", |d| {
        loop_with_chain_of(
            "a0 = i + 1",
            "a{k} = if i > 1:\n              acc := acc + 1\n              a{p} + a{p}\n          else:\n              a{p}",
            d,
            "      ",
            "acc: Mut(Int, Txn) := 0\nfor i in [1, 2, 3]:\n    with begin():\n",
            "acc := acc + {last}\nawait_final(acc)\n",
        )
    });
}

#[test]
fn a_chain_of_declarations_stays_linear() {
    // Each `:=` declares a variable of the body, seeded from the one before it.
    assert_linear_in_chain_length("declarations", |d| {
        loop_with_chain_of(
            "a0 := i + 1",
            "a{k} := a{p} + a{p}",
            d,
            "  ",
            "x := 0\nfor i in [1, 2, 3]:\n",
            "x += {last}\nx\n",
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
            "pool: Mut(Int, Txn) := 100\nout: Feed(_)\nfor i in [1, 2, 3]:\n    with begin():\n",
            "out << {last} + pool\nout\n",
        )
    });
}

#[test]
fn a_chain_in_a_writing_block_stays_linear() {
    assert_linear_in_chain_length("writing `with begin():` block", |d| {
        loop_with_chain(
            d,
            "        ",
            "pool: Mut(Int, Txn) := 100\nfor i in [1, 2, 3]:\n    with begin():\n",
            "pool := pool + {last}\nawait_final(pool)\n",
        )
    });
}

#[test]
fn a_chain_read_under_a_guard_in_a_writing_block_stays_linear() {
    // The guard reaches the commit gate, the guarded write a value-`Case` arm, and
    // the feed a tap: three regions, each given the bindings it reads.
    assert_linear_in_chain_length("guarded writing `with begin():` block", |d| {
        loop_with_chain(
            d,
            "        ",
            "pool: Mut(Int, Txn) := 100\nout: Feed(_)\nfor i in [1, 2, 3]:\n    with begin():\n",
            "if {last} > 10:\n            pool := pool + {last}\n            out << {last}\nout\n",
        )
    });
}

#[test]
fn a_chain_inside_a_guard_in_a_writing_block_stays_linear() {
    // The arm's bindings stay apart from the block's and travel with each value
    // leaving the arm.
    assert_linear_in_chain_length("chain in a guarded writing `with begin():` arm", |d| {
        loop_with_chain(
            d,
            "            ",
            "pool: Mut(Int, Txn) := 100\nfor i in [1, 2, 3]:\n    with begin():\n        if i > 1:\n",
            "pool := pool + {last}\nawait_final(pool)\n",
        )
    });
}

/// `{write}` repeated `depth` times in a writing `with begin():` block over `pool`.
fn block_with_writes(depth: usize, write: &str) -> String {
    format!(
        "pool: Mut(Int, Txn) := 1\nfor i in [1, 2, 3]:\n    with begin():\n{}await_final(pool)\n",
        write.repeat(depth)
    )
}

#[test]
fn writes_each_reading_the_last_twice_stay_linear() {
    assert_linear_in_chain_length("writes in a `with begin():` block", |d| {
        block_with_writes(d, "        pool := pool + pool\n")
    });
}

#[test]
fn guarded_writes_each_reading_the_last_twice_stay_linear() {
    // Each `if` rejoins `pool`, and the next one reads the rejoined value twice.
    assert_linear_in_chain_length("guarded writes in a `with begin():` block", |d| {
        block_with_writes(d, "        if i > 1:\n            pool := pool + pool\n")
    });
}

/// `{write}` repeated `depth` times in the body of a loop over `x`.
fn loop_with_writes(depth: usize, write: &str) -> String {
    format!("x := 1\nfor i in [1, 2, 3]:\n{}x\n", write.repeat(depth))
}

#[test]
fn loop_writes_each_reading_the_last_twice_stay_linear() {
    assert_linear_in_chain_length("writes in a loop body", |d| {
        loop_with_writes(d, "  x := x + x\n")
    });
}

#[test]
fn loop_guarded_writes_each_reading_the_last_twice_stay_linear() {
    // Each `if` merges `x`, and the next one reads the merged value in both of its
    // arms.
    assert_linear_in_chain_length("guarded writes in a loop body", |d| {
        loop_with_writes(d, "  if i > 1:\n    x := x + x\n")
    });
}

/// Recurrences in the tree `mut_elim` emits.
fn recurrences(code: &str) -> usize {
    fn count(e: &Expr) -> usize {
        let mut n = usize::from(matches!(e.node, TypedExprNode::LetRec { .. }));
        e.walk_children(|c| n += count(c));
        n
    }
    let loaded = cambra::ccl::load::LoadedProgram::test(code);
    count(&compile_to(&loaded, Phase::Letrec).expect("the program compiles"))
}

#[test]
fn an_inner_loop_in_a_branch_is_one_recurrence_whatever_it_writes() {
    // The branch's values leave it in one merged tuple, so the inner loop they all read
    // is bound once rather than once per variable.
    let code = indoc::indoc! {"
        x := 0
        y := 0
        z := 0
        for i in [1, 2, 3]:
            if i > 1:
                for j in [1, 2]:
                    x += j
                    y += j
                    z += j
        x
    "};
    assert_eq!(
        recurrences(code),
        2,
        "the outer loop's and the inner loop's"
    );
}

#[test]
fn an_inner_loop_in_a_branch_is_one_recurrence_when_it_also_feeds() {
    // The feed leaves the branch in the merged tuple beside the variable, so both read the
    // one inner loop.
    let code = indoc::indoc! {"
        s := 0
        ys: Feed(_)
        for i in [1, 2]:
            if i > 1:
                for j in [1, 2]:
                    s += j
                    ys << j * 10
        sum(ys) + s
    "};
    assert_eq!(
        recurrences(code),
        2,
        "the outer loop's and the inner loop's"
    );
}

/// How many times the literal `marker` stands in the tree `mut_elim` emits.
fn copies_of(marker: i64, code: &str) -> usize {
    fn count(marker: i64, e: &Expr) -> usize {
        let mut n = usize::from(matches!(
            e.node,
            TypedExprNode::Lit(cambra::ccl::Lit::Int(v)) if v == marker
        ));
        e.walk_children(|c| n += count(marker, c));
        n
    }
    let loaded = cambra::ccl::load::LoadedProgram::test(code);
    count(
        marker,
        &compile_to(&loaded, Phase::Letrec).expect("the program compiles"),
    )
}

/// A branch writes `t` and feeds what it wrote, so the merge of `t` and the feed read one
/// binding of the written value. A copy each would evaluate it twice, which two readings of
/// the clock or of a random source tell apart.
#[rstest::rstest]
#[case::in_a_loop(indoc::indoc! {"
    t := 0
    ys: Feed(_)
    zs: Feed(_)
    for x in [1, 2]:
        if t == 0:
            t := x * 7919
            ys << t
        zs << t
    sum(ys) + sum(zs)
"})]
#[case::in_a_writing_block(indoc::indoc! {"
    t: Mut(Int, Txn) := 0
    ys: Feed(_)
    zs: Feed(_)
    for x in [1, 2]:
        with begin():
            if t == 0:
                t := x * 7919
                ys << t
            zs << t
    sum(ys) + sum(zs)
"})]
#[case::in_a_match_arm(indoc::indoc! {"
    t := 0
    ys: Feed(_)
    zs: Feed(_)
    for x in [1, 2]:
        match `some(x):
            case `some(y):
                t := y * 7919
                ys << t
            case `none(_):
                t += 1
        zs << t
    sum(ys) + sum(zs)
"})]
fn a_value_a_branch_writes_and_feeds_is_bound_once(#[case] code: &str) {
    assert_eq!(copies_of(7919, code), 1, "program:\n{code}");
}
