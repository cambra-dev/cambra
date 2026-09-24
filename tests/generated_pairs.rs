//! Generated pairs: every type-compatible (skeleton, filler) program, run through both
//! oracles.
//!
//! Each compiler defect `tests/differential_interp.rs` pins is one feature inside
//! another — a collection under a feed, a collection in a record field, a
//! comprehension inside a loop, an aggregate over a keyed-written store. So the unit here
//! is a **position** and what fills it, rather than a random term: a skeleton is a whole
//! program with one hole, a filler is an expression that can sit in it, and the corpus is
//! every pair whose types agree.
//!
//! Enumerated rather than sampled, which buys determinism: no seed, no flaky reproduction,
//! and coverage that can be stated rather than estimated.
//!
//! Two oracles run per program:
//!
//! - a panic, assertion or wall failure is a bug by construction, whatever the program;
//! - a disagreement between compiler and interpreter is a wrong answer.
//!
//! Outcomes are classified by mechanism: any `CompileError` is a rejection, whether its
//! message states a gap or reports a compiler bug, and a sink the compiled program could not
//! read counts as a panic. An interpreter refusal is a gap in the oracle, not in the
//! compiler.
//!
//! Every outcome other than agreement is pinned in [`LEDGER`], by cell and cause, so a new
//! failure, a changed cause and a newly passing cell all fail `enumerate_pairs`.
//! `PAIRS_BLESS=1` rewrites the ledger from the run.

#[path = "support/differential.rs"]
mod differential;

use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use differential::{Compiled, run_compiled, run_interpreted};
use indoc::indoc;

/// Every cell whose outcome is not agreement, one per line: `cell<TAB>kind<TAB>cause key`.
const LEDGER: &str = include_str!("generated_pairs.ledger");

/// The types a hole can want and a filler can produce.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Ty {
    Int,
    Bool,
    Str,
    /// A collection of integers.
    IntColl,
    /// A record with fields `a` and `b`, both integers.
    Rec,
    /// A collection of those records.
    RecColl,
    /// A collection of strings.
    StrColl,
    /// A tagged value, `some` or `none`.
    Variant,
    /// A record with a collection field `xs` and an integer field `n`.
    RecWithColl,
    /// A transactional mutable variable. Nothing evaluates to one, so it names what a binder
    /// denotes and never what a hole wants or a filler produces; `no_hole_wants_a_store`
    /// holds that.
    TxnStore,
}

struct Skeleton {
    name: &'static str,
    hole: Ty,
    /// The binders in scope at the hole, outermost first: a name and what it holds.
    ///
    /// A filler that reads an enclosing binder is how a correlated shape arises, and a grid
    /// of closed fillers cannot reach one. Two binders is the case where a hole sits under
    /// two nested constructs and names both, which no pair of one-binder skeletons covers:
    /// the outer binder has to survive the inner construct's own abstraction. The skeleton
    /// says what the hole may read; the filler says what it needs.
    scope: &'static [(&'static str, Ty)],
    /// A whole program with `{}` where the filler goes.
    body: &'static str,
}

struct Filler {
    name: &'static str,
    ty: Ty,
    /// The binders this expression reads: `needs[0]` is the `{b}` in `expr`, `needs[1]` the
    /// `{c}`. Each is bound to a distinct skeleton binder holding that type, in every way
    /// the scope allows.
    needs: &'static [Ty],
    /// Declarations the expression needs, placed above the program.
    decls: &'static str,
    expr: &'static str,
}

/// One program's outcome.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Outcome {
    Agrees,
    /// The two sides computed different values.
    Disagrees(String),
    /// The compiler panicked, tripped an assertion, or failed one of its own walls.
    CompilerPanics(String),
    /// The compiler stated a gap.
    CompilerRejects(String),
    /// The interpreter does not cover the program.
    OracleGap(String),
    /// The interpreter itself crashed, which is a defect in the oracle rather than in the
    /// compiler. Named separately so it can never be read as a compiler finding.
    OraclePanics(String),
    /// The compiled program did not complete, so its sink holds a partial value.
    DidNotFinish,
}

impl Outcome {
    /// The outcome without its detail, for tallying.
    fn kind(&self) -> &'static str {
        match self {
            Outcome::Agrees => "Agrees",
            Outcome::Disagrees(_) => "Disagrees",
            Outcome::CompilerPanics(_) => "CompilerPanics",
            Outcome::CompilerRejects(_) => "CompilerRejects",
            Outcome::OracleGap(_) => "OracleGap",
            Outcome::OraclePanics(_) => "OraclePanics",
            Outcome::DidNotFinish => "DidNotFinish",
        }
    }

    fn detail(&self) -> &str {
        match self {
            Outcome::Agrees | Outcome::DidNotFinish => "",
            Outcome::Disagrees(d)
            | Outcome::CompilerPanics(d)
            | Outcome::CompilerRejects(d)
            | Outcome::OracleGap(d)
            | Outcome::OraclePanics(d) => d,
        }
    }
}

// A table, one case per line: the file is read to see what is covered and edited to widen
// it, and rustfmt spreads each case over seven lines.
#[rustfmt::skip]
fn skeletons() -> Vec<Skeleton> {
    vec![
        Skeleton { name: "feed", hole: Ty::Int, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << {}
        "#}},
        Skeleton { name: "feed_in_loop", hole: Ty::Int, scope: &[("i", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            for i in [1, 2]:
                out << {}
        "#}},
        Skeleton { name: "comp_element", hole: Ty::Int, scope: &[("q", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            out << sum([{} for q in [1, 2, 3]])
        "#}},
        Skeleton { name: "comp_element_in_loop", hole: Ty::Int, scope: &[("i", Ty::Int), ("q", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            for i in [1, 2]:
                out << sum([{} for q in [1, 2, 3]])
        "#}},
        Skeleton { name: "comp_source", hole: Ty::IntColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << sum([q * 2 for q in {}])
        "#}},
        Skeleton { name: "comp_filter", hole: Ty::Bool, scope: &[("q", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            out << sum([q for q in [1, 2, 3] if {}])
        "#}},
        Skeleton { name: "loop_source", hole: Ty::IntColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            for q in {}:
                out << q
        "#}},
        Skeleton { name: "record_field", hole: Ty::Int, scope: &[], body: indoc! {r#"
            out = test_sink()
            r = (a={}, b=2)
            out << r.a + r.b
        "#}},
        Skeleton { name: "record_collection_field", hole: Ty::IntColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            r = (xs={}, n=1)
            out << sum(r.xs) + r.n
        "#}},
        Skeleton { name: "record_in_list", hole: Ty::Int, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << sum([r.a for r in [(a={}, b=1)]])
        "#}},
        Skeleton { name: "tuple_component", hole: Ty::Int, scope: &[], body: indoc! {r#"
            out = test_sink()
            t = ({}, 2)
            out << t.0 + t.1
        "#}},
        Skeleton { name: "function_arg", hole: Ty::Int, scope: &[], body: indoc! {r#"
            def fn_under_test(n):
                n + 1

            out = test_sink()
            out << fn_under_test({})
        "#}},
        Skeleton { name: "function_body", hole: Ty::Int, scope: &[("n", Ty::Int)], body: indoc! {r#"
            def fn_under_test(n):
                {}

            out = test_sink()
            out << fn_under_test(3)
        "#}},
        Skeleton { name: "lambda_body", hole: Ty::Int, scope: &[("e", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            out << sum([sum([s for s in g]) for g in groupby([1, 1, 2], \e -> {})])
        "#}},
        Skeleton { name: "aggregate_arg", hole: Ty::IntColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << sum({})
        "#}},
        Skeleton { name: "max_arg", hole: Ty::IntColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << max({})
        "#}},
        Skeleton { name: "binop_operand", hole: Ty::Int, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << ({}) + 1
        "#}},
        Skeleton { name: "match_arm", hole: Ty::Int, scope: &[("v", Ty::Int)], body: indoc! {r#"
            scrut = `some(7)
            picked = match scrut:
                case `some(v):
                    {}
                case `none:
                    0
            out = test_sink()
            out << picked
        "#}},
        Skeleton { name: "ternary_branch", hole: Ty::Int, scope: &[], body: indoc! {r#"
            out = test_sink()
            n = 5
            out << ({} if n > 3 else 0)
        "#}},
        // The store is in scope as well as the iteration: a filler reading it makes an
        // in-context read before the write ("8.3 Reads"), and the reply after the write reads
        // its own write.
        Skeleton { name: "txn_write_rhs", hole: Ty::Int, scope: &[("pool", Ty::Int), ("r", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [1, 2]:
                with begin():
                    pool := {}
                    out << pool
        "#}},
        // A guard reading the store decides on the in-context value the write replaces.
        Skeleton { name: "txn_guard", hole: Ty::Bool, scope: &[("pool", Ty::Int), ("r", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [1, 2]:
                with begin():
                    if {}:
                        pool := pool - r
                        out << pool
        "#}},
        Skeleton { name: "txn_reply", hole: Ty::Int, scope: &[("r", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [1, 2]:
                with begin():
                    pool := pool - r
                    out << {}
        "#}},
        Skeleton { name: "mut_init", hole: Ty::Int, scope: &[], body: indoc! {r#"
            acc := {}
            for i in [1, 2]:
                acc := acc + i
            out = test_sink()
            out << acc
        "#}},
        Skeleton { name: "mut_write_rhs", hole: Ty::Int, scope: &[("i", Ty::Int)], body: indoc! {r#"
            acc := 0
            for i in [1, 2]:
                acc := acc + {}
            out = test_sink()
            out << acc
        "#}},
        Skeleton { name: "keyed_write_value", hole: Ty::Int, scope: &[("k", Ty::Str)], body: indoc! {r#"
            m: Mut(Map(String, Int)) := box(map([("a", 1)]))
            for k in ["b"]:
                m[k] := {}
            out = test_sink()
            out << sum(m)
        "#}},
        Skeleton { name: "generator_yield", hole: Ty::Int, scope: &[("x", Ty::Int)], body: indoc! {r#"
            def gen_under_test(xs):
                for x in xs:
                    yield {}

            out = test_sink()
            out << max(gen_under_test([1, 2, 3]))
        "#}},
        Skeleton { name: "defer_feed", hole: Ty::Int, scope: &[("i", Ty::Int)], body: indoc! {r#"
            ch = defer()
            for i in [1, 2]:
                ch << {}
            out = test_sink()
            out << sum(ch)
        "#}},
        Skeleton { name: "two_feed_sites", hole: Ty::Int, scope: &[("i", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            for i in [1, 2]:
                out << {}
            for j in [10, 20]:
                out << j
        "#}},
        // Feeds a collection rather than folding it first. Its disagreement is the ledger's
        // check on the comparison: a run with no disagreements at all would not say whether
        // the comparison discriminates.
        Skeleton { name: "feed_collection", hole: Ty::IntColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << {}
        "#}},
        Skeleton { name: "record_coll_source", hole: Ty::RecColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << sum([r.a for r in {}])
        "#}},
        Skeleton { name: "groupby_source", hole: Ty::RecColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << sum([sum([r.a for r in g]) for g in groupby({}, \e -> e.b)])
        "#}},
        Skeleton { name: "record_feed", hole: Ty::Rec, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << {}
        "#}},
        Skeleton { name: "record_projected", hole: Ty::Rec, scope: &[], body: indoc! {r#"
            out = test_sink()
            r = {}
            out << r.a + r.b
        "#}},
        Skeleton { name: "mut_reads_itself", hole: Ty::Int, scope: &[("acc", Ty::Int)], body: indoc! {r#"
            acc := 1
            for i in [1, 2]:
                acc := {}
            out = test_sink()
            out << acc
        "#}},
        // A record binder: iterating records is the shape a rollup is written in.
        Skeleton { name: "rec_comp_element", hole: Ty::Int, scope: &[("r", Ty::Rec)], body: indoc! {r#"
            out = test_sink()
            out << sum([{} for r in [(a=1, b=2), (a=3, b=4)]])
        "#}},
        Skeleton { name: "rec_loop_feed", hole: Ty::Int, scope: &[("r", Ty::Rec)], body: indoc! {r#"
            out = test_sink()
            for r in [(a=1, b=2), (a=3, b=4)]:
                out << {}
        "#}},
        Skeleton { name: "rec_comp_filter", hole: Ty::Bool, scope: &[("r", Ty::Rec)], body: indoc! {r#"
            out = test_sink()
            out << sum([r.a for r in [(a=1, b=2), (a=3, b=4)] if {}])
        "#}},
        // Strings as a collection element, and as a group key.
        Skeleton { name: "str_loop_feed", hole: Ty::Str, scope: &[("sv", Ty::Str)], body: indoc! {r#"
            out = test_sink()
            for sv in ["a", "b"]:
                out << {}
        "#}},
        Skeleton { name: "str_coll_source", hole: Ty::StrColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            for sv in {}:
                out << sv
        "#}},
        // Variants: a tagged value fed, and one dispatched on.
        Skeleton { name: "variant_feed", hole: Ty::Variant, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << {}
        "#}},
        Skeleton { name: "match_scrutinee", hole: Ty::Variant, scope: &[], body: indoc! {r#"
            scrut = {}
            picked = match scrut:
                case `some(v):
                    v + 1
                case `none:
                    0
            out = test_sink()
            out << picked
        "#}},
        Skeleton { name: "string_feed", hole: Ty::Str, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << {}
        "#}},
        Skeleton { name: "bool_feed", hole: Ty::Bool, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << {}
        "#}},

        // Two binders at one hole: a filler that names both constructs it sits under.
        Skeleton { name: "comp_in_comp", hole: Ty::Int, scope: &[("w", Ty::Int), ("z", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            out << sum([sum([{} for z in [1, 2]]) for w in [3, 4]])
        "#}},
        Skeleton { name: "comp_filter_in_loop", hole: Ty::Bool, scope: &[("i", Ty::Int), ("z", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            for i in [1, 2]:
                out << sum([z for z in [1, 2, 3] if {}])
        "#}},
        Skeleton { name: "rec_comp_in_loop", hole: Ty::Int, scope: &[("r", Ty::Rec), ("z", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            for r in [(a=1, b=2), (a=3, b=4)]:
                out << sum([{} for z in [1, 2]])
        "#}},
        Skeleton { name: "rec_comp_filter_in_loop", hole: Ty::Bool, scope: &[("r", Ty::Rec), ("z", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            for r in [(a=1, b=2), (a=3, b=4)]:
                out << sum([z for z in [1, 2] if {}])
        "#}},
        Skeleton { name: "match_arm_in_loop", hole: Ty::Int, scope: &[("i", Ty::Int), ("v", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            for i in [1, 2]:
                scrut = `some(7)
                picked = match scrut:
                    case `some(v):
                        {}
                    case `none:
                        0
                out << picked
        "#}},
        Skeleton { name: "lambda_body_in_loop", hole: Ty::Int, scope: &[("i", Ty::Int), ("e", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            for i in [1, 2]:
                out << sum([sum([s for s in g]) for g in groupby([1, 1, 2], \e -> {})])
        "#}},

        // Terminal reads. Every other transactional skeleton reads the store in context, inside
        // the block that writes it; `await_final` waits for the whole commit history.
        Skeleton { name: "terminal_read", hole: Ty::Int, scope: &[("pool", Ty::TxnStore)], body: indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [1, 2]:
                with begin():
                    pool := pool - r
            out << {}
        "#}},
        Skeleton { name: "terminal_read_after_guard", hole: Ty::Int, scope: &[("pool", Ty::TxnStore)], body: indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [1, 2]:
                with begin():
                    if r > 1:
                        pool := pool - r
            out << {}
        "#}},
        Skeleton { name: "terminal_read_guard", hole: Ty::Bool, scope: &[("pool", Ty::TxnStore)], body: indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [1, 2]:
                with begin():
                    pool := pool - r
            out << (1 if {} else 0)
        "#}},

        // A record holding a collection, arriving as a value: `record_collection_field` fixes
        // the record and varies the collection, and these vary the whole record.
        Skeleton { name: "rec_with_coll_feed", hole: Ty::RecWithColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            out << {}
        "#}},
        Skeleton { name: "rec_with_coll_projected", hole: Ty::RecWithColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            r = {}
            out << sum(r.xs) + r.n
        "#}},
        Skeleton { name: "rec_with_coll_scalar_field", hole: Ty::RecWithColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            r = {}
            out << r.n
        "#}},
        Skeleton { name: "rec_with_coll_in_loop", hole: Ty::RecWithColl, scope: &[("i", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            for i in [1, 2]:
                r = {}
                out << sum(r.xs)
        "#}},
    ]
}

#[rustfmt::skip]
fn fillers() -> Vec<Filler> {
    vec![
        // --- closed integers
        Filler { name: "int_lit", ty: Ty::Int, needs: &[], decls: "", expr: "7" },
        Filler { name: "arith", ty: Ty::Int, needs: &[], decls: "", expr: "2 + 3 * 4" },
        Filler { name: "neg", ty: Ty::Int, needs: &[], decls: "", expr: "-5" },
        Filler { name: "floordiv", ty: Ty::Int, needs: &[], decls: "", expr: "9 // 2" },
        Filler { name: "sum_lit", ty: Ty::Int, needs: &[], decls: "", expr: "sum([1, 2, 3])" },
        Filler { name: "max_lit", ty: Ty::Int, needs: &[], decls: "", expr: "max([1, 2, 3])" },
        Filler { name: "comp_sum", ty: Ty::Int, needs: &[], decls: "", expr: "sum([z * 2 for z in [1, 2, 3]])" },
        Filler { name: "filtered_sum", ty: Ty::Int, needs: &[], decls: "", expr: "sum([z for z in [1, 2, 3, 4] if z > 2])" },
        Filler { name: "union_sum", ty: Ty::Int, needs: &[], decls: "", expr: "sum([1, 2] ++ [3, 4])" },
        Filler { name: "nested_comp_sum", ty: Ty::Int, needs: &[], decls: "", expr: "sum([sum([z for z in [1, 2]]) for w in [1, 2]])" },
        Filler { name: "groupby_sum", ty: Ty::Int, needs: &[], decls: "", expr: "sum([sum([s for s in g]) for g in groupby([1, 1, 2], \\e2 -> e2)])" },
        Filler { name: "tuple_proj", ty: Ty::Int, needs: &[], decls: "", expr: "(3, 4).0" },
        Filler { name: "record_proj", ty: Ty::Int, needs: &[], decls: "", expr: "(p=3, q=4).p" },
        Filler { name: "ternary", ty: Ty::Int, needs: &[], decls: "", expr: "(1 if 2 > 1 else 0)" },
        // A sum of nothing, which is its identity, 0.
        Filler { name: "sum_of_empty", ty: Ty::Int, needs: &[], decls: "", expr: "sum([z for z in [1, 2] if z > 99])" },
        Filler { name: "call", ty: Ty::Int, needs: &[], decls: indoc! {r#"
            def helper_fn(hn):
                hn * 2
        "#}, expr: "helper_fn(4)" },
        Filler { name: "generator_max", ty: Ty::Int, needs: &[], decls: indoc! {r#"
            def helper_gen(hxs):
                for hx in hxs:
                    yield hx * 3
        "#}, expr: "max(helper_gen([1, 2]))" },

        // --- integers reading the binder in scope
        Filler { name: "binder", ty: Ty::Int, needs: &[Ty::Int], decls: "", expr: "{b}" },
        Filler { name: "binder_arith", ty: Ty::Int, needs: &[Ty::Int], decls: "", expr: "{b} * 2 + 1" },
        Filler { name: "binder_in_comp", ty: Ty::Int, needs: &[Ty::Int], decls: "", expr: "sum([z2 * {b} for z2 in [1, 2]])" },
        Filler { name: "binder_in_comp_filter", ty: Ty::Int, needs: &[Ty::Int], decls: "", expr: "sum([z2 for z2 in [1, 2, 3] if z2 > {b}])" },
        Filler { name: "binder_in_call", ty: Ty::Int, needs: &[Ty::Int], decls: indoc! {r#"
            def helper_fn2(hn):
                hn * 2
        "#}, expr: "helper_fn2({b})" },
        Filler { name: "binder_ternary", ty: Ty::Int, needs: &[Ty::Int], decls: "", expr: "({b} if {b} > 1 else 0)" },

        // --- booleans
        Filler { name: "bool_lit", ty: Ty::Bool, needs: &[], decls: "", expr: "True" },
        Filler { name: "cmp", ty: Ty::Bool, needs: &[], decls: "", expr: "2 > 1" },
        Filler { name: "cmp_on_sum", ty: Ty::Bool, needs: &[], decls: "", expr: "sum([1, 2]) > 2" },
        Filler { name: "boolop", ty: Ty::Bool, needs: &[], decls: "", expr: "2 > 1 and 3 > 2" },
        Filler { name: "not", ty: Ty::Bool, needs: &[], decls: "", expr: "not 1 > 2" },
        Filler { name: "binder_cmp", ty: Ty::Bool, needs: &[Ty::Int], decls: "", expr: "{b} > 1" },
        Filler { name: "binder_cmp_on_comp", ty: Ty::Bool, needs: &[Ty::Int], decls: "", expr: "sum([z2 for z2 in [1, 2]]) > {b}" },
        Filler { name: "str_binder_cmp", ty: Ty::Bool, needs: &[Ty::Str], decls: "", expr: "{b} == \"b\"" },

        // --- strings
        Filler { name: "str_lit", ty: Ty::Str, needs: &[], decls: "", expr: "\"hi\"" },
        Filler { name: "str_concat", ty: Ty::Str, needs: &[], decls: "", expr: "\"a\" + \"b\"" },
        Filler { name: "str_binder", ty: Ty::Str, needs: &[Ty::Str], decls: "", expr: "{b}" },

        // --- integer collections, including the empty and duplicated edges
        Filler { name: "list_lit", ty: Ty::IntColl, needs: &[], decls: "", expr: "[1, 2, 3]" },
        Filler { name: "singleton", ty: Ty::IntColl, needs: &[], decls: "", expr: "[7]" },
        Filler { name: "all_filtered", ty: Ty::IntColl, needs: &[], decls: "", expr: "[z for z in [1, 2, 3] if z > 99]" },
        Filler { name: "comp", ty: Ty::IntColl, needs: &[], decls: "", expr: "[z * 2 for z in [1, 2, 3]]" },
        Filler { name: "filtered_comp", ty: Ty::IntColl, needs: &[], decls: "", expr: "[z for z in [1, 2, 3, 4] if z > 2]" },
        Filler { name: "union", ty: Ty::IntColl, needs: &[], decls: "", expr: "[1, 2] ++ [3, 4]" },
        Filler { name: "dup_union", ty: Ty::IntColl, needs: &[], decls: "", expr: "[1, 2] ++ [1, 2]" },
        Filler { name: "map_lit", ty: Ty::IntColl, needs: &[], decls: "", expr: "map([(\"a\", 1), (\"b\", 2)])" },
        Filler { name: "binder_list", ty: Ty::IntColl, needs: &[Ty::Int], decls: "", expr: "[{b}, {b} * 2]" },
        Filler { name: "binder_comp", ty: Ty::IntColl, needs: &[Ty::Int], decls: "", expr: "[z2 * {b} for z2 in [1, 2]]" },
        Filler { name: "generator_coll", ty: Ty::IntColl, needs: &[], decls: indoc! {r#"
            def helper_gen2(hxs):
                for hx in hxs:
                    yield hx + 1
        "#}, expr: "helper_gen2([1, 2, 3])" },

        // --- values read out of a record binder
        Filler { name: "rec_binder_field", ty: Ty::Int, needs: &[Ty::Rec], decls: "", expr: "{b}.a" },
        Filler { name: "rec_binder_sum", ty: Ty::Int, needs: &[Ty::Rec], decls: "", expr: "{b}.a + {b}.b" },
        Filler { name: "rec_binder_in_comp", ty: Ty::Int, needs: &[Ty::Rec], decls: "", expr: "sum([z2 * {b}.a for z2 in [1, 2]])" },
        Filler { name: "rec_binder_cmp", ty: Ty::Bool, needs: &[Ty::Rec], decls: "", expr: "{b}.a > 1" },

        // --- strings and collections of them
        Filler { name: "str_list", ty: Ty::StrColl, needs: &[], decls: "", expr: "[\"a\", \"b\"]" },
        Filler { name: "str_comp", ty: Ty::StrColl, needs: &[], decls: "", expr: "[sz + \"!\" for sz in [\"a\", \"b\"]]" },
        Filler { name: "str_union", ty: Ty::StrColl, needs: &[], decls: "", expr: "[\"a\"] ++ [\"b\"]" },
        Filler { name: "str_binder_concat", ty: Ty::Str, needs: &[Ty::Str], decls: "", expr: "{b} + \"!\"" },

        // --- variants
        Filler { name: "variant_some", ty: Ty::Variant, needs: &[], decls: "", expr: "`some(7)" },
        Filler { name: "variant_none", ty: Ty::Variant, needs: &[], decls: "", expr: "`none" },
        Filler { name: "variant_computed", ty: Ty::Variant, needs: &[], decls: "", expr: "`some(sum([1, 2]))" },
        Filler { name: "variant_ternary", ty: Ty::Variant, needs: &[], decls: "", expr: "(`some(1) if 2 > 1 else `none)" },

        // --- records and collections of them
        Filler { name: "rec_lit", ty: Ty::Rec, needs: &[], decls: "", expr: "(a=1, b=2)" },
        Filler { name: "rec_computed", ty: Ty::Rec, needs: &[], decls: "", expr: "(a=sum([1, 2]), b=max([3, 4]))" },
        Filler { name: "rec_binder", ty: Ty::Rec, needs: &[Ty::Int], decls: "", expr: "(a={b}, b={b} * 2)" },
        Filler { name: "rec_list", ty: Ty::RecColl, needs: &[], decls: "", expr: "[(a=1, b=2), (a=3, b=2)]" },
        Filler { name: "rec_comp", ty: Ty::RecColl, needs: &[], decls: "", expr: "[(a=z, b=1) for z in [1, 2, 3]]" },
        Filler { name: "rec_filtered", ty: Ty::RecColl, needs: &[], decls: "", expr: "[r2 for r2 in [(a=1, b=2), (a=3, b=2)] if r2.a > 1]" },

        // --- reading both binders in scope
        Filler { name: "two_binders", ty: Ty::Int, needs: &[Ty::Int, Ty::Int], decls: "", expr: "{b} + {c}" },
        Filler { name: "two_binders_arith", ty: Ty::Int, needs: &[Ty::Int, Ty::Int], decls: "", expr: "{b} * 10 + {c}" },
        Filler { name: "two_binders_in_comp", ty: Ty::Int, needs: &[Ty::Int, Ty::Int], decls: "", expr: "sum([z2 * {b} + {c} for z2 in [1, 2]])" },
        Filler { name: "two_binders_in_filter", ty: Ty::Int, needs: &[Ty::Int, Ty::Int], decls: "", expr: "sum([z2 for z2 in [1, 2, 3] if z2 > {b} - {c}])" },
        Filler { name: "two_binders_ternary", ty: Ty::Int, needs: &[Ty::Int, Ty::Int], decls: "", expr: "({b} if {c} > 1 else {c})" },
        Filler { name: "two_binders_cmp", ty: Ty::Bool, needs: &[Ty::Int, Ty::Int], decls: "", expr: "{b} > {c}" },
        Filler { name: "rec_and_int", ty: Ty::Int, needs: &[Ty::Rec, Ty::Int], decls: "", expr: "{b}.a * {c}" },
        Filler { name: "rec_and_int_cmp", ty: Ty::Bool, needs: &[Ty::Rec, Ty::Int], decls: "", expr: "{b}.a > {c}" },

        // --- terminal reads of the store in scope. One `await_final` per variable: a second
        // reference to it is a compile error, so a filler with two would test the rule
        // rather than the compiler (chl-spec.md, "8.6 `await_final`").
        Filler { name: "terminal", ty: Ty::Int, needs: &[Ty::TxnStore], decls: "", expr: "await_final({b})" },
        Filler { name: "terminal_arith", ty: Ty::Int, needs: &[Ty::TxnStore], decls: "", expr: "await_final({b}) * 2 + 1" },
        Filler { name: "terminal_in_comp", ty: Ty::Int, needs: &[Ty::TxnStore], decls: "", expr: "sum([z2 + await_final({b}) for z2 in [1, 2]])" },
        Filler { name: "terminal_in_agg", ty: Ty::Int, needs: &[Ty::TxnStore], decls: "", expr: "max([await_final({b}), 0])" },
        Filler { name: "terminal_ternary", ty: Ty::Int, needs: &[Ty::TxnStore], decls: "", expr: "(await_final({b}) if 2 > 1 else 0)" },
        Filler { name: "terminal_cmp", ty: Ty::Bool, needs: &[Ty::TxnStore], decls: "", expr: "await_final({b}) > 90" },

        // --- records holding a collection
        Filler { name: "rec_with_list", ty: Ty::RecWithColl, needs: &[], decls: "", expr: "(xs=[1, 2, 3], n=4)" },
        Filler { name: "rec_with_singleton", ty: Ty::RecWithColl, needs: &[], decls: "", expr: "(xs=[7], n=1)" },
        Filler { name: "rec_with_comp", ty: Ty::RecWithColl, needs: &[], decls: "", expr: "(xs=[z2 * 2 for z2 in [1, 2]], n=1)" },
        Filler { name: "rec_with_empty", ty: Ty::RecWithColl, needs: &[], decls: "", expr: "(xs=[z2 for z2 in [1, 2] if z2 > 99], n=0)" },
        Filler { name: "rec_with_union", ty: Ty::RecWithColl, needs: &[], decls: "", expr: "(xs=[1, 2] ++ [3], n=2)" },
        Filler { name: "rec_with_map", ty: Ty::RecWithColl, needs: &[], decls: "", expr: "(xs=map([(\"a\", 1), (\"b\", 2)]), n=3)" },
        Filler { name: "rec_with_binder_coll", ty: Ty::RecWithColl, needs: &[Ty::Int], decls: "", expr: "(xs=[{b}, {b} * 2], n={b})" },
    ]
}

/// The names a filler writes its binder reads as, in scope order.
const PLACEHOLDERS: [&str; 2] = ["{b}", "{c}"];

/// Every way this filler can sit in this hole: the types agree, and each binder the filler
/// reads is bound to a distinct scope position holding what it expects. Answered as those
/// positions, one list per way.
fn placements(skeleton: &Skeleton, filler: &Filler) -> Vec<Vec<usize>> {
    fn extend(
        scope: &[(&str, Ty)],
        needs: &[Ty],
        chosen: &mut Vec<usize>,
        out: &mut Vec<Vec<usize>>,
    ) {
        let Some((wanted, rest)) = needs.split_first() else {
            out.push(chosen.clone());
            return;
        };
        for (i, (_, held)) in scope.iter().enumerate() {
            if held == wanted && !chosen.contains(&i) {
                chosen.push(i);
                extend(scope, rest, chosen, out);
                chosen.pop();
            }
        }
    }
    let mut out = Vec::new();
    if skeleton.hole == filler.ty {
        extend(skeleton.scope, filler.needs, &mut Vec::new(), &mut out);
    }
    out
}

/// A cell's name: the skeleton, the filler, and the binders the filler reads, so a
/// skeleton gaining a binder adds cells without renaming the ones it had.
fn cell_name(skeleton: &Skeleton, filler: &Filler, placement: &[usize]) -> String {
    if placement.is_empty() {
        return format!("{}/{}", skeleton.name, filler.name);
    }
    let binders: Vec<&str> = placement.iter().map(|&i| skeleton.scope[i].0).collect();
    format!("{}/{}[{}]", skeleton.name, filler.name, binders.join(","))
}

/// Build the program for one pair.
fn program(skeleton: &Skeleton, filler: &Filler, placement: &[usize]) -> String {
    let mut expr = filler.expr.to_string();
    for (placeholder, &i) in PLACEHOLDERS.iter().zip(placement) {
        expr = expr.replace(placeholder, skeleton.scope[i].0);
    }
    let body = skeleton.body.replace("{}", &expr);
    if filler.decls.is_empty() {
        body
    } else {
        format!("{}\n{}", filler.decls.trim_end(), body)
    }
}

/// Run one program through both oracles.
///
/// The compiler runs whatever the interpreter said. A program the oracle cannot judge can
/// still crash the compiler, and a crash is a bug whether or not anything was going to
/// compare the answer, so the compiler's verdict is taken first and the comparison only
/// happens when both sides produced a value.
fn classify(source: &str) -> Outcome {
    let interpreted = catch_unwind(AssertUnwindSafe(|| run_interpreted(source)));
    let compiled = catch_unwind(AssertUnwindSafe(|| run_compiled(source)));

    let c = match compiled {
        Err(payload) => return Outcome::CompilerPanics(first_line(&panic_message(&*payload))),
        Ok(Compiled::Rejected(errs)) => return Outcome::CompilerRejects(first_line(&errs)),
        Ok(Compiled::Unreadable(e)) => {
            return Outcome::CompilerPanics(format!("sink unreadable: {e}"));
        }
        Ok(Compiled::DidNotFinish) => return Outcome::DidNotFinish,
        Ok(Compiled::Value(c)) => c,
    };
    match interpreted {
        Err(payload) => Outcome::OraclePanics(first_line(&panic_message(&*payload))),
        Ok(Err(why)) => Outcome::OracleGap(why),
        Ok(Ok(i)) if c == i => Outcome::Agrees,
        Ok(Ok(i)) => Outcome::Disagrees(format!("compiled {c} vs interpreted {i}")),
    }
}

/// The key one cause is tallied and pinned under.
///
/// A disagreement is keyed by the two values it renders, so a change to either answer
/// fails the ledger. Any other detail is keyed by the message stem [`message_stem`]
/// extracts.
fn cause_key(outcome: &Outcome) -> String {
    match outcome {
        Outcome::Disagrees(d) => d.clone(),
        other => message_stem(other.detail()),
    }
}

/// A message with everything that varies per program removed.
///
/// A rendered compile error is `Debug` output, so its outer variant is kept and the
/// wrapping between it and the message is dropped, as is an assertion's fixed wording.
/// Every bracketed, parenthesized or quoted segment becomes `…`, since that is where a
/// message shows the type, term or name it saw, and every digit run becomes `#`, since
/// inference-variable ids and binder uids count from the start of the run. The stem keeps
/// at most its first 16 words.
fn message_stem(detail: &str) -> String {
    const WORDS: usize = 16;
    let (variant, message) = match detail.strip_prefix('[') {
        Some(rest) => {
            let variant: String = rest.chars().take_while(|c| c.is_alphanumeric()).collect();
            // Where the message starts: a string payload `("…")`, a `message: "…"` field,
            // or an inference error's `error: …`, whichever comes first.
            let message = ["(\"", "message: \"", "error: "]
                .iter()
                .filter_map(|m| rest.find(m).map(|i| i + m.len()))
                .min()
                .map_or(&rest[variant.len()..], |i| &rest[i..]);
            // The wrapper's closing delimiters, and the span an inference error carries.
            let message = message.split(", span: ").next().unwrap_or(message);
            let message = message.trim_end_matches(['"', ')', ']', '}', ' ']);
            (format!("{variant}: "), message)
        }
        None => (String::new(), detail),
    };
    // An assertion's own wording is the same for every assertion; its message follows.
    let message = ["assertion `left == right` failed: ", "assertion failed: "]
        .iter()
        .find_map(|p| message.strip_prefix(p))
        .unwrap_or(message);

    let mut stem = String::new();
    let mut closers: Vec<char> = Vec::new();
    let mut chars = message.chars().peekable();
    let mut previous = ' ';
    while let Some(c) = chars.next() {
        // An apostrophe inside a word (`function's`) is not a quote.
        let quote = matches!(c, '`' | '"') || (c == '\'' && !previous.is_alphanumeric());
        previous = c;
        let closer = match c {
            '(' => Some(')'),
            '[' => Some(']'),
            '{' => Some('}'),
            _ if quote && closers.last() != Some(&c) => Some(c),
            _ => None,
        };
        if closers.last() == Some(&c) {
            closers.pop();
            continue;
        }
        if let Some(closer) = closer {
            if closers.is_empty() {
                stem.push('…');
            }
            closers.push(closer);
            continue;
        }
        if !closers.is_empty() {
            continue;
        }
        if c.is_ascii_digit() {
            while chars.peek().is_some_and(char::is_ascii_digit) {
                chars.next();
            }
            stem.push('#');
        } else {
            stem.push(c);
        }
    }
    let words: Vec<&str> = stem.split_whitespace().take(WORDS).collect();
    format!("{variant}{}", words.join(" "))
}

/// The message a caught panic carried.
fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_else(|| "non-string panic".into())
}

/// The first line of a message, whole: the cause key is cut from it, and a cut taken before
/// the key would split one cause wherever the cut lands.
fn first_line(msg: &str) -> String {
    msg.lines().next().unwrap_or("").trim().to_string()
}

/// `TxnStore` names what a binder denotes, and no expression has that type. A hole wanting
/// one, or a filler claiming to produce one, would substitute an expression where a store
/// name has to stand.
#[test]
fn no_hole_wants_a_store() {
    for s in &skeletons() {
        assert_ne!(
            s.hole,
            Ty::TxnStore,
            "skeleton `{}` wants a store in its hole",
            s.name
        );
    }
    for f in &fillers() {
        assert_ne!(
            f.ty,
            Ty::TxnStore,
            "filler `{}` claims to produce a store",
            f.name
        );
    }
}

/// A filler that reads a binder must not bind a skeleton binder's name itself, or the read
/// a placement names is a read of the filler's local instead.
#[test]
fn no_filler_binds_a_skeleton_binder() {
    let scope_names: Vec<&str> = skeletons()
        .iter()
        .flat_map(|s| s.scope.iter().map(|(n, _)| *n))
        .collect();
    // A closed filler reads no binder, so nothing of its can be captured.
    for f in fillers().iter().filter(|f| !f.needs.is_empty()) {
        for n in &scope_names {
            assert!(
                !f.expr.contains(&format!("for {n} in")) && !f.expr.contains(&format!("\\{n} ->")),
                "filler `{}` binds `{n}`, which a skeleton puts in scope",
                f.name
            );
        }
    }
}

/// A filler names its binders through [`PLACEHOLDERS`], so it can read at most that many.
#[test]
fn no_filler_reads_more_binders_than_can_be_named() {
    for f in &fillers() {
        assert!(
            f.needs.len() <= PLACEHOLDERS.len(),
            "filler `{}` reads {} binders and only {} can be named",
            f.name,
            f.needs.len(),
            PLACEHOLDERS.len(),
        );
    }
}

#[test]
fn a_message_stem_drops_what_varies_per_program() {
    let stem = |d: &str| message_stem(d);
    assert_eq!(
        stem(r#"[Conversion(Unsupported("unrecognised Var(i) in λ-free CCL"))]"#),
        stem(r#"[Conversion(Unsupported("unrecognised Var(q) in λ-free CCL"))]"#),
    );
    assert_eq!(
        stem("[Infer { error: Type mismatch for Apply: expected [0, 2], found Int, span: None }]"),
        "Infer: Type mismatch for Apply: expected …, found Int",
    );
    assert_eq!(
        stem("FanIn pairs collections over 1 ambient level(s), got Fn(String → Int) and Int"),
        stem("FanIn pairs collections over 1 ambient level(s), got Fn({[0, 2]} → Int) and Int"),
    );
    assert_ne!(
        stem(r#"[Conversion(Unsupported("unrecognised Var(i) in λ-free CCL"))]"#),
        stem(r#"[Conversion(Unsupported("a list element must be a constant"))]"#),
    );
    assert_eq!(
        stem(
            r#"[Lower(Unsupported { span: Span { start: 1, end: 2 }, message: "a list element must be a constant" })]"#
        ),
        "Lower: a list element must be a constant",
    );
    // The distinguishing tail survives a parenthesized aside.
    assert_ne!(
        stem(
            "Only higher-order combinators (map, const, zip) can take an input operator; found input for non-combinator curry"
        ),
        stem(
            "Only higher-order combinators (map, const, zip) can take an input operator; found input for non-combinator zip"
        ),
    );
    assert_eq!(
        stem("an unnamed function's codomain references it"),
        "an unnamed function's codomain references it"
    );
}

thread_local! {
    /// Whether this thread is inside `classify`, where a panic is an outcome.
    static CLASSIFYING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[test]
#[cfg_attr(
    not(debug_assertions),
    ignore = "the ledger records the verdicts of a build with `debug_assertions`: a debug-only \
              check reports a defect at the stage that introduced it, and without one a later \
              stage reports the same defect in its own words"
)]
fn enumerate_pairs() {
    // A panic inside `classify` is an outcome, so the default hook's backtrace is noise
    // there. Only those are silenced: the hook is process-wide, the other tests in this
    // binary run concurrently, and this test's own assertions must still print.
    let previous: Arc<dyn Fn(&std::panic::PanicHookInfo<'_>) + Send + Sync> =
        Arc::from(std::panic::take_hook());
    let show = std::env::var("PAIRS_SHOW_PANICS").is_ok();
    let delegate = previous.clone();
    std::panic::set_hook(Box::new(move |info| {
        if show || !CLASSIFYING.get() {
            delegate(info);
        }
    }));

    let (skeletons, fillers) = (skeletons(), fillers());
    let mut tally: BTreeMap<&str, usize> = BTreeMap::new();
    let mut observed: BTreeMap<String, (&str, String)> = BTreeMap::new();
    let mut details: BTreeMap<String, String> = BTreeMap::new();
    let mut programs: BTreeMap<String, String> = BTreeMap::new();

    for s in &skeletons {
        for f in &fillers {
            for placement in placements(s, f) {
                let cell = cell_name(s, f, &placement);
                let source = program(s, f, &placement);
                // Two pairs can spell one program (`feed/sum_lit` is
                // `aggregate_arg/list_lit`); it runs once, under the first cell's name.
                if programs.insert(source.clone(), cell.clone()).is_some() {
                    continue;
                }
                CLASSIFYING.set(true);
                let outcome = classify(&source);
                CLASSIFYING.set(false);
                *tally.entry(outcome.kind()).or_default() += 1;
                if outcome != Outcome::Agrees {
                    details.insert(cell.clone(), outcome.detail().to_string());
                    observed.insert(cell.clone(), (outcome.kind(), cause_key(&outcome)));
                }
            }
        }
    }

    std::panic::set_hook(Box::new(move |info| previous(info)));

    println!("\n=== {} pairs ===", programs.len());
    for (kind, n) in &tally {
        println!("{kind:>16}: {n}");
    }

    let rendered: String = observed
        .iter()
        .map(|(cell, (kind, cause))| format!("{cell}\t{kind}\t{cause}\n"))
        .collect();
    if std::env::var("PAIRS_BLESS").is_ok() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/generated_pairs.ledger");
        std::fs::write(path, &rendered).expect("write the ledger");
        return;
    }

    // Two-sided: a cell the ledger lacks is a new failure, a cell whose line differs failed
    // differently, and a ledger line the run lacks is a cell that now agrees or is no longer
    // generated.
    let mut pinned: BTreeMap<&str, &str> = BTreeMap::new();
    for line in LEDGER.lines() {
        let (cell, rest) = line
            .split_once('\t')
            .unwrap_or_else(|| panic!("a ledger line is `cell<TAB>kind<TAB>cause`: {line}"));
        assert!(
            pinned.insert(cell, rest).is_none(),
            "`{cell}` is in the ledger twice"
        );
    }
    let mut drift = Vec::new();
    for (cell, (kind, cause)) in &observed {
        let now = format!("{kind}\t{cause}");
        match pinned.get(cell.as_str()) {
            None => drift.push(format!("new     {cell}\t{now}\n        {}", details[cell])),
            Some(was) if *was != now => drift.push(format!(
                "changed {cell}\n        was {was}\n        now {now}\n        {}",
                details[cell]
            )),
            Some(_) => {}
        }
    }
    for (cell, was) in &pinned {
        if !observed.contains_key(*cell) {
            drift.push(format!("gone    {cell}\t(was {was})"));
        }
    }
    assert!(
        drift.is_empty(),
        "the grid drifted from tests/generated_pairs.ledger (PAIRS_BLESS=1 rewrites it):\n{}",
        drift.join("\n")
    );
}
