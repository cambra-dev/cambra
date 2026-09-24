//! Generated pairs: every type-compatible (skeleton, filler) program, run through both
//! oracles.
//!
//! Each of the four compiler defects this suite's hand-written sibling found was one
//! feature inside another — a collection under a feed, a collection in a record field, a
//! comprehension inside a loop, an aggregate over a keyed-written store. So the unit here
//! is a **position** and what fills it, rather than a random term: a skeleton is a whole
//! program with one hole, a filler is an expression that can sit in it, and the corpus is
//! every pair whose types agree.
//!
//! Enumerated rather than sampled. A program takes about 5ms, so all pairs cost about a
//! second, which buys determinism: no seed, no flaky reproduction, and coverage that can be
//! stated rather than estimated.
//!
//! Two oracles run per program, because three of the four known defects were crashes rather
//! than wrong answers:
//!
//! - a panic, assertion or wall failure is a bug by construction, whatever the program;
//! - a disagreement between compiler and interpreter is a wrong answer.
//!
//! A declared `CompileError` is a gap the compiler states, not a failure. An interpreter
//! refusal is a gap in the oracle, not in the compiler.

// The ledger records the verdicts of a build with `debug_assertions`: a debug-only check
// reports a defect at the stage that introduced it, and without one a later stage reports
// the same defect in its own words. The grid's own checks need no second profile.
#![cfg(debug_assertions)]

use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};

use cambra::ccl::context::{GlobalContext, compile_program};
use cambra::interpreter::{Consumer, Value as TileValue};
use chl_interp::{Collection, Value};
use indoc::indoc;

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
    /// The binders this expression reads, positionally against the skeleton's scope:
    /// `needs[0]` is the `{b}` in `expr`, `needs[1]` the `{c}`.
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
        }
    }

    fn detail(&self) -> &str {
        match self {
            Outcome::Agrees => "",
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
        Skeleton { name: "txn_write_rhs", hole: Ty::Int, scope: &[("r", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [1, 2]:
                with begin():
                    pool := {}
                    out << pool
        "#}},
        Skeleton { name: "txn_guard", hole: Ty::Bool, scope: &[("r", Ty::Int)], body: indoc! {r#"
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
        Skeleton { name: "subscript_target", hole: Ty::IntColl, scope: &[], body: indoc! {r#"
            out = test_sink()
            xs = {}
            out << xs[0]
        "#}},
        // Feeds a collection rather than folding it first. Known to disagree today, which
        // is what makes it the matrix's check on itself: a run with no disagreements at all
        // would not say whether the comparison discriminates.
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
        // Reads the store inside the block it writes: the read-your-writes path, which
        // nothing else in the grid reaches.
        Skeleton { name: "txn_reads_store", hole: Ty::Int, scope: &[("pool", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [1, 2]:
                with begin():
                    pool := {}
                    out << pool
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
        // The decision reads the store it guards, so what it commits on and what it writes
        // are the same tick's value. `txn_guard` reads only the iteration.
        Skeleton { name: "txn_guard_reads_store", hole: Ty::Bool, scope: &[("pool", Ty::Int), ("r", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [1, 2]:
                with begin():
                    if {}:
                        pool := pool - r
                        out << pool
        "#}},

        // Terminal reads. Every other transactional skeleton observes the store from inside
        // a block, which is an as-of read at that tick; `await_final` waits for the commits.
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
        // An aggregate of nothing: the identity, or an error, depending on the aggregate.
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
        Filler { name: "binder_in_comp", ty: Ty::Int, needs: &[Ty::Int], decls: "", expr: "sum([z * {b} for z in [1, 2]])" },
        Filler { name: "binder_in_comp_filter", ty: Ty::Int, needs: &[Ty::Int], decls: "", expr: "sum([z for z in [1, 2, 3] if z > {b}])" },
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
        Filler { name: "binder_cmp_on_comp", ty: Ty::Bool, needs: &[Ty::Int], decls: "", expr: "sum([z for z in [1, 2]]) > {b}" },
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
        Filler { name: "binder_comp", ty: Ty::IntColl, needs: &[Ty::Int], decls: "", expr: "[z * {b} for z in [1, 2]]" },
        Filler { name: "generator_coll", ty: Ty::IntColl, needs: &[], decls: indoc! {r#"
            def helper_gen2(hxs):
                for hx in hxs:
                    yield hx + 1
        "#}, expr: "helper_gen2([1, 2, 3])" },

        // --- values read out of a record binder
        Filler { name: "rec_binder_field", ty: Ty::Int, needs: &[Ty::Rec], decls: "", expr: "{b}.a" },
        Filler { name: "rec_binder_sum", ty: Ty::Int, needs: &[Ty::Rec], decls: "", expr: "{b}.a + {b}.b" },
        Filler { name: "rec_binder_in_comp", ty: Ty::Int, needs: &[Ty::Rec], decls: "", expr: "sum([z * {b}.a for z in [1, 2]])" },
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

/// Whether this filler can sit in this hole: the types agree, and every binder the filler
/// reads is in scope there and holds what it expects.
///
/// The match is positional, so a filler reading one binder always reads the outermost one. A
/// skeleton that gains an inner binder keeps the one it already declared first, which is what
/// holds its existing cells still.
fn compatible(skeleton: &Skeleton, filler: &Filler) -> bool {
    skeleton.hole == filler.ty
        && filler.needs.len() <= skeleton.scope.len()
        && (filler.needs.iter())
            .zip(skeleton.scope)
            .all(|(wanted, (_, held))| wanted == held)
}

/// Build the program for one pair.
fn program(skeleton: &Skeleton, filler: &Filler) -> String {
    assert!(
        skeleton.scope.len() <= PLACEHOLDERS.len(),
        "skeleton `{}` puts {} binders in scope and only {} of them can be named",
        skeleton.name,
        skeleton.scope.len(),
        PLACEHOLDERS.len(),
    );
    let mut expr = filler.expr.to_string();
    for (placeholder, (name, _)) in PLACEHOLDERS.iter().zip(skeleton.scope) {
        expr = expr.replace(placeholder, name);
    }
    let body = skeleton.body.replace("{}", &expr);
    if filler.decls.is_empty() {
        body
    } else {
        format!("{}\n{}", filler.decls.trim_end(), body)
    }
}

fn convert(v: TileValue) -> Value {
    match v {
        TileValue::Int(i) => Value::Int(i),
        TileValue::UInt(u) => Value::Int(u as i64),
        TileValue::String(s) => Value::Str(s.to_string()),
        TileValue::Bool(b) => Value::Bool(b),
        TileValue::Unit => Value::Unit,
        TileValue::Record(fields) => {
            Value::Record(fields.into_iter().map(|(n, v)| (n, convert(v))).collect())
        }
        TileValue::Union { tag, inner } => Value::Variant {
            tag: tag.to_string(),
            payload: Box::new(convert(*inner)),
        },
        TileValue::Function(bindings) => Value::Collection(Collection::from_entries(
            bindings
                .into_iter()
                .map(|b| (convert(b.input), convert(b.output)))
                .collect(),
        )),
        TileValue::ComputableFunction(_) => Value::Unit,
    }
}

/// Run one program through both oracles.
///
/// The compiler runs whatever the interpreter said. A program the oracle cannot judge can
/// still crash the compiler, and a crash is a bug whether or not anything was going to
/// compare the answer — so the compiler's verdict is taken first and the comparison only
/// happens when both sides produced a value.
fn classify(source: &str) -> Outcome {
    let interp_source = source.to_string();
    let interpreted = match catch_unwind(AssertUnwindSafe(move || {
        chl_interp::run(&interp_source, BTreeMap::new())
    })) {
        Err(payload) => {
            let msg = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "non-string panic".into());
            return Outcome::OraclePanics(first_line(&msg));
        }
        Ok(r) => r
            .map_err(|e| e.to_string())
            .and_then(|mut obs| obs.remove("out").ok_or_else(|| "no sink `out`".to_string())),
    };

    let source_owned = source.to_string();
    let compiled = catch_unwind(AssertUnwindSafe(move || {
        const CAP: usize = 10_000;
        let mut ctx = GlobalContext::default();
        let sink = ctx.register_test_sink("out");
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let program = compile_program(&mut ctx, &source_owned, consumer)?;
        for _ in 0..CAP {
            ctx.scheduler().check_for_notifications();
            if program.done.try_recv().is_ok() {
                break;
            }
        }
        Ok::<_, Vec<cambra::ccl::context::CompileError>>(sink.value())
    }));

    match compiled {
        Err(payload) => {
            let msg = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "non-string panic".into());
            Outcome::CompilerPanics(first_line(&msg))
        }
        Ok(Err(errs)) => Outcome::CompilerRejects(first_line(&format!("{errs:?}"))),
        Ok(Ok(Err(e))) => Outcome::CompilerPanics(format!("sink unreadable: {e}")),
        Ok(Ok(Ok(v))) => match interpreted {
            Err(why) => Outcome::OracleGap(why),
            Ok(i) => {
                let c = convert(v);
                if c == i {
                    Outcome::Agrees
                } else {
                    Outcome::Disagrees(format!("compiled {c} vs interpreted {i}"))
                }
            }
        },
    }
}

/// The key one cause is tallied under.
///
/// Two things come out of the message first. Inference-variable ids and binder uids count
/// from the start of the run, so adding a skeleton renumbers every message after it and one
/// cause reads as two across runs. And a defect reported with the types it saw yields a
/// family of messages differing only in those types, so the key is a prefix: long enough to
/// separate causes, short enough that a rendered type is mostly cut off.
fn cause_key(detail: &str) -> String {
    let mut key = String::new();
    let mut chars = detail.chars().peekable();
    while let Some(c) = chars.next() {
        key.push(c);
        if c == '?' || key.ends_with("uid: ") {
            while chars.peek().is_some_and(char::is_ascii_digit) {
                chars.next();
            }
        }
    }
    key.chars().take(58).collect()
}

/// The first line of a message, trimmed: a panic's detail is usually its first sentence and
/// the rest is a backtrace hint.
fn first_line(msg: &str) -> String {
    // By characters, not bytes: these messages render types, and a byte slice lands inside
    // a multi-byte arrow.
    let line = msg.lines().next().unwrap_or("").trim();
    let truncated: String = line.chars().take(140).collect();
    if truncated.chars().count() < line.chars().count() {
        format!("{truncated}…")
    } else {
        truncated
    }
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

#[test]
fn enumerate_pairs() {
    // Panics are an outcome here, so the default hook's backtrace spam is noise.
    let hook = std::panic::take_hook();
    if std::env::var("PAIRS_SHOW_PANICS").is_err() {
        std::panic::set_hook(Box::new(|_| {}));
    }

    let (skeletons, fillers) = (skeletons(), fillers());
    let mut tally: BTreeMap<String, usize> = BTreeMap::new();
    let mut interesting: Vec<(String, Outcome)> = Vec::new();
    let mut total = 0;

    for s in &skeletons {
        for f in &fillers {
            if !compatible(s, f) {
                continue;
            }
            total += 1;
            let outcome = classify(&program(s, f));
            *tally.entry(outcome.kind().to_string()).or_default() += 1;
            if outcome != Outcome::Agrees {
                interesting.push((format!("{}/{}", s.name, f.name), outcome));
            }
        }
    }

    std::panic::set_hook(hook);

    println!("\n=== {total} pairs ===");
    for (outcome, n) in &tally {
        println!("{outcome:>16}: {n}");
    }
    // Group by cause: one defect reached through many fillers is one defect.
    println!("\n=== distinct causes ===");
    let mut by_cause: BTreeMap<(&str, String), (&str, Vec<String>)> = BTreeMap::new();
    for (name, outcome) in &interesting {
        by_cause
            .entry((outcome.kind(), cause_key(outcome.detail())))
            // The first cell's whole message, so the report reads as what the compiler said
            // rather than as the truncated key its cells were bucketed under.
            .or_insert_with(|| (outcome.detail(), Vec::new()))
            .1
            .push(name.clone());
    }
    for ((kind, _), (detail, cells)) in &by_cause {
        println!(
            "\n{kind} ({} cell(s))\n  {detail}\n  e.g. {}",
            cells.len(),
            cells[0]
        );
        if cells.len() > 1 {
            println!("  all: {}", cells.join(", "));
        }
    }
}
