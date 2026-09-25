//! Generated pairs: every type-compatible (skeleton, filler) program, run through both the
//! compiler and the differential interpreter.
//!
//! A compiler defect is often one feature inside another: a collection under a feed, a
//! record holding a collection, a comprehension inside a loop. So the unit here is a
//! **position** and what fills it, rather than a random term: a skeleton is a whole program
//! with one hole, a filler is an expression that can sit in it, and the corpus is every pair
//! whose types agree.
//!
//! Enumerated rather than sampled, which buys determinism: no seed and no flaky
//! reproduction. `every_filler_and_binder_is_reached` holds the tables to generating at least
//! one cell per filler and per skeleton binder.
//!
//! Two checks run per program:
//!
//! - a compiler panic, including a failed assertion or phase-boundary check, is a bug by
//!   construction, whatever the program;
//! - a disagreement between compiler and interpreter is a wrong answer.
//!
//! Outcomes are classified by mechanism: any `CompileError` is a rejection, whether its
//! message states a gap or reports a compiler bug, and a sink the compiled program could not
//! read counts as a panic. An interpreter refusal is a gap in the differential interpreter, not
//! in the compiler.
//!
//! Two tests run the grid:
//!
//! - `live_rows_agree` runs every cell of each skeleton in [`LIVE`], the rows known to agree
//!   everywhere, and fails on any outcome other than agreement.
//! - `full_grid` is ignored by default. It runs every cell and reports the failures grouped by
//!   cause, with a count and sample cells, and names every fully agreeing row [`LIVE`] does not
//!   list yet. A fix that makes a row agree moves it into [`LIVE`]:
//!   `cargo test --test generated_pairs full_grid -- --ignored --nocapture`.

#[path = "support/differential.rs"]
mod differential;
#[path = "support/panic_message.rs"]
mod panic_message;

use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use differential::{Compiled, run_compiled, run_interpreted};
use indoc::indoc;
use panic_message::panic_message;

/// The skeletons whose every cell agrees, so a change that breaks one of them fails
/// `live_rows_agree`.
const LIVE: &[&str] = &[
    "aggregate_arg",
    "binop_operand",
    "bool_feed",
    "comp_source",
    "feed",
    "function_arg",
    "function_body",
    "groupby_source",
    "match_scrutinee",
    "mut_init",
    "record_coll_source",
    "record_feed",
    "record_feed_in_loop",
    "record_field",
    "record_projected",
    "str_coll_source",
    "str_loop_feed",
    "string_feed",
    "ternary_branch",
    "tuple_component",
    "txn_guard",
    "variant_feed",
];

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
    /// The compiler panicked, including a failed assertion or phase-boundary check, or the
    /// program completed with a sink that could not state a value.
    CompilerPanics(String),
    /// The compiler answered a `CompileError`, whether it states a gap or reports a compiler
    /// bug.
    CompilerRejects(String),
    /// The interpreter does not cover the program. Carries the interpreter's reason and the
    /// value the compiler produced, which the report shows beside the reason.
    InterpreterGap(String, String),
    /// The interpreter itself crashed, which is a defect in the differential interpreter rather
    /// than in the compiler. Named separately so it can never be read as a compiler finding.
    InterpreterPanics(String),
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
            Outcome::InterpreterGap(..) => "InterpreterGap",
            Outcome::InterpreterPanics(_) => "InterpreterPanics",
            Outcome::DidNotFinish => "DidNotFinish",
        }
    }

    fn detail(&self) -> &str {
        match self {
            Outcome::Agrees | Outcome::DidNotFinish => "",
            Outcome::Disagrees(d)
            | Outcome::CompilerPanics(d)
            | Outcome::CompilerRejects(d)
            | Outcome::InterpreterGap(d, _)
            | Outcome::InterpreterPanics(d) => d,
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
        // A collection built from a loop binder, as a comprehension's source and as a nested
        // loop's.
        Skeleton { name: "comp_source_in_loop", hole: Ty::IntColl, scope: &[("i", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            for i in [1, 2]:
                out << sum([q * 2 for q in {}])
        "#}},
        Skeleton { name: "loop_source_in_loop", hole: Ty::IntColl, scope: &[("i", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            for i in [1, 2]:
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
        Skeleton { name: "ternary_branch", hole: Ty::Int, scope: &[("n", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            n = 5
            out << ({} if n > 3 else 0)
        "#}},
        // The store is in scope as well as the iteration: a filler reading it makes an
        // in-context read before the write (`docs/chl-spec.md`, "8.3 Reads"), and the reply
        // after the write reads its own write.
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
        Skeleton { name: "txn_reply", hole: Ty::Int, scope: &[("pool", Ty::Int), ("r", Ty::Int)], body: indoc! {r#"
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
        Skeleton { name: "mut_write_rhs", hole: Ty::Int, scope: &[("acc", Ty::Int), ("i", Ty::Int)], body: indoc! {r#"
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
        // Feeds a collection rather than folding it first. The compiled sink holds the
        // elements and the interpreter one contribution holding the collection, and
        // `the_comparison_discriminates` holds that disagreement: a grid with no
        // disagreement at all would not say whether the comparison can see one.
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
        Skeleton { name: "record_feed_in_loop", hole: Ty::Rec, scope: &[("i", Ty::Int)], body: indoc! {r#"
            out = test_sink()
            for i in [1, 2]:
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
        Skeleton { name: "str_loop_guard", hole: Ty::Bool, scope: &[("sv", Ty::Str)], body: indoc! {r#"
            out = test_sink()
            for sv in ["a", "b"]:
                out << (1 if {} else 0)
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
        Filler { name: "str_binder_ternary", ty: Ty::Int, needs: &[Ty::Str], decls: "", expr: "(1 if {b} == \"b\" else 0)" },

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
        // rather than the compiler (`docs/chl-spec.md`, "8.6 `await_final`").
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

/// The names a filler writes its binder reads as, in `needs` order.
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

/// A cell's name: the skeleton, the filler, and the binders the filler reads.
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

/// Run one program through the compiler and the differential interpreter.
///
/// The compiler runs whatever the interpreter said. A program the interpreter cannot judge can
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
        Err(payload) => Outcome::InterpreterPanics(first_line(&panic_message(&*payload))),
        Ok(Err(why)) => Outcome::InterpreterGap(why, c.to_string()),
        Ok(Ok(i)) if c == i => Outcome::Agrees,
        Ok(Ok(i)) => Outcome::Disagrees(format!("compiled {c} vs interpreted {i}")),
    }
}

/// The key the report groups one cause's cells under.
///
/// A disagreement is keyed by the two values it renders, and an interpreter gap by its message
/// stem and the value the compiler produced. Any other detail is keyed by the message stem
/// [`message_stem`] extracts, so the cells one defect fails group together.
fn cause_key(outcome: &Outcome) -> String {
    match outcome {
        Outcome::Disagrees(d) => d.clone(),
        Outcome::InterpreterGap(why, compiled) => {
            format!("{} / compiled {compiled}", message_stem(why))
        }
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

/// The first line of a message. [`message_stem`] bounds the key cut from it.
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

/// A name is a cell's identity in a report, and a skeleton substitutes its filler once.
#[test]
fn names_are_unique_and_each_skeleton_has_one_hole() {
    let mut names = std::collections::BTreeSet::new();
    for s in &skeletons() {
        assert!(names.insert(s.name), "two skeletons are named `{}`", s.name);
        assert_eq!(
            s.body.matches("{}").count(),
            1,
            "skeleton `{}` has other than one hole",
            s.name
        );
    }
    let mut names = std::collections::BTreeSet::new();
    for f in &fillers() {
        assert!(names.insert(f.name), "two fillers are named `{}`", f.name);
    }
}

/// Every filler sits in some hole, every skeleton has a cell, and every skeleton binder is
/// read by some filler, so no row of either table is dead weight.
#[test]
fn every_filler_and_binder_is_reached() {
    let (skeletons, fillers) = (skeletons(), fillers());
    for f in &fillers {
        assert!(
            skeletons.iter().any(|s| !placements(s, f).is_empty()),
            "filler `{}` fits no hole",
            f.name
        );
    }
    for s in &skeletons {
        assert!(
            fillers.iter().any(|f| !placements(s, f).is_empty()),
            "skeleton `{}` has no cell",
            s.name
        );
        for (i, (binder, _)) in s.scope.iter().enumerate() {
            assert!(
                fillers
                    .iter()
                    .any(|f| placements(s, f).iter().any(|p| p.contains(&i))),
                "no filler reads `{binder}` in skeleton `{}`",
                s.name
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
    let stem = message_stem;
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

/// Run every cell of the skeletons `rows` admits, and answer each cell's outcome.
///
/// Two pairs can spell one program (`feed/sum_lit` is `aggregate_arg/list_lit`); it runs once,
/// and every cell that spells it takes its outcome, so a failure counts against every row it
/// sits in.
fn run_cells(rows: impl Fn(&Skeleton) -> bool) -> BTreeMap<String, Outcome> {
    // A panic inside `classify` is an outcome, so the default hook's backtrace is noise
    // there. Only those are silenced: the hook is process-wide, the other tests in this
    // binary run concurrently, and a test's own assertions must still print.
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
    let mut outcomes = BTreeMap::new();
    let mut programs: BTreeMap<String, Outcome> = BTreeMap::new();
    for s in skeletons.iter().filter(|s| rows(s)) {
        for f in &fillers {
            for placement in placements(s, f) {
                let cell = cell_name(s, f, &placement);
                let source = program(s, f, &placement);
                let outcome = programs
                    .entry(source)
                    .or_insert_with_key(|source| {
                        CLASSIFYING.set(true);
                        let outcome = classify(source);
                        CLASSIFYING.set(false);
                        outcome
                    })
                    .clone();
                outcomes.insert(cell, outcome);
            }
        }
    }

    std::panic::set_hook(Box::new(move |info| previous(info)));
    outcomes
}

/// The comparison can see a disagreement: `feed_collection/list_lit` is one.
#[test]
fn the_comparison_discriminates() {
    let (skeletons, fillers) = (skeletons(), fillers());
    let s = skeletons
        .iter()
        .find(|s| s.name == "feed_collection")
        .unwrap();
    let f = fillers.iter().find(|f| f.name == "list_lit").unwrap();
    let outcome = classify(&program(s, f, &[]));
    assert!(
        matches!(outcome, Outcome::Disagrees(_)),
        "expected a disagreement, got {outcome:?}"
    );
}

/// Every [`LIVE`] name is a skeleton, once.
#[test]
fn live_names_skeletons() {
    let names: Vec<&str> = skeletons().iter().map(|s| s.name).collect();
    let mut seen = std::collections::BTreeSet::new();
    for live in LIVE {
        assert!(
            names.contains(live),
            "`{live}` is in LIVE but is not a skeleton"
        );
        assert!(seen.insert(live), "`{live}` is in LIVE twice");
    }
}

#[test]
fn live_rows_agree() {
    let failures: Vec<String> = run_cells(|s| LIVE.contains(&s.name))
        .into_iter()
        .filter(|(_, outcome)| *outcome != Outcome::Agrees)
        .map(|(cell, outcome)| format!("{cell}\t{}\t{}", outcome.kind(), outcome.detail()))
        .collect();
    assert!(
        failures.is_empty(),
        "cells of a live row no longer agree:\n{}",
        failures.join("\n")
    );
}

/// The whole grid, for choosing what to fix next: the failures by cause, most cells first,
/// and the rows that agree everywhere but are not yet [`LIVE`].
#[test]
#[ignore = "a report for prioritizing fixes, not a check: run with --ignored --nocapture"]
fn full_grid() {
    let outcomes = run_cells(|_| true);

    let mut tally: BTreeMap<&str, usize> = BTreeMap::new();
    let mut by_cause: BTreeMap<(&str, String), Vec<&str>> = BTreeMap::new();
    let mut failing_rows: BTreeMap<&str, usize> = BTreeMap::new();
    for (cell, outcome) in &outcomes {
        *tally.entry(outcome.kind()).or_default() += 1;
        if *outcome != Outcome::Agrees {
            by_cause
                .entry((outcome.kind(), cause_key(outcome)))
                .or_default()
                .push(cell);
            let row = cell.split('/').next().expect("a cell name has a skeleton");
            *failing_rows.entry(row).or_default() += 1;
        }
    }

    println!("\n=== {} cells ===", outcomes.len());
    for (kind, n) in &tally {
        println!("{kind:>16}: {n}");
    }
    let mut causes: Vec<_> = by_cause.into_iter().collect();
    causes.sort_by_key(|(_, cells)| std::cmp::Reverse(cells.len()));
    println!("\n=== {} causes ===", causes.len());
    for ((kind, cause), cells) in &causes {
        let sample: Vec<&str> = cells.iter().take(3).copied().collect();
        println!(
            "{:>4} {kind:<15} {cause}\n       e.g. {}",
            cells.len(),
            sample.join(", ")
        );
    }
    let promotable: Vec<&str> = skeletons()
        .iter()
        .map(|s| s.name)
        .filter(|n| !failing_rows.contains_key(n) && !LIVE.contains(n))
        .collect();
    println!("\n=== rows that agree everywhere but are not LIVE ===\n{promotable:?}");
}
