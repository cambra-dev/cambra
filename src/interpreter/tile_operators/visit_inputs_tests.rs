//! The operator kinds a corpus of compiled programs reaches through `TileOperator::visit_inputs`.

use std::collections::{BTreeSet, HashSet};
use std::sync::{Arc, Mutex};

use indoc::indoc;

use super::*;
use crate::ccl::Type;
use crate::ccl::context::{GlobalContext, compile_program};
use crate::ccl::load::LoadedProgram;
use crate::interpreter::operator_graph::EdgeKind;
use crate::interpreter::{BaseType, Extent, TestDataSource};

/// Record the kind of `op` and of everything below it through the owned and shared inputs it
/// states.
fn reached_by_value_edges(op: &dyn TileOperator, kinds: &mut BTreeSet<&'static str>) {
    kinds.insert(op.kind());
    op.visit_inputs(&mut |edge| {
        if matches!(
            edge.kind,
            EdgeKind::Value { deferred: false } | EdgeKind::Share
        ) {
            reached_by_value_edges(edge.target, kinds);
        }
    });
}

/// The kinds of the operators that state an input, reached through every edge `visit_inputs`
/// states, deferred ones included, each node once.
fn kinds_with_inputs(
    op: &dyn TileOperator,
    seen: &mut HashSet<NodeId>,
    kinds: &mut BTreeSet<&'static str>,
) {
    if let Some(id) = op.operator_id()
        && !seen.insert(id)
    {
        return;
    }
    let mut holds_one = false;
    op.visit_inputs(&mut |edge| {
        holds_one = true;
        kinds_with_inputs(edge.target, seen, kinds);
    });
    if holds_one {
        kinds.insert(op.kind());
    }
}

/// A program of the corpus, and what its context registers.
struct Case {
    code: &'static str,
    source: bool,
    sinks: &'static [&'static str],
}

fn pure(code: &'static str) -> Case {
    Case {
        code,
        source: false,
        sinks: &[],
    }
}

/// Programs over the operator families a graph holds: comprehensions and filters, records and
/// variants, joins and group-bys, aggregates, unions, a value read twice, commit stores and their
/// writers, and a source read at its keys. Every one compiles; a program that stops compiling
/// fails the test.
fn corpus() -> Vec<Case> {
    let mut cases: Vec<Case> = [
        include_str!("../../../tests/programs/arithmetic/program.cambra"),
        include_str!("../../../tests/programs/defer_generators/program.cambra"),
        include_str!("../../../tests/programs/defer_lift/program.cambra"),
        include_str!("../../../tests/programs/filter_and_aggregate/program.cambra"),
        include_str!("../../../tests/programs/for_accumulator/program.cambra"),
        include_str!("../../../tests/programs/generator_pipeline/program.cambra"),
        include_str!("../../../tests/programs/groupby_filtered_rollup/program.cambra"),
        include_str!("../../../tests/programs/groupby_rollup/program.cambra"),
        include_str!("../../../tests/programs/inner_join/program.cambra"),
        include_str!("../../../tests/programs/join_then_groupby/program.cambra"),
        include_str!("../../../tests/programs/list_comp/program.cambra"),
        include_str!("../../../tests/programs/list_min/program.cambra"),
        include_str!("../../../tests/programs/polymorphic/program.cambra"),
        include_str!("../../../tests/programs/udf_closure/program.cambra"),
    ]
    .into_iter()
    .map(pure)
    .collect();
    cases.extend(
        [
            indoc! {r#"
                xs = [1, 2, 3, 4]
                [a + b for a in xs for b in xs if a < b]
            "#},
            indoc! {r#"
                xs = [1, 2, 3, 4]
                (sum(xs), max(xs), [x * 2 for x in xs if x > 1])
            "#},
            indoc! {r#"
                people = [(name="a", age=3), (name="b", age=5)]
                [(p.name, p.age + 1) for p in people]
            "#},
            indoc! {r#"
                xs = [(a=1, b=[1, 2]), (a=3, b=[4, 5])]
                xs
            "#},
            indoc! {r#"
                m: Mut({`ping{Int} | `close}) := `ping(3)
                n = (match m: case `ping(s): s case `close: 0)
                n
            "#},
            indoc! {r#"
                def g(c: Mut(Int)):
                    c += 100
                    c + 0
                x := 1
                t = (x, g(x))
                t.0 * 1000 + t.1
            "#},
            indoc! {r#"
                pool: Mut(Int, Txn) := 100
                for r in [10, 20, 30]:
                    with begin():
                        pool := pool - r
                await_final(pool)
            "#},
            indoc! {r#"
                a: Mut(Int, Txn) := 5
                b: Mut(Int, Txn) := 0
                for x in [1, 2, 3]:
                    with begin():
                        b := b + a
                        a := a + x
                await_final(a) * 100 + await_final(b)
            "#},
        ]
        .map(pure),
    );
    cases.push(Case {
        code: "[x + 1 for x in source1()]",
        source: true,
        sinks: &[],
    });
    cases
}

/// A context with what `case` registers.
fn context(case: &Case) -> GlobalContext {
    let mut ctx = GlobalContext::default();
    if case.source {
        ctx.register_source(Arc::new(Mutex::new(TestDataSource::new(
            "source1",
            Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        ))));
    }
    for sink in case.sinks {
        ctx.register_test_sink(*sink);
    }
    ctx
}

/// The kinds reached through the owned and shared inputs, and the kinds with inputs the program's
/// graph holds through any edge.
pub(crate) fn survey() -> (BTreeSet<&'static str>, BTreeSet<&'static str>) {
    let (mut reached, mut held) = (BTreeSet::new(), BTreeSet::new());
    for case in corpus() {
        let mut ctx = context(&case);
        let loaded = LoadedProgram::test(case.code);
        let program = compile_program(&mut ctx, &loaded, Box::new(|| {})).unwrap_or_else(|why| {
            panic!(
                "`{}` compiles: {why:?}",
                case.code.lines().next().unwrap_or("")
            )
        });
        let mut seen = HashSet::new();
        for output in &program.outputs {
            kinds_with_inputs(&*output.op, &mut seen, &mut held);
            reached_by_value_edges(&*output.op, &mut reached);
        }
    }
    (reached, held)
}

/// The production kinds that state an input, which the corpus reaches through some edge.
const REACHED: &[&str] = &[
    "Aggregate",
    "Converse",
    "ExtractAggregate",
    "ExtractFinal",
    "FanOutSlot",
    "Filter",
    "MakeRecord",
    "MapAggregate",
    "MapDomain",
    "MapExtractAggregate",
    "MapResult",
    "MapResultToConst",
    "MapResultWithSource",
    "Memo",
    "Restrict",
    "SelectField",
    "StoreFinalRead",
    "Uncurry",
    "UnionOperator",
    "VariantProject",
    "VariantWrap",
    "Zip",
];

/// Production kinds that state an input and that no program of the corpus reaches: a harvest of
/// the programs of `tests/it/compilation_pipeline` that compile on a bare context found none for
/// them, and the commit stores state no input until a writer is wired to them. The test fails
/// when the corpus starts to reach one, so it moves to `REACHED`.
const NOT_REACHED: &[&str] = &[
    "AsOf",
    "CheckedLookup",
    "CommitOperator",
    "FlattenTupleDomain",
    "InductionDriver",
    "PermuteRecordDomain",
    "Product",
    "RecordWrap",
    "StoreDenseRead",
    "StoreValueStream",
    "TransactDriver",
    "TransactWriter",
    "VariantIs",
];

/// The corpus reaches the kinds listed.
#[test]
fn the_corpus_reaches_the_operator_kinds_listed() {
    let (reached_through_values, held) = survey();
    let reached: BTreeSet<&str> = REACHED.iter().copied().collect();
    let missing: Vec<_> = reached.difference(&held).collect();
    assert!(
        missing.is_empty(),
        "the corpus no longer reaches {missing:?}"
    );
    let new: Vec<_> = held
        .iter()
        .filter(|k| !reached.contains(**k) && !NOT_REACHED.contains(*k))
        .collect();
    assert!(
        new.is_empty(),
        "the corpus reaches {new:?}: list it in `REACHED`"
    );
    let moved: Vec<_> = NOT_REACHED.iter().filter(|k| held.contains(*k)).collect();
    assert!(
        moved.is_empty(),
        "the corpus reaches {moved:?}: move it to `REACHED`"
    );
    assert!(
        reached.is_subset(&reached_through_values.iter().copied().collect()),
        "every kind listed is reached through the owned and shared inputs: {reached_through_values:?}"
    );
}
