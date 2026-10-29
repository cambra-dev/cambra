//! Retained pipeline snapshots and folds between adjacent snapshots.
//!
//! `PANES` declares ordered content, phase filters and leak-gate selection.
//! Materialization returns relations, attribution, deaths and leaks; callers
//! decide whether to assert leak freedom. Both the inspector and the optional
//! compile-time gate consume it.
//!
//! See `src/ccl/design/provenance.md`, "Retained snapshots", "Pane materialization"
//! and "Gate and audit coverage".

use std::collections::HashSet;

use crate::ccl::Expr;
use crate::ccl::context::{CompiledProgram, Phase, collect_tree_ids};
use crate::ccl::provenance::{Leak, NodeId, ProvenanceMap, SourceProjection, fold};

impl CompiledProgram {
    /// Fold adjacent snapshots using `PANES` phase filters. The anchor uses the
    /// lowering projection; later folds consume the preceding projection.
    /// Returns leaks without asserting on them. Used by the inspector and the
    /// optional per-compile gate. See `src/ccl/design/provenance.md`,
    /// "Pane materialization".
    #[allow(dead_code)]
    pub(crate) fn materialize_panes(&self) -> MaterializedPanes {
        let ids = self.pane_ids();

        // The anchor precedes phases that mint new expression IDs. Lowering
        // also contains module-check IDs and IDs removed by uniquification.
        let mut projections = Vec::with_capacity(PANES.len());
        projections.push(self.lowering_projection.clone());
        let mut pairs = Vec::with_capacity(PANES.len() - 1);

        // Each pair folds against the projection of the pane before it, so the
        // attributions compose down the pipeline in one pass.
        for i in 1..PANES.len() {
            let spec = &PANES[i];
            let (map, projection, deaths, leaks) = fold(
                &self.provenance_table,
                spec.phases,
                &ids[i - 1],
                &ids[i],
                &projections[i - 1],
            );
            pairs.push(PanePair {
                name: format!("{} → {}", PANES[i - 1].name, spec.name),
                phases: spec.phases,
                map,
                deaths,
                leaks,
                gated: spec.gated,
            });
            projections.push(projection);
        }

        MaterializedPanes { projections, pairs }
    }

    /// Expression snapshots in the order of `PANES`' leading IR entries.
    /// The compile-time count check pins their number; callers depend on the order.
    pub(crate) fn pane_trees(&self) -> [&Expr; IR_PANE_COUNT] {
        [
            &self.pre_inference_ir,
            &self.post_inference_ir,
            &self.post_channelize_ir,
            &self.post_as_of_read_ir,
            &self.post_lambda_elim_ir,
            &self.ast,
        ]
    }

    /// IDs for each declared pane. IR sets include predicate interiors; operator
    /// sets enumerate the graph. The fold requires only these sets, not content.
    pub(crate) fn pane_ids(&self) -> Vec<HashSet<NodeId>> {
        let mut trees = self.pane_trees().into_iter();
        PANES
            .iter()
            .map(|spec| match spec.content {
                PaneKind::Ir => collect_tree_ids(
                    trees
                        .next()
                        .unwrap_or_else(|| unreachable!("one tree per declared IR pane")),
                ),
                PaneKind::Operators => self.operator_graph.ids().collect(),
            })
            .collect()
    }
}

/// What a pane holds.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum PaneKind {
    /// An expression tree.
    Ir,
    /// The dataflow operator graph.
    Operators,
}

/// One retained snapshot and the phases since its predecessor.
/// Adding an IR entry also requires its matching tree in `pane_trees`.
pub(crate) struct PaneSpec {
    /// The pane's name, e.g. `"post-channelize"`.
    pub(crate) name: &'static str,
    /// Content used for ID enumeration and rendering. IR entries must precede
    /// operator entries, as checked by `IR_PANE_COUNT`.
    pub(crate) content: PaneKind,
    /// Selected producing phases for this pair's fold. Filtering must stop at the
    /// input boundary; a phase recorded in the corpus must belong to exactly one
    /// pair (`every_recorded_phase_belongs_to_exactly_one_pane_pair`).
    pub(crate) phases: &'static [Phase],
    /// Whether callers should assert this pair's leaks are empty. Unused on the
    /// anchor. All current pairs are gated; adding an uninstrumented pair can leave
    /// it ungated while recording is completed. False does not redefine leaks as
    /// valid provenance. See `src/ccl/design/provenance.md`, "Gate and audit coverage".
    pub(crate) gated: bool,
}

/// How many panes hold an expression tree.
///
/// [`CompiledProgram::pane_trees`]' arity. The assertion below pins it against
/// [`PANES`], so the trees zip against the [`PaneKind::Ir`] entries in order.
pub(crate) const IR_PANE_COUNT: usize = 6;

/// Ordered snapshot topology. The first entry has no predecessor or selected
/// phases and uses the lowering projection. Each remaining entry defines one
/// pair; all current pairs are selected for leak checking.
pub(crate) const PANES: [PaneSpec; 7] = [
    PaneSpec {
        name: "pre-inference",
        content: PaneKind::Ir,
        phases: &[],
        gated: false,
    },
    PaneSpec {
        name: "post-inference",
        content: PaneKind::Ir,
        phases: &[
            Phase::Anf,
            Phase::MutRead,
            Phase::Comprehension,
            Phase::OpaqueOutput,
            Phase::Infer,
        ],
        gated: true,
    },
    PaneSpec {
        name: "post-channelize",
        content: PaneKind::Ir,
        phases: &[
            Phase::Inline,
            Phase::Transact,
            Phase::Letrec,
            Phase::Channelize,
        ],
        gated: true,
    },
    PaneSpec {
        name: "post-as-of-read",
        content: PaneKind::Ir,
        phases: &[Phase::AsOfRead],
        gated: true,
    },
    PaneSpec {
        name: "post-lambda-elim",
        content: PaneKind::Ir,
        phases: &[Phase::LambdaElim],
        gated: true,
    },
    PaneSpec {
        name: "post-planning",
        content: PaneKind::Ir,
        phases: &[Phase::Planning],
        gated: true,
    },
    PaneSpec {
        name: "post-conversion",
        content: PaneKind::Operators,
        phases: &[Phase::Convert],
        gated: true,
    },
];

/// [`PANES`]' [`PaneKind::Ir`] entries are exactly its leading [`IR_PANE_COUNT`].
///
/// [`CompiledProgram::pane_ids`] zips the trees against them in declaration
/// order, so both the count and the position are load-bearing. Counting is O(1)
/// at compile time, which is what keeps the two declarations from drifting.
const _: () = {
    let mut i = 0;
    while i < PANES.len() {
        assert!(
            matches!(PANES[i].content, PaneKind::Ir) == (i < IR_PANE_COUNT),
            "PANES' `Ir` entries must be exactly its leading `IR_PANE_COUNT` entries",
        );
        i += 1;
    }
};

/// One adjacent pair of panes and everything the fold derives for it.
// Consumed by the inspector model; the compiler reads only `leaks` and `gated`.
#[allow(dead_code)]
pub(crate) struct PanePair {
    /// `"post-inference → post-channelize"`, joined from the two pane names so
    /// it cannot drift from the topology it describes.
    pub(crate) name: String,
    /// The phases that ran between the two panes — [`PaneSpec::phases`].
    pub(crate) phases: &'static [Phase],
    /// The dense bidirectional node↔node relation, a self-edge for every
    /// survivor, each edge carrying its label set.
    pub(crate) map: ProvenanceMap<NodeId, NodeId>,
    /// The input-pane ids absent from the output pane — `input_ids ∖
    /// output_ids`, which is the whole of what "died" means here. A product, not
    /// a defect.
    pub(crate) deaths: Vec<NodeId>,
    /// Integrity defects, every one of them a bug.
    pub(crate) leaks: Vec<Leak>,
    /// Whether [`leaks`](Self::leaks) is asserted empty — [`PaneSpec::gated`].
    pub(crate) gated: bool,
}

/// The per-pane projections and per-pair folds materialized from
/// [`CompiledProgram::provenance_table`] — see
/// [`CompiledProgram::materialize_panes`].
// Used by the inspector and optional per-compile leak checking.
#[allow(dead_code)]
pub(crate) struct MaterializedPanes {
    /// Each pane's projection, in pipeline order, parallel to [`PANES`].
    pub(crate) projections: Vec<SourceProjection>,
    /// The pairs between adjacent panes, in pipeline order — one shorter than
    /// [`projections`](Self::projections).
    pub(crate) pairs: Vec<PanePair>,
}

impl MaterializedPanes {
    /// The projection of the pane named `pane`.
    ///
    /// Panics if no pane carries that name, which is a typo in a caller rather
    /// than a runtime condition: the names are [`PANES`]' compile-time literals.
    #[allow(dead_code)]
    pub(crate) fn projection(&self, pane: &str) -> &SourceProjection {
        let i = PANES
            .iter()
            .position(|p| p.name == pane)
            .unwrap_or_else(|| panic!("no pane named {pane}"));
        &self.projections[i]
    }

    /// The pair whose name is `pair`, e.g. `"post-inference → post-channelize"`.
    ///
    /// Panics if no pair carries that name, for the same reason as
    /// [`projection`](Self::projection).
    #[allow(dead_code)]
    pub(crate) fn pair(&self, pair: &str) -> &PanePair {
        self.pairs
            .iter()
            .find(|p| p.name == pair)
            .unwrap_or_else(|| panic!("no pane pair named {pair}"))
    }

    /// Pairs selected for leak checking by `PaneSpec::gated`.
    /// Selection does not itself assert or filter their leak vectors.
    pub(crate) fn gated_pane_pairs(&self) -> impl Iterator<Item = &PanePair> {
        self.pairs.iter().filter(|p| p.gated)
    }
}

/// Assert that the leak vector is empty in debug or test builds; otherwise return.
/// Both classes are errors. Deaths are a separate fold product and are not passed
/// here. See `src/ccl/design/provenance.md`, "Recording leaks".
pub(crate) fn gate_leaks(leaks: &[Leak], pair: &str) {
    if !cfg!(any(debug_assertions, test)) {
        return;
    }
    assert!(
        leaks.is_empty(),
        "provenance capture defect between the {pair} panes ({} leaks): {leaks:?}",
        leaks.len(),
    );
}

#[cfg(test)]
mod tests {
    use crate::ccl::load::LoadedProgram;
    use std::{collections::HashSet, env::VarError, num::NonZeroUsize};

    use indoc::indoc;

    use super::*;

    use crate::ccl::TypedExprNode;
    use crate::ccl::context::{
        GlobalContext, PERF_REPS_ENV, compile_program, predicate_id_collisions,
        provenance_capture_enabled,
    };
    use crate::ccl::provenance::Link;
    use crate::ccl::test_corpus::pipeline_corpus as corpus;
    use crate::interpreter::Consumer;

    /// Compile `code` through the full pipeline, panicking on error.
    fn compile_ok(code: &str) -> CompiledProgram {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        match compile_program(&mut ctx, &LoadedProgram::test(code), consumer) {
            Ok(p) => p,
            Err(errs) => panic!("expected a successful compile, got {errs:?}"),
        }
    }

    /// Per-leak-class counts, for reporting one fold.
    #[derive(Default, Debug, PartialEq, Eq)]
    struct LeakCounts {
        unrecorded: usize,
        dangling_parent: usize,
    }

    impl LeakCounts {
        fn tally(leaks: &[Leak]) -> Self {
            let mut c = LeakCounts::default();
            for l in leaks {
                match l {
                    Leak::Unrecorded { .. } => c.unrecorded += 1,
                    Leak::DanglingParent { .. } => c.dangling_parent += 1,
                }
            }
            c
        }

        fn add(&mut self, o: &LeakCounts) {
            self.unrecorded += o.unrecorded;
            self.dangling_parent += o.dangling_parent;
        }
    }

    /// Check both leak classes for gated pairs across the pipeline corpus.
    /// This establishes coverage for observed outputs and selected rows, not that
    /// every intermediate mint was recorded or every attribution is precise.
    #[test]
    fn pane_pair_folds_have_no_structural_leaks() {
        let mut totals: std::collections::HashMap<String, LeakCounts> =
            std::collections::HashMap::new();
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            let panes = program.materialize_panes();
            for pair in panes.gated_pane_pairs() {
                let c = LeakCounts::tally(&pair.leaks);
                let pair_name = &pair.name;
                assert_eq!(
                    c.dangling_parent, 0,
                    "{name}: structural leaks between the {pair_name} panes: {c:?}"
                );
                assert_eq!(
                    c.unrecorded, 0,
                    "{name}: unrecorded output nodes between the {pair_name} panes — a rewrite \
                     that mints with nothing recording: {c:?}"
                );
                eprintln!("[pane {name} / {pair_name}] {c:?}");
                totals.entry(pair.name.clone()).or_default().add(&c);
            }
            // Require nonempty products through the contiguous gated prefix.
            let reached = panes.pairs.iter().take_while(|p| p.gated).count();
            for (i, projection) in panes.projections.iter().take(reached + 1).enumerate() {
                assert!(!projection.is_empty(), "{name}: {}", PANES[i].name);
            }
            for pair in panes.pairs.iter().take(reached) {
                assert!(!pair.map.edges().is_empty(), "{name}: {}", pair.name);
            }
        }
        let mut names: Vec<_> = totals.keys().cloned().collect();
        names.sort();
        for pair in names {
            eprintln!("[pane totals] {pair} {:?}", totals[&pair]);
        }
    }

    /// Require every phase recorded by a corpus compile to belong to exactly one
    /// pair. Otherwise its rows are omitted or folded at multiple boundaries.
    #[test]
    fn every_recorded_phase_belongs_to_exactly_one_pane_pair() {
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            for p in program.provenance_table.recorded_phases() {
                let pairs = PANES.iter().filter(|s| s.phases.contains(&p)).count();
                assert_eq!(
                    pairs, 1,
                    "{name}: {p:?} belongs to {pairs} pane pairs, want exactly 1",
                );
            }
        }
    }

    /// Check endpoint membership and survivor self-edges across the corpus.
    /// Each gated pair must also have a non-self edge on at least one program, so
    /// identity-only maps cannot satisfy all checks without exercising recording.
    #[test]
    fn the_pane_folds_derive_a_non_vacuous_provenance_map() {
        let mut exercised: HashSet<usize> = HashSet::new();
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            let panes = program.materialize_panes();
            let ids = program.pane_ids();

            for (i, pane_pair) in panes.pairs.iter().enumerate() {
                if !pane_pair.gated {
                    continue;
                }
                let (pair, map) = (&pane_pair.name, &pane_pair.map);
                let (input_ids, output_ids) = (&ids[i], &ids[i + 1]);
                let edges = map.edges();
                assert!(
                    !edges.is_empty(),
                    "{name}: the {pair} fold derived no edges at all",
                );
                for (u, d) in &edges {
                    assert!(
                        input_ids.contains(u),
                        "{name}: {u:?} is an edge origin at {pair} but not an input-pane id",
                    );
                    assert!(
                        output_ids.contains(&d.id),
                        "{name}: {:?} is an edge target at {pair} but not an output-pane id",
                        d.id,
                    );
                }
                // Surviving corpus IDs must have ancestry self-edges.
                for id in input_ids.intersection(output_ids) {
                    let self_edge = map.upstream(id).iter().find(|l| l.id == *id);
                    assert!(
                        self_edge.is_some_and(|l| l.labels.has_ancestry()),
                        "{name}: {id:?} survives {pair} without an ancestry self-edge",
                    );
                }
                // Identity-only maps do not witness use of a recorded row.
                if edges.iter().any(|(u, d)| *u != d.id) {
                    exercised.insert(i);
                }
            }
        }
        for (i, spec) in PANES.iter().enumerate().skip(1).filter(|(_, s)| s.gated) {
            assert!(
                exercised.contains(&(i - 1)),
                "no corpus program's fold reads a row at {} → {}: either the phases inside the \
                 pair record nothing, or the corpus lost the program that exercised them",
                PANES[i - 1].name,
                spec.name,
            );
        }
    }

    /// The `program / pane pair` names at which a **blame** edge reaches the
    /// provenance map — where a rewrite named blame and the fold labelled the
    /// edge it contributed. See
    /// [`blame_reaches_the_provenance_map_labelled`].
    const RELATING_BOUNDARIES: &[&str] = &[
        "for_accumulator / post-inference → post-channelize",
        "inner_join / post-lambda-elim → post-planning",
        "join_then_groupby / post-lambda-elim → post-planning",
        "transaction / post-inference → post-channelize",
    ];

    /// Pin the corpus boundaries where at least one emitted edge carries blame.
    /// This tests reachability of blame, not absence of ancestry on the same edge;
    /// the mixed-label algebra is tested separately in `provenance.rs`.
    #[test]
    fn blame_reaches_the_provenance_map_labelled() {
        let mut relating: Vec<String> = Vec::new();
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            let panes = program.materialize_panes();
            for pane_pair in panes.gated_pane_pairs() {
                if pane_pair
                    .map
                    .edges()
                    .iter()
                    .any(|(_, d)| d.labels.has_blame())
                {
                    relating.push(format!("{name} / {}", pane_pair.name));
                }
            }
        }
        relating.sort();
        assert_eq!(
            relating, RELATING_BOUNDARIES,
            "the pane pairs at which blame contributes an edge have changed",
        );
    }

    /// A statement's downstream IDs, separated into ancestry and blame relations.
    /// Blame must not satisfy tests that require the statement to have products.
    struct StatementImage {
        kind: &'static str,
        descendants: HashSet<NodeId>,
        blamed: HashSet<NodeId>,
    }

    /// The mutation statements of `program`, in tree order, each with its image.
    /// `expected` is the statements the fixture is meant to have, named by the
    /// marker each holds, so a program that stops exercising the shape fails
    /// here rather than passing vacuously.
    fn statement_images(program: &str, expected: &[&'static str]) -> Vec<StatementImage> {
        let program = compile_ok(program);
        let panes = program.materialize_panes();
        let pair = panes.pair("post-inference → post-channelize");

        // The statements of interest, found by the marker each holds.
        let mut sites: Vec<(&'static str, NodeId)> = Vec::new();
        fn find(e: &Expr, sites: &mut Vec<(&'static str, NodeId)>) {
            if let TypedExprNode::ExprStmt { expr: effect, .. } = &e.node {
                let kind = match &effect.node {
                    TypedExprNode::For { .. } => Some("loop"),
                    TypedExprNode::MutWrite { .. } => Some("write"),
                    TypedExprNode::Feed { .. } => Some("feed"),
                    _ => None,
                };
                if let Some(kind) = kind {
                    sites.push((kind, e.node_id()));
                }
            }
            e.walk_children(|c| find(c, sites));
        }
        find(&program.post_inference_ir, &mut sites);
        assert_eq!(
            sites.iter().map(|(k, _)| *k).collect::<Vec<_>>(),
            expected,
            "the fixture no longer has the statements the test is about",
        );

        sites
            .iter()
            .map(|(kind, id)| {
                let links = pair.map.downstream(id);
                let of = |f: fn(&Link<NodeId>) -> bool| -> HashSet<NodeId> {
                    links
                        .iter()
                        .filter(|l| l.id != *id && f(l))
                        .map(|l| l.id)
                        .collect()
                };
                StatementImage {
                    kind,
                    descendants: of(|l| l.labels.has_ancestry()),
                    blamed: of(|l| !l.labels.has_ancestry() && l.labels.has_blame()),
                }
            })
            .collect()
    }

    /// No two statements produced the same node.
    fn assert_disjoint(images: &[StatementImage]) {
        for (i, a) in images.iter().enumerate() {
            for b in &images[i + 1..] {
                let shared: Vec<NodeId> = a
                    .descendants
                    .intersection(&b.descendants)
                    .copied()
                    .collect();
                assert!(
                    shared.is_empty(),
                    "the {} and {} statements both claim {shared:?}",
                    a.kind,
                    b.kind,
                );
            }
        }
    }

    /// **A loop-body statement reaches its own products, not the loop's.**
    /// `mut_elim` turns one `For` statement into a recurrence carrying a slot
    /// per accumulator and a tap per feed. One recording on the loop statement
    /// claims all of it, which leaves every write and every feed in the body
    /// with no descendants: the inspector then has nothing to answer with for
    /// the lines that do the mutating. The nested `letrec.accumulator` and
    /// `letrec.feed` recordings are what split it.
    ///
    /// Disjointness is the other half of the claim. A product belongs to one of
    /// the three statements, so a recording that widened instead of splitting —
    /// blaming the body statements on the loop's own recording — passes the
    /// non-emptiness check and fails here.
    #[test]
    fn a_loop_body_statement_reaches_its_own_products() {
        let images = statement_images(
            indoc! {"
                out: Feed(_)
                total := 0
                for n in [1, 2, 3]:
                    total := total + n
                    out << total
                max(out)
            "},
            &["loop", "write", "feed"],
        );
        for image in &images {
            assert!(
                !image.descendants.is_empty(),
                "the {} statement reaches nothing in `post-channelize`",
                image.kind,
            );
        }
        assert_disjoint(&images);
    }

    /// **Two accumulators resolve to two write statements.** One recurrence
    /// carries a slot per accumulator, and the slots differ only by the index
    /// they project — so a recording that named the loop, or that named the
    /// first write for both slots, produces exactly the same tree and is
    /// visible only here.
    #[test]
    fn each_accumulator_reaches_the_statement_that_writes_it() {
        let images = statement_images(
            indoc! {"
                out: Feed(_)
                total := 0
                count := 0
                for n in [1, 2, 3]:
                    total := total + n
                    count := count + 1
                    out << total
                max(out) + count
            "},
            &["loop", "write", "write", "feed"],
        );
        for image in &images {
            assert!(
                !image.descendants.is_empty(),
                "the {} statement reaches nothing in `post-channelize`",
                image.kind,
            );
        }
        assert_disjoint(&images);
    }

    /// **A feed reaches its own products whether or not the loop accumulates,
    /// and the loop it sits in is blamed for them.** An accumulator-free loop
    /// takes the plain-map path (`mut_elim::transform_feed_only_loop`), which
    /// mints one mapped source per feed instead of a recurrence. Every product
    /// there belongs to a feed — the loop mints nothing beyond them, and with
    /// two feeds it mints two maps — so the split is the whole expansion moving
    /// to the feed statements, not a slice of it.
    ///
    /// That leaves the `for` line answering with nothing of its own, which is
    /// why the map blames it: the iteration is what the map is about, and blame
    /// is how a site widens attribution to a node it did not produce. The
    /// asymmetry with the accumulator path — where the loop keeps its history
    /// binder and its guard — is the point being pinned, so the loop's empty
    /// descent is asserted rather than tolerated.
    ///
    /// The read-only `with begin():` block is what reaches that path: a
    /// non-transactional `for n in xs: out << n` is already a `Compose` by
    /// `post-inference`, lowered without ever reaching `mut_elim`.
    #[test]
    fn a_feed_in_an_accumulator_free_loop_reaches_its_own_products() {
        let images = statement_images(
            indoc! {"
                out: Feed(_)
                pool: Mut(Int, Txn) := 100
                for r in [10, 20, 30]:
                    with begin():
                        out << pool
                max(out)
            "},
            &["loop", "feed"],
        );
        let [loop_stmt, feed] = &images[..] else {
            unreachable!("two statements, asserted above")
        };
        assert!(
            !feed.descendants.is_empty(),
            "the feed statement reaches nothing in `post-channelize`",
        );
        assert!(
            loop_stmt.descendants.is_empty(),
            "the loop statement produced {:?} of its own, so the products no \
             longer all belong to the feed",
            loop_stmt.descendants,
        );
        assert!(
            feed.descendants.is_subset(&loop_stmt.blamed),
            "the loop is not blamed for the feed's products: blamed {:?}, feed produced {:?}",
            loop_stmt.blamed,
            feed.descendants,
        );
        assert_disjoint(&images);
    }

    /// Compare flat and nested joins: planning.hash_join must contribute blame
    /// from one and two distinct predicate IDs respectively.
    #[test]
    fn a_nested_join_blames_both_join_conditions() {
        let flat = "[x + y for x in [2] for y in [1, 2, 3] if x == y]";
        let nested = "[x + y for x in [2] \
                      for y in [a + b for a in [1, 2] for b in [1, 2, 3] if a == b] if x == y]";
        for (name, code, want) in [("flat", flat, 1), ("nested", nested, 2)] {
            let program = compile_ok(code);
            let panes = program.materialize_panes();
            let pair = panes
                .pairs
                .iter()
                .find(|p| p.name == "post-lambda-elim → post-planning")
                .expect("the planning pane pair");
            let blamed: HashSet<NodeId> = pair
                .map
                .edges()
                .into_iter()
                .filter(|(u, d)| {
                    *u != d.id
                        && d.labels.has_blame()
                        && program
                            .provenance_table
                            .tag(d.id)
                            .is_some_and(|t| t.label == "planning.hash_join")
                })
                .map(|(u, _)| u)
                .collect();
            assert_eq!(
                blamed.len(),
                want,
                "{name}: distinct predicates blamed by planning.hash_join",
            );
        }
    }

    /// Corpus fixtures selected to exercise generalized-definition specialization.
    const SPECIALIZING: &[&str] = &["generator_pipeline", "udf_chain"];

    /// Require no structural leaks across the first pair and nonempty deaths on
    /// specializing fixtures. The pair includes normalization and other producers;
    /// this test does not isolate monomorphization's rows.
    #[test]
    fn monomorphization_explains_every_node_it_produces() {
        for (name, code) in corpus() {
            let panes = compile_ok(&code).materialize_panes();
            let pair = panes.pair("pre-inference → post-inference");
            let c = LeakCounts::tally(&pair.leaks);
            assert_eq!(c.dangling_parent, 0, "{name}: {c:?}");
            assert_eq!(
                c.unrecorded, 0,
                "{name}: pre-inference → post-inference is uncaptured: {c:?}"
            );
            if SPECIALIZING.contains(&name) {
                assert!(
                    !pair.deaths.is_empty(),
                    "{name}: specializes, so the generalized definition must die"
                );
            }
        }
    }

    /// Require no structural leaks across the Inline/Transact/Letrec/Channelize pair.
    /// Selected rewriting fixtures must also have deaths, preventing an unchanged
    /// tree from satisfying every assertion.
    #[test]
    fn the_second_pane_pair_explains_every_node_its_phases_produce() {
        /// Reaches `transact_phase` or `channelize` — the whole-program
        /// rewrites, where naming one node is least obviously applicable.
        const WHOLE_PROGRAM_REWRITES: &[&str] = &["transaction", "feed_loop", "generator_pipeline"];
        for (name, code) in corpus() {
            let panes = compile_ok(&code).materialize_panes();
            let pair = panes.pair("post-inference → post-channelize");
            let c = LeakCounts::tally(&pair.leaks);
            assert_eq!(c.dangling_parent, 0, "{name}: {c:?}");
            assert_eq!(
                c.unrecorded, 0,
                "{name}: post-inference → post-channelize is uncaptured: {c:?}"
            );
            if WHOLE_PROGRAM_REWRITES.contains(&name) {
                assert!(
                    !pair.deaths.is_empty(),
                    "{name}: rewrites its whole shape, so nodes must die"
                );
            }
        }
    }

    /// Deaths are the live-set difference and nothing else: what the fold reports
    /// between two panes is exactly `input_ids ∖ output_ids` on a real program,
    /// with no phase having declared any of them. `for_accumulator` folds a
    /// mutation loop into a `LetRec`, so the difference is non-empty.
    #[test]
    fn deaths_between_two_panes_are_the_set_difference() {
        let program = compile_ok(include_str!(
            "../../tests/programs/for_accumulator/program.cambra"
        ));
        let panes = program.materialize_panes();
        let input = collect_tree_ids(&program.post_inference_ir);
        let output = collect_tree_ids(&program.post_channelize_ir);
        let mut expected: Vec<NodeId> = input.difference(&output).copied().collect();
        expected.sort_unstable();
        assert!(!expected.is_empty(), "the fixture must actually kill nodes");
        assert_eq!(
            panes.pair("post-inference → post-channelize").deaths,
            expected
        );
    }

    /// Check distinct-predicate and predicate/main-tree ID collisions on the three
    /// explicitly listed snapshots. Shared occurrences of one predicate Rc are valid.
    /// The traversal's limits are specified in `src/ccl/design/provenance.md`,
    /// "Walking the ids".
    #[test]
    fn distinct_predicate_terms_never_share_a_node_id() {
        let mut found: Vec<(String, usize, &'static str)> = Vec::new();
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            for (pane, tree) in [
                ("pre-inference", &program.pre_inference_ir),
                ("post-inference", &program.post_inference_ir),
                ("post-channelize", &program.post_channelize_ir),
            ] {
                for (_, kind) in predicate_id_collisions(tree) {
                    found.push((format!("{name} / {pane}"), 1, kind));
                }
            }
        }
        assert!(
            found.is_empty(),
            "{} predicate id collisions: {found:?}",
            found.len(),
        );
    }

    /// Pin the recorded phase set for the transaction fixture, sorted by phase name.
    /// A phase can run without recording a product; its absence from this set does
    /// not establish that the phase was skipped.
    #[test]
    fn a_rewriting_phase_tags_its_rows_with_itself() {
        let (_, code) = corpus()
            .into_iter()
            .find(|(name, _)| *name == "transaction")
            .expect("the transaction fixture");
        let program = compile_ok(&code);
        let mut recorded = program.provenance_table.recorded_phases();
        recorded.sort_by_key(|p| format!("{p:?}"));
        assert_eq!(
            recorded,
            vec![
                Phase::Anf,
                Phase::AsOfRead,
                Phase::Channelize,
                Phase::Convert,
                Phase::Infer,
                Phase::Inline,
                Phase::LambdaElim,
                Phase::Letrec,
                Phase::Planning,
                Phase::Transact
            ],
            "the transaction fixture is rewritten by exactly these phases",
        );
    }

    // -----------------------------------------------------------------------
    // Perf sanity for pane capture
    // -----------------------------------------------------------------------

    /// One generated program shape, parameterized by size.
    ///
    /// The shapes are chosen to hit the phases the panes span: `comprehension`
    /// and `arith` are `inline`-light and mostly id-preserving, `udf` drives
    /// inlining and monomorphization, `loop_acc` drives `mut_elim`, and `feed`
    /// drives `channelize`.
    ///
    /// Sizes are deliberately small. Compile time here is **superlinear in
    /// program size** for reasons that predate provenance capture (a UDF-heavy 63-line
    /// program compiles in tens of seconds), so a corpus large enough to be a
    /// benchmark would be too slow to run; this is a sanity check on the
    /// *ratio* between capture on and capture off, not a benchmark.
    fn generated(shape: &str, n: usize) -> String {
        match shape {
            "arith" => {
                let terms: Vec<String> = (1..=n).map(|i| format!("{i} * {}", i + 1)).collect();
                format!("x = {}\nx\n", terms.join(" + "))
            }
            "comprehension" => {
                // Independent comprehensions summed, rather than a chain: a
                // chained comprehension trips an unrelated substitution bug
                // ("discharged binder still free after substitution into
                // predicate") that has nothing to do with provenance.
                let parts: Vec<String> = (0..n)
                    .map(|i| format!("sum([y + {i} for y in xs if y > 0])"))
                    .collect();
                format!("xs = [1, 2, 3, 4, 5]\nt = {}\nt\n", parts.join(" + "))
            }
            "udf" => {
                let mut src = String::new();
                for i in 0..n {
                    src.push_str(&format!("def f{i}(x):\n    x + {i}\n"));
                }
                src.push_str("xs = [1, 2, 3, 4, 5]\n");
                let calls: Vec<String> = (0..n).map(|i| format!("f{i}(y)")).collect();
                src.push_str(&format!("[{} for y in xs]\n", calls.join(" + ")));
                src
            }
            "loop_acc" => {
                let mut src = String::from("xs = [1, 2, 3, 4, 5]\n");
                for i in 0..n {
                    src.push_str(&format!("a{i}: Mut(Int) := 0\n"));
                }
                src.push_str("for v in xs:\n");
                for i in 0..n {
                    src.push_str(&format!("    a{i} += v + {i}\n"));
                }
                src.push_str(&format!("a{}\n", n - 1));
                src
            }
            "feed" => {
                let mut src = String::from("out: Feed(_)\nxs = [1, 2, 3, 4, 5]\n");
                for i in 0..n {
                    src.push_str(&format!("for v in xs:\n    out << v + {i}\n"));
                }
                src.push_str("out\n");
                src
            }
            other => panic!("unknown shape {other}"),
        }
    }

    /// The perf corpus: `(shape, size)` pairs, sized to keep the whole run in
    /// the low seconds per repetition.
    const PERF_CORPUS: &[(&str, usize)] = &[
        ("arith", 40),
        ("arith", 80),
        ("arith", 160),
        ("comprehension", 6),
        ("comprehension", 12),
        ("comprehension", 20),
        ("udf", 5),
        ("udf", 8),
        ("udf", 12),
        ("loop_acc", 4),
        ("loop_acc", 8),
        ("loop_acc", 14),
        ("feed", 3),
        ("feed", 6),
        ("feed", 12),
    ];

    /// Each `Transact` writer's own ids — its source and its body — paired with a
    /// description for the failure message.
    fn collect_writer_domains(expr: &Expr, out: &mut Vec<(HashSet<NodeId>, String)>) {
        if let TypedExprNode::Transact { writers, .. } = &expr.node {
            for (i, w) in writers.iter().enumerate() {
                let mut ids = collect_tree_ids(&w.source);
                ids.extend(collect_tree_ids(&w.body));
                out.push((ids, format!("writer {i}")));
            }
        }
        for child in expr.child_exprs() {
            collect_writer_domains(child, out);
        }
    }

    /// **A source's anchors are the iterations over its domain.**
    ///
    /// `source_accumulator` iterates stdin once, in the chain that reads its
    /// values: the read after the loop is a `StoreFinalRead`, which takes no
    /// trigger of its own. That iteration is an `IterateExtent` whose tiling
    /// names stdin, and `source_nodes` answers it, so per-source state attached
    /// through it shows there.
    #[test]
    fn a_source_is_anchored_at_every_iteration_over_its_domain() {
        use crate::interpreter::operator_graph::{GraphNode, source_nodes};

        let program = compile_ok(include_str!(
            "../../tests/programs/source_accumulator/program.cambra"
        ));
        let graph = &program.operator_graph;
        let anchors = source_nodes(graph);
        let stdin = anchors.get("stdin").expect("the program iterates stdin");
        assert_eq!(stdin.len(), 1, "one iteration over stdin: {stdin:?}");
        for id in stdin {
            let kind = graph.nodes().iter().find_map(|n| match n {
                GraphNode::Operator { id: node, kind, .. } if node == id => Some(*kind),
                _ => None,
            });
            assert_eq!(kind, Some("IterateExtent"), "anchor {id:?}");
        }
    }

    /// **The graph has its output boundary**: a sink per compiled output.
    ///
    /// Without it the graph ends in the middle of nothing, and a reader has no way
    /// to tell an output from an operator whose consumer the capture missed. A
    /// sink is a pane node like any other, so it carries a provenance row and
    /// resolves to a span.
    #[test]
    fn the_operator_graph_carries_its_output_boundary() {
        use crate::interpreter::operator_graph::GraphNode;

        for (name, code) in corpus() {
            let program = compile_ok(&code);
            let graph = &program.operator_graph;
            let sinks: Vec<&str> = graph
                .nodes()
                .iter()
                .filter_map(|n| match n {
                    GraphNode::Sink { name, .. } => Some(name.as_str()),
                    _ => None,
                })
                .collect();
            assert!(
                !sinks.is_empty(),
                "{name}: the graph has no sink, so it has no output boundary",
            );

            let projection = program.materialize_panes();
            let attribution = projection
                .projections
                .last()
                .expect("the operator pane's projection");
            for node in graph.nodes() {
                let GraphNode::Sink { id, name: sink, .. } = node else {
                    continue;
                };
                assert!(
                    attribution.contains_key(id),
                    "{name}: sink {sink} carries no attribution, so it resolves to no span",
                );
            }
        }
    }

    /// Whether the subscription relation is acyclic, optionally with the edges
    /// wired through a `CycleSlot` removed. Kahn over the whole graph.
    fn subscription_relation_is_acyclic(
        graph: &crate::interpreter::operator_graph::OperatorGraph,
        without_deferred: bool,
    ) -> bool {
        use crate::interpreter::operator_graph::EdgeKind;
        use std::collections::HashMap;

        let mut indegree: HashMap<NodeId, usize> = graph.ids().map(|id| (id, 0usize)).collect();
        let mut forward: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
        for (consumer, edge) in graph.edges() {
            if without_deferred && matches!(edge.kind, EdgeKind::Value { deferred: true }) {
                continue;
            }
            *indegree.entry(edge.subscribed).or_default() += 1;
            forward.entry(consumer).or_default().push(edge.subscribed);
        }
        let mut ready: Vec<NodeId> = indegree
            .iter()
            .filter(|(_, d)| **d == 0)
            .map(|(id, _)| *id)
            .collect();
        let mut settled = 0usize;
        while let Some(id) = ready.pop() {
            settled += 1;
            for next in forward.get(&id).into_iter().flatten() {
                let Some(d) = indegree.get_mut(next) else {
                    continue;
                };
                *d -= 1;
                if *d == 0 {
                    ready.push(*next);
                }
            }
        }
        settled == indegree.len()
    }

    /// **Every cycle in the operator graph runs through a deferred edge.**
    ///
    /// A `CycleSlot` is the only way an operator subscribes something built after
    /// it — every other input is handed to a constructor, so it names an operator
    /// that already exists — and a slot-held input is the only one stated
    /// deferred. So the deferred edges are the set whose removal leaves the
    /// relation acyclic, which is the set a layered layout withholds from ranking
    /// and draws back as returns.
    ///
    /// A few programs rather than every compile: this is a property of the shapes
    /// the corpus reaches, and `assert_graph_invariants` should not carry a graph
    /// walk on the compile path to restate it.
    ///
    /// Non-vacuous because the store programs are asserted cyclic first — without
    /// that, "acyclic once the deferred edges are gone" would hold of any acyclic
    /// graph.
    #[test]
    fn every_operator_graph_cycle_runs_through_a_deferred_edge() {
        use crate::interpreter::operator_graph::EdgeKind;

        let mut cyclic_programs = 0usize;
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            let graph = &program.operator_graph;
            let deferred = graph
                .edges()
                .filter(|(_, e)| matches!(e.kind, EdgeKind::Value { deferred: true }))
                .count();

            if !subscription_relation_is_acyclic(graph, false) {
                cyclic_programs += 1;
                assert!(
                    deferred > 0,
                    "{name}: the graph has a cycle and no deferred edge, so a construct closed a \
                     cycle without a `CycleSlot` and the cycle set no longer names it",
                );
            }
            assert!(
                subscription_relation_is_acyclic(graph, true),
                "{name}: a cycle survives with the {deferred} deferred edge(s) removed, so the \
                 deferred edges are not the cycle set a layout can cut",
            );
        }
        assert!(
            cyclic_programs > 0,
            "no corpus program builds a cyclic operator graph, so this check is vacuous",
        );
    }

    /// **Each writer of a transaction names some operator of its own.**
    ///
    /// Every operator of the commit complex is minted after the writer's own
    /// subexpressions have been converted and closed their recordings, so
    /// without a scope per writer they all attribute to the `let __hist =
    /// Transact{…}` binding and the pane's whole transaction region resolves to
    /// one span. No leak class can see that: the rows are present and the
    /// parents are live, only coarse.
    ///
    /// A tripwire for that collapse rather than a measure of attribution
    /// quality — it would pass on a partial collapse where one writer swallowed
    /// another's operators. It asserts nothing about *how many* operators a
    /// writer compiles into, which is what keeps it stable across changes to the
    /// complex.
    #[test]
    fn every_writer_site_has_an_operator_attributed_inside_it() {
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            let mut writers: Vec<(HashSet<NodeId>, String)> = Vec::new();
            collect_writer_domains(&program.ast, &mut writers);
            if writers.is_empty() {
                continue;
            }
            let panes = program.materialize_panes();
            let pair = panes
                .pairs
                .last()
                .expect("the operator pane pair is the last one");
            for (ids, what) in &writers {
                let attributed = ids.iter().any(|id| !pair.map.downstream(id).is_empty());
                assert!(
                    attributed,
                    "{name}: no operator attributes to anything inside {what}, so the whole \
                     transaction resolves to its binding — `build_commit_store` needs its \
                     per-writer recording",
                );
            }
        }
    }

    /// Every conditional-induction shape reaches every pane pair clean.
    ///
    /// The leak gates and `assert_unique_node_ids` at a pane boundary run only
    /// under [`CompiledProgram::materialize_panes`], so the compilation-pipeline
    /// suite — which compiles but never materializes — cannot see a leak in a
    /// rewrite it otherwise exercises heavily. The statement-`Case` arm of the
    /// letrec phase is exactly that blind spot: it fans the post-`Case` remainder
    /// and the entering read-your-writes env across every branch, so each shape
    /// below stresses a different copy/consume pairing.
    #[test]
    fn conditional_induction_panes_are_leak_free() {
        for (name, code) in [
            // One conditional write: guard preserved into its own arm predicate,
            // echoed (freshened) into the carry arm's.
            (
                "guard_only",
                "x := 0\nfor i in [1, 2, 3]:\n    if i > 1:\n        x := x + i\nx\n",
            ),
            // Unconditional write *before* the `Case`: its inlined value sits in
            // the read-your-writes env slot every branch clones.
            (
                "uncond_before",
                "x := 0\nfor i in [1, 2, 3]:\n    x := x + 1\n    if i > 1:\n        x := x + 10\nx\n",
            ),
            // Unconditional write *after* the `Case`: the remainder is spliced
            // onto every path, including the trailing carry arm.
            (
                "uncond_after",
                "x := 0\nfor i in [1, 2, 3]:\n    if i > 1:\n        x := x + 10\n    x := x + 1\nx\n",
            ),
            // `if`/`else` writing one accumulator on both arms.
            (
                "if_else",
                "t := 0\nfor x in [1, 2, 3]:\n    if x > 2:\n        t := t + x\n    else:\n        t := t + 1\nt\n",
            ),
            // Two accumulators, one unconditional and one conditional — the
            // shape where a branch's write set matches the carry for *some*
            // accumulator but not all.
            (
                "two_accumulators",
                "cnt := 0\ntotal := 0\nfor i in [1, 2, 3]:\n    cnt := cnt + 1\n    if i > 1:\n        total := total + i\ncnt * 10 + total\n",
            ),
            // Sibling `if`s (not `elif`) on one accumulator: two guard-Cases in
            // one body, so the second one's remainder is itself a spliced copy.
            (
                "sibling_ifs",
                "a := 0\nfor i in [1, 2, 3]:\n    if i > 1:\n        a := a + i\n    if i < 3:\n        a := a + 100\na\n",
            ),
        ] {
            let compiled = compile_ok(code);
            let panes = compiled.materialize_panes();
            for pair in panes.gated_pane_pairs() {
                assert!(
                    pair.leaks.is_empty(),
                    "`{name}`: leaks between the {} panes: {:?}",
                    pair.name,
                    pair.leaks
                );
            }
        }
    }

    fn perf_repetitions(value: Result<String, VarError>) -> NonZeroUsize {
        match value {
            Err(VarError::NotPresent) => NonZeroUsize::new(3).unwrap(),
            Ok(value) => value.parse().unwrap_or_else(|_| {
                panic!("{PERF_REPS_ENV} must be a positive integer, got {value:?}")
            }),
            Err(VarError::NotUnicode(value)) => {
                panic!("{PERF_REPS_ENV} must be a positive integer, got {value:?}")
            }
        }
    }

    #[test]
    fn pane_perf_repetitions_default_only_when_absent() {
        assert_eq!(perf_repetitions(Err(VarError::NotPresent)).get(), 3);
        for reps in [1, 9, usize::MAX] {
            assert_eq!(perf_repetitions(Ok(reps.to_string())).get(), reps);
        }
    }

    #[test]
    fn pane_perf_repetitions_reject_invalid_values() {
        for value in ["0", "", "abc", "-1", "1.5", "184467440737095516160"] {
            let err = std::panic::catch_unwind(|| perf_repetitions(Ok(value.to_string())))
                .expect_err("invalid repetition count must fail");
            let message = err.downcast_ref::<String>().expect("formatted panic");
            assert!(message.contains("CAMBRA_PERF_REPS must be a positive integer"));
        }
        let err = std::panic::catch_unwind(|| {
            perf_repetitions(Err(VarError::NotUnicode(std::ffi::OsString::from(
                "invalid",
            ))))
        })
        .expect_err("non-Unicode repetition count must fail");
        let message = err.downcast_ref::<String>().expect("formatted panic");
        assert!(message.contains("CAMBRA_PERF_REPS must be a positive integer"));
    }

    /// Rough compile-time and retained-memory sanity for pane capture. Ignored
    /// by default — it is a measurement, not an assertion.
    ///
    /// Run it as two interleaved processes so the two arms see the same machine
    /// state, and take the min over repetitions:
    ///
    /// ```text
    /// for i in 1 2 3; do
    ///   CAMBRA_PROVENANCE=1 cargo test --release --lib provenance_pane_perf -- --ignored --nocapture
    ///   CAMBRA_PROVENANCE=0 cargo test --release --lib provenance_pane_perf -- --ignored --nocapture
    /// done
    /// ```
    ///
    /// With capture on it also materializes and folds the panes, since that is
    /// the cost the design actually incurs.
    #[test]
    #[ignore = "measurement, not an assertion; see the doc comment for the driver"]
    fn provenance_pane_perf() {
        let capture = provenance_capture_enabled();
        let reps = perf_repetitions(std::env::var(PERF_REPS_ENV));
        let mut total_compile = std::time::Duration::ZERO;
        let mut total_fold = std::time::Duration::ZERO;
        for (shape, n) in PERF_CORPUS {
            let code = generated(shape, *n);
            let mut best_compile = std::time::Duration::MAX;
            let mut best_fold = std::time::Duration::MAX;
            let mut rows = 0usize;
            let mut tags = 0usize;
            // The retained pane snapshots — every tree, and the operator graph —
            // are not part of what the capture switch turns off, so their size
            // is the pane design's real memory floor, against which the logs are
            // noise.
            let mut panes_nodes = 0usize;
            for _ in 0..reps.get() {
                let t0 = std::time::Instant::now();
                let program = compile_ok(&code);
                best_compile = best_compile.min(t0.elapsed());
                rows = program.provenance_table.len();
                tags = program.provenance_table.tag_count();
                panes_nodes = collect_tree_ids(&program.pre_inference_ir).len()
                    + collect_tree_ids(&program.post_inference_ir).len()
                    + collect_tree_ids(&program.post_channelize_ir).len();
                if capture {
                    let t1 = std::time::Instant::now();
                    let panes = program.materialize_panes();
                    std::hint::black_box(panes.projection("post-channelize"));
                    best_fold = best_fold.min(t1.elapsed());
                }
            }
            if !capture {
                best_fold = std::time::Duration::ZERO;
            }
            total_compile += best_compile;
            total_fold += best_fold;
            eprintln!(
                "[perf capture={capture}] {shape}/{n}: compile {:?} fold {:?} rows {rows} \
                 tags {tags} pane_nodes {panes_nodes} lines {}",
                best_compile,
                best_fold,
                code.lines().count(),
            );
        }
        eprintln!("[perf capture={capture}] TOTAL compile {total_compile:?} fold {total_fold:?}");
    }

    /// **Planning's two recognizers carry the `Nature` they were assigned.**
    /// Both replace a term-tree site that images a source construct, and they
    /// answer the `Expansion`/`Machinery` question differently: a bucketize
    /// chain is what `groupby` denotes, while a hash join is one way of
    /// materialising a comprehension the user never wrote as a join. The tag
    /// rides the wire, so a consumer reads the difference as meaningful and a
    /// silent flip is a change to what the inspector claims about the source.
    /// See `design/provenance.md`, "Choosing between `Expansion` and
    /// `Machinery`".
    ///
    /// Asserting both labels are *present* is the second half: this fixture
    /// exists to put both recognizers on one tree, and a program that stopped
    /// reaching one would otherwise pass the nature check vacuously.
    #[test]
    fn planning_labels_carry_their_declared_nature() {
        use crate::ccl::provenance::{Nature, RewriteLabel};

        let program = compile_ok(include_str!(
            "../../tests/programs/join_then_groupby/program.cambra"
        ));
        let mut seen: std::collections::BTreeMap<RewriteLabel, Nature> = Default::default();
        for id in collect_tree_ids(&program.ast) {
            let Some(tag) = program.provenance_table.tag_in(id, &[Phase::Planning]) else {
                continue;
            };
            // One label, one nature: a recording carries both for its whole
            // extent, so two natures under one label means two sites disagree.
            if let Some(prev) = seen.insert(tag.label, tag.nature) {
                assert_eq!(
                    prev, tag.nature,
                    "label {} is recorded at two different natures",
                    tag.label,
                );
            }
        }
        assert_eq!(
            seen.get("planning.groupby"),
            Some(&Nature::Expansion),
            "the bucketize chain is what `groupby` denotes, so its rewrite expands \
             a source construct; labels seen: {:?}",
            seen,
        );
        assert_eq!(
            seen.get("planning.hash_join"),
            Some(&Nature::Machinery),
            "a hash join is a materialization strategy for a comprehension, not \
             something the source names; labels seen: {:?}",
            seen,
        );
    }

    /// **One `Phase::Planning` scope covers both halves of planning.**
    /// `compile_program` runs `plan_loops` and `planning::run` inside a single
    /// scope. A regression that scoped `run` alone leaves `plan_loops`'
    /// recognition rewrites writing into no table; the leak gate catches that as
    /// a count of unexplained nodes, and this names which half stopped
    /// recording.
    ///
    /// The two halves are told apart by label: `planning.recognize` is
    /// `plan_loops` turning a causal `LetRec` into a `Transact`, and
    /// `planning.iterate` is `run` wrapping an iteration site.
    #[test]
    fn one_planning_scope_covers_recognition_and_iteration() {
        let (_, code) = corpus()
            .into_iter()
            .find(|(name, _)| *name == "transaction")
            .expect("the corpus carries the transaction fixture");
        let program = compile_ok(&code);
        let labels: std::collections::BTreeSet<_> = collect_tree_ids(&program.ast)
            .into_iter()
            .filter_map(|id| program.provenance_table.tag_in(id, &[Phase::Planning]))
            .map(|tag| tag.label)
            .collect();
        for expected in ["planning.recognize", "planning.iterate"] {
            assert!(
                labels.contains(expected),
                "no `{expected}` row survives into the post-planning pane; labels seen: {labels:?}",
            );
        }
    }
}
