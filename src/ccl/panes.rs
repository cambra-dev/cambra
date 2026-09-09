//! The pipeline's **panes** — its retained snapshots — and what a fold between
//! two adjacent ones produces.
//!
//! A pane is one snapshot taken at a named point in
//! [`compile_program`](crate::ccl::context::compile_program): an expression tree
//! through `post-planning`, and the operator graph at `post-conversion`.
//! [`PANES`] declares the topology once: every pane, the phases that produced
//! it from the pane before it, and whether its pair is gated.
//!
//! Split out of [`context`](crate::ccl::context) because it is the inspector's
//! half of the seam. `context` owns the pipeline and the [`Phase`] axis; this
//! module owns what a pane pair is and what folding one yields. Only
//! [`gate_leaks`] is asserted, and `compile_program` calls it under
//! `CAMBRA_PROVENANCE_GATE` alone; the snapshots themselves are retained
//! whatever the capture switch says. The inherent `impl
//! CompiledProgram` below lives here rather than beside the struct for the same
//! reason: the methods are the pane layer's, not the pipeline's. See
//! `design/provenance.md`, "The seam".

use std::collections::HashSet;

use crate::ccl::Expr;
use crate::ccl::context::{CompiledProgram, Phase, collect_tree_ids};
use crate::ccl::provenance::{Leak, NodeId, ProvenanceMap, SourceProjection, fold};

impl CompiledProgram {
    /// Fold [`provenance_table`](Self::provenance_table) across every adjacent
    /// pane pair into the per-pane [`SourceProjection`]s, the pair
    /// [`ProvenanceMap`]s, and each pair's [`Leak`]s. Cold path (snapshot-serve
    /// only), never called by [`compile_program`].
    ///
    /// [`PANES`] is the topology: the anchor pane's projection is the lowering
    /// projection, and each pane after it folds its own phases against the pane
    /// before it. There is no catch-all pair — a node is explained by a recorded
    /// row or it is not explained at all, and the gate is what says which.
    ///
    /// The leaks are **returned, not asserted**: a span reaches zero only once
    /// every phase inside it records its rewrites, so [`gate_leaks`] is left to
    /// the callers that fold an instrumented span. The deaths ride alongside them
    /// as a product, since nothing declares a fate.
    // Cold path: the inspector's snapshot serve, which is not in this workspace.
    #[allow(dead_code)]
    pub(crate) fn materialize_panes(&self) -> MaterializedPanes {
        let ids = self.pane_ids();

        // The anchor pane's projection is the lowering projection: `uniquify`
        // preserves every id in place, so lowering's keys are still its keys.
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

    /// The retained pane trees, in pipeline order, element for element with
    /// [`PANES`]' leading [`PaneKind::Ir`] entries. [`IR_PANE_COUNT`] is pinned
    /// against [`PANES`], so the two cannot disagree about how many there are.
    ///
    /// The inspector model reads this alongside [`PANES`] to build one snapshot
    /// pane per entry.
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

    /// Each pane's id set, in pipeline order, element for element with
    /// [`PANES`].
    ///
    /// This is all the fold wants from a pane — it never reads content — which
    /// is what lets a pane hold an operator graph rather than a tree.
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

/// One pane — one retained snapshot of the pipeline — and the phases that
/// produced it from the pane before it.
///
/// [`PANES`] declares the whole topology in one place, so adding a pane is one
/// entry there, plus its tree in [`CompiledProgram::pane_trees`] when it holds
/// one.
pub(crate) struct PaneSpec {
    /// The pane's name, e.g. `"post-channelize"`.
    pub(crate) name: &'static str,
    /// What this pane holds.
    ///
    /// The fold reads id sets rather than content, so this distinction reaches
    /// only the consumers that render a pane. Declaration order is pipeline
    /// order and conversion runs last, so every [`PaneKind::Ir`] pane precedes
    /// every [`PaneKind::Operators`] one, which the assertion under
    /// [`IR_PANE_COUNT`] pins.
    pub(crate) content: PaneKind,
    /// The phases that ran between the previous pane and this one — the set
    /// [`CompiledProgram::materialize_panes`] restricts the whole-compile table
    /// by.
    ///
    /// A pair's fold is defined by the phases that ran between its two panes,
    /// not by a position in this list: a program that skips a phase must not
    /// shift another pair's set, and a row produced outside a pair's phases has
    /// to read to it as an ordinary un-produced id. A phase therefore belongs to
    /// exactly one pair, which
    /// `every_recorded_phase_belongs_to_exactly_one_pane_pair` asserts.
    pub(crate) phases: &'static [Phase],
    /// Whether the pair ending at this pane is asserted to carry no [`Leak`] of
    /// either class — by `pane_pair_folds_have_no_structural_leaks` over the
    /// programs `corpus()` lists, and by `CAMBRA_PROVENANCE_GATE` over whatever
    /// the caller compiles.
    ///
    /// **This does not license a nonzero residue where it is false.** A [`Leak`]
    /// is a bug wherever it appears; the flag says whether an assertion has been
    /// turned on. A pair goes ungated only while some phase inside it does not
    /// record, where the residue is a count of how little that phase records — a
    /// constant no correct recording elsewhere can drive down, so gating it would
    /// pin churn rather than catch a defect. Flip it in the commit that
    /// instruments the last phase in the pair, the same way an audit span's
    /// endpoint moves. Unused on the anchor, which has no pair. A pane may be
    /// issued at any point in the pipeline, so the bit outlives any one pair
    /// becoming gated; see `src/ccl/design/provenance.md`, "What gating every
    /// pair does not retire".
    pub(crate) gated: bool,
}

/// How many panes hold an expression tree.
///
/// [`CompiledProgram::pane_trees`]' arity. The assertion below pins it against
/// [`PANES`], so the trees zip against the [`PaneKind::Ir`] entries in order.
pub(crate) const IR_PANE_COUNT: usize = 6;

/// The pipeline's panes, in pipeline order, each naming the phases that produced
/// it from its predecessor.
///
/// The first entry is the anchor: it has no predecessor, so its `phases` is
/// empty and its `gated` is unused — its projection is the lowering projection
/// rather than a fold product.
///
/// Every pair is gated, so the leak classes hold at zero over whatever the caller
/// compiles. `pre-inference → post-inference` reaches that only because the fold's
/// id domain was widened to the slot domain the passes rewrite and inference's
/// per-instantiation predicate freshen took a copy recording.
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
        phases: &[Phase::Infer],
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
// Consumed by the inspector model; unused within the compiler itself.
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

    /// The pane pairs held at zero on both leak classes — [`PaneSpec::gated`].
    ///
    /// Two checks read this same set at different widths:
    /// `pane_pair_folds_have_no_structural_leaks` over the programs `corpus()`
    /// lists, on every test run, and `CAMBRA_PROVENANCE_GATE` over whatever the
    /// caller compiles, which is strictly stronger because the wider corpus
    /// reaches shapes the listed programs do not.
    pub(crate) fn gated_pane_pairs(&self) -> impl Iterator<Item = &PanePair> {
        self.pairs.iter().filter(|p| p.gated)
    }
}

/// The leak gate: **a fold's [`Leak`] vector must be empty**.
///
/// Both classes are asserted the same way. Each means a node reached the output
/// pane with nothing recording where it came from, and neither localizes the site
/// to fix on its own, so the gate reads the vector's emptiness and not its
/// composition (see [`Leak`]). A death is not a leak and reaches a caller as its
/// own collection, so there is nothing here to filter.
///
/// Debug/test only, single code path (`cfg!`, not `#[cfg]`).
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
    use std::collections::HashSet;

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
        match compile_program(&mut ctx, code, consumer) {
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

    /// **Capture totality**, as a corpus-wide property rather than a per-phase
    /// assertion: every pane pair materializes and folds over every corpus
    /// program, every output-pane node has an origin (`Unrecorded == 0`), and
    /// no node's ancestry dangles (`DanglingParent == 0`).
    ///
    /// The two invariants fail differently and are worth reading apart.
    /// `dangling_parent == 0` says no node's ancestry stops at an id the fold
    /// never heard of. `Unrecorded == 0` says no rewrite went
    /// *unrecorded* — it is the gate the whole driver-capture design exists to
    /// phase, and the number a newly-added rewrite site breaks first.
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
            // The panes are the thing being materialized: each projection must
            // hold entries for the tree it describes, and each map edges.
            //
            // Only down to the first uninstrumented pair. A pair folds against
            // the projection of the pane above it, so the first pair whose
            // phases do not record leaves every pane below it with nothing to
            // carry forward — an empty projection there is the expected state,
            // not a defect.
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

    /// Every phase that records rows in a normal compile belongs to exactly one
    /// pane pair, so no rewrite is folded twice and none is silently dropped.
    ///
    /// [`PANES`]' phase sets are the only thing that decides which pane pair a
    /// row reaches, so a phase that opens a scope without joining one would
    /// record rows nothing ever folds, and a phase in two would be folded twice.
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

    /// **The provenance map is well-formed and non-vacuous** on every corpus
    /// program: every edge runs from an input-pane id to an output-pane id,
    /// every id present in both panes is its own dense self-edge, and every
    /// gated pane pair reads a *row* on at least one program.
    ///
    /// The non-vacuity half is what this test is for. A pane pair whose phases
    /// minted nothing on a given program derives its whole map from the two
    /// pane id sets, so the well-formedness assertions above hold there for
    /// reasons that have nothing to do with the recording. Requiring one
    /// witness per pair is what keeps a pair whose instrumentation stopped
    /// firing — or a corpus that lost the only program exercising it — from
    /// leaving a green tautology behind. Which programs supply the witness is
    /// not pinned: a program rewrites where its own shape makes it rewrite, and
    /// pinning that turns every corpus edit into a list edit.
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
                // Dense: a node present in both panes is its own self-edge, and
                // a node descends from itself — so a consumer only ever follows
                // edges, never reconstructs one, and reads ancestry off the
                // label it finds there.
                for id in input_ids.intersection(output_ids) {
                    let self_edge = map.upstream(id).iter().find(|l| l.id == *id);
                    assert!(
                        self_edge.is_some_and(|l| l.labels.has_ancestry()),
                        "{name}: {id:?} survives {pair} without an ancestry self-edge",
                    );
                }
                // A non-self edge is the only proof a row was consulted: a
                // pane pair whose phases rewrote nothing derives its whole
                // map from the two pane id sets.
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

    /// **Blame reaches the provenance map, labelled**: the `blame` column is
    /// closed transitively alongside `parents`, so a consumer receives the
    /// blame edges and can render or prune them.
    ///
    /// Pinned by name, unlike the per-pair witness
    /// [`the_pane_folds_derive_a_non_vacuous_provenance_map`] asks for: blame is
    /// named at a handful of sites — the mutability phases' effect and begin
    /// nodes, and the refinement predicate `planning.hash_join` reads its plan
    /// out of — so the pin is short, and a corpus or recording edit that stopped
    /// exercising them would otherwise leave the labelled half of the map
    /// untested.
    ///
    /// A blame edge is *only* blame here: no corpus rewrite both
    /// consumes a node and blames it, so nothing in the corpus pins the
    /// both-labels case — the fold tests in `provenance.rs` do.
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

    /// One mutation statement's image across the `post-inference →
    /// post-channelize` pair, split by what the edge asserts: the nodes that
    /// descend from it, and the nodes merely related to it.
    ///
    /// The two are kept apart because the claims are different. "This statement
    /// reaches its own products" is ancestry; blame relates without claiming
    /// ancestry, and two statements are legitimately blamed on one node
    /// (`planning.hash_join` blames both of a join's conditions). Folding blame
    /// in would let a statement that was only mentioned pass for one that
    /// produced something, and would make disjointness reject a correct pair of
    /// blame edges.
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
                out = defer()
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
                out = defer()
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
                out = defer()
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

    /// **Both of a nested join's conditions reach the map**, as blame edges from
    /// `planning.hash_join`.
    ///
    /// The site's recording blames what the *domain type* carries rather than the
    /// refinement the recogniser accepted, because `join_plan_to_expr` re-enters
    /// `convert_refinement_to_join` on an arm's own refined type — three frames
    /// below the recording, with no access to its guard. A one-condition join
    /// cannot tell the two apart, which is what the flat control fixes: the
    /// nested program must blame two distinct predicates where the flat one
    /// blames one.
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

    /// The corpus programs whose definitions inference **generalizes and then
    /// specializes** — the ones monomorphization actually clones a subtree for.
    /// Everything else in the corpus is first-order, and mono mints nothing.
    const SPECIALIZING: &[&str] = &["generator_pipeline", "udf_chain"];

    /// Monomorphization — the one thing that mints between the first two panes —
    /// explains every node it produces, on first-order and specializing
    /// programs alike.
    ///
    /// Two recordings get it there, and both are needed: `specialize_use` sinks
    /// the clone's `on_copy` pairs, and `coalesce_generalized_let` sinks the
    /// chain of `let`s the binding rebuilds itself as. Without the second, a
    /// specializing program leaves one unrecorded `let` per demanded
    /// specialization — a per-program count that tracks how many types the body
    /// asked for, which is why it read as a small constant on this corpus.
    ///
    /// Asserted both ways so the zero cannot be vacuous: a specializing program
    /// must also *kill* nodes here, since its generalized definition is
    /// replaced by clones. A regression that stopped running mono at all would
    /// otherwise pass.
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

    /// Every phase inside the second pane pair explains what it produces.
    ///
    /// The interesting programs are the ones that drive a *whole-program*
    /// rewrite, where naming one node is least obviously applicable: a
    /// transaction is disassembled into a commit carrier whose pieces have no
    /// single source node, and a defer cluster becomes a `LetRec` assembled from
    /// contributions scattered across the body. Both are covered by recording
    /// against the node each product stands in for — the `with begin():`
    /// statement, the register declaration, the `let d = Defer`.
    ///
    /// Asserted with a non-vacuity guard for the same reason the first pane pair is: a
    /// program that reaches one of these phases must also kill nodes, so a
    /// regression that stopped running the phase cannot pass as capture.
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

    /// **Distinct predicate terms never share a `NodeId`** — with each other, or
    /// with the main tree — on the three trees the panes retain.
    ///
    /// [`assert_unique_node_ids`] runs the same [`predicate_id_collisions`] walk
    /// at every phase boundary, so what this adds is the panes: `pre_inference_ir`
    /// is snapshotted after `uniquify`, between two boundaries, and no boundary
    /// walk reaches it.
    ///
    /// What the walk catches is a rebuild that **preserves ids when it should
    /// not**. A predicate cannot be mutated through its `Rc`, so every rewrite
    /// builds a new `Rc` and repoints the refinement it was handed. That is a
    /// *replacement* only if the walk reaches every occurrence; otherwise the
    /// original survives on some type the walk missed, and preserving ids puts one
    /// id-set on two live terms. `PredMemo::replacing` is the opt-in for walks
    /// that do reach everything, and `uniquify` — the only one — asserts its own
    /// 1:1 correspondence separately.
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

    /// A phase that rewrites the program records its rewrites under its own phase
    /// tag — the tag being the one part of a row no recording site knows, and the
    /// only thing that places a row in a pane pair's fold.
    ///
    /// A phase that rewrites *nothing* on a given program records nothing, which
    /// is the preserve case and correct (most of the corpus preserves end to
    /// end), so the fixture is one that drives three of the five: the
    /// transaction, which `transact_phase` disassembles, `mut_elim` rebuilds as
    /// a `LetRec`, and `channelize` rewrites.
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
                Phase::AsOfRead,
                Phase::Channelize,
                Phase::Convert,
                Phase::Infer,
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
                let mut src = String::from("out = defer()\nxs = [1, 2, 3, 4, 5]\n");
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

    /// **The graph has both program boundaries**: a sink per compiled output, and
    /// a source per registered data source that some expression reads.
    ///
    /// Without them the graph begins and ends in the middle of nothing, and a
    /// reader has no way to tell an output from an operator whose consumer the
    /// capture missed. Both are pane nodes like any other, so each carries a
    /// provenance row and resolves to a span.
    #[test]
    fn the_operator_graph_carries_its_boundary_nodes() {
        use crate::interpreter::operator_graph::GraphNode;

        let mut saw_a_source = false;
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
                let (id, what) = match node {
                    GraphNode::Source { id, name } => (*id, format!("source {name}")),
                    GraphNode::Sink { id, name, .. } => (*id, format!("sink {name}")),
                    GraphNode::Operator { .. } => continue,
                };
                assert!(
                    attribution.contains_key(&id),
                    "{name}: {what} carries no attribution, so it resolves to no span",
                );
            }

            saw_a_source |= graph
                .nodes()
                .iter()
                .any(|n| matches!(n, GraphNode::Source { .. }));
        }
        assert!(
            saw_a_source,
            "no corpus program reads a data source, so the source-node path is unexercised",
        );
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
    /// that already exists — and `record_deferred_edge` runs only when a slot is
    /// filled. So the deferred edges are the set whose removal leaves the
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
        let reps: usize = std::env::var(PERF_REPS_ENV)
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(3);
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
            for _ in 0..reps {
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
