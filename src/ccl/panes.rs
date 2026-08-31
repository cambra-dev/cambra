//! The pipeline's **panes** — its retained AST snapshots — and what a fold
//! between two adjacent ones produces.
//!
//! A pane is one snapshot of the tree, taken at a named point in
//! [`compile_program`](crate::ccl::context::compile_program). [`PANES`] declares
//! the topology once: every pane, the phases that produced it from the pane
//! before it, and whether its pair is gated.
//!
//! Split out of [`context`](crate::ccl::context) because it is the inspector's
//! half of the seam. `context` owns the pipeline and the [`Phase`] axis; this
//! module owns what a pane pair is and what folding one yields, and none of it
//! runs in a release compile except [`gate_leaks`], which `compile_program`
//! calls only under `CAMBRA_PROVENANCE_GATE`. The inherent `impl
//! CompiledProgram` below lives here rather than beside the struct for the same
//! reason: the methods are the pane layer's, not the pipeline's. See
//! `design/provenance.md`, "The seam".

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
        let trees = self.pane_trees();
        let ids: Vec<_> = trees.iter().map(|t| collect_tree_ids(t)).collect();

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
    /// [`PANES`]. The length is [`PANES`]' own, so the two cannot disagree about
    /// how many panes there are.
    fn pane_trees(&self) -> [&Expr; PANES.len()] {
        [
            &self.pre_inference_ir,
            &self.post_inference_ir,
            &self.post_channelize_ir,
            &self.post_as_of_read_ir,
            &self.post_lambda_elim_ir,
            &self.ast,
        ]
    }
}

/// One pane — a retained AST snapshot — and the phases that produced it from the
/// pane before it.
///
/// [`PANES`] declares the whole topology in one place, so adding a pane is one
/// entry there plus its tree in [`CompiledProgram::pane_trees`].
pub(crate) struct PaneSpec {
    /// The pane's name, e.g. `"post-channelize"`.
    pub(crate) name: &'static str,
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

/// The pipeline's panes, in pipeline order, each naming the phases that produced
/// it from its predecessor. Order matches [`CompiledProgram::pane_trees`]
/// element for element.
///
/// The first entry is the anchor: it has no predecessor, so its `phases` is
/// empty and its `gated` is unused — its projection is the lowering projection
/// rather than a fold product.
///
/// Every pair is gated, so the leak classes hold at zero over whatever the caller
/// compiles. `pre-inference → post-inference` reaches that only because the fold's
/// id domain was widened to the slot domain the passes rewrite and inference's
/// per-instantiation predicate freshen took a copy recording.
pub(crate) const PANES: [PaneSpec; 6] = [
    PaneSpec {
        name: "pre-inference",
        phases: &[],
        gated: false,
    },
    PaneSpec {
        name: "post-inference",
        phases: &[Phase::Infer],
        gated: true,
    },
    PaneSpec {
        name: "post-channelize",
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
        phases: &[Phase::AsOfRead],
        gated: true,
    },
    PaneSpec {
        name: "post-lambda-elim",
        phases: &[Phase::LambdaElim],
        gated: true,
    },
    PaneSpec {
        name: "post-planning",
        phases: &[Phase::Planning],
        gated: true,
    },
];

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
    use super::*;
    use crate::ccl::context::{
        GlobalContext, PERF_REPS_ENV, compile_program, predicate_id_collisions,
        provenance_capture_enabled,
    };
    use crate::interpreter::Consumer;

    /// The pane-measurement corpus: every demo-gallery program that compiles
    /// today, plus four inline programs covering the phases the gallery does not
    /// reach (a `with begin():` transaction, a group-by, a UDF chain, and a
    /// nested comprehension).
    ///
    /// The gallery's remaining programs are excluded for reasons unrelated to
    /// provenance: most are deliberate *failure* fixtures (`while`, record-term
    /// syntax, `Feed(_)` types) that pin errors and so have no panes to fold,
    /// and the three HTTP demos bind a real listening socket during lowering,
    /// which collides with itself under a parallel test runner.
    fn corpus() -> Vec<(&'static str, String)> {
        vec![
            (
                "arithmetic",
                include_str!("../../tests/programs/arithmetic/program.cambra").to_string(),
            ),
            (
                "filter_and_aggregate",
                include_str!("../../tests/programs/filter_and_aggregate/program.cambra").to_string(),
            ),
            (
                "for_accumulator",
                include_str!("../../tests/programs/for_accumulator/program.cambra").to_string(),
            ),
            (
                "generator_pipeline",
                include_str!("../../tests/programs/generator_pipeline/program.cambra").to_string(),
            ),
            (
                "inner_join",
                include_str!("../../tests/programs/inner_join/program.cambra").to_string(),
            ),
            (
                "join_then_groupby",
                include_str!("../../tests/programs/join_then_groupby/program.cambra").to_string(),
            ),
            (
                "prefix_lines",
                include_str!("../../tests/programs/prefix_lines/program.cambra").to_string(),
            ),
            (
                "streaming_echo",
                include_str!("../../tests/programs/streaming_echo/program.cambra").to_string(),
            ),
            (
                "transaction",
                "out = defer()\n\
                 pool: Mut(Int, Txn) := 100\n\
                 for r in [10, 20, 30]:\n\
                 \x20   with begin():\n\
                 \x20       pool := pool - r\n\
                 with begin():\n\
                 \x20   out << pool\n\
                 out\n"
                    .to_string(),
            ),
            (
                "group_by",
                "[sum(x) for x in groupby([y + 10 for y in [2,3,4,5,6] if y < 6], \\x -> x // 2)]\n"
                    .to_string(),
            ),
            (
                "udf_chain",
                "def double(x):\n    x * 2\ndef bump(x):\n    double(x) + 1\n\
                 xs = [1, 2, 3]\n[bump(x) for x in xs]\n"
                    .to_string(),
            ),
            (
                "feed_loop",
                "out = defer()\nfor x in [1, 2, 3]:\n    out << x * 2\nout\n".to_string(),
            ),
        ]
    }

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
        let mut exercised: std::collections::HashSet<usize> = std::collections::HashSet::new();
        for (name, code) in corpus() {
            let program = compile_ok(&code);
            let panes = program.materialize_panes();
            let ids: Vec<_> = program
                .pane_trees()
                .iter()
                .map(|t| collect_tree_ids(t))
                .collect();

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
            let blamed: std::collections::HashSet<NodeId> = pair
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
            // The three retained pane snapshots are unconditional — they are not
            // part of what the capture switch turns off — so their size is the
            // pane design's real memory floor, against which the logs are noise.
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

    /// A substituted parameter's two spans stay on **distinct** nodes, pane by
    /// pane, for as long as the projection carries them at all.
    ///
    /// `uncurry_params` answers "where is `a` declared" with a pair — the
    /// projection root carries the occurrence, its `Proj` child the declaration
    /// (`src/ccl/design/ir.md`, "A substituted parameter's site rides its
    /// projection"). A `SourceAttribution`'s `spans` is a *set* and the fold
    /// unions attributions along its edges, so the pair is only readable while no
    /// node holds both halves. `lower/functions.rs` pins the pair as lowering
    /// emits it; this pins that folding four pane pairs onto it does not merge
    /// them, which is the property a consumer reading a lowered pane depends on.
    ///
    /// It also pins where the answer stops. `lambda_elim` rewrites the body
    /// point-free and the parameter spans do not reach its pane — so the
    /// mechanism covers the panes before it and no further, and a change that
    /// carried them through would fail here and be a guarantee worth widening in
    /// `ir.md` rather than a silent improvement.
    #[test]
    fn a_substituted_parameters_two_spans_stay_on_distinct_nodes() {
        use crate::chl_parser::ast::Span;

        let code = "def add(a, b):\n  a + a + b\nadd(1, 2)\n";
        // `a` and `b` as written: two declarations and three occurrences.
        let decls = [Span::new(8, 9), Span::new(11, 12)];
        let occurrences = [Span::new(17, 18), Span::new(21, 22), Span::new(25, 26)];

        let panes = compile_ok(code).materialize_panes();
        for name in [
            "pre-inference",
            "post-inference",
            "post-channelize",
            "post-as-of-read",
        ] {
            let projection = panes.projection(name);
            let (mut saw_decl, mut saw_occurrence) = (false, false);
            for (id, attr) in projection.iter() {
                let decl = attr.spans.iter().any(|s| decls.contains(s));
                let occurrence = attr.spans.iter().any(|s| occurrences.contains(s));
                assert!(
                    !(decl && occurrence),
                    "pane {name}: {id:?} carries a parameter's declaration and an \
                     occurrence at once ({:?}), so a consumer cannot tell the two \
                     apart",
                    attr.spans
                );
                saw_decl |= decl;
                saw_occurrence |= occurrence;
            }
            assert!(
                saw_decl && saw_occurrence,
                "pane {name}: the projection carries no parameter spans at all \
                 (declaration: {saw_decl}, occurrence: {saw_occurrence}), so the \
                 disjointness above proves nothing"
            );
        }

        // The bound: `lambda_elim` does not carry the parameter spans forward.
        let after = panes.projection("post-lambda-elim");
        let carried: Vec<_> = after
            .iter()
            .filter(|(_, a)| {
                a.spans
                    .iter()
                    .any(|s| decls.contains(s) || occurrences.contains(s))
            })
            .map(|(id, _)| id)
            .collect();
        assert!(
            carried.is_empty(),
            "post-lambda-elim now carries parameter spans ({carried:?}) — widen \
             the guarantee in `ir.md` and extend the pane list above"
        );
    }
}
