//! Stage adjacency — the node→node links between two adjacent pipeline stages.
//!
//! The multi-pane inspector shows several pipeline stages side by side (CHL
//! source, pre-inference IR, post-inference IR, post-desugar IR, …) and links a node in one pane
//! to the node(s) it came from / became in the adjacent panes. That link is the
//! *true derivation chain*, not a span approximation.
//!
//! The link decomposes into two parts:
//!
//! * **Identity edges** — a [`NodeId`] preserved unchanged across a pass appears
//!   in *both* stages' trees with the same id. The vast majority of nodes are
//!   like this (lowering→uniquify→desugar→infer all preserve ids in place for
//!   ordinary nodes). Identity edges are **not stored** here: the consumer
//!   recomputes them trivially ("highlight the same id in each pane").
//! * **Non-identity edges** — the few sites where a pass changes node identity:
//!   monomorphization fan-out (one upstream generalized definition → N
//!   downstream specialization clones, plus the `coalesce_generalized_let`
//!   wrappers) bridges the pre-inference⇄post-inference pair, and inline
//!   fan-out (one upstream node → N freshened copies of a multi-use UDF body)
//!   bridges post-inference⇄post-desugar. These come from the per-pass remaps
//!   the compiler retains
//!   ([`CompiledProgram::pass_remaps`](crate::ccl::context::CompiledProgram::pass_remaps)),
//!   associated to their stage pair by [`remap_between_stages`].
//!
//! This is the reusable pattern for every future stage: a pass that changes
//! identity surfaces a node→node remap; [`StageAdjacency::from_remap`] turns it
//! into a bidirectional projection. lambda-elim (1→many), planning (many→1), and
//! `operator_conversion` (`OperatorId`→`NodeId`, the dataflow pane) all slot in
//! the same way.

use std::collections::HashMap;

use crate::ccl::Expr;
use crate::ccl::provenance::{NodeId, Pass};

/// The non-identity node→node links between an *upstream* stage and a
/// *downstream* stage, in both directions. Keyed by the opaque `u64` node handle
/// ([`NodeId::as_u64`]) so it is directly serializable for the wire payload.
///
/// Identity edges are intentionally absent (see the module doc) — a consumer
/// resolves an upstream node `n` to downstream nodes as
/// `downstream(n)` ∪ (`{n}` if `n` is also a node in the downstream tree).
#[derive(Debug, Default, Clone)]
pub struct StageAdjacency {
    /// upstream node id → downstream node ids (e.g. a def → its mono clones).
    down: HashMap<u64, Vec<u64>>,
    /// downstream node id → upstream node ids (e.g. a clone → its origin def).
    up: HashMap<u64, Vec<u64>>,
}

impl StageAdjacency {
    /// Build the adjacency between `upstream_ir` and `downstream_ir` from a raw
    /// `(downstream_id, upstream_origin_id)` remap (an entry of
    /// [`CompiledProgram::pass_remaps`](crate::ccl::context::CompiledProgram::pass_remaps),
    /// or several concatenated by `remap_between_stages`).
    ///
    /// Each `downstream_id` is a node minted in the downstream stage (a clone or
    /// wrapper). Its `upstream_origin_id` is followed transitively through the
    /// remap (nested specializations chain: `fresh → fresh → … → original`)
    /// until it reaches a node that actually exists in `upstream_ir` — that is
    /// the upstream end of the edge. A chain that never reaches an upstream node
    /// contributes no edge (graceful: the clone simply has no upstream pane
    /// counterpart, e.g. a clone of a synthesized node with no source analogue).
    pub fn from_remap(
        upstream_ir: &Expr,
        downstream_ir: &Expr,
        remap: &[(NodeId, NodeId)],
    ) -> Self {
        let upstream_ids = collect_ids(upstream_ir);
        let downstream_ids = collect_ids(downstream_ir);
        // `downstream_id → origin` lookup so a chain step is O(1).
        let predecessor: HashMap<NodeId, NodeId> = remap.iter().copied().collect();

        let mut adj = StageAdjacency::default();
        for &(fresh, origin) in remap {
            // Only record edges whose downstream end is a live node in the
            // downstream tree (the remap can carry interior ids inference later
            // discarded).
            if !downstream_ids.contains(&fresh.as_u64()) {
                continue;
            }
            if let Some(upstream) = resolve_to_existing(origin, &predecessor, &upstream_ids) {
                let (d, u) = (fresh.as_u64(), upstream);
                push_unique(adj.down.entry(u).or_default(), d);
                push_unique(adj.up.entry(d).or_default(), u);
            }
        }
        adj
    }

    /// The downstream node ids an upstream node id flowed into (the non-identity
    /// fan-out). Empty slice if none.
    pub fn downstream(&self, upstream: u64) -> &[u64] {
        self.down.get(&upstream).map_or(&[], Vec::as_slice)
    }

    /// The upstream node ids a downstream node id came from. Empty slice if none.
    pub fn upstream(&self, downstream: u64) -> &[u64] {
        self.up.get(&downstream).map_or(&[], Vec::as_slice)
    }

    /// Iterate every non-identity edge as `(upstream_id, downstream_id)` — the
    /// shape the wire payload serializes.
    pub fn edges(&self) -> impl Iterator<Item = (u64, u64)> + '_ {
        self.down
            .iter()
            .flat_map(|(&u, ds)| ds.iter().map(move |&d| (u, d)))
    }
}

/// The compiler passes that run between two adjacent inspector stage snapshots
/// — the stage-pair → pass association the stage links are built from.
///
/// The compiler retains remaps keyed by [`Pass`]
/// ([`CompiledProgram::pass_remaps`](crate::ccl::context::CompiledProgram::pass_remaps))
/// — it knows passes, not panes; stage ids are inspector vocabulary, so the
/// pairing is declared here, keyed by the pair's *ids* (never by position in
/// the stage list, so it cannot silently rot when stages are added or
/// reordered): monomorphization runs between the pre-inference and
/// post-inference snapshots, inline between post-inference and post-desugar.
/// An unknown pair is bridged by no recorded pass — graceful, its links are
/// identity-only.
fn passes_between(upstream_stage: &str, downstream_stage: &str) -> &'static [Pass] {
    match (upstream_stage, downstream_stage) {
        ("pre-inference", "post-inference") => &[Pass::Mono],
        ("post-inference", "post-desugar") => &[Pass::Inline],
        _ => &[],
    }
}

/// The `(downstream, upstream)` remap bridging the
/// `upstream_stage → downstream_stage` stage pair: the retained remaps of every
/// pass that runs between the two snapshots ([`passes_between`]), concatenated
/// in pass order when a pair spans several.
pub(super) fn remap_between_stages(
    pass_remaps: &[(Pass, Vec<(NodeId, NodeId)>)],
    upstream_stage: &str,
    downstream_stage: &str,
) -> Vec<(NodeId, NodeId)> {
    passes_between(upstream_stage, downstream_stage)
        .iter()
        .flat_map(|pass| {
            pass_remaps
                .iter()
                .filter(move |(p, _)| p == pass)
                .flat_map(|(_, remap)| remap.iter().copied())
        })
        .collect()
}

/// Follow `start → predecessor[start] → …` until reaching an id present in
/// `existing`, returning it as a `u64`. `None` if the chain bottoms out first.
fn resolve_to_existing(
    start: NodeId,
    predecessor: &HashMap<NodeId, NodeId>,
    existing: &std::collections::HashSet<u64>,
) -> Option<u64> {
    use std::collections::HashSet;
    let mut cursor = start;
    let mut seen = HashSet::new();
    loop {
        if existing.contains(&cursor.as_u64()) {
            break Some(cursor.as_u64());
        }
        if !seen.insert(cursor) {
            break None;
        }
        match predecessor.get(&cursor) {
            Some(&next) => cursor = next,
            None => break None,
        }
    }
}

fn collect_ids(expr: &Expr) -> std::collections::HashSet<u64> {
    let mut ids = std::collections::HashSet::new();
    fn walk(e: &Expr, ids: &mut std::collections::HashSet<u64>) {
        ids.insert(e.node_id().as_u64());
        e.walk_children(|c| walk(c, ids));
    }
    walk(expr, &mut ids);
    ids
}

fn push_unique(v: &mut Vec<u64>, x: u64) {
    if !v.contains(&x) {
        v.push(x);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::interpreter::Consumer;

    fn compile(code: &str) -> crate::ccl::context::CompiledProgram {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        compile_program(&mut ctx, code, consumer).expect("program compiles")
    }

    /// A let-polymorphic def used at two types fans out: the upstream `dup`
    /// definition (in the pre-inference tree) links downstream to ≥2 distinct
    /// specialization nodes (in the post-inference tree), and each of those links
    /// back up to the one upstream origin. Monomorphization runs inside `infer`,
    /// so the fan-out is exactly the pre-inference → post-inference stage edge.
    #[test]
    fn mono_fanout_links_upstream_def_to_downstream_clones() {
        let code = "\
dup = lambda x: (x, x)
a = dup(1)
b = dup(2 == 2)
a
";
        let prog = compile(code);
        let adj = StageAdjacency::from_remap(
            &prog.pre_inference_ir,
            &prog.post_inference_ir,
            prog.remap_for(Pass::Mono),
        );

        // Every recorded edge is bidirectionally consistent and crosses the
        // identity boundary (upstream id ≠ downstream id).
        let edges: Vec<(u64, u64)> = adj.edges().collect();
        assert!(
            !edges.is_empty(),
            "a monomorphized def must produce non-identity stage edges"
        );
        for (u, d) in &edges {
            assert_ne!(u, d, "a non-identity edge must cross the id boundary");
            assert!(
                adj.upstream(*d).contains(u),
                "down edge {u}->{d} must have the matching up edge"
            );
            assert!(
                adj.downstream(*u).contains(d),
                "up edge {d}<-{u} must have the matching down edge"
            );
        }

        // At least one upstream node fans out to ≥2 downstream nodes (dup used
        // at Int and Bool).
        assert!(
            adj.down.values().any(|ds| ds.len() >= 2),
            "dup used at two types should fan out to ≥2 downstream nodes; edges={edges:?}"
        );
    }

    /// RT-3c — the retained inline remap feeds `StageAdjacency::from_remap` to
    /// link the post-inference anchor to its post-desugar inline fan-out copies.
    ///
    /// A scalar UDF called at two sites *at the same type* fans its body out
    /// during inlining (mono makes one specialization; inline duplicates the
    /// body). Each `(copy, origin)` pair the recorder retained yields a
    /// non-identity stage edge whose downstream (copy) id lives in the
    /// post-desugar tree and whose upstream (origin) id lives in the
    /// post-inference tree.
    ///
    /// Without the retained inline remap, there is nothing to feed
    /// `StageAdjacency::from_remap` and this link would not exist.
    #[test]
    fn inline_fanout_links_post_inference_to_post_desugar_copies() {
        let code = "\
add1 = lambda x: x + 1
a = add1(10)
b = add1(20)
a + b
";
        let prog = compile(code);
        let adj = StageAdjacency::from_remap(
            &prog.post_inference_ir,
            &prog.post_desugar_ir,
            prog.remap_for(Pass::Inline),
        );

        let up_ids = collect_ids(&prog.post_inference_ir);
        let down_ids = collect_ids(&prog.post_desugar_ir);
        let edges: Vec<(u64, u64)> = adj.edges().collect();
        assert!(
            !edges.is_empty(),
            "a two-site inline fan-out must produce non-identity stage edges"
        );
        // `edges()` yields `(upstream, downstream)`.
        for (u, d) in &edges {
            assert!(
                up_ids.contains(u),
                "edge upstream id {u} must be a node in the post-inference tree"
            );
            assert!(
                down_ids.contains(d),
                "edge downstream id {d} must be a node in the post-desugar tree"
            );
            assert!(
                adj.upstream(*d).contains(u),
                "down edge {u}->{d} must have the matching up edge"
            );
        }
    }

    /// A program with no monomorphization has no non-identity edges — every
    /// cross-pane link is pure identity.
    #[test]
    fn monomorphic_program_has_no_non_identity_edges() {
        let code = "\
x = 1 + 2
x
";
        let prog = compile(code);
        let adj = StageAdjacency::from_remap(
            &prog.pre_inference_ir,
            &prog.post_inference_ir,
            prog.remap_for(Pass::Mono),
        );
        assert_eq!(adj.edges().count(), 0);
    }

    /// The stage-pair → pass association selects by the pair's *ids*, never by
    /// position in a stage list: the (pre-inference, post-inference) pair gets
    /// the `Mono` remap, (post-inference, post-desugar) the `Inline` remap —
    /// regardless of the order the retained entries arrive in — and an unknown
    /// pair gets an empty remap (graceful identity-only links).
    #[test]
    fn stage_pair_selects_the_remap_of_its_bridging_pass() {
        let mono = vec![(NodeId::fresh(), NodeId::fresh())];
        let inline = vec![
            (NodeId::fresh(), NodeId::fresh()),
            (NodeId::fresh(), NodeId::fresh()),
        ];

        // Both retention orders — the association must not depend on entry
        // position.
        let retained = [
            vec![(Pass::Mono, mono.clone()), (Pass::Inline, inline.clone())],
            vec![(Pass::Inline, inline.clone()), (Pass::Mono, mono.clone())],
        ];
        for pass_remaps in &retained {
            assert_eq!(
                remap_between_stages(pass_remaps, "pre-inference", "post-inference"),
                mono,
                "the pre-inference → post-inference pair selects Mono's remap"
            );
            assert_eq!(
                remap_between_stages(pass_remaps, "post-inference", "post-desugar"),
                inline,
                "the post-inference → post-desugar pair selects Inline's remap"
            );
            assert!(
                remap_between_stages(pass_remaps, "post-desugar", "operator").is_empty(),
                "an unknown stage pair selects no remap (graceful)"
            );
        }
    }
}
