//! Pane-pair node→node links (the provenance map).
//!
//! The multi-pane inspector shows several pipeline stages side by side (CHL
//! source, pre-inference IR, post-inference IR, post-channelize IR, …) and links a
//! node in one pane to the node(s) it came from / became in the adjacent panes.
//! That link is the node's provenance across the phase.
//!
//! The link is a [`ProvenanceMap<NodeId, NodeId>`] folded at the pane boundary by
//! [`collapse`](crate::ccl::provenance::collapse) — one per adjacent pane pair,
//! materialized on [`CompiledProgram`](crate::ccl::context::CompiledProgram) via
//! `materialize_panes`. The map is **dense**: every id that survived the phase
//! is its own self-edge. The wire ships the map **verbatim** — self-edges
//! included — so the frontend follows edges only (no identity special case); a
//! surviving node's cross-pane link is the shipped `[id, id]` self-edge, and a
//! genuine identity *change* (monomorphization / inline fan-out, channelize's
//! cluster/fan-in copies) is a `u != d` edge.

use crate::ccl::provenance::{EdgeLabels, NodeId, ProvenanceMap};

/// Every edge of a pane-pair [`ProvenanceMap`], as `(upstream, downstream, labels)`
/// — **dense**: self-edges (`u == d`, a node preserved across the phase) are
/// kept, so the frontend needs no identity special case.
///
/// The labels say what the edge *asserts*, which a consumer needs in order to
/// render or prune the two apart: `"descends"` for an edge the downstream node
/// was made from, `"relates"` for one it is about but was not made from. They
/// are a **set** — an edge reachable both ways carries both — so this is an
/// array rather than one discriminant, and an edge always carries at least one.
///
/// [`ProvenanceMap::edges`] already yields sorted, deduplicated edges, one entry
/// per pair; this only projects to the wire's `u64` and label strings.
pub fn dense_edges(map: &ProvenanceMap<NodeId, NodeId>) -> Vec<(u64, u64, Vec<&'static str>)> {
    map.edges()
        .into_iter()
        .map(|(u, d)| (u.as_u64(), d.id.as_u64(), wire_labels(d.labels)))
        .collect()
}

/// The wire spelling of an edge's label set, in a fixed order so the payload is
/// deterministic.
fn wire_labels(labels: EdgeLabels) -> Vec<&'static str> {
    let mut out = Vec::with_capacity(2);
    if labels.has_ancestry() {
        out.push("descends");
    }
    if labels.has_blame() {
        out.push("relates");
    }
    debug_assert!(!out.is_empty(), "an edge carries at least one label");
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::context::{CompiledProgram, GlobalContext, compile_program};
    use crate::interpreter::Consumer;

    fn compile(code: &str) -> CompiledProgram {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        compile_program(&mut ctx, code, consumer).expect("program compiles")
    }

    /// A let-polymorphic def used at two types fans out: the pre-inference →
    /// post-inference map (folded from the rows `Phase::Infer` wrote) is dense —
    /// surviving nodes carry `[id, id]` self-edges — and at least one upstream
    /// node fans out to ≥2 distinct downstream nodes (the specialization
    /// clones), a genuine `u != d` identity change.
    #[test]
    fn mono_fanout_links_upstream_def_to_downstream_clones() {
        let code = "\
dup = \\x -> (x, x)
a = dup(1)
b = dup(2 == 2)
a
";
        let prog = compile(code);
        let panes = prog.materialize_panes();
        let edges = dense_edges(&panes.pair("pre-inference → post-inference").map);

        assert!(!edges.is_empty(), "the pane-pair map has edges");
        assert!(
            edges.iter().any(|(u, d, _)| u == d),
            "the dense map ships self-edges for nodes preserved across the phase"
        );

        // At least one upstream node fans out to ≥2 distinct downstream nodes
        // (dup used at Int and Bool) — counting only the genuine identity
        // changes, not the self-edges.
        let mut fanout: std::collections::HashMap<u64, usize> = std::collections::HashMap::new();
        for (u, d, _) in &edges {
            if u != d {
                *fanout.entry(*u).or_default() += 1;
            }
        }
        assert!(
            fanout.values().any(|&n| n >= 2),
            "dup used at two types should fan out to ≥2 downstream nodes; edges={edges:?}"
        );
    }

    /// Every edge endpoint of a pane pair is a node of the pane it points into.
    ///
    /// The id set is `collect_tree_ids`', not `walk_children`': predicate
    /// interiors are rows the fold explains, so they are edge endpoints, and a
    /// tree walk that stopped at the main tree would call a live endpoint dead.
    /// This is the invariant the wire validators enforce on the shipped payload,
    /// asserted here against the source of truth.
    fn assert_endpoints_live(
        edges: &[(u64, u64, Vec<&'static str>)],
        upstream: &crate::ccl::Expr,
        downstream: &crate::ccl::Expr,
        up_name: &str,
        down_name: &str,
    ) {
        let ids = |e: &crate::ccl::Expr| -> std::collections::HashSet<u64> {
            crate::ccl::context::collect_tree_ids(e)
                .iter()
                .map(|id| id.as_u64())
                .collect()
        };
        let up_ids = ids(upstream);
        let down_ids = ids(downstream);
        for (u, d, _) in edges {
            assert!(
                up_ids.contains(u),
                "edge upstream id {u} must be a node in the {up_name} tree"
            );
            assert!(
                down_ids.contains(d),
                "edge downstream id {d} must be a node in the {down_name} tree"
            );
        }
    }

    /// A two-site inline fan-out surfaces as non-identity edges on the
    /// post-inference → post-channelize map, each edge's upstream a
    /// post-inference node and downstream a post-channelize node.
    #[test]
    fn inline_fanout_links_post_inference_to_post_channelize_copies() {
        let code = "\
add1 = \\x -> x + 1
a = add1(10)
b = add1(20)
a + b
";
        let prog = compile(code);
        let panes = prog.materialize_panes();
        let edges = dense_edges(&panes.pair("post-inference → post-channelize").map);
        assert!(
            !edges.is_empty(),
            "a two-site inline fan-out must produce non-identity stage edges"
        );
        assert_endpoints_live(
            &edges,
            &prog.post_inference_ir,
            &prog.post_channelize_ir,
            "post-inference",
            "post-channelize",
        );
    }

    /// A monomorphic program changes no **main-tree** identity across inference:
    /// every main-tree edge is a self-edge. Its predicates are a different story
    /// — inference rebuilds a refinement predicate rather than preserving it, so
    /// each rebuild is a genuine `u != d` edge — and this pins that the whole of
    /// the difference is predicate interiors and nothing else.
    #[test]
    fn a_monomorphic_program_changes_no_main_tree_identity_across_inference() {
        let code = "\
x = 1 + 2
x
";
        let prog = compile(code);
        let panes = prog.materialize_panes();
        let edges = dense_edges(&panes.pair("pre-inference → post-inference").map);
        assert!(
            !edges.is_empty(),
            "a compiled program has surviving nodes, hence dense self-edges"
        );
        assert_endpoints_live(
            &edges,
            &prog.pre_inference_ir,
            &prog.post_inference_ir,
            "pre-inference",
            "post-inference",
        );

        // The main tree: `walk_children` only, which is exactly the domain the
        // identity claim covers.
        fn main_tree_ids(e: &crate::ccl::Expr) -> std::collections::HashSet<u64> {
            let mut s = std::collections::HashSet::new();
            fn go(e: &crate::ccl::Expr, s: &mut std::collections::HashSet<u64>) {
                s.insert(e.node_id().as_u64());
                e.walk_children(|c| go(c, s));
            }
            go(e, &mut s);
            s
        }
        let up_main = main_tree_ids(&prog.pre_inference_ir);
        let down_main = main_tree_ids(&prog.post_inference_ir);

        let mut changed_main = Vec::new();
        let mut changed_predicate = 0usize;
        for (u, d, _) in &edges {
            if u == d {
                continue;
            }
            if up_main.contains(u) && down_main.contains(d) {
                changed_main.push((*u, *d));
            } else {
                changed_predicate += 1;
            }
        }
        assert!(
            changed_main.is_empty(),
            "a monomorphic program preserves every main-tree identity across \
             inference; these changed: {changed_main:?}"
        );
        assert!(
            changed_predicate > 0,
            "inference rebuilds this program's literal-singleton predicates, so \
             the pair must carry predicate-interior identity changes"
        );
    }
}
