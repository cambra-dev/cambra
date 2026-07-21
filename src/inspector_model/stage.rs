//! Pane-pair node→node links (the lineage map).
//!
//! The multi-pane inspector shows several pipeline stages side by side (CHL
//! source, pre-inference IR, post-inference IR, post-desugar IR, …) and links a
//! node in one pane to the node(s) it came from / became in the adjacent panes.
//! That link is the true lineage chain.
//!
//! The link is a [`LineageMap<NodeId, NodeId>`] folded at the pane boundary by
//! [`collapse`](crate::ccl::lineage::collapse) — one per adjacent pane pair,
//! materialized on [`CompiledProgram`](crate::ccl::context::CompiledProgram) via
//! `materialize_panes`. The map is **dense**: every id that survived the phase
//! is its own self-edge. Schema 3 ships the map **verbatim** — self-edges
//! included — so the frontend follows edges only (no identity special case); a
//! surviving node's cross-pane link is the shipped `[id, id]` self-edge, and a
//! genuine identity *change* (monomorphization / inline fan-out, channelize's
//! cluster/fan-in copies) is a `u != d` edge.

use crate::ccl::lineage::LineageMap;
use crate::ccl::provenance::NodeId;

/// Every edge of a pane-pair [`LineageMap`], as `(upstream, downstream)` `u64`
/// pairs — **dense**: self-edges (`u == d`, a node preserved across the phase)
/// are kept, so the frontend needs no identity special case.
///
/// [`LineageMap::edges`] already yields sorted, deduplicated edges (the dense
/// self-edges among them); this only projects the `NodeId`s to their wire `u64`.
pub fn dense_edges(map: &LineageMap<NodeId, NodeId>) -> Vec<(u64, u64)> {
    map.edges()
        .into_iter()
        .map(|(u, d)| (u.as_u64(), d.as_u64()))
        .collect()
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
    /// post-inference map (folded from the `Pass::Mono` lineage log) is dense —
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
        let edges = dense_edges(&panes.mono_map);

        assert!(!edges.is_empty(), "the pane-pair map has edges");
        assert!(
            edges.iter().any(|(u, d)| u == d),
            "the dense map ships self-edges for nodes preserved across the phase"
        );

        // At least one upstream node fans out to ≥2 distinct downstream nodes
        // (dup used at Int and Bool) — counting only the genuine identity
        // changes, not the self-edges.
        let mut fanout: std::collections::HashMap<u64, usize> = std::collections::HashMap::new();
        for (u, d) in &edges {
            if u != d {
                *fanout.entry(*u).or_default() += 1;
            }
        }
        assert!(
            fanout.values().any(|&n| n >= 2),
            "dup used at two types should fan out to ≥2 downstream nodes; edges={edges:?}"
        );
    }

    /// A two-site inline fan-out surfaces as non-identity edges on the
    /// post-inference → post-desugar map, each edge's upstream a post-inference
    /// node and downstream a post-desugar node.
    #[test]
    fn inline_fanout_links_post_inference_to_post_desugar_copies() {
        let code = "\
add1 = \\x -> x + 1
a = add1(10)
b = add1(20)
a + b
";
        let prog = compile(code);
        let panes = prog.materialize_panes();
        let edges = dense_edges(&panes.desugar_map);

        fn ids(e: &crate::ccl::Expr) -> std::collections::HashSet<u64> {
            let mut s = std::collections::HashSet::new();
            fn go(e: &crate::ccl::Expr, s: &mut std::collections::HashSet<u64>) {
                s.insert(e.node_id().as_u64());
                e.walk_children(|c| go(c, s));
            }
            go(e, &mut s);
            s
        }
        let up_ids = ids(&prog.post_inference_ir);
        let down_ids = ids(&prog.post_desugar_ir);
        assert!(
            !edges.is_empty(),
            "a two-site inline fan-out must produce non-identity stage edges"
        );
        for (u, d) in &edges {
            assert!(
                up_ids.contains(u),
                "edge upstream id {u} must be a node in the post-inference tree"
            );
            assert!(
                down_ids.contains(d),
                "edge downstream id {d} must be a node in the post-desugar tree"
            );
        }
    }

    /// A monomorphic program's mono boundary is identity-only: the dense map has
    /// edges (the surviving nodes' self-edges), and every one is a self-edge —
    /// no genuine identity change.
    #[test]
    fn monomorphic_program_mono_map_is_identity_only() {
        let code = "\
x = 1 + 2
x
";
        let prog = compile(code);
        let panes = prog.materialize_panes();
        let edges = dense_edges(&panes.mono_map);
        assert!(
            !edges.is_empty(),
            "a compiled program has surviving nodes, hence dense self-edges"
        );
        for (u, d) in &edges {
            assert_eq!(
                u, d,
                "a monomorphic program's mono map ships only self-edges"
            );
        }
    }
}
