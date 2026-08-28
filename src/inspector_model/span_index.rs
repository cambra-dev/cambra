//! The span → node index over one pane's IR tree.
//!
//! A pane's [`SourceProjection`](crate::ccl::provenance::SourceProjection) maps
//! each [`NodeId`] to the source spans it traces to (node → span). [`SpanIndex`]
//! is the inverse, span → node, which is the table the payload ships as a
//! pane's `spanIndex` and the consumer answers "what is at this source
//! position" over. The two are complementary projections of one
//! `(tree, projection)` pair; `span_index_round_trips_with_projection` pins that
//! they agree.

use crate::ccl::Expr;
use crate::ccl::provenance::{NodeId, SourceProjection};
use crate::chl_parser::ast::Span;
use std::collections::HashSet;

/// One node's entry in a [`SpanIndex`]: its id and one source span it is
/// indexed under.
#[derive(Clone, Copy, Debug)]
struct Entry {
    node: NodeId,
    span: Span,
}

/// Span → node index over one pane's IR tree.
///
/// Each node is indexed under **every** span its attribution records, so a node
/// that several source spans fan into is reachable from each of them. A node
/// with no spans (synthetic plumbing), or one the projection does not cover,
/// contributes no row.
///
/// # What the entries are
///
/// One `(span, node)` row per node per span its attribution records, in build
/// order (tree pre-order × each node's spans), and no `(span, node)` pair
/// twice. One source position sits inside
/// many nodes at once — in `x = 1 + 2` the position of the `1` is inside the
/// literal, inside the `+`, and inside the whole `let` — so a position matches
/// several rows.
///
/// The index neither orders nor narrows them. Which row a position resolves to,
/// and how a tie between byte-identical spans breaks, is the consumer's, over
/// the rows and the tree the payload ships alongside them: the tie-breaker is
/// tree depth, and the consumer walks that tree already. See
/// `src/inspector_model/design.md`, "The usage model".
#[derive(Clone, Debug, Default)]
pub struct SpanIndex {
    /// Every (node, span) pair, one per (node × span).
    entries: Vec<Entry>,
}

// Containment is the integer test `start <= pos < end`, so the table is a flat
// vector. Why not an interval tree or `intervalsets`:
// `src/inspector_model/design.md`, "Span containment is a scan".
impl SpanIndex {
    /// Build the index from a pane's tree and its [`SourceProjection`]. Each node
    /// is indexed under every span in its attribution; a node with no spans, or
    /// one the projection does not cover, contributes nothing.
    ///
    /// Each node is visited once. One refinement predicate is shared across
    /// every type slot that carries it, so a walk visiting it per slot would
    /// push its rows once per slot; a node indexed under several *distinct*
    /// spans still contributes one row per span.
    pub fn build(tree: &Expr, projection: &SourceProjection) -> Self {
        let mut entries = Vec::new();
        let mut visited = HashSet::new();
        Self::collect(tree, projection, &mut visited, &mut entries);
        SpanIndex { entries }
    }

    fn collect(
        expr: &Expr,
        projection: &SourceProjection,
        visited: &mut HashSet<NodeId>,
        out: &mut Vec<Entry>,
    ) {
        let node = expr.node_id();
        if !visited.insert(node) {
            return;
        }
        if let Some(attr) = projection.get(&node) {
            for &span in &attr.spans {
                out.push(Entry { node, span });
            }
        }
        expr.walk_children(|c| Self::collect(c, projection, visited, out));
        // Predicate interiors carry their own attributions, so a position inside
        // one has to reach it — see
        // [`predicate_children`](super::walk::predicate_children).
        for (_, predicate) in super::walk::predicate_children(expr) {
            Self::collect(predicate, projection, visited, out);
        }
    }

    /// Every `(span, node)` entry, one per (node × span) — the data behind the
    /// `spanIndex` array of the payload. Order is build order (tree
    /// pre-order × each node's spans), and a node indexed under several spans
    /// appears once per span — never twice under one span.
    pub fn entries(&self) -> impl Iterator<Item = (Span, NodeId)> + '_ {
        self.entries.iter().map(|e| (e.span, e.node))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::interpreter::Consumer;

    /// Compile a CHL program and return its post-inference tree + that pane's
    /// projection — the pair a [`SpanIndex`] is built over.
    fn compile_pane(code: &str) -> (Expr, SourceProjection) {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        let compiled = compile_program(&mut ctx, code, consumer).expect("program compiles");
        let projection = compiled
            .materialize_panes()
            .projection("post-inference")
            .clone();
        (compiled.post_inference_ir, projection)
    }

    /// The source every test here indexes: lowering seeds the statement-level
    /// `let x = …`, its RHS and the operands with source spans, so the index has
    /// real entries to resolve against.
    const CODE: &str = "\
x = 1 + 2
x
";

    /// Round-trip: every `(span, node)` entry names a node the pane's tree
    /// holds, and the pane projection lists that same span for that node. The
    /// inverse directions agree, over every row rather than one probe.
    #[test]
    fn span_index_round_trips_with_projection() {
        let (tree, projection) = compile_pane(CODE);
        let index = SpanIndex::build(&tree, &projection);

        /// Is `target` a node of this tree? Predicate interiors count: the index
        /// descends into them, so a row may name one.
        fn holds(expr: &Expr, target: NodeId) -> bool {
            expr.node_id() == target
                || expr.child_exprs().iter().any(|c| holds(c, target))
                || crate::inspector_model::walk::predicate_children(expr)
                    .iter()
                    .any(|(_, p)| holds(p, target))
        }

        let rows: Vec<_> = index.entries().collect();
        assert!(!rows.is_empty(), "the index has rows to check");
        for (span, node) in rows {
            assert!(
                holds(&tree, node),
                "row ({span:?}, {node:?}) names a node absent from the tree"
            );
            let spans = &projection
                .get(&node)
                .unwrap_or_else(|| panic!("indexed node {node:?} is known to the projection"))
                .spans;
            assert!(
                spans.contains(&span),
                "node→span must list the span the row indexed it under; \
                 row span {span:?}, node spans {spans:?}"
            );
        }
    }
}
