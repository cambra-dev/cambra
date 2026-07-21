//! The span → node index over one pane's IR tree.
//!
//! A pane's [`SourceProjection`](crate::ccl::provenance::SourceProjection) maps
//! each [`NodeId`] to the source spans it traces to (node → span). [`SpanIndex`]
//! is the inverse, span → node, which is what answers "what is at this source
//! position". The two are complementary projections of one
//! `(tree, projection)` pair; `span_index_round_trips_with_projection` pins that
//! they agree.

use std::collections::HashMap;

use crate::ccl::Expr;
use crate::ccl::provenance::{NodeId, SourceProjection};
use crate::chl_parser::ast::Span;

/// One node's entry in a [`SpanIndex`]: its id, the source span it is indexed
/// under, and its depth in the pane's tree (root = 0). Depth orders two entries
/// whose spans are byte-identical, where neither span is the more specific.
#[derive(Clone, Copy, Debug)]
struct Entry {
    node: NodeId,
    span: Span,
    depth: u32,
}

impl Entry {
    /// Width of the indexed span.
    fn extent(&self) -> usize {
        self.span.end.saturating_sub(self.span.start)
    }

    /// Does this entry's span contain `pos` (half-open: `[start, end)`)?
    ///
    /// A zero-width span (`start == end`) contains nothing under half-open
    /// semantics, so a synthetic point span never matches a position query.
    fn contains_pos(&self, pos: usize) -> bool {
        self.span.start <= pos && pos < self.span.end
    }

    /// Does this entry's span fully contain `query` (`query ⊆ span`)?
    /// A `query` whose width is zero is treated as the position `query.start`.
    fn contains_span(&self, query: Span) -> bool {
        if query.start == query.end {
            return self.contains_pos(query.start);
        }
        self.span.start <= query.start && query.end <= self.span.end
    }
}

/// Span → node containment index over one pane's IR tree.
///
/// Each node is indexed under **every** span its attribution records, so a node
/// that several source spans fan into is reachable from each of them. A node
/// with no spans (synthetic plumbing), or one the projection does not cover, is
/// absent from the index: a lookup answers nothing rather than panicking.
///
/// # What a lookup returns
///
/// One source position sits inside many nodes at once. In `x = 1 + 2` the
/// position of the `1` is inside the literal, inside the `+`, and inside the
/// whole `let`. So [`enclosing`](Self::enclosing) returns **every** node whose
/// span contains the position, and [`tightest`](Self::tightest) is the last of
/// them.
///
/// The order is least specific first: widest span first, then, for spans that
/// are byte-identical, shallowest node first. A consumer reads the result as a
/// drill-down — the first entry is the largest construct at that position and
/// the last is the smallest, which is the order a breadcrumb renders in.
///
/// The result is a **set** of nodes at a position, not one line of ancestors,
/// and two cases make that concrete. Byte-identical spans: a `def`'s `let` node
/// and the `λ` it binds both carry the whole statement span, and the `λ` is the
/// value at that position, so depth puts it last. Equally specific siblings:
/// monomorphization gives every specialization of one definition that
/// definition's source span, so several unrelated nodes tie. A consumer wanting
/// a single node therefore takes the last rather than assuming there is one, and
/// a consumer wanting every type at a position reads the whole set (see
/// `Snapshot::hover`).
#[derive(Clone, Debug, Default)]
pub struct SpanIndex {
    /// Every (node, span, depth) triple, one per (node × span).
    entries: Vec<Entry>,
}

// Containment is the integer test `start <= pos < end`, so a lookup filters and
// sorts the entry vector. One program's tree is small enough that this is not
// worth an interval tree, and lookups hand back node ids rather than exposing
// the entries, so a different backing structure stays a change behind this API.
// `intervalsets` is not used: it is built for numeric value domains and carries a
// `contains` bug on half-bounded intervals (see `interpreter/tiling.rs`).
impl SpanIndex {
    /// Build the index from a pane's tree and its [`SourceProjection`]. Each node
    /// is indexed under every span in its attribution; a node with no spans, or
    /// one the projection does not cover, contributes nothing.
    pub fn build(snapshot: &Expr, projection: &SourceProjection) -> Self {
        let mut entries = Vec::new();
        Self::collect(snapshot, projection, 0, &mut entries);
        SpanIndex { entries }
    }

    fn collect(expr: &Expr, projection: &SourceProjection, depth: u32, out: &mut Vec<Entry>) {
        let node = expr.node_id();
        if let Some(attr) = projection.get(&node) {
            for &span in &attr.spans {
                out.push(Entry { node, span, depth });
            }
        }
        expr.walk_children(|c| Self::collect(c, projection, depth + 1, out));
        // Predicate interiors carry their own attributions, so a span query has
        // to be able to land on one — see
        // [`predicate_children`](crate::inspector_model::query::predicate_children).
        for (_, predicate) in crate::inspector_model::query::predicate_children(expr) {
            Self::collect(predicate, projection, depth + 1, out);
        }
    }

    /// Every node whose span contains `pos`, least specific first — see
    /// [What a lookup returns](#what-a-lookup-returns).
    ///
    /// A node indexed under several spans that all contain `pos` appears once,
    /// positioned by its narrowest matching span.
    pub fn enclosing(&self, pos: usize) -> Vec<NodeId> {
        self.ordered_matches(|e| e.contains_pos(pos))
    }

    /// Every node whose span contains the whole `query` span, least specific
    /// first (see [`enclosing`](Self::enclosing)). A zero-width `query`
    /// degenerates to a lookup at the position `query.start`.
    pub fn enclosing_span(&self, query: Span) -> Vec<NodeId> {
        self.ordered_matches(|e| e.contains_span(query))
    }

    /// The most specific node containing `pos`, or `None` if no span contains it
    /// — the last of [`enclosing`](Self::enclosing).
    ///
    /// Where the narrowest span is shared, this picks one: the deepest node at
    /// that span (a `def`'s value `λ` over the `let` that binds it), and among
    /// nodes tied on span and depth, the one the tree walk reached last. A
    /// caller that must distinguish those reads the whole set instead.
    pub fn tightest(&self, pos: usize) -> Option<NodeId> {
        self.enclosing(pos).into_iter().next_back()
    }

    /// Every `(span, node)` entry, one per (node × span) — the data behind the
    /// `spanIndex` array of the snapshot payload. Order is build order (tree
    /// pre-order × each node's spans), and a node indexed under several spans
    /// appears once per span.
    pub fn entries(&self) -> impl Iterator<Item = (Span, NodeId)> + '_ {
        self.entries.iter().map(|e| (e.span, e.node))
    }

    /// Shared matching and ordering for the `enclosing*` lookups.
    fn ordered_matches(&self, mut matches: impl FnMut(&Entry) -> bool) -> Vec<NodeId> {
        let mut hits: Vec<&Entry> = self.entries.iter().filter(|e| matches(e)).collect();
        // Least specific first: wider span first, then shallower node, so a node
        // sharing its span with a descendant sorts ahead of that descendant.
        hits.sort_by(|a, b| {
            b.extent()
                .cmp(&a.extent())
                .then(a.depth.cmp(&b.depth))
                .then(a.span.start.cmp(&b.span.start))
        });
        // One entry per node, kept at its most specific (last) position.
        let mut last_pos: HashMap<NodeId, usize> = HashMap::new();
        for (i, e) in hits.iter().enumerate() {
            last_pos.insert(e.node, i);
        }
        hits.iter()
            .enumerate()
            .filter(|(i, e)| last_pos.get(&e.node) == Some(i))
            .map(|(_, e)| e.node)
            .collect()
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

    /// Round-trip: a position resolved to a node via `SpanIndex` (span → node)
    /// must resolve back through the pane projection (node → span) to a span
    /// that actually contains that position. The backward and forward
    /// directions agree.
    #[test]
    fn span_index_round_trips_with_projection() {
        let (tree, projection) = compile_pane(CODE);
        let index = SpanIndex::build(&tree, &projection);

        // The `1` literal sits at byte 4 ("x = 1 + 2" → '1' at offset 4).
        let pos = CODE.find('1').expect("literal 1 present");
        let node = index
            .tightest(pos)
            .expect("a node encloses the literal position");

        // node → span agrees with span → node: the resolved node's spans
        // include a span that contains the position we started from.
        let spans = &projection
            .get(&node)
            .expect("resolved node is known to the projection")
            .spans;
        assert!(
            spans.iter().any(|s| s.start <= pos && pos < s.end),
            "node→span must point back at a span containing pos {pos}; spans: {spans:?}"
        );
    }

    /// A position inside `1 + 2` returns every node containing it — the operand
    /// leaf and the nodes around it — with the least specific first.
    ///
    /// The claim under test is containment, not the sort: the first entry's span
    /// must strictly contain the last's, so an ordering that agreed with the
    /// comparator while indexing unrelated nodes would fail.
    #[test]
    fn enclosing_returns_every_containing_node_least_specific_first() {
        let (tree, projection) = compile_pane(CODE);
        let index = SpanIndex::build(&tree, &projection);

        // Position on the `1` operand: inside both the operand leaf and the
        // enclosing `+` BinOp (and the `let x = …` RHS).
        let pos = CODE.find('1').expect("literal 1 present");
        let chain = index.enclosing(pos);
        assert!(
            chain.len() >= 2,
            "a nested position returns the containment set (≥2 nodes), got {}: {chain:?}",
            chain.len()
        );

        // Each successive span is no wider than the previous one.
        let spans: Vec<_> = chain
            .iter()
            .map(|&n| {
                // Tightest matching span for this node.
                projection
                    .get(&n)
                    .expect("chain node is known")
                    .spans
                    .iter()
                    .filter(|s| s.start <= pos && pos < s.end)
                    .min_by_key(|s| s.end - s.start)
                    .copied()
                    .expect("node was indexed under a containing span")
            })
            .collect();
        for w in spans.windows(2) {
            let outer = w[0].end - w[0].start;
            let inner = w[1].end - w[1].start;
            assert!(
                inner <= outer,
                "least specific first: {:?} (extent {outer}) then {:?} (extent {inner})",
                w[0],
                w[1]
            );
        }

        // Containment, not merely ordering: the first span strictly contains the
        // last, so these are nested nodes at one position rather than a sorted
        // list of unrelated ones.
        let (first, last) = (spans[0], spans[spans.len() - 1]);
        assert!(
            first.start <= last.start && last.end <= first.end && first != last,
            "the least specific span must strictly contain the most specific: \
             {first:?} vs {last:?}"
        );

        // `tightest` is the last entry.
        assert_eq!(
            chain.last().copied(),
            index.tightest(pos),
            "tightest() is the last of enclosing()"
        );
    }

    /// A position outside every tagged span resolves to nothing — graceful, no
    /// panic.
    #[test]
    fn position_outside_all_spans_resolves_to_none() {
        let (tree, projection) = compile_pane(CODE);
        let index = SpanIndex::build(&tree, &projection);
        // Past the end of the source.
        assert!(index.tightest(CODE.len() + 100).is_none());
        assert!(index.enclosing(CODE.len() + 100).is_empty());
    }
}
