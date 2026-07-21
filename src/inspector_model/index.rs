//! The span→node index over the post-inference IR snapshot.
//!
//! This is the *backward* direction of the lineage projection: a pane's
//! [`SourceProjection`](crate::ccl::lineage::SourceProjection) maps a
//! [`NodeId`] forward to the source spans it traces to (node → span);
//! [`SpanIndex`] inverts that to answer "what nodes sit at this source
//! position" (span → node). The two are complementary projections of the same
//! `(snapshot, projection)` pair — see the round-trip in this module's tests.

use std::collections::HashMap;

use crate::ccl::Expr;
use crate::ccl::lineage::SourceProjection;
use crate::ccl::provenance::NodeId;
use crate::chl_parser::ast::Span;

/// A node's entry in the span index: its id, the origin span it is indexed
/// under, and its structural depth in the snapshot tree (root = 0). Depth is
/// the coincident-span tie-break: when two nodes carry byte-identical
/// spans, the deeper (descendant) node is the "innermost" one.
#[derive(Clone, Copy, Debug)]
struct Entry {
    node: NodeId,
    span: Span,
    depth: u32,
}

impl Entry {
    /// Width of the indexed origin span (the containment extent).
    fn extent(&self) -> usize {
        self.span.end.saturating_sub(self.span.start)
    }

    /// Does this entry's origin span contain `pos` (half-open: `[start, end)`)?
    ///
    /// A zero-width span (`start == end`) contains nothing under half-open
    /// semantics, so a synthetic point span never matches a position query.
    fn contains_pos(&self, pos: usize) -> bool {
        self.span.start <= pos && pos < self.span.end
    }

    /// Does this entry's origin span fully contain `query` (`query ⊆ span`)?
    /// A `query` whose width is zero is treated as the position `query.start`.
    fn contains_span(&self, query: Span) -> bool {
        if query.start == query.end {
            return self.contains_pos(query.start);
        }
        self.span.start <= query.start && query.end <= self.span.end
    }
}

/// Span → node containment index over the post-inference IR snapshot.
///
/// Built by walking the snapshot and indexing each node under *every* origin
/// span its provenance records (so a multi-origin fan-in node — N source spans
/// → one node — is reachable from each of those spans). Nodes with empty
/// origins (synthetic plumbing) and nodes the table does not know are simply
/// absent — graceful degradation, never a panic.
///
/// # Query model
///
/// The primitive is the **containment set/chain**, not a single node: span
/// containment is a nesting stack (`let ⊃ + ⊃ literal`), so
/// [`enclosing`](Self::enclosing) returns *all* nodes whose origin span contains
/// the position, ordered **outermost → innermost**. Ordering is by span extent
/// (wider = more enclosing = earlier); for coincident spans (byte-identical
/// extent — today the `def` case, where the `let f = …` node and its inner
/// `λ __arg_tuple_0 → …` node share the whole-statement span) the tie-break is
/// **structural depth** in the snapshot tree, so the deepest descendant sorts
/// last ("innermost"). [`tightest`](Self::tightest) is merely the tip of that
/// chain; that it must pick *one* among coincident spans is the query-layer
/// policy (innermost/deepest wins), not an index-level narrowing.
///
/// # Implementation: sorted-interval scan, not `intervalsets`
///
/// Span containment is the trivial integer test `start <= pos < end`, and the
/// snapshot is a single program's tree (small). A flat `Vec<Entry>` scanned per
/// query is simpler and obviously correct here; `intervalsets` is geared to
/// numeric value-domains (and carries a known `contains` bug on half-bounded
/// intervals, see `interpreter/tiling.rs`), so it buys nothing for this
/// integer-offset containment and is deliberately not used. Revisit only if the
/// snapshot grows large enough that a linear scan per query matters (it can be
/// swapped for an interval tree behind this same API).
#[derive(Clone, Debug, Default)]
pub struct SpanIndex {
    /// Every (node, origin-span, depth) triple, one per (node × origin span).
    entries: Vec<Entry>,
}

impl SpanIndex {
    /// Build the index from the snapshot tree and its pane [`SourceProjection`].
    /// Each node is indexed under every span in its attribution's `spans`; nodes
    /// with empty spans (machinery/synthetic) or absent from the projection
    /// contribute nothing.
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
    }

    /// All nodes whose origin span contains `pos`, ordered outermost → innermost
    /// (the containment chain). "Innermost" = narrowest span, with
    /// structural depth as the coincident-span tie-break (deepest last).
    ///
    /// Duplicate node ids are removed (a node indexed under several origin spans
    /// all containing `pos` appears once, under its tightest matching span).
    pub fn enclosing(&self, pos: usize) -> Vec<NodeId> {
        self.ordered_matches(|e| e.contains_pos(pos))
    }

    /// All nodes whose origin span contains the whole `query` span, ordered
    /// outermost → innermost (see [`enclosing`](Self::enclosing)). A zero-width
    /// `query` degenerates to a position query at `query.start`.
    pub fn enclosing_span(&self, query: Span) -> Vec<NodeId> {
        self.ordered_matches(|e| e.contains_span(query))
    }

    /// The tightest (innermost) node enclosing `pos`, or `None` if no origin
    /// span contains it. The tip of [`enclosing`](Self::enclosing).
    ///
    /// Coincident-span policy: when the innermost span is shared by several
    /// nodes (e.g. a `def`'s `let` and its value `λ`), the structurally deepest
    /// (the value-carrying descendant) wins. This is a deliberate query-layer
    /// choice, not a property of the spans themselves.
    pub fn tightest(&self, pos: usize) -> Option<NodeId> {
        self.enclosing(pos).into_iter().next_back()
    }

    /// Enumerate every `(span → node)` entry in the index, one per
    /// (node × origin span) — the raw data behind the `/api/snapshot`
    /// `spanIndex` array. Pure (no query position), order is index-build order
    /// (snapshot pre-order × each node's origins). A node indexed under several
    /// origin spans appears once per span, mirroring the index's internal shape.
    pub fn entries(&self) -> impl Iterator<Item = (Span, NodeId)> + '_ {
        self.entries.iter().map(|e| (e.span, e.node))
    }

    /// Shared matching + ordering for the `enclosing*` queries.
    fn ordered_matches(&self, mut matches: impl FnMut(&Entry) -> bool) -> Vec<NodeId> {
        let mut hits: Vec<&Entry> = self.entries.iter().filter(|e| matches(e)).collect();
        // Outermost → innermost: wider extent first; ties broken by shallower
        // structural depth first, so the deepest descendant (the true
        // "innermost" among coincident spans) sorts last.
        hits.sort_by(|a, b| {
            b.extent()
                .cmp(&a.extent())
                .then(a.depth.cmp(&b.depth))
                .then(a.span.start.cmp(&b.span.start))
        });
        // Dedup node ids while preserving the outermost→innermost order, keeping
        // each node at its tightest (last) matching position.
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
