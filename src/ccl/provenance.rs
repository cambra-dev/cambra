//! Node identities, rewrite recording and source attribution.
//!
//! Each produced node has at most one provenance row. Mint and copy hooks populate
//! the innermost recording; closing it writes captured products to the active sink.
//! `parents` records ancestry and `blame` records additional attribution. Neither
//! column declares whether an input node survives.
//!
//! [`fold`] relates selected phases' input and output IDs and derives source
//! attribution, deaths and recording leaks. Lowering attaches literal source
//! spans and uses the sequential [`fold_lowering`].
//!
//! The reference owns the cross-component contracts: `src/ccl/design/provenance.md`,
//! "Node identity", "The provenance model", "The recorder" and "The fold".
//! `crate::ccl::context` installs pipeline sessions; `crate::ccl::panes` defines
//! pane topology and materialization.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::ccl::context::Phase;
use crate::chl_parser::ast::Span;

// ===========================================================================
// Node identity: the two primitives every row below is keyed and tagged by.
//
// A `NodeId` says *which node*, a `Phase` says *which stage rewrote it*. Both are
// data a row carries rather than types anything is parameterized over, which is
// why they live beside the table instead of behind an interface.
// ===========================================================================

/// An expression or operator identity allocated from a process-global counter.
///
/// [`NodeId::fresh`] uses a separate counter from binder [`Uid`](crate::ccl::names::Uid).
/// IDs are map keys, and [`fold`] uses their order to traverse produced-node dependencies.
/// Serialized numbers are handles, not stable names across compilations.
///
/// `TypedExpr::PartialEq` excludes `node_id`: structurally equal expressions with
/// different provenance compare equal. `TypedExpr` has no value-hashing implementation;
/// this type's `Hash` is for identity-keyed collections.
/// See `src/ccl/design/provenance.md`, "Node identity".
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(u64);

static FRESH_NODE_ID: AtomicU64 = AtomicU64::new(1);

impl NodeId {
    /// Sentinel for `Default`/`mem::take` placeholders and diagnostic throwaways.
    ///
    /// Zero is never allocated by the counter. Construction at this ID and the
    /// mint/copy hooks record no birth. It must not remain in the main tree;
    /// `assert_unique_node_ids` checks that condition in debug/test builds.
    pub(crate) const PLACEHOLDER: NodeId = NodeId(0);

    /// Allocate a fresh identity without calling the expression construction hooks.
    pub fn fresh() -> Self {
        NodeId(FRESH_NODE_ID.fetch_add(1, Ordering::Relaxed))
    }

    /// The numeric handle used by the inspector wire representation.
    ///
    /// It exposes identity, not a stable program position. Allocation counts affect
    /// later handles; internal folds also use mint order to resolve dependencies.
    pub fn as_u64(self) -> u64 {
        self.0
    }
}

/// An error with the identity of the node where it was raised.
///
/// Pipeline error reporting resolves this identity through the available source
/// projection. Keeping the location beside `E` leaves the underlying error
/// location-free and comparable independently of attribution.
#[derive(Debug, Clone, PartialEq)]
pub struct Located<E> {
    /// The underlying error.
    pub error: E,
    /// The node the error was raised at.
    pub node_id: NodeId,
}

impl<E> Located<E> {
    /// `error` raised at `node_id`.
    pub fn new(error: E, node_id: NodeId) -> Self {
        Located { error, node_id }
    }
}

impl std::fmt::Debug for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NodeId({})", self.0)
    }
}

// Serialize the identity as a bare JSON number, matching `as_u64`.
// TODO(wire-stability): allocation-count changes renumber later fixture handles.
// A serialization-layer walk could assign deterministic first-encounter indices
// without changing internal IDs. That remapping is not implemented.
impl serde::Serialize for NodeId {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_u64(self.0)
    }
}

/// A stable, human-readable name for a rewrite, e.g. `"channelize.cluster"` or
/// `"inline.beta"`. Fixed at the recording site, interned into every row's
/// [`RewriteTag`], and surfaced from there for inspector tooltips.
pub type RewriteLabel = &'static str;

/// The fidelity of a node to its blamed source — the one fact the folded
/// graph cannot recover. A trinary axis.
///
/// **Work in progress.** This axis exists to carry display metadata to the
/// inspector frontend, and neither the vocabulary nor the tagging is settled: the
/// three variants are a first cut and the rule assigning them is deliberately
/// structural for now (below). Treat a node's nature as a hint the frontend may
/// present, not as a fact any compiler decision should turn on — nothing in
/// `ccl/` branches on it today, and the per-site `label` is the durable datum.
/// Retagging is cheap precisely because of that: a label-keyed remap can
/// recompute a different taxonomy without touching how any phase records.
///
/// Public because it rides in the public [`RewriteTag`] (and thus
/// [`SourceAttribution`]); a [`LoweringStep::Leaf`] carries one too.
///
/// [`Source`](Nature::Source) is listed first because it is the base case: the
/// root of a lowered source expression. The rule for who gets it is *structural*
/// and stated in one place — see `LoweringContext::tag_source` in
/// `src/ccl/lower/mod.rs`, and `design/provenance.md`, "The seam". It is emitted
/// **only by lowering**: [`attribute`]
/// debug-asserts that no *phase* rewrite carries it, and that is the one guard.
/// On the wire a `Source`-nature tag null-compresses
/// (serializes as
/// `rewritten: null` via [`is_source`](Nature::is_source)) so the wire stays
/// byte-identical to the retired `rewritten: None` encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Nature {
    /// The node is the root of a lowered source expression. Lowering-only;
    /// guarded off the phase rows and off the wire. Note this is a *positional*
    /// fact, not "images something the user wrote" — an interior image (a call's
    /// callee, a chained comparison's operands) carries `Machinery` with the
    /// `"lower.image"` label instead.
    Source,
    /// Faithful expansion of a source construct (an inlined UDF body, a
    /// transaction's writer, a channelized defer cluster). Recorded by phases,
    /// never by lowering, whose expansions carry `Machinery` with a per-rule
    /// label.
    Expansion,
    /// Pure plumbing with no direct source counterpart.
    Machinery,
}

impl Nature {
    /// The lowercase wire discriminant (`"source"` / `"expansion"` /
    /// `"machinery"`) a payload tree node's `rewritten` tag carries.
    ///
    /// `"source"` never reaches the wire: the sole emission path branches on
    /// [`is_source`](Self::is_source) first and writes `null` instead. The arm
    /// exists for completeness.
    pub(crate) fn wire_str(self) -> &'static str {
        match self {
            Nature::Source => "source",
            Nature::Expansion => "expansion",
            Nature::Machinery => "machinery",
        }
    }

    /// Whether this is the [`Source`](Self::Source) direct-image nature — the
    /// wire null-compression predicate. A node whose attribution tag
    /// `is_source()` ships `rewritten: null`.
    pub(crate) fn is_source(self) -> bool {
        matches!(self, Nature::Source)
    }
}

/// Lowering's log entry, in the two shapes lowering actually has.
///
/// Its attribution channel is a literal source **span**, attached here at
/// construction because lowering knows the source token it is imaging right
/// there. A [`ProvenanceTable`] row's `blame`, by contrast, is a NodeId
/// *reference* resolved later through the accumulating projection: a phase names
/// an upstream id whose spans it does not itself hold. Attached-literal and
/// resolved-through-state are different semantics, not two instances of one
/// thing, which is why lowering records into its own log rather than into the
/// table — and thread-local statics cannot be generic, so an
/// attribution-domain generic would erase to the same thing at the recorder
/// boundary anyway. There is no NodeId-blame channel here: the one site that
/// would name an upstream id — a substitution, whose replacement takes the
/// replaced occurrence's attribution — carries the occurrence's identity instead
/// (`crate::ccl::subst`'s `as_expr_preserving`), so there is no id left to
/// resolve. Add one when a site demands it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LoweringStep {
    /// A **leaf mint**: one node, imaged at one span. Lowering's ordinary
    /// record — it mints from scratch, so a leaf has no ancestor and is
    /// a node plus the span it images, and nothing else.
    Leaf {
        /// The node this record is about.
        id: NodeId,
        /// The literal source span it images.
        anchor: Span,
        /// `Source` for a lowered expression's root, `Machinery` for an interior
        /// image or manufactured plumbing (`Expansion` is unused at lowering
        /// sites — the split folds into `Machinery`, the per-rule label being
        /// the primary datum).
        nature: Nature,
        /// Stable rewrite label for tooling (`"lower.image"`, `"lower.<rule>"`).
        label: RewriteLabel,
    },
    /// A **copy**: `produced` are freshened duplicates of `origin` and mirror
    /// its folded entry verbatim. It carries no anchor, nature or label because
    /// the fold reads none of them — uncurry's template interiors and the
    /// compare-chain's second-use operands are exactly their origins' images, so
    /// a tag here would be an unobservable value, and a wrong one would look
    /// meaningful while being inert.
    Copy {
        /// The node whose folded entry the copies mirror. Must be recorded by an
        /// earlier record, else [`Leak::DanglingParent`].
        origin: NodeId,
        /// The freshened duplicates.
        produced: Vec<NodeId>,
    },
}

/// Lowering's ordered record. Appended at leaf grain by [`lowering_leaf`] and by
/// the copy-capturing recordings [`copy_frame`] opens; folded once at the
/// lowering boundary by [`fold_lowering`] into the always-on lowering
/// projection.
pub(crate) type LoweringLog = Vec<LoweringStep>;

/// The lowering log, plus the set of [`NodeId`]s it has already explained.
///
/// The set exists for one caller: [`lowering_predicate_leaf`], which sweeps a
/// finished refinement predicate and must **not** re-record a node that already
/// carries precise attribution from its own lowering. The fold is
/// last-write-wins, so a blanket sweep would silently replace a node's real span
/// and label with the coarse predicate ones — a loss no leak class can see,
/// because the node stays explained either way.
#[derive(Default)]
struct LoweringRecord {
    log: LoweringLog,
    recorded: HashSet<NodeId>,
}

/// Nonempty set of ancestry and blame labels for one endpoint pair.
///
/// A parent hop contributes ancestry; a blame hop contributes relatedness without
/// ancestry. [`then`](Self::then) composes paths and [`union`](Self::union)
/// combines alternative paths. See `src/ccl/design/provenance.md`, "The edge labels".
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EdgeLabels {
    ancestry: bool,
    blame: bool,
}

impl EdgeLabels {
    /// Ancestry-only hop and the identity for path composition.
    pub const ANCESTRY: Self = EdgeLabels {
        ancestry: true,
        blame: false,
    };

    /// Blame-only hop, without an ancestry claim.
    pub const BLAME: Self = EdgeLabels {
        ancestry: false,
        blame: true,
    };

    /// Whether the pair is in the ancestry relation.
    pub fn has_ancestry(self) -> bool {
        self.ancestry
    }

    /// Whether the pair is in the blame relation.
    pub fn has_blame(self) -> bool {
        self.blame
    }

    /// Compose path labels: ancestry requires both operands; blame requires either.
    /// Associative, with [`ANCESTRY`](Self::ANCESTRY) as identity.
    #[must_use]
    pub fn then(self, hop: Self) -> Self {
        EdgeLabels {
            ancestry: self.ancestry && hop.ancestry,
            blame: self.blame || hop.blame,
        }
    }

    /// Both readings of two paths that reach the same endpoint pair.
    #[must_use]
    pub fn union(self, other: Self) -> Self {
        EdgeLabels {
            ancestry: self.ancestry || other.ancestry,
            blame: self.blame || other.blame,
        }
    }
}

/// The opposite endpoint of an edge and its label set.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Link<T> {
    /// The id at the far end of the edge.
    pub id: T,
    /// What the edge to it asserts.
    pub labels: EdgeLabels,
}

/// Bidirectional relation with one label set per endpoint pair.
///
/// The phase fold includes ancestry self-edges for unchanged input IDs.
/// Accessors expose those edges alongside rewritten-node edges; callers need
/// not reconstruct identity edges. Both directions are stored with sorted
/// adjacency lists. See `src/ccl/design/provenance.md`, "The fold".
pub struct ProvenanceMap<U, D> {
    /// upstream → labelled downstream (fan-out).
    down: HashMap<U, Vec<Link<D>>>,
    /// downstream → labelled upstream (origins).
    up: HashMap<D, Vec<Link<U>>>,
}

impl<U, D> ProvenanceMap<U, D>
where
    U: Eq + Hash + Copy + Ord,
    D: Eq + Hash + Copy + Ord,
{
    /// The upstream origins of a downstream id, each with what its edge asserts
    /// (empty if the id is unknown to the map). Sorted by id, one entry per
    /// origin.
    pub fn upstream(&self, d: &D) -> &[Link<U>] {
        self.up.get(d).map_or(&[], Vec::as_slice)
    }

    /// The downstream fan-out of an upstream id, each with what its edge asserts
    /// (empty if the id is unknown to the map). Sorted by id, one entry per
    /// target.
    pub fn downstream(&self, u: &U) -> &[Link<D>] {
        self.down.get(u).map_or(&[], Vec::as_slice)
    }

    /// Every edge as `(upstream, labelled downstream)`, in deterministic order.
    /// Includes the dense self-edges.
    pub fn edges(&self) -> Vec<(U, Link<D>)> {
        let mut out: Vec<(U, Link<D>)> = self
            .up
            .iter()
            .flat_map(|(d, us)| {
                us.iter().map(move |u| {
                    (
                        u.id,
                        Link {
                            id: *d,
                            labels: u.labels,
                        },
                    )
                })
            })
            .collect();
        out.sort_unstable();
        out
    }
}

/// Source spans and a rewrite tag associated with a node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceAttribution {
    /// Known source spans. An empty vector is a present attribution with no known
    /// anchor, distinct from an ID absent from [`SourceProjection`].
    pub spans: Vec<Span>,
    /// The producing rewrite, or [`RewriteTag::direct_image`] for a lowered root.
    /// Mandatory internally; the inspector encodes a Source-nature tag as null.
    pub rewritten: RewriteTag,
}

/// Producing phase and site-selected nature and label.
///
/// The table interns the whole triple. A phase scope supplies `via`; the
/// recording site supplies `nature` and `label`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RewriteTag {
    /// The phase that performed the rewrite.
    pub via: Phase,
    /// Faithful expansion vs. pure machinery vs. direct source image.
    pub nature: Nature,
    /// The rewrite's stable label.
    pub label: RewriteLabel,
}

impl RewriteTag {
    /// The tag for a lowered source expression's root. Interior images can use the
    /// same label with `Nature::Machinery`; they do not use this constructor.
    pub fn direct_image() -> Self {
        RewriteTag {
            via: Phase::Lower,
            nature: Nature::Source,
            label: "lower.image",
        }
    }
}

/// Node attribution at a pipeline boundary. The lowering projection is always
/// computed; downstream projections are materialized by [`fold`] when requested
/// by a consumer or the compile-time leak gate.
pub type SourceProjection = HashMap<NodeId, SourceAttribution>;

/// A recording-integrity failure detected by a fold.
///
/// One missing mint can cause either class or both. Folds deduplicate by class
/// and ID; neither class alone identifies the recording site to fix. Deaths
/// are separate set-difference products, and live-ID duplication is checked by
/// the tree-identity checks. See `src/ccl/design/provenance.md`, "Recording leaks".
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Leak {
    /// An output ID is neither an input ID nor a product known to the fold.
    Unrecorded { output: NodeId },
    /// A recorded ancestry hop names an ID unknown to the fold. Phase folding
    /// checks all selected rows, not just rows reachable from surviving products.
    /// Unknown blame-only endpoints do not produce this leak.
    DanglingParent { parent: NodeId },
}

/// Attribute a recorded node using its row's tag and upstream spans.
///
/// Spans are deduplicated in first-seen order, parents before blame. Unknown
/// source IDs contribute nothing; the returned entry may have no spans.
/// See `src/ccl/design/provenance.md`, "Source attribution".
fn attribute(
    table: &ProvenanceTable,
    id: NodeId,
    tag: RewriteTag,
    attr: &SourceProjection,
) -> SourceAttribution {
    // Source tags originate in lowering. Preserved IDs inherit them without
    // passing through this helper; newly produced phase nodes must not use one.
    debug_assert!(
        !tag.nature.is_source(),
        "a phase rewrite carries Nature::Source (label {:?}, via {:?}) — \
         Source is emitted only by lowering",
        tag.label,
        tag.via,
    );
    let mut spans: Vec<Span> = Vec::new();
    for src in table.parents(id).iter().chain(table.blame(id)) {
        if let Some(a) = attr.get(src) {
            for sp in &a.spans {
                if !spans.contains(sp) {
                    spans.push(*sp);
                }
            }
        }
    }
    SourceAttribution {
        spans,
        rewritten: tag,
    }
}

/// Distinct upstream IDs with labels from both columns, parents first.
/// An ID present in both columns contributes one hop with both labels.
fn row_hops(table: &ProvenanceTable, x: NodeId) -> Vec<(NodeId, EdgeLabels)> {
    let mut hops: Vec<(NodeId, EdgeLabels)> = Vec::new();
    let named = (table.parents(x).iter().map(|p| (*p, EdgeLabels::ANCESTRY)))
        .chain(table.blame(x).iter().map(|b| (*b, EdgeLabels::BLAME)));
    for (id, label) in named {
        match hops.iter_mut().find(|(h, _)| *h == id) {
            Some((_, labels)) => *labels = labels.union(label),
            None => hops.push((id, label)),
        }
    }
    hops
}

/// Fold selected phase rows into a bidirectional relation, output attribution,
/// sorted input-minus-output deaths and sorted, deduplicated leaks.
///
/// Input IDs without selected rows are roots; earlier-phase rows are not
/// followed past this boundary. Such roots are pre-seeded regardless of ID order.
/// A dependency between two selected products must point from smaller to larger
/// ID (debug-asserted). This permits one ascending sweep independent of row
/// insertion order.
///
/// A recorded vertex with no reachable input retains an empty root map; an
/// unknown output has no entry and produces [`Leak::Unrecorded`]. All selected
/// rows are checked for dangling parents, including discarded products.
///
/// See `src/ccl/design/provenance.md`, "The fold", "The fold is order-free",
/// "Source attribution" and "Recording leaks".
pub(crate) fn fold(
    table: &ProvenanceTable,
    phases: &[Phase],
    input_ids: &HashSet<NodeId>,
    output_ids: &HashSet<NodeId>,
    upstream_attr: &SourceProjection,
) -> (
    ProvenanceMap<NodeId, NodeId>,
    SourceProjection,
    Vec<NodeId>,
    Vec<Leak>,
) {
    let mut leaks: Vec<Leak> = Vec::new();

    // Input roots and selected products form the complete vertex set.
    let mut vertices: Vec<NodeId> = table
        .rows_in(phases)
        .chain(input_ids.iter().copied())
        .collect();
    vertices.sort_unstable();
    vertices.dedup();

    let mut roots: HashMap<NodeId, HashMap<NodeId, EdgeLabels>> = HashMap::new();
    let mut attr: SourceProjection = upstream_attr.clone();

    // Input-boundary roots may be newer than products (for example, reused
    // operators). Seed them before the ordered sweep of selected products.
    for &x in &vertices {
        if table.tag_in(x, phases).is_none() {
            roots.insert(x, HashMap::from([(x, EdgeLabels::ANCESTRY)]));
        }
    }

    for &x in &vertices {
        let Some(tag) = table.tag_in(x, phases) else {
            // Its root and attribution were seeded before the sweep.
            continue;
        };

        let mut r: HashMap<NodeId, EdgeLabels> = HashMap::new();
        for (p, hop) in row_hops(table, x) {
            debug_assert!(
                p < x || table.tag_in(p, phases).is_none(),
                "row {x:?} names the younger id {p:?} as an upstream, and this fold \
                 produces {p:?} too — ascending NodeId order must be a topological order \
                 of what the fold produces, so a rewrite must read an id before it mints \
                 one",
            );
            // Missing ancestry is a leak; unknown blame contributes neither
            // a relation nor an error. Empty known roots remain distinct from absence.
            match roots.get(&p) {
                Some(pr) => {
                    for (root, path) in pr {
                        let composed = path.then(hop);
                        r.entry(*root)
                            .and_modify(|l| *l = l.union(composed))
                            .or_insert(composed);
                    }
                }
                None if hop.has_ancestry() => leaks.push(Leak::DanglingParent { parent: p }),
                None => {}
            }
        }
        roots.insert(x, r);

        let a = attribute(table, x, tag, &attr);
        attr.insert(x, a);
    }

    // Emit. Each output id's labelled roots become its up-edges (and the
    // mirrored down-edges); sorted for determinism.
    let mut down: HashMap<NodeId, Vec<Link<NodeId>>> = HashMap::new();
    let mut up: HashMap<NodeId, Vec<Link<NodeId>>> = HashMap::new();
    for o in output_ids {
        match roots.get(o) {
            Some(origins) => {
                let mut origins: Vec<Link<NodeId>> = origins
                    .iter()
                    .map(|(u, labels)| Link {
                        id: *u,
                        labels: *labels,
                    })
                    .collect();
                origins.sort_unstable();
                for link in &origins {
                    down.entry(link.id).or_default().push(Link {
                        id: *o,
                        labels: link.labels,
                    });
                }
                up.insert(*o, origins);
            }
            // Neither an input-pane id nor produced by any row the fold read.
            None => leaks.push(Leak::Unrecorded { output: *o }),
        }
    }
    for ds in down.values_mut() {
        ds.sort_unstable();
    }

    // Deaths depend on boundary membership, not on rows' ancestry claims.
    let mut deaths: Vec<NodeId> = input_ids.difference(output_ids).copied().collect();
    deaths.sort_unstable();

    // Discard intermediate attributions. A missing entry remains different
    // from a present attribution with an empty span vector.
    let projection: SourceProjection = output_ids
        .iter()
        .filter_map(|o| attr.get(o).map(|a| (*o, a.clone())))
        .collect();

    // Several rows can name the same missing parent.
    leaks.sort_unstable();
    leaks.dedup();

    (ProvenanceMap { down, up }, projection, deaths, leaks)
}

/// Counts for the selected fold graph, without computing its closure.
/// Backward edges violate the selected-product ordering; the count does not
/// measure vertices to revisit or the cost of an alternative algorithm.
#[cfg(test)]
pub(crate) struct SweepMetrics {
    /// Distinct input IDs and selected products; also the final roots-map size.
    pub vertices: usize,
    /// Provenance edges (`upstream → node`, either label) the fold reads.
    pub edges: usize,
    /// Hops whose upstream is also selected and has an ID greater than or equal
    /// to the product's ID. Pre-seeded input roots are excluded.
    pub backward_edges: usize,
}

/// Measure the cost without folding: enumerate the same vertices and edges
/// [`fold`] sweeps and count any edge that runs backwards.
#[cfg(test)]
pub(crate) fn sweep_metrics(
    table: &ProvenanceTable,
    phases: &[Phase],
    input_ids: &HashSet<NodeId>,
) -> SweepMetrics {
    let mut vertices: HashSet<NodeId> = table.rows_in(phases).collect();
    vertices.extend(input_ids.iter().copied());
    let (mut edges, mut backward_edges) = (0usize, 0usize);
    for x in table.rows_in(phases) {
        for (p, _) in row_hops(table, x) {
            edges += 1;
            if p >= x && table.tag_in(p, phases).is_some() {
                backward_edges += 1;
            }
        }
    }
    SweepMetrics {
        vertices: vertices.len(),
        edges,
        backward_edges,
    }
}

/// Fold a [`LoweringLog`] into the always-on **lowering projection** and any
/// integrity [`Leak`]s. The lowering counterpart to [`fold`], and the one
/// fold that is **sequential**: its log genuinely is chronology (leaf entries
/// are appended at construction, not when a guard drops), and its last-tag-wins
/// re-imaging is real semantics rather than an artifact of reading a log as a
/// sequence. Four simplifications follow from lowering minting from scratch:
///
/// * **no input pane** — so there is no ancestry to compose. Where [`fold`]
///   carries a set of input-pane roots per id, here every such set would be
///   empty, and what is left of it is a plain **live set**: the ids some record
///   has covered;
/// * **no [`ProvenanceMap`] output** — the lowering projection ships as pane-0
///   spans, not edges, so there is no `up`/`down` to build and no deaths to
///   report (there are no input ids to drop);
/// * **no attribution state to resolve through** — a leaf's attribution is
///   `{spans: [anchor], RewriteTag}` built directly here from its literal span; a
///   copy mirrors its origin's already-folded entry;
/// * **no one-row-per-id requirement** — a re-image is a second record for one
///   id (`lower_expr` re-tags an arm's already-tagged root as the construct's
///   direct image) and the later tag deliberately wins.
///
/// Runs always-on at the lowering→pipeline handoff (the leak *checks* stay
/// debug/test-gated at the boundary). [`Leak::Unrecorded`] is an unrecorded mint
/// (an output-tree node that no leaf produced and no copy placed);
/// [`Leak::DanglingParent`] is a copy of an origin no earlier record covered; a
/// template id born, copied, and never placed composes away (live but not an
/// output, so no leak); orphaned keys are structurally impossible (the projection
/// is produced by the fold, never mutated).
pub(crate) fn fold_lowering(
    log: &LoweringLog,
    output_ids: &HashSet<NodeId>,
) -> (SourceProjection, Vec<Leak>) {
    let mut live: HashSet<NodeId> = HashSet::new();
    let mut leaks: Vec<Leak> = Vec::new();
    let mut attr: SourceProjection = SourceProjection::new();

    for step in log {
        match step {
            LoweringStep::Leaf {
                id,
                anchor,
                nature,
                label,
            } => {
                live.insert(*id);
                // Attribution comes straight from the literal anchor — no
                // resolution through state, because lowering knows the source
                // token right here.
                attr.insert(
                    *id,
                    SourceAttribution {
                        spans: vec![*anchor],
                        rewritten: RewriteTag {
                            via: Phase::Lower,
                            nature: *nature,
                            label,
                        },
                    },
                );
            }
            LoweringStep::Copy { origin, produced } => {
                // A copy mirrors its origin's already-folded entry verbatim (the
                // compare-chain second-use operand and the uncurry template
                // interiors are exactly their origins' images/plumbing).
                if !live.contains(origin) {
                    leaks.push(Leak::DanglingParent { parent: *origin });
                    continue;
                }
                live.extend(produced.iter().copied());
                if let Some(origin_attr) = attr.get(origin).cloned() {
                    for p in produced {
                        attr.insert(*p, origin_attr.clone());
                    }
                }
            }
        }
    }

    // Every output-tree node must be explained (produced by a leaf or a copy).
    // An unexplained output is an unrecorded lowering mint; this leak IS the
    // coverage check (there is no separate gate). There are no deaths to report
    // (no input pane).
    for o in output_ids {
        if !live.contains(o) {
            leaks.push(Leak::Unrecorded { output: *o });
        }
    }

    let projection: SourceProjection = output_ids
        .iter()
        .filter_map(|o| attr.get(o).map(|a| (*o, a.clone())))
        .collect();

    // One entry per distinct defect, as in [`fold`].
    leaks.sort_unstable();
    leaks.dedup();

    (projection, leaks)
}

// Table storage and tag interning.

/// Table-local index of an interned `{via, nature, label}` triple.
///
/// Shared helpers can use the same label under different phases, producing
/// distinct tags. The index addresses this table's tag vector, not a global
/// rule registry. A recording's births and copies share the same interned tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct TagId(u32);

/// One node's ancestry, additional attribution and interned rewrite tag.
struct Row {
    parents: Vec<NodeId>,
    blame: Vec<NodeId>,
    tag: TagId,
}

/// Per-compile rows keyed by produced node identity.
///
/// Each row separates ancestry (`parents`) from additional attribution (`blame`).
/// Both contribute source spans during folding; only parents assert ancestry.
/// Spans are derived from upstream attribution, not stored in the row.
///
/// Unknown IDs are permitted: edge accessors return empty slices and tag accessors
/// return `None`. Enumeration includes recorded rows only. Predicate interiors use
/// the same representation as main-tree nodes.
///
/// See `src/ccl/design/provenance.md`, "The provenance model" and
/// "Table access and write invariants" for row semantics and write preconditions.
#[derive(Default)]
pub(crate) struct ProvenanceTable {
    rows: HashMap<NodeId, Row>,
    /// Tag by [`TagId`] index — the interning table's forward direction.
    tags: Vec<RewriteTag>,
    /// Tag → its already-assigned id, so equal tags share one row column.
    interned: HashMap<RewriteTag, TagId>,
}

// `tag_id`, `contains`, `deaths`, `len`, and `tag_count` are used only by tests.
#[allow(dead_code)]
impl ProvenanceTable {
    /// The [`TagId`] for `tag` in this table, assigning one on first sight.
    ///
    /// Interning is separate from [`record`](Self::record) because one closing
    /// guard writes many rows under one tag: the caller interns once and hands
    /// the handle to each row.
    pub(crate) fn intern_tag(&mut self, tag: RewriteTag) -> TagId {
        if let Some(id) = self.interned.get(&tag) {
            return *id;
        }
        // Distinct phase/nature/label triples are bounded by the compiler's recording sites,
        // not by the size of the program being compiled, so their count fits in u32.
        let id = TagId(
            u32::try_from(self.tags.len()).expect("more distinct rewrite tags than a u32 indexes"),
        );
        self.tags.push(tag);
        self.interned.insert(tag, id);
        id
    }

    /// Record a produced node. Debug-asserts that `id` has no row, at least one
    /// of `parents` or `blame` is nonempty, and `id` is not its own parent.
    ///
    /// The caller must satisfy these preconditions in every build; insertion
    /// overwrites an existing row when debug assertions are disabled. A preserve
    /// writes no row. A pure insertion may use blame without parents.
    pub(crate) fn record(&mut self, id: NodeId, parents: &[NodeId], blame: &[NodeId], tag: TagId) {
        debug_assert!(
            !self.rows.contains_key(&id),
            "node {id:?} already has a provenance row — a rewrite claims to have minted an id \
             that already exists, and attribution has no join to resolve the two claims with"
        );
        debug_assert!(
            !parents.is_empty() || !blame.is_empty(),
            "node {id:?} has neither a parent nor a blamed id — every record must anchor its \
             node through some channel: consumption or blame"
        );
        debug_assert!(
            !parents.contains(&id),
            "node {id:?} is its own parent — a rewrite cannot consume what it produces"
        );
        self.rows.insert(
            id,
            Row {
                parents: parents.to_vec(),
                blame: blame.to_vec(),
                tag,
            },
        );
    }

    /// The ancestry IDs of `id`, or an empty slice when it has no row.
    pub(crate) fn parents(&self, id: NodeId) -> &[NodeId] {
        self.rows.get(&id).map_or(&[], |r| r.parents.as_slice())
    }

    /// Additional attribution IDs, or an empty slice when `id` has no row.
    pub(crate) fn blame(&self, id: NodeId) -> &[NodeId] {
        self.rows.get(&id).map_or(&[], |r| r.blame.as_slice())
    }

    /// The rewrite that produced `id`, or `None` for an unrecorded id.
    pub(crate) fn tag(&self, id: NodeId) -> Option<RewriteTag> {
        let row = self.rows.get(&id)?;
        Some(self.tags[row.tag.0 as usize])
    }

    /// The interned handle a recorded id's row holds, or `None` for an
    /// unrecorded id. The identity two rows share when they name one rewrite.
    pub(crate) fn tag_id(&self, id: NodeId) -> Option<TagId> {
        Some(self.rows.get(&id)?.tag)
    }

    /// Whether `id` has a row.
    pub(crate) fn contains(&self, id: NodeId) -> bool {
        self.rows.contains_key(&id)
    }

    /// The producing tag when its phase is selected, otherwise `None`.
    ///
    /// An earlier phase's row must not be followed past this fold's input boundary.
    pub(crate) fn tag_in(&self, id: NodeId, phases: &[Phase]) -> Option<RewriteTag> {
        self.tag(id).filter(|tag| phases.contains(&tag.via))
    }

    /// Recorded IDs produced by the selected phases, in unspecified order.
    fn rows_in<'a>(&'a self, phases: &'a [Phase]) -> impl Iterator<Item = NodeId> + 'a {
        self.rows
            .iter()
            .filter(|(_, row)| phases.contains(&self.tags[row.tag.0 as usize].via))
            .map(|(id, _)| *id)
    }

    /// Recorded IDs produced from `start` through `end` inclusive and absent
    /// from `live`, sorted by ID. Requires `start <= end` (debug-asserted).
    /// Phase declaration order defines the range.
    ///
    /// Unlike [`fold`]'s input-minus-output deaths, this query can include products
    /// born and discarded between boundaries, but excludes nodes with no selected
    /// row. Neither result is necessarily a subset of the other.
    pub(crate) fn deaths(&self, start: Phase, end: Phase, live: &HashSet<NodeId>) -> Vec<NodeId> {
        debug_assert!(
            start <= end,
            "deaths range runs backwards through the pipeline: {start:?} is after {end:?}",
        );
        let mut out: Vec<NodeId> = self
            .rows
            .iter()
            .filter(|(_, row)| {
                let via = self.tags[row.tag.0 as usize].via;
                start <= via && via <= end
            })
            .map(|(id, _)| *id)
            .filter(|id| !live.contains(id))
            .collect();
        out.sort_unstable();
        out
    }

    /// The number of recorded nodes.
    pub(crate) fn len(&self) -> usize {
        self.rows.len()
    }

    /// The number of distinct rewrite tags interned — the `tag` column's
    /// cardinality.
    pub(crate) fn tag_count(&self) -> usize {
        self.tags.len()
    }

    /// Distinct phases in the interned tags, in first-interned order.
    ///
    /// The recorder interns tags when writing products. Direct callers of
    /// [`intern_tag`](Self::intern_tag) can also intern a tag without writing a row.
    #[cfg(test)]
    pub(crate) fn recorded_phases(&self) -> Vec<Phase> {
        let mut out: Vec<Phase> = Vec::new();
        for tag in &self.tags {
            if !out.contains(&tag.via) {
                out.push(tag.via);
            }
        }
        out
    }
}

// Thread-local recording state. Lifetimes and routing are specified in
// `src/ccl/design/provenance.md`, "The recorder".

thread_local! {
    /// Open recordings, innermost last. Mint and copy hooks capture only there.
    static RECORDING_STACK: RefCell<Vec<OpenRecording>> = const { RefCell::new(Vec::new()) };

    /// The compile-wide table installed by [`TableSession`]. No table means
    /// table flushes are discarded; it does not disable recording hooks.
    static ACTIVE_TABLE: RefCell<Option<ProvenanceTable>> = const { RefCell::new(None) };

    /// The phase supplied to table rows by [`PhaseScope`]. Lowering and derivation
    /// logs have separate routing and do not require this slot.
    static ACTIVE_PHASE: RefCell<Option<Phase>> = const { RefCell::new(None) };

    /// Lowering's literal-span and copy log, installed by [`LoweringSession`].
    static ACTIVE_LOWERING_LOG: RefCell<Option<LoweringRecord>> = const { RefCell::new(None) };

    /// The phase-local error-attribution log, written independently of table capture.
    static ACTIVE_DERIVATION_LOG: RefCell<Option<DerivationLog>> = const { RefCell::new(None) };
}

/// Products captured while this frame is innermost, flushed when its guard drops.
struct OpenRecording {
    label: RewriteLabel,
    /// Additional ancestors for minted products, supplied by `also_consumes`.
    consumed: Vec<NodeId>,
    /// The rewritten input. Minted products take it as a parent; copies use their
    /// own origins. `None` denotes a copy-only frame. Naming an input does not
    /// declare its death.
    named: Option<NodeId>,
    blame: Vec<NodeId>,
    nature: Nature,
    /// Ids minted via `Expr::new` while this guard was the innermost open one.
    births: Vec<NodeId>,
    /// `(origin, fresh)` pairs the freshen hooks reported while this guard was
    /// the innermost open one.
    copies: Vec<(NodeId, NodeId)>,
}

impl OpenRecording {
    /// Write one row per captured product using the ambient phase.
    ///
    /// Births take the named input and extra consumed IDs as parents, plus this
    /// frame's blame. Copies take only their own origin and no added blame.
    /// An event-free attempt writes nothing, regardless of its named input.
    fn flush_into_table(self, via: Phase) {
        let OpenRecording {
            label,
            consumed,
            named,
            blame,
            nature,
            births,
            copies,
        } = self;
        let Some(named) = named else {
            Self::assert_copy_only(label, &consumed, &births);
            Self::row_per_copy(via, label, nature, &copies);
            return;
        };
        debug_assert!(
            !births.contains(&named),
            "recording {label:?} minted the node it named, {named:?} — the named id is \
             read before the rewrite runs, so it cannot also be a birth",
        );
        if !births.is_empty() {
            let mut parents = vec![named];
            parents.extend(consumed.into_iter().filter(|c| *c != named));
            with_table(|table| {
                let tag_id = table.intern_tag(RewriteTag { via, nature, label });
                for &id in &births {
                    table.record(id, &parents, &blame, tag_id);
                }
            });
        }
        Self::row_per_copy(via, label, nature, &copies);
    }

    /// Write each copy with its origin as sole parent, no blame and the frame's tag.
    fn row_per_copy(via: Phase, label: RewriteLabel, nature: Nature, copies: &[(NodeId, NodeId)]) {
        if copies.is_empty() {
            return;
        }
        with_table(|table| {
            let tag_id = table.intern_tag(RewriteTag { via, nature, label });
            for &(origin, fresh) in copies {
                table.record(fresh, &[origin], &[], tag_id);
            }
        });
    }

    /// Debug-check the copy-only contract. Without a named input, consumed IDs and
    /// births would be discarded. Rewrites that mint need [`enter`]; lowering
    /// leaf attribution uses [`lowering_leaf`].
    fn assert_copy_only(label: RewriteLabel, consumed: &[NodeId], births: &[NodeId]) {
        debug_assert!(
            consumed.is_empty() && births.is_empty(),
            "copy frame {label:?} captured consumes {consumed:?} and mints {births:?} — a \
             recording that names no node has nothing to attach them to. A phase site wants \
             `enter` on the node being rewritten; a lowering leaf mint belongs in \
             `lowering_leaf`",
        );
    }

    /// Append births as one mint step and copies grouped by origin.
    ///
    /// Extra consumed IDs and blame are unsupported (debug-asserted): the derivation
    /// fold attributes births to the named input alone.
    fn log_derivation(&self, log: &mut DerivationLog) {
        debug_assert!(
            self.blame.is_empty() && self.consumed.is_empty(),
            "recording {:?} names blame or consumed ids under a DerivationSession, which \
             folds a birth to its named node alone",
            self.label,
        );
        if let Some(named) = self.named
            && !self.births.is_empty()
        {
            log.push(DerivationStep::Mint {
                named,
                produced: self.births.clone(),
                nature: self.nature,
                label: self.label,
            });
        }
        for (origin, produced) in group_copies(&self.copies) {
            log.push(DerivationStep::Copy { origin, produced });
        }
    }

    /// Append captured copies by origin. Leaf mints use [`lowering_leaf`] directly;
    /// births and extra consumed IDs violate this frame's copy-only contract.
    fn flush_into_lowering(self, rec: &mut LoweringRecord) {
        let OpenRecording {
            label,
            consumed,
            births,
            copies,
            ..
        } = self;
        Self::assert_copy_only(label, &consumed, &births);
        for (origin, produced) in group_copies(&copies) {
            rec.recorded.extend(produced.iter().copied());
            rec.log.push(LoweringStep::Copy { origin, produced });
        }
    }
}

#[cfg(test)]
thread_local! {
    /// How many nodes the predicate sweep has skipped on this thread.
    ///
    /// A skip is one node the sweep would otherwise have clobbered, so the count
    /// is the size of the damage the skip prevents. No leak class can see it — a
    /// clobbered node is still explained — which is why it is counted rather than
    /// asserted away.
    static PREDICATE_SWEEP_SKIPS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Read the predicate-sweep skip count and reset it.
#[cfg(test)]
pub(crate) fn take_predicate_sweep_skips() -> usize {
    PREDICATE_SWEEP_SKIPS.with(|n| n.replace(0))
}

/// Record one node of a **refinement predicate**, unless it is already
/// explained.
///
/// Lowering builds a predicate out of ordinary sub-expressions that were lowered
/// — and therefore recorded — in the main tree, then mints and copies extra
/// nodes to assemble them (`ccl_utils::refined_data_fun` is where the result is
/// sealed into a `Refinement`). Those assembly nodes live only in a type slot,
/// outside the `walk_children` domain, so nothing recorded them.
///
/// The skip is the whole point. A node the main-tree walk already explained has
/// a precise span and label; re-recording it here would replace both with this
/// sweep's coarse ones, because the fold is last-write-wins. Without the skip
/// the sweep clobbers 30 nodes over the pipeline corpus, and no leak class
/// reports anything, since a clobbered node is still explained.
/// `the_predicate_sweep_skips_already_recorded_nodes` pins the skip and
/// `the_predicate_sweep_skips_this_many_nodes_over_the_corpus` pins its size.
pub(crate) fn lowering_predicate_leaf(id: NodeId, span: Span, nature: Nature, label: RewriteLabel) {
    if id == NodeId::PLACEHOLDER {
        return;
    }
    ACTIVE_LOWERING_LOG.with(|slot| {
        if let Some(rec) = slot.borrow_mut().as_mut() {
            if !rec.recorded.insert(id) {
                #[cfg(test)]
                PREDICATE_SWEEP_SKIPS.with(|n| n.set(n.get() + 1));
                return;
            }
            rec.log.push(LoweringStep::Leaf {
                id,
                anchor: span,
                nature,
                label,
            });
        }
    });
}

/// Append a [`LoweringStep::Leaf`] to the active lowering log — the leaf-grain
/// recording that `tag_source`/`tag_machinery` route through. A no-op when no
/// [`LoweringSession`] is installed (the lower submodules' unit tests, which
/// only inspect the tree shape).
pub(crate) fn lowering_leaf(id: NodeId, span: Span, nature: Nature, label: RewriteLabel) {
    ACTIVE_LOWERING_LOG.with(|slot| {
        if let Some(rec) = slot.borrow_mut().as_mut() {
            rec.recorded.insert(id);
            rec.log.push(LoweringStep::Leaf {
                id,
                anchor: span,
                nature,
                label,
            });
        }
    });
}

/// Mutate the active table, or do nothing when no table session is installed.
fn with_table(f: impl FnOnce(&mut ProvenanceTable)) {
    ACTIVE_TABLE.with(|slot| {
        if let Some(table) = slot.borrow_mut().as_mut() {
            f(table);
        }
    });
}

/// Compile-wide table owner. It surrounds phase scopes and clears the installed
/// table on drop, including unwinding. [`into_table`](Self::into_table) drains it.
pub(crate) struct TableSession {
    // Not `Copy`/`Clone`; holds the installed-table invariant for its lifetime.
    _private: (),
}

impl TableSession {
    /// Install a fresh, empty table as this thread's mirror target. Non-reentrant
    /// (debug-asserted): a nested install would silently split one compile's rows
    /// across two tables.
    pub(crate) fn install() -> Self {
        ACTIVE_TABLE.with(|slot| {
            let mut slot = slot.borrow_mut();
            debug_assert!(
                slot.is_none(),
                "a TableSession is already installed on this thread",
            );
            *slot = Some(ProvenanceTable::default());
        });
        TableSession { _private: () }
    }

    /// Drain and return the table, ending the session. The `Drop` that follows
    /// finds the slot already empty and is a no-op.
    pub(crate) fn into_table(self) -> ProvenanceTable {
        ACTIVE_TABLE.with(|slot| slot.borrow_mut().take().unwrap_or_default())
    }
}

impl Drop for TableSession {
    fn drop(&mut self) {
        ACTIVE_TABLE.with(|slot| *slot.borrow_mut() = None);
    }
}

/// Group captured `(origin, fresh)` pairs into per-origin produced-lists,
/// preserving first-seen origin order for a deterministic log.
fn group_copies(copies: &[(NodeId, NodeId)]) -> Vec<(NodeId, Vec<NodeId>)> {
    let mut out: Vec<(NodeId, Vec<NodeId>)> = Vec::new();
    for &(origin, fresh) in copies {
        match out.iter_mut().find(|(o, _)| *o == origin) {
            Some((_, freshs)) => freshs.push(fresh),
            None => out.push((origin, vec![fresh])),
        }
    }
    out
}

/// Capture standalone duplication without naming a rewritten input.
///
/// Each copy hook supplies its own origin. The frame must capture no births or
/// extra consumed IDs; [`OpenRecording::assert_copy_only`] debug-checks this.
/// Use [`enter`] when a rewrite also mints nodes.
///
/// Table rows use `Nature::Machinery`. Lowering copies instead mirror their
/// origins' complete attribution and do not use this frame's nature or label.
pub(crate) fn copy_frame(label: RewriteLabel) -> RecordingGuard {
    RECORDING_STACK.with(|s| {
        let mut stack = s.borrow_mut();
        let depth = stack.len();
        stack.push(OpenRecording {
            label,
            consumed: Vec::new(),
            named: None,
            blame: Vec::new(),
            nature: Nature::Machinery,
            births: Vec::new(),
            copies: Vec::new(),
        });
        RecordingGuard { depth }
    })
}

/// Record products of a local rewrite until the returned guard drops.
///
/// Read `named_id` before rewriting. Births captured by this innermost frame
/// take it as a parent; copies retain their own origins. The named input need
/// not die. Bind the guard as `let _g = ...`; `let _ = ...` drops it immediately.
///
/// Open after recursive child work unless each child opens its own recording,
/// as [`converting`] does. Otherwise the parent frame captures child products.
/// See `src/ccl/design/provenance.md`, "Where to open a recording".
pub(crate) fn enter(named_id: NodeId, label: RewriteLabel, nature: Nature) -> RecordingGuard {
    RECORDING_STACK.with(|s| {
        let mut stack = s.borrow_mut();
        let depth = stack.len();
        stack.push(OpenRecording {
            label,
            consumed: Vec::new(),
            named: Some(named_id),
            blame: Vec::new(),
            nature,
            births: Vec::new(),
            copies: Vec::new(),
        });
        RecordingGuard { depth }
    })
}

/// Record one expression's conversion, including recursive child conversion.
///
/// Every recursive frame opens a recording, so child products use the child's
/// frame. Operators minted after a child returns belong to the parent frame.
/// Sites needing finer attribution, such as per-writer commit-store construction,
/// open a nested recording on the relevant input.
pub(crate) fn converting(named_id: NodeId) -> RecordingGuard {
    enter(named_id, "opconv.convert", Nature::Machinery)
}

/// Handle for one open recording. Drop pops it and flushes captured events,
/// including during unwinding. Guards must be dropped in LIFO order; channel
/// methods require this guard to be innermost. Both are debug-checked, not
/// enforced by the type system.
#[must_use = "a dropped RecordingGuard records nothing — bind it (`let _g = …`), \
              and note `let _ = …` drops it immediately"]
pub(crate) struct RecordingGuard {
    /// The stack index this recording occupied when opened, for the LIFO
    /// tripwire.
    depth: usize,
}

impl RecordingGuard {
    /// Add an ancestor for every birth in this recording. Placeholder IDs are ignored.
    /// This asserts ancestry, not death, and does not affect captured copies.
    ///
    /// Invalid on a copy-only frame. The fusion test
    /// `a_fusion_gives_every_product_the_bipartite_product` exercises this channel.
    #[allow(dead_code)]
    pub(crate) fn also_consumes(&self, id: NodeId) {
        if id == NodeId::PLACEHOLDER {
            return;
        }
        self.with_own_frame(|top| top.consumed.push(id));
    }

    /// Add related source IDs for minted products without asserting ancestry.
    /// Their spans augment the parents' spans; captured copies do not inherit them.
    pub(crate) fn blame(&self, ids: &[NodeId]) {
        self.with_own_frame(|top| top.blame.extend(ids.iter().copied()));
    }

    /// Require this guard to be innermost before modifying the top frame.
    /// The depth check is a debug assertion; callers must obey it in release builds.
    fn with_own_frame(&self, f: impl FnOnce(&mut OpenRecording)) {
        RECORDING_STACK.with(|s| {
            let mut stack = s.borrow_mut();
            debug_assert_eq!(
                stack.len(),
                self.depth + 1,
                "RecordingGuard channel used while it is not the innermost open recording \
                 (expected depth {}, stack has {})",
                self.depth,
                stack.len(),
            );
            if let Some(top) = stack.last_mut() {
                f(top);
            }
        });
    }
}

impl Drop for RecordingGuard {
    fn drop(&mut self) {
        // Pop this guard's recording. Guards drop in LIFO order in normal
        // control flow and on unwind alike; the tripwire catches a
        // manually-mis-ordered drop.
        let frame = RECORDING_STACK.with(|s| {
            let mut stack = s.borrow_mut();
            debug_assert_eq!(
                stack.len(),
                self.depth + 1,
                "RecordingGuard dropped out of LIFO order (expected depth {}, stack has {})",
                self.depth,
                stack.len(),
            );
            stack.pop()
        });
        let Some(frame) = frame else { return };
        // A derivation session logs every recording that closes inside it,
        // whether or not a phase scope also rows it into the table.
        ACTIVE_DERIVATION_LOG.with(|slot| {
            if let Some(log) = slot.borrow_mut().as_mut() {
                frame.log_derivation(log);
            }
        });
        // Lowering records into its own log; under a phase scope the rows go to
        // the table, tagged with the ambient phase. Under neither, the write is a
        // silent no-op: the recording captured, and has nowhere to land.
        if ACTIVE_LOWERING_LOG.with(|slot| slot.borrow().is_some()) {
            ACTIVE_LOWERING_LOG.with(|slot| {
                if let Some(rec) = slot.borrow_mut().as_mut() {
                    frame.flush_into_lowering(rec);
                }
            });
            return;
        }
        if let Some(via) = ACTIVE_PHASE.with(|p| *p.borrow()) {
            frame.flush_into_table(via);
        }
    }
}

/// Capture a minted ID in the innermost frame, ignoring the placeholder.
/// Outside lowering, an active phase requires a recording (debug-asserted).
/// Without either a recording or an active phase, the event is discarded.
pub(crate) fn on_mint(id: NodeId) {
    if id == NodeId::PLACEHOLDER {
        return;
    }
    let captured = RECORDING_STACK.with(|s| {
        if let Some(top) = s.borrow_mut().last_mut() {
            top.births.push(id);
            true
        } else {
            false
        }
    });
    debug_assert!(
        captured || !rows_would_reach_the_table(),
        "{id:?} was minted with no recording open, under a phase scope that writes \
         rows: the birth reaches no row and the fold reports the node as Unrecorded. \
         Open a recording over the rewrite with `provenance::enter`."
    );
}

/// Whether a phase scope is active outside lowering. This tests routing, not
/// whether a table is installed. Lowering mints use its leaf channel instead.
///
/// Keep the helper available in release builds: `debug_assert!` still
/// type-checks its condition when its execution is disabled.
fn rows_would_reach_the_table() -> bool {
    ACTIVE_LOWERING_LOG.with(|slot| slot.borrow().is_none())
        && ACTIVE_PHASE.with(|p| p.borrow().is_some())
}

/// A thread-local scope that nests, entered through a guard.
///
/// A depth rather than a flag because both scopes re-enter: a preserving copy of
/// a tree recurses through `Clone` for every child, and a sealed check clones as
/// it resolves. A guard rather than a decrement after the call because the depth
/// has to fall on an unwind. Both scopes wrap assertions, an assertion that fires
/// panics, and a depth left raised turns every later
/// [`TypedExpr::new`](crate::ccl::expr::TypedExpr::new) on that thread into a
/// throwaway.
trait ScopeDepth {
    /// Enter the scope; it stays open until the returned guard drops.
    fn enter(&'static self) -> DepthGuard;
    /// Whether any scope is open on this thread.
    fn is_open(&'static self) -> bool;
}

impl ScopeDepth for std::thread::LocalKey<std::cell::Cell<usize>> {
    fn enter(&'static self) -> DepthGuard {
        self.with(|c| c.set(c.get() + 1));
        DepthGuard(self)
    }

    fn is_open(&'static self) -> bool {
        self.with(std::cell::Cell::get) > 0
    }
}

/// Guard returned by [`ScopeDepth::enter`]. Dropping it leaves the scope.
#[must_use]
pub(crate) struct DepthGuard(&'static std::thread::LocalKey<std::cell::Cell<usize>>);

impl Drop for DepthGuard {
    fn drop(&mut self) {
        self.0.with(|c| c.set(c.get() - 1));
    }
}

thread_local! {
    /// Depth of the enclosing [`preserve_ids`] scopes: non-zero means a clone in
    /// progress is a **re-allocation of the same node**, not a duplication, so it
    /// must carry the origin's id rather than mint one.
    static PRESERVING_IDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Enter a thread-local scope where expression clones preserve their source IDs.
///
/// Callers use `TypedExpr::clone_preserving_ids` for one copy or [`run_debug_check`]
/// for diagnostic work. A genuine duplication inside this scope would reuse IDs;
/// the scope must not enclose unrelated cloning.
pub(crate) fn preserve_ids() -> DepthGuard {
    PRESERVING_IDS.enter()
}

/// Run a replacement rewrite with id-preserving expression clones.
///
/// `PredMemo` uses this only in replacing mode, currently selected by `uniquify`.
/// The traversal must replace every occurrence of each predicate; otherwise the
/// original and rebuilt terms may both survive with the same IDs. This scope covers
/// every clone on the thread while `f` runs, including clones made by its callees.
///
/// A single preserving copy uses `TypedExpr::clone_preserving_ids` instead.
/// See `src/ccl/design/provenance.md`, "Walking the ids".
pub(crate) fn preserving_ids<R>(f: impl FnOnce() -> R) -> R {
    let _guard = preserve_ids();
    f()
}

#[cfg(debug_assertions)]
thread_local! {
    /// Depth of the enclosing [`run_debug_check`] scopes.
    static SEALED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Whether a [`run_debug_check`] scope is open on this thread, so
/// [`TypedExpr::new`](crate::ccl::expr::TypedExpr::new) builds a throwaway
/// rather than minting.
#[cfg(debug_assertions)]
pub(crate) fn record_sealed() -> bool {
    SEALED.is_open()
}

/// Never sealed in a build with assertions off: `run_debug_check` is the only
/// thing that seals, and it does not exist there. `const` so that
/// [`TypedExpr::new`](crate::ccl::expr::TypedExpr::new) folds its throwaway
/// branch away rather than reading a thread-local for every node it builds.
#[cfg(not(debug_assertions))]
pub(crate) const fn record_sealed() -> bool {
    false
}

/// Run a diagnostic check without allocating expression identities.
///
/// Clones preserve their source IDs, and `TypedExpr::new` builds
/// [`NodeId::PLACEHOLDER`] throwaways. Nothing constructed by `f` may enter a live
/// tree. Both nested scopes unwind through guards if the check panics.
///
/// Type resolution can rebuild refinement predicates even during a check. Suppressing
/// those allocations keeps diagnostic work from renumbering later serialized IDs
/// between debug and release builds. Read-only checks need no such scope.
#[cfg(debug_assertions)]
pub(crate) fn run_debug_check<R>(f: impl FnOnce() -> R) -> R {
    let _preserving = preserve_ids();
    let _sealed = SEALED.enter();
    f()
}

/// Select a clone's identity and report a fresh copy to [`on_copy`].
///
/// An open [`preserve_ids`] scope returns `origin` unchanged and records nothing.
/// Otherwise the returned ID is freshly allocated.
pub(crate) fn copy_id(origin: NodeId) -> NodeId {
    if PRESERVING_IDS.is_open() {
        return origin;
    }
    let fresh = NodeId::fresh();
    on_copy(origin, fresh);
    fresh
}

/// Capture `(origin, fresh)` in the innermost recording, if one is open.
///
/// Pairs containing [`NodeId::PLACEHOLDER`] are ignored. Outside lowering, an active
/// phase with no recording triggers a debug assertion, matching [`on_mint`]'s
/// coverage check. A copy with no active phase or recording writes nothing.
pub(crate) fn on_copy(origin: NodeId, fresh: NodeId) {
    if origin == NodeId::PLACEHOLDER || fresh == NodeId::PLACEHOLDER {
        return;
    }
    let captured = RECORDING_STACK.with(|s| {
        if let Some(top) = s.borrow_mut().last_mut() {
            top.copies.push((origin, fresh));
            true
        } else {
            false
        }
    });
    debug_assert!(
        captured || !rows_would_reach_the_table(),
        "{fresh:?} was copied from {origin:?} with no recording open, under a \
         phase scope that writes rows: the copy reaches no row and the fold \
         reports it as Unrecorded. Open a recording over the duplication — \
         `provenance::enter` when a rewrite is being performed, `copy_frame` \
         when nothing is being rewritten and the copy is the whole of it."
    );
}

/// RAII installer for **lowering's** log.
///
/// Installed unconditionally for the whole of lowering in every build, because
/// the projection it folds into is release-critical: an `InferError` resolves
/// its blame node to a span through it. [`into_log`](Self::into_log) drains and
/// ends the session; `Drop` clears the slot so a panic never leaves a stale log
/// installed. At most one per thread, and it must fully drain before the first
/// [`PhaseScope`] opens — a guard closing while both were installed would record
/// lowering-shaped copies for a phase rewrite.
pub(crate) struct LoweringSession {
    // Not `Copy`/`Clone`; holds the installed-log invariant for its lifetime.
    _private: (),
}

impl LoweringSession {
    /// Install a fresh, empty lowering log as this thread's recording target.
    /// Non-reentrant (debug-asserted).
    pub(crate) fn install() -> Self {
        ACTIVE_LOWERING_LOG.with(|slot| {
            let mut slot = slot.borrow_mut();
            debug_assert!(
                slot.is_none(),
                "a LoweringSession is already installed on this thread",
            );
            *slot = Some(LoweringRecord::default());
        });
        LoweringSession { _private: () }
    }

    /// Drain and return the recorded log, ending the session. The `Drop` that
    /// follows finds the slot already empty and is a no-op.
    pub(crate) fn into_log(self) -> LoweringLog {
        ACTIVE_LOWERING_LOG.with(|slot| slot.borrow_mut().take().unwrap_or_default().log)
    }
}

impl Drop for LoweringSession {
    fn drop(&mut self) {
        ACTIVE_LOWERING_LOG.with(|slot| *slot.borrow_mut() = None);
    }
}

/// One step of a [`DerivationLog`].
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum DerivationStep {
    /// `produced` were minted by a recording that named `named`.
    Mint {
        /// The node the recording named.
        named: NodeId,
        /// The ids minted while it was the innermost open recording.
        produced: Vec<NodeId>,
        /// The recording's nature.
        nature: Nature,
        /// The recording's label.
        label: RewriteLabel,
    },
    /// `produced` are freshened copies of `origin`.
    Copy {
        /// The node copied.
        origin: NodeId,
        /// The copies.
        produced: Vec<NodeId>,
    },
}

/// The recordings a phase closed, in closing order, kept whether or not
/// provenance capture is on.
///
/// A phase whose mints an error can be raised at, and whose mints have no
/// lowering-projection ancestor in the tree around them, needs this to resolve
/// that error to a span when [`compile_to`](crate::ccl::context::compile_to)
/// records nothing. [`fold_derivation`] turns it into a projection over the
/// lowering projection. See `design/provenance.md`, "The derivation log".
pub(crate) type DerivationLog = Vec<DerivationStep>;

/// RAII installer for a [`DerivationLog`], the always-on sink a phase's
/// recordings write to beside the table.
///
/// Non-reentrant, and never open while lowering's log is: lowering's records
/// carry literal spans and go to its own sink.
pub(crate) struct DerivationSession {
    // Not `Copy`/`Clone`; holds the installed-log invariant for its lifetime.
    _private: (),
}

impl DerivationSession {
    /// Install a fresh, empty derivation log as this thread's sink.
    pub(crate) fn install() -> Self {
        debug_assert!(
            ACTIVE_LOWERING_LOG.with(|slot| slot.borrow().is_none()),
            "a DerivationSession opened while lowering's log is installed",
        );
        ACTIVE_DERIVATION_LOG.with(|slot| {
            let mut slot = slot.borrow_mut();
            debug_assert!(
                slot.is_none(),
                "a DerivationSession is already installed on this thread",
            );
            *slot = Some(DerivationLog::new());
        });
        DerivationSession { _private: () }
    }

    /// Drain and return the log, ending the session.
    pub(crate) fn into_log(self) -> DerivationLog {
        ACTIVE_DERIVATION_LOG.with(|slot| slot.borrow_mut().take().unwrap_or_default())
    }
}

impl Drop for DerivationSession {
    fn drop(&mut self) {
        ACTIVE_DERIVATION_LOG.with(|slot| *slot.borrow_mut() = None);
    }
}

/// Fold `log`, written by phase `via`, into a projection of the ids it minted
/// or copied, resolving each through `base` and through the entries the fold
/// has already made. `base` answers for ids an earlier projection holds.
///
/// A mint takes its named node's spans and the recording's tag; a copy mirrors
/// its origin. Steps are read in closing order, so a recording that names or
/// copies a node an inner recording minted finds that node already folded. A
/// step whose named node or origin resolves to nothing contributes no entry,
/// and a lookup for one of its ids falls through to the caller's next answer.
pub(crate) fn fold_derivation(
    log: &DerivationLog,
    base: &dyn Fn(&NodeId) -> Option<SourceAttribution>,
    via: Phase,
) -> SourceProjection {
    let mut out = SourceProjection::new();
    for step in log {
        match step {
            DerivationStep::Mint {
                named,
                produced,
                nature,
                label,
            } => {
                let Some(spans) = base(named)
                    .or_else(|| out.get(named).cloned())
                    .map(|a| a.spans)
                else {
                    continue;
                };
                let attr = SourceAttribution {
                    spans,
                    rewritten: RewriteTag {
                        via,
                        nature: *nature,
                        label,
                    },
                };
                for p in produced {
                    out.insert(*p, attr.clone());
                }
            }
            DerivationStep::Copy { origin, produced } => {
                let Some(attr) = base(origin).or_else(|| out.get(origin).cloned()) else {
                    continue;
                };
                for p in produced {
                    out.insert(*p, attr.clone());
                }
            }
        }
    }
    out
}

/// RAII installer for the ambient [`Phase`] every row is tagged with.
///
/// One scope per phase, opened at the boundary that runs it. The phase is carried
/// here rather than named per recording because a recording site knows its
/// `label` and `nature` but not which phase is running, while the boundary that
/// opens the scope knows exactly that: one phase runs inside one scope, so the
/// phase is ambient over the scope's whole extent. (A scope spanning several
/// phases, as an audit span opens, tags every row with the one phase it names —
/// no single phase being the truthful answer there.)
///
/// Opening a scope is what turns phase recording **on**: outside one a guard still
/// captures, but has no tag to complete a row with and writes nothing.
pub(crate) struct PhaseScope {
    // Not `Copy`/`Clone`; holds the installed-phase invariant for its lifetime.
    _private: (),
}

impl PhaseScope {
    /// Install `phase` as this thread's ambient recording phase. Non-reentrant
    /// (debug-asserted): a nested scope would silently retag the inner phase's
    /// rows on exit.
    pub(crate) fn enter(phase: Phase) -> Self {
        debug_assert!(
            ACTIVE_LOWERING_LOG.with(|slot| slot.borrow().is_none()),
            "opening a PhaseScope ({phase:?}) while lowering's log is still installed — a \
             closing guard would write lowering-shaped copies for a phase rewrite. Drain \
             the LoweringSession first",
        );
        ACTIVE_PHASE.with(|slot| {
            let mut slot = slot.borrow_mut();
            debug_assert!(
                slot.is_none(),
                "a PhaseScope is already open on this thread (opening {phase:?})",
            );
            *slot = Some(phase);
        });
        PhaseScope { _private: () }
    }
}

impl Drop for PhaseScope {
    fn drop(&mut self) {
        ACTIVE_PHASE.with(|slot| *slot.borrow_mut() = None);
    }
}

/// Read the installed [`ProvenanceTable`] mid-compile, or `None` when no
/// [`TableSession`] is installed.
///
/// The compile's table is drained at the end of the compile, so a measurement
/// that folds a span *inside* one — the provenance audit — has no other way to
/// reach the rows it just caused to be written.
pub(crate) fn with_active_table<R>(f: impl FnOnce(&ProvenanceTable) -> R) -> Option<R> {
    ACTIVE_TABLE.with(|slot| slot.borrow().as_ref().map(f))
}

/// The number of open recordings on this thread — a probe for the panic-safety
/// and no-op tests, which assert the stack is left clean.
#[cfg(test)]
fn open_recording_depth() -> usize {
    RECORDING_STACK.with(|s| s.borrow().len())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::load::LoadedProgram;

    /// A span in the one file these tests' attributions name.
    fn span(start: usize, end: usize) -> Span {
        Span::new(chl_parser::FileId::ROOT, start, end)
    }

    /// The phase the tests record under. The recorder is phase-agnostic — the tag
    /// only rides through to a row — so naming one constant keeps the choice
    /// from looking meaningful at each call site.
    const TEST_PHASE: Phase = Phase::Inline;

    /// The phase set every fold test uses: the one phase its rows carry.
    const PHASES: &[Phase] = &[TEST_PHASE];

    fn ids<const N: usize>() -> [NodeId; N] {
        std::array::from_fn(|_| NodeId::fresh())
    }

    fn set(items: impl IntoIterator<Item = NodeId>) -> HashSet<NodeId> {
        items.into_iter().collect()
    }

    fn sorted(mut v: Vec<NodeId>) -> Vec<NodeId> {
        v.sort_unstable();
        v
    }

    /// The ids one side of a node's edges names, labels dropped — for the tests
    /// whose subject is *which pairs* the fold derives rather than what they
    /// assert. The label tests below read [`Link::labels`] instead.
    fn ids_of(links: &[Link<NodeId>]) -> Vec<NodeId> {
        links.iter().map(|l| l.id).collect()
    }

    /// What the edge to `id` asserts, or `None` when the pair is not an edge at
    /// all — the two answers a labelled relation can give, kept apart.
    fn labels_of(links: &[Link<NodeId>], id: NodeId) -> Option<EdgeLabels> {
        links.iter().find(|l| l.id == id).map(|l| l.labels)
    }

    /// Write one row by hand, at `TEST_PHASE` with an `Expansion` nature.
    fn row(table: &mut ProvenanceTable, id: NodeId, parents: &[NodeId], blame: &[NodeId]) {
        row_tagged(
            table,
            id,
            parents,
            blame,
            RewriteTag {
                via: TEST_PHASE,
                nature: Nature::Expansion,
                label: "test.rewrite",
            },
        );
    }

    /// Write one row by hand under a named tag — for the tests where the phase,
    /// the nature or the label is the thing under test.
    fn row_tagged(
        table: &mut ProvenanceTable,
        id: NodeId,
        parents: &[NodeId],
        blame: &[NodeId],
        tag: RewriteTag,
    ) {
        let tag_id = table.intern_tag(tag);
        table.record(id, parents, blame, tag_id);
    }

    /// A table holding exactly `rows`, each `(node, parents)` with no blame.
    fn table_of(rows: &[(NodeId, &[NodeId])]) -> ProvenanceTable {
        let mut table = ProvenanceTable::default();
        for (id, parents) in rows {
            row(&mut table, *id, parents, &[]);
        }
        table
    }

    /// An attribution holding `spans`, tagged as a lowered direct image — what
    /// an upstream pane's entries look like.
    fn imaged(spans: &[Span]) -> SourceAttribution {
        SourceAttribution {
            spans: spans.to_vec(),
            rewritten: RewriteTag::direct_image(),
        }
    }

    // ---- provenance composition -------------------------------------------

    #[test]
    fn transient_born_and_consumed_composes_away() {
        // A → B (born) → C. B exists in neither snapshot; provenance flows A → C.
        let [a, b, c] = ids();
        let table = table_of(&[(b, &[a]), (c, &[b])]);
        let (map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([a]),
            &set([c]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(ids_of(map.upstream(&c)), vec![a]);
        assert_eq!(ids_of(map.downstream(&a)), vec![c]);
        // B is a transient: unknown to the map in both directions.
        assert!(map.upstream(&b).is_empty());
        assert!(map.downstream(&b).is_empty());
    }

    #[test]
    fn one_parent_reaching_two_products_fans_out() {
        // A is rewritten twice — a duplication and a replacement, say. Both
        // products trace to A, and A's own fate is decided by the panes alone:
        // here it survives, so it keeps its self-edge alongside the fan-out.
        let [a, b, c] = ids();
        let table = table_of(&[(b, &[a]), (c, &[a])]);
        let (map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([a]),
            &set([a, b, c]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(ids_of(map.upstream(&b)), vec![a]);
        assert_eq!(ids_of(map.upstream(&c)), vec![a]);
        assert_eq!(
            ids_of(map.upstream(&a)),
            vec![a],
            "the parent keeps its self-edge"
        );
        assert_eq!(sorted(ids_of(map.downstream(&a))), sorted(vec![a, b, c]));
    }

    #[test]
    fn a_fusion_gives_every_product_the_bipartite_product() {
        // {A,B} fused into {C,D}: every input reaches every output (2×2 = 4
        // edges), which falls out of each product row holding the whole
        // consumed set as its parents.
        let [a, b, c, d] = ids();
        let table = table_of(&[(c, &[a, b]), (d, &[a, b])]);
        let (map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([a, b]),
            &set([c, d]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(ids_of(map.upstream(&c)), sorted(vec![a, b]));
        assert_eq!(ids_of(map.upstream(&d)), sorted(vec![a, b]));
        assert_eq!(ids_of(map.downstream(&a)), sorted(vec![c, d]));
        assert_eq!(ids_of(map.downstream(&b)), sorted(vec![c, d]));
        assert_eq!(map.edges().len(), 4);
    }

    #[test]
    fn untouched_id_gets_self_edge_and_inherits_attribution() {
        // No row mentions A: it survives with a self-edge and its upstream
        // attribution passes through unchanged.
        let [a] = ids();
        let mut upstream = SourceProjection::new();
        upstream.insert(a, imaged(&[span(3, 9)]));
        let (map, proj, _deaths, leaks) = fold(
            &ProvenanceTable::default(),
            PHASES,
            &set([a]),
            &set([a]),
            &upstream,
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(ids_of(map.upstream(&a)), vec![a]);
        assert_eq!(ids_of(map.downstream(&a)), vec![a]);
        assert_eq!(proj.get(&a), upstream.get(&a), "attribution unchanged");
    }

    /// A phase set exercising a chain, a fan-out and an N:1 merge, with every
    /// parent known and every input dying — so it folds leak-free whichever
    /// order its rows were written in. Returns `(rows, inputs, outputs,
    /// upstream_attr)` with the rows in dependency order.
    #[allow(clippy::type_complexity)]
    fn mixed_phases() -> (
        Vec<(NodeId, Vec<NodeId>, Vec<NodeId>)>,
        HashSet<NodeId>,
        HashSet<NodeId>,
        SourceProjection,
    ) {
        let [a, b, x, y, z] = ids();
        let mut upstream = SourceProjection::new();
        upstream.insert(a, imaged(&[span(0, 2)]));
        upstream.insert(b, imaged(&[span(4, 6)]));
        let rows = vec![
            (x, vec![a], vec![a]),
            (y, vec![x], vec![]),
            (z, vec![x, b], vec![b]),
        ];
        (rows, set([a, b]), set([y, z]), upstream)
    }

    fn table_from(rows: &[(NodeId, Vec<NodeId>, Vec<NodeId>)]) -> ProvenanceTable {
        let mut table = ProvenanceTable::default();
        for (id, parents, blame) in rows {
            row(&mut table, *id, parents, blame);
        }
        table
    }

    #[test]
    fn the_write_order_of_the_rows_does_not_change_the_fold() {
        // The property the ascending sweep buys: the rows are an edge set, so
        // writing them in dependency order or in reverse gives byte-identical
        // results. Write order is not chronology — rows are written when their
        // guard drops, so an enclosing rewrite's rows land after the rows of the
        // rewrites nested inside it.
        let (rows, inputs, outputs, upstream) = mixed_phases();
        let mut reversed = rows.clone();
        reversed.reverse();

        let (map, proj, _deaths, leaks) =
            fold(&table_from(&rows), PHASES, &inputs, &outputs, &upstream);
        let (rev_map, rev_proj, _deaths, rev_leaks) =
            fold(&table_from(&reversed), PHASES, &inputs, &outputs, &upstream);

        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(leaks, rev_leaks, "same leaks in either order");
        assert_eq!(
            map.edges(),
            rev_map.edges(),
            "same relation in either order"
        );
        assert_eq!(proj, rev_proj, "same projection in either order");
    }

    #[test]
    fn the_sweep_visits_every_vertex_once_and_never_backwards() {
        // The sweep's premise, measured: ascending NodeId is a topological order
        // of the definition graph, so the revisit count is zero.
        let (rows, inputs, _outputs, _upstream) = mixed_phases();
        let m = sweep_metrics(&table_from(&rows), PHASES, &inputs);
        assert_eq!(m.vertices, 5, "two input ids + three produced");
        assert_eq!(m.edges, 4, "a→x, x→y, x→z, b→z");
        assert_eq!(
            m.backward_edges, 0,
            "a backward edge is a vertex the single sweep would have to revisit",
        );
    }

    #[test]
    fn a_row_produced_outside_the_phases_reads_as_un_produced() {
        // The phase restriction, which is what turns a whole-compile table back
        // into a per-pane-pair one. B was produced by a phase this pair does
        // not span, so to this pair it is an ordinary input-pane node: the
        // fold stops there rather than resolving through to A.
        let [a, b, c] = ids();
        let mut table = ProvenanceTable::default();
        row_tagged(
            &mut table,
            b,
            &[a],
            &[],
            RewriteTag {
                via: Phase::Infer,
                nature: Nature::Machinery,
                label: "other.phase",
            },
        );
        row(&mut table, c, &[b], &[]);
        let (map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([b]),
            &set([c]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(
            ids_of(map.upstream(&c)),
            vec![b],
            "the out-of-scope row is the fold's input, not a hop through it",
        );
    }

    // ---- leak taxonomy -----------------------------------------------------

    #[test]
    fn clean_rows_produce_no_leaks() {
        let [a, b] = ids();
        let table = table_of(&[(b, &[a])]);
        let (_map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([a]),
            &set([a, b]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
    }

    #[test]
    fn leak_unrecorded_fires_on_an_output_no_row_produced() {
        // Z appears in the output snapshot but no row produced it and the input
        // pane does not hold it.
        let [a, z] = ids();
        let (_map, _proj, _deaths, leaks) = fold(
            &ProvenanceTable::default(),
            PHASES,
            &set([a]),
            &set([a, z]),
            &SourceProjection::new(),
        );
        assert!(leaks.contains(&Leak::Unrecorded { output: z }), "{leaks:?}");
    }

    #[test]
    fn a_death_is_an_input_missing_from_the_output_and_not_a_leak() {
        // B is an input-pane id absent from the output pane, and nothing said so.
        let [a, b] = ids();
        let (_map, _proj, deaths, leaks) = fold(
            &ProvenanceTable::default(),
            PHASES,
            &set([a, b]),
            &set([a]),
            &SourceProjection::new(),
        );
        assert_eq!(deaths, vec![b]);
        assert!(leaks.is_empty(), "{leaks:?}");
    }

    #[test]
    fn leak_dangling_parent_fires_on_a_parent_the_fold_never_heard_of() {
        // X is neither an input-pane id nor produced by a phase the fold read, so B's
        // ancestry stops at an id that describes nothing. One class, whether the
        // unknown id is a lone parent (as here) or one of a fusion's several —
        // the parents column does not record which.
        let [a, x, b] = ids();
        let table = table_of(&[(b, &[x])]);
        let (_map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([a]),
            &set([a, b]),
            &SourceProjection::new(),
        );
        assert!(
            leaks.contains(&Leak::DanglingParent { parent: x }),
            "{leaks:?}"
        );

        let [a2, x2, b2] = ids();
        let table = table_of(&[(b2, &[a2, x2])]);
        let (_map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([a2]),
            &set([b2]),
            &SourceProjection::new(),
        );
        assert!(
            leaks.contains(&Leak::DanglingParent { parent: x2 }),
            "one of a fusion's parents is the same class: {leaks:?}",
        );
    }

    #[test]
    fn one_unrecorded_mint_can_fire_both_classes_for_the_same_id() {
        // Z was minted with nothing recording it; a recorded rewrite then consumed
        // it to produce B, and Z itself also survived into the output pane. Both
        // walks report Z, because the classes name where the fold noticed an id
        // rather than which defect occurred. Neither localizes the missing
        // recording.
        let [a, z, b] = ids();
        let table = table_of(&[(b, &[z])]);
        let (_map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([a]),
            &set([a, z, b]),
            &SourceProjection::new(),
        );
        assert!(
            leaks.contains(&Leak::DanglingParent { parent: z }),
            "{leaks:?}"
        );
        assert!(leaks.contains(&Leak::Unrecorded { output: z }), "{leaks:?}");
    }

    #[test]
    fn a_dangling_parent_that_many_rows_name_is_one_leak() {
        // Three rows name the same unknown parent, the shape a specialized
        // definition's per-instantiation copies produce. A leak count is broken
        // ancestry targets, not the rows pointing at them.
        let [a, x, b, c, d] = ids();
        let table = table_of(&[(b, &[x]), (c, &[x]), (d, &[x])]);
        let (_map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([a]),
            &set([a, b, c, d]),
            &SourceProjection::new(),
        );
        assert_eq!(leaks, vec![Leak::DanglingParent { parent: x }]);
    }

    // ---- the write-time invariants -----------------------------------------
    //
    // Each is a property of the *record*, asserted where the second writer is
    // standing rather than in a fold that only runs when a pane is materialized.
    // Debug-gated because they are `debug_assert!`s: there is no release
    // behaviour to assert, the row being written the same way in every build.

    #[test]
    #[cfg(debug_assertions)]
    fn a_second_row_for_one_id_is_rejected() {
        // Attribution has no join — a node cannot carry two `via`/`label` pairs
        // — so a second claimant has no answer and overwriting would make the
        // survivor a lie about which rewrite made the node.
        let [a, b, p] = ids();
        let caught = std::panic::catch_unwind(|| {
            let mut table = ProvenanceTable::default();
            row(&mut table, p, &[a], &[]);
            row(&mut table, p, &[b], &[]);
        });
        assert!(caught.is_err(), "a duplicate produce must be rejected");
    }

    #[test]
    #[cfg(debug_assertions)]
    fn a_row_with_neither_parent_nor_blame_is_rejected() {
        // A truly unanchored mint: nothing explains where the node came from.
        let [b] = ids();
        let caught = std::panic::catch_unwind(|| {
            let mut table = ProvenanceTable::default();
            row(&mut table, b, &[], &[]);
        });
        assert!(caught.is_err(), "an unanchored record must be rejected");
    }

    #[test]
    #[cfg(debug_assertions)]
    fn a_node_may_not_be_its_own_parent() {
        // The self-referential definition — the one construct that makes an edge
        // run backwards and forces the fold to a fixed point. An in-place
        // rewrite that keeps its id is a preserve: it records nothing.
        let [a, b] = ids();
        let caught = std::panic::catch_unwind(|| {
            let mut table = ProvenanceTable::default();
            row(&mut table, a, &[a, b], &[]);
        });
        assert!(caught.is_err(), "consumed ∩ produced ≠ ∅ must be rejected");
    }

    // ---- blame / attribution ----------------------------------------------

    #[test]
    fn a_pure_insertion_is_blamed_and_descends_from_nothing() {
        // A node placed over surviving material: no parents at all, attributed
        // through blame. Its one edge is the blame edge blame contributes;
        // nothing claims it descends from anything.
        let [a, b] = ids();
        let mut upstream = SourceProjection::new();
        upstream.insert(a, imaged(&[span(1, 4)]));
        let mut table = ProvenanceTable::default();
        row(&mut table, b, &[], &[a]);
        let (map, proj, _deaths, leaks) = fold(&table, PHASES, &set([a]), &set([a, b]), &upstream);
        assert!(leaks.is_empty(), "pure insertion is leak-free: {leaks:?}");
        assert_eq!(
            labels_of(map.upstream(&b), a),
            Some(EdgeLabels::BLAME),
            "the insertion is related to what it was blamed on, and descends from nothing",
        );
        assert_eq!(ids_of(map.upstream(&b)), vec![a], "and from nothing else");
        let attr = proj.get(&b).expect("b attributed via blame");
        assert_eq!(attr.spans, vec![span(1, 4)]);
    }

    #[test]
    fn the_span_union_is_deduplicated_across_both_channels() {
        // parents = [A], blame = [A, B] — A is named twice and A's own spans
        // overlap B's. A: [s1, s2], B: [s2, s3] → [s1, s2, s3], each span once.
        let [a, b, out] = ids();
        let (s1, s2, s3) = (span(0, 1), span(2, 3), span(4, 5));
        let mut upstream = SourceProjection::new();
        upstream.insert(a, imaged(&[s1, s2]));
        upstream.insert(b, imaged(&[s2, s3]));
        let mut table = ProvenanceTable::default();
        row(&mut table, out, &[a], &[a, b]);
        // B is carried to the output pane so the fold reports no death for it.
        let (_map, proj, _deaths, leaks) =
            fold(&table, PHASES, &set([a, b]), &set([out, b]), &upstream);
        assert!(
            leaks.is_empty(),
            "blame does not affect fate accounting: {leaks:?}"
        );
        let attr = proj.get(&out).expect("out attributed");
        assert_eq!(attr.spans, vec![s1, s2, s3]);
        assert_eq!(attr.rewritten.via, Phase::Inline);
        assert_eq!(attr.rewritten.nature, Nature::Expansion);
    }

    #[test]
    fn empty_blame_attributes_through_the_parents() {
        // The common case: no blame, so the node's spans are its parent's,
        // re-tagged with the rewrite that produced it.
        let [a, b] = ids();
        let mut upstream = SourceProjection::new();
        upstream.insert(a, imaged(&[span(1, 2)]));
        let mut table = ProvenanceTable::default();
        row_tagged(
            &mut table,
            b,
            &[a],
            &[],
            RewriteTag {
                via: TEST_PHASE,
                nature: Nature::Expansion,
                label: "copy.mirror",
            },
        );
        let (_map, proj, _deaths, leaks) = fold(&table, PHASES, &set([a]), &set([a, b]), &upstream);
        assert!(leaks.is_empty(), "{leaks:?}");
        let attr = proj.get(&b).expect("product attributed");
        assert_eq!(attr.spans, vec![span(1, 2)], "mirrors the parent's spans");
        assert_eq!(attr.rewritten.via, Phase::Inline);
        assert_eq!(attr.rewritten.nature, Nature::Expansion);
        assert_eq!(attr.rewritten.label, "copy.mirror");
    }

    #[test]
    fn empty_blame_on_a_fusion_unions_every_parents_spans() {
        // The many:1 case of the same rule, and the reason it is one rule: a
        // fusion names no blame, and its product is an image of everything it
        // was made from — so it resolves to the union, not to nothing.
        let [a, b, out] = ids();
        let mut upstream = SourceProjection::new();
        upstream.insert(a, imaged(&[span(0, 3)]));
        upstream.insert(b, imaged(&[span(7, 9)]));
        let table = table_of(&[(out, &[a, b])]);
        let (_map, proj, _deaths, leaks) =
            fold(&table, PHASES, &set([a, b]), &set([out]), &upstream);
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(
            proj.get(&out).expect("fusion attributed").spans,
            vec![span(0, 3), span(7, 9)],
        );
    }

    #[test]
    fn parents_and_blame_reach_the_relation_under_different_labels() {
        // The two channels populated with *distinct* nodes: the product was made
        // from P and is additionally *about* B. Its spans are both, parentage
        // first. Both nodes reach the relation, and the labels are what keep the
        // claims apart — B survives the rewrite, so "the product is related to
        // B" must not read as "the product descends from B".
        let [p, b, out] = ids();
        let (sp, sb) = (span(0, 4), span(9, 12));
        let mut upstream = SourceProjection::new();
        upstream.insert(p, imaged(&[sp]));
        upstream.insert(b, imaged(&[sb]));
        let mut table = ProvenanceTable::default();
        row(&mut table, out, &[p], &[b]);
        let (map, proj, _deaths, leaks) =
            fold(&table, PHASES, &set([p, b]), &set([b, out]), &upstream);
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(
            proj.get(&out).expect("out attributed").spans,
            vec![sp, sb],
            "both channels resolve, parentage first",
        );
        assert_eq!(
            labels_of(map.upstream(&out), p),
            Some(EdgeLabels::ANCESTRY),
            "ancestry-only: the consumed node is an ancestor and nothing else",
        );
        assert_eq!(
            labels_of(map.upstream(&out), b),
            Some(EdgeLabels::BLAME),
            "blame-only: the blamed node is named, not descended from",
        );
        assert_eq!(
            labels_of(map.downstream(&b), b),
            Some(EdgeLabels::ANCESTRY),
            "and B, surviving, still descends from itself",
        );
    }

    #[test]
    fn one_id_in_both_columns_is_one_edge_carrying_both_labels() {
        // A rewrite that consumes P *and* names it as blame — the case the
        // per-pair storage exists for. It is one pair, so it is one edge, and
        // the edge asserts both relations rather than the fold picking a winner
        // or the map holding the pair twice.
        let [p, out] = ids();
        let mut table = ProvenanceTable::default();
        row(&mut table, out, &[p], &[p]);
        let (map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([p]),
            &set([out]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(
            ids_of(map.upstream(&out)),
            vec![p],
            "one entry for one pair"
        );
        let labels = labels_of(map.upstream(&out), p).expect("the pair is an edge");
        assert!(labels.has_ancestry() && labels.has_blame(), "{labels:?}");
    }

    #[test]
    fn two_paths_to_one_root_union_their_labels() {
        // The same pair reached twice, once each way: OUT descends from X, which
        // descends from R, and OUT is separately blamed on R. Both readings are
        // true of the pair `(R, OUT)`, and the entry carries both — a consumer
        // pruning blame still sees the ancestry, and one pruning ancestry
        // still sees the blame.
        let [r, x, out] = ids();
        let mut table = ProvenanceTable::default();
        row(&mut table, x, &[r], &[]);
        row(&mut table, out, &[x], &[r]);
        let (map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([r]),
            &set([out]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        let labels = labels_of(map.upstream(&out), r).expect("the pair is an edge");
        assert!(labels.has_ancestry() && labels.has_blame(), "{labels:?}");
    }

    #[test]
    fn a_mixed_path_is_blame_not_ancestry() {
        // Weakest link, which is the whole content of the label. OUT descends
        // from M, and M is *related to* R — so OUT is related to R and does not
        // descend from it. Reading the closure as unlabelled reachability would
        // make R an ancestor of OUT while R is still standing in the tree.
        let [r, m, out] = ids();
        let mut table = ProvenanceTable::default();
        row(&mut table, m, &[], &[r]);
        row(&mut table, out, &[m], &[]);
        let (map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([r]),
            &set([r, out]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(
            labels_of(map.upstream(&out), r),
            Some(EdgeLabels::BLAME),
            "one blame hop on the path makes the endpoint related",
        );
        assert_eq!(
            labels_of(map.downstream(&r), out),
            Some(EdgeLabels::BLAME),
            "and the mirrored direction agrees",
        );
    }

    #[test]
    fn an_all_ancestry_path_stays_ancestry_through_a_transient() {
        // The other half of weakest-link: composing ancestry with ancestry is
        // ancestry however many transients the path runs through, so the label
        // means more than "one hop, unrewritten".
        let [a, b, c] = ids();
        let table = table_of(&[(b, &[a]), (c, &[b])]);
        let (map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([a]),
            &set([c]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(labels_of(map.upstream(&c), a), Some(EdgeLabels::ANCESTRY));
    }

    #[test]
    fn a_blamed_id_the_fold_never_heard_of_is_not_a_dangling_parent() {
        // `DanglingParent` is a claim about the `parents` column: an *ancestry* hop
        // that stops at an id describing nothing. Blame points at material the
        // relation need not hold, so an unknown blamed id contributes no edge and
        // no leak — the same silence `attribute` keeps for a blamed id with no
        // known spans.
        let [a, unknown, b] = ids();
        let mut table = ProvenanceTable::default();
        row(&mut table, b, &[a], &[unknown]);
        let (map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([a]),
            &set([b]),
            &SourceProjection::new(),
        );
        assert!(
            leaks.is_empty(),
            "an unknown blamed id is not a defect: {leaks:?}"
        );
        assert_eq!(
            ids_of(map.upstream(&b)),
            vec![a],
            "and it contributes no edge"
        );
    }

    #[test]
    fn machinery_empty_blame_is_present_with_empty_spans() {
        // The "known node, no source anchor" case: present in the projection
        // with spans: [], distinct from a node absent from the projection. Its
        // ancestor has no spans either, so there is nothing to inherit.
        let [a, b] = ids();
        let mut table = ProvenanceTable::default();
        row_tagged(
            &mut table,
            b,
            &[a],
            &[],
            RewriteTag {
                via: TEST_PHASE,
                nature: Nature::Machinery,
                label: "machinery.plumbing",
            },
        );
        let (_map, proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([a]),
            &set([b]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        let attr = proj.get(&b).expect("b present in projection");
        assert!(attr.spans.is_empty(), "known node, no source anchor");
        assert_eq!(attr.rewritten.nature, Nature::Machinery);
    }

    #[test]
    fn node_absent_from_projection_is_distinct_from_empty_spans() {
        // An input id with no upstream attribution that survives untouched has
        // no projection entry at all — distinct from present-but-empty spans.
        let [a] = ids();
        let (_map, proj, _deaths, leaks) = fold(
            &ProvenanceTable::default(),
            PHASES,
            &set([a]),
            &set([a]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        assert!(
            !proj.contains_key(&a),
            "unknown node absent from projection"
        );
    }

    // ---- the lowering fold (fold_lowering) -----------------------------

    fn leaf(id: NodeId, sp: Span, nature: Nature, label: RewriteLabel) -> LoweringStep {
        LoweringStep::Leaf {
            id,
            anchor: sp,
            nature,
            label,
        }
    }

    fn lowering_copy(origin: NodeId, produced: Vec<NodeId>) -> LoweringStep {
        LoweringStep::Copy { origin, produced }
    }

    #[test]
    fn lowering_leaf_is_attributed_from_its_anchor() {
        // A leaf mint: no input pane, no ancestor, attribution straight
        // from the literal anchor span with the direct-image tag.
        let [a] = ids();
        let log = vec![leaf(a, span(2, 7), Nature::Source, "lower.image")];
        let (proj, leaks) = fold_lowering(&log, &set([a]));
        assert!(leaks.is_empty(), "{leaks:?}");
        let attr = proj.get(&a).expect("leaf attributed");
        assert_eq!(attr.spans, vec![span(2, 7)]);
        assert_eq!(attr.rewritten.via, Phase::Lower);
        assert_eq!(attr.rewritten.nature, Nature::Source);
    }

    #[test]
    fn lowering_copy_mirrors_its_origins_folded_entry() {
        // The compare-chain shape: an operand leaf (Source), then a freshened
        // second-use copy mirroring it verbatim.
        let [orig, copy] = ids();
        let log = vec![
            leaf(orig, span(0, 1), Nature::Source, "lower.image"),
            lowering_copy(orig, vec![copy]),
        ];
        let (proj, leaks) = fold_lowering(&log, &set([orig, copy]));
        assert!(leaks.is_empty(), "{leaks:?}");
        let orig_attr = proj.get(&orig).expect("origin");
        let copy_attr = proj.get(&copy).expect("copy");
        assert_eq!(
            copy_attr.spans, orig_attr.spans,
            "copy mirrors origin spans"
        );
        assert_eq!(
            copy_attr.rewritten.nature,
            Nature::Source,
            "copy mirrors origin's Source tag"
        );
    }

    #[test]
    fn lowering_born_copied_discarded_template_composes_away() {
        // The uncurry shape: a template proj node is minted (leaf, Machinery),
        // copied into an occurrence's interior, and never itself placed in the
        // output tree. It is live at the end but not an output id, so it
        // composes away with NO leak (lowering reports no deaths, and
        // Unrecorded checks outputs only).
        let [template, occ_interior] = ids();
        let log = vec![
            leaf(
                template,
                span(4, 9),
                Nature::Machinery,
                "lower.uncurry_proj",
            ),
            lowering_copy(template, vec![occ_interior]),
        ];
        // Output = only the copied interior; the template is discarded.
        let (proj, leaks) = fold_lowering(&log, &set([occ_interior]));
        assert!(
            leaks.is_empty(),
            "born-copied-discarded template must compose away leak-free: {leaks:?}"
        );
        assert_eq!(
            proj.get(&occ_interior).expect("interior").rewritten.nature,
            Nature::Machinery,
            "interior mirrors the template's machinery tag"
        );
        assert!(
            !proj.contains_key(&template),
            "the discarded template is not an output node"
        );
    }

    #[test]
    fn lowering_unrecorded_fires_on_an_unrecorded_mint() {
        // An output-tree node that no leaf produced and no copy placed — the
        // unrecorded-lowering-mint class.
        let [tagged, orphan] = ids();
        let log = vec![leaf(tagged, span(0, 1), Nature::Source, "lower.image")];
        let (_proj, leaks) = fold_lowering(&log, &set([tagged, orphan]));
        assert!(
            leaks.contains(&Leak::Unrecorded { output: orphan }),
            "{leaks:?}"
        );
    }

    #[test]
    fn lowering_dangling_parent_fires_on_a_copy_of_an_unrecorded_origin() {
        let [never, copy] = ids();
        let log = vec![lowering_copy(never, vec![copy])];
        let (_proj, leaks) = fold_lowering(&log, &set([copy]));
        assert!(
            leaks.contains(&Leak::DanglingParent { parent: never }),
            "{leaks:?}"
        );
    }

    #[test]
    fn lowering_root_carry_preserve_inherits_its_leaf_attribution() {
        // A substituted root carries the occurrence's own id, so the log holds no
        // entry for it — just the occurrence's leaf entry — while its interior
        // children are copies of the replacement template. The root keeps its own
        // (Source) attribution; the interior mirrors the template (Machinery).
        let [occurrence, tmpl_child, occ_child] = ids();
        let log = vec![
            // The param-use occurrence, imaged Source at its mint.
            leaf(occurrence, span(10, 11), Nature::Source, "lower.image"),
            // The template child (tuple ref / projection index), machinery.
            leaf(
                tmpl_child,
                span(3, 6),
                Nature::Machinery,
                "lower.uncurry_proj",
            ),
            // The occurrence's interior is a freshened copy of the template child.
            lowering_copy(tmpl_child, vec![occ_child]),
        ];
        // Output tree: the carried root (occurrence id) + its fresh interior.
        let (proj, leaks) = fold_lowering(&log, &set([occurrence, occ_child]));
        assert!(leaks.is_empty(), "{leaks:?}");
        let root_attr = proj.get(&occurrence).expect("carried root");
        assert_eq!(
            root_attr.rewritten.nature,
            Nature::Source,
            "the carried root keeps the occurrence's own Source attribution"
        );
        assert_eq!(root_attr.spans, vec![span(10, 11)]);
        assert_eq!(
            proj.get(&occ_child).expect("interior").rewritten.nature,
            Nature::Machinery,
            "the interior mirrors the template's machinery tag"
        );
    }

    #[test]
    fn lowering_reimage_last_tag_wins() {
        // `lower_expr` re-tags an arm's already-tagged root as the construct's
        // direct image: two leaf records for one id. Lowering has no
        // one-record-per-id rule (the fold is sequential and its log genuinely
        // is chronology), so the later Source tag wins over the earlier
        // machinery one, with no leak.
        let [id] = ids();
        let log = vec![
            leaf(id, span(0, 5), Nature::Machinery, "lower.compare_chain"),
            leaf(id, span(0, 5), Nature::Source, "lower.image"),
        ];
        let (proj, leaks) = fold_lowering(&log, &set([id]));
        assert!(leaks.is_empty(), "re-image is not a leak: {leaks:?}");
        assert_eq!(
            proj.get(&id).expect("reimaged").rewritten.nature,
            Nature::Source,
            "the later (Source) tag wins"
        );
    }

    // ---- the recorder ------------------------------------------------------
    //
    // These exercise the hooks through *real* `Expr` construction (`Expr::lit`,
    // `Expr::tuple`) and the freshening `Clone`, not hand-built rows, so the hook
    // wiring in `expr.rs` is under test too.

    use crate::ccl::expr::Expr;
    use crate::ccl::{Lit, TypedExprNode};

    /// Run `f` with a table installed and `TEST_PHASE` ambient, and return the
    /// rows it recorded — the two things a phase boundary sets up.
    fn recorded(f: impl FnOnce()) -> ProvenanceTable {
        let table = TableSession::install();
        {
            let _scope = PhaseScope::enter(TEST_PHASE);
            f();
        }
        table.into_table()
    }

    /// The skip's size, over the pipeline corpus.
    ///
    /// The unit test above pins that the skip happens; this pins how much it is
    /// worth. Both matter because no leak class can see the difference: a node
    /// the sweep clobbers is still explained, so without this number a
    /// regression that removed the skip would show up nowhere.
    ///
    /// The number moves when the corpus does. It is a measurement, not a bound —
    /// update it and say what changed.
    #[test]
    fn the_predicate_sweep_skips_this_many_nodes_over_the_corpus() {
        use crate::ccl::context::{GlobalContext, compile_program};
        use crate::ccl::test_corpus::pipeline_corpus;
        use crate::interpreter::Consumer;

        let _ = take_predicate_sweep_skips();
        let mut total = 0usize;
        for (name, code) in pipeline_corpus() {
            let mut ctx = GlobalContext::default();
            let consumer: Box<dyn Consumer> = Box::new(|| {});
            compile_program(&mut ctx, &LoadedProgram::from_text(name, &code), consumer)
                .unwrap_or_else(|e| panic!("{name}: expected a successful compile, got {e:?}"));
            total += take_predicate_sweep_skips();
        }
        assert_eq!(
            total, 8,
            "the predicate sweep skipped {total} nodes over the corpus",
        );
    }

    /// The predicate sweep must not overwrite attribution a node already has.
    ///
    /// This is the one property of `lowering_predicate_leaf` that **no leak class
    /// can see**: the fold is last-write-wins, so a node re-recorded by the sweep
    /// is still explained — it has swapped its real span and label for the
    /// sweep's coarse ones. A blanket sweep clobbers 30 nodes over the pipeline
    /// corpus and every gate stays green.
    #[test]
    fn the_predicate_sweep_skips_already_recorded_nodes() {
        let [recorded_id, fresh] = ids::<2>();
        let session = LoweringSession::install();
        lowering_leaf(recorded_id, span(10, 20), Nature::Source, "lower.precise");
        lowering_predicate_leaf(recorded_id, span(0, 99), Nature::Machinery, "lower.sweep");
        lowering_predicate_leaf(fresh, span(0, 99), Nature::Machinery, "lower.sweep");
        let log = session.into_log();

        assert_eq!(log.len(), 2, "the already-recorded node is not re-recorded");
        let leaf = |want: NodeId| {
            log.iter()
                .find_map(|s| match s {
                    LoweringStep::Leaf {
                        id, anchor, label, ..
                    } if *id == want => Some((*anchor, *label)),
                    _ => None,
                })
                .expect("a leaf for this id")
        };
        assert_eq!(
            leaf(recorded_id),
            (span(10, 20), "lower.precise"),
            "the lowered node keeps its own span and label",
        );
        assert_eq!(
            leaf(fresh),
            (span(0, 99), "lower.sweep"),
            "the assembly node is explained by the sweep",
        );
    }

    /// A second sweep over the same predicate adds nothing — the skip is keyed on
    /// the id, not on which sweep recorded it, so overlapping predicates (one
    /// term riding several type slots) cannot double-record.
    #[test]
    fn the_predicate_sweep_is_idempotent() {
        let [n] = ids::<1>();
        let session = LoweringSession::install();
        lowering_predicate_leaf(n, span(1, 2), Nature::Machinery, "lower.sweep");
        lowering_predicate_leaf(n, span(3, 4), Nature::Machinery, "lower.sweep");
        let log = session.into_log();
        assert_eq!(
            log.len(),
            1,
            "one entry per node however many sweeps reach it"
        );
        assert!(matches!(&log[0], LoweringStep::Leaf { anchor, .. } if *anchor == span(1, 2)));
    }

    #[test]
    fn a_recording_rows_every_birth_on_the_node_it_names() {
        let named = NodeId::fresh();
        let (mut a, mut b) = (NodeId::PLACEHOLDER, NodeId::PLACEHOLDER);
        let table = recorded(|| {
            let _g = enter(named, "rw.build", Nature::Expansion);
            a = Expr::lit(Lit::Int(1)).node_id();
            b = Expr::lit(Lit::Int(2)).node_id();
        });
        assert_eq!(
            table.parents(a),
            &[named],
            "a birth is parented on the node the recording named",
        );
        assert_eq!(table.parents(b), &[named]);
        assert_eq!(
            table.tag(a),
            Some(RewriteTag {
                via: TEST_PHASE,
                nature: Nature::Expansion,
                label: "rw.build",
            }),
            "the row's `via` is the ambient phase — the one part of the tag no \
             recording site knows",
        );
        assert_eq!(table.tag(a), table.tag(b));
        assert!(
            !table.contains(named),
            "the named node is read, not produced: it gets no row of its own",
        );
        assert_eq!(table.len(), 2, "one row per produced id");
        assert_eq!(open_recording_depth(), 0, "guard popped its recording");
    }

    #[test]
    fn nested_recordings_attribute_each_mint_to_the_innermost_named_node() {
        // Granularity is precision: a mint attributes to the innermost open
        // recording. A coarser recording is not *wrong*, it is less precise —
        // the mint attaches to whatever enclosing node was named.
        let (outer_named, inner_named) = (NodeId::fresh(), NodeId::fresh());
        let (mut outer_pre, mut inner_id, mut outer_post) = (
            NodeId::PLACEHOLDER,
            NodeId::PLACEHOLDER,
            NodeId::PLACEHOLDER,
        );
        let table = recorded(|| {
            let _outer = enter(outer_named, "rw.outer", Nature::Expansion);
            outer_pre = Expr::lit(Lit::Int(0)).node_id();
            {
                let _inner = enter(inner_named, "rw.inner", Nature::Expansion);
                inner_id = Expr::lit(Lit::Int(1)).node_id();
            }
            outer_post = Expr::lit(Lit::Int(2)).node_id();
        });
        assert_eq!(table.parents(inner_id), &[inner_named]);
        assert_eq!(table.parents(outer_pre), &[outer_named]);
        assert_eq!(
            table.parents(outer_post),
            &[outer_named],
            "the outer recording owns the births outside the inner extent, and only those",
        );
        assert_eq!(table.tag(inner_id).map(|t| t.label), Some("rw.inner"));
        assert_eq!(table.tag(outer_pre).map(|t| t.label), Some("rw.outer"));
    }

    #[test]
    fn a_deep_freshen_rows_each_node_on_its_own_origin() {
        // Build a 3-node tree (tuple + two lits) with nothing recording, then
        // clone it inside a copy-only recording — one that consumes nothing and
        // mints nothing of its own, so its whole output is the freshen pairs
        // `Clone` reports through the `on_copy` hook.
        let source = Expr::tuple(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]);
        // The source's node ids are the origins each per-node row should name.
        let old_ids: HashSet<NodeId> = std::iter::once(source.node_id())
            .chain(source.child_exprs().iter().map(|c| c.node_id()))
            .collect();

        let mut clone = Expr::lit(Lit::Int(0));
        let table = recorded(|| {
            let _g = copy_frame("dup");
            clone = source.clone();
        });

        let fresh_ids: HashSet<NodeId> = std::iter::once(clone.node_id())
            .chain(clone.child_exprs().iter().map(|c| c.node_id()))
            .collect();
        assert_eq!(fresh_ids.len(), 3, "the clone is a distinct 3-node tree");
        assert!(
            fresh_ids.is_disjoint(&old_ids),
            "a clone shares no id with its source",
        );
        assert_eq!(table.len(), 3, "one row per cloned node");
        let mut origins: HashSet<NodeId> = HashSet::new();
        for id in fresh_ids {
            let parents = table.parents(id);
            assert_eq!(parents.len(), 1, "a copy has exactly its origin as parent");
            origins.insert(parents[0]);
        }
        assert_eq!(
            origins, old_ids,
            "every cloned node rows on the node it was duplicated from",
        );
    }

    #[test]
    fn a_recording_that_only_clones_records_nothing_of_its_own() {
        // A recording whose rewrite turns out to be a pure duplication (nothing
        // minted by hand, nothing fused) writes only the rows the clone reported,
        // none of them naming its named.
        let source = Expr::tuple(vec![Expr::lit(Lit::Int(1)), Expr::lit(Lit::Int(2))]);
        // The named named is the node being rewritten, not the tree being
        // duplicated — the two are distinct at every real site.
        let named = NodeId::fresh();
        let mut clone = Expr::lit(Lit::Int(0));
        let table = recorded(|| {
            let _g = enter(named, "wrap.freshen", Nature::Machinery);
            clone = source.clone();
        });
        assert_eq!(table.len(), 3, "only the three cloned nodes");
        for id in
            std::iter::once(clone.node_id()).chain(clone.child_exprs().iter().map(|c| c.node_id()))
        {
            assert_ne!(
                table.parents(id),
                &[named],
                "each row names the cloned node's own origin, not the node the recording named",
            );
        }
    }

    #[test]
    fn a_captured_freshen_rows_on_its_own_origin() {
        // Most production in `channelize`/`transact_phase` is a `clone`, not
        // an `Expr::new`. Those fire `on_copy`, whose origin is the *copied* node,
        // not the named node — so the copy channel stays independent of the
        // recording's own parentage rather than being folded into it.
        let tree = Expr::tuple(vec![Expr::lit(Lit::Int(1))]);
        let named = NodeId::fresh();
        let mut copy_root = NodeId::PLACEHOLDER;
        let table = recorded(|| {
            let _g = enter(named, "rw.duplicate", Nature::Machinery);
            copy_root = tree.clone().node_id();
        });
        assert_eq!(table.parents(copy_root), &[tree.node_id()]);
        assert!(
            table.blame(copy_root).is_empty(),
            "a copy mirrors its origin rather than re-attributing",
        );
    }

    #[test]
    fn no_recording_open_records_nothing() {
        // No phase scope: a mint with nothing recording is legitimate here, so
        // `on_mint`'s assert does not apply. Under a phase scope the same code
        // trips it, which is the point of the assert — see
        // `rows_would_reach_the_table`.
        let table_session = TableSession::install();
        {
            // Construction and cloning with an empty stack capture nowhere.
            let _e = Expr::lit(Lit::Int(1));
            let x = Expr::lit(Lit::Int(2));
            let _copy = x.clone();
        }
        assert_eq!(
            table_session.into_table().len(),
            0,
            "empty stack ⇒ nothing recorded"
        );
    }

    #[test]
    fn no_pass_scope_open_makes_the_flush_a_silent_no_op() {
        // A recording open with no ambient phase: births still capture into it,
        // but the guard has no tag to complete a row with and writes nothing (no
        // panic).
        assert!(
            ACTIVE_PHASE.with(|s| s.borrow().is_none()),
            "precondition: no phase scope open",
        );
        let table_session = TableSession::install();
        {
            let _g = enter(NodeId::fresh(), "rw", Nature::Expansion);
            let _a = Expr::lit(Lit::Int(1));
        }
        assert_eq!(
            open_recording_depth(),
            0,
            "guard still pops cleanly with no phase scope"
        );
        assert_eq!(table_session.into_table().len(), 0);
    }

    #[test]
    fn no_table_installed_makes_the_flush_a_silent_no_op() {
        assert!(
            ACTIVE_TABLE.with(|s| s.borrow().is_none()),
            "precondition: no table installed",
        );
        let _scope = PhaseScope::enter(TEST_PHASE);
        let named = NodeId::fresh();
        {
            let _g = enter(named, "rw.build", Nature::Machinery);
            let _ = Expr::lit(Lit::Int(1));
        }
        assert_eq!(open_recording_depth(), 0, "guard still pops cleanly");
    }

    #[test]
    fn panic_inside_a_recording_unwinds_without_poisoning_the_stack() {
        assert_eq!(open_recording_depth(), 0, "clean precondition");
        let result = std::panic::catch_unwind(|| {
            let _g = enter(NodeId::fresh(), "boom", Nature::Expansion);
            let _a = Expr::lit(Lit::Int(1));
            panic!("deliberate panic inside an open recording");
        });
        assert!(result.is_err(), "the panic propagated");
        assert_eq!(
            open_recording_depth(),
            0,
            "the guard's Drop popped the recording on unwind"
        );

        // Recording still works afterward.
        let named = NodeId::fresh();
        let mut a = NodeId::PLACEHOLDER;
        let table = recorded(|| {
            let _g = enter(named, "rw", Nature::Expansion);
            a = Expr::lit(Lit::Int(7)).node_id();
        });
        assert_eq!(table.parents(a), &[named]);
    }

    #[test]
    #[cfg(debug_assertions)]
    fn panic_inside_a_debug_check_unwinds_without_leaving_the_record_sealed() {
        // The scope wraps an assertion, so a panic out of it is the assertion
        // doing its job. A seal left standing would make every later node on this
        // thread a throwaway, and throwaways share one id, so the damage surfaces
        // far from here.
        assert!(!record_sealed(), "clean precondition");
        let inside = std::cell::Cell::new(None);
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run_debug_check(|| {
                inside.set(Some(Expr::lit(Lit::Int(1)).node_id()));
                panic!("deliberate panic inside a debug check");
            })
        }));
        assert!(caught.is_err(), "the panic propagated");
        assert_eq!(
            inside.get(),
            Some(NodeId::PLACEHOLDER),
            "the record was sealed while `f` ran"
        );
        assert!(
            !record_sealed(),
            "the guard's Drop unsealed the record on unwind"
        );
        assert_ne!(
            Expr::lit(Lit::Int(2)).node_id(),
            NodeId::PLACEHOLDER,
            "a later mint takes a real id"
        );
    }

    #[test]
    fn default_uses_placeholder_records_nothing_and_two_defaults_share_id() {
        let named = NodeId::fresh();
        let (mut d1, mut d2) = (NodeId::PLACEHOLDER, NodeId::PLACEHOLDER);
        let mut kept = NodeId::PLACEHOLDER;
        let table = recorded(|| {
            d1 = Expr::default().node_id();
            d2 = Expr::default().node_id();
            // Even inside an open recording, a Default throwaway must not be
            // captured.
            let _g = enter(named, "rw", Nature::Expansion);
            let _d3 = Expr::default();
            // A real mint alongside it, so something is recorded at all: a
            // recording that captures nothing is a preserve and stays silent,
            // which would make "the Default was not captured" vacuously true.
            kept = Expr::lit(Lit::Int(3)).node_id();
        });

        assert_eq!(d1, NodeId::PLACEHOLDER, "Default mints the sentinel");
        assert_eq!(
            d1, d2,
            "two Defaults share the placeholder id (they compare equal regardless — \
             node_id is excluded from PartialEq)",
        );
        assert_eq!(table.len(), 1, "the Default throwaway got no row");
        assert_eq!(table.parents(kept), &[named], "the real mint was captured");
    }

    #[test]
    fn a_fused_flush_gives_its_product_every_consumed_id_as_a_parent() {
        // Fusion (many:1), the sole escape hatch and the only place any id is
        // named at record time. The product's provenance is the product of every
        // origin's, which is what the parents column carries.
        let (named, fused) = (NodeId::fresh(), NodeId::fresh());
        let mut product = NodeId::PLACEHOLDER;
        let table = recorded(|| {
            let g = enter(named, "rw.fuse", Nature::Machinery);
            g.also_consumes(fused);
            product = Expr::lit(Lit::Int(1)).node_id();
        });
        assert_eq!(
            table.parents(product),
            &[named, fused],
            "a fusion's whole consumed set is the product's parent set",
        );
    }

    #[test]
    fn a_flush_carries_the_blame_channel_into_the_row_unmerged() {
        let (named, blamed) = (NodeId::fresh(), NodeId::fresh());
        let mut product = NodeId::PLACEHOLDER;
        let table = recorded(|| {
            let g = enter(named, "rw.blamed", Nature::Machinery);
            g.blame(&[blamed]);
            product = Expr::lit(Lit::Int(1)).node_id();
        });
        assert_eq!(table.parents(product), &[named], "blame is not a parent");
        assert_eq!(table.blame(product), &[blamed], "and a parent is not blame");
    }

    #[test]
    fn a_recording_over_an_untouched_node_records_nothing() {
        // A rule that inspects and declines. No mint, no copy, id unchanged:
        // the *preserve*, and it must not cost a row — this is what lets a phase
        // open a recording on every rewrite *attempt* rather than every firing.
        let e = Expr::lit(Lit::Int(1));
        let table = recorded(|| {
            let _g = enter(e.node_id(), "rw.noop", Nature::Machinery);
        });
        assert_eq!(table.len(), 0);
    }

    #[test]
    fn a_recording_over_an_in_place_mutation_records_nothing() {
        // `simplify`'s `*op = BinOpKind::Concat` shape: the node's *value*
        // changes, its identity does not. A preserve, and correctly silent —
        // the node's provenance is the self-edge it already had.
        let mut e = Expr::lit(Lit::Int(1));
        let id = e.node_id();
        let table = recorded(|| {
            let _g = enter(id, "rw.in_place", Nature::Machinery);
            e.node = TypedExprNode::Lit(Lit::Int(2));
        });
        assert_eq!(e.node_id(), id);
        assert_eq!(table.len(), 0);
    }

    // ---- a recording declares nothing --------------------------------------
    //
    // The property under test throughout: a site names the node being rewritten,
    // births are captured, and fate is the relation's live-set difference. These
    // are the pass/fail statements behind the design.

    #[test]
    fn an_end_to_end_recording_feeds_the_fold() {
        // Record a real rewrite, then fold the rows and check
        // the resulting relation and attribution.
        let a = Expr::lit(Lit::Int(1));
        let a_id = a.node_id();
        let mut out_id = NodeId::PLACEHOLDER;
        let table = recorded(|| {
            let _g = enter(a_id, "rw.replace", Nature::Expansion);
            out_id = Expr::lit(Lit::Int(2)).node_id();
        });

        let (map, proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([a_id]),
            &set([out_id]),
            &SourceProjection::new(),
        );
        // `a` is replaced, so it dies — reported, not a defect.
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(ids_of(map.upstream(&out_id)), vec![a_id]);
        assert_eq!(ids_of(map.downstream(&a_id)), vec![out_id]);
        let attr = proj.get(&out_id).expect("output attributed");
        assert_eq!(attr.rewritten.via, Phase::Inline);
        assert_eq!(attr.rewritten.label, "rw.replace");
    }

    #[test]
    fn born_copied_discarded_template_composes_without_leaks() {
        // The `fold_induction_loop`/`build_writer` template shape (transact/letrec
        // instrumentation hazard): one recording births a template `T`, copies
        // it per read site (via `Subst::discharge_env_in_place`), and discards
        // `T` (it never reaches the output tree). `T` is neither an input-pane nor an output-pane id, so
        // it triggers no leak (the death report reads inputs only, `Unrecorded`
        // outputs only) — the whole shape composes in ONE recording, no split
        // needed.
        let origin = NodeId::fresh(); // the named node, an input-pane id
        let (mut t, mut c1, mut c2) = (
            NodeId::PLACEHOLDER,
            NodeId::PLACEHOLDER,
            NodeId::PLACEHOLDER,
        );
        let table = recorded(|| {
            let _g = enter(origin, "test.template", Nature::Machinery);
            // Birth the template inside the recording (a mint captured as a
            // birth).
            let template = Expr::lit(Lit::Int(0));
            t = template.node_id();
            // Copy it twice — one freshened clone per read site.
            let r1 = template.clone();
            c1 = r1.node_id();
            let r2 = template.clone();
            c2 = r2.node_id();
        });
        assert_eq!(table.parents(t), &[origin]);
        assert_eq!(table.parents(c1), &[t], "the copies row on the template");
        assert_eq!(table.parents(c2), &[t]);

        // The sweep's premise on rows written by the *recorder* rather than by
        // hand: capture-only births plus one monotone counter means no edge runs
        // backwards, so no vertex is ever revisited.
        assert_eq!(
            sweep_metrics(&table, PHASES, &set([origin])).backward_edges,
            0,
            "a captured record's edges all run from smaller NodeId to larger",
        );
        let (map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([origin]),
            &set([c1, c2]),
            &SourceProjection::new(),
        );
        assert!(
            leaks.is_empty(),
            "born-copied-discarded template composes defect-free in one recording: {leaks:?}",
        );
        // c1/c2 carry T's roots — the recording's parentage (`origin`).
        assert_eq!(ids_of(map.upstream(&c1)), vec![origin]);
        assert_eq!(ids_of(map.upstream(&c2)), vec![origin]);
        assert_eq!(
            sorted(ids_of(map.downstream(&origin))),
            sorted(vec![c1, c2])
        );
    }

    #[test]
    fn a_recorded_wrap_does_not_claim_the_wrapped_node_died() {
        // The adopt-a-live-subtree shape: mint a wrapper *over* the named node,
        // which stays in the tree as a child. Both ids are live at the
        // fold; it must report no death and no leak. A record that
        // declared the named consumed would report it dead.
        let named = NodeId::fresh();
        let mut wrapper = NodeId::PLACEHOLDER;
        let table = recorded(|| {
            let _g = enter(named, "rw.wrap", Nature::Machinery);
            wrapper = Expr::lit(Lit::Int(0)).node_id();
        });
        let (map, _proj, _deaths, leaks) = fold(
            &table,
            PHASES,
            &set([named]),
            &set([named, wrapper]),
            &SourceProjection::new(),
        );
        assert!(leaks.is_empty(), "{leaks:?}");
        assert_eq!(ids_of(map.upstream(&wrapper)), vec![named]);
        assert_eq!(
            ids_of(map.upstream(&named)),
            vec![named],
            "the wrapped node survives"
        );
    }

    #[test]
    fn deaths_are_the_live_set_difference_not_a_declaration() {
        // The fate-prediction replacement, end to end. One rewrite; whether the
        // named node survives is decided *only* by which snapshot it is in.
        // The identical record yields "survived" against one output pane and
        // "died" against another, and no site said either.
        let make = || {
            let named = NodeId::fresh();
            let mut born = NodeId::PLACEHOLDER;
            let table = recorded(|| {
                let _g = enter(named, "rw.maybe_drop", Nature::Expansion);
                born = Expr::lit(Lit::Int(1)).node_id();
            });
            (named, born, table)
        };

        let (named, born, table) = make();
        let (_m, _p, deaths, leaks) = fold(
            &table,
            PHASES,
            &set([named]),
            &set([named, born]),
            &SourceProjection::new(),
        );
        assert!(deaths.is_empty(), "survivor pane");
        assert!(leaks.is_empty(), "survivor pane: {leaks:?}");

        let (named, born, table) = make();
        let (map, _p, deaths, leaks) = fold(
            &table,
            PHASES,
            &set([named]),
            &set([born]),
            &SourceProjection::new(),
        );
        assert_eq!(
            deaths,
            vec![named],
            "nothing declares a fate, so the live-set difference IS the death report",
        );
        assert!(leaks.is_empty(), "a death is not a leak: {leaks:?}");
        assert_eq!(
            ids_of(map.upstream(&born)),
            vec![named],
            "provenance survives the death"
        );
    }

    // ---- the node table's columns ------------------------------------------

    fn tag(label: RewriteLabel) -> RewriteTag {
        RewriteTag {
            via: TEST_PHASE,
            nature: Nature::Machinery,
            label,
        }
    }

    #[test]
    fn a_row_round_trips_every_column() {
        let mut table = ProvenanceTable::default();
        let [node, parent, blamed] = ids();
        let tag_id = table.intern_tag(tag("rw.one"));
        table.record(node, &[parent], &[blamed], tag_id);

        assert_eq!(table.parents(node), &[parent]);
        assert_eq!(table.blame(node), &[blamed]);
        assert_eq!(table.tag(node), Some(tag("rw.one")));
        assert!(table.contains(node));
    }

    #[test]
    fn a_fusion_row_round_trips_all_its_parents() {
        // The many:1 shape: one product, every consumed id a parent. Parents are
        // a set of edges, not a single channel, so none of them may be dropped
        // or reordered into a "primary".
        let mut table = ProvenanceTable::default();
        let [node, p0, p1, p2] = ids();
        let tag_id = table.intern_tag(tag("rw.fuse"));
        table.record(node, &[p0, p1, p2], &[], tag_id);

        assert_eq!(table.parents(node), &[p0, p1, p2]);
        assert!(
            table.blame(node).is_empty(),
            "no blame is not empty parents"
        );
    }

    #[test]
    fn an_unrecorded_id_reads_empty_rather_than_panicking() {
        // The predicate-interior case: a real id from the same counter that no
        // recording ever produced. Every read must have an answer for it.
        let mut table = ProvenanceTable::default();
        let [parent, recorded, never] = ids();
        let tag_id = table.intern_tag(tag("rw.one"));
        table.record(recorded, &[parent], &[], tag_id);

        assert!(table.parents(never).is_empty());
        assert!(table.blame(never).is_empty());
        assert_eq!(table.tag(never), None);
        assert_eq!(table.tag_in(never, PHASES), None);
        assert!(!table.contains(never));
    }

    #[test]
    fn a_row_outside_the_phases_reads_as_unrecorded_to_that_fold() {
        let mut table = ProvenanceTable::default();
        let [parent, node] = ids();
        let tag_id = table.intern_tag(RewriteTag {
            via: Phase::Infer,
            ..tag("rw.one")
        });
        table.record(node, &[parent], &[], tag_id);

        assert!(table.tag(node).is_some(), "the row exists");
        assert_eq!(
            table.tag_in(node, PHASES),
            None,
            "but not to a fold whose phases exclude it",
        );
    }

    #[test]
    fn deaths_read_rows_in_range_and_never_the_key_space() {
        // Two properties of the range difference. The key space is the global
        // counter, so it addresses ids this compile never built; a difference
        // taken over it would report every one of them as a death. And the range
        // is pipeline order, so a row tagged with a phase outside it is another
        // range's churn: `Planning` runs after `Channelize` and is excluded here.
        let mut table = ProvenanceTable::default();
        let [parent, survivor, dead, never, late] = ids();
        let tag_id = table.intern_tag(tag("rw.one"));
        let late_tag = table.intern_tag(RewriteTag {
            via: Phase::Planning,
            nature: Nature::Machinery,
            label: "rw.late",
        });
        table.record(survivor, &[parent], &[], tag_id);
        table.record(dead, &[parent], &[], tag_id);
        table.record(late, &[parent], &[], late_tag);

        let live: HashSet<NodeId> = set([survivor]);
        let deaths = table.deaths(Phase::Inline, Phase::Channelize, &live);
        assert!(
            !deaths.contains(&late),
            "a row tagged Planning is outside Inline..=Channelize",
        );
        assert_eq!(
            deaths,
            vec![dead],
            "only a recorded id absent from the live set is a death",
        );
        assert!(
            !deaths.contains(&never),
            "an id with no row describes no node that could have died",
        );
    }

    #[test]
    fn equal_tags_share_one_tag_id_and_distinct_tags_do_not() {
        let mut table = ProvenanceTable::default();
        let [parent, a, b, c] = ids();
        let one = table.intern_tag(tag("rw.one"));
        let one_again = table.intern_tag(tag("rw.one"));
        let other = table.intern_tag(tag("rw.other"));
        assert_eq!(one, one_again, "the tag is the interning key, by value");
        assert_ne!(one, other);

        table.record(a, &[parent], &[], one);
        table.record(b, &[parent], &[], one_again);
        table.record(c, &[parent], &[], other);
        assert_eq!(
            table.tag_id(a),
            table.tag_id(b),
            "two rows naming one rewrite hold one handle",
        );
        assert_ne!(table.tag_id(a), table.tag_id(c));
        assert_eq!(table.tag_count(), 2, "two distinct tags, two entries");
        assert_eq!(table.tag(c), Some(tag("rw.other")));
    }

    #[test]
    fn a_differing_nature_is_a_distinct_tag_despite_a_shared_label() {
        // The triple is interned whole: one arm of a rewrite relabelled to a
        // different nature is a different tag, which is exactly why a site that
        // needs two natures opens a second recording rather than mutating one.
        let mut table = ProvenanceTable::default();
        let machinery = table.intern_tag(tag("rw.one"));
        let expansion = table.intern_tag(RewriteTag {
            nature: Nature::Expansion,
            ..tag("rw.one")
        });
        assert_ne!(machinery, expansion);
        assert_eq!(table.tag_count(), 2);
    }
}
