//! Node identity, and the per-compile table that records where each node came
//! from.
//!
//! # The model
//!
//! Every IR expression node carries a [`NodeId`], unique within a tree — a
//! pipeline invariant asserted at every phase boundary by
//! `assert_unique_node_ids`. Rows are keyed by that identity, so everything
//! below rests on it: two nodes sharing an id would share one row and one
//! attribution.
//!
//! Every node a phase *produces* gets a row in the [`ProvenanceTable`]: the ids
//! the rewrite consumed to produce it (`parents`), the ids it attributes to
//! (`blame` — **not** the same as what it consumed), and an interned
//! [`RewriteTag`] carrying the [`Phase`], the fidelity `nature`, and a stable
//! `label`. An id with no row was never rewritten.
//!
//! Rows are a byproduct of performing the rewrite, never a post-phase diff. A
//! phase names the node it is about to rewrite ([`enter`]), and the construction
//! hooks record every node minted while that guard is the innermost one open.
//!
//! For a pair of inspector panes the rows the phases between them wrote are
//! folded once by [`fold`] into a [`ProvenanceMap`] — a bidirectional node↔node
//! relation with an explicit self-edge for every id that survived — and, in
//! parallel, into a [`SourceProjection`] that resolves each surviving node's
//! attribution back to source spans. The fold composes away ids born and
//! consumed within the phase; its [`Leak`] vector is what says whether a node
//! silently lost its history, and the input ids it reports dead are the
//! live-set difference.
//!
//! The fold is order-free: it reads the rows as an edge set and sweeps them in
//! ascending [`NodeId`], which is a topological order of the definition graph
//! (see [`fold`], "The algebra"). Write order is not chronology, and
//! [`fold`] explains why nothing may depend on it.
//!
//! # Two columns, because they are two kinds of relation
//!
//! Both columns relate a node to other nodes, and differ in what the relation
//! asserts. Both reach [`ProvenanceMap`], each labelling the edges it
//! contributes:
//!
//! * **`parents`** — descends from. The ids the rewrite consumed to produce
//!   this node, and the column the leak audit reads: a parent the fold
//!   never heard of is an ancestry that stops at an id describing nothing
//!   ([`Leak::DanglingParent`]).
//! * **`blame`** — related to, but not consumed. It may name ids that survive
//!   the rewrite, so it is not an ancestry claim, and a reader asking "what was
//!   this made from" reads the edge's label rather than its presence.
//!
//! The labels compose weakest-link along a path, so that the inspector can
//! render blame or prune it once transitivity has run; [`EdgeLabels`]
//! states the composition.
//!
//! Attribution reads both columns, unioned: a node's spans are its parents'
//! spans plus whatever distinct spans its blame adds. Blame is named at a
//! handful of sites, all in the mutability phases, so for almost every node this
//! is the spans of whatever it was made from. Attribution reads no label — a
//! span is a span whichever column named the node it came from.
//!
//! # Domains, not phases
//!
//! [`ProvenanceMap`] is generic over its two id domains so the same relation can
//! serve a pane pair's `NodeId → NodeId` and a future `NodeId → OperatorId`
//! edge; both domains are `NodeId` today. Phases live in the *data* (each row's
//! [`RewriteTag`]), never in the type.
//!
//! # What this module does not own
//!
//! Lowering's own attribution channel, whose entries carry a literal source span
//! rather than a NodeId reference, is a [`LoweringLog`] folded once at the
//! lowering handoff — see [`LoweringStep`] for why it is a separate sink.
//! `CompiledProgram::materialize_panes` (`crate::ccl::context`) is the caller
//! that folds a whole compile's table into the inspector's panes, and
//! `design/provenance.md` is the reference for the design.

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

/// A stable identity for an IR expression node, minted fresh and never reused.
///
/// Minted only via [`NodeId::fresh`]; nothing observes its numeric value (only
/// id *equality*), so non-determinism across process runs is fine — uniqueness
/// is all that matters. This mirrors the [`crate::ccl::names::Uid`] /
/// `FRESH_UID` idiom in [`crate::ccl::names`]; it uses a separate counter
/// because `NodeId` identifies expression *nodes* whereas `Uid` identifies
/// *binders*, and the two id spaces should not be conflated.
///
/// # Identity-contamination rule (load-bearing)
///
/// `NodeId` is embedded inline on `TypedExpr` (`crate::ccl::expr`), whose
/// `PartialEq` is hand-written rather than derived precisely so it can
/// **exclude** it. Provenance is metadata, not part of a node's value: two nodes
/// that are structurally equal as values must still compare equal even with
/// different `NodeId`s. The structural-equality memoization the phases rely on
/// (`uniquify`'s memo, `planning`'s predicate memo) depends on this — including
/// `node_id` would make every node look distinct and the memo tables would
/// never hit. (Nodes are never hashed by value — `TypedExpr` has no `Hash` impl
/// — so there is no equality/hash pair to keep consistent here; `NodeId`'s own
/// `Hash` is for using it as a map key.)
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(u64);

static FRESH_NODE_ID: AtomicU64 = AtomicU64::new(1);

impl NodeId {
    /// The reserved sentinel id for [`TypedExpr`](crate::ccl::expr::TypedExpr)'s
    /// `Default`.
    ///
    /// `Default` exists only so `std::mem::take` can move an `Expr` out of a
    /// slot, leaving a transient throwaway behind that is immediately
    /// overwritten. Giving that throwaway a *reserved* id (rather than minting a
    /// fresh one) keeps it from polluting an open recording: the recorder's
    /// `on_mint` ignores this id, and `Default` constructs with it directly
    /// rather than through [`TypedExpr::new`](crate::ccl::expr::TypedExpr::new).
    ///
    /// `FRESH_NODE_ID` starts at 1, so 0 is never minted — a placeholder node is
    /// always distinguishable from a real one. It must never persist into a
    /// checked tree; `assert_unique_node_ids` backstops that invariant.
    pub(crate) const PLACEHOLDER: NodeId = NodeId(0);

    /// Mint a globally-fresh node id. The only way to construct a `NodeId`.
    pub fn fresh() -> Self {
        NodeId(FRESH_NODE_ID.fetch_add(1, Ordering::Relaxed))
    }

    /// The id's underlying number, for use as an opaque serialization handle
    /// (the inspector wire shape carries a `NodeId` as a JSON number; see
    /// [`crate::inspector_model`]). This is the *only* place the numeric value
    /// is observed — internal logic compares ids by equality, never by value —
    /// so it is exposed solely so a client can round-trip a handle, not to give
    /// the value any in-compiler meaning.
    pub fn as_u64(self) -> u64 {
        self.0
    }
}

impl std::fmt::Debug for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NodeId({})", self.0)
    }
}

// Wire shape (inspector, feature `serde`): a bare JSON number. A `NodeId` is an
// opaque handle the client round-trips, so it serializes as its underlying
// `u64`, read off the field directly, not as a struct. Hand-written rather than
// `#[serde(transparent)]` because the inner field is private. Nothing in the
// compiler reads the number — ids are compared by equality — so the only
// readers are this impl and [`NodeId::as_u64`], which the inspector model uses
// to project an id onto the wire outside a `Serialize` context.
//
// TODO(wire-stability): the mint-order value is not stable across compiler
// changes — anything that shifts upstream mint *counts* renumbers every later id,
// so a semantically tiny change rewrites every subsequent `nodeId` and every
// `paneLinks` endpoint in the golden fixtures. The fix belongs in the
// serialization layer rather than here, leaving `NodeId` as the internal identity:
// one deterministic walk of the snapshot assigns dense first-encounter indices
// (the uniquify binder-index precedent), so mint-count changes produce no fixture
// diff and a genuine reordering produces one proportional to it. Not yet
// implemented.
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

/// What an edge asserts about its two endpoints — a **set**, because one pair of
/// ids can carry both labels at once.
///
/// Each label is one row column, closed transitively:
///
/// * **ancestry** — the closure of `parents`: the downstream node descends from
///   the upstream one, every hop between them having consumed the node before it
///   to produce the next. Reflexive, so a surviving node is its own ancestor;
///   the column itself is irreflexive, since an in-place rewrite that keeps a
///   node's id is a *preserve* and records nothing.
/// * **blame** — the closure of `blame`: the downstream node is related to, but
///   did not consume, the upstream one. A blamed id may name a node still alive
///   elsewhere in the output tree, which is why it is not an ancestry claim.
///
/// The closure is **weakest-link** ([`then`](Self::then)): a path is ancestry
/// only while every hop on it is an ancestry hop, and one blame hop anywhere
/// makes the whole path blame. Without that rule the label would decay into
/// "reachable somehow" over two hops: a node does not descend from something it
/// is only blamed on. Paths meeting at one endpoint pair [`union`](Self::union)
/// their labels, which is how a pair comes to carry both.
///
/// The set is never empty: a label set exists only where an edge does.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EdgeLabels {
    ancestry: bool,
    blame: bool,
}

impl EdgeLabels {
    /// *Descends from*, alone — a `parents` hop, and the identity of
    /// [`then`](Self::then): the zero-length path from a surviving node to
    /// itself is ancestry, which is what makes a dense self-edge read as
    /// ancestry rather than needing a special case.
    pub const ANCESTRY: Self = EdgeLabels {
        ancestry: true,
        blame: false,
    };

    /// *Related to, but not consumed*, alone — a `blame` hop.
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

    /// Extend a path by one hop: the weakest-link composition.
    ///
    /// Ancestry survives only if both the path so far and the hop are ancestry;
    /// blame appears as soon as either is blame, because a path may take the
    /// blame reading of any hop that offers one. Associative, with
    /// [`ANCESTRY`](Self::ANCESTRY) as its identity, so the sweep can carry one
    /// label per root and fold hops in any order.
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

/// One end of a labelled edge: the id at the far end, and what the edge to it
/// asserts.
///
/// The accessors hand back these rather than bare ids because the label is the
/// content of the edge, not a detail to project away — a consumer that cannot
/// tell blame from ancestry cannot choose to render or prune it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Link<T> {
    /// The id at the far end of the edge.
    pub id: T,
    /// What the edge to it asserts.
    pub labels: EdgeLabels,
}

/// A folded bidirectional relation between two id domains, its edges labelled
/// by what they assert ([`EdgeLabels`]).
///
/// **One entry per `(upstream, downstream)` pair**, holding the label set: a
/// pair reached both by ancestry and by blame is one edge carrying both,
/// never two edges disagreeing about one pair.
///
/// **Dense**: an id that survived a phase appears as its own ancestry self-edge,
/// so there is one uniform edge kind and no identity special case. Self-edges
/// are derivable (an id present in both snapshots is its own edge) and so are
/// the two directions from each other, so a later sparse re-encoding behind the
/// accessors is a pure re-encoding — consumers must go through
/// [`upstream`](Self::upstream) / [`downstream`](Self::downstream) /
/// [`edges`](Self::edges) and never touch the raw maps. The accessors expose the
/// labels, so that promise covers what an edge *asserts* as well as which pairs
/// exist.
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

/// A pane node's source attribution — the blame channel's terminal form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceAttribution {
    /// Source spans this node traces to. **Empty** = machinery with no source
    /// anchor (a *known* node with no span) — deliberately distinct from a node
    /// that is absent from the [`SourceProjection`] entirely (a node the
    /// projection knows nothing about).
    pub spans: Vec<Span>,
    /// How the node came to exist — **mandatory**. A direct image is
    /// [`RewriteTag::direct_image`] (`{via: Lower, nature: Source, label:
    /// "lower.image"}`), never an absence; every other tag names the rewrite
    /// that produced the node. Null-compressed on the wire when the tag
    /// [`is_source`](Nature::is_source).
    pub rewritten: RewriteTag,
}

/// How a rewritten node came to exist, for tooltips and display policy.
///
/// `Hash`/`Eq` are what let a [`ProvenanceTable`] intern the whole triple as one
/// [`TagId`]. The recording site fixes `label` and `nature`, the enclosing
/// [`PhaseScope`] supplies `via`, and both are settled before a row is written,
/// so the triple is one value rather than three columns.
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
    /// The tag a **lowered expression root** carries: `{via: Lower, nature:
    /// Source, label: "lower.image"}` — a tag, never an absence.
    ///
    /// An interior image shares the `"lower.image"` label but carries
    /// `Nature::Machinery`, per the structural rule on
    /// `LoweringContext::tag_source`, so this constructor is specifically the
    /// root case.
    pub fn direct_image() -> Self {
        RewriteTag {
            via: Phase::Lower,
            nature: Nature::Source,
            label: "lower.image",
        }
    }
}

/// Per-pane node → attribution. The lowering-projection instance (folded from
/// the `LoweringLog` at the lowering boundary) is always-on; a downstream
/// pane's instance is materialized by [`fold`] at snapshot-serve time.
pub type SourceProjection = HashMap<NodeId, SourceAttribution>;

/// A history-integrity violation surfaced by a fold. The folds' error channel,
/// and every class in it is a defect: a gate asserts the whole vector empty.
///
/// # The classes name a detection role, not two defects
///
/// One unrecorded mint produces either class or both, according to what became
/// of the node downstream. It surfaces as [`Leak::Unrecorded`] while it survives
/// into the output pane, as [`Leak::DanglingParent`] once a recorded rewrite
/// consumes it, and as both when it is copied and also survives. Neither class
/// identifies the site to fix on its own.
///
/// What the split carries is which half of the recording failed across a whole
/// fold. `Unrecorded == 0` says a recording scope was open at every mint in the
/// span. A `DanglingParent` count over a zero `Unrecorded` count says the scopes
/// are open and that some producer upstream of the span never rowed the ids
/// those recordings name. That reading is what holds the first pane pair out of
/// the gate; see `MaterializedPanes::gated_pane_pairs` in `crate::ccl::panes`.
///
/// Each class is reported once per distinct id. [`fold`] sorts and dedups its
/// vector, so a dangling parent that four rows name is one entry.
///
/// # Deaths and duplicates are not classes
///
/// An input id absent from the output pane **died**. That is the set difference
/// `input_ids ∖ output_ids`, which no row declares and which every ordinary
/// rewrite produces, so [`fold`] returns the deaths as their own collection for
/// the inspector to read.
///
/// `Leak::Duplicate` (one id at two tree positions) is a tree invariant, checked
/// pipeline-wide by `assert_unique_node_ids` rather than by a fold. Nor is any
/// class shaped like a claim about a rewrite. A row describes a node, so "two
/// rewrites did X" has nowhere to live. The two invariants that are properties
/// of a record, one row per id and every row anchored through some channel, are
/// asserted at [`ProvenanceTable::record`], at the site that would violate them.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Leak {
    /// Found walking the **output tree**: an output-pane id with no row that the
    /// input pane does not hold either, a `fresh()` where a preserve was
    /// intended. Nothing explains why it is in the output tree.
    Unrecorded { output: NodeId },
    /// Found walking the **table**: a row's parent edge names an id the fold
    /// never saw. No row it read produced that id and the input pane does not
    /// hold it, so a recorded node's ancestry stops at an id that describes
    /// nothing.
    ///
    /// **One class for both edge shapes.** The sole parent of a freshened copy
    /// and one consumed id of a fusion are the identical condition, an edge to
    /// an id outside the fold. Telling them apart would mean recording the shape
    /// of the rewrite, which the `parents` column does not carry: its
    /// cardinality already expresses 1:1, 1:many and many:1, and nothing else
    /// about the shape was ever read.
    DanglingParent { parent: NodeId },
}

/// The [`SourceAttribution`] a recorded node carries: the ordered, deduplicated
/// union of its attribution sources' spans, tagged with the row's tag.
///
/// **The sources are `parents` ∪ `blame`** — both channels, `parents` first and
/// then blame's distinct additions. Parentage takes precedence in the *order*,
/// which is what keeps the projection deterministic, but blame is never dropped:
/// a rewrite that names blame is saying "these outputs are also about that
/// node", not "attribute them there instead". A row with no parents (the pure
/// insertion) has blame as all there is; a row with no blame — the common case,
/// blame being named at a handful of sites, all in the mutability phases —
/// resolves through what it was made from, which is why walking the parent
/// edges recovers a source location for almost every node.
///
/// The union is **unlabelled**: a span is a span whichever channel named the
/// node it came from, so this function reads the two columns as one sequence.
/// The distinction they carry is spent in the [`ProvenanceMap`] instead, where each
/// column labels the edges it contributes ([`EdgeLabels`]) — `mut_elim`'s
/// `enter(stmt_id)` + `blame(for_id)` is the shape: the products descend from
/// the statement and are merely *related to* the loop keyword, and both spans
/// are theirs.
///
/// A source id absent from `attr` contributes no spans (it has no known source),
/// which is legal: a node whose every source is unknown gets `spans: []`, the
/// "known node, no source anchor" case, deliberately distinct from a node absent
/// from the projection entirely.
fn attribute(
    table: &ProvenanceTable,
    id: NodeId,
    tag: RewriteTag,
    attr: &SourceProjection,
) -> SourceAttribution {
    // No *phase* row may carry `Nature::Source`: `Source` means "this node is a
    // source construct's direct one-to-one translation", which only lowering can
    // produce — a later phase rewriting a node changes what it is. The guard sits
    // here, on the node being attributed by a rewrite, not on projection entries:
    // an *inherited* Source tag on a preserved id in a later pane is legal and
    // reaches the projection by clone, never through this fn. See
    // `design/provenance.md`, "The provenance model".
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

/// A row's one-hop upstream edges, each with what that hop asserts: `parents` as
/// ancestry hops, `blame` as blame hops.
///
/// **One entry per id.** A row naming an id in both columns is one hop carrying
/// both labels, not two hops — the pair `(p, x)` is a single edge, and emitting
/// it twice would leave the endpoint pair with two disagreeing labels for the
/// fold to pick between. Parents come first so the order is deterministic; the
/// linear scan is over a row's own columns, which hold a handful of ids.
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

/// Fold the rows the phases between two panes wrote into the [`ProvenanceMap`]
/// joining them, the output pane's [`SourceProjection`], the input ids that
/// **died**, and any integrity [`Leak`]s.
///
/// The deaths are `input_ids ∖ output_ids`, returned as a product rather than as
/// a leak class: nothing declares a fate, so the difference fires on every
/// ordinary rewrite and is data the inspector reads. Every [`Leak`] is a defect.
///
/// `phases` are the ones between the two panes, and they are what restricts a
/// whole-compile table to that span: one table covers every session a compile
/// opens, so a row's `via` is the only thing that says which span produced it.
/// **An id whose row lies outside `phases` is, to this fold, an ordinary
/// un-produced id** — an input-pane node if the input pane holds it, and unknown
/// otherwise. Without that restriction an `Infer`-produced input-pane id would
/// resolve straight past the post-channelize pane it is supposed to bottom out
/// in.
///
/// `input_ids` / `output_ids` are the two pane snapshots; `upstream_attr` is the
/// input pane's already-resolved projection, which untouched ids inherit
/// unchanged.
///
/// # The algebra
///
/// A node's provenance annotation is a **map from input-pane ids to the label of
/// the path that reached them** ([`EdgeLabels`]):
///
/// ```text
/// roots(x) = ⋃ { roots(p) ∘ hop(p → x) : p ∈ parents(x) ∪ blame(x) }
/// roots(x) = { x ↦ ancestry }                  if x is an input-pane id
/// ```
///
/// where `hop(p → x)` is ancestry for a `parents` edge, blame for a `blame`
/// edge and both for an id the row names in both columns; `∘` extends every path
/// in `roots(p)` by that hop, weakest-link ([`EdgeLabels::then`]); and `⋃` unions
/// the labels of paths that arrive at one root. The empty union `∅` is a row
/// whose parents are all unknown.
///
/// Labelled root maps under that union form a commutative monoid — `union` on
/// [`EdgeLabels`] is a join, and `then` distributes over it — and commutativity
/// plus associativity, plus one row per id so no node has two definitions to
/// order, are exactly what make the fold insensitive to the order the rows were
/// written in. (Idempotence buys cheapness, not order-freeness.)
///
/// Order-freeness is load-bearing, because write order is not chronology: rows
/// are written when their guard drops, so an enclosing rewrite's rows land after
/// the rows of the rewrites nested inside it.
///
/// Ids born and consumed inside those phases are interior vertices on a path and
/// compose away; the self-edge for an untouched id falls out; the N:M bipartite
/// product of a fusion falls out of its product rows each holding the whole
/// consumed set as parents.
///
/// # The fold is one ascending sweep
///
/// Every edge runs from a smaller [`NodeId`] to a larger one: a row's parents and
/// its blame are alike ids the rewrite *read*, and the node itself was minted
/// afterwards from one process-global monotone counter (a produced id is
/// *captured* via [`on_mint`], never declared). A node is therefore never its
/// own ancestor, so **ascending `NodeId` order is a topological order** and one
/// sweep suffices — no fixed point, no memo, no cycle guard. [`sweep_metrics`]
/// measures the falsifier (a backward edge).
///
/// A node reachable from nothing still keeps an entry holding `∅`, which is what
/// distinguishes "known, with empty ancestry" from "the fold has never heard of
/// this id" ([`Leak::Unrecorded`]).
///
/// # The attribution channel rides along, and is not a monoid
///
/// `attr` is resolved in the same sweep, and needs the same topological order for
/// a different reason: a row's attribution sources are ids that existed when the
/// rewrite ran. But attribution has no join — one node cannot carry two
/// `via`/`label` pairs — so it depends on there being exactly **one row per id**,
/// not on any algebra. That is the invariant [`ProvenanceTable::record`] asserts at
/// write time, where the second writer is standing.
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

    // The vertex set: every id the fold knows, in mint order — which is a
    // topological order of the edges (see the doc comment).
    let mut vertices: Vec<NodeId> = table
        .rows_in(phases)
        .chain(input_ids.iter().copied())
        .collect();
    vertices.sort_unstable();
    vertices.dedup();

    let mut roots: HashMap<NodeId, HashMap<NodeId, EdgeLabels>> = HashMap::new();
    let mut attr: SourceProjection = upstream_attr.clone();

    for &x in &vertices {
        let Some(tag) = table.tag_in(x, phases) else {
            // No row among these phases: an input-pane id, reachable from itself and
            // nothing else. A node descends from itself, so the self-edge is an
            // ancestry edge. Its upstream attribution passes through unchanged.
            roots.insert(x, HashMap::from([(x, EdgeLabels::ANCESTRY)]));
            continue;
        };

        let mut r: HashMap<NodeId, EdgeLabels> = HashMap::new();
        for (p, hop) in row_hops(table, x) {
            debug_assert!(
                p < x,
                "row {x:?} names the younger id {p:?} as an upstream — both columns hold \
                 ids the rewrite read before it minted, so ascending NodeId order must be \
                 a topological order of the definition graph",
            );
            // An upstream older than `x` is already resolved if the fold knows
            // it at all. No entry means it is neither an input-pane id nor
            // produced here: an *ancestry* hop there stops at an id that
            // describes nothing, while a blame-only hop is the same
            // silence `attribute` keeps for a blamed id with no known spans —
            // blame is a pointer at material the relation need not hold, so it
            // contributes no edge and no class.
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

    // An input id absent from the output pane **died**. Nothing declares a fate,
    // so this difference is the whole death report rather than a residue of one,
    // which is why it is a product of the fold and not a leak class.
    let mut deaths: Vec<NodeId> = input_ids.difference(output_ids).copied().collect();
    deaths.sort_unstable();

    // The pane projection is exactly the output nodes' attributions: transients
    // (born and consumed within the phase) drop out, untouched ids keep their
    // inherited entry, and an output id with no attribution is legitimately
    // absent (distinct from a present-but-empty `spans`).
    let projection: SourceProjection = output_ids
        .iter()
        .filter_map(|o| attr.get(o).map(|a| (*o, a.clone())))
        .collect();

    // One entry per distinct defect. A dangling parent is discovered once per row
    // that names it, so the raw vector counts rows rather than broken ancestry
    // targets: the id every row of a specialized definition points at would be
    // reported once per copy.
    leaks.sort_unstable();
    leaks.dedup();

    (ProvenanceMap { down, up }, projection, deaths, leaks)
}

/// What one ascending sweep of [`fold`] costs over a given set of phases, and whether
/// the sweep's premise holds. Measurement-only.
///
/// [`backward_edges`](Self::backward_edges) is the falsifier: ascending `NodeId`
/// order is only a topological order if every edge runs from a smaller id to a
/// larger one, so a non-zero count is exactly the number of vertices the sweep
/// would have to revisit — the fixed point it claims not to need.
#[cfg(test)]
pub(crate) struct SweepMetrics {
    /// Vertices the sweep visits — and, since `roots` only ever grows, its peak
    /// entry count.
    pub vertices: usize,
    /// Provenance edges (`upstream → node`, either label) the fold reads.
    pub edges: usize,
    /// Edges running from a larger `NodeId` to a smaller one — the revisit
    /// count. Must be zero.
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
            if p >= x {
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

// ===========================================================================
// The node table: the recording, keyed by the node it describes.
//
// One row per recorded *node*, which is how every consumer asks its question
// ("where did this node come from?"), so a lookup is a hash probe and the pane
// fold is one ascending sweep over the rows a pane pair's phases wrote.
// ===========================================================================

/// An interned [`RewriteTag`] — a [`ProvenanceTable`] row's `tag` column.
///
/// The whole `{via, nature, label}` triple is interned as one id because the
/// three are settled together: `via` is the session's phase, and
/// `nature`/`label` are the two literals at the [`enter`] call. There are on the
/// order of fifty distinct triples in the compiler — a property of the source,
/// not of the program being compiled — so one index buys all three columns and a
/// row carries a single handle instead of three fields.
///
/// A `TagId` is not the identity of a *rewrite rule*: `via` is part of the
/// interned triple, so a shared helper recorded under whichever [`PhaseScope`] is
/// open around it — `subst`'s `"subst.transport"`, `PredMemo::rebuild`'s
/// `"predicate.rebuild"` — interns one tag per phase it runs under. The `label`
/// alone names the rewrite.
///
/// Only meaningful against the table that minted it: the ids are dense indices
/// into that table's tag vector, not global constants.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct TagId(u32);

/// One recorded node's row. Both edge kinds plus the interned tag; see
/// [`ProvenanceTable`] for why there is no span column, and
/// [`record`](ProvenanceTable::record) for the two invariants a row must satisfy.
struct Row {
    parents: Vec<NodeId>,
    blame: Vec<NodeId>,
    tag: TagId,
}

/// Per-compile provenance keyed by the node each record describes: `NodeId → {
/// parents, blame, tag }`.
///
/// # The two edge kinds stay separate
///
/// `parents` are the ids a rewrite consumed to produce the node — the node the
/// recording named, or a fusion's whole consumed set. `blame` are the ids the
/// rewrite is *related to* but did not consume; they may still be alive
/// elsewhere in the tree, and they say nothing about any node's fate. Both are
/// relations over the same pair of ids and both reach the fold, so what the
/// columns buy is the **label** the fold puts on the edge ([`EdgeLabels`]).
/// Merging them would answer "what was this made from" with a node that merely
/// survives beside the answer (see the module docs, "Two columns, because they
/// are two kinds of relation").
///
/// # There is no span column, deliberately
///
/// A node's spans are *derived*: walk `parents` back until the walk reaches a
/// node the lowering projection covers, which is where real spans live. That
/// walk is a handful of hops and does not lengthen as programs grow, so a span
/// column would be a denormalization paid on every row ever minted, for a
/// lookup the parent edges already answer.
///
/// # "No row" is an expected state, not an error
///
/// The key space is `NodeId`, and a `NodeId` can be *addressed* without ever
/// having been *recorded*. So every read tolerates an unknown id —
/// [`parents`](Self::parents) and [`blame`](Self::blame) come back empty,
/// [`tag`](Self::tag) `None` — and, the sharper half of the same rule,
/// [`deaths`](Self::deaths) considers **only ids a [`record`](Self::record)
/// actually wrote**. A death is the set difference `recorded ∖ live`, so a
/// difference taken over addressed-but-unwritten ids would report nodes that
/// never existed as deaths. Row enumeration is private for exactly that reason —
/// [`deaths`](Self::deaths) and the pane fold's `rows_in` are the operations
/// that legitimately need it, and each takes the difference against something
/// (a live set, a set of phases) rather than against the key space.
///
/// Refinement-predicate interiors **are** recorded here. They are `TypedExpr`s
/// inside a `Type::Refinement`'s predicate, carrying real `NodeId`s from the same
/// global counter and interleaved with main-tree ids, and `collect_tree_ids`
/// enumerates them — so the fold must explain them and this table must hold their
/// rows (`design/provenance.md`, "Walking the ids").
///
/// **All three crossings of the predicate boundary record.** *Entry*: lowering
/// sweeps the finished term, and inference records `singleton_predicate` against
/// its literal. *Transformation*: `PredMemo::rebuild` either carries the ids or
/// records against the node whose type holds the predicate. *Raising* — planning
/// lifting a term back into the main tree — attributes the raised material to the
/// predicate rather than to the term-tree site, because a clone's copy names the
/// node it was freshened from (`design/provenance.md`, "Walking the ids").
///
/// Admitting these ids was a **population** change, not a schema change: they
/// already had addresses here, so no column moved. The measurement that justified
/// it, at the `post-inference..join-planned` audit span: the residue was
/// [`Leak::DanglingParent`] edges and nothing else, every one a
/// predicate-interior id of the input tree, and admitting them took every gated
/// class to zero.
///
/// The backing store is a plain map on purpose: the row *semantics* above are
/// what a reader has to check, and a paged/interned column encoding would be a
/// pure re-encoding behind these accessors — the same promise
/// [`ProvenanceMap`] makes.
#[derive(Default)]
pub(crate) struct ProvenanceTable {
    rows: HashMap<NodeId, Row>,
    /// Tag by [`TagId`] index — the interning table's forward direction.
    tags: Vec<RewriteTag>,
    /// Tag → its already-assigned id, so equal tags share one row column.
    interned: HashMap<RewriteTag, TagId>,
}

// The accessors are the table's whole contract and are exercised as such by this
// module's tests; the compiler itself only ever writes rows.
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
        // u32 is not a real limit: the distinct-tag count is a source-code
        // property — one triple per label-and-nature pair the compiler writes —
        // not a function of the program being compiled.
        let id = TagId(
            u32::try_from(self.tags.len()).expect("more distinct rewrite tags than a u32 indexes"),
        );
        self.tags.push(tag);
        self.interned.insert(tag, id);
        id
    }

    /// Record one produced node's row.
    ///
    /// Three invariants, all of them properties of the write and all of them
    /// checked here, at the site that would violate one, rather than at a fold
    /// that only runs when someone materializes a pane:
    ///
    /// * **one row per id.** Attribution has no join — a node cannot carry two
    ///   `via`/`label` pairs — so a second writer for an id has no answer, and
    ///   silently overwriting would make the surviving row a lie about which
    ///   rewrite made the node. Ids come from one monotone counter and
    ///   `produced` is captured from the construction hook, so a second write
    ///   means a rewrite claimed to mint what already existed.
    /// * **every row is anchored through some channel** — consumption or blame.
    ///   A row with neither cannot explain where the node came from, which is
    ///   the whole content of a provenance record. (A row with blame but no parents
    ///   is the legal *pure insertion*: a node placed over surviving material,
    ///   attributed through blame, with genuinely no ancestor.)
    /// * **a node is not its own parent.** A node's provenance is the product of
    ///   its parents', so an id on both sides would define itself in terms of
    ///   itself — the one construct that makes an edge run backwards and forces
    ///   [`fold`] to a fixed point rather than a single ascending sweep. An
    ///   in-place rewrite that keeps its id is a **preserve**: it records
    ///   nothing, and that is correct, because identity here is *referent*
    ///   identity and the pane resolves it by shared id.
    ///
    /// The checks are `debug_assert!`s because this is the construction hot
    /// path — every mint under an open guard lands here — and each one costs a
    /// hash probe or a scan. What is gated is the checking; the row written is
    /// the same row in every build.
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

    /// The ids consumed to produce `id`; empty for an unrecorded id. Predicate
    /// interiors used to be the standing example of one and no longer are — they
    /// are recorded (see the type's docs).
    pub(crate) fn parents(&self, id: NodeId) -> &[NodeId] {
        self.rows.get(&id).map_or(&[], |r| r.parents.as_slice())
    }

    /// The ids `id`'s rewrite is related to but did not consume; empty for an
    /// unrecorded id, and empty for the common case of a row that mirrors its
    /// parents' attribution.
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

    /// The rewrite that produced `id` **if that rewrite is one of `phases`**,
    /// else `None`.
    ///
    /// This is what restricts a whole-compile table to one pane pair: to that
    /// pair, an id produced by a phase it does not span is an ordinary
    /// un-produced id, which is exactly how the input pane's own nodes have to
    /// read for the fold to bottom out there.
    pub(crate) fn tag_in(&self, id: NodeId, phases: &[Phase]) -> Option<RewriteTag> {
        self.tag(id).filter(|tag| phases.contains(&tag.via))
    }

    /// The ids `phases` produced, in arbitrary order.
    ///
    /// Private, for the rule [`deaths`](Self::deaths) shares: enumerating rows is
    /// only ever correct against a set of phases, since a `NodeId` can be
    /// addressed without ever having been recorded. This module's folds are the
    /// only callers.
    fn rows_in<'a>(&'a self, phases: &'a [Phase]) -> impl Iterator<Item = NodeId> + 'a {
        self.rows
            .iter()
            .filter(|(_, row)| phases.contains(&self.tags[row.tag.0 as usize].via))
            .map(|(id, _)| *id)
    }

    /// Ids produced by the phases from `start` through `end` inclusive that are
    /// absent from `live`: what those phases built and then discarded.
    ///
    /// The range reads every phase between the two, [`Phase`]'s declaration
    /// order being pipeline order, so `deaths(Phase::Inline, Phase::Channelize,
    /// live)` covers `Transact` and `Letrec` as well.
    ///
    /// **Narrower than the fold's death product**, and the two answer different
    /// questions. The fold takes `input_ids ∖ output_ids` over two pane walks, so
    /// it sees a node no phase ever produced — a lowered node dropped by a later
    /// rewrite — and it cannot see a node born and discarded between the panes.
    /// This one is the mirror image: every id here has a row, so a never-produced
    /// node is invisible to it, and an intra-phase transient is exactly what it
    /// reports. Reach for the fold to ask what died between two trees, and for
    /// this to ask what a phase churned.
    ///
    /// The difference is taken over rows in range, never over the key *space*:
    /// the key space is a global counter, so it addresses ids this compile never
    /// built, and an id that was addressed but never recorded describes no node
    /// that could have died. Sorted, so a caller's report is deterministic.
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

    /// The distinct phases this table holds rows for, deduplicated.
    ///
    /// A tag is interned only when a row is written under it, so the interning
    /// table's phases are exactly the phases that recorded something. Test-only:
    /// it answers "which phases rewrote this program", which is a question about
    /// a compile rather than about a node, and nothing in the pipeline asks it.
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

// ===========================================================================
// The recorder: an ambient thread-local stack of open recordings that turns node
// construction into provenance rows as a byproduct of the rewrite.
//
// Discipline mirrors `infer_var::ACTIVE_ARENA`: install a capture target at a
// boundary, let construction hooks feed it, drain at the boundary. The compile
// path is single-threaded (the only `thread::spawn`s are runtime I/O), so a
// per-thread stack is safe. An empty stack means recording is off — the
// overwhelmingly common case (tests, non-recorded compiles), reduced to a cheap
// emptiness check on the construction hot path.
// ===========================================================================

thread_local! {
    /// The open recordings, innermost last. Empty ⇒ recording off. A
    /// construction hook ([`on_mint`]/[`on_copy`]) pushes into the innermost
    /// one only.
    static RECORDING_STACK: RefCell<Vec<OpenRecording>> = const { RefCell::new(Vec::new()) };

    /// The [`ProvenanceTable`] a closing guard writes its rows into, installed by
    /// a [`TableSession`]. `None` ⇒ no table, and the write is a silent no-op,
    /// so there is one code path either way.
    ///
    /// Installed for a **whole compile** rather than per phase, unlike
    /// [`ACTIVE_PHASE`]: a row is keyed by a node id, which is unique for the
    /// life of the process, so one table spans every phase a compile runs and no
    /// id can collide between them.
    static ACTIVE_TABLE: RefCell<Option<ProvenanceTable>> = const { RefCell::new(None) };

    /// The phase a row is tagged with, installed per phase by a [`PhaseScope`].
    /// `None` ⇒ no phase is being recorded: a guard still captures into itself,
    /// but writes nothing when it drops.
    ///
    /// The phase is ambient for the scope's extent because a [`RewriteTag`] needs
    /// it and the recording site cannot supply it: an [`OpenRecording`] carries the
    /// two literals at its [`enter`] call (`label`, `nature`) and knows nothing
    /// about which phase is running, while the boundary that opens the scope
    /// knows exactly that.
    static ACTIVE_PHASE: RefCell<Option<Phase>> = const { RefCell::new(None) };

    /// Lowering's log, installed by the always-on [`LoweringSession`]. `None` ⇒
    /// lowering is not running. Lowering records into its own sink because its
    /// attribution is a literal span rather than a reference resolved later (see
    /// [`LoweringStep`]).
    static ACTIVE_LOWERING_LOG: RefCell<Option<LoweringRecord>> = const { RefCell::new(None) };
}

/// One in-flight recording, accumulating the ids born and copied while its guard
/// is the innermost one open. Finalized when the [`RecordingGuard`] drops. The
/// produced side is captured from the construction hooks rather than declared,
/// which is what makes a row a byproduct of the rewrite.
struct OpenRecording {
    label: RewriteLabel,
    /// Extra ids the rewrite consumed, added through
    /// [`RecordingGuard::also_consumes`] for a fusion. The produced side is
    /// discovered from the construction hooks, never declared.
    ///
    /// Empty at open, and — `also_consumes` having no production caller — empty
    /// for every rewrite in the compiler today. See [`named`](Self::named).
    consumed: Vec<NodeId>,
    /// The id the recording site named — the node about to be rewritten. `None`
    /// for a [`copy_frame`], which names no node.
    ///
    /// Every id minted in the guard's extent takes this as a **parent**: the
    /// output was made from that node. The claim says nothing about whether that
    /// node dies, which is what makes it safe to name a node the rewrite keeps
    /// (keep the id, mint a wrapper over a child). Death is the live-set
    /// difference between two panes, never a record-time claim.
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
    /// Finalize this recording into the installed [`ProvenanceTable`], one row per
    /// node it produced.
    ///
    /// Two products:
    ///
    /// * **the mints** — every id minted in the guard's extent takes the named
    ///   node as its parent. With a fusion ([`RecordingGuard::also_consumes`]) it
    ///   takes the named node plus every extra id, which is the many:1 shape and
    ///   the only place any id is named at record time. Either way the parents
    ///   are ancestry edges, not fate claims, so naming a node that survives
    ///   costs an over-broad edge and never a phantom death.
    /// * **the captured freshens** — each `(origin, fresh)` pair the `on_copy`
    ///   hook reported rows the fresh id on the node it was duplicated from, not
    ///   on the named node. A copy's origin is discovered through the hook rather
    ///   than declared: every duplication path runs through [`copy_id`], called
    ///   from `TypedExpr`'s `Clone`, so capture needs no help from the site.
    ///
    /// A guard that minted nothing, freshened nothing and fused nothing writes no
    /// row. That is the **preserve** case — an in-place mutation such as `*op =
    /// BinOpKind::Concat` — and it is what lets a phase open a recording on every
    /// rewrite *attempt* rather than only on the ones that fire.
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

    /// Row each captured freshen on the node it duplicated. A copy mirrors its
    /// origin rather than re-attributing, so it carries no blame of its own.
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

    /// A [`copy_frame`] names no node, so it has nowhere to attach a consume or
    /// a mint: a row needs a parent. Anything captured into one would vanish
    /// from the record rather than land somewhere wrong. A phase site that trips
    /// this wants [`enter`] on the node it is rewriting; a lowering site wants
    /// [`lowering_leaf`] for its mints.
    fn assert_copy_only(label: RewriteLabel, consumed: &[NodeId], births: &[NodeId]) {
        debug_assert!(
            consumed.is_empty() && births.is_empty(),
            "copy frame {label:?} captured consumes {consumed:?} and mints {births:?} — a \
             recording that names no node has nothing to attach them to. A phase site wants \
             `enter` on the node being rewritten; a lowering leaf mint belongs in \
             `lowering_leaf`",
        );
    }

    /// Finalize this recording into a [`LoweringLog`]. Lowering opens a guard
    /// only to capture ambient copies — uncurry's template-interior freshens and
    /// the compare-chain operand freshens — while its leaf mints append directly
    /// via [`lowering_leaf`]. So a lowering guard carries no consumed ids and no
    /// births, and only the captured per-origin copies are written here, as
    /// [`LoweringStep::Copy`]s mirroring their origins' folded entries.
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
/// sweep's coarse ones, because the fold is last-write-wins. Measured on the
/// pipeline corpus: 318 nodes would be clobbered without it, and no leak class
/// would report anything, since a clobbered node is still explained.
/// `the_predicate_sweep_skips_already_recorded_nodes` pins the skip.
pub(crate) fn lowering_predicate_leaf(id: NodeId, span: Span, nature: Nature, label: RewriteLabel) {
    if id == NodeId::PLACEHOLDER {
        return;
    }
    ACTIVE_LOWERING_LOG.with(|slot| {
        if let Some(rec) = slot.borrow_mut().as_mut() {
            if !rec.recorded.insert(id) {
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

/// Run `f` against the installed [`ProvenanceTable`], or do nothing when no
/// [`TableSession`] is installed — the one place a flush touches the sink, so
/// "recording is off" is a single silent no-op rather than a branch per row.
fn with_table(f: impl FnOnce(&mut ProvenanceTable)) {
    ACTIVE_TABLE.with(|slot| {
        if let Some(table) = slot.borrow_mut().as_mut() {
            f(table);
        }
    });
}

/// RAII installer for the per-compile [`ProvenanceTable`] — the sink every closing
/// guard writes into.
///
/// It covers a **whole compile** rather than a phase, so it outlives and nests
/// around every [`PhaseScope`] that compile opens. `Drop` clears the slot, so a
/// panicking compile never leaves a stale table for the next one.
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

/// Open a copy-only recording: it consumes nothing, mints nothing, and exists to
/// capture the `(origin, fresh)` pairs a clone's freshen reports, written as
/// per-origin [`LoweringStep::Copy`]s under lowering or as one row per copy
/// under a phase scope.
///
/// This is the one recording that **names no node**, and the shape it fits is a
/// duplication with *nothing being rewritten*, where there is no id to name:
/// lowering's uncurry template-interior and compare-chain operand freshens, and
/// inference's two freshens — a refinement predicate per scheme instantiation
/// (`infer.freshen_predicate`) and a trait obligation's stored operand
/// expressions per obligation copy (`infer.freshen_obligation`). Every captured
/// copy carries its own origin from the hook, which is why this one can afford to
/// declare nothing at all —
/// [`row_per_copy`](OpenRecording::row_per_copy) never reads the named node.
///
/// A duplication performed *as part of* a rewrite uses [`enter`] instead, naming
/// the node the rewrite replaces, so the mints beside the copies have a parent.
/// [`assert_copy_only`](OpenRecording::assert_copy_only) is what keeps the two
/// apart: a mint captured here is a site that should have named a node.
///
/// `nature` is fixed at [`Machinery`](Nature::Machinery) rather than taken as an
/// argument. Under lowering a copy's nature is never read — a
/// [`LoweringStep::Copy`] mirrors the origin's already-folded attribution
/// *verbatim* — so a nature would be unobservable, and a wrong one (a
/// `Nature::Source` on a copy) would look meaningful while being inert. Under a
/// phase scope the fixed value is the honest one: a duplication that rewrites
/// nothing is plumbing by construction.
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

// ===========================================================================
// Capture keyed on node identity.
//
// A rewriting site names the node it is *about to rewrite* and declares nothing
// else. Every id minted while that guard is the innermost one open records the
// named node as its parent, which says nothing about whether the named node
// survived: death is the live-set difference between two panes, so no site predicts
// a fate.
//
// The produced side is never declared. It is a byproduct of construction,
// discovered through the mint and copy hooks. The one recording that names no
// node is `copy_frame`, lowering's copy sink, whose captured copies each carry
// their own origin.
// ===========================================================================

/// Open a recording over the node about to be rewritten, returning an RAII guard
/// that finalizes it on drop.
///
/// `named_id` is read off the node *before* the rewrite runs; every id minted
/// while this guard is the innermost one open records `named_id` as its parent.
/// The site declares nothing further — see [`OpenRecording::flush_into_table`].
///
/// A guard rather than a closure, for two reasons that outlive the ergonomics:
///
/// * **The region is a scope, not an expression.** A site may talk to the open
///   recording after opening it — `mut_elim` calls [`RecordingGuard::blame`] on the
///   next line, naming the `For` so the products resolve to the loop keyword's
///   span rather than the enclosing statement's. A closure taking only the
///   rewrite has no channel for that, so each extra channel would become a
///   parameter.
/// * **A channel may fire from a runtime-decided point inside the region.**
///   Whether a rewrite takes the arm that widens its attribution is decided by a
///   `match` on the node, potentially far below the `enter`. As a closure, that
///   means making a function's whole tail a closure body so one arm can reach
///   the recording.
///
/// The guard costs nothing in expressiveness: the id is needed only at *entry*,
/// and nothing reads the named node again at exit.
///
/// Two consequences a site does not restate:
///
/// * **A recording is where the hooks write.** An installed table captures
///   nothing on its own; the mint and copy hooks need an open recording to
///   attach to, so a rewrite that clones or mints outside one drops its pairs on
///   the floor. That is the failure mode, not a wrong parent.
/// * **Open it after any recursion into children.** A recording adopts
///   everything minted under it, so opening one around a recursive call attaches
///   the callee's own products to this node instead of theirs. Open it around the
///   rewrite alone, and after the early returns that abandon it.
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

/// RAII finalizer for an open recording. Popping and writing on `Drop` is
/// panic-safe: an unwind through an open recording still pops it, so the stack
/// is never left corrupt, and writes what was captured before the panic.
///
/// The guard is also the *only* handle on the recording it opened: the extra
/// channels ([`RecordingGuard::also_consumes`], [`RecordingGuard::blame`]) are inherent
/// methods on it, so a site cannot address a recording it does not hold — the
/// innermost one may belong to a callee or to an enclosing recursion.
#[must_use = "a dropped RecordingGuard records nothing — bind it (`let _g = …`), \
              and note `let _ = …` drops it immediately"]
pub(crate) struct RecordingGuard {
    /// The stack index this recording occupied when opened, for the LIFO
    /// tripwire.
    depth: usize,
}

impl RecordingGuard {
    /// Fusion (many:1): this rewrite **also** consumed `id`, a node the
    /// construction hooks cannot attribute because it is not the one the site
    /// named.
    ///
    /// The only channel that adds a *consumed* id beyond the named one, and so
    /// **the only place any id is named at record time** — everything else about
    /// a recording is observed. The named id joins the site's own node in the
    /// products' `parents`, asserting ancestry and nothing about `id`'s fate.
    ///
    /// A [`copy_frame`] names no node for it to sit beside, so this is
    /// meaningless there and [`assert_copy_only`] catches it.
    ///
    /// [`assert_copy_only`]: OpenRecording::assert_copy_only
    // No production caller: every rewrite in the compiler is 1:many, so each
    // recording writes one parent per product. The channel is retained because
    // nothing else can express the many:1 shape — a fusion onto an older
    // survivor has to remint (`consumed: [S, D…] → produced: [S′]`) to keep
    // parents ahead of children. Exercised by
    // `a_fusion_gives_every_product_the_bipartite_product`.
    #[allow(dead_code)]
    pub(crate) fn also_consumes(&self, id: NodeId) {
        if id == NodeId::PLACEHOLDER {
            return;
        }
        self.with_own_frame(|top| top.consumed.push(id));
    }

    /// Additional source attribution: nodes this rewrite's products are *about*
    /// beyond the one being rewritten.
    ///
    /// With no blame the products take the named node's spans, which is right for
    /// most rewrites. Naming blame **adds** to that — attribution is the union of
    /// the parents' spans and these — so a site widens the attribution rather
    /// than redirecting it.
    ///
    /// Blame relates without claiming ancestry: these ids may name nodes that
    /// survive the rewrite, so they ride the `blame` column rather than `parents`
    /// and reach the provenance map as *blame* edges ([`EdgeLabels`]), which the
    /// inspector can render or prune. Weakest-link closure keeps that distinction
    /// alive at a distance: anything reached through one of these hops is
    /// related, never descended. Naming an id here therefore asserts nothing
    /// about its fate, which is what lets a site blame a node it leaves in the
    /// tree.
    pub(crate) fn blame(&self, ids: &[NodeId]) {
        self.with_own_frame(|top| top.blame.extend(ids.iter().copied()));
    }

    /// Address *this* guard's own recording, asserting it is the innermost open
    /// one.
    ///
    /// The channels above are only meaningful about the recording the caller
    /// holds; reaching whatever happens to be on top would silently retarget a
    /// callee's or an enclosing recursion's. Same `debug_assert_eq!` convention
    /// as the LIFO tripwire in [`Drop`](RecordingGuard::drop).
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

/// A hook called from `Expr::new` for every minted [`NodeId`]. Pushes the id
/// into the innermost open recording's births, or does nothing when none is open
/// (the common case — a borrow and an emptiness check). The [`PLACEHOLDER`]
/// sentinel is ignored, so `Default`/`mem::take` throwaways are never attributed
/// to a rewrite.
///
/// [`PLACEHOLDER`]: NodeId::PLACEHOLDER
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

/// Whether a recording dropped here would write rows: a [`PhaseScope`] is
/// installed and lowering is not running.
///
/// Mirrors the routing in [`RecordingGuard::drop`], which is what makes it the
/// right precondition for [`on_mint`]'s assert. Lowering is excluded because it
/// records through the leaf channel ([`LoweringStep::Leaf`]) rather than through
/// births, so a mint with nothing recording is the designed path there, not a gap.
///
/// Not `cfg(debug_assertions)`-gated: `debug_assert!` compiles its expression in
/// every configuration and only drops the execution, so a gated helper fails the
/// release build.
fn rows_would_reach_the_table() -> bool {
    ACTIVE_LOWERING_LOG.with(|slot| slot.borrow().is_none())
        && ACTIVE_PHASE.with(|p| p.borrow().is_some())
}

thread_local! {
    /// Depth counter for [`preserve_ids`]: non-zero means a clone in progress is
    /// a **re-allocation of the same node**, not a duplication, so it must carry
    /// the origin's id rather than mint one.
    ///
    /// A counter rather than a flag because the scopes nest — a preserving copy
    /// of a tree recurses through `Clone` for every child.
    static PRESERVING_IDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Guard returned by [`preserve_ids`]. Dropping it re-enables freshening.
pub(crate) struct PreservingIds;

impl Drop for PreservingIds {
    fn drop(&mut self) {
        PRESERVING_IDS.with(|c| c.set(c.get() - 1));
    }
}

/// Open a scope in which [`TypedExpr`](crate::ccl::expr::TypedExpr)'s `Clone`
/// **preserves** ids instead of freshening them.
///
/// Reach for it through
/// [`TypedExpr::clone_preserving_ids`](crate::ccl::expr::TypedExpr::clone_preserving_ids),
/// never directly: the scope must cover the clone and nothing else, and a
/// genuine duplication performed inside one would silently produce a
/// duplicate id.
#[must_use]
pub(crate) fn preserve_ids() -> PreservingIds {
    PRESERVING_IDS.with(|c| c.set(c.get() + 1));
    PreservingIds
}

/// Run `f` with id-preserving clones — a scope over a whole *rewrite region*,
/// not over a single copy.
///
/// # TODO(predicate-domain): do not add callers without reading this.
///
/// **One legitimate user: [`PredMemo`] in *replacing* mode**, which is to say
/// [`uniquify`](crate::ccl::uniquify) and nothing else. Anything that needs a
/// preserving *copy* has one — [`TypedExpr::clone_preserving_ids`] — and should
/// use it. This scope silences the freshening for **every** clone on the thread
/// until `f` returns, including genuine duplications a callee performs, so unlike
/// the per-copy method it can manufacture duplicate ids.
///
/// It exists because what must keep its identity is not a copy but an arbitrary
/// caller-supplied *rewrite*: `f` mints and copies *into* the term (a
/// substitution materializing a template, a rule building a conjunction), and
/// those products are part of the same replacement.
///
/// The justification is **replacement, not domain**. Predicate interiors are in
/// the explanation domain and the fold explains them (`design/provenance.md`,
/// "Walking the ids"). What makes preserving honest here is that the rebuilt term stands in
/// for the original *everywhere* — which is true only because `uniquify` walks
/// the whole tree, and which `uniquify` asserts on every compile as a 1:1
/// correspondence over distinct predicate terms. A rebuild whose walk misses an
/// occurrence leaves the original alive beside its replacement, and then this
/// scope puts one id-set on two live terms.
///
/// [`PredMemo`]: crate::ccl::ccl_utils::PredMemo
/// [`TypedExpr::clone_preserving_ids`]: crate::ccl::expr::TypedExpr::clone_preserving_ids
pub(crate) fn preserving_ids<R>(f: impl FnOnce() -> R) -> R {
    let _guard = preserve_ids();
    f()
}

/// The id a clone of `origin` should carry, and the one place that decides.
///
/// Freshens by default — a clone is a sibling — reporting the pair through
/// [`on_copy`]. Inside a [`preserve_ids`] scope it returns `origin` unchanged
/// and records nothing, because no new node came into being.
pub(crate) fn copy_id(origin: NodeId) -> NodeId {
    if PRESERVING_IDS.with(std::cell::Cell::get) > 0 {
        return origin;
    }
    let fresh = NodeId::fresh();
    on_copy(origin, fresh);
    fresh
}

/// A hook called from the freshen helpers for every `(origin, fresh)`
/// duplication. Pushes the pair into the innermost open recording's copies, or
/// does nothing when none is open. Guards the [`PLACEHOLDER`] sentinel on both
/// sides, as [`on_mint`] does: a placeholder origin would fold as
/// [`Leak::DanglingParent`] against an id nothing ever records.
///
/// Asserts the same coverage [`on_mint`] does, and for the same reason: a node
/// reaches a tree by being minted or by being copied, so a check on one channel
/// alone leaves the other silent. The silence was not hypothetical — copies
/// outnumbered mints among the uncaptured nodes when the check was added.
///
/// [`PLACEHOLDER`]: NodeId::PLACEHOLDER
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

    fn span(start: usize, end: usize) -> Span {
        Span::new(start, end)
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

    /// The predicate sweep must not overwrite attribution a node already has.
    ///
    /// This is the one property of `lowering_predicate_leaf` that **no leak class
    /// can see**: the fold is last-write-wins, so a node re-recorded by the sweep
    /// is still perfectly *explained* — it has just silently swapped its real
    /// span and label for the sweep's coarse ones. Measured on the pipeline
    /// corpus, a blanket sweep clobbers 318 nodes and every gate stays green.
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
