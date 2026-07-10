//! Provenance substrate: stable IR-node identity plus a side table mapping each
//! node back to the source it came from.
//!
//! # Purpose
//!
//! Cambra lowers source through a chain of passes (lowering → uniquify →
//! infer → inline → lambda-elim → planning), and along the way the connection
//! between an IR node and the source the user wrote is steadily lost: spans are
//! dropped at the lowering boundary, monomorphization clones subtrees, lambda
//! elimination synthesizes point-free combinators, and planning fuses clauses.
//! This module is the foundation that keeps that connection: every IR
//! expression node gets a stable [`NodeId`], and a [`ProvenanceTable`] maps that
//! id to a [`Provenance`] record describing *where* it came from (source spans)
//! and *how* it came to be (a [`Derivation`]).
//!
//! # Dual use: inspector *and* compiler diagnostics
//!
//! The table is deliberately not inspector-specific. It is the single mechanism
//! behind two consumers:
//!
//! * **The program inspector** — `resolve`-ing a node id to its origin spans
//!   *is* the inspector's source-map projection (goto-definition, hover, "what
//!   produced this"), with no separate projection to maintain.
//! * **Compiler diagnostics** — passes downstream of lowering (infer,
//!   lambda-elim, planning, conversion) are location-poor today. An
//!   error-emission site captures a [`NodeId`]; rendering resolves it through
//!   *this same* table to a span. "Handle tracing" through the shared side
//!   table is the one diagnostic path, not a parallel ad-hoc one.
//!
//! Both call the same [`ProvenanceTable::resolve`]. That sharing is the point.
//!
//! # Scope of this module
//!
//! This is the standalone data-structure core: the id type, the provenance
//! model, the side table, and resolution. [`crate::ccl::expr::TypedExpr`]
//! carries a [`NodeId`], lowering and the later passes populate the table, and
//! the inverse span→node lookup is provided separately by
//! `inspector_model::SpanIndex` (an upstack commit introduces it).

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::chl_parser::ast::Span;

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
/// `NodeId` is embedded inline on `TypedExpr` (`crate::ccl::expr`), which
/// **excludes it from that type's `PartialEq`/`Hash`** (hand-written, not
/// derived). Provenance is metadata, not part of a node's value: two nodes
/// that are structurally equal as values must still compare equal even with
/// different `NodeId`s. The structural-equality memoization the passes rely on
/// (`uniquify`'s memo, `planning`'s predicate memo) depends on this — including
/// `node_id` would make every node look distinct and the memo tables would
/// never hit.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(u64);

static FRESH_NODE_ID: AtomicU64 = AtomicU64::new(1);

impl NodeId {
    /// Mint a globally-fresh node id. The only way to construct a `NodeId`.
    pub fn fresh() -> Self {
        NodeId(FRESH_NODE_ID.fetch_add(1, Ordering::Relaxed))
    }

    /// The id's underlying number, for use as an opaque serialization handle
    /// (the inspector wire shape carries a `NodeId` as a JSON number; see
    /// `crate::inspector_model`, an upstack commit). This is the *only* place the numeric value
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
// `u64` (the one place the numeric value is observed — see [`NodeId::as_u64`]),
// not as a struct. Hand-written rather than `#[serde(transparent)]` because the
// inner field is private.
#[cfg(feature = "serde")]
impl serde::Serialize for NodeId {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_u64(self.0)
    }
}

/// The compiler stage that produced a node — the WHO axis of provenance.
///
/// Minimal on purpose: only the stages that *mint or restructure* expression
/// nodes (and therefore need to record why a node exists) appear here.
///
/// `Pass` and [`crate::ccl::names::SyntheticKind`] (which tracks *binder*
/// provenance: `Pair`, `Mono`, `SolverArg`, …) are deliberately separate enums,
/// neither wrapping the other — one tags `NodeId`s (expression nodes), the
/// other tags `Uid`s (binders), and merging them would conflate the WHO axis
/// with binder-role payloads. See `design-provenance.md`'s "`Pass` and
/// `SyntheticKind` stay separate" section for the full rationale.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum Pass {
    /// Lowering CHL source into CCL.
    Lower,
    /// The 1:1 binder rename in [`crate::ccl::uniquify`].
    Uniquify,
    /// UDF inlining + beta-reduction ([`crate::ccl::inline`]): the pass that
    /// runs between the post-inference and post-desugar snapshots. Mostly
    /// id-preserving (a rebuilt node carries its input id); its genuine
    /// deviations are the fan-out at multi-use call sites (one occurrence
    /// preserved, the rest `Replicated`) and the wrappers/redexes it drops
    /// (`Discarded`).
    Inline,
    /// Defer desugaring ([`crate::ccl::desugar_defers`]): channelizing
    /// `Defer`/`Feed`/`Define` into collection unions and contribution records.
    /// Mostly a 1:1 transform (ids preserved), but its channelization machinery
    /// synthesizes new nodes (channel unions, contribution records, floated
    /// lambdas, DI wrappers) that are tagged `Synthetic`/`Derived { via: Desugar }`.
    Desugar,
    /// Monomorphization: cloning a generalized definition's subtree once per
    /// distinct resolved type (during inference).
    Mono,
    /// Lambda elimination: synthesizing point-free combinators (`Compose`,
    /// `Zip`, `Id`) from explicit lambdas.
    LambdaElim,
    /// Join/dataflow planning: hash-join and restrict scaffolding, clause
    /// fusion, refinement-predicate compilation.
    Planning,
}

/// How a node came to exist — the HOW axis of provenance, and the inspector's
/// "collapse vs. hide" toggle.
///
/// The `Derived` vs. `Synthetic` distinction is the one worth having from day
/// one: the synthesizing pass already knows which it is making, so it is free to
/// record at the call site, and it directly drives inspector presentation.
///
/// Role-rich variants (e.g. a `Fused { via, role }` for planning's hash-join
/// key/probe/predicate) can be added later **without migration**.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Derivation {
    /// Directly lowered, 1:1 with a source node. The inspector shows it as-is.
    Source,
    /// Synthesized but traceable: the node expands a user construct (a
    /// comparison chain, a comprehension, a lambda-elim combinator). Its
    /// origins point at that construct, and the inspector **collapses** it
    /// under that source construct.
    Derived {
        /// The pass that synthesized it.
        via: Pass,
    },
    /// Pure plumbing with no direct source counterpart (iteration markers,
    /// FanOut/Memo wrappers). Origins are the enclosing construct or empty, and
    /// the inspector **hides** it unless "show internals" is on.
    Synthetic {
        /// The pass that synthesized it.
        via: Pass,
    },
}

/// Where a node came from (`origins`) and how (`kind`).
///
/// # Full-capable, blame-populated
///
/// `origins` is a *set* of source spans, so one representation covers both
/// regimes with zero migration between them:
///
/// * one origin = **blame** (the common case: "this node traces to this span"),
/// * many origins = **full**/fusion (planning fuses {left, right, predicate}
///   into one node, so the node blames several source spans at once).
///
/// The MVP populates everything at blame level (singletons); planning's fusion
/// sites grow to multiple origins later without changing this type.
///
/// # Representation note
///
/// `origins` is a plain [`Vec<Span>`]. The overwhelmingly common case is a
/// single origin, so a `SmallVec<[Span; 1]>` (storing the lone span inline, no
/// heap allocation) is a worthwhile future optimization. It is deliberately not
/// taken here to avoid adding a `smallvec` dependency for the substrate's first
/// increment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Provenance {
    /// Source spans this node traces to. Length 1 = blame; length >1 = fusion.
    /// May be empty for [`Derivation::Synthetic`] plumbing with no source.
    pub origins: Vec<Span>,
    /// How the node came to exist.
    pub kind: Derivation,
}

// Wire shape (inspector, feature `serde`): the flat `{ "kind", "via", "origins" }`
// the `/api/snapshot` / `resolve` / `hover` schema specifies — `kind` is the
// [`Derivation`] discriminant as a bare string (`"Source"`/`"Derived"`/
// `"Synthetic"`), `via` is the synthesizing [`Pass`] (or `null` for `Source`),
// and `origins` is the span list. Hand-written so `via` flattens out of the
// `Derivation` enum to a sibling field with an explicit `null` (a derived
// tagged-enum would nest it and omit it for `Source`).
#[cfg(feature = "serde")]
impl serde::Serialize for Provenance {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let (kind, via): (&str, Option<Pass>) = match self.kind {
            Derivation::Source => ("Source", None),
            Derivation::Derived { via } => ("Derived", Some(via)),
            Derivation::Synthetic { via } => ("Synthetic", Some(via)),
        };
        let mut s = serializer.serialize_struct("Provenance", 3)?;
        s.serialize_field("kind", kind)?;
        s.serialize_field("via", &via)?;
        s.serialize_field("origins", &self.origins)?;
        s.end()
    }
}

impl Provenance {
    /// A node lowered directly 1:1 from a single source span.
    pub fn source(span: Span) -> Self {
        Provenance {
            origins: vec![span],
            kind: Derivation::Source,
        }
    }

    /// A node synthesized by `via` but traceable to `origins` (inspector
    /// collapses it under that source construct).
    pub fn derived(via: Pass, origins: impl IntoIterator<Item = Span>) -> Self {
        Provenance {
            origins: origins.into_iter().collect(),
            kind: Derivation::Derived { via },
        }
    }

    /// Pure plumbing introduced by `via`, with optional enclosing-construct
    /// origins (inspector hides it unless internals are shown).
    pub fn synthetic(via: Pass, origins: impl IntoIterator<Item = Span>) -> Self {
        Provenance {
            origins: origins.into_iter().collect(),
            kind: Derivation::Synthetic { via },
        }
    }
}

/// The side table: a [`NodeId`]-keyed map of [`Provenance`].
///
/// This is the layer-1 instance of a uniform pattern (stable ids + side table +
/// `resolve`) the substrate repeats per IR layer (`OperatorId → NodeId →
/// spans`); a later layer's table would have the same shape. The inspector and
/// compiler diagnostics share *this* table — both resolve through it.
///
/// # Graceful degradation
///
/// A missing entry resolves to `None` ("source unknown"), never a panic. A
/// node whose registration was forgotten is a quality bug (degraded provenance
/// for that node), not a correctness bug that crashes the compiler.
#[derive(Clone, Debug, Default)]
pub struct ProvenanceTable {
    entries: HashMap<NodeId, Provenance>,
}

impl ProvenanceTable {
    /// An empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register `prov` for `node`, returning any provenance previously recorded
    /// for that id (normally `None` — a fresh id is registered once).
    pub fn insert(&mut self, node: NodeId, prov: Provenance) -> Option<Provenance> {
        self.entries.insert(node, prov)
    }

    /// Resolve a node to its provenance, or `None` if unknown (see "graceful
    /// degradation" on the type). This is the shared entry point for the
    /// inspector and for diagnostic rendering.
    pub fn resolve(&self, node: NodeId) -> Option<&Provenance> {
        self.entries.get(&node)
    }

    /// The source spans a node traces to, or `None` if the node is unknown.
    /// Convenience over [`resolve`](Self::resolve) for the common "just give me
    /// the spans to point at" case; an empty slice is a *known* node with no
    /// source (synthetic plumbing), distinct from `None` (unknown node).
    pub fn origins(&self, node: NodeId) -> Option<&[Span]> {
        self.resolve(node).map(|p| p.origins.as_slice())
    }

    /// Number of registered nodes.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether any nodes are registered.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Iterate the registered [`Provenance`] records (test-only; the table is
    /// otherwise resolved by id, not enumerated). Used by monomorphization
    /// tests to assert that specialization clones were tagged
    /// `Derived { via: Mono }`.
    #[cfg(test)]
    pub(crate) fn iter_provenances(&self) -> impl Iterator<Item = &Provenance> {
        self.entries.values()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span(start: usize, end: usize) -> Span {
        Span::new(start, end)
    }

    #[test]
    fn fresh_node_ids_are_distinct() {
        let a = NodeId::fresh();
        let b = NodeId::fresh();
        let c = NodeId::fresh();
        assert_ne!(a, b);
        assert_ne!(b, c);
        assert_ne!(a, c);
        // A copy preserves identity (NodeId is Copy).
        assert_eq!(a, a);
        let a_copy = a;
        assert_eq!(a, a_copy);
    }

    #[test]
    fn resolve_returns_registered_source_entry() {
        let mut table = ProvenanceTable::new();
        let node = NodeId::fresh();
        table.insert(node, Provenance::source(span(3, 9)));

        let prov = table.resolve(node).expect("registered node resolves");
        assert_eq!(prov.kind, Derivation::Source);
        assert_eq!(prov.origins, vec![span(3, 9)]);
        // Blame level: exactly one origin.
        assert_eq!(prov.origins.len(), 1);
    }

    #[test]
    fn resolve_returns_registered_derived_entry() {
        let mut table = ProvenanceTable::new();
        let node = NodeId::fresh();
        table.insert(node, Provenance::derived(Pass::LambdaElim, [span(0, 12)]));

        let prov = table.resolve(node).expect("registered node resolves");
        assert_eq!(
            prov.kind,
            Derivation::Derived {
                via: Pass::LambdaElim
            }
        );
        assert_eq!(prov.origins, vec![span(0, 12)]);
    }

    #[test]
    fn resolve_returns_registered_synthetic_entry() {
        let mut table = ProvenanceTable::new();
        let node = NodeId::fresh();
        // Synthetic plumbing may carry no source origin at all.
        table.insert(node, Provenance::synthetic(Pass::Planning, []));

        let prov = table.resolve(node).expect("registered node resolves");
        assert_eq!(
            prov.kind,
            Derivation::Synthetic {
                via: Pass::Planning
            }
        );
        assert!(prov.origins.is_empty());
    }

    #[test]
    fn fusion_records_multiple_origins() {
        // Full-capable: a fused node blames several source spans at once.
        let mut table = ProvenanceTable::new();
        let node = NodeId::fresh();
        table.insert(
            node,
            Provenance::derived(Pass::Planning, [span(1, 4), span(8, 11), span(20, 25)]),
        );

        let origins = table.origins(node).expect("registered node has origins");
        assert_eq!(origins, &[span(1, 4), span(8, 11), span(20, 25)]);
    }

    #[test]
    fn unknown_node_resolves_to_none_not_panic() {
        let table = ProvenanceTable::new();
        let unknown = NodeId::fresh();
        assert!(table.resolve(unknown).is_none());
        assert!(table.origins(unknown).is_none());
    }

    #[test]
    fn distinguishes_unknown_node_from_origin_less_node() {
        let mut table = ProvenanceTable::new();
        let plumbing = NodeId::fresh();
        let unknown = NodeId::fresh();
        table.insert(plumbing, Provenance::synthetic(Pass::Planning, []));

        // Known-but-no-source: Some(empty slice).
        assert_eq!(table.origins(plumbing), Some(&[][..]));
        // Unknown: None ("source unknown").
        assert_eq!(table.origins(unknown), None);
    }

    #[test]
    fn insert_returns_previous_entry() {
        let mut table = ProvenanceTable::new();
        let node = NodeId::fresh();
        assert!(table.insert(node, Provenance::source(span(0, 1))).is_none());
        let prev = table
            .insert(node, Provenance::source(span(2, 3)))
            .expect("second insert returns the prior provenance");
        assert_eq!(prev.origins, vec![span(0, 1)]);
        assert_eq!(table.len(), 1);
    }

    #[test]
    fn empty_table_is_empty() {
        let mut table = ProvenanceTable::new();
        assert!(table.is_empty());
        assert_eq!(table.len(), 0);
        table.insert(NodeId::fresh(), Provenance::source(span(0, 1)));
        assert!(!table.is_empty());
        assert_eq!(table.len(), 1);
    }
}
