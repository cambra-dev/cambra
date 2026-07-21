//! Stable IR-node identity ([`NodeId`]) and the compiler-stage axis ([`Pass`]).
//!
//! # Purpose
//!
//! Cambra lowers source through a chain of passes (lowering → uniquify →
//! infer → inline → lambda-elim → planning). Every IR expression node carries a
//! stable [`NodeId`] so its identity survives across those passes, and each
//! rewrite records — through the lineage recorder in [`crate::ccl::lineage`] —
//! how the node it produced relates to the nodes it consumed. That lineage
//! folds, at each inspector pane boundary, into a
//! [`SourceProjection`](crate::ccl::lineage::SourceProjection) mapping a node
//! back to the source spans it traces to. This module owns only the two
//! identity primitives that lineage is parameterized over: the node id and the
//! pass tag.
//!
//! Node→source attribution lives in [`crate::ccl::lineage`], not here.

use std::sync::atomic::{AtomicU64, Ordering};

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
/// different `NodeId`s. The structural-equality memoization the passes rely on
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
    /// fresh one) keeps it from polluting an open lineage step: the recorder's
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
// `u64` (the one place the numeric value is observed — see [`NodeId::as_u64`]),
// not as a struct. Hand-written rather than `#[serde(transparent)]` because the
// inner field is private.
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
/// with binder-role payloads.
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
    /// deviations are the fan-out clones at multi-use call sites (`Copy`s) and
    /// the wrappers/redexes it drops (`Transform` discards).
    Inline,
    /// Defer desugaring ([`crate::ccl::channelize`]): channelizing
    /// `Defer`/`Feed`/`Define` into collection unions and contribution records.
    /// Mostly a 1:1 transform (ids preserved), but its channelization machinery
    /// synthesizes new nodes (channel unions, contribution records, floated
    /// lambdas, DI wrappers) that are tagged `{via: Desugar, nature: Machinery}`.
    Desugar,
    /// The transaction slice of the unified mutability phase
    /// ([`crate::ccl::transact_phase::run`]): stripping `with begin():` writer
    /// sites and assembling the `get_prev_txn`-guarded `LetRec` (histories,
    /// commit records, taps). Runs between the post-inference and post-desugar
    /// snapshots (after `Inline`, before `Desugar`).
    Transact,
    /// The induction slice of the unified mutability phase
    /// ([`crate::ccl::mut_elim::run`]): folding direct-mirror `For`/`MutWrite`
    /// loops into guarded `LetRec` induction histories. Runs between the
    /// post-inference and post-desugar snapshots (after `Transact`, before
    /// `Desugar`).
    Letrec,
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
