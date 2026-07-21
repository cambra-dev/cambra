//! The program inspector's read-only model over the post-inference IR snapshot.
//!
//! This module lives in the `cambra` core crate (not a separate inspector
//! crate) because it is coupled to `ccl` internals — it walks the
//! [`Expr`](crate::ccl::Expr) snapshot and reads the per-pane
//! [`SourceProjection`](crate::ccl::provenance::SourceProjection)s materialized by
//! [`CompiledProgram::materialize_panes`](crate::ccl::context::CompiledProgram::materialize_panes).
//! It is deliberately **serde-free**: serialization lives in the
//! `cambra-inspector` workspace crate behind the optional, default-off `serde`
//! feature on `cambra`, so plain `ccl`/interpreter builds
//! (`cargo build -p cambra`) never compile it.
//!
//! # The anchor (post-inference snapshot)
//!
//! Every index here is built over the **post-inference** IR retained on
//! [`CompiledProgram::post_inference_ir`](crate::ccl::context::CompiledProgram::post_inference_ir):
//! fully typed, but still source-shaped (lambdas intact, before
//! inline/lambda-elim/planning). That snapshot's node ids resolve against the
//! materialized post-inference pane
//! [`SourceProjection`](crate::ccl::provenance::SourceProjection).
//!
//! # The pane set is the compiler's, not this module's
//!
//! [`Snapshot::new`] derives one wire stage per entry of
//! [`PANES`](crate::ccl::panes::PANES) and one pane link per adjacent pair, so
//! the topology is declared in the compiler and read here. Adding a pane there
//! adds a stage here with no edit in this module.
//!
//! # Predicates are nodes
//!
//! A refinement predicate riding a type slot is an expression tree with its own
//! [`NodeId`](crate::ccl::provenance::NodeId)s, and the pane fold explains those
//! ids — `collect_tree_ids` enumerates them, so they appear in the pane
//! projections and as endpoints of the pane-pair maps. Every walk here descends
//! into them for that reason: a tree that stopped at the main expression tree
//! would ship links pointing at nodes it had omitted. A predicate reaches the
//! wire as a child edge labelled `where.N` rather than a positional index, which
//! is how a consumer tells "inside a type" from "an operand".
//!
//! # Scope
//!
//! Two source-side indices live here:
//!
//! * [`SpanIndex`] — span → typed-IR-node containment, over
//!   [`post_inference_ir`](crate::ccl::context::CompiledProgram::post_inference_ir)
//!   + the pane [`SourceProjection`](crate::ccl::provenance::SourceProjection).
//! * [`NameBinderIndex`] — source-level lexical name resolution
//!   (`goto-definition`, the binder half of `scope-at`), over the parsed CHL
//!   surface AST retained on
//!   [`source_ast`](crate::ccl::context::CompiledProgram::source_ast). This is
//!   done at the *source* level, not over the lowered tree: some
//!   source variables (multi-param `def`/`lambda` parameters) are destroyed by
//!   lowering before any IR node exists, so only the surface AST can resolve
//!   them.
//!
//! # Query handlers
//!
//! [`Snapshot`] bundles the two indices + the snapshot projections
//! (source text, IR, per-pane [`SourceProjection`](crate::ccl::provenance::SourceProjection), surface AST) and exposes the
//! transport-agnostic query handlers as methods: [`Snapshot::resolve`],
//! [`Snapshot::hover`]/[`Snapshot::type_of`], [`Snapshot::goto_definition`],
//! [`Snapshot::scope_at`], [`Snapshot::expand`]. These are pure reads — no
//! serde, no I/O (serialization lives in the `cambra-inspector` crate, per the
//! module doc above). Every value-ish result carries the
//! always-`None` live seams (`tick`, `value_summary`).
//!
//! The substituted-parameter span fix (so `hover`/`type_of` on a *use* of a
//! multi-param `def`/`lambda` parameter resolves to a type rather than `None`)
//! is still a follow-up — see [`Snapshot::type_of`].

mod index;
mod name_binder;
mod query;
mod snapshot;
mod stage;

pub use index::SpanIndex;
pub use name_binder::{Binding, Definition, NameBinderIndex, ScopeRegion};
pub use query::{
    GotoDefinition, Hover, Resolve, ScopeAt, ScopeBinding, Snapshot, Tick, ValueSummary,
};
pub use snapshot::{
    DefinitionEntry, Diagnostic, DiagnosticLabel, Meta, PaneLinkEntry, SCHEMA_VERSION,
    ScopeBindingEntry, ScopeEntry, SnapshotPayload, SourceInfo, SpanEntry, StageEntry,
    diagnostics_from_compile_errors,
};
pub use stage::dense_edges;
