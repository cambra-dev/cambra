//! The program inspector's read-only model over the retained IR panes.
//!
//! `src/inspector_model/design.md` is the reference for this layer: what the
//! payload carries, when it is built, and what the wire promises. See "The usage
//! model" there before adding an entry point, and "Decided, not yet built" for
//! the changes this module is ratified to make and has not made.
//!
//! This module lives in the `cambra` core crate (not a separate inspector
//! crate) because it is coupled to `ccl` internals — it walks the
//! [`Expr`](crate::ccl::Expr) snapshot and reads the per-pane
//! [`SourceProjection`](crate::ccl::provenance::SourceProjection)s materialized by
//! [`CompiledProgram::materialize_panes`](crate::ccl::context::CompiledProgram::materialize_panes).
//! The wire types here derive `Serialize` under the optional, default-off
//! `serde` feature, and nothing else about serialization lives here: no
//! `serde_json`, no transport. A plain `ccl`/interpreter build
//! (`cargo build -p cambra`) compiles none of it.
//!
//! # The anchor pane
//!
//! Each stage carries its own tree and its own
//! [`SourceProjection`](crate::ccl::provenance::SourceProjection), and one of
//! them is the **anchor**: the post-inference pane, fully typed but still
//! source-shaped (lambdas intact, before inline/lambda-elim/planning). A
//! binder's type is read from it, so the payload's scope-binding types are
//! post-inference types. See `src/inspector_model/design.md`, "The anchor pane".
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
//! [`NodeId`](crate::ccl::provenance::NodeId)s, so every walk here descends into
//! them and a predicate reaches the wire as a child edge labelled `where.N`
//! rather than a positional index. Why the ids are in the walk's domain at all:
//! `src/inspector_model/design.md`, "Predicates are nodes".
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
//!   [`source_ast`](crate::ccl::context::CompiledProgram::source_ast). It resolves
//!   at the *source* level because lowering destroys the **name** of a
//!   multi-param `def`/`lambda` parameter: `uncurry_params` rewrites `Var(p)` to
//!   `__arg_tuple_N ▷ .i`, so nothing downstream binds or mentions `p`. The
//!   occurrence's span survives (substitution is root-carry), which is why a
//!   *use* of such a parameter still resolves to a node and a type; what only the
//!   surface AST can say is which binder that use refers to.
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
//! No consumer calls them, and they are removed by item 1 of
//! `src/inspector_model/design.md`, "Decided, not yet built" — a positional
//! question is the consumer's to answer over the shipped tables.

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
