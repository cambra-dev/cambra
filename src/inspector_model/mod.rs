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
//! Each pane carries its own tree and its own
//! [`SourceProjection`](crate::ccl::provenance::SourceProjection), and one of
//! them is the **anchor**: the post-inference pane, fully typed but still
//! source-shaped (lambdas intact, before inline/lambda-elim/planning). A
//! binder's type is read from it, so the payload's scope-binding types are
//! post-inference types. See `src/inspector_model/design.md`, "The anchor pane".
//!
//! # The pane set is the compiler's, not this module's
//!
//! [`InspectedProgram::new`] derives one wire pane per entry of
//! [`PANES`](crate::ccl::panes::PANES) and one pane link per adjacent pair, so
//! the topology is declared in the compiler and read here. Adding a pane there
//! adds a pane here with no edit in this module.
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
//! Two source-side indices live here, both enumerated onto the wire rather than
//! queried:
//!
//! * [`SpanIndex`] — the `(span, node)` table over one pane's tree and its
//!   [`SourceProjection`](crate::ccl::provenance::SourceProjection), shipped as
//!   a pane's `spanIndex`.
//! * [`NameBinderIndex`] — source-level lexical name resolution, over the parsed
//!   CHL surface AST retained on
//!   [`source_ast`](crate::ccl::context::CompiledProgram::source_ast), shipped as
//!   the payload's `definitions` and the name half of its `scopes`. It resolves
//!   at the *source* level because lowering destroys the **name** of a
//!   multi-param `def`/`lambda` parameter: `uncurry_params` rewrites `Var(p)` to
//!   `__arg_tuple_N ▷ .i`, so nothing downstream binds or mentions `p`. The
//!   occurrence's span survives (substitution is root-carry), which is why a
//!   *use* of such a parameter still resolves to a node and a type; what only the
//!   surface AST can say is which binder that use refers to.
//!
//! # One payload, no point queries
//!
//! [`InspectedProgram`] bundles the two indices with the per-pane projections (source
//! text, one IR tree and one `SourceProjection` per pane, surface AST), and
//! [`InspectedProgram::build_payload`] assembles the payload from them. That is the
//! module's whole entry surface: a positional question is answered by the
//! consumer over the shipped `(span, node)` rows and the shipped node table,
//! which is the copy that runs. See `src/inspector_model/design.md`, "The usage model".

mod name_binder;
mod program;
mod span_index;
mod walk;
mod wire;

pub use name_binder::{Binding, Definition, NameBinderIndex, ScopeRegion};
pub use program::InspectedProgram;
pub use span_index::SpanIndex;
pub use wire::{
    DefinitionEntry, Diagnostic, DiagnosticLabel, InspectorPayload, IrChild, IrNode, Meta,
    PaneEntry, PaneLinkEntry, RewriteInfo, SCHEMA_VERSION, ScopeBindingEntry, ScopeEntry,
    SourceInfo, SpanEntry, dense_edges, diagnostics_from_compile_errors,
};
