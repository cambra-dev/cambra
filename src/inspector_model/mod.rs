//! The program inspector's read-only model over the retained IR panes.
//!
//! The reference for this layer — what the payload carries, when it is built,
//! and what the wire promises — is `src/inspector_model/design.md`, "The usage
//! model". What the payload deliberately cannot answer is
//! `src/inspector_model/design.md`, "What the model cannot say".
//!
//! This module lives in the `cambra` core crate (not a separate inspector
//! crate) because it is coupled to `ccl` internals — it walks the
//! [`Expr`](crate::ccl::Expr) snapshot and reads the per-pane
//! [`SourceProjection`](crate::ccl::provenance::SourceProjection)s materialized by
//! [`CompiledProgram::materialize_panes`](crate::ccl::context::CompiledProgram::materialize_panes).
//! The wire types here derive `Serialize`, and nothing else about
//! serialization lives here: the transport that turns the typed payload into
//! JSON is [`inspector_server`](crate::inspector_server).
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
//! them and a predicate reaches the wire as a child marked `predicate`, after
//! the node's value children. A predicate shared across type slots is one node
//! and one child. How a refinement ships is provisional; why the ids are in the
//! walk's domain at all is not — `src/inspector_model/design.md`, "Predicates
//! are nodes".
//!
//! # A node carries its own spans
//!
//! A pane ships one entry per node, and each entry carries every source span its
//! attribution records. There is no second span → node table: it held one row
//! per node per span, which is what the node entry already says. "Which node is
//! at this position" is a scan of the shipped nodes, and it is the consumer's —
//! see `src/inspector_model/design.md`, "A pane resolves against itself".
//!
//! # Names resolve over the IR
//!
//! The payload's `definitions` pairs each use with the source site of the binder
//! it names, read off the pre-inference pane. Uid equality is lexical resolution
//! after uniquification, and a binder carries the span of the name written at it,
//! so this is two reads rather than a scope walk — see
//! `src/inspector_model/design.md`, "Definitions resolve over the IR".
//!
//! # One payload, no point queries
//!
//! [`InspectedProgram`] bundles the per-pane projections (source text, one IR
//! tree and one `SourceProjection` per pane), and
//! [`InspectedProgram::build_payload`] assembles the payload from them. That
//! is the module's whole entry surface: a positional question is answered by the
//! consumer over the shipped node table, which is the copy that runs. See
//! `src/inspector_model/design.md`, "The usage model".

mod definitions;
mod frame;
mod program;
mod walk;
mod wire;

use crate::ccl::context::CompiledProgram;

pub use frame::render_frame;

/// Build the `/api/snapshot` payload for a compiled program and serialize it to
/// a JSON string.
///
/// This is the build-then-serialize entry the inspector server calls per
/// request. `name` becomes the payload's `source.name` (the program's display
/// name). Serialization is infallible for this payload (it is plain data — no
/// maps with non-string keys, no custom errors), so a failure is a bug; we
/// surface it via `expect` rather than leaking a `serde_json::Error` into the
/// signature the server wants.
pub fn snapshot_json(compiled: &CompiledProgram, name: &str, generation: u64) -> String {
    let inspected = InspectedProgram::new(compiled);
    let payload = inspected.build_payload(name, generation);
    serde_json::to_string(&payload).expect("snapshot payload serializes")
}

/// Pretty-printed [`snapshot_json`] — the byte format of the committed golden
/// fixtures (`web/src/__fixtures__/`).
///
/// The binary owns these bytes deliberately: the fixtures are byte-compared by
/// `ci.sh`'s `ci_fixtures` gate, so their formatter must be pinned by
/// Cargo.lock, not an external tool. Piping through `python3 -m json.tool` made
/// the corpus a function of the local Python version, and of `FORCE_COLOR` —
/// either silently rewrites every fixture and the gate reads it as drift.
pub fn snapshot_json_pretty(compiled: &CompiledProgram, name: &str, generation: u64) -> String {
    let inspected = InspectedProgram::new(compiled);
    let payload = inspected.build_payload(name, generation);
    serde_json::to_string_pretty(&payload).expect("snapshot payload serializes")
}

pub use program::InspectedProgram;
pub use wire::{
    DefinitionEntry, Diagnostic, InspectorPayload, IrChild, IrNode, Meta, PaneEntry, PaneLinkEntry,
    RewriteInfo, SCHEMA_VERSION, SourceInfo, diagnostics_from_compile_errors,
};
