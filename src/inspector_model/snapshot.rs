//! The `/api/snapshot` bulk payload — the whole read-only M1 model in one
//! struct, assembled by enumerating the snapshot's two indices.
//!
//! [`m1-static-plan`] §2 defines `GET /api/snapshot` as the primary endpoint:
//! source + the pipeline stages (each an IR tree + span→node index) + use→def
//! definitions + per-scope bindings + diagnostics + meta. This module mirrors
//! that JSON exactly as a serde-gated [`SnapshotPayload`]; the actual
//! serialization (and `serde_json`) lives in the `cambra-inspector` crate.
//! Building the payload is pure: it enumerates
//! [`SpanIndex`](crate::inspector_model::SpanIndex) and
//! [`NameBinderIndex`](crate::inspector_model::NameBinderIndex) (the enumeration
//! methods added alongside their point queries) and builds each stage's IR tree
//! via the shared `build_inspect_tree`.
//!
//! # Wire-type isolation
//!
//! Every type here carries `#[cfg_attr(feature = "serde", derive(Serialize))]`
//! with camelCase field names (`spanIndex`, `useSpan`, `defSpan`,
//! `snapshotKind`, …) to match the schema. `cambra` itself never compiles serde
//! unless the feature is on — see the module-level note on
//! [`inspector_model`](crate::inspector_model).
//!
//! # Populated vs. stubbed (M1)
//!
//! * `source`, `stages` (each with its own IR tree + span index),
//!   `definitions`, `scopes`, `meta` — fully populated.
//! * `diagnostics` — **always empty `[]`** in this payload: a `/api/snapshot`
//!   describes a *successfully compiled* program, and M1 has no warnings. The
//!   wire type ([`Diagnostic`]) drives the standalone compile-failure path
//!   (`cambra-inspector::diagnose_json`); a failed compile instead flows
//!   through [`SnapshotPayload::degraded`], which carries the same
//!   diagnostics in place of a real snapshot (see `cambra-inspector::server`'s
//!   "Transport decision" note).
//! * `outline` — **omitted** from the payload. Rather than ship an empty stub
//!   of an undecided shape, the field is left out until an `outline` query
//!   exists.
//! * `meta.tick` — `null` (the live seam); `snapshotKind` is `"post-inference"`,
//!   `schema` is `2`.

use crate::chl_parser::ast::Span;

use super::StageAdjacency;
use super::name_binder::{Definition, ScopeRegion};
use super::query::Snapshot;
use crate::ccl::provenance::ProvenanceTable;
use crate::ccl::{Expr, Type};
use crate::pretty_tree::InspectNode;

/// The current `/api/snapshot` wire-format version, emitted as `meta.schema` on
/// both the success and degraded payloads. See [`Meta::schema`] for the
/// versioning contract and the current version's field set.
pub const SCHEMA_VERSION: u32 = 2;

/// The `GET /api/snapshot` bulk payload — the whole static M1 model.
///
/// Field order/names mirror the schema. `outline` is intentionally absent (see
/// the module note); `diagnostics` is always empty in M1.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct SnapshotPayload {
    /// The program's name + full source text.
    pub source: SourceInfo,
    /// Every resolved use→definition pair.
    pub definitions: Vec<DefinitionEntry>,
    /// Per-scope visible-binding lists.
    pub scopes: Vec<ScopeEntry>,
    /// Always empty on the success path (see the module doc's "Populated vs.
    /// stubbed" section) — a failed compile carries real diagnostics through
    /// [`SnapshotPayload::degraded`] instead.
    pub diagnostics: Vec<Diagnostic>,
    /// Snapshot metadata + the live-protocol seams.
    pub meta: Meta,
    /// The ordered pipeline stages (upstream → downstream), each carrying its
    /// own IR tree + span index. The three stages
    /// `["pre-inference", "post-inference", "post-desugar"]`.
    pub stages: Vec<StageEntry>,
    /// The non-identity node→node links between adjacent stages. One entry per
    /// adjacent pair, in order: `{ from: "pre-inference", to: "post-inference" }`
    /// (the monomorphization fan-out) and `{ from: "post-inference", to:
    /// "post-desugar" }` (the inline fan-out).
    pub stage_links: Vec<StageLinkEntry>,
}

/// One IR pipeline stage in the multi-pane snapshot.
///
/// Carries its own self-contained IR tree and span index — each stage resolves
/// against its own (Expr, ProvenanceTable) pair.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct StageEntry {
    /// Stable machine id, e.g. `"pre-inference"`, `"post-inference"`,
    /// `"post-desugar"`.
    pub id: &'static str,
    /// Human-readable label for the pane header.
    pub label: &'static str,
    /// Discriminant for the stage kind: `"holes"` for the still-hole-typed
    /// pre-inference tree, `"typed"` for a fully-typed tree (post-inference and
    /// post-desugar both).
    pub kind: &'static str,
    /// The full IR expand-tree for this stage.
    pub ir: InspectNode,
    /// Every `(span → nodeId)` entry of this stage's span index.
    pub span_index: Vec<SpanEntry>,
}

/// The non-identity node→node links between two adjacent pipeline stages.
///
/// Identity edges (same [`NodeId`] in both trees) are not stored here — the
/// consumer resolves them as "highlight the same id in each pane". Only the
/// non-identity edges (e.g. monomorphization fan-out) are recorded.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct StageLinkEntry {
    /// The upstream stage id, e.g. `"pre-inference"`.
    pub from: &'static str,
    /// The downstream stage id, e.g. `"post-inference"`.
    pub to: &'static str,
    /// Every non-identity edge as `(upstream_node_id, downstream_node_id)`.
    pub edges: Vec<(u64, u64)>,
}

/// `{ name, text }` — the program identity + source.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct SourceInfo {
    /// A program name (a placeholder in M1; the server can override it).
    pub name: String,
    /// The full source text.
    pub text: String,
}

/// One `{ span, nodeId }` row of `spanIndex`.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct SpanEntry {
    /// The origin span.
    pub span: Span,
    /// The node indexed under it.
    pub node_id: crate::ccl::provenance::NodeId,
}

/// One `{ useSpan, defSpan, name }` row of `definitions`. The schema's optional
/// `uid` is omitted — M1 resolves over the source AST (D5), which keys on spans,
/// not uniquify uids.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct DefinitionEntry {
    /// The use-site span.
    pub use_span: Span,
    /// The binder's source span.
    pub def_span: Span,
    /// The bound name.
    pub name: String,
}

/// One `{ span, bindings }` row of `scopes`. `nodeId` is omitted: scope regions
/// are source-AST spans (the `NameBinderIndex` is source-level, D5), not IR
/// nodes, so there is no single node id to attach.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct ScopeEntry {
    /// The region's source span.
    pub span: Span,
    /// The binders visible in the region, each joined with its type.
    pub bindings: Vec<ScopeBindingEntry>,
}

/// One `{ name, defSpan, type }` binding inside a [`ScopeEntry`].
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct ScopeBindingEntry {
    /// The bound name.
    pub name: String,
    /// The binder's source span.
    pub def_span: Span,
    /// The binder's type, joined through the `SpanIndex`. `None` (serializes as
    /// `null`) when the def-span maps to no typed node — e.g. a substituted
    /// multi-param parameter (the deferred substituted-parameter fix).
    #[cfg_attr(feature = "serde", serde(rename = "type"))]
    pub ty: Option<Type>,
}

/// A diagnostic entry.
///
/// The web half of the dual-use diagnostics: a [`CompileError`] rendered as
/// structured JSON, the same error the terminal renders via ariadne. Built by
/// [`Diagnostic::from_compile_error`] / [`diagnostics_from_compile_errors`].
///
/// `diagnostics` on [`SnapshotPayload`] stays `[]` for *successful* compiles
/// (no warnings in M1); these are produced on the compile-failure path by the
/// standalone `diagnose_json` entry, not by `build_payload`.
///
/// [`CompileError`]: crate::ccl::context::CompileError
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct Diagnostic {
    /// Severity discriminant — `"error"` (M1 has no warnings).
    pub severity: String,
    /// The compile stage that produced it — `"parse"`, `"lower"`, `"infer"`, …
    /// (the `CompileError` variant's stage).
    pub stage: String,
    /// The human-readable message (reuses the variant's rendered text).
    pub message: String,
    /// The primary source span, when one is known.
    pub span: Option<Span>,
    /// Labelled spans (one per pointed-at range). Empty when no span is known.
    pub labels: Vec<DiagnosticLabel>,
}

/// A `{ span, message }` label inside a [`Diagnostic`].
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct DiagnosticLabel {
    /// The source range this label points at.
    pub span: Span,
    /// The label text.
    pub message: String,
}

impl Diagnostic {
    /// Build a [`Diagnostic`] from a single [`CompileError`].
    ///
    /// Maps the variant to its stage string and reuses the variant's existing
    /// rendered message. The infer path carries the span resolved at the
    /// `compile_program` boundary (the dual-use payload); other variants
    /// extract their span where it is cheaply reachable and otherwise degrade
    /// to `span: None` — still a valid, renderable diagnostic.
    ///
    /// [`CompileError`]: crate::ccl::context::CompileError
    pub fn from_compile_error(error: &crate::ccl::context::CompileError) -> Self {
        use crate::ccl::context::CompileError;
        let (stage, message, span) = match error {
            CompileError::Parse(e) => ("parse", format!("{e:?}"), None),
            CompileError::Lower(e) => ("lower", format!("{e:?}"), Some(e.span())),
            CompileError::DesugarDefers(e) => ("desugarDefers", format!("{e:?}"), None),
            CompileError::Infer { error, span } => ("infer", format!("{error:?}"), *span),
            CompileError::LambdaElim(e) => ("lambdaElim", format!("{e:?}"), None),
            CompileError::Conversion(e) => ("conversion", format!("{e:?}"), None),
            CompileError::Unsupported(msg) => ("unsupported", msg.clone(), None),
        };
        let labels = span
            .map(|span| {
                vec![DiagnosticLabel {
                    span,
                    message: message.clone(),
                }]
            })
            .unwrap_or_default();
        Diagnostic {
            severity: "error".to_string(),
            stage: stage.to_string(),
            message,
            span,
            labels,
        }
    }
}

/// Convert a slice of [`CompileError`](crate::ccl::context::CompileError)s into
/// wire [`Diagnostic`]s — the dual-use JSON consumer of the same errors the
/// terminal renders.
pub fn diagnostics_from_compile_errors(
    errors: &[crate::ccl::context::CompileError],
) -> Vec<Diagnostic> {
    errors.iter().map(Diagnostic::from_compile_error).collect()
}

/// `meta` — snapshot metadata + the forward-compat live seams.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct Meta {
    /// Live seam: the engine tick — **always `null`** in M1 ("the program, no
    /// execution"). A live snapshot carries a real tick.
    pub tick: Option<u64>,
    /// The snapshot kind discriminant — `"post-inference"` for a successful
    /// compile, `"failed"` for a degraded (compile-error) payload.
    pub snapshot_kind: String,
    /// The wire-format version. A client reads this to detect an incompatible
    /// payload before parsing the rest.
    ///
    /// **Schema 2** is the field set of [`SnapshotPayload`] documented on that
    /// type (`source`, `definitions`, `scopes`, `diagnostics`, `meta`, `stages`,
    /// `stageLinks`), with the per-field shapes here and the live seams
    /// (`meta.tick`, value summaries) always null. Its **delta from schema 1**:
    /// the legacy top-level `ir`/`spanIndex` fields (byte-for-byte duplicates of
    /// the post-inference stage) are **removed** — a client reads the stages;
    /// and the `StageEntry.kind` vocabulary was renamed
    /// `"pre-inference"/"post-inference"` → `"holes"/"typed"` (so it no longer
    /// collides with stage *ids* and the post-desugar stage is honestly
    /// `"typed"`). The `stages`/`stageLinks` shapes are as emitted today (three
    /// stages, two windows).
    ///
    /// **Bump the version** on any *breaking* wire change — a field removed,
    /// renamed, or retyped, or a value-shape change a schema-1 client would
    /// misread. Purely *additive* optional fields do **not** bump it (an old
    /// client ignores them). The frontend pins this in its wire-shape contract
    /// test, so a bump is a deliberate, reviewed event on both sides.
    pub schema: u32,
}

/// Build the IR expand-tree and span-index entries for one pipeline stage.
///
/// Parameterized by `(ir, provenance)` so every stage goes through the same
/// shared path: the tree via [`build_inspect_tree`] (the single source-linking
/// tree-builder) and the index via [`SpanIndex::build`].
fn build_stage_ir_and_index(
    ir: &Expr,
    provenance: &ProvenanceTable,
) -> (InspectNode, Vec<SpanEntry>) {
    use super::index::SpanIndex;
    use super::query::{build_inspect_tree, tree_height};

    let span_entries = SpanIndex::build(ir, provenance)
        .entries()
        .map(|(span, node_id)| SpanEntry { span, node_id })
        .collect();

    // Expand the full IR tree (M1 ship-everything: descend to max depth).
    let ir_node = build_inspect_tree(ir, provenance, tree_height(ir));

    (ir_node, span_entries)
}

impl Snapshot<'_> {
    /// Assemble the `/api/snapshot` bulk payload by enumerating the indices.
    ///
    /// `name` is the program name for `source.name` (a placeholder; the server
    /// picks it). Every other field is derived purely from the snapshot:
    ///
    /// * `stages` — the pipeline stages in upstream → downstream order:
    ///   `"pre-inference"`, `"post-inference"`, `"post-desugar"`, each with its
    ///   own IR tree + span index.
    /// * `stageLinks` — per consecutive stage pair, the non-identity edges
    ///   produced by [`StageAdjacency::from_remap`] over the remaps of the
    ///   passes that run between the pair's snapshots (the pair→pass
    ///   association in `Snapshot::remap_between`).
    /// * `definitions` — [`NameBinderIndex::definitions`](crate::inspector_model::NameBinderIndex::definitions).
    /// * `scopes` — [`NameBinderIndex::scopes`](crate::inspector_model::NameBinderIndex::scopes),
    ///   each binding's `type` joined via [`Snapshot::type_of`] on its def-span.
    /// * `diagnostics` — empty.
    /// * `meta` — `tick: None`, `snapshotKind: "post-inference"`, `schema: 2`.
    pub fn build_payload(&self, name: impl Into<String>) -> SnapshotPayload {
        let source = SourceInfo {
            name: name.into(),
            text: self.source_text().to_string(),
        };

        let definitions = self
            .name_binder_ref()
            .definitions()
            .into_iter()
            .map(
                |Definition {
                     use_span,
                     def_span,
                     name,
                 }| DefinitionEntry {
                    use_span,
                    def_span,
                    name: name.to_string(),
                },
            )
            .collect();

        let scopes = self
            .name_binder_ref()
            .scopes()
            .into_iter()
            .map(|ScopeRegion { span, bindings }| ScopeEntry {
                span,
                bindings: bindings
                    .into_iter()
                    .map(|b| ScopeBindingEntry {
                        // Join the binder's type by resolving its def-span
                        // through the SpanIndex (None for a substituted param).
                        ty: self.type_of(b.def_span),
                        name: b.name.to_string(),
                        def_span: b.def_span,
                    })
                    .collect(),
            })
            .collect();

        // Build the pipeline stages (upstream → downstream) from the bundled
        // stage projections — each ships its own IR tree + span index.
        let stages = self
            .stages()
            .iter()
            .map(|stage| {
                let (ir, span_index) = build_stage_ir_and_index(stage.ir, stage.provenance);
                StageEntry {
                    id: stage.id,
                    label: stage.label,
                    kind: stage.kind,
                    ir,
                    span_index,
                }
            })
            .collect();

        // Non-identity edges between each consecutive stage pair, bridged by
        // the retained remaps of the passes that run between the pair's two
        // snapshots — associated by the pair's stage *ids*, never by window
        // position, so the association cannot silently rot when stages are
        // added or reordered (see `stage::remap_between_stages`). Identity
        // edges are resolved by the consumer. Sorted so the payload is
        // byte-reproducible run-to-run (the adjacency is built over HashMaps,
        // whose iteration order is nondeterministic) — which keeps the committed
        // golden fixtures from churning on regen.
        let stage_links = self
            .stages()
            .windows(2)
            .map(|pair| {
                let (upstream, downstream) = (&pair[0], &pair[1]);
                let remap = self.remap_between(upstream.id, downstream.id);
                let mut edges: Vec<(u64, u64)> =
                    StageAdjacency::from_remap(upstream.ir, downstream.ir, &remap)
                        .edges()
                        .collect();
                edges.sort_unstable();
                StageLinkEntry {
                    from: upstream.id,
                    to: downstream.id,
                    edges,
                }
            })
            .collect();

        SnapshotPayload {
            source,
            definitions,
            scopes,
            diagnostics: Vec::new(),
            meta: Meta {
                tick: None,
                snapshot_kind: "post-inference".to_string(),
                schema: SCHEMA_VERSION,
            },
            stages,
            stage_links,
        }
    }
}

impl SnapshotPayload {
    /// The degraded `/api/snapshot` payload for a program that failed to
    /// compile: the source text + the structured diagnostics, with no typed IR.
    ///
    /// Built from the **same** [`SnapshotPayload`] type as the success path
    /// (rather than a separately hand-rolled JSON object), so the two shapes
    /// cannot silently diverge as the schema evolves — the `stages`/scope
    /// collections are empty and `meta.snapshotKind` is `"failed"`. The frontend
    /// still renders the editor + squiggles from this.
    ///
    /// TODO(degraded-stages): emit whatever pipeline stages *did* complete — if
    /// desugaring succeeds and only inference fails, we can still ship the
    /// post-desugar `stages[]` entry so the inspector visualizes the desugared
    /// IR. Today every degraded payload ships empty `stages`/`stageLinks`
    /// regardless of where the failure occurred.
    pub fn degraded(
        name: impl Into<String>,
        text: impl Into<String>,
        diagnostics: Vec<Diagnostic>,
    ) -> SnapshotPayload {
        SnapshotPayload {
            source: SourceInfo {
                name: name.into(),
                text: text.into(),
            },
            definitions: Vec::new(),
            scopes: Vec::new(),
            diagnostics,
            meta: Meta {
                tick: None,
                snapshot_kind: "failed".to_string(),
                schema: SCHEMA_VERSION,
            },
            stages: Vec::new(),
            stage_links: Vec::new(),
        }
    }
}
