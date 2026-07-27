//! The `/api/snapshot` bulk payload — the whole read-only model in one
//! struct, assembled by enumerating the snapshot's two indices.
//!
//! `/api/snapshot` is the primary read-only endpoint:
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
//! # Populated vs. stubbed
//!
//! * `source`, `stages` (each with its own IR tree + span index),
//!   `definitions`, `scopes`, `meta` — fully populated.
//! * `diagnostics` — **always empty `[]`** in this payload: a `/api/snapshot`
//!   describes a *successfully compiled* program, and there are no warnings. The
//!   wire type ([`Diagnostic`]) drives the standalone compile-failure path
//!   (`cambra-inspector::diagnose_json`); a failed compile instead flows
//!   through [`SnapshotPayload::degraded`], which carries the same
//!   diagnostics in place of a real snapshot (see `cambra-inspector::server`'s
//!   "Transport decision" note).
//! * `outline` — **omitted** from the payload. Rather than ship an empty stub
//!   of an undecided shape, the field is left out until an `outline` query
//!   exists.
//! * `meta.tick` — `null` (the live seam); `snapshotKind` is `"post-inference"`,
//!   `schema` is `4`.
//!
//! # Schema 4: the span index is no longer shipped
//!
//! Schema 4 drops the per-stage `spanIndex` array from the wire. It was pure
//! derived data: a pre-order walk of the stage's IR tree emitting one
//! `{span, nodeId}` per node origin span (see [`SpanIndex::build`](super::index::SpanIndex::build)),
//! and every wire node already carries its origin span inline (`InspectNode.span`).
//! Shipping it duplicated span bytes already on the tree and coupled the fixture
//! corpus to churn that carried no information the client could not rebuild. The
//! frontend now reconstructs the index on load from the stage tree
//! (`web/src/indices.ts`). The internal [`SpanIndex`](super::index::SpanIndex)
//! type and the server-side query path (`Snapshot::resolve` et al.) are
//! unchanged — only the wire stopped embedding its entries.

use crate::chl_parser::ast::Span;

use super::name_binder::{Definition, ScopeRegion};
use super::query::Snapshot;
use super::stage::dense_edges;
use crate::ccl::lineage::SourceProjection;
use crate::ccl::{Expr, Type};
use crate::pretty_tree::InspectNode;

/// The current `/api/snapshot` wire-format version, emitted as `meta.schema` on
/// both the success and degraded payloads. See [`Meta::schema`] for the
/// versioning contract and the current version's field set.
pub const SCHEMA_VERSION: u32 = 4;

/// The `GET /api/snapshot` bulk payload — the whole static read-only model.
///
/// Field order/names mirror the schema. `outline` is intentionally absent (see
/// the module note); `diagnostics` is always empty on the success path.
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
    /// own IR tree. The three stages
    /// `["pre-inference", "post-inference", "post-desugar"]`.
    ///
    /// On the live wire this is always the full pipeline. A fixture dump
    /// ([`prune_for_fixture`](Self::prune_for_fixture)) may retain a subset (in
    /// pipeline order) to slim the committed golden bytes.
    pub stages: Vec<StageEntry>,
    /// The dense node→node links between adjacent stages — each adjacent pane
    /// pair's `LineageMap` shipped verbatim, self-edges included. One entry per
    /// adjacent pair, in order: `{ from: "pre-inference", to: "post-inference" }`
    /// (the monomorphization boundary) and `{ from: "post-inference", to:
    /// "post-desugar" }` (the inline/desugar boundary).
    ///
    /// `Option` solely for the fixture-slimming path: `None` **omits** the field
    /// from the payload (see [`prune_for_fixture`](Self::prune_for_fixture)),
    /// which the fixture validator alone accepts. The **live wire always ships
    /// it** (`Some`) — the frontend's link graph consumes shipped edges — so a
    /// missing `paneLinks` on a live payload is a bug, never "no links".
    #[cfg_attr(feature = "serde", serde(skip_serializing_if = "Option::is_none"))]
    pub pane_links: Option<Vec<PaneLinkEntry>>,
}

/// One IR pipeline stage in the multi-pane snapshot.
///
/// Carries its own self-contained IR tree — each stage resolves against its own
/// (`Expr`, `SourceProjection`) pair. The span→node index is **not** shipped
/// (schema 4): every node carries its origin span inline on `ir`, and the
/// frontend rebuilds the index from the tree (see the module's schema-4 note).
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
}

/// The dense node→node links between two adjacent pipeline stages — the
/// pane-pair [`LineageMap`](crate::ccl::lineage::LineageMap) shipped verbatim.
///
/// **Dense**: an id preserved unchanged across the phase appears as its own
/// `[id, id]` self-edge, so the consumer follows edges only (no identity special
/// case). Genuine identity changes (monomorphization / inline fan-out) are the
/// `u != d` edges.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct PaneLinkEntry {
    /// The upstream stage id, e.g. `"pre-inference"`.
    pub from: &'static str,
    /// The downstream stage id, e.g. `"post-inference"`.
    pub to: &'static str,
    /// Every edge as `(upstream_node_id, downstream_node_id)`, self-edges
    /// included, sorted deterministically.
    pub edges: Vec<(u64, u64)>,
}

/// `{ name, text }` — the program identity + source.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct SourceInfo {
    /// A program name (a placeholder; the server can override it).
    pub name: String,
    /// The full source text.
    pub text: String,
}

/// One `{ useSpan, defSpan, name }` row of `definitions`. The schema's optional
/// `uid` is omitted — resolution is over the source AST, which keys on spans,
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
/// are source-AST spans (the `NameBinderIndex` is source-level), not IR
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
/// (no warnings); these are produced on the compile-failure path by the
/// standalone `diagnose_json` entry, not by `build_payload`.
///
/// [`CompileError`]: crate::ccl::context::CompileError
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct Diagnostic {
    /// Severity discriminant — `"error"` (no warnings).
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
    /// Live seam: the engine tick — **always `null`** here ("the program, no
    /// execution"). A live snapshot carries a real tick.
    pub tick: Option<u64>,
    /// The snapshot kind discriminant — `"post-inference"` for a successful
    /// compile, `"failed"` for a degraded (compile-error) payload.
    pub snapshot_kind: String,
    /// The wire-format version. A client reads this to detect an incompatible
    /// payload before parsing the rest.
    ///
    /// **Schema 4** is the field set of [`SnapshotPayload`] documented on that
    /// type (`source`, `definitions`, `scopes`, `diagnostics`, `meta`, `stages`,
    /// `paneLinks`), with the live seams (`meta.tick`, value summaries) always
    /// null. Each `stages[].ir` node carries its native attribution: the spans
    /// channel on the `span` field plus a `rewritten` tag
    /// (`null | { via, nature, label }`). `paneLinks` ships each adjacent pane
    /// pair's `LineageMap` **dense** (self-edges included), so the consumer
    /// follows edges only. There are three stages / two windows. Schema 4
    /// removed the per-stage `spanIndex` array (derivable from the stage tree —
    /// see the module's schema-4 note); schema 3 shipped it.
    ///
    /// **Bump the version** on any *breaking* wire change — a field removed,
    /// renamed, or retyped, or a value-shape change an old client would
    /// misread. Purely *additive* optional fields do **not** bump it (an old
    /// client ignores them). The frontend pins this in its wire-shape contract
    /// test, so a bump is a deliberate, reviewed event on both sides.
    pub schema: u32,
}

/// Build the full IR expand-tree for one pipeline stage.
///
/// Parameterized by `(Expr, SourceProjection)` so every stage goes through the
/// same shared source-linking tree-builder ([`build_inspect_tree`]). Schema 4
/// no longer ships a span→node index: every node carries its origin span inline
/// on the tree and the frontend rebuilds the index from it.
fn build_stage_ir(ir: &Expr, projection: &SourceProjection) -> InspectNode {
    use super::query::{build_inspect_tree, tree_height};

    // Expand the full IR tree (ship-everything: descend to max depth).
    build_inspect_tree(ir, projection, tree_height(ir))
}

impl Snapshot<'_> {
    /// Assemble the `/api/snapshot` bulk payload by enumerating the indices.
    ///
    /// `name` is the program name for `source.name` (a placeholder; the server
    /// picks it). Every other field is derived purely from the snapshot:
    ///
    /// * `stages` — the pipeline stages in upstream → downstream order:
    ///   `"pre-inference"`, `"post-inference"`, `"post-desugar"`, each with its
    ///   own IR tree.
    /// * `paneLinks` — per consecutive stage pair, the dense edges of the
    ///   pane-pair `LineageMap` folded at that boundary, self-edges included (see
    ///   [`dense_edges`](super::stage::dense_edges)).
    /// * `definitions` — [`NameBinderIndex::definitions`](crate::inspector_model::NameBinderIndex::definitions).
    /// * `scopes` — [`NameBinderIndex::scopes`](crate::inspector_model::NameBinderIndex::scopes),
    ///   each binding's `type` joined via [`Snapshot::type_of`] on its def-span.
    /// * `diagnostics` — empty.
    /// * `meta` — `tick: None`, `snapshotKind: "post-inference"`, `schema: 4`.
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
        // stage projections — each ships its own IR tree.
        let stages = self
            .stages()
            .iter()
            .map(|stage| StageEntry {
                id: stage.id,
                label: stage.label,
                kind: stage.kind,
                ir: build_stage_ir(stage.ir, &stage.projection),
            })
            .collect();

        // Dense edges between each consecutive stage pair, read off the pane-pair
        // `LineageMap` folded at that boundary (aligned with the same
        // `windows(2)`). `dense_edges` ships every edge — self-edges included —
        // already sorted for a byte-reproducible payload; the frontend follows
        // edges only, with no identity special case.
        let stage_maps = self.stage_maps();
        let pane_links = self
            .stages()
            .windows(2)
            .zip(stage_maps)
            .map(|(pair, map)| {
                let (upstream, downstream) = (&pair[0], &pair[1]);
                PaneLinkEntry {
                    from: upstream.id,
                    to: downstream.id,
                    edges: dense_edges(map),
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
            // The live wire always ships the links; fixture slimming may elide
            // them afterwards via `prune_for_fixture`.
            pane_links: Some(pane_links),
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
    /// IR. Today every degraded payload ships empty `stages`/`paneLinks`
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
            // Degraded ships an empty (but present) array — the frontend reads
            // it unconditionally; only fixture slimming ever omits the field.
            pane_links: Some(Vec::new()),
        }
    }
}

/// Fixture-only payload slimming: which panes a golden dump retains and whether
/// it ships `paneLinks`.
///
/// This exists **solely** for the `--dump-snapshot` fixture path (driven by
/// `cambra-inspector/scripts/fixtures.manifest`). The live server and the
/// default `--dump-snapshot` always emit the full wire ([`FixtureRetention::FULL`]).
/// Slimming trims what the byte-exact golden corpus pins on the big, volatile
/// programs (paneLinks are ~4 lines/edge with super-linear growth in the
/// collapsed desugar window; stages are the bulk of the bytes) without touching
/// the live contract — see [`SnapshotPayload::prune_for_fixture`].
#[derive(Clone, Debug)]
pub struct FixtureRetention {
    /// Stage ids to retain (in the payload's existing pipeline order), or `None`
    /// to keep every stage.
    pub panes: Option<Vec<String>>,
    /// Whether to ship `paneLinks`. `false` omits the field entirely (the
    /// fixture validator alone accepts an absent `paneLinks`).
    pub links: bool,
}

impl FixtureRetention {
    /// The full wire: every pane, links shipped. The live default.
    pub const FULL: FixtureRetention = FixtureRetention {
        panes: None,
        links: true,
    };

    /// Is this the full wire (no pruning)? A fast path so `prune_for_fixture`
    /// (and its callers) can skip work on the common live/default dump.
    pub fn is_full(&self) -> bool {
        self.panes.is_none() && self.links
    }
}

impl Default for FixtureRetention {
    fn default() -> Self {
        FixtureRetention::FULL
    }
}

impl SnapshotPayload {
    /// Slim a freshly-built payload for the committed golden corpus, per a
    /// [`FixtureRetention`] spec. **Fixture path only** — never applied to a
    /// live/served payload.
    ///
    /// * `panes = Some(keep)` retains only the listed stages (preserving the
    ///   payload's pipeline order) and drops any `paneLinks` window that
    ///   references a dropped pane (so the slimmed payload still validates).
    /// * `links = false` omits `paneLinks` entirely (the field, not an empty
    ///   array — an empty array would lie that the wire carries no edges).
    pub fn prune_for_fixture(&mut self, retention: &FixtureRetention) {
        if retention.is_full() {
            return;
        }
        if let Some(keep) = &retention.panes {
            self.stages.retain(|s| keep.iter().any(|k| k == s.id));
            if let Some(links) = &mut self.pane_links {
                links
                    .retain(|l| keep.iter().any(|k| k == l.from) && keep.iter().any(|k| k == l.to));
            }
        }
        if !retention.links {
            self.pane_links = None;
        }
    }
}
