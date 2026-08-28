//! The `/api/snapshot` bulk payload — the whole read-only model in one
//! struct, assembled by enumerating the model's two indices.
//!
//! `/api/snapshot` is the primary read-only endpoint:
//! source + the panes (each a node table + span→node index) + use→def
//! definitions + per-scope bindings + diagnostics + meta. This module mirrors
//! that JSON exactly as a serde-gated [`InspectorPayload`]; the actual
//! serialization (and `serde_json`) lives in the `cambra-inspector` crate.
//! Building the payload is pure: it enumerates
//! [`SpanIndex`](crate::inspector_model::SpanIndex) and
//! [`NameBinderIndex`](crate::inspector_model::NameBinderIndex) and builds each
//! pane's node table via [`build_node_table`], over the IR walk `walk.rs` owns.
//!
//! # Pane links
//!
//! The multi-pane inspector shows several panes side by side (CHL
//! source, pre-inference IR, post-inference IR, post-channelize IR, …) and links a
//! node in one pane to the node(s) it came from / became in the adjacent panes.
//! That link is the node's provenance across the phase.
//!
//! The link is a [`ProvenanceMap<NodeId, NodeId>`] folded at the pane boundary by
//! [`collapse`](crate::ccl::provenance::collapse) — one per adjacent pane pair,
//! materialized on [`CompiledProgram`](crate::ccl::context::CompiledProgram) via
//! `materialize_panes`. The wire ships it verbatim, so a surviving node's
//! cross-pane link is a `[id, id]` self-edge and a genuine identity change
//! (monomorphization or inline fan-out, channelize's cluster and fan-in copies)
//! is a `u != d` edge. What the density and the labels promise a consumer:
//! `src/inspector_model/design.md`, "Pane links are dense and labelled".
//!
//! # Wire-type isolation
//!
//! Every type here carries `#[cfg_attr(feature = "serde", derive(Serialize))]`
//! with camelCase field names (`spanIndex`, `useSpan`, `defSpan`,
//! `payloadKind`, …) to match the schema. `cambra` itself never compiles serde
//! unless the feature is on — see the module-level note on
//! [`inspector_model`](crate::inspector_model).
//!
//! # Populated vs. stubbed
//!
//! * `source`, `panes` (each with its own node table + span index),
//!   `definitions`, `scopes`, `meta` — fully populated.
//! * `diagnostics` — **always empty `[]`** in this payload: a `/api/snapshot`
//!   describes a *successfully compiled* program, and there are no warnings. The
//!   wire type ([`Diagnostic`]) drives the standalone compile-failure path
//!   (`cambra-inspector::diagnose_json`); a failed compile instead flows
//!   through [`InspectorPayload::degraded`], which carries the same
//!   diagnostics in place of a real snapshot (see `cambra-inspector::server`'s
//!   "Transport decision" note).
//! * `outline` — **omitted** from the payload. Rather than ship an empty stub
//!   of an undecided shape, the field is left out until an `outline` query
//!   exists.
//! * `meta.tick` — `null` (the live seam); `payloadKind` is `"post-inference"`,
//!   `schema` is [`SCHEMA_VERSION`].

use crate::ccl::provenance::{EdgeLabels, NodeId, ProvenanceMap, SourceProjection};
use crate::ccl::{Expr, FunKind, HistoryKind, Type};
use crate::chl_parser::ast::Span;

use super::name_binder::{Definition, ScopeRegion};
use super::program::{InspectedProgram, PaneProjection};
use super::walk::{node_label, predicate_children};

/// The current `/api/snapshot` wire-format version, emitted as `meta.schema` on
/// both the success and degraded payloads. See [`Meta::schema`] for the
/// versioning contract and the current version's field set.
pub const SCHEMA_VERSION: u32 = 5;

/// The `GET /api/snapshot` bulk payload — the whole static read-only model.
///
/// Field order/names mirror the schema. `outline` is intentionally absent (see
/// the module note); `diagnostics` is always empty on the success path.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct InspectorPayload {
    /// The program's name + full source text.
    pub source: SourceInfo,
    /// Every resolved use→definition pair.
    pub definitions: Vec<DefinitionEntry>,
    /// Per-scope visible-binding lists.
    pub scopes: Vec<ScopeEntry>,
    /// Always empty on the success path (see the module doc's "Populated vs.
    /// stubbed" section) — a failed compile carries real diagnostics through
    /// [`InspectorPayload::degraded`] instead.
    pub diagnostics: Vec<Diagnostic>,
    /// InspectedProgram metadata + the live-protocol seams.
    pub meta: Meta,
    /// The panes, upstream → downstream, each carrying its own node
    /// table and span index — one entry per pane
    /// [`PANES`](crate::ccl::panes::PANES) declares, in pipeline order. Read
    /// `PANES` for the current set rather than a list here.
    pub panes: Vec<PaneEntry>,
    /// The dense node→node links between adjacent panes — each adjacent pane
    /// pair's `ProvenanceMap` shipped verbatim, self-edges included. One entry
    /// per adjacent pair, in the same order as `panes.windows(2)`, so this is
    /// always one shorter than [`panes`](Self::panes).
    pub pane_links: Vec<PaneLinkEntry>,
}

/// One IR pipeline pane in the multi-pane snapshot.
///
/// Carries its own self-contained node table and span index — each pane
/// resolves against its own (`Expr`, `SourceProjection`) pair.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct PaneEntry {
    /// Stable machine id — the pane's declared name, e.g. `"pre-inference"`,
    /// `"post-inference"`, `"post-channelize"`.
    pub id: &'static str,
    /// Human-readable label for the pane header, derived from `id`.
    pub label: String,
    /// Discriminant for the pane kind: `"holes"` for a tree inference has not
    /// run on yet, `"typed"` for one it has.
    pub kind: &'static str,
    /// The id of the pane's root node — where a consumer starts walking
    /// [`nodes`](Self::nodes).
    pub root: u64,
    /// Every node of this pane exactly once, in first-visit pre-order. A node
    /// reached from several places — a refinement predicate shared by several
    /// type slots, most of all — is one entry here that each of those places
    /// names by id.
    pub nodes: Vec<IrNode>,
    /// Every `(span → nodeId)` entry of this pane's span index.
    pub span_index: Vec<SpanEntry>,
}

/// One node of a pane's shipped node table.
///
/// The wire's own node type, owned here rather than borrowed from the terminal
/// renderer: the fields are this payload's and nothing else sets them. See
/// `src/inspector_model/design.md`, "A node on the wire".
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct IrNode {
    /// The node's kind, rendered — `BinOp(Arithmetic(Mul))`, `Lit(Int(1))`,
    /// `Let(x)`. Built by `node_label`.
    pub label: String,
    /// The node's [`NodeId`](crate::ccl::provenance::NodeId) as a number — the
    /// handle every pane link and span row names.
    pub node_id: u64,
    /// The **narrowest** source span this node traces to, absent when it traces
    /// to none. A node several source spans fan into carries one of them here
    /// and all of them in [`PaneEntry::span_index`], so it stays reachable from
    /// each.
    pub span: Option<Span>,
    /// The node's rewrite tag, `None` for a
    /// [`Nature::Source`](crate::ccl::provenance::Nature::Source) tag — the root
    /// of a lowered source expression — and for a node the pane's projection
    /// does not cover. The spans channel of the same attribution rides
    /// [`span`](Self::span).
    pub rewritten: Option<RewriteInfo>,
    /// The node's type, rendered by `Display for Type`, so a change to that
    /// rendering changes this verbatim. See
    /// `src/inspector_model/design.md`, "Types on the wire".
    #[cfg_attr(feature = "serde", serde(rename = "type"))]
    pub ty: String,
    /// Which constructor sits at the top of [`ty`](Self::ty) — `"base"`,
    /// `"fun"`, `"dataFun"`, `"refinement"`, `"hole"`, … — so a consumer can
    /// branch on the type without parsing the rendering. Says nothing about what
    /// is inside the type.
    pub type_kind: &'static str,
    /// The predicates riding [`ty`](Self::ty), as ids into this pane's table.
    ///
    /// A node's `where.N` children cover every type slot it carries, so they do
    /// not say which predicate refines *this node's* type; these do. They are the
    /// node's leading predicate children, since the walk reaches the node's own
    /// type first.
    pub predicate_refs: Vec<u64>,
    /// The node's children, each named by id under the edge that reaches it.
    pub children: Vec<IrChild>,
}

/// One `{ edge, id, predicate }` child of an [`IrNode`] — an edge into the
/// pane's node table.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct IrChild {
    /// The edge's display label: a value child's positional index (`"0"`,
    /// `"1"`, …), or `where.N` for a refinement predicate riding one of the
    /// parent's type slots.
    pub edge: String,
    /// The child node's id — an entry of the same pane's
    /// [`nodes`](PaneEntry::nodes).
    pub id: u64,
    /// Whether the child is a type-interior subtree: `true` for a refinement
    /// predicate, `false` for a value child. This is what a consumer branches
    /// on, rather than reading a `where.` prefix off
    /// [`edge`](Self::edge); see `src/inspector_model/design.md`, "Predicates
    /// are nodes".
    pub predicate: bool,
}

/// A node's rewrite tag — the
/// [`RewriteTag`](crate::ccl::provenance::RewriteTag) of its attribution,
/// rendered for the wire.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct RewriteInfo {
    /// The phase that performed the rewrite — the
    /// [`Phase`](crate::ccl::context::Phase) debug name, e.g. `"Infer"`.
    pub via: String,
    /// The `Nature` discriminant as its wire string: `"expansion"` for a
    /// faithful expansion of a user construct, `"machinery"` for pure plumbing.
    /// `"source"` never ships — that tag null-compresses to
    /// [`IrNode::rewritten`] `= None`.
    pub nature: String,
    /// The rewrite's stable label, e.g. `"channelize.feed_union"`.
    pub label: String,
}

/// The dense node→node links between two adjacent panes — the
/// pane-pair [`ProvenanceMap`](crate::ccl::provenance::ProvenanceMap) shipped verbatim.
///
/// **Dense**: an id preserved unchanged across the phase appears as its own
/// `[id, id]` self-edge, so the consumer follows edges only (no identity special
/// case). Genuine identity changes (monomorphization / inline fan-out) are the
/// `u != d` edges.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct PaneLinkEntry {
    /// The upstream pane id, e.g. `"pre-inference"`.
    pub from: &'static str,
    /// The downstream pane id, e.g. `"post-inference"`.
    pub to: &'static str,
    /// Every edge as `(upstream_node_id, downstream_node_id, labels)`,
    /// self-edges included, sorted deterministically. `labels` is a non-empty
    /// set drawn from `"descends"` (the downstream node was made from the
    /// upstream one) and `"relates"` (it is *about* the upstream node but was
    /// not made from it); an edge reachable both ways carries both.
    pub edges: Vec<(u64, u64, Vec<&'static str>)>,
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

/// One `{ span, nodeId }` row of `spanIndex`.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub struct SpanEntry {
    /// The origin span.
    pub span: Span,
    /// The node indexed under it.
    pub node_id: NodeId,
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
    /// The binder's declared type, read off the IR node that binds it. `None`
    /// (serializes as `null`) when no IR node binds the name — a substituted
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
/// `diagnostics` on [`InspectorPayload`] stays `[]` for *successful* compiles
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
    /// The compiler stage that produced it — `"parse"`, `"lower"`, `"infer"`, …
    ///
    /// A `CompileError` variant, not a pane: no value of it appears in
    /// [`PANES`](crate::ccl::panes::PANES). This is the one place the word
    /// "stage" is the right one.
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
    /// The message is the variant's `Display` rendering, which is the same
    /// single-line text the terminal path puts in its ariadne label, so the two
    /// renderers say the same thing. Two variants have no `Display` and use
    /// `Debug` instead: [`InferError`](crate::ccl::infer::InferError), whose
    /// `Debug` *is* its message by convention (`infer_report` renders it that
    /// way), and `ConversionError`.
    ///
    /// The span is the error's own wherever it carries one. `Infer`'s is
    /// resolved at the `compile_program` boundary and arrives on the variant;
    /// the rest read theirs off the error. A variant with no span degrades to
    /// `span: None` — still renderable, but the consumer has nothing to
    /// underline, which is why the ones that can carry a span do.
    ///
    /// [`CompileError`]: crate::ccl::context::CompileError
    pub fn from_compile_error(error: &crate::ccl::context::CompileError) -> Self {
        use crate::ccl::context::CompileError;
        let (stage, message, span) = match error {
            CompileError::Parse(e) => ("parse", e.to_string(), Some(e.span())),
            CompileError::Lower(e) => ("lower", e.to_string(), Some(e.span())),
            CompileError::ChannelizeDefers(e) => ("channelizeDefers", e.to_string(), None),
            CompileError::Infer { error, span } => ("infer", format!("{error:?}"), *span),
            CompileError::LambdaElim(e) => ("lambdaElim", e.to_string(), None),
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
    pub payload_kind: String,
    /// The wire-format version. A client reads this to detect an incompatible
    /// payload before parsing the rest.
    ///
    /// The current version is [`SCHEMA_VERSION`], whose field set is
    /// [`InspectorPayload`]'s as documented on that type. Each
    /// `panes[].nodes[]` entry carries its attribution as the spans channel on
    /// `span` plus a `rewritten` tag (`null | { via, nature, label }`).
    ///
    /// **Bump the version** on any *breaking* wire change — a field removed,
    /// renamed, or retyped, or a value-shape change an old client would
    /// misread. Purely *additive* optional fields do **not** bump it (an old
    /// client ignores them). The frontend pins this in its wire-shape contract
    /// test, so a bump is a deliberate, reviewed event on both sides.
    pub schema: u32,
}

/// Every edge of a pane-pair [`ProvenanceMap`], as `(upstream, downstream, labels)`
/// — **dense**: self-edges (`u == d`, a node preserved across the phase) are
/// kept, so the frontend needs no identity special case.
///
/// The labels say what the edge *asserts*, which a consumer needs in order to
/// render or prune the two apart: `"descends"` for an edge the downstream node
/// was made from, `"relates"` for one it is about but was not made from. They
/// are a **set** — an edge reachable both ways carries both — so this is an
/// array rather than one discriminant, and an edge always carries at least one.
///
/// [`ProvenanceMap::edges`] already yields sorted, deduplicated edges, one entry
/// per pair; this only projects to the wire's `u64` and label strings.
pub fn dense_edges(map: &ProvenanceMap<NodeId, NodeId>) -> Vec<(u64, u64, Vec<&'static str>)> {
    map.edges()
        .into_iter()
        .map(|(u, d)| (u.as_u64(), d.id.as_u64(), wire_labels(d.labels)))
        .collect()
}

/// The wire spelling of an edge's label set, in a fixed order so the payload is
/// deterministic.
fn wire_labels(labels: EdgeLabels) -> Vec<&'static str> {
    let mut out = Vec::with_capacity(2);
    if labels.has_ancestry() {
        out.push("descends");
    }
    if labels.has_blame() {
        out.push("relates");
    }
    debug_assert!(!out.is_empty(), "an edge carries at least one label");
    out
}

/// The wire's discriminant for a type: which constructor it is, without its
/// contents.
///
/// A rendered type is one string ([`crate::inspector_model`]'s design doc,
/// "Types on the wire"), so a consumer that wants to branch — colour the
/// function-typed nodes, filter to the refined ones — has nothing to branch on.
/// This is that datum, and nothing more: it says which constructor sits at the
/// top of the type, never what is inside it.
///
/// A function's kind is part of the discriminant, since the two render
/// differently (`⇒` against `⤇`) and mean different things. An unpinned kind
/// variable reads as a compute function, matching how `Display` renders it.
fn type_kind(ty: &Type) -> &'static str {
    match ty {
        Type::Base(_) => "base",
        Type::UIntRange(_) => "range",
        Type::Fun {
            kind: FunKind::Data,
            ..
        } => "dataFun",
        Type::Fun { .. } => "fun",
        Type::Tuple(_) => "tuple",
        Type::Record(_) => "record",
        Type::Variant(..) => "variant",
        Type::Refinement(..) => "refinement",
        Type::Hole | Type::SharedHole(_) | Type::BoundedHole(_) => "hole",
        Type::Infer(_) => "infer",
        Type::DataSource(_) => "source",
        Type::ChanDom(..) => "channel",
        Type::Txn => "txn",
        // A history is a mutable variable or a feed channel, and the two read
        // differently enough that one discriminant would hide the distinction.
        Type::History { kind, .. } => match kind {
            HistoryKind::Overwrite => "mut",
            HistoryKind::Append => "feed",
        },
    }
}

/// The predicates riding `ty` itself, as node ids, in the order
/// [`predicate_children`] reaches them.
///
/// A node's `where.N` children cover every type slot it carries — its own type,
/// an annotation, a `Cast` target, each binder's type — so a consumer holding
/// them cannot tell which predicate refines *this node's* type. These are that
/// subset, and because `predicate_children` walks the node's own type first,
/// they are its leading children.
fn own_type_predicates(ty: &Type) -> Vec<u64> {
    fn walk(t: &Type, out: &mut Vec<u64>) {
        if let Type::Refinement(_, refinements) = t {
            for r in refinements.iter() {
                out.push(r.predicate.node_id().as_u64());
            }
        }
        t.walk_children(|c| walk(c, out));
    }
    let mut out = Vec::new();
    walk(ty, &mut out);
    out
}

/// Build one pane's node table against its `projection`, returning the root
/// node's id and every node reachable from `expr` exactly once, in first-visit
/// pre-order.
///
/// The single source-linking node builder: every pane's payload nodes go
/// through this one shape, parameterized only by its `(Expr, SourceProjection)`
/// pair.
///
/// A node reached from several places — a refinement predicate shared by
/// several type slots — is emitted once and named by id from each place that
/// reaches it, so nothing repeats and the walk terminates on a shared term. The
/// pre-order is what makes the emitted array byte-reproducible.
fn build_node_table(expr: &Expr, projection: &SourceProjection) -> (u64, Vec<IrNode>) {
    fn visit(
        expr: &Expr,
        projection: &SourceProjection,
        visited: &mut std::collections::HashSet<NodeId>,
        out: &mut Vec<IrNode>,
    ) -> u64 {
        let id = expr.node_id();
        if !visited.insert(id) {
            return id.as_u64();
        }

        let mut node = IrNode {
            label: node_label(&expr.node),
            node_id: id.as_u64(),
            span: None,
            rewritten: None,
            ty: expr.ty.to_string(),
            type_kind: type_kind(&expr.ty),
            predicate_refs: own_type_predicates(&expr.ty),
            children: Vec::new(),
        };
        if let Some(attr) = projection.get(&id) {
            // The rewrite channel: a `Nature::Source` tag — the root of a
            // lowered source expression — null-compresses and carries no wire
            // tag; every other node carries `{via, nature, label}`. The
            // validators guard that `"source"` never ships.
            let tag = &attr.rewritten;
            if !tag.nature.is_source() {
                node.rewritten = Some(RewriteInfo {
                    via: format!("{:?}", tag.via),
                    nature: tag.nature.wire_str().to_string(),
                    label: tag.label.to_string(),
                });
            }
            // The spans channel: the node's primary (narrowest) source span, if
            // any.
            node.span = attr
                .spans
                .iter()
                .min_by_key(|s| s.end.saturating_sub(s.start))
                .copied();
        }

        // The entry claims its pre-order slot before its children are walked, so
        // the array is ordered by first visit rather than by completion.
        let slot = out.len();
        out.push(node);

        let mut children = Vec::new();
        for (idx, child) in expr.child_exprs().into_iter().enumerate() {
            children.push(IrChild {
                edge: idx.to_string(),
                id: visit(child, projection, visited, out),
                predicate: false,
            });
        }
        // Predicate subtrees come after the value children so a consumer that
        // reads children positionally is unaffected; `predicate` is what marks
        // them (see [`predicate_children`]).
        for (edge, predicate) in predicate_children(expr) {
            children.push(IrChild {
                edge,
                id: visit(predicate, projection, visited, out),
                predicate: true,
            });
        }
        out[slot].children = children;

        id.as_u64()
    }

    let mut visited = std::collections::HashSet::new();
    let mut nodes = Vec::new();
    let root = visit(expr, projection, &mut visited, &mut nodes);
    debug_assert_eq!(
        nodes.len(),
        visited.len(),
        "the node table holds one entry per visited id"
    );
    (root, nodes)
}

/// Build one pane's node table — its root id and its nodes — and its span rows.
///
/// The rows are enumerated from the index the pane already carries; building a
/// second one over the same pair would duplicate the walk. The nodes go through
/// [`build_node_table`], the single source-linking node builder.
fn build_pane_nodes_and_index(pane: &PaneProjection<'_>) -> (u64, Vec<IrNode>, Vec<SpanEntry>) {
    let span_entries = pane
        .span_index
        .entries()
        .map(|(span, node_id)| SpanEntry { span, node_id })
        .collect();

    let (root, nodes) = build_node_table(pane.ir, &pane.projection);

    (root, nodes, span_entries)
}

impl InspectedProgram<'_> {
    /// Assemble the `/api/snapshot` bulk payload by enumerating the indices.
    ///
    /// `name` is the program name for `source.name` (a placeholder; the server
    /// picks it). Every other field is derived purely from the snapshot:
    ///
    /// * `panes` — the panes in upstream → downstream order:
    ///   one per declared pane in pipeline order, each with its
    ///   own node table + span index.
    /// * `paneLinks` — per consecutive pane pair, the dense edges of the
    ///   pane-pair `ProvenanceMap` folded at that boundary, self-edges included (see
    ///   [`dense_edges`]).
    /// * `definitions` — [`NameBinderIndex::definitions`](crate::inspector_model::NameBinderIndex::definitions).
    /// * `scopes` — [`NameBinderIndex::scopes`](crate::inspector_model::NameBinderIndex::scopes),
    ///   each binding's `type` read off the IR node that binds it.
    /// * `diagnostics` — empty.
    /// * `meta` — `tick: None`, `payloadKind: "post-inference"`, `schema:
    ///   `[`SCHEMA_VERSION`].
    pub fn build_payload(&self, name: impl Into<String>) -> InspectorPayload {
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
                        // The binder's own declared type, off the IR node that
                        // binds it (`None` for a substituted multi-param
                        // parameter, which no IR node binds).
                        ty: self.binder_type(&b),
                        name: b.name.to_string(),
                        def_span: b.def_span,
                    })
                    .collect(),
            })
            .collect();

        // Build the panes (upstream → downstream) from the bundled
        // pane projections — each ships its own node table + span index.
        let panes = self
            .panes()
            .iter()
            .map(|pane| {
                let (root, nodes, span_index) = build_pane_nodes_and_index(pane);
                PaneEntry {
                    id: pane.id,
                    label: pane.label.clone(),
                    kind: pane.kind,
                    root,
                    nodes,
                    span_index,
                }
            })
            .collect();

        // Dense edges between each consecutive pane pair, read off the pane-pair
        // `ProvenanceMap` folded at that boundary (aligned with the same
        // `windows(2)`). `dense_edges` ships every edge — self-edges included —
        // already sorted for a byte-reproducible payload; the frontend follows
        // edges only, with no identity special case.
        let pane_maps = self.pane_maps();
        let pane_links = self
            .panes()
            .windows(2)
            .zip(pane_maps)
            .map(|(pair, map)| {
                let (upstream, downstream) = (&pair[0], &pair[1]);
                PaneLinkEntry {
                    from: upstream.id,
                    to: downstream.id,
                    edges: dense_edges(map),
                }
            })
            .collect();

        InspectorPayload {
            source,
            definitions,
            scopes,
            diagnostics: Vec::new(),
            meta: Meta {
                tick: None,
                payload_kind: "post-inference".to_string(),
                schema: SCHEMA_VERSION,
            },
            panes,
            pane_links,
        }
    }
}

impl InspectorPayload {
    /// The degraded `/api/snapshot` payload for a program that failed to
    /// compile: the source text + the structured diagnostics, with no typed IR.
    ///
    /// Built from the **same** [`InspectorPayload`] type as the success path
    /// (rather than a separately hand-rolled JSON object), so the two shapes
    /// cannot silently diverge as the schema evolves — the `panes`/scope
    /// collections are empty and `meta.payloadKind` is `"failed"`. The frontend
    /// still renders the editor + squiggles from this.
    ///
    /// TODO(degraded-panes): emit whatever panes *did* complete — if
    /// channelization succeeds and only inference fails, the post-channelize
    /// `panes[]` entry is still displayable. Today every degraded payload ships
    /// empty `panes`/`paneLinks` regardless of where the failure occurred. It
    /// needs `compile_program` to hand back its partial panes rather than one
    /// error, so the change is mostly outside this module; see
    /// `src/inspector_model/design.md`, "Diagnostics and the degraded payload".
    pub fn degraded(
        name: impl Into<String>,
        text: impl Into<String>,
        diagnostics: Vec<Diagnostic>,
    ) -> InspectorPayload {
        InspectorPayload {
            source: SourceInfo {
                name: name.into(),
                text: text.into(),
            },
            definitions: Vec::new(),
            scopes: Vec::new(),
            diagnostics,
            meta: Meta {
                tick: None,
                payload_kind: "failed".to_string(),
                schema: SCHEMA_VERSION,
            },
            panes: Vec::new(),
            pane_links: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::context::{CompiledProgram, GlobalContext, collect_tree_ids, compile_program};
    use crate::ccl::panes::PANES;
    use crate::interpreter::Consumer;
    use indoc::indoc;
    use std::collections::{HashMap, HashSet};

    fn compile(code: &str) -> CompiledProgram {
        let mut ctx = GlobalContext::default();
        let consumer: Box<dyn Consumer> = Box::new(|| {});
        compile_program(&mut ctx, code, consumer).expect("program compiles")
    }

    /// The span of the `n`-th (0-based) byte occurrence of `needle` in `code`.
    fn nth_span(code: &str, needle: &str, n: usize) -> Span {
        let start = code
            .match_indices(needle)
            .nth(n)
            .unwrap_or_else(|| panic!("occurrence {n} of {needle:?} not found"))
            .0;
        Span::new(start, start + needle.len())
    }

    /// Programs whose shapes reach the payload's moving parts: a comprehension
    /// (refinement predicates on type slots), a monomorphized definition (one
    /// source span over several nodes), and a mutable loop (a recurrence, whose
    /// phases rewrite the most).
    fn corpus() -> Vec<&'static str> {
        vec![
            indoc! {r#"
                xs = [1, 2, 3, 4]
                ys = [x * 2 for x in xs if x > 2]
                max(ys)
            "#},
            indoc! {r#"
                dup = \x -> (x, x)
                (dup(1), dup("a"))
            "#},
            indoc! {r#"
                total := 0
                for x in [1, 2, 3]:
                  total := total + x
                total
            "#},
        ]
    }

    /// Every `nodeId` in one pane's shipped node table.
    fn pane_ids(pane: &PaneEntry) -> HashSet<u64> {
        pane.nodes.iter().map(|n| n.node_id).collect()
    }

    /// The pane's node carrying `id`. Panics when no node does, which is the
    /// dangling-child-id failure `every_child_id_resolves_in_its_own_table`
    /// rules out over the whole corpus.
    fn node_with_id(pane: &PaneEntry, id: u64) -> &IrNode {
        pane.nodes
            .iter()
            .find(|n| n.node_id == id)
            .unwrap_or_else(|| panic!("node {id} is absent from the {} table", pane.id))
    }

    /// The pane's first node labelled `label`.
    fn node_named<'a>(pane: &'a PaneEntry, label: &str) -> &'a IrNode {
        pane.nodes
            .iter()
            .find(|n| n.label == label)
            .unwrap_or_else(|| panic!("no {label} node in the {} table", pane.id))
    }

    /// Every node reachable from `id` by following child edges, `id` included.
    fn reachable(pane: &PaneEntry, id: u64) -> Vec<&IrNode> {
        let mut seen = HashSet::new();
        let mut queue = vec![id];
        let mut out = Vec::new();
        while let Some(id) = queue.pop() {
            if !seen.insert(id) {
                continue;
            }
            let node = node_with_id(pane, id);
            out.push(node);
            queue.extend(node.children.iter().map(|c| c.id));
        }
        out
    }

    /// The payload's pane list is [`PANES`]: one pane per declared pane, in
    /// pipeline order, under the pane's own name, and one link per adjacent pair
    /// naming the panes it joins.
    ///
    /// This is what "adding a pane is an entry in `PANES` and no edit here" means
    /// operationally. The `cambra-inspector` crate pins the same set as a literal
    /// list, so that a pane added upstream fails a test rather than appearing
    /// unannounced; this asserts the two agree at the producer.
    #[test]
    fn the_payload_ships_one_pane_entry_per_declared_pane_and_one_link_per_pair() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");

            let ids: Vec<&str> = payload.panes.iter().map(|s| s.id).collect();
            let declared: Vec<&str> = PANES.iter().map(|p| p.name).collect();
            assert_eq!(ids, declared, "panes are `PANES`, in order");

            assert_eq!(
                payload.pane_links.len(),
                payload.panes.len() - 1,
                "one link per adjacent pane pair"
            );
            for (link, pair) in payload.pane_links.iter().zip(payload.panes.windows(2)) {
                assert_eq!(link.from, pair[0].id);
                assert_eq!(link.to, pair[1].id);
            }

            // The kind is read off the phases, so exactly the panes at or after
            // inference are typed.
            assert_eq!(
                payload.panes[0].kind, "holes",
                "the anchor precedes inference"
            );
            assert!(
                payload.panes[1..].iter().all(|s| s.kind == "typed"),
                "every pane at or after inference is typed"
            );
            assert_eq!(payload.meta.schema, SCHEMA_VERSION);
        }
    }

    /// Every pane-link endpoint is a node of the tree it points into.
    ///
    /// This is why every walk that builds the payload descends into refinement
    /// predicates: their ids are rows the fold explains, so they are endpoints of
    /// the pane-pair maps, and a tree walk stopping at the main expression tree
    /// would ship links pointing at nodes the payload had omitted. A consumer
    /// following such an edge lands nowhere.
    #[test]
    fn every_pane_link_endpoint_is_a_node_of_the_tree_it_points_into() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");
            let ids: HashMap<&str, HashSet<u64>> =
                payload.panes.iter().map(|s| (s.id, pane_ids(s))).collect();

            for link in &payload.pane_links {
                assert!(
                    !link.edges.is_empty(),
                    "{} → {} has edges",
                    link.from,
                    link.to
                );
                for (upstream, downstream, labels) in &link.edges {
                    assert!(
                        ids[link.from].contains(upstream),
                        "edge upstream {upstream} is absent from the {} tree",
                        link.from
                    );
                    assert!(
                        ids[link.to].contains(downstream),
                        "edge downstream {downstream} is absent from the {} tree",
                        link.to
                    );
                    assert!(
                        !labels.is_empty(),
                        "an edge asserts at least one of descends/relates"
                    );
                }
            }
        }
    }

    /// Every `spanIndex` row points at a node the same pane's tree carries, so a
    /// span lookup cannot resolve to an id the consumer has no node for.
    #[test]
    fn every_span_index_row_points_at_a_node_of_its_own_pane() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");
            for pane in &payload.panes {
                let ids = pane_ids(pane);
                for row in &pane.span_index {
                    assert!(
                        ids.contains(&row.node_id.as_u64()),
                        "spanIndex row {:?} names an id absent from the {} table",
                        row.node_id,
                        pane.id
                    );
                }
            }
        }
    }

    /// A shipped node carries the row `src/inspector_model/design.md`, "A node on
    /// the wire" describes: an id, the narrowest span it traces to, a rendered
    /// type, no rewrite tag when its tag is `Nature::Source`, positional edges
    /// for its value children and `where.N`, marked `predicate`, for a predicate
    /// riding one of its type slots.
    #[test]
    fn a_wire_node_carries_its_id_span_type_and_edges() {
        let code = indoc! {r#"
            xs = [1, 2, 3, 4]
            ys = [x * 2 for x in xs if x > 2]
            max(ys)
        "#};
        let prog = compile(code);
        let payload = InspectedProgram::new(&prog).build_payload("test");
        let pane = payload
            .panes
            .iter()
            .find(|s| s.id == "post-inference")
            .expect("the payload ships the post-inference pane");

        let mut spans: HashMap<u64, Vec<Span>> = HashMap::new();
        for row in &pane.span_index {
            spans
                .entry(row.node_id.as_u64())
                .or_default()
                .push(row.span);
        }

        for node in &pane.nodes {
            // The node ships one span and the rows ship all of them, so the one
            // it ships is the narrowest.
            let narrowest = spans
                .get(&node.node_id)
                .and_then(|s| s.iter().copied().min_by_key(|s| s.end - s.start));
            assert_eq!(
                node.span, narrowest,
                "{} ships the narrowest of {:?}",
                node.label, spans[&node.node_id]
            );
            assert!(!node.ty.is_empty(), "{} ships a type", node.label);

            // Value children come first under their positional index; every
            // predicate follows, under `where.N`, and the flag says which is
            // which without reading the label.
            let positional = node.children.iter().take_while(|c| !c.predicate).count();
            let edges: Vec<&str> = node.children.iter().map(|c| c.edge.as_str()).collect();
            let expected: Vec<String> = (0..positional)
                .map(|i| i.to_string())
                .chain((0..edges.len() - positional).map(|i| format!("where.{i}")))
                .collect();
            assert_eq!(edges, expected, "{}'s edges", node.label);
            assert!(
                node.children[positional..].iter().all(|c| c.predicate),
                "{}'s `where.N` edges are the marked ones",
                node.label
            );
        }

        // `x * 2` is the root of a lowered source expression, so its rewrite tag
        // null-compresses; it carries its own span and its inferred type.
        let mul = node_named(pane, "BinOp(Arithmetic(Mul))");
        assert_eq!(mul.span, Some(Span::new(24, 29)), "the span of `x * 2`");
        assert_eq!(mul.ty, "Int");
        assert!(
            mul.rewritten.is_none(),
            "a `Nature::Source` tag null-compresses; got {:?}",
            mul.rewritten
        );

        // The comprehension's filter rides the `Cast`'s refined domain, so it
        // hangs off a marked `where.N` edge rather than a positional one.
        let cast = node_named(pane, "Cast");
        let edges: Vec<(&str, bool)> = cast
            .children
            .iter()
            .map(|c| (c.edge.as_str(), c.predicate))
            .collect();
        assert_eq!(edges, [("0", false), ("where.0", true), ("where.1", true)]);
        let predicate = node_with_id(pane, cast.children[1].id);
        assert_ne!(
            predicate.node_id, cast.node_id,
            "a predicate is a node in its own right"
        );
        let labels: Vec<&str> = reachable(pane, predicate.node_id)
            .iter()
            .map(|n| n.label.as_str())
            .collect();
        assert!(
            labels.contains(&"BinOp(Compare(Greater))"),
            "the `x > 2` filter is the predicate subtree; got {labels:?}"
        );
    }

    /// Every child id, and every pane's `root`, names a node of that pane's own
    /// table. A dangling child id is the failure the node table makes possible
    /// and a nested tree could not express.
    #[test]
    fn every_child_id_resolves_in_its_own_table() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");
            for pane in &payload.panes {
                let ids = pane_ids(pane);
                assert!(
                    ids.contains(&pane.root),
                    "the {} root {} is absent from its own table",
                    pane.id,
                    pane.root
                );
                for node in &pane.nodes {
                    for child in &node.children {
                        assert!(
                            ids.contains(&child.id),
                            "{}'s child edge {} of {} names {}, absent from the {} table",
                            node.label,
                            child.edge,
                            node.node_id,
                            child.id,
                            pane.id
                        );
                    }
                }
            }
        }
    }

    /// A pane's table holds each node exactly once, and holds exactly the ids
    /// `collect_tree_ids` enumerates for that pane's tree — the main tree plus
    /// everything reachable through its type slots.
    ///
    /// The two halves are one claim from opposite sides: no id repeats, and the
    /// id set is neither short of nor beyond what the pane holds. `collect_tree_ids`
    /// is the same enumeration the pane folds explain, so a table disagreeing
    /// with it would ship pane links whose endpoints have no node.
    #[test]
    fn a_pane_table_holds_each_node_exactly_once() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");
            for (pane, tree) in payload.panes.iter().zip(prog.pane_trees()) {
                let mut seen = HashSet::new();
                for node in &pane.nodes {
                    assert!(
                        seen.insert(node.node_id),
                        "{} appears twice in the {} table",
                        node.node_id,
                        pane.id
                    );
                }

                let held: HashSet<u64> =
                    collect_tree_ids(tree).iter().map(|i| i.as_u64()).collect();
                let dropped: Vec<u64> = held.difference(&seen).copied().collect();
                let invented: Vec<u64> = seen.difference(&held).copied().collect();
                assert!(
                    dropped.is_empty() && invented.is_empty(),
                    "the {} table drops {dropped:?} and invents {invented:?}",
                    pane.id
                );
            }
        }
    }

    /// No `(span, nodeId)` row repeats. The rows come from one visit per node,
    /// so a node reached from several type slots contributes its rows once; a
    /// node indexed under several *distinct* spans still contributes one row per
    /// span.
    #[test]
    fn no_span_index_row_repeats() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");
            for pane in &payload.panes {
                let mut seen = HashSet::new();
                for row in &pane.span_index {
                    assert!(
                        seen.insert((row.span.start, row.span.end, row.node_id)),
                        "the {} span index repeats ({:?}, {:?})",
                        pane.id,
                        row.span,
                        row.node_id
                    );
                }
            }
        }
    }

    /// A predicate reached from more than one type slot is one entry in the
    /// table, named by each edge that reaches it. This is the repetition the
    /// node table removes: the nested tree emitted the whole subtree once per
    /// slot.
    #[test]
    fn a_shared_predicate_is_one_entry_named_by_several_edges() {
        // The comprehension's filter rides both the `Cast`'s own refined type
        // and its target, so the same predicate term is reached twice.
        let code = corpus()[0];
        let prog = compile(code);
        let payload = InspectedProgram::new(&prog).build_payload("test");
        let pane = payload
            .panes
            .iter()
            .find(|s| s.id == "post-inference")
            .expect("the payload ships the post-inference pane");

        let mut edges: HashMap<u64, usize> = HashMap::new();
        for node in &pane.nodes {
            for child in node.children.iter().filter(|c| c.predicate) {
                *edges.entry(child.id).or_default() += 1;
            }
        }
        let (&shared, &count) = edges
            .iter()
            .find(|&(_, &count)| count > 1)
            .expect("a predicate this pane reaches from more than one type slot");
        assert!(count > 1, "{shared} is named by {count} predicate edges");
        assert_eq!(
            pane.nodes.iter().filter(|n| n.node_id == shared).count(),
            1,
            "the shared predicate {shared} is one entry in the table"
        );
    }

    /// A parse failure — the most common one — ships a message a person can read
    /// and a span the consumer can underline.
    ///
    /// The `Debug` rendering of a `ParseError` is a struct dump naming the
    /// variant and its fields, so a consumer showing the message verbatim shows
    /// that dump; the `Display` rendering is the single line the terminal's
    /// ariadne label carries.
    #[test]
    fn a_parse_failure_ships_a_readable_message_and_a_span() {
        let code = "x = (1 + \n";
        let compiled = compile_program(
            &mut GlobalContext::default(),
            code,
            Box::new(|| {}) as Box<dyn Consumer>,
        );
        let Err(errors) = compiled else {
            panic!("an unclosed paren must fail to compile")
        };
        let diagnostics = diagnostics_from_compile_errors(&errors);
        let parse = diagnostics
            .iter()
            .find(|d| d.stage == "parse")
            .unwrap_or_else(|| panic!("a parse diagnostic; got {diagnostics:?}"));

        assert!(
            !parse.message.contains("ParseErrorInfo") && !parse.message.contains("Span {"),
            "the message is the rendering, not the struct dump; got {:?}",
            parse.message
        );
        assert!(
            !parse.message.is_empty() && !parse.message.contains('\n'),
            "the message is one line; got {:?}",
            parse.message
        );

        let span = parse
            .span
            .unwrap_or_else(|| panic!("a parse error carries its span; got {parse:?}"));
        assert!(
            span.end <= code.len(),
            "the span is a range in this source; got {span:?} over {} bytes",
            code.len()
        );
        assert_eq!(
            parse.labels.len(),
            1,
            "the span is also a label, so a consumer can underline it"
        );
        assert_eq!(parse.labels[0].span, span);
    }

    /// A lowering failure ships its own message rather than the enum's `Debug`
    /// form, which would repeat the span and the variant name inside the text.
    #[test]
    fn a_lowering_failure_ships_its_message() {
        use crate::ccl::lower::LoweringError;
        use crate::chl_parser::ast::Span;

        let error = crate::ccl::context::CompileError::Lower(LoweringError::unsupported(
            Span::new(3, 7),
            "generators are not supported here",
        ));
        let diagnostic = Diagnostic::from_compile_error(&error);
        assert_eq!(diagnostic.stage, "lower");
        assert_eq!(diagnostic.message, "generators are not supported here");
        assert_eq!(diagnostic.span, Some(Span::new(3, 7)));
    }

    /// Every node of every pane carries an attribution, so `span` and `rewritten`
    /// are absent only where the node is a lowering root — never because the pane
    /// failed to explain the node.
    ///
    /// The wire cannot tell those apart: a node the projection does not cover
    /// ships the same `span: null, rewritten: null` as a `Nature::Source` root.
    /// This is what keeps the second case from arising, and it is the payload-wide
    /// form of the leak gate's promise that every node of a pane is explained.
    #[test]
    fn every_node_of_every_pane_carries_an_attribution() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");
            for pane in &payload.panes {
                let ids = pane_ids(pane);
                let attributed: HashSet<u64> =
                    pane.span_index.iter().map(|r| r.node_id.as_u64()).collect();
                let missing: Vec<u64> = ids.difference(&attributed).copied().collect();
                assert!(
                    missing.is_empty(),
                    "{} nodes of the {} pane carry no span row: {missing:?}",
                    missing.len(),
                    pane.id
                );
            }
        }
    }

    /// Every node carries a type discriminant, and a refined node's
    /// `predicateRefs` name predicate nodes of its own pane — the two facts a
    /// consumer needs to branch on a type it only receives rendered.
    ///
    /// `predicateRefs` is the leading part of a node's predicate children,
    /// because the walk reaches the node's own type before its annotation, its
    /// `Cast` target and its binders. That is what lets a consumer tell "the
    /// predicate refining this node's type" from "a predicate riding some other
    /// slot of it".
    #[test]
    fn a_node_carries_its_type_kind_and_its_own_predicates() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");
            for pane in &payload.panes {
                let ids = pane_ids(pane);
                let mut refined = 0;
                for node in &pane.nodes {
                    assert!(
                        !node.type_kind.is_empty(),
                        "node {} has no type discriminant",
                        node.node_id
                    );
                    if node.type_kind == "refinement" {
                        refined += 1;
                        assert!(
                            !node.predicate_refs.is_empty(),
                            "a refined node names the predicates refining it; node {}",
                            node.node_id
                        );
                    }
                    for id in &node.predicate_refs {
                        assert!(
                            ids.contains(id),
                            "predicate ref {id} resolves in the {} table",
                            pane.id
                        );
                    }
                    // The node's own type is walked first, so its predicates are
                    // the leading predicate children.
                    let predicate_children: Vec<u64> = node
                        .children
                        .iter()
                        .filter(|c| c.predicate)
                        .map(|c| c.id)
                        .collect();
                    assert_eq!(
                        predicate_children[..node.predicate_refs.len()],
                        node.predicate_refs[..],
                        "node {}'s own-type predicates lead its predicate children",
                        node.node_id
                    );
                }
                // Inference types a literal by which literal it is, so a pane it
                // has run on carries refined nodes; before it, the types are
                // holes and this says nothing.
                if pane.kind == "typed" {
                    assert!(
                        refined > 0,
                        "the {} pane is typed, so a literal's singleton refines some node",
                        pane.id
                    );
                }
            }
        }
    }

    /// A degraded payload carries the diagnostics and no IR: same type as the
    /// success path, so the two shapes cannot drift apart.
    #[test]
    fn a_degraded_payload_carries_diagnostics_and_no_panes() {
        let compiled = compile_program(
            &mut GlobalContext::default(),
            "z + 1\n",
            Box::new(|| {}) as Box<dyn Consumer>,
        );
        let Err(errors) = compiled else {
            panic!("an unbound name must fail to compile")
        };
        let diagnostics = diagnostics_from_compile_errors(&errors);
        assert!(!diagnostics.is_empty(), "the failure produces diagnostics");

        let payload = InspectorPayload::degraded("test", "z + 1\n", diagnostics);
        assert_eq!(payload.meta.payload_kind, "failed");
        assert_eq!(payload.meta.schema, SCHEMA_VERSION);
        assert!(payload.panes.is_empty());
        assert!(payload.pane_links.is_empty());
        assert!(!payload.diagnostics.is_empty());
    }

    /// A let-polymorphic def used at two types fans out: the pre-inference →
    /// post-inference map (folded from the rows `Phase::Infer` wrote) is dense —
    /// surviving nodes carry `[id, id]` self-edges — and at least one upstream
    /// node fans out to ≥2 distinct downstream nodes (the specialization
    /// clones), a genuine `u != d` identity change.
    #[test]
    fn mono_fanout_links_upstream_def_to_downstream_clones() {
        let code = "\
dup = \\x -> (x, x)
a = dup(1)
b = dup(2 == 2)
a
";
        let prog = compile(code);
        let panes = prog.materialize_panes();
        let edges = dense_edges(&panes.pair("pre-inference → post-inference").map);

        assert!(!edges.is_empty(), "the pane-pair map has edges");
        assert!(
            edges.iter().any(|(u, d, _)| u == d),
            "the dense map ships self-edges for nodes preserved across the phase"
        );

        // At least one upstream node fans out to ≥2 distinct downstream nodes
        // (dup used at Int and Bool) — counting only the genuine identity
        // changes, not the self-edges.
        let mut fanout: HashMap<u64, usize> = HashMap::new();
        for (u, d, _) in &edges {
            if u != d {
                *fanout.entry(*u).or_default() += 1;
            }
        }
        assert!(
            fanout.values().any(|&n| n >= 2),
            "dup used at two types should fan out to ≥2 downstream nodes; edges={edges:?}"
        );
    }

    /// Every edge endpoint of a pane pair is a node of the pane it points into.
    ///
    /// The id set is `collect_tree_ids`', not `walk_children`': predicate
    /// interiors are rows the fold explains, so they are edge endpoints, and a
    /// tree walk that stopped at the main tree would call a live endpoint dead.
    /// This is the invariant the wire validators enforce on the shipped payload,
    /// asserted here against the source of truth.
    fn assert_endpoints_live(
        edges: &[(u64, u64, Vec<&'static str>)],
        upstream: &Expr,
        downstream: &Expr,
        up_name: &str,
        down_name: &str,
    ) {
        let ids = |e: &Expr| -> HashSet<u64> {
            collect_tree_ids(e).iter().map(|id| id.as_u64()).collect()
        };
        let up_ids = ids(upstream);
        let down_ids = ids(downstream);
        for (u, d, _) in edges {
            assert!(
                up_ids.contains(u),
                "edge upstream id {u} must be a node in the {up_name} tree"
            );
            assert!(
                down_ids.contains(d),
                "edge downstream id {d} must be a node in the {down_name} tree"
            );
        }
    }

    /// A two-site inline fan-out surfaces as non-identity edges on the
    /// post-inference → post-channelize map, each edge's upstream a
    /// post-inference node and downstream a post-channelize node.
    #[test]
    fn inline_fanout_links_post_inference_to_post_channelize_copies() {
        let code = "\
add1 = \\x -> x + 1
a = add1(10)
b = add1(20)
a + b
";
        let prog = compile(code);
        let panes = prog.materialize_panes();
        let edges = dense_edges(&panes.pair("post-inference → post-channelize").map);
        assert!(
            !edges.is_empty(),
            "a two-site inline fan-out must produce non-identity pane edges"
        );
        assert_endpoints_live(
            &edges,
            &prog.post_inference_ir,
            &prog.post_channelize_ir,
            "post-inference",
            "post-channelize",
        );
    }

    /// A monomorphic program changes no **main-tree** identity across inference:
    /// every main-tree edge is a self-edge. Its predicates are a different story
    /// — inference rebuilds a refinement predicate rather than preserving it, so
    /// each rebuild is a genuine `u != d` edge — and this pins that the whole of
    /// the difference is predicate interiors and nothing else.
    #[test]
    fn a_monomorphic_program_changes_no_main_tree_identity_across_inference() {
        let code = "\
x = 1 + 2
x
";
        let prog = compile(code);
        let panes = prog.materialize_panes();
        let edges = dense_edges(&panes.pair("pre-inference → post-inference").map);
        assert!(
            !edges.is_empty(),
            "a compiled program has surviving nodes, hence dense self-edges"
        );
        assert_endpoints_live(
            &edges,
            &prog.pre_inference_ir,
            &prog.post_inference_ir,
            "pre-inference",
            "post-inference",
        );

        // The main tree: `walk_children` only, which is exactly the domain the
        // identity claim covers.
        fn main_tree_ids(e: &Expr) -> HashSet<u64> {
            let mut s = HashSet::new();
            fn go(e: &Expr, s: &mut HashSet<u64>) {
                s.insert(e.node_id().as_u64());
                e.walk_children(|c| go(c, s));
            }
            go(e, &mut s);
            s
        }
        let up_main = main_tree_ids(&prog.pre_inference_ir);
        let down_main = main_tree_ids(&prog.post_inference_ir);

        let mut changed_main = Vec::new();
        let mut changed_predicate = 0usize;
        for (u, d, _) in &edges {
            if u == d {
                continue;
            }
            if up_main.contains(u) && down_main.contains(d) {
                changed_main.push((*u, *d));
            } else {
                changed_predicate += 1;
            }
        }
        assert!(
            changed_main.is_empty(),
            "a monomorphic program preserves every main-tree identity across \
             inference; these changed: {changed_main:?}"
        );
        assert!(
            changed_predicate > 0,
            "inference rebuilds this program's literal-singleton predicates, so \
             the pair must carry predicate-interior identity changes"
        );
    }

    // ------------------------------------------------------------------------
    // Span↔CCL (source↔IR) mapping over the payload.
    //
    // These pin which source construct maps to which IR node, over two programs
    // whose lowering produces synthetic wrapper chains: a `yield` generator and
    // a `defer()`/`<<` feed pipeline. They mirror the manual web-validation
    // examples (`cambra-inspector/examples/{generator_min,defer_min}.chl`) but
    // inline the source so the flow is exercised without the front end.
    //
    // The question they ask is the consumer's — "what is at this span" — and it
    // is asked the way a consumer asks it: over the shipped `(span, nodeId)`
    // rows and the shipped tree.
    // ------------------------------------------------------------------------

    const GENERATOR_SRC: &str = "\
def squared(xs):
    for x in xs:
        yield x * x

max(squared([1, 2, 3, 4]))
";

    const DEFER_SRC: &str = "\
readings = [1, 2, 3, 4]
totals = defer()
totals << sum(readings)
for x in readings:
    totals << x
max(totals)
";

    /// The labels of the nodes `pane_id` indexes at `span`: every `(span,
    /// nodeId)` row of that pane whose span covers the query, resolved to the
    /// node carrying that id in that pane's node table. This is the consumer's
    /// lookup, over the two shipped tables and nothing else.
    ///
    /// Panics if a row names a node the table does not hold — the invariant
    /// `span_index_round_trips_with_projection` (`span_index.rs`) pins.
    fn labels_at(payload: &InspectorPayload, pane_id: &str, span: Span) -> Vec<String> {
        let pane = payload
            .panes
            .iter()
            .find(|s| s.id == pane_id)
            .unwrap_or_else(|| panic!("the payload ships a {pane_id} pane"));
        pane.span_index
            .iter()
            .filter(|row| row.span.start <= span.start && span.end <= row.span.end)
            .map(|row| {
                pane.nodes
                    .iter()
                    .find(|n| n.node_id == row.node_id.as_u64())
                    .unwrap_or_else(|| panic!("row node {:?} is in the table", row.node_id))
                    .label
                    .clone()
            })
            .collect()
    }

    /// GENERATOR: the source constructs that map name the expected IR node.
    /// `x * x` → the `Mul` BinOp; `max(...)` → `Aggregate(Max)`; the list
    /// literals → their `Lit` nodes.
    #[test]
    fn generator_mapped_spans_resolve_to_expected_nodes() {
        let prog = compile(GENERATOR_SRC);
        let payload = InspectedProgram::new(&prog).build_payload("test");
        let at = |span| labels_at(&payload, "post-inference", span);

        // The `x * x` body → the arithmetic-mul BinOp (a mono clone of the
        // generator body, which *does* carry the body span).
        let mul = at(nth_span(GENERATOR_SRC, "x * x", 0));
        assert!(
            mul.iter().any(|l| l.contains("BinOp(Arithmetic(Mul))")),
            "`x * x` → Mul BinOp; got {mul:?}"
        );

        // `max(squared(...))` → the Max aggregate.
        let max = at(nth_span(GENERATOR_SRC, "max", 0));
        assert!(
            max.iter().any(|l| l.contains("Aggregate(Max)")),
            "`max` → Max; got {max:?}"
        );

        // The list literals `1` and `2` map to their Lit nodes.
        let lit1 = at(nth_span(GENERATOR_SRC, "1", 0));
        assert!(
            lit1.iter().any(|l| l.contains("Lit(Int(1))")),
            "`1` → Lit; got {lit1:?}"
        );
        let lit2 = at(nth_span(GENERATOR_SRC, "2", 0));
        assert!(
            lit2.iter().any(|l| l.contains("Lit(Int(2))")),
            "`2` → Lit; got {lit2:?}"
        );

        // The whole `[1, 2, 3, 4]` list literal (the argument of the
        // monomorphized `squared(...)` call) maps to the `List` node. Span the
        // elements, not the whole `[...]`: the `[` sits outside the lowered list
        // span, so the elements' extent is what a row covers.
        let list = at(nth_span(GENERATOR_SRC, "1, 2, 3, 4", 0));
        assert!(
            list.iter().any(|l| l.contains("List")),
            "`[1, 2, 3, 4]` → List; got {list:?}"
        );
    }

    /// DEFER: the source constructs that map name the expected IR node.
    /// `sum(readings)` → `Aggregate(Sum)`; `max(totals)` → `Aggregate(Max)`; the
    /// `totals` use in `max(totals)` → `Var(totals)`; the readings list literals
    /// map.
    #[test]
    fn defer_mapped_spans_resolve_to_expected_nodes() {
        let prog = compile(DEFER_SRC);
        let payload = InspectedProgram::new(&prog).build_payload("test");
        let at = |span| labels_at(&payload, "post-inference", span);

        let sum = at(nth_span(DEFER_SRC, "sum", 0));
        assert!(
            sum.iter().any(|l| l.contains("Aggregate(Sum)")),
            "`sum` → Sum; got {sum:?}"
        );

        let max = at(nth_span(DEFER_SRC, "max", 0));
        assert!(
            max.iter().any(|l| l.contains("Aggregate(Max)")),
            "`max` → Max; got {max:?}"
        );

        // `totals` occurs 4×: the def (0), the two `<<` feeds (1, 2), and the
        // `max(totals)` use (3). The last is the read whose span maps to Var.
        let totals_use = at(nth_span(DEFER_SRC, "totals", 3));
        assert!(
            totals_use.iter().any(|l| l.contains("Var(totals)")),
            "`totals` in `max(totals)` → Var(totals); got {totals_use:?}"
        );

        // The readings list literals map to Lit nodes.
        let lit1 = at(nth_span(DEFER_SRC, "1", 0));
        assert!(
            lit1.iter().any(|l| l.contains("Lit(Int(1))")),
            "`1` → Lit; got {lit1:?}"
        );
    }

    /// DEFER: the **copaired fan-in** carries a source span.
    ///
    /// `Copair` is the node the `defer()`/`<<`/`for`-feed plumbing fans into,
    /// tagged `via: Channelize, nature: Expansion`. It is indexed at the
    /// `totals = defer()` statement — the declaration the feeds fan into — so a
    /// consumer clicking the `defer()` site reaches it. Distinct from the feed
    /// plumbing (`Lambda(__unused)`, the `Compose` over the feed body), tagged
    /// `nature: Machinery`, which carries no span by design.
    ///
    /// The fan-in is a post-channelize artifact, absent from the post-inference
    /// anchor, so the payload under test carries the post-channelize pane
    /// alone.
    #[test]
    fn defer_coverage_maps_the_copaired_fan_in() {
        let prog = compile(DEFER_SRC);
        let panes = prog.materialize_panes();
        let payload = InspectedProgram::from_parts(
            "post-channelize",
            &prog.source,
            &prog.post_channelize_ir,
            panes.projection("post-channelize").clone(),
            &prog.source_ast,
        )
        .build_payload("test");
        let at = |span| labels_at(&payload, "post-channelize", span);

        // Copairing, not a disjoint join: the arms land on their coproduct, and
        // nothing asserts the two feeds cover disjoint parts of one domain.
        let defer_site = at(nth_span(DEFER_SRC, "defer()", 0));
        assert!(
            defer_site.iter().any(|l| l.contains("Copair")),
            "the `defer()` declaration reaches the copaired fan-in; got {defer_site:?}"
        );

        // The fed value the user wrote still maps to its own aggregate, and the
        // rest of the Part-A set maps at this pane too.
        let feed = at(nth_span(DEFER_SRC, "sum", 0));
        assert!(
            feed.iter().any(|l| l.contains("Aggregate(Sum)")),
            "`sum` → Sum; got {feed:?}"
        );
        let max = at(nth_span(DEFER_SRC, "max", 0));
        assert!(
            max.iter().any(|l| l.contains("Aggregate(Max)")),
            "`max` → Max; got {max:?}"
        );
        let totals_use = at(nth_span(DEFER_SRC, "totals", 3));
        assert!(
            totals_use.iter().any(|l| l.contains("Var(totals)")),
            "`totals` in `max(totals)` → Var(totals); got {totals_use:?}"
        );
        for digit in ["1", "2", "3", "4"] {
            let lit = at(nth_span(DEFER_SRC, digit, 0));
            assert!(
                lit.iter()
                    .any(|l| l.contains(&format!("Lit(Int({digit}))"))),
                "the readings literal `{digit}` → Lit; got {lit:?}"
            );
        }

        // Every node of the shipped table carries an attribution: the
        // fully-folded rows leave no node absent from the projection, and a node
        // the projection does not cover would ship neither a span nor a rewrite
        // tag.
        let pane = payload
            .panes
            .iter()
            .find(|s| s.id == "post-channelize")
            .expect("the payload ships the post-channelize pane");
        let absent: Vec<&str> = pane
            .nodes
            .iter()
            .filter(|n| n.span.is_none() && n.rewritten.is_none())
            .map(|n| n.label.as_str())
            .collect();
        assert!(
            absent.is_empty(),
            "no defer node is left untagged (absent from projection); got {absent:?}"
        );
    }
}
