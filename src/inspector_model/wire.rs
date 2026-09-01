//! The `/api/snapshot` bulk payload — the whole read-only model in one struct.
//!
//! `/api/snapshot` is the primary read-only endpoint: source + the panes (each
//! a node table) + use→def definitions + diagnostics + meta. This module
//! mirrors that JSON exactly as a serde-gated [`InspectorPayload`]; the actual
//! serialization (and `serde_json`) lives in `crate::inspector_server`.
//! Building the payload is pure: it resolves names over the pre-inference pane
//! (`definitions`) and builds each pane's node table via [`build_node_table`],
//! over the IR walk `walk.rs` owns.
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
//! is a `u != d` edge. What the density promises a consumer:
//! `src/inspector_model/design.md`, "Pane links are dense".
//!
//! # Wire-type isolation
//!
//! Every type here derives `Serialize` with camelCase field names (`nodeId`,
//! `useSpan`, `defSpan`, `payloadKind`, …) to match the schema. `serde_json`
//! does not live here: this module builds the typed payload and the transport
//! turns it into JSON — see the module-level note on
//! [`inspector_model`](crate::inspector_model).
//!
//! # Populated vs. stubbed
//!
//! * `source`, `panes` (each with its own node table), `definitions`, `meta` —
//!   fully populated.
//! * `diagnostics` — **always empty `[]`** in this payload: a `/api/snapshot`
//!   describes a *successfully compiled* program, and there are no warnings. The
//!   wire type ([`Diagnostic`]) drives the compile-failure path instead: a
//!   failed compile flows through [`InspectorPayload::degraded`], which carries
//!   the diagnostics in place of a real snapshot, and `/api/diagnostics` serves
//!   the same array (see `src/inspector_server/serve.rs`'s "Transport decision"
//!   note).
//! * `outline` and `meta.tick` — **omitted**. Rather than ship an empty stub of
//!   an undecided shape, or a `null` reserved for a live layer that does not
//!   exist, a field stays off the wire until something reads it.
//! * `payloadKind` is `"program"`; `schema` is [`SCHEMA_VERSION`].

use crate::ccl::Expr;
use crate::ccl::provenance::{NodeId, ProvenanceMap, SourceProjection};
use crate::chl_parser::ast::Span;
use crate::interpreter::operator_graph::{EdgeKind, EdgeRole, GraphNode, InputEdge, OperatorGraph};

use super::definitions::Definition;
use super::program::{InspectedProgram, PaneContent};
use super::walk::{node_label, predicate_children};

/// The current `/api/snapshot` wire-format version, emitted as `meta.schema` on
/// both the success and degraded payloads. See [`Meta::schema`] for the
/// versioning contract and the current version's field set.
pub const SCHEMA_VERSION: u32 = 1;

/// The `GET /api/snapshot` bulk payload — the whole static read-only model.
///
/// Field order/names mirror the schema. `outline` is intentionally absent (see
/// the module note); `diagnostics` is always empty on the success path.
#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InspectorPayload {
    /// The program's name + full source text.
    pub source: SourceInfo,
    /// Every resolved use→definition pair.
    pub definitions: Vec<DefinitionEntry>,
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
/// Carries its own self-contained node table — each pane resolves against its
/// own (`Expr`, `SourceProjection`) pair.
#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct PaneEntry {
    /// Stable machine id — the pane's declared name, e.g. `"pre-inference"`,
    /// `"post-inference"`, `"post-channelize"`.
    pub id: &'static str,
    /// Human-readable label for the pane header, derived from `id`.
    pub label: String,
    /// Discriminant for the pane kind, and for which shape
    /// [`nodes`](Self::nodes) holds: `"holes"` for a tree inference has not run
    /// on yet, `"typed"` for one it has, `"operators"` for the dataflow graph.
    pub kind: &'static str,
    /// The ids a consumer starts walking [`nodes`](Self::nodes) from.
    ///
    /// One for a tree. An operator graph has several: a sink per compiled
    /// output, and a fan input per share point, which are the nodes nothing
    /// owns.
    pub roots: Vec<u64>,
    /// Every node of this pane exactly once, in first-visit pre-order for a
    /// tree and conversion order for a graph. A node reached from several
    /// places — a refinement predicate shared by several type slots, or a fan
    /// input several branches read — is one entry that each of those places
    /// names by id.
    pub nodes: PaneNodes,
}

/// A pane's node table, in whichever shape the pane holds.
///
/// Untagged, so `nodes` is a plain array either way; [`PaneEntry::kind`] is the
/// discriminant. The two shapes share nothing but an id and an attribution: an
/// expression node has a type and children, an operator has a tiling and typed
/// input edges, and neither field set is meaningful for the other.
#[derive(Clone, Debug, serde::Serialize)]
#[serde(untagged)]
pub enum PaneNodes {
    Ir(Vec<IrNode>),
    Operators(Vec<OperatorNode>),
}

impl PaneNodes {
    /// Every node's id, in table order.
    pub fn ids(&self) -> Vec<u64> {
        match self {
            PaneNodes::Ir(nodes) => nodes.iter().map(|n| n.node_id).collect(),
            PaneNodes::Operators(nodes) => nodes.iter().map(|n| n.node_id).collect(),
        }
    }

    /// How many nodes the pane holds.
    pub fn len(&self) -> usize {
        match self {
            PaneNodes::Ir(nodes) => nodes.len(),
            PaneNodes::Operators(nodes) => nodes.len(),
        }
    }

    /// Whether the pane holds no nodes.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The expression nodes, or `None` for an operator pane.
    pub fn ir(&self) -> Option<&[IrNode]> {
        match self {
            PaneNodes::Ir(nodes) => Some(nodes),
            PaneNodes::Operators(_) => None,
        }
    }
}

/// One node of an operator pane: an operator, or one of the two program
/// boundaries.
#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OperatorNode {
    /// What to show: the operator's type name, or `Source(name)` / `Sink(name)`
    /// for a boundary.
    pub label: String,
    /// The node's [`NodeId`](crate::ccl::provenance::NodeId) as a number, in the
    /// same space as an expression node's — an operator carries a `NodeId` so a
    /// pane pair spanning conversion is homogeneous like every other.
    pub node_id: u64,
    /// Which of the three node kinds this is: `"operator"`, `"source"`,
    /// `"sink"`. Data, not display policy.
    pub role: &'static str,
    /// The operator's output tiling, rendered, and `None` for a boundary node.
    pub tiling: Option<String>,
    /// Every source span this node traces to, narrowest first. Same channel and
    /// same meaning as [`IrNode::spans`].
    pub spans: Vec<Span>,
    /// The node's rewrite tag, on the same terms as [`IrNode::rewritten`].
    pub rewritten: Option<RewriteInfo>,
    /// The graph inputs this node holds.
    pub inputs: Vec<OperatorEdge>,
}

/// One input edge of an operator node.
///
/// A **construction** edge — which operator holds which, and how. Runtime
/// dataflow follows `get` and `notify`, a different relation, and nothing here
/// asserts the two coincide.
#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OperatorEdge {
    /// What names this input at its consumer: a field name, a position, or a
    /// store key, rendered.
    pub role: String,
    /// `"value"` for an exclusively owned input, `"share"` for one several
    /// consumers may reach, `"feedback"` for a share that closes a cycle.
    ///
    /// The value edges form a forest, which is what lets a renderer walk them as
    /// a child relation with no cycle guard; share and feedback are the
    /// cross-references.
    pub kind: &'static str,
    /// Whether the edge was wired after its consumer was constructed, through a
    /// `CycleSlot`. An attribute of when, not of ownership.
    pub deferred: bool,
    /// The input's node id.
    pub id: u64,
}

/// One node of a pane's shipped node table.
///
/// The wire's own node type, owned here rather than borrowed from the terminal
/// renderer: the fields are this payload's and nothing else sets them. See
/// `src/inspector_model/design.md`, "A node on the wire".
#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct IrNode {
    /// The node's kind, rendered — `BinOp(Arithmetic(Mul))`, `Lit(Int(1))`,
    /// `Let(x)`. Built by `node_label`.
    pub label: String,
    /// The node's [`NodeId`](crate::ccl::provenance::NodeId) as a number — the
    /// handle every pane link and span row names.
    pub node_id: u64,
    /// Every source span this node traces to, narrowest first, empty when it
    /// traces to none.
    ///
    /// A node's attribution records each span that fans into it — `fold` unions
    /// blame spans, so a node several source positions reach carries all of
    /// them. Narrowest first because that is the one a consumer renders when it
    /// wants a single position; a containment scan reads them all. Each distinct
    /// span appears once.
    pub spans: Vec<Span>,
    /// The node's rewrite tag, `None` for a
    /// [`Nature::Source`](crate::ccl::provenance::Nature::Source) tag — the root
    /// of a lowered source expression — and for a node the pane's projection
    /// does not cover. The spans channel of the same attribution rides
    /// [`spans`](Self::spans).
    pub rewritten: Option<RewriteInfo>,
    /// The node's type, rendered by `Display for Type`, so a change to that
    /// rendering changes this verbatim. See
    /// `src/inspector_model/design.md`, "Types on the wire".
    #[serde(rename = "type")]
    pub ty: String,
    /// The node's children by id: the value children in positional order,
    /// then every refinement predicate riding one of its type slots, each
    /// marked [`predicate`](IrChild::predicate).
    pub children: Vec<IrChild>,
}

/// One `{ id, predicate }` child of an [`IrNode`] — an edge into the pane's
/// node table.
///
/// The edge carries no label. Children ship in order — value children under
/// their positional index, then the parent's predicates — so the position in
/// [`children`](IrNode::children) is the label a consumer would read, and
/// [`predicate`](Self::predicate) is what it branches on.
#[derive(Clone, Debug, serde::Serialize)]
pub struct IrChild {
    /// The child node's id — an entry of the same pane's
    /// [`nodes`](PaneEntry::nodes).
    pub id: u64,
    /// Whether the child is a type-interior subtree: `true` for a refinement
    /// predicate, `false` for a value child. See
    /// `src/inspector_model/design.md`, "Predicates are nodes".
    pub predicate: bool,
}

/// A node's rewrite tag — the
/// [`RewriteTag`](crate::ccl::provenance::RewriteTag) of its attribution,
/// rendered for the wire.
#[derive(Clone, Debug, serde::Serialize)]
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
#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct PaneLinkEntry {
    /// The upstream pane id, e.g. `"pre-inference"`.
    pub from: &'static str,
    /// The downstream pane id, e.g. `"post-inference"`.
    pub to: &'static str,
    /// Every edge as `(upstream_node_id, downstream_node_id)`, self-edges
    /// included, sorted deterministically.
    pub edges: Vec<(u64, u64)>,
}

/// `{ name, text }` — the program identity + source.
#[derive(Clone, Debug, serde::Serialize)]
pub struct SourceInfo {
    /// A program name (a placeholder; the server can override it).
    pub name: String,
    /// The full source text.
    pub text: String,
}

/// One `{ useSpan, defSpan, name }` row of `definitions`. The schema's optional
/// `uid` is omitted — resolution is over the source AST, which keys on spans,
/// not uniquify uids.
#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DefinitionEntry {
    /// The use-site span.
    pub use_span: Span,
    /// The binder's source span.
    pub def_span: Span,
    /// The bound name.
    pub name: String,
}

/// A diagnostic entry.
///
/// The web half of the dual-use diagnostics: a [`CompileError`] rendered as
/// structured JSON, the same error the terminal renders via ariadne. Built by
/// [`Diagnostic::from_compile_error`] / [`diagnostics_from_compile_errors`].
///
/// `diagnostics` on [`InspectorPayload`] stays `[]` for *successful* compiles
/// (no warnings); these are produced on the compile-failure path, not by
/// `build_payload`.
///
/// [`CompileError`]: crate::ccl::context::CompileError
#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
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
    ///
    /// One span, not a list: a diagnostic is built from one `CompileError`,
    /// which carries at most one range. Pointing at several ranges with distinct
    /// texts is a different type from this one, and needs a producer that has
    /// those texts.
    pub span: Option<Span>,
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
        Diagnostic {
            severity: "error".to_string(),
            stage: stage.to_string(),
            message,
            span,
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
#[derive(Clone, Debug, serde::Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Meta {
    /// The payload kind discriminant — `"program"` for a successful compile,
    /// `"failed"` for a degraded (compile-error) payload.
    ///
    /// Neither value is a pane id. A pane id names a position in the pipeline;
    /// this names what the document is. Spelling the success case after the
    /// anchor pane would put one word on the wire for two unrelated things, and
    /// a consumer rendering this as a header badge would show the reader a pane
    /// name where the kind belongs.
    pub payload_kind: String,
    /// The wire-format version. A client reads this to detect an incompatible
    /// payload before parsing the rest.
    ///
    /// The current version is [`SCHEMA_VERSION`], whose field set is
    /// [`InspectorPayload`]'s as documented on that type. Each
    /// `panes[].nodes[]` entry carries its attribution as the spans channel on
    /// `spans` plus a `rewritten` tag (`null | { via, nature, label }`).
    ///
    /// **Bump the version** on any *breaking* wire change — a field removed,
    /// renamed, or retyped, or a value-shape change an old client would
    /// misread. Purely *additive* optional fields do **not** bump it (an old
    /// client ignores them). The frontend pins this in its wire-shape contract
    /// test, so a bump is a deliberate, reviewed event on both sides.
    ///
    /// No bump is due yet. Nothing durable consumes this payload — the frontend
    /// is rebuilt from this repo — so the version stays at 1 through any change
    /// until a consumer exists that an old version could reach.
    pub schema: u32,
}

/// Every edge of a pane-pair [`ProvenanceMap`], as `(upstream, downstream)` —
/// **dense**: self-edges (`u == d`, a node preserved across the phase) are kept,
/// so the frontend needs no identity special case.
///
/// An edge's label set stays in `ccl` and does not reach the wire. Upstream the
/// distinction is load-bearing —
/// [`EdgeLabels::has_ancestry`](crate::ccl::provenance::EdgeLabels::has_ancestry)
/// drives leak accounting.
///
/// **Provisional.** Today's consumer resolves links bidirectionally and
/// transitively, so it treats `descends` and `relates` alike and the wire omits
/// the label. A consumer that separates descent from mention wants it; carrying
/// it is an additive field.
///
/// [`ProvenanceMap::edges`] already yields sorted, deduplicated edges, one entry
/// per pair; this only projects to the wire's `u64`.
pub fn dense_edges(map: &ProvenanceMap<NodeId, NodeId>) -> Vec<(u64, u64)> {
    map.edges()
        .into_iter()
        .map(|(u, d)| (u.as_u64(), d.id.as_u64()))
        .collect()
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
/// The operator pane's node table and its roots.
///
/// Nodes come out in the graph's own order, which is conversion order and so
/// deterministic. Attribution is read the same way an expression node's is: the
/// pane's projection is a fold product like any other.
fn build_operator_table(
    graph: &OperatorGraph,
    projection: &SourceProjection,
) -> (Vec<u64>, Vec<OperatorNode>) {
    let nodes = graph
        .nodes()
        .iter()
        .map(|node| {
            let (id, label, role, tiling, inputs) = match node {
                GraphNode::Operator {
                    id,
                    kind,
                    tiling,
                    inputs,
                } => (
                    *id,
                    (*kind).to_string(),
                    "operator",
                    Some(tiling.clone()),
                    inputs.as_slice(),
                ),
                GraphNode::Source { id, name } => (
                    *id,
                    format!("Source({name})"),
                    "source",
                    None,
                    [].as_slice(),
                ),
                GraphNode::Sink { id, name, input } => (
                    *id,
                    format!("Sink({name})"),
                    "sink",
                    None,
                    std::slice::from_ref(input),
                ),
            };
            let attribution = projection.get(&id);
            OperatorNode {
                label,
                node_id: id.as_u64(),
                role,
                tiling,
                spans: attribution
                    .map(|a| wire_spans(&a.spans))
                    .unwrap_or_default(),
                rewritten: attribution.and_then(rewrite_info),
                inputs: inputs.iter().map(wire_edge).collect(),
            }
        })
        .collect();
    (graph.roots().iter().map(|id| id.as_u64()).collect(), nodes)
}

/// The rewrite tag as it ships, or `None` for a
/// [`Nature::Source`](crate::ccl::provenance::Nature::Source) tag — the root of a
/// lowered source expression. The validators guard that `"source"` never ships.
/// An attribution's spans as they ship: **narrowest first**, deduplicated.
///
/// Both node shapes carry this channel on the same terms — see
/// [`IrNode::spans`] and [`OperatorNode::spans`] — so both get it from here.
/// `fold` unions blame spans in encounter order, which is not width order, so
/// the ordering is this function's to establish rather than something the
/// projection already holds. Writing it at each construction site instead left
/// the two shapes to agree by convention, and they did not: the operator table
/// shipped the union order verbatim, so a consumer reading `spans[0]` as the
/// narrowest got the widest.
///
/// The key is `(width, start, end)` rather than width alone, so two spans of
/// equal width order by position and the payload stays byte-reproducible.
fn wire_spans(spans: &[Span]) -> Vec<Span> {
    let mut spans = spans.to_vec();
    spans.sort_by_key(|s| (s.end.saturating_sub(s.start), s.start, s.end));
    spans.dedup();
    spans
}

fn rewrite_info(attr: &crate::ccl::provenance::SourceAttribution) -> Option<RewriteInfo> {
    let tag = &attr.rewritten;
    (!tag.nature.is_source()).then(|| RewriteInfo {
        via: format!("{:?}", tag.via),
        nature: tag.nature.wire_str().to_string(),
        label: tag.label.to_string(),
    })
}

fn wire_edge(edge: &InputEdge) -> OperatorEdge {
    let (kind, deferred) = match edge.kind {
        EdgeKind::Value { deferred } => ("value", deferred),
        EdgeKind::Share => ("share", false),
        EdgeKind::Feedback => ("feedback", false),
    };
    OperatorEdge {
        role: match &edge.role {
            EdgeRole::Named(name) => (*name).to_string(),
            EdgeRole::Positional(i) => i.to_string(),
            EdgeRole::StoreKey(key) => key.clone(),
        },
        kind,
        deferred,
        id: edge.target.as_u64(),
    }
}

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
            spans: Vec::new(),
            rewritten: None,
            ty: expr.ty.to_string(),
            children: Vec::new(),
        };
        if let Some(attr) = projection.get(&id) {
            node.rewritten = rewrite_info(attr);
            node.spans = wire_spans(&attr.spans);
        }

        // The entry claims its pre-order slot before its children are walked, so
        // the array is ordered by first visit rather than by completion.
        let slot = out.len();
        out.push(node);

        let mut children = Vec::new();
        for child in expr.child_exprs() {
            children.push(IrChild {
                id: visit(child, projection, visited, out),
                predicate: false,
            });
        }
        // Predicate subtrees come after the value children, so a value child's
        // index in `children` is its positional index; `predicate` is what marks
        // the rest (see [`predicate_children`]).
        for predicate in predicate_children(expr) {
            children.push(IrChild {
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

impl InspectedProgram<'_> {
    /// Assemble the `/api/snapshot` bulk payload by enumerating the indices.
    ///
    /// `name` is the program name for `source.name` (a placeholder; the server
    /// picks it). Every other field is derived purely from the snapshot:
    ///
    /// * `panes` — the panes in upstream → downstream order: one per declared
    ///   pane in pipeline order, each with its own node table.
    /// * `paneLinks` — per consecutive pane pair, the dense edges of the
    ///   pane-pair `ProvenanceMap` folded at that boundary, self-edges included (see
    ///   [`dense_edges`]).
    /// * `definitions` — [`InspectedProgram::definitions`](super::program::InspectedProgram).
    /// * `diagnostics` — empty.
    /// * `meta` — `payloadKind: "program"`, `schema:` [`SCHEMA_VERSION`].
    pub fn build_payload(&self, name: impl Into<String>) -> InspectorPayload {
        let source = SourceInfo {
            name: name.into(),
            text: self.source_text().to_string(),
        };

        let definitions = self
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
                    name,
                },
            )
            .collect();

        // Build the panes (upstream → downstream) from the bundled pane
        // projections — each ships its own node table.
        let panes = self
            .panes()
            .iter()
            .map(|pane| {
                let (roots, nodes) = match pane.content {
                    PaneContent::Ir(ir) => {
                        let (root, nodes) = build_node_table(ir, &pane.projection);
                        (vec![root], PaneNodes::Ir(nodes))
                    }
                    PaneContent::Operators(graph) => {
                        let (roots, nodes) = build_operator_table(graph, &pane.projection);
                        (roots, PaneNodes::Operators(nodes))
                    }
                };
                PaneEntry {
                    id: pane.id,
                    label: pane.label.clone(),
                    kind: pane.kind,
                    roots,
                    nodes,
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
            diagnostics: Vec::new(),
            meta: Meta {
                payload_kind: "program".to_string(),
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
    /// cannot silently diverge as the schema evolves — the `panes` and
    /// `definitions` collections are empty and `meta.payloadKind` is
    /// `"failed"`. The frontend still renders the editor + squiggles from this.
    ///
    /// TODO(degraded-panes): emit the panes that completed — a program that
    /// fails inference has already built its pre-inference pane, and one that
    /// fails a later phase has that pane and every pane before the failure.
    /// Today every degraded payload ships empty `panes`/`paneLinks` regardless
    /// of where the failure occurred. It needs `compile_program` to hand back
    /// its partial panes rather than one error, so the change is mostly outside
    /// this module; see `src/inspector_model/design.md`, "Diagnostics and the
    /// degraded payload".
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
            diagnostics,
            meta: Meta {
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
            // A join, for the multi-span node. Every other corpus program
            // attributes each node to one span, so the span-ordering and
            // span-uniqueness assertions below ran only over one-element
            // vectors and could not fail. The hash-join planner attributes the
            // operators it builds to both the comprehension and the record
            // inside it, which is the only shape in the tree that reaches
            // `wire_spans` with something to order.
            indoc! {r#"
                us = [(id=1, n="a")]
                os = [(uid=1, amt=5)]
                [(c=u.n, t=o.amt) for u in us for o in os if u.id == o.uid]
            "#},
        ]
    }

    /// Every `nodeId` in one pane's shipped node table, whatever shape the pane
    /// holds.
    fn pane_ids(pane: &PaneEntry) -> HashSet<u64> {
        pane.nodes.ids().into_iter().collect()
    }

    /// Each node's id, label and spans, whatever shape the pane holds. The two
    /// shapes carry the same span channel, so a check over spans covers an
    /// operator pane on the same terms as a tree.
    fn node_rows(pane: &PaneEntry) -> Vec<(u64, &str, &[Span])> {
        match &pane.nodes {
            PaneNodes::Ir(nodes) => nodes
                .iter()
                .map(|n| (n.node_id, n.label.as_str(), n.spans.as_slice()))
                .collect(),
            PaneNodes::Operators(nodes) => nodes
                .iter()
                .map(|n| (n.node_id, n.label.as_str(), n.spans.as_slice()))
                .collect(),
        }
    }

    /// The pane's expression nodes. Panics for an operator pane, which the
    /// callers reach by pane id and so never hand one.
    fn ir_nodes(pane: &PaneEntry) -> &[IrNode] {
        pane.nodes
            .ir()
            .unwrap_or_else(|| panic!("the {} pane holds expression nodes", pane.id))
    }

    /// The pane's node carrying `id`. Panics when no node does, which is the
    /// dangling-child-id failure `every_child_id_resolves_in_its_own_table`
    /// rules out over the whole corpus.
    fn node_with_id(pane: &PaneEntry, id: u64) -> &IrNode {
        ir_nodes(pane)
            .iter()
            .find(|n| n.node_id == id)
            .unwrap_or_else(|| panic!("node {id} is absent from the {} table", pane.id))
    }

    /// The pane's first node labelled `label`.
    fn node_named<'a>(pane: &'a PaneEntry, label: &str) -> &'a IrNode {
        ir_nodes(pane)
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
    /// operationally. The wire validator pins the same set as a literal
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

            // The kind is read off the phases and the pane's content, so
            // exactly the tree panes at or after inference are typed, and it is
            // the discriminant for which shape `nodes` holds.
            assert_eq!(
                payload.panes[0].kind, "holes",
                "the anchor precedes inference"
            );
            for pane in &payload.panes[1..] {
                let expected = match pane.nodes {
                    PaneNodes::Ir(_) => "typed",
                    PaneNodes::Operators(_) => "operators",
                };
                assert_eq!(
                    pane.kind, expected,
                    "the {} pane's kind names the shape it ships",
                    pane.id
                );
            }
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
                for (upstream, downstream) in &link.edges {
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
                }
            }
        }
    }

    /// `wire_spans` establishes the ordering both node shapes promise, over
    /// spans handed to it in any order.
    ///
    /// A unit test rather than a corpus one because the corpus cannot reach the
    /// case: an operator node with more than one span needs a join, and no
    /// program in `corpus()` has one. That gap is why the operator table
    /// shipped `a.spans.clone()` unsorted through every payload the suite
    /// built — `inner_join` and `join_then_groupby` are the only programs in
    /// the tree that expose it, and neither was in a corpus the validators ran
    /// on. Here the shape is stated directly, so the invariant no longer
    /// depends on some program happening to produce it.
    #[test]
    fn wire_spans_orders_narrowest_first_and_dedups() {
        let span = |start: usize, end: usize| Span { start, end };

        // The observed regression: `inner_join`'s operator nodes carried the
        // 99-byte comprehension ahead of the 32-byte record it contains, so
        // `spans[0]` — the one a consumer renders — was the widest.
        assert_eq!(
            wire_spans(&[span(435, 534), span(436, 468)]),
            vec![span(436, 468), span(435, 534)],
        );

        // Already narrowest-first is left alone.
        assert_eq!(
            wire_spans(&[span(436, 468), span(435, 534)]),
            vec![span(436, 468), span(435, 534)],
        );

        // Equal widths order by position, so the payload is byte-reproducible
        // whatever order the union produced. `source_shared`'s one multi-span
        // operator node is this case.
        assert_eq!(
            wire_spans(&[span(348, 355), span(305, 312)]),
            vec![span(305, 312), span(348, 355)],
        );

        // A repeated span is claimed once. The operator table omitted this too.
        assert_eq!(
            wire_spans(&[span(10, 20), span(10, 20), span(1, 2)]),
            vec![span(1, 2), span(10, 20)],
        );

        // Adjacent-after-sort is what `dedup` needs, so a duplicate separated
        // by a narrower span still collapses.
        assert_eq!(
            wire_spans(&[span(10, 20), span(1, 2), span(10, 20)]),
            vec![span(1, 2), span(10, 20)],
        );

        assert_eq!(wire_spans(&[]), vec![]);
    }

    /// A node's `spans` are exactly the spans its pane's projection records for
    /// it, narrowest first and each one once. This is what the retired parallel
    /// span table used to pin as a round trip: with the spans on the node there
    /// is one table to agree with itself, so the check is that the projection and
    /// the wire say the same thing.
    #[test]
    fn a_nodes_spans_are_its_attributions_narrowest_first() {
        for code in corpus() {
            let prog = compile(code);
            let inspected = InspectedProgram::new(&prog);
            let payload = inspected.build_payload("test");
            for (wire_pane, pane) in payload.panes.iter().zip(inspected.panes()) {
                assert_eq!(wire_pane.id, pane.id, "the panes line up");

                // The recorded side is a tree walk, so this covers the IR
                // panes; an operator pane has no tree to walk.
                let (Some(shipped_nodes), Some(ir)) = (wire_pane.nodes.ir(), pane.content.ir())
                else {
                    continue;
                };

                // What the projection records, keyed the way the wire keys it.
                let mut recorded: HashMap<u64, Vec<Span>> = HashMap::new();
                fn collect(
                    expr: &Expr,
                    projection: &SourceProjection,
                    seen: &mut HashSet<u64>,
                    out: &mut HashMap<u64, Vec<Span>>,
                ) {
                    let id = expr.node_id();
                    if !seen.insert(id.as_u64()) {
                        return;
                    }
                    if let Some(attr) = projection.get(&id) {
                        let mut spans = attr.spans.clone();
                        spans.sort_by_key(|s| (s.start, s.end));
                        spans.dedup();
                        out.insert(id.as_u64(), spans);
                    }
                    expr.walk_children(|c| collect(c, projection, seen, out));
                    for predicate in predicate_children(expr) {
                        collect(predicate, projection, seen, out);
                    }
                }
                collect(ir, &pane.projection, &mut HashSet::new(), &mut recorded);

                for node in shipped_nodes {
                    let mut shipped = node.spans.clone();
                    shipped.sort_by_key(|s| (s.start, s.end));
                    assert_eq!(
                        shipped,
                        recorded.get(&node.node_id).cloned().unwrap_or_default(),
                        "{}'s shipped spans are the projection's",
                        node.label
                    );

                    let widths: Vec<usize> = node.spans.iter().map(|s| s.end - s.start).collect();
                    assert!(
                        widths.windows(2).all(|w| w[0] <= w[1]),
                        "{} ships its spans narrowest first; got {:?}",
                        node.label,
                        node.spans
                    );
                }
            }
        }
    }

    /// A shipped node carries the row `src/inspector_model/design.md`, "A node on
    /// the wire" describes: an id, the spans it traces to, a rendered type, no
    /// rewrite tag when its tag is `Nature::Source`, and its children — the
    /// value children first, then every predicate riding one of its type slots,
    /// marked `predicate`.
    #[test]
    fn a_wire_node_carries_its_id_spans_type_and_children() {
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

        for node in ir_nodes(pane) {
            assert!(!node.ty.is_empty(), "{} ships a type", node.label);

            // The value children come first and the predicates follow, so a
            // value child's index in `children` is its positional index and the
            // marked ones are one contiguous tail.
            let positional = node.children.iter().take_while(|c| !c.predicate).count();
            assert!(
                node.children[positional..].iter().all(|c| c.predicate),
                "{}'s predicate children are the tail",
                node.label
            );
        }

        // `x * 2` is the root of a lowered source expression, so its rewrite tag
        // null-compresses; it carries its own span and its inferred type.
        let mul = node_named(pane, "BinOp(Arithmetic(Mul))");
        assert_eq!(mul.spans, [Span::new(24, 29)], "the span of `x * 2`");
        assert_eq!(mul.ty, "Int");
        assert!(
            mul.rewritten.is_none(),
            "a `Nature::Source` tag null-compresses; got {:?}",
            mul.rewritten
        );

        // The comprehension's filter rides the `Cast`'s refined domain, so it
        // hangs off a marked child rather than a value one. One child, not two:
        // the filter sits in the `Cast`'s own type and in its target, and the
        // two slots reach one predicate node.
        let cast = node_named(pane, "Cast");
        let marks: Vec<bool> = cast.children.iter().map(|c| c.predicate).collect();
        assert_eq!(marks, [false, true]);
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

    /// Every child id, every operator input id, and every root of every pane
    /// names a node of that pane's own table. A dangling id is the failure the
    /// node table makes possible and a nested tree could not express.
    #[test]
    fn every_child_id_resolves_in_its_own_table() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");
            for pane in &payload.panes {
                let ids = pane_ids(pane);
                for root in &pane.roots {
                    assert!(
                        ids.contains(root),
                        "the {} root {root} is absent from its own table",
                        pane.id
                    );
                }
                match &pane.nodes {
                    PaneNodes::Ir(nodes) => {
                        assert_eq!(
                            pane.roots.len(),
                            1,
                            "a tree pane has one root; {} names {:?}",
                            pane.id,
                            pane.roots
                        );
                        for node in nodes {
                            for child in &node.children {
                                assert!(
                                    ids.contains(&child.id),
                                    "{}'s child {} of {} is absent from the {} table",
                                    node.label,
                                    child.id,
                                    node.node_id,
                                    pane.id
                                );
                            }
                        }
                    }
                    // An operator's inputs are its edges into the same table.
                    PaneNodes::Operators(nodes) => {
                        for node in nodes {
                            for input in &node.inputs {
                                assert!(
                                    ids.contains(&input.id),
                                    "{}'s {} input {} of {} is absent from the {} table",
                                    node.label,
                                    input.role,
                                    input.id,
                                    node.node_id,
                                    pane.id
                                );
                            }
                        }
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
            // No id repeats, in a pane of either shape.
            for pane in &payload.panes {
                let mut seen = HashSet::new();
                for id in pane.nodes.ids() {
                    assert!(
                        seen.insert(id),
                        "{id} appears twice in the {} table",
                        pane.id
                    );
                }
            }

            // The id set is the pane's tree, neither short nor beyond.
            // `pane_trees` yields the six IR panes, so the zip runs over those.
            for (pane, tree) in payload
                .panes
                .iter()
                .filter(|pane| pane.nodes.ir().is_some())
                .zip(prog.pane_trees())
            {
                let shipped: HashSet<u64> = pane_ids(pane);
                let held: HashSet<u64> =
                    collect_tree_ids(tree).iter().map(|i| i.as_u64()).collect();
                let dropped: Vec<u64> = held.difference(&shipped).copied().collect();
                let invented: Vec<u64> = shipped.difference(&held).copied().collect();
                assert!(
                    dropped.is_empty() && invented.is_empty(),
                    "the {} table drops {dropped:?} and invents {invented:?}",
                    pane.id
                );
            }
        }
    }

    /// No node claims one span twice. A node is visited once and its spans come
    /// from that one attribution, so a repeat would mean the attribution itself
    /// carries a duplicate.
    /// **An operator node's own fields**: `role` says which of the three node
    /// kinds it is, `tiling` is present for an operator and absent for a
    /// boundary, and `spans` is narrowest-first like an expression node's.
    ///
    /// The shape checks elsewhere range over ids and attributions, which both
    /// node kinds share. These are the fields only an operator node has.
    #[test]
    fn an_operator_node_carries_its_role_tiling_and_ordered_spans() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");
            let pane = payload
                .panes
                .last()
                .expect("the operator pane is the last one");
            let PaneNodes::Operators(nodes) = &pane.nodes else {
                panic!("the last pane holds operators");
            };
            assert!(!nodes.is_empty(), "the operator pane has no nodes");
            for node in nodes {
                match node.role {
                    "operator" => assert!(
                        node.tiling.is_some(),
                        "operator {} ships no tiling",
                        node.label
                    ),
                    "source" | "sink" => assert!(
                        node.tiling.is_none(),
                        "boundary node {} ships a tiling, which it has none of",
                        node.label
                    ),
                    other => panic!("unknown operator-node role {other:?} on {}", node.label),
                }
                let widths: Vec<usize> = node.spans.iter().map(|s| s.end - s.start).collect();
                assert!(
                    widths.windows(2).all(|w| w[0] <= w[1]),
                    "{}'s spans are not narrowest-first: {widths:?}",
                    node.label,
                );
            }
        }
    }

    #[test]
    fn no_node_repeats_a_span() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");
            for pane in &payload.panes {
                for (_, label, spans) in node_rows(pane) {
                    let mut seen = HashSet::new();
                    for span in spans {
                        assert!(
                            seen.insert((span.start, span.end)),
                            "{label} in {} repeats span {span:?}",
                            pane.id
                        );
                    }
                }
            }
        }
    }

    /// No node names one predicate twice. `walk_type_slots` yields a `Lambda`'s
    /// own type and its binder's type, which for a lambda are the same `Type`, so
    /// a slot-order walk reaches that type's predicates once per slot; the
    /// repeats named one node and asserted nothing the first edge did not.
    ///
    /// A shared predicate reached from different parents is a different thing
    /// and stays — `a_shared_predicate_is_one_entry_named_by_several_edges` pins
    /// it.
    #[test]
    fn no_node_repeats_a_predicate_edge() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");
            for pane in &payload.panes {
                // A predicate edge rides a type slot, which only a tree node has.
                let Some(nodes) = pane.nodes.ir() else {
                    continue;
                };
                for node in nodes {
                    let mut seen = HashSet::new();
                    for child in node.children.iter().filter(|c| c.predicate) {
                        assert!(
                            seen.insert(child.id),
                            "{} in {} names predicate {} twice",
                            node.label,
                            pane.id,
                            child.id
                        );
                    }
                }
            }
        }
    }

    /// Neither `payloadKind` value is a pane id. The success value was
    /// `"post-inference"`, which is also a pane's id, so one word on the wire
    /// named two unrelated things and a consumer rendering the kind as a header
    /// badge showed the reader a pane name.
    #[test]
    fn a_payload_kind_is_never_a_pane_id() {
        let prog = compile(corpus()[0]);
        let payload = InspectedProgram::new(&prog).build_payload("test");
        assert_eq!(payload.meta.payload_kind, "program");
        let degraded = InspectorPayload::degraded("test", "x = 1", Vec::new());
        assert_eq!(degraded.meta.payload_kind, "failed");
        for kind in [&payload.meta.payload_kind, &degraded.meta.payload_kind] {
            assert!(
                !PANES.iter().any(|spec| spec.name == kind.as_str()),
                "payloadKind {kind:?} is also a pane id"
            );
        }
    }

    /// A predicate several *nodes* reach is one entry in the table, named by an
    /// edge from each of them. This is the repetition the node table removes: the
    /// nested tree emitted the whole subtree once per parent.
    #[test]
    fn a_shared_predicate_is_one_entry_named_by_several_edges() {
        // A refinement minted once and carried through a projection is reached
        // from each node whose type slot holds it.
        let code = corpus()[0];
        let prog = compile(code);
        let payload = InspectedProgram::new(&prog).build_payload("test");
        let pane = payload
            .panes
            .iter()
            .find(|s| s.id == "post-inference")
            .expect("the payload ships the post-inference pane");

        let mut edges: HashMap<u64, usize> = HashMap::new();
        for node in ir_nodes(pane) {
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
            ir_nodes(pane)
                .iter()
                .filter(|n| n.node_id == shared)
                .count(),
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

    /// Every node of every pane carries an attribution, so `spans` and
    /// `rewritten` are absent only where the node is a lowering root — never
    /// because the pane failed to explain the node.
    ///
    /// The wire cannot tell those apart: a node the projection does not cover
    /// ships the same `spans: [], rewritten: null` as a `Nature::Source` root.
    /// This is what keeps the second case from arising, and it is the payload-wide
    /// form of the leak gate's promise that every node of a pane is explained.
    #[test]
    fn every_node_of_every_pane_carries_an_attribution() {
        for code in corpus() {
            let prog = compile(code);
            let payload = InspectedProgram::new(&prog).build_payload("test");
            for pane in &payload.panes {
                let ids = pane_ids(pane);
                let attributed: HashSet<u64> = node_rows(pane)
                    .iter()
                    .filter(|(_, _, spans)| !spans.is_empty())
                    .map(|(id, _, _)| *id)
                    .collect();
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
            edges.iter().any(|(u, d)| u == d),
            "the dense map ships self-edges for nodes preserved across the phase"
        );

        // At least one upstream node fans out to ≥2 distinct downstream nodes
        // (dup used at Int and Bool) — counting only the genuine identity
        // changes, not the self-edges.
        let mut fanout: HashMap<u64, usize> = HashMap::new();
        for (u, d) in &edges {
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
        edges: &[(u64, u64)],
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
        for (u, d) in edges {
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
        for (u, d) in &edges {
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
    // gallery programs (`tests/programs/defer_lift/`, `generator_pipeline/`) but
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
    fn labels_at(payload: &InspectorPayload, pane_id: &str, span: Span) -> Vec<String> {
        let pane = payload
            .panes
            .iter()
            .find(|s| s.id == pane_id)
            .unwrap_or_else(|| panic!("the payload ships a {pane_id} pane"));
        node_rows(pane)
            .iter()
            .filter(|(_, _, spans)| {
                spans
                    .iter()
                    .any(|s| s.start <= span.start && span.end <= s.end)
            })
            .map(|(_, label, _)| (*label).to_string())
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
        let absent: Vec<&str> = ir_nodes(pane)
            .iter()
            .filter(|n| n.spans.is_empty() && n.rewritten.is_none())
            .map(|n| n.label.as_str())
            .collect();
        assert!(
            absent.is_empty(),
            "no defer node is left untagged (absent from projection); got {absent:?}"
        );
    }
}
