// Wire types mirroring the `/api/snapshot` JSON — the shapes
// `cambra::inspector_model` serializes (`src/inspector_model/design.md`, "A pane
// on the wire"). These are the *transport* shapes; the frontend is read-only and
// never constructs them, so they are kept deliberately loose where the backend
// allows null (degraded payloads).

export interface Span {
  start: number;
  end: number;
}

export interface Source {
  name: string;
  text: string;
}

// One edge out of an `IrNode`, naming a node of the *same* pane's table.
//
// The edge carries no label. Children arrive in order — the value children,
// then the parent's refinement predicates — so a value child's index in
// `children` is its positional index, and `treeView` derives the row prefix it
// draws from that rather than from a shipped string.
export interface IrChild {
  // The child's `nodeId`, an entry of the same pane's `nodes`.
  id: number;
  // Whether the child is a type-interior subtree (a refinement predicate) rather
  // than a value child.
  //
  // Predicates are on the wire because the compiler's pane fold explains their
  // node ids, so a link can point at one; they are *not* part of the program's
  // value tree, so a query about a value ("what does this hole resolve to", "the
  // `Lit(Int(1))` node") must not wander into them. Every traversal that means
  // "the program" filters on this flag.
  predicate: boolean;
}

// A node's rewrite tag: how a phase produced this node. `null` on an `IrNode`
// means the node is a lowering root, or that the pane's projection does not
// cover it — the wire cannot tell the two apart. The spans channel of the same
// attribution rides the `span` field.
export interface RewriteInfo {
  // The phase that produced the node (the `Phase` debug name, e.g. "Infer").
  via: string;
  // "expansion" (faithful expansion of a user construct) or "machinery" (pure
  // plumbing) — the lowercase Nature discriminant.
  nature: string;
  // The rewrite's stable label, e.g. "channelize.feed_union".
  label: string;
}

// One entry of a pane's node table. Every node of the pane appears exactly once;
// a node reached from several places — a refinement predicate shared by several
// type slots — is one entry that several `IrChild`s name.
export interface IrNode {
  label: string;
  nodeId: number;
  // Every source span this node traces to, narrowest first, empty when it
  // traces to none. The narrowest is first so a caller wanting one position
  // takes `spans[0]`; a containment scan reads them all.
  spans: Span[];
  // The native rewrite tag, or null (see `RewriteInfo`).
  rewritten: RewriteInfo | null;
  // The node's type as CCL's canonical `Display` rendering (e.g. `"Int"`,
  // `"(Int ⇒ Int)"`, hole `"_"`). Every node has a type, so this is never null.
  type: string;
  children: IrChild[];
}

// One node of an operator pane: an operator, or one of the two program
// boundaries.
export interface OperatorNode {
  // What to show: the operator's type name, or `Source(name)` / `Sink(name)`
  // for a boundary.
  label: string;
  // The node's `NodeId`, in the same space as an expression node's — an
  // operator carries a `NodeId` so a pane pair spanning conversion is
  // homogeneous like every other.
  nodeId: number;
  // Which of the three node kinds this is: "operator", "source", "sink". Data,
  // not display policy.
  role: string;
  // The operator's output tiling, rendered, and null for a boundary node.
  tiling: string | null;
  // Every source span this node traces to, narrowest first. Same channel and
  // same meaning as `IrNode.spans`.
  spans: Span[];
  // The node's rewrite tag, on the same terms as `IrNode.rewritten`.
  rewritten: RewriteInfo | null;
  // The graph inputs this node holds.
  inputs: OperatorEdge[];
}

// What names an input at its consumer, carrying the shape that named it. A
// field called `0` and the first element of a `Vec` render alike, so the wire
// keeps the shape rather than flattening both to a string.
export type OperatorEdgeRole =
  | { kind: "named"; name: string }
  | { kind: "positional"; index: number }
  | { kind: "storeKey"; key: string };

// How a role reads in a row label.
export function roleLabel(role: OperatorEdgeRole): string {
  switch (role.kind) {
    case "named":
      return role.name;
    case "positional":
      return String(role.index);
    case "storeKey":
      return role.key;
  }
}

// One input edge of an operator node.
//
// A *construction* edge — which operator holds which, and how. Runtime dataflow
// follows a different relation, and nothing here asserts the two coincide.
export interface OperatorEdge {
  // What names this input at its consumer.
  role: OperatorEdgeRole;
  // "value" for an exclusively owned input, "share" for one several consumers
  // may reach.
  //
  // The value edges form a forest, which is what lets a renderer walk them as a
  // child relation with no cycle guard; the share edges are the
  // cross-references. A cycle is a "value" edge with `deferred` set.
  kind: string;
  // Whether the edge was wired after its consumer was constructed. An attribute
  // of when, not of ownership.
  deferred: boolean;
  // The id of the node this edge subscribes — an entry of the same pane's
  // `nodes`.
  subscribed: number;
}

export interface Definition {
  useSpan: Span;
  defSpan: Span;
  name: string;
}

export interface Diagnostic {
  severity: string;
  // The compiler stage that raised it — "parse", "lower", "infer", … These are
  // `CompileError` variants, not pane ids.
  stage: string;
  message: string;
  // The one range a consumer underlines. A diagnostic is built from one
  // `CompileError`, which carries at most one range.
  span: Span | null;
}

export interface Meta {
  // Which payload this is: "program" for a successful compile, "failed" for the
  // degraded one. Never a pane id.
  payloadKind: string;
  schema: number;
}

// What every pane carries, whichever shape its node table holds. Each pane is
// one position in the pipeline (upstream -> downstream) and resolves against its
// own (Expr, SourceProjection) projection on the backend.
interface PaneCommon {
  id: string;
  label: string;
}

// A pane holding an expression tree: "holes" for the still-hole-typed
// pre-inference tree, "typed" for a fully typed one (every tree pane from
// post-inference on).
export interface IrPane extends PaneCommon {
  kind: "holes" | "typed";
  // The root node of this pane's expression, shipped by the producer. Not a
  // derived walk start: the operator pane's starts are read off its edges, this
  // is the tree the pane is.
  root: number;
  // Every node of this pane exactly once, in first-visit pre-order.
  nodes: IrNode[];
}

// The pane holding the dataflow operator graph.
export interface OperatorPane extends PaneCommon {
  kind: "operators";
  // A graph names no walk start. The nodes no `value` edge subscribes are where
  // a walk begins — a sink per compiled output, a fan input per share point, a
  // source per registered data source — and the `inputs` already say which those
  // are, so a consumer derives them. `wireValidate.ts` pins that they reach the
  // whole table.
  //
  // Every node of this pane exactly once, in conversion order.
  nodes: OperatorNode[];
}

// One ordered pipeline pane. `kind` is the discriminant for which shape `nodes`
// holds: the two share an id and a label and nothing else — a tree pane names
// one `root` and its nodes have a type and children, an operator pane names no
// start and its nodes have a tiling and typed input edges, and neither field set
// is meaningful for the other.
export type PaneEntry = IrPane | OperatorPane;

/**
 * Narrow a pane to the tree-shaped panes. The one place the `kind` discriminant
 * is read as a predicate, so a caller that needs `IrNode`s — a tree walk, a
 * type query — states that need once rather than re-spelling the kind set.
 */
export function isIrPane(pane: PaneEntry): pane is IrPane {
  return pane.kind !== "operators";
}

/**
 * An edge the child relation follows, as against one a view renders as a
 * reference.
 */
export function isChildEdge(edge: OperatorEdge): boolean {
  return edge.kind === "value";
}

/**
 * The nodes no value edge subscribes, in table order — where each tree of the
 * operator forest starts.
 *
 * Derived rather than shipped: a node's owner is the one value edge naming it,
 * so the table already answers this, and a shipped copy could only disagree.
 * Both the renderer and the validator read it here, so the derivation the
 * validator pins is the one the renderer walks.
 */
export function walkStarts(nodes: readonly OperatorNode[]): number[] {
  const subscribed = new Set(
    nodes.flatMap((n) => n.inputs.filter(isChildEdge).map((e) => e.subscribed)),
  );
  return nodes.map((n) => n.nodeId).filter((id) => !subscribed.has(id));
}

// The dense node->node links between two adjacent panes — each adjacent pane
// pair's ProvenanceMap shipped verbatim. A node preserved unchanged across the
// phase appears as its own `[id, id]` self-edge, so the client follows edges
// only (no identity special case); genuine identity changes (fan-out) are the
// `u !== d` edges.
/** One dense pane-pair edge: upstream id, downstream id. */
export type PaneEdge = [number, number];

export interface PaneLink {
  from: string;
  to: string;
  // `[upstreamNodeId, downstreamNodeId]` pairs, self-edges included. The
  // backend's `descends`/`relates` distinction stays there: resolution here is
  // bidirectional and transitive, which treats the two alike.
  edges: PaneEdge[];
}

// The payload drives entirely off `panes`/`paneLinks`. Both arrays are always
// present — empty on the degraded (failed-compile) payload.
export interface Snapshot {
  source: Source;
  definitions: Definition[];
  diagnostics: Diagnostic[];
  meta: Meta;
  panes: PaneEntry[];
  paneLinks: PaneLink[];
}

// ---------------------------------------------------------------------------
// The live wire — `/api/live`
// ---------------------------------------------------------------------------
//
// A frame is whole state, not an append. Each one carries every producer that
// produced during its tick, and replaces the frame before it; the server has
// already collapsed each producer's several `get`s within the tick to one
// answer (`ValueRecorder::latest_non_empty`). The frontend keeps a per-node
// cache so a newly pinned operator answers from the last frame rather than
// waiting for the next one, which on a converged program never comes.

// One row of a recorded tile or a source's retained window.
export interface LiveRow {
  // The domain key this row sits at, or `null` for a shape whose positions are
  // implicit (a `Scalar` has no domain).
  key: string | null;
  // The value, already rendered by the backend through `Display for Value`.
  value: string;
  // Whether the tile marks this position deleted. Carried rather than filtered:
  // a `Restrict` marks a row while the `Memo` below it has compacted the same
  // row away, so dropping the flag makes two producers look alike where they
  // differ.
  deleted: boolean;
}

// One producer's answer for a tick. An operator can have several, because a
// `FanOut` branch is subscribed once per branch.
export interface LiveProducer {
  producerId: number;
  // The producer's display name, e.g. `"MapResultWithSource#1"`.
  producer: string;
  // The tile's variant name, e.g. `"SealedFunction"`.
  shape: string;
  // The tile's `domain_predicate`, rendered: `False`, then `LessThanEq(uN)`,
  // then `True`. `null` for a shape carrying no such region.
  watermark: string | null;
  // Why this answer carries no rows, for a shape the backend does not render.
  note: string | null;
  // The tick this answer came from, which is not the frame's tick when the
  // producer has since produced nothing.
  tick: number;
  seq: number;
  // Whether a newer answer for this producer carried nothing.
  stale: boolean;
  // Rows the tile held, of which `rows` is the last `rows.length`.
  total: number;
  dropped: number;
  rows: LiveRow[];
}

// Every producer built by one operator. Nodes arrive in ascending `nodeId`,
// which is construction order, so upstream sorts first.
export interface LiveNode {
  nodeId: number;
  producers: LiveProducer[];
}

// A data source's retained window: what has arrived and not yet been released
// by every reader. Not a recording — a source has no producer and takes no
// `get`, so this is read through `&self` and sampling it releases nothing.
export interface LiveSource {
  // The source's own node in the operator graph, which is what a click on it
  // resolves to. `null` when the graph carries no node for it.
  nodeId: number | null;
  // The registered name, e.g. `"stdin"`.
  name: string;
  total: number;
  dropped: number;
  rows: LiveRow[];
}

export interface LiveFrame {
  // The driver tick this frame reports. Advances only over a tick that recorded
  // something, so it counts data rather than loop iterations.
  tick: number;
  // Frames published so far, so a client can tell it is behind.
  published: number;
  // Whether the run is over and this frame is the last. A reader that never
  // sees one and then loses the socket was disconnected; a reader holding one
  // knows the quiet is the end rather than a pause.
  final: boolean;
  nodes: LiveNode[];
  sources: LiveSource[];
}
