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

// One input edge of an operator node.
//
// A *construction* edge — which operator holds which, and how. Runtime dataflow
// follows a different relation, and nothing here asserts the two coincide.
export interface OperatorEdge {
  // What names this input at its consumer: a field name, a position, or a store
  // key, rendered.
  role: string;
  // "value" for an exclusively owned input, "share" for one several consumers
  // may reach, "feedback" for a share that closes a cycle.
  //
  // The value edges form a forest, which is what lets a renderer walk them as a
  // child relation with no cycle guard; share and feedback are the
  // cross-references.
  kind: string;
  // Whether the edge was wired after its consumer was constructed. An attribute
  // of when, not of ownership.
  deferred: boolean;
  // The input's node id.
  id: number;
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
  // The ids a consumer starts walking `nodes` from — each an entry of `nodes`.
  //
  // One for a tree. An operator graph has several: a sink per compiled output,
  // and a fan input per share point, which are the nodes nothing owns.
  roots: number[];
}

// A pane holding an expression tree: "holes" for the still-hole-typed
// pre-inference tree, "typed" for a fully typed one (every tree pane from
// post-inference on).
export interface IrPane extends PaneCommon {
  kind: "holes" | "typed";
  // Every node of this pane exactly once, in first-visit pre-order.
  nodes: IrNode[];
}

// The pane holding the dataflow operator graph.
export interface OperatorPane extends PaneCommon {
  kind: "operators";
  // Every node of this pane exactly once, in conversion order.
  nodes: OperatorNode[];
}

// One ordered pipeline pane. `kind` is the discriminant for which shape `nodes`
// holds: the two share an id, a label and an attribution, and nothing else — an
// expression node has a type and children, an operator has a tiling and typed
// input edges, and neither field set is meaningful for the other.
export type PaneEntry = IrPane | OperatorPane;

/**
 * Narrow a pane to the tree-shaped panes. The one place the `kind` discriminant
 * is read as a predicate, so a caller that needs `IrNode`s — a tree walk, a
 * type query — states that need once rather than re-spelling the kind set.
 */
export function isIrPane(pane: PaneEntry): pane is IrPane {
  return pane.kind !== "operators";
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
