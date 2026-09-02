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

// One ordered pipeline pane (upstream -> downstream). Each pane carries its own
// self-contained node table; it resolves against its own
// (Expr, SourceProjection) projection on the backend.
export interface PaneEntry {
  id: string;
  label: string;
  // "holes" (the still-hole-typed pre-inference tree) or "typed" (a fully
  // typed tree — every pane from post-inference on).
  kind: string;
  // The id of the node the pane's walk starts from — an entry of `nodes`.
  root: number;
  // Every node of this pane exactly once, in first-visit pre-order.
  nodes: IrNode[];
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
