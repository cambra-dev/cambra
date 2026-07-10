// Wire types mirroring the `/api/snapshot` JSON (cambra-inspector I3 serde
// shapes). These are the *transport* shapes; the frontend is read-only and
// never constructs them, so they are kept deliberately loose where the backend
// allows null (degraded snapshots).

export interface Span {
  start: number;
  end: number;
}

export interface Source {
  name: string;
  text: string;
}

export interface InspectEdge {
  edge: string;
  node: InspectNode;
}

export interface InspectNode {
  label: string;
  // The node's type as CCL's canonical `Display` rendering (e.g. `"Int"`,
  // `"(Int ⇒ Int)"`, hole `"_"`), or null if untyped. IR nodes carry their type
  // here as a first-class field; `annotations` is now usually empty (other,
  // non-type annotations only).
  type: string | null;
  annotations: string[];
  nodeId: number;
  span: Span | null;
  provenance: string | null;
  tiling: unknown | null;
  children: InspectEdge[];
}

export interface SpanIndexEntry {
  span: Span;
  nodeId: number;
}

export interface Definition {
  useSpan: Span;
  defSpan: Span;
  name: string;
}

export interface ScopeBinding {
  name: string;
  defSpan: Span;
  // Null when the binder's def-span maps to no typed node (Rust
  // `ScopeBindingEntry.ty: Option<Type>`) — e.g. a substituted multi-param
  // parameter, or a `Mut`-store binder erased before the anchor stage.
  type: string | null;
}

export interface Scope {
  span: Span;
  bindings: ScopeBinding[];
}

export interface DiagnosticLabel {
  span: Span;
  message: string;
}

export interface Diagnostic {
  severity: string;
  stage: string;
  message: string;
  span: Span | null;
  labels: DiagnosticLabel[];
}

export interface Meta {
  tick: number | null;
  snapshotKind: string;
  schema: number;
}

// One ordered pipeline stage (upstream -> downstream). Each stage carries its
// own self-contained IR tree and span index; it resolves against its own
// (Expr, ProvenanceTable) projection on the backend (B2/B4).
export interface StageEntry {
  id: string;
  label: string;
  // "holes" (the still-hole-typed pre-inference tree) or "typed" (a fully
  // typed tree — post-inference and post-desugar both).
  kind: string;
  ir: InspectNode | null;
  spanIndex: SpanIndexEntry[];
}

// The non-identity node->node links between two adjacent stages. Identity edges
// (same NodeId in both trees) are NOT carried — the client resolves them as
// "the same id in each pane"; only fan-out/wrapper overrides ship here.
export interface StageLink {
  from: string;
  to: string;
  // `[upstreamNodeId, downstreamNodeId]` pairs.
  edges: [number, number][];
}

// Schema 2: the multi-pane payload drives entirely off `stages`/`stageLinks`
// (the schema-1 top-level `ir`/`spanIndex` aliases are gone). Both arrays are
// always present — empty on the degraded (failed-compile) payload.
export interface Snapshot {
  source: Source;
  definitions: Definition[];
  scopes: Scope[];
  diagnostics: Diagnostic[];
  meta: Meta;
  stages: StageEntry[];
  stageLinks: StageLink[];
}
