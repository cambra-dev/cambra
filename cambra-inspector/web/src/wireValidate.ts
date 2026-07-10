// Runtime validator for the `/api/snapshot` wire shape (schema 2).
//
// The fixtures (and, in production, the fetched payload) are untyped JSON. A
// bare `json as Snapshot` cast gives zero runtime checking, so a backend wire
// drift surfaces only as a confusing downstream crash. `validateSnapshot` walks
// the required keys and types of the Snapshot shape and throws an Error naming
// the failing *path* (e.g. `meta.schema`) on the first violation, then returns
// the value typed as `Snapshot`.
//
// This is the TS twin of the Rust `assert_snapshot_shape`
// (`cambra-inspector/src/lib.rs`) — the two languages pin ONE wire contract:
// schema exactly 2; a successful payload ships the three pipeline stages in
// order with their kinds and the two adjacent stageLinks windows; a degraded
// (`snapshotKind: "failed"`) payload ships empty stages/stageLinks; and every
// node's provenance label stays inside the pinned vocabulary. Extend both
// validators together.

import type {
  InspectEdge,
  InspectNode,
  Snapshot,
  Span,
  SpanIndexEntry,
  StageEntry,
  StageLink,
} from "./types";

class WireError extends Error {
  constructor(path: string, expected: string, got: unknown) {
    super(`snapshot.${path}: expected ${expected}, got ${describe(got)}`);
    this.name = "WireError";
  }
}

/** The wire-format version this frontend speaks (`meta.schema`). */
export const SCHEMA_VERSION = 2;

// The stage contract of a successful schema-2 payload (mirrors the Rust
// assert_snapshot_shape constants).
const STAGE_IDS = ["pre-inference", "post-inference", "post-desugar"] as const;
const STAGE_KINDS = ["holes", "typed", "typed"] as const;
const STAGE_WINDOWS = [
  ["pre-inference", "post-inference"],
  ["post-inference", "post-desugar"],
] as const;

// The observed `Provenance` label vocabulary on the wire: `Source`, or
// `Derived(<via>)`/`Synthetic(<via>)` with `<via>` a pass in this set. Note
// Synthetic(Mono)/Synthetic(Inline) DO occur, not just Synthetic(Desugar).
const ALLOWED_VIA = ["Mono", "Inline", "Desugar"];

function isAllowedProvenance(p: string): boolean {
  if (p === "Source") return true;
  for (const kind of ["Derived(", "Synthetic("]) {
    if (p.startsWith(kind) && p.endsWith(")")) {
      return ALLOWED_VIA.includes(p.slice(kind.length, -1));
    }
  }
  return false;
}

function describe(v: unknown): string {
  if (v === null) return "null";
  if (Array.isArray(v)) return "array";
  return typeof v;
}

function isObject(v: unknown): v is Record<string, unknown> {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}

function obj(v: unknown, path: string): Record<string, unknown> {
  if (!isObject(v)) throw new WireError(path, "object", v);
  return v;
}

function str(v: unknown, path: string): string {
  if (typeof v !== "string") throw new WireError(path, "string", v);
  return v;
}

function num(v: unknown, path: string): number {
  if (typeof v !== "number") throw new WireError(path, "number", v);
  return v;
}

function arr(v: unknown, path: string): unknown[] {
  if (!Array.isArray(v)) throw new WireError(path, "array", v);
  return v;
}

function strOrNull(v: unknown, path: string): string | null {
  if (v !== null && typeof v !== "string") throw new WireError(path, "string|null", v);
  return v as string | null;
}

function numOrNull(v: unknown, path: string): number | null {
  if (v !== null && typeof v !== "number") throw new WireError(path, "number|null", v);
  return v as number | null;
}

function validateSpan(v: unknown, path: string): Span {
  const o = obj(v, path);
  num(o.start, `${path}.start`);
  num(o.end, `${path}.end`);
  return v as Span;
}

function validateSpanOrNull(v: unknown, path: string): Span | null {
  if (v === null) return null;
  return validateSpan(v, path);
}

function validateNode(v: unknown, path: string): InspectNode {
  const o = obj(v, path);
  str(o.label, `${path}.label`);
  // The first-class type field (CCL Display rendering) or null.
  strOrNull(o.type, `${path}.type`);
  const annotations = arr(o.annotations, `${path}.annotations`);
  annotations.forEach((a, i) => str(a, `${path}.annotations[${i}]`));
  num(o.nodeId, `${path}.nodeId`);
  validateSpanOrNull(o.span, `${path}.span`);
  // The provenance label, pinned to the observed vocabulary — a new pass name
  // reaching the wire must be a deliberate, reviewed event on both sides.
  const provenance = strOrNull(o.provenance, `${path}.provenance`);
  if (provenance !== null && !isAllowedProvenance(provenance)) {
    throw new WireError(
      `${path}.provenance`,
      `Source | Derived(via) | Synthetic(via) with via in {${ALLOWED_VIA.join(", ")}}`,
      provenance,
    );
  }
  const children = arr(o.children, `${path}.children`);
  children.forEach((c, i) => validateEdge(c, `${path}.children[${i}]`));
  return v as InspectNode;
}

function validateEdge(v: unknown, path: string): InspectEdge {
  const o = obj(v, path);
  str(o.edge, `${path}.edge`);
  validateNode(o.node, `${path}.node`);
  return v as InspectEdge;
}

function validateNodeOrNull(v: unknown, path: string): InspectNode | null {
  if (v === null) return null;
  return validateNode(v, path);
}

function validateSpanIndex(v: unknown, path: string): SpanIndexEntry[] {
  const entries = arr(v, path);
  entries.forEach((e, i) => {
    const o = obj(e, `${path}[${i}]`);
    validateSpan(o.span, `${path}[${i}].span`);
    num(o.nodeId, `${path}[${i}].nodeId`);
  });
  return v as SpanIndexEntry[];
}

function validateStage(v: unknown, path: string): StageEntry {
  const o = obj(v, path);
  str(o.id, `${path}.id`);
  str(o.label, `${path}.label`);
  str(o.kind, `${path}.kind`);
  validateNodeOrNull(o.ir, `${path}.ir`);
  validateSpanIndex(o.spanIndex, `${path}.spanIndex`);
  return v as StageEntry;
}

function validateStageLink(v: unknown, path: string): StageLink {
  const o = obj(v, path);
  str(o.from, `${path}.from`);
  str(o.to, `${path}.to`);
  const edges = arr(o.edges, `${path}.edges`);
  edges.forEach((pair, i) => {
    const p = arr(pair, `${path}.edges[${i}]`);
    if (p.length !== 2) throw new WireError(`${path}.edges[${i}]`, "a [number, number] pair", pair);
    num(p[0], `${path}.edges[${i}][0]`);
    num(p[1], `${path}.edges[${i}][1]`);
  });
  return v as StageLink;
}

/**
 * Validate an untyped JSON value against the Snapshot wire shape. Throws an
 * Error naming the failing path on the first missing/mistyped required field;
 * returns the value typed as `Snapshot` on success.
 */
export function validateSnapshot(json: unknown): Snapshot {
  const o = obj(json, "");

  const source = obj(o.source, "source");
  str(source.name, "source.name");
  str(source.text, "source.text");

  // Schema 2 retired the top-level `ir`/`spanIndex` aliases. Their *absence*
  // is part of the contract: a payload still carrying them is not the schema
  // this frontend speaks, however the schema number reads.
  if (o.ir !== undefined) throw new WireError("ir", "absent (schema 2)", o.ir);
  if (o.spanIndex !== undefined) {
    throw new WireError("spanIndex", "absent (schema 2)", o.spanIndex);
  }

  const definitions = arr(o.definitions, "definitions");
  definitions.forEach((d, i) => {
    const dd = obj(d, `definitions[${i}]`);
    validateSpan(dd.useSpan, `definitions[${i}].useSpan`);
    validateSpan(dd.defSpan, `definitions[${i}].defSpan`);
    str(dd.name, `definitions[${i}].name`);
  });

  const scopes = arr(o.scopes, "scopes");
  scopes.forEach((s, i) => {
    const sc = obj(s, `scopes[${i}]`);
    validateSpan(sc.span, `scopes[${i}].span`);
    const bindings = arr(sc.bindings, `scopes[${i}].bindings`);
    bindings.forEach((b, j) => {
      const bd = obj(b, `scopes[${i}].bindings[${j}]`);
      str(bd.name, `scopes[${i}].bindings[${j}].name`);
      validateSpan(bd.defSpan, `scopes[${i}].bindings[${j}].defSpan`);
      // Nullable: a binder whose def-span maps to no typed node ships null
      // (Rust `ScopeBindingEntry.ty: Option<Type>`).
      strOrNull(bd.type, `scopes[${i}].bindings[${j}].type`);
    });
  });

  const diagnostics = arr(o.diagnostics, "diagnostics");
  diagnostics.forEach((d, i) => {
    const dg = obj(d, `diagnostics[${i}]`);
    str(dg.severity, `diagnostics[${i}].severity`);
    str(dg.stage, `diagnostics[${i}].stage`);
    str(dg.message, `diagnostics[${i}].message`);
    validateSpanOrNull(dg.span, `diagnostics[${i}].span`);
    const labels = arr(dg.labels, `diagnostics[${i}].labels`);
    labels.forEach((l, j) => {
      const lb = obj(l, `diagnostics[${i}].labels[${j}]`);
      validateSpan(lb.span, `diagnostics[${i}].labels[${j}].span`);
      str(lb.message, `diagnostics[${i}].labels[${j}].message`);
    });
  });

  const meta = obj(o.meta, "meta");
  numOrNull(meta.tick, "meta.tick");
  const snapshotKind = str(meta.snapshotKind, "meta.snapshotKind");
  if (num(meta.schema, "meta.schema") !== SCHEMA_VERSION) {
    throw new WireError("meta.schema", `exactly ${SCHEMA_VERSION}`, meta.schema);
  }

  const stages = arr(o.stages, "stages").map((s, i) => validateStage(s, `stages[${i}]`));
  const stageLinks = arr(o.stageLinks, "stageLinks").map((l, i) =>
    validateStageLink(l, `stageLinks[${i}]`),
  );

  if (snapshotKind === "failed") {
    // Degraded payload: source + diagnostics only, no pipeline stages.
    if (stages.length !== 0) {
      throw new WireError("stages", "empty on a degraded payload", o.stages);
    }
    if (stageLinks.length !== 0) {
      throw new WireError("stageLinks", "empty on a degraded payload", o.stageLinks);
    }
  } else {
    // Successful payload: exactly the three pipeline stages in order, with
    // their kinds, and the two adjacent stageLinks windows.
    const ids = stages.map((s) => s.id);
    if (ids.length !== STAGE_IDS.length || ids.some((id, i) => id !== STAGE_IDS[i])) {
      throw new WireError("stages", `ids [${STAGE_IDS.join(", ")}] in order`, ids);
    }
    const kinds = stages.map((s) => s.kind);
    if (kinds.some((k, i) => k !== STAGE_KINDS[i])) {
      throw new WireError("stages", `kinds [${STAGE_KINDS.join(", ")}]`, kinds);
    }
    const windows = stageLinks.map((l) => [l.from, l.to]);
    if (
      windows.length !== STAGE_WINDOWS.length ||
      windows.some(([f, t], i) => f !== STAGE_WINDOWS[i][0] || t !== STAGE_WINDOWS[i][1])
    ) {
      throw new WireError(
        "stageLinks",
        `the windows ${STAGE_WINDOWS.map(([f, t]) => `${f}>${t}`).join(", ")} in order`,
        windows,
      );
    }
  }

  return json as Snapshot;
}
