// Runtime validator for the `/api/snapshot` wire shape (schema 4).
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
// schema exactly 4; a successful payload ships the three pipeline stages in
// order with their kinds (no per-stage `spanIndex` — schema 4 rebuilds it
// client-side) and the two adjacent paneLinks windows (dense — self-edges
// legal, every edge endpoint a live node id in its pane); a degraded
// (`snapshotKind: "failed"`) payload ships empty stages/paneLinks; and every
// node's `rewritten` tag stays inside the pinned vocabulary. Extend both
// validators together.
//
// The `fixtureSlimming` option (mirroring Rust's `FixtureContext::Fixture`)
// relaxes the contract for a committed golden fixture ONLY: panes may be a
// non-empty ordered subset and `paneLinks` may be omitted entirely (elided for
// slimming). It never loosens the live path — production callers pass no options
// and get the full contract, so a live payload that drops a pane or paneLinks
// still fails.

import type { InspectEdge, InspectNode, PaneLink, Snapshot, Span, StageEntry } from "./types";

class WireError extends Error {
  constructor(path: string, expected: string, got: unknown) {
    super(`snapshot.${path}: expected ${expected}, got ${describe(got)}`);
    this.name = "WireError";
  }
}

/** The wire-format version this frontend speaks (`meta.schema`). */
export const SCHEMA_VERSION = 4;

/** Options for {@link validateSnapshot}. */
export interface ValidateOptions {
  /**
   * Validate a committed golden fixture, which may be slimmed: a non-empty
   * ordered pane subset, and `paneLinks` omitted entirely (elided for the
   * fixture corpus). NEVER pass this for a live payload — the live wire always
   * ships every pane and its links, and slimming only relaxes the fixture path.
   */
  fixtureSlimming?: boolean;
}

// The stage contract of a successful live payload (mirrors the Rust
// assert_snapshot_shape constants). A slimmed fixture may retain an ordered
// subset of the stages / windows.
const STAGE_IDS = ["pre-inference", "post-inference", "post-desugar"] as const;
const STAGE_KINDS = ["holes", "typed", "typed"] as const;
const STAGE_WINDOWS = [
  ["pre-inference", "post-inference"],
  ["post-inference", "post-desugar"],
] as const;

// The observed rewrite-tag vocabulary on the wire: `rewritten.via` is a pass in
// this set, `rewritten.nature` one of these discriminants. ALLOWED_NATURE
// deliberately omits "source": a direct-image (Nature::Source) tag
// null-compresses to `rewritten: null` on the compiler side, so "source" must
// never reach the wire — validateRewritten guards that boundary explicitly.
const ALLOWED_VIA = ["Lower", "Mono", "Inline", "Transact", "Letrec", "Desugar"];
const ALLOWED_NATURE = ["expansion", "machinery"];

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
  // The rewrite tag (schema 3): null for a directly-lowered source node, else
  // { via, nature, label } pinned to the observed vocabulary — a new pass name
  // or nature reaching the wire must be a deliberate, reviewed event.
  validateRewritten(o.rewritten, `${path}.rewritten`);
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

function validateStage(v: unknown, path: string): StageEntry {
  const o = obj(v, path);
  str(o.id, `${path}.id`);
  str(o.label, `${path}.label`);
  str(o.kind, `${path}.kind`);
  validateNodeOrNull(o.ir, `${path}.ir`);
  // Schema 4 dropped the per-stage span index (rebuilt client-side from `ir`).
  // Its *absence* is part of the contract — a payload still shipping it is not
  // the schema this frontend speaks.
  if (o.spanIndex !== undefined) {
    throw new WireError(`${path}.spanIndex`, "absent (schema 4 rebuilds it client-side)", o.spanIndex);
  }
  return v as StageEntry;
}

function validateRewritten(v: unknown, path: string): void {
  if (v === null || v === undefined) return;
  const o = obj(v, path);
  const via = str(o.via, `${path}.via`);
  if (!ALLOWED_VIA.includes(via)) {
    throw new WireError(`${path}.via`, `one of {${ALLOWED_VIA.join(", ")}}`, via);
  }
  const nature = str(o.nature, `${path}.nature`);
  // Null-compression guard (lineage-redesign §2.14): a direct image
  // (Nature::Source) ships as `rewritten: null`, never as a "source" tag. If
  // this fires, the compiler-side null-compression rotted.
  if (nature === "source") {
    throw new WireError(
      `${path}.nature`,
      "not \"source\" (a direct image must null-compress to rewritten: null)",
      nature,
    );
  }
  if (!ALLOWED_NATURE.includes(nature)) {
    throw new WireError(`${path}.nature`, `one of {${ALLOWED_NATURE.join(", ")}}`, nature);
  }
  const label = str(o.label, `${path}.label`);
  if (label.length === 0) throw new WireError(`${path}.label`, "a non-empty string", label);
}

function validatePaneLink(v: unknown, path: string): PaneLink {
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
  return v as PaneLink;
}

// Every `nodeId` in a stage's IR tree, for pane-link endpoint-liveness checks.
function collectNodeIds(node: InspectNode | null, out: Set<number>): void {
  if (!node) return;
  out.add(node.nodeId);
  for (const c of node.children) collectNodeIds(c.node, out);
}

/** Is `sub` a subsequence of `full` (same relative order, gaps allowed)? */
function isOrderedSubsequence<T>(sub: T[], full: readonly T[], eq: (a: T, b: T) => boolean): boolean {
  let i = 0;
  for (const x of sub) {
    while (i < full.length && !eq(x, full[i])) i++;
    if (i === full.length) return false;
    i++;
  }
  return true;
}

/**
 * Validate an untyped JSON value against the Snapshot wire shape. Throws an
 * Error naming the failing path on the first missing/mistyped required field;
 * returns the value typed as `Snapshot` on success.
 *
 * Pass `{ fixtureSlimming: true }` ONLY when validating a committed golden
 * fixture (see {@link ValidateOptions}); production callers omit it and get the
 * strict live contract.
 */
export function validateSnapshot(json: unknown, options: ValidateOptions = {}): Snapshot {
  const slimming = options.fixtureSlimming === true;
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
  // A slimmed fixture may OMIT paneLinks entirely (elided). Absent is accepted
  // only under fixtureSlimming; the live wire always ships the (possibly empty)
  // array.
  const paneLinksRaw = o.paneLinks;
  if (paneLinksRaw === undefined) {
    if (!slimming) {
      throw new WireError("paneLinks", "present (the live wire always ships it)", paneLinksRaw);
    }
  }
  const paneLinks: PaneLink[] =
    paneLinksRaw === undefined
      ? []
      : arr(paneLinksRaw, "paneLinks").map((l, i) => validatePaneLink(l, `paneLinks[${i}]`));

  if (snapshotKind === "failed") {
    // Degraded payload: source + diagnostics only, no pipeline stages.
    if (stages.length !== 0) {
      throw new WireError("stages", "empty on a degraded payload", o.stages);
    }
    if (paneLinks.length !== 0) {
      throw new WireError("paneLinks", "empty on a degraded payload", o.paneLinks);
    }
  } else {
    // Successful payload. Live: exactly the three pipeline stages in order with
    // their kinds, and the two adjacent paneLinks windows. Fixture slimming:
    // panes may be a non-empty ordered subset and paneLinks a subset (or absent).
    const ids = stages.map((s) => s.id);
    const idsOk = slimming
      ? ids.length > 0 && isOrderedSubsequence(ids, STAGE_IDS, (a, b) => a === b)
      : ids.length === STAGE_IDS.length && ids.every((id, i) => id === STAGE_IDS[i]);
    if (!idsOk) {
      throw new WireError(
        "stages",
        slimming
          ? `a non-empty subset of [${STAGE_IDS.join(", ")}] in order`
          : `ids [${STAGE_IDS.join(", ")}] in order`,
        ids,
      );
    }
    // Each retained stage carries the kind its id mandates (subset-safe).
    const kindById = new Map<string, string>(STAGE_IDS.map((id, i) => [id, STAGE_KINDS[i]]));
    stages.forEach((s) => {
      if (s.kind !== kindById.get(s.id)) {
        throw new WireError(`stages (${s.id}).kind`, `${kindById.get(s.id)}`, s.kind);
      }
    });
    const windows: string[][] = paneLinks.map((l) => [l.from, l.to]);
    const eqWin = (a: readonly string[], b: readonly string[]): boolean =>
      a[0] === b[0] && a[1] === b[1];
    const windowsOk = slimming
      ? isOrderedSubsequence<readonly string[]>(
          windows,
          STAGE_WINDOWS as readonly (readonly string[])[],
          eqWin,
        )
      : windows.length === STAGE_WINDOWS.length &&
        windows.every(([f, t], i) => f === STAGE_WINDOWS[i][0] && t === STAGE_WINDOWS[i][1]);
    if (!windowsOk) {
      throw new WireError(
        "paneLinks",
        `the windows ${STAGE_WINDOWS.map(([f, t]) => `${f}>${t}`).join(", ")}${
          slimming ? " (subset, in order)" : " in order"
        }`,
        windows,
      );
    }

    // Dense edges: self-edges (u === d) are legal, but every endpoint must be a
    // live node id in its respective pane.
    const idsByStage = new Map<string, Set<number>>();
    for (const s of stages) {
      const set = new Set<number>();
      collectNodeIds(s.ir, set);
      idsByStage.set(s.id, set);
    }
    paneLinks.forEach((link, i) => {
      const up = idsByStage.get(link.from);
      const down = idsByStage.get(link.to);
      link.edges.forEach(([u, d], j) => {
        if (!up?.has(u)) {
          throw new WireError(`paneLinks[${i}].edges[${j}][0]`, `a live node in ${link.from}`, u);
        }
        if (!down?.has(d)) {
          throw new WireError(`paneLinks[${i}].edges[${j}][1]`, `a live node in ${link.to}`, d);
        }
      });
    });
  }

  return json as Snapshot;
}
