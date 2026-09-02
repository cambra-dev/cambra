// Runtime validator for the `/api/snapshot` wire shape.
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
// the schema version below; a successful payload ships the pipeline panes in order with
// their kinds and the adjacent paneLinks windows (dense — self-edges legal,
// every edge endpoint a live node id in its pane); a degraded
// (`payloadKind: "failed"`) payload ships empty panes/paneLinks; each pane's
// node table is closed under its own child edges and `root`; and every node's
// `rewritten` tag stays inside the pinned vocabulary. Extend both validators
// together.
//
// One contract, no relaxations: a committed fixture is a whole payload document,
// so a fixture and a live payload are validated on identical terms.

import type { IrChild, IrNode, PaneEntry, PaneLink, Snapshot, Span } from "./types";

class WireError extends Error {
  constructor(path: string, expected: string, got: unknown) {
    super(`snapshot.${path}: expected ${expected}, got ${describe(got)}`);
    this.name = "WireError";
  }
}

/** The wire-format version this frontend speaks (`meta.schema`). */
export const SCHEMA_VERSION = 1;

// The pane contract of a successful live payload — the single TypeScript-side
// declaration of it, and the cross-language twin of the Rust
// assert_snapshot_shape constants (the two cannot literally share code). A
// slimmed fixture may retain an ordered subset of the stages / windows.
//
// A pin, not a derivation. The producer builds its panes from the compiler's
// PANES table, so reading the payload's own pane list here would make this
// agree with the producer by construction and check nothing. A pane added
// upstream is meant to fail these lists.
export const PANE_IDS = [
  "pre-inference",
  "post-inference",
  "post-channelize",
  "post-as-of-read",
  "post-lambda-elim",
  "post-planning",
] as const;
const PANE_KINDS = ["holes", "typed", "typed", "typed", "typed", "typed"] as const;
const PANE_WINDOWS = [
  ["pre-inference", "post-inference"],
  ["post-inference", "post-channelize"],
  ["post-channelize", "post-as-of-read"],
  ["post-as-of-read", "post-lambda-elim"],
  ["post-lambda-elim", "post-planning"],
] as const;

// The observed rewrite-tag vocabulary on the wire: `rewritten.via` is a phase in
// this set, `rewritten.nature` one of these discriminants. Uniquify is a
// declared phase that records nothing, so it is absent on purpose: this is what
// the wire carries, not what the enum spells. ALLOWED_NATURE deliberately omits
// "source": a direct-image (Nature::Source) tag null-compresses to
// `rewritten: null` on the compiler side, so "source" must never reach the wire
// — validateRewritten guards that boundary explicitly.
const ALLOWED_VIA = [
  "Lower",
  "Infer",
  "Inline",
  "Transact",
  "Letrec",
  "Channelize",
  "AsOfRead",
  "LambdaElim",
  "Planning",
];
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

function validateNode(v: unknown, path: string): IrNode {
  const o = obj(v, path);
  str(o.label, `${path}.label`);
  // Every node has a type, so the field is a string and never null.
  str(o.type, `${path}.type`);
  // `annotations` and `tiling` were tile-producer fields on the renderer's node
  // that the payload never set. `typeKind` and `predicateRefs` rode beside the
  // rendered type for a consumer that read neither. Their absence is part of the
  // contract: a payload still carrying them is not the schema this frontend
  // speaks, however the schema number reads.
  if (o.annotations !== undefined) throw new WireError(`${path}.annotations`, "absent", o.annotations);
  if (o.tiling !== undefined) throw new WireError(`${path}.tiling`, "absent", o.tiling);
  if (o.typeKind !== undefined) throw new WireError(`${path}.typeKind`, "absent", o.typeKind);
  if (o.predicateRefs !== undefined) {
    throw new WireError(`${path}.predicateRefs`, "absent", o.predicateRefs);
  }
  if (o.span !== undefined) throw new WireError(`${path}.span`, "absent", o.span);
  num(o.nodeId, `${path}.nodeId`);
  // Every span the node's attribution records, narrowest first and each once —
  // the table the spatial queries scan.
  const spans = arr(o.spans, `${path}.spans`).map((sp, i) =>
    validateSpan(sp, `${path}.spans[${i}]`),
  );
  let previousExtent = -1;
  const seenSpans = new Set<string>();
  spans.forEach((sp, i) => {
    const key = `${sp.start}:${sp.end}`;
    if (seenSpans.has(key)) {
      throw new WireError(`${path}.spans[${i}]`, "a span not already on this node", sp);
    }
    seenSpans.add(key);
    const extent = sp.end - sp.start;
    if (extent < previousExtent) {
      throw new WireError(`${path}.spans[${i}]`, "spans ordered narrowest first", sp);
    }
    previousExtent = extent;
  });
  // The rewrite tag: null for a lowering root (or an uncovered node), else
  // { via, nature, label } pinned to the observed vocabulary — a new pass name
  // or nature reaching the wire must be a deliberate, reviewed event.
  validateRewritten(o.rewritten, `${path}.rewritten`);
  const children = arr(o.children, `${path}.children`);
  children.forEach((c, i) => validateChild(c, `${path}.children[${i}]`));
  return v as IrNode;
}

function validateChild(v: unknown, path: string): IrChild {
  const o = obj(v, path);
  num(o.id, `${path}.id`);
  if (typeof o.predicate !== "boolean") {
    throw new WireError(`${path}.predicate`, "boolean", o.predicate);
  }
  return v as IrChild;
}

// A pane's node table: `root` and every child id name an entry of this same
// pane's `nodes`, and no id appears twice. The closure check is what the table
// buys over the nested tree it replaced — an edge a consumer follows always
// lands on an entry the pane holds.
function validatePane(v: unknown, path: string): PaneEntry {
  const o = obj(v, path);
  str(o.id, `${path}.id`);
  str(o.label, `${path}.label`);
  str(o.kind, `${path}.kind`);
  if (o.ir !== undefined) throw new WireError(`${path}.ir`, "absent", o.ir);
  // The parallel span table shipped one row per node per span, which is what a
  // node's own `spans` says.
  if (o.spanIndex !== undefined) throw new WireError(`${path}.spanIndex`, "absent", o.spanIndex);
  const root = num(o.root, `${path}.root`);
  const nodes = arr(o.nodes, `${path}.nodes`).map((n, i) =>
    validateNode(n, `${path}.nodes[${i}]`),
  );
  const ids = new Set<number>();
  nodes.forEach((n, i) => {
    if (ids.has(n.nodeId)) {
      throw new WireError(`${path}.nodes[${i}].nodeId`, "an id not already in the table", n.nodeId);
    }
    ids.add(n.nodeId);
  });
  if (!ids.has(root)) {
    throw new WireError(`${path}.root`, "an id present in this pane's nodes", root);
  }
  nodes.forEach((n, i) => {
    // One edge per predicate: a node's type slots overlap, so a slot-order walk
    // upstream reaches a shared predicate once per slot, and a second edge to it
    // asserts nothing the first does.
    const predicateTargets = new Set<number>();
    n.children.forEach((c, j) => {
      if (!ids.has(c.id)) {
        throw new WireError(
          `${path}.nodes[${i}].children[${j}].id`,
          "an id present in this pane's nodes",
          c.id,
        );
      }
      if (c.predicate) {
        if (predicateTargets.has(c.id)) {
          throw new WireError(
            `${path}.nodes[${i}].children[${j}].id`,
            "a predicate not already named by this node",
            c.id,
          );
        }
        predicateTargets.add(c.id);
      }
    });
  });
  return v as PaneEntry;
}

function validateRewritten(v: unknown, path: string): void {
  if (v === null || v === undefined) return;
  const o = obj(v, path);
  const via = str(o.via, `${path}.via`);
  if (!ALLOWED_VIA.includes(via)) {
    throw new WireError(`${path}.via`, `one of {${ALLOWED_VIA.join(", ")}}`, via);
  }
  const nature = str(o.nature, `${path}.nature`);
  // Null-compression guard: a direct image
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
    // A pair, not a triple: the backend's `descends`/`relates` label set stayed
    // there, since resolution here is bidirectional and transitive and treats
    // the two alike.
    if (p.length !== 2)
      throw new WireError(`${path}.edges[${i}]`, "a [number, number] pair", pair);
    num(p[0], `${path}.edges[${i}][0]`);
    num(p[1], `${path}.edges[${i}][1]`);
  });
  return v as PaneLink;
}

// Every `nodeId` of a pane, for pane-link endpoint-liveness checks — the node
// table, read directly.
function collectNodeIds(pane: PaneEntry, out: Set<number>): void {
  for (const n of pane.nodes) out.add(n.nodeId);
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

  // The top-level `ir`/`spanIndex` aliases are retired. Their absence
  // is part of the contract: a payload still carrying them is not the schema
  // this frontend speaks, however the schema number reads.
  if (o.ir !== undefined) throw new WireError("ir", "absent", o.ir);
  if (o.spanIndex !== undefined) {
    throw new WireError("spanIndex", "absent", o.spanIndex);
  }

  const definitions = arr(o.definitions, "definitions");
  definitions.forEach((d, i) => {
    const dd = obj(d, `definitions[${i}]`);
    validateSpan(dd.useSpan, `definitions[${i}].useSpan`);
    validateSpan(dd.defSpan, `definitions[${i}].defSpan`);
    str(dd.name, `definitions[${i}].name`);
  });

  // `scopes` carried a per-region visible-binder list with each binder's type.
  // Nothing here read it, and no channel names a binder site, so the binder
  // types were recovered by search rather than read.
  if (o.scopes !== undefined) throw new WireError("scopes", "absent", o.scopes);

  const diagnostics = arr(o.diagnostics, "diagnostics");
  diagnostics.forEach((d, i) => {
    const dg = obj(d, `diagnostics[${i}]`);
    str(dg.severity, `diagnostics[${i}].severity`);
    str(dg.stage, `diagnostics[${i}].stage`);
    str(dg.message, `diagnostics[${i}].message`);
    validateSpanOrNull(dg.span, `diagnostics[${i}].span`);
    // `labels` held one label repeating `span` and `message`: a diagnostic is
    // built from one `CompileError`, which carries at most one range.
    if (dg.labels !== undefined) {
      throw new WireError(`diagnostics[${i}].labels`, "absent", dg.labels);
    }
  });

  const meta = obj(o.meta, "meta");
  // A `tick` reserved for a live layer that does not exist, like `outline`, is
  // off the wire until something reads it.
  if (meta.tick !== undefined) throw new WireError("meta.tick", "absent", meta.tick);
  const payloadKind = str(meta.payloadKind, "meta.payloadKind");
  // A payload kind names what the document is; a pane id names a position in the
  // pipeline. One word for both put a pane name in the header badge.
  if (payloadKind !== "program" && payloadKind !== "failed") {
    throw new WireError("meta.payloadKind", "`program` or `failed`", payloadKind);
  }
  if (num(meta.schema, "meta.schema") !== SCHEMA_VERSION) {
    throw new WireError("meta.schema", `exactly ${SCHEMA_VERSION}`, meta.schema);
  }

  const panes = arr(o.panes, "panes").map((s, i) => validatePane(s, `panes[${i}]`));
  // Always present, empty on a degraded payload: no payload omits the field.
  if (o.paneLinks === undefined) {
    throw new WireError("paneLinks", "present (every payload ships it)", o.paneLinks);
  }
  const paneLinks: PaneLink[] = arr(o.paneLinks, "paneLinks").map((l, i) =>
    validatePaneLink(l, `paneLinks[${i}]`),
  );

  if (payloadKind === "failed") {
    // Degraded payload: source + diagnostics only, no pipeline panes.
    if (panes.length !== 0) {
      throw new WireError("panes", "empty on a degraded payload", o.panes);
    }
    if (paneLinks.length !== 0) {
      throw new WireError("paneLinks", "empty on a degraded payload", o.paneLinks);
    }
  } else {
    // Successful payload: exactly the pipeline panes in order with their kinds,
    // and the adjacent paneLinks windows.
    const ids = panes.map((s) => s.id);
    if (ids.length !== PANE_IDS.length || !ids.every((id, i) => id === PANE_IDS[i])) {
      throw new WireError("panes", `ids [${PANE_IDS.join(", ")}] in order`, ids);
    }
    // Each pane carries the kind its id mandates.
    const kindById = new Map<string, string>(PANE_IDS.map((id, i) => [id, PANE_KINDS[i]]));
    panes.forEach((s) => {
      if (s.kind !== kindById.get(s.id)) {
        throw new WireError(`panes (${s.id}).kind`, `${kindById.get(s.id)}`, s.kind);
      }
    });
    const windows: string[][] = paneLinks.map((l) => [l.from, l.to]);
    const windowsOk =
      windows.length === PANE_WINDOWS.length &&
      windows.every(([f, t], i) => f === PANE_WINDOWS[i][0] && t === PANE_WINDOWS[i][1]);
    if (!windowsOk) {
      throw new WireError(
        "paneLinks",
        `the windows ${PANE_WINDOWS.map(([f, t]) => `${f}>${t}`).join(", ")} in order`,
        windows,
      );
    }

    // Dense edges: self-edges (u === d) are legal, but every endpoint must be a
    // live node id in its respective pane.
    const idsByPane = new Map<string, Set<number>>();
    for (const s of panes) {
      const set = new Set<number>();
      collectNodeIds(s, set);
      idsByPane.set(s.id, set);
    }
    paneLinks.forEach((link, i) => {
      const up = idsByPane.get(link.from);
      const down = idsByPane.get(link.to);
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
