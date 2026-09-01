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
// node table is closed under its own `roots` and its own edges — child edges
// for a tree pane, operator inputs for the operator pane; and every node's
// `rewritten` tag stays inside the pinned vocabulary. Extend both validators
// together.
//
// One contract, no relaxations: a committed fixture is a whole payload document,
// so a fixture and a live payload are validated on identical terms.

import type {
  IrChild,
  IrNode,
  OperatorEdge,
  OperatorNode,
  PaneEntry,
  PaneLink,
  Snapshot,
  Span,
} from "./types";

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
  "post-conversion",
] as const;
// The `kind` each pane id mandates, aligned with `PANE_IDS`. It is also the
// node-shape discriminant: a "holes" or "typed" pane holds IR nodes, an
// "operators" pane holds operator nodes.
const PANE_KINDS = [
  "holes",
  "typed",
  "typed",
  "typed",
  "typed",
  "typed",
  "operators",
] as const;
const PANE_WINDOWS = [
  ["pre-inference", "post-inference"],
  ["post-inference", "post-channelize"],
  ["post-channelize", "post-as-of-read"],
  ["post-as-of-read", "post-lambda-elim"],
  ["post-lambda-elim", "post-planning"],
  ["post-planning", "post-conversion"],
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
  "Convert",
];
const ALLOWED_NATURE = ["expansion", "machinery"];

// An operator node's `role`, and an operator input edge's `kind` — the two
// closed vocabularies of the operator pane.
const ALLOWED_ROLE = ["operator", "source", "sink"];
const ALLOWED_EDGE_KIND = ["value", "share", "feedback"];

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

// One entry of a *tree* pane's node table. `validatePane` dispatches here on the
// pane's kind, which is what keeps the retired-field checks below off an
// operator node — an operator carries a `tiling`, and on a tree node that field
// is the renderer's, not the wire's.
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
  validateSpans(o.spans, path);
  // The rewrite tag: null for a lowering root (or an uncovered node), else
  // { via, nature, label } pinned to the observed vocabulary — a new pass name
  // or nature reaching the wire must be a deliberate, reviewed event.
  validateRewritten(o.rewritten, `${path}.rewritten`);
  const children = arr(o.children, `${path}.children`);
  children.forEach((c, i) => validateChild(c, `${path}.children[${i}]`));
  return v as IrNode;
}

// One entry of the operator pane's node table: an operator, or one of the two
// program boundaries. It shares an id, a span table and a rewrite tag with a
// tree node and nothing else, so the two fields that carry a tree node's
// content are asserted absent here exactly as `tiling` is asserted absent
// there.
// Every span a node's attribution records, narrowest first and each once — the
// table the spatial queries scan. Both node shapes carry the channel and both
// carry the same contract, so both read it here.
function validateSpans(v: unknown, path: string): void {
  const spans = arr(v, `${path}.spans`).map((sp, i) => validateSpan(sp, `${path}.spans[${i}]`));
  let previousExtent = -1;
  const seen = new Set<string>();
  spans.forEach((sp, i) => {
    const key = `${sp.start}:${sp.end}`;
    if (seen.has(key)) {
      throw new WireError(`${path}.spans[${i}]`, "a span not already on this node", sp);
    }
    seen.add(key);
    const extent = sp.end - sp.start;
    if (extent < previousExtent) {
      throw new WireError(`${path}.spans[${i}]`, "spans ordered narrowest first", sp);
    }
    previousExtent = extent;
  });
}

function validateOperatorNode(v: unknown, path: string): OperatorNode {
  const o = obj(v, path);
  str(o.label, `${path}.label`);
  num(o.nodeId, `${path}.nodeId`);
  if (o.type !== undefined) throw new WireError(`${path}.type`, "absent", o.type);
  if (o.children !== undefined) throw new WireError(`${path}.children`, "absent", o.children);
  const role = str(o.role, `${path}.role`);
  if (!ALLOWED_ROLE.includes(role)) {
    throw new WireError(`${path}.role`, `one of {${ALLOWED_ROLE.join(", ")}}`, role);
  }
  // The tiling is the operator's own rendered output tiling, so a boundary has
  // none: `Source` and `Sink` name a program edge rather than a computation.
  if (role === "operator") {
    str(o.tiling, `${path}.tiling`);
  } else if (o.tiling !== undefined && o.tiling !== null) {
    throw new WireError(`${path}.tiling`, "null or absent on a boundary node", o.tiling);
  }
  validateSpans(o.spans, path);
  validateRewritten(o.rewritten, `${path}.rewritten`);
  arr(o.inputs, `${path}.inputs`).forEach((e, i) =>
    validateOperatorEdge(e, `${path}.inputs[${i}]`),
  );
  return v as OperatorNode;
}

// One input edge of an operator node. `id` names a node of the same pane's
// table; `validatePane` checks that once the table's ids are known.
function validateOperatorEdge(v: unknown, path: string): OperatorEdge {
  const o = obj(v, path);
  str(o.role, `${path}.role`);
  const kind = str(o.kind, `${path}.kind`);
  if (!ALLOWED_EDGE_KIND.includes(kind)) {
    throw new WireError(`${path}.kind`, `one of {${ALLOWED_EDGE_KIND.join(", ")}}`, kind);
  }
  if (typeof o.deferred !== "boolean") {
    throw new WireError(`${path}.deferred`, "boolean", o.deferred);
  }
  num(o.id, `${path}.id`);
  return v as OperatorEdge;
}

function validateChild(v: unknown, path: string): IrChild {
  const o = obj(v, path);
  num(o.id, `${path}.id`);
  if (typeof o.predicate !== "boolean") {
    throw new WireError(`${path}.predicate`, "boolean", o.predicate);
  }
  return v as IrChild;
}

// A pane's node table: every root, every child id and every operator input id
// names an entry of this same pane's `nodes`, and no id appears twice. The
// closure check is what the table buys over the nested tree it replaced — an
// edge a consumer follows always lands on an entry the pane holds.
//
// `kind` is the shape discriminant, so it picks both the node validator and the
// edge relation the closure runs over. A kind outside the pinned set reads as a
// tree here and is caught by the per-id kind pin in `validateSnapshot`.
function validatePane(v: unknown, path: string): PaneEntry {
  const o = obj(v, path);
  str(o.id, `${path}.id`);
  str(o.label, `${path}.label`);
  const kind = str(o.kind, `${path}.kind`);
  if (o.ir !== undefined) throw new WireError(`${path}.ir`, "absent", o.ir);
  // The parallel span table shipped one row per node per span, which is what a
  // node's own `spans` says.
  if (o.spanIndex !== undefined) throw new WireError(`${path}.spanIndex`, "absent", o.spanIndex);
  // Superseded by `roots`: a pane may have several, and an operator pane does.
  if (o.root !== undefined) throw new WireError(`${path}.root`, "absent (use roots)", o.root);
  const operators = kind === "operators";

  const roots = arr(o.roots, `${path}.roots`).map((r, i) => num(r, `${path}.roots[${i}]`));
  if (roots.length === 0) {
    throw new WireError(`${path}.roots`, "a non-empty array", o.roots);
  }
  // A tree has one root by construction; several roots is the operator graph's
  // shape — a sink per compiled output and a fan input per share point.
  if (!operators && roots.length !== 1) {
    throw new WireError(`${path}.roots`, "exactly one root on a tree pane", roots);
  }
  if (new Set(roots).size !== roots.length) {
    throw new WireError(`${path}.roots`, "no repeated root", roots);
  }

  const rawNodes = arr(o.nodes, `${path}.nodes`);
  const ids = new Set<number>();

  // The table holds each node once, and the roots name entries of it. Both hold
  // whichever shape the nodes are, so they run off the ids alone.
  const closeOverIds = (validated: readonly { nodeId: number }[]): void => {
    validated.forEach((n, i) => {
      if (ids.has(n.nodeId)) {
        throw new WireError(
          `${path}.nodes[${i}].nodeId`,
          "an id not already in the table",
          n.nodeId,
        );
      }
      ids.add(n.nodeId);
    });
    roots.forEach((root, i) => {
      if (!ids.has(root)) {
        throw new WireError(`${path}.roots[${i}]`, "an id present in this pane's nodes", root);
      }
    });
  };

  if (operators) {
    const nodes = rawNodes.map((n, i) => validateOperatorNode(n, `${path}.nodes[${i}]`));
    closeOverIds(nodes);
    nodes.forEach((n, i) => {
      n.inputs.forEach((e, j) => {
        if (!ids.has(e.id)) {
          throw new WireError(
            `${path}.nodes[${i}].inputs[${j}].id`,
            "an id present in this pane's nodes",
            e.id,
          );
        }
      });
    });
    return v as PaneEntry;
  }

  const nodes = rawNodes.map((n, i) => validateNode(n, `${path}.nodes[${i}]`));
  closeOverIds(nodes);
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
