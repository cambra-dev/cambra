// Runtime validator for the `/api/live` frame shape.
//
// A frame arrives as untyped JSON on every tick of a running program, so a
// backend drift here surfaces far from its cause: a missing `rows` reads as an
// operator that produced nothing, which is a state the pane is meant to
// display. `validateLiveFrame` walks the required keys and types and throws an
// Error naming the failing *path* on the first violation, the same discipline
// `validateSnapshot` applies to the static payload.
//
// Unlike the snapshot there is no golden byte fixture to pin this against: a
// frame carries ticks and sequence numbers from a live run, so its bytes are
// not reproducible. This validator plus the Rust side's own frame tests are
// what hold the contract, and they are extended together.

import type { LiveFrame, LiveNode, LiveProducer, LiveRow, LiveSource } from "./types";

class LiveWireError extends Error {
  constructor(path: string, expected: string, got: unknown) {
    super(`frame.${path}: expected ${expected}, got ${describe(got)}`);
    this.name = "LiveWireError";
  }
}

function describe(v: unknown): string {
  if (v === null) return "null";
  if (typeof v !== "object") return typeof v;
  const kind = Array.isArray(v) ? "array" : "object";
  try {
    return JSON.stringify(v) ?? kind;
  } catch {
    return kind;
  }
}

function isObject(v: unknown): v is Record<string, unknown> {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}

function obj(v: unknown, path: string): Record<string, unknown> {
  if (!isObject(v)) throw new LiveWireError(path, "object", v);
  return v;
}

function str(v: unknown, path: string): string {
  if (typeof v !== "string") throw new LiveWireError(path, "string", v);
  return v;
}

function num(v: unknown, path: string): number {
  if (typeof v !== "number") throw new LiveWireError(path, "number", v);
  return v;
}

function bool(v: unknown, path: string): boolean {
  if (typeof v !== "boolean") throw new LiveWireError(path, "boolean", v);
  return v;
}

function arr(v: unknown, path: string): unknown[] {
  if (!Array.isArray(v)) throw new LiveWireError(path, "array", v);
  return v;
}

function nullableStr(v: unknown, path: string): string | null {
  if (v === null) return null;
  return str(v, path);
}

function nullableNum(v: unknown, path: string): number | null {
  if (v === null) return null;
  return num(v, path);
}

function validateRow(v: unknown, path: string): LiveRow {
  const o = obj(v, path);
  return {
    // Null rather than absent for a shape whose positions are implicit, so a
    // keyless row is distinguishable from a row whose key failed to render.
    key: nullableStr(o["key"], `${path}.key`),
    value: str(o["value"], `${path}.value`),
    deleted: bool(o["deleted"], `${path}.deleted`),
  };
}

function validateRows(v: unknown, path: string, total: number, dropped: number): LiveRow[] {
  const rows = arr(v, path).map((row, i) => validateRow(row, `${path}[${i}]`));
  // The counts are the pane's only claim about completeness, so they have to
  // agree with what arrived: `total` is what the tile held and `rows` its tail,
  // so `dropped` is the difference and nothing else.
  if (dropped !== total - rows.length) {
    throw new LiveWireError(
      `${path} counts`,
      `dropped === total - rows.length (${total} - ${rows.length})`,
      dropped,
    );
  }
  return rows;
}

function validateProducer(v: unknown, path: string): LiveProducer {
  const o = obj(v, path);
  const total = num(o["total"], `${path}.total`);
  const dropped = num(o["dropped"], `${path}.dropped`);
  return {
    producerId: num(o["producerId"], `${path}.producerId`),
    producer: str(o["producer"], `${path}.producer`),
    shape: str(o["shape"], `${path}.shape`),
    watermark: nullableStr(o["watermark"], `${path}.watermark`),
    note: nullableStr(o["note"], `${path}.note`),
    tick: num(o["tick"], `${path}.tick`),
    seq: num(o["seq"], `${path}.seq`),
    stale: bool(o["stale"], `${path}.stale`),
    total,
    dropped,
    rows: validateRows(o["rows"], `${path}.rows`, total, dropped),
  };
}

function validateNode(v: unknown, path: string): LiveNode {
  const o = obj(v, path);
  const producers = arr(o["producers"], `${path}.producers`).map((p, i) =>
    validateProducer(p, `${path}.producers[${i}]`),
  );
  // One operator can build several producers, and the pane keys on the pair, so
  // a repeated id would silently collapse two of them into one row.
  const ids = new Set(producers.map((p) => p.producerId));
  if (ids.size !== producers.length) {
    throw new LiveWireError(`${path}.producers`, "distinct producerIds", producers.length);
  }
  return { nodeId: num(o["nodeId"], `${path}.nodeId`), producers };
}

function validateSource(v: unknown, path: string): LiveSource {
  const o = obj(v, path);
  const total = num(o["total"], `${path}.total`);
  const dropped = num(o["dropped"], `${path}.dropped`);
  return {
    nodeId: nullableNum(o["nodeId"], `${path}.nodeId`),
    name: str(o["name"], `${path}.name`),
    total,
    dropped,
    rows: validateRows(o["rows"], `${path}.rows`, total, dropped),
  };
}

/**
 * Validate one `/api/live` frame, returning it typed.
 *
 * Throws a `LiveWireError` naming the failing path on the first violation.
 */
export function validateLiveFrame(value: unknown): LiveFrame {
  const o = obj(value, "");
  const nodes = arr(o["nodes"], "nodes").map((n, i) => validateNode(n, `nodes[${i}]`));
  // Ascending `nodeId` is construction order, so a pane rendering them in
  // arrival order shows upstream first and does not reshuffle between frames.
  // The backend sorts; unsorted, the array arrived differently on every run.
  for (let i = 1; i < nodes.length; i++) {
    const previous = nodes[i - 1];
    const current = nodes[i];
    if (previous === undefined || current === undefined) continue;
    if (current.nodeId <= previous.nodeId) {
      throw new LiveWireError(`nodes[${i}].nodeId`, `> ${previous.nodeId}`, current.nodeId);
    }
  }
  return {
    tick: num(o["tick"], "tick"),
    published: num(o["published"], "published"),
    final: bool(o["final"], "final"),
    nodes,
    sources: arr(o["sources"], "sources").map((s, i) => validateSource(s, `sources[${i}]`)),
  };
}
