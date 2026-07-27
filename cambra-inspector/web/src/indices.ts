// Derived, snapshot-first lookups over the `/api/snapshot` payload.
//
// Everything here is a pure client-side index over data the client already
// loaded — no round-trips. The spatial queries (`tightestNodeAt`, `typesAt`,
// `definitionAt`) are the cross-link engine: a source position maps to an IR
// node / type set / definition with no help from the server.
//
// `tightestNodeAt` is the TS prototype of the D4 tightest-enclosing policy.
// A Rust port (and dedup against the source-level index) is a tracked followup;
// the unit tests here pin the behaviour so the port has a spec to mirror.

import type { Definition, InspectNode, SpanIndexEntry } from "./types";

export interface Indices {
  /** Every node keyed by its id, from flattening the IR tree (empty if no IR). */
  readonly nodeById: Map<number, InspectNode>;
  /** Nesting depth (root = 0) per node id; deeper = innermost. */
  readonly depthById: Map<number, number>;
  /** The raw span index, kept for the spatial queries. */
  readonly spanIndex: SpanIndexEntry[];
  /** The definitions table (use-site -> def-site). */
  readonly definitions: Definition[];

  tightestNodeAt(byteOffset: number): number | null;
  typesAt(byteOffset: number): string[];
  definitionAt(byteOffset: number): Definition | null;
}

function spanContains(start: number, end: number, off: number): boolean {
  // Half-open: [start, end). A zero-width span contains nothing.
  return start <= off && off < end;
}

// Rebuild the span→node index from a stage's IR tree.
//
// Schema 4 stopped shipping the per-stage `spanIndex` on the wire: it was pure
// derived data — a pre-order walk emitting one `{span, nodeId}` per node origin
// span — and every wire node already carries its origin span inline on `node.span`.
// Shipping it churned the byte-exact fixture corpus with no information the
// client could not reconstruct. This mirrors Rust's `SpanIndex::build`
// (`src/inspector_model/index.rs`): a pre-order walk emitting one entry per node
// that has a span. (Rust's index can carry several origin spans for a single
// fan-in node; the wire only ever carried each node's *primary* — narrowest —
// span, so the rebuilt index indexes each node under that one span, exactly what
// the wire could express. `depth` is not stored here — the spatial queries
// recover it from `depthById`.)
export function buildSpanIndex(ir: InspectNode | null): SpanIndexEntry[] {
  const out: SpanIndexEntry[] = [];
  const walk = (node: InspectNode): void => {
    if (node.span !== null) out.push({ span: node.span, nodeId: node.nodeId });
    for (const edge of node.children) walk(edge.node);
  };
  if (ir) walk(ir);
  return out;
}

export function buildIndices(
  ir: InspectNode | null,
  spanIndex: SpanIndexEntry[],
  definitions: Definition[],
): Indices {
  const nodeById = new Map<number, InspectNode>();
  const depthById = new Map<number, number>();

  const walk = (node: InspectNode, depth: number): void => {
    nodeById.set(node.nodeId, node);
    depthById.set(node.nodeId, depth);
    for (const edge of node.children) walk(edge.node, depth + 1);
  };
  if (ir) walk(ir, 0);

  // tightestNodeAt — the D4 tightest-enclosing policy:
  //   1. from `spanIndex`, take every entry whose span contains the offset;
  //   2. pick the smallest extent (end - start);
  //   3. break ties (coincident spans: the `def` case, or monomorphized clones
  //      sharing an origin span) by greatest depth (innermost in the IR tree).
  const tightestNodeAt = (byteOffset: number): number | null => {
    let best: { nodeId: number; extent: number; depth: number } | null = null;
    for (const { span, nodeId } of spanIndex) {
      if (!spanContains(span.start, span.end, byteOffset)) continue;
      const extent = span.end - span.start;
      const depth = depthById.get(nodeId) ?? -1;
      if (
        best === null ||
        extent < best.extent ||
        (extent === best.extent && depth > best.depth)
      ) {
        best = { nodeId, extent, depth };
      }
    }
    return best ? best.nodeId : null;
  };

  // typesAt — the monomorphized type-set (R2). Gather every node whose span
  // equals the *narrowest* containing span at the offset, collect each node's
  // type, dedupe (stable / outermost-first). Usually length 1; >1 for a mono
  // def body where several clones share one origin span.
  const typesAt = (byteOffset: number): string[] => {
    let narrowest = Infinity;
    for (const { span } of spanIndex) {
      if (!spanContains(span.start, span.end, byteOffset)) continue;
      narrowest = Math.min(narrowest, span.end - span.start);
    }
    if (narrowest === Infinity) return [];

    const types: string[] = [];
    const seen = new Set<string>();
    for (const { span, nodeId } of spanIndex) {
      if (!spanContains(span.start, span.end, byteOffset)) continue;
      if (span.end - span.start !== narrowest) continue;
      const node = nodeById.get(nodeId);
      if (!node) continue;
      const type = node.type;
      if (type !== null && !seen.has(type)) {
        seen.add(type);
        types.push(type);
      }
    }
    return types;
  };

  const definitionAt = (byteOffset: number): Definition | null => {
    // A use-site span is the narrow identifier range; first containing match
    // wins (use-sites do not overlap each other).
    for (const def of definitions) {
      if (spanContains(def.useSpan.start, def.useSpan.end, byteOffset)) return def;
    }
    return null;
  };

  return {
    nodeById,
    depthById,
    spanIndex,
    definitions,
    tightestNodeAt,
    typesAt,
    definitionAt,
  };
}
