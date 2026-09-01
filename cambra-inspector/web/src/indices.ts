// Derived, snapshot-first lookups over the `/api/snapshot` payload.
//
// Everything here is a pure client-side index over data the client already
// loaded — no round-trips. The spatial queries (`tightestNodeAt`, `typesAt`,
// `definitionAt`) are the cross-link engine: a source position maps to an IR
// node / type set / definition with no help from the server. The backend ships
// the tables and answers no positional query (`src/inspector_model/design.md`,
// "The usage model"), so this is the only implementation of that policy.

import type { Definition, IrNode } from "./types";

export interface Indices {
  /** Every node keyed by its id — the pane's node table, read directly. */
  readonly nodeById: Map<number, IrNode>;
  /** Nesting depth (root = 0) per node id; deeper = innermost. */
  readonly depthById: Map<number, number>;
  /**
   * The ids that live inside a refinement predicate rather than in the value
   * tree — reached only through a `predicate` child edge.
   *
   * They are indexed (a link can point at one, and the tree renders them), but
   * a query about a value must not answer with one, so the spatial queries and
   * the cross-pane type stitch consult this.
   */
  readonly predicateIds: Set<number>;
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

export function buildIndices(
  roots: number[],
  nodes: IrNode[],
  definitions: Definition[],
): Indices {
  const nodeById = new Map<number, IrNode>();
  for (const node of nodes) nodeById.set(node.nodeId, node);

  // The (span, node) pairs the spatial queries scan, flattened from the node
  // table once. A node carries every span its attribution records, so one node
  // contributes one row per span.
  const spanRows: Array<{ start: number; end: number; nodeId: number }> = [];
  for (const node of nodes) {
    for (const span of node.spans) {
      spanRows.push({ start: span.start, end: span.end, nodeId: node.nodeId });
    }
  }

  // Depth and predicate-ness are properties of a *position* in the tree, and the
  // table is a DAG: a shared predicate hangs off several parents. Both are
  // resolved at first visit of a pre-order walk from the pane's roots — the same
  // order the producer emits `nodes` in, so a node's depth here is the depth of
  // the position that put it in the array. Value children precede predicate
  // children at every node, so a node reachable both as an operand and inside a
  // type is first reached as the operand and is correctly not a predicate
  // interior.
  //
  // A tree pane names exactly one root, so the stack starts with one entry; an
  // empty `roots` walks nothing.
  const depthById = new Map<number, number>();
  const predicateIds = new Set<number>();
  const stack: Array<{ id: number; depth: number; inPredicate: boolean }> = roots.map((id) => ({
    id,
    depth: 0,
    inPredicate: false,
  }));
  while (stack.length > 0) {
    const { id, depth, inPredicate } = stack.pop()!;
    if (depthById.has(id)) continue;
    depthById.set(id, depth);
    if (inPredicate) predicateIds.add(id);
    const node = nodeById.get(id);
    if (!node) continue;
    // Reversed, so the LIFO stack pops children in wire order.
    for (let i = node.children.length - 1; i >= 0; i--) {
      const child = node.children[i];
      stack.push({
        id: child.id,
        depth: depth + 1,
        inPredicate: inPredicate || child.predicate,
      });
    }
  }

  // tightestNodeAt — the D4 tightest-enclosing policy:
  //   1. from the nodes' spans, take every pair whose span contains the offset;
  //   2. pick the smallest extent (end - start);
  //   3. break ties (coincident spans: the `def` case, or monomorphized clones
  //      sharing an origin span) by value-tree-before-predicate, then by
  //      greatest depth (innermost in the IR tree).
  //
  // The predicate half of that tie-break is what a literal needs. Inference
  // synthesizes a singleton refinement *from* the literal, so the predicate's
  // nodes inherit the literal's span exactly; without it the deepest-wins rule
  // would answer a hover on `1` with a node inside `__elem == 1`. A predicate
  // the author actually wrote has the annotation's span, which is a different
  // extent, so this only ever fires on the synthesized case.
  const tightestNodeAt = (byteOffset: number): number | null => {
    let best: { nodeId: number; extent: number; depth: number; pred: boolean } | null = null;
    for (const { start, end, nodeId } of spanRows) {
      if (!spanContains(start, end, byteOffset)) continue;
      const extent = end - start;
      const depth = depthById.get(nodeId) ?? -1;
      const pred = predicateIds.has(nodeId);
      if (
        best === null ||
        extent < best.extent ||
        (extent === best.extent &&
          ((best.pred && !pred) || (best.pred === pred && depth > best.depth)))
      ) {
        best = { nodeId, extent, depth, pred };
      }
    }
    return best ? best.nodeId : null;
  };

  // typesAt — the monomorphized type-set (R2). Gather every node whose span
  // equals the *narrowest* containing span at the offset, collect each node's
  // type, dedupe (stable / outermost-first). Usually length 1; >1 for a mono
  // def body where several clones share one origin span.
  //
  // Predicate interiors are excluded: asking what type is at a position must not
  // answer with the types of the nodes that *constitute* a type there.
  const typesAt = (byteOffset: number): string[] => {
    let narrowest = Infinity;
    for (const { start, end, nodeId } of spanRows) {
      if (!spanContains(start, end, byteOffset)) continue;
      if (predicateIds.has(nodeId)) continue;
      narrowest = Math.min(narrowest, end - start);
    }
    if (narrowest === Infinity) return [];

    const types: string[] = [];
    const seen = new Set<string>();
    for (const { start, end, nodeId } of spanRows) {
      if (!spanContains(start, end, byteOffset)) continue;
      if (end - start !== narrowest) continue;
      if (predicateIds.has(nodeId)) continue;
      const node = nodeById.get(nodeId);
      if (!node) continue;
      if (!seen.has(node.type)) {
        seen.add(node.type);
        types.push(node.type);
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
    predicateIds,
    definitions,
    tightestNodeAt,
    typesAt,
    definitionAt,
  };
}
