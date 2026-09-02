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
  /**
   * Every node this pane draws inside the half-open byte range `[from, to)` —
   * the seed set for a source selection. Order is unspecified; the caller
   * seeds a set. See the policy note above `nodesInRange`.
   */
  nodesInRange(from: number, to: number): number[];
  /**
   * How much of the source a selection explains: the construct it sits inside,
   * together with every construct it cuts across, taken whole. Never narrower
   * than `[from, to)`. See the note above `selectionRegion`.
   */
  selectionRegion(from: number, to: number): { from: number; to: number };
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
  /**
   * The program text, for deciding a span's **visible** extent.
   *
   * A construct's span runs to the newline that ends it, so `with begin():`
   * and its body span one byte past the last character the reader can see.
   * Dragging over those lines stops at that character, and containment then
   * turned on a byte nothing renders — the enclosing construct fell out of a
   * selection that visibly covered it. `nodesInRange` compares trimmed extents
   * for that reason.
   */
  sourceText: string,
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

  // A unit standing for a construct's result — the value of an `if` with no
  // `else`, of a statement sequence, of a `with` block. The reader never wrote
  // it, so it is not what they meant by clicking; it carries the span of the
  // construct that minted it, which is how it comes to compete at all.
  //
  // Matched on the label because nothing else on the wire separates it: the
  // whole region is `nature: machinery` (a `with` block lowers entirely to
  // images), so authored-versus-synthesized does not discriminate. The durable
  // fix is for such a node not to inherit the construct's extent in the first
  // place; until then this keeps the query from answering with it.
  const isSynthesizedUnit = (node: IrNode | undefined): boolean =>
    node?.label === "Lit(Unit)";

  // tightestRowAt / tightestNodeAt — the D4 tightest-enclosing policy, over
  // the value tree:
  //   1. from the nodes' spans, take every row whose span contains the offset;
  //   2. pick the smallest extent (end - start);
  //   3. break ties (coincident spans: the `def` case, or monomorphized clones
  //      sharing an origin span) by a construct before a synthesized unit, then
  //      by greatest depth (innermost in the IR tree).
  //
  // Depth-first is right almost everywhere: it is what answers a click on
  // `stdin()` with `Source(stdin)` rather than the `Apply` around it, and
  // `pool := pool - r` with `MutWrite(pool)` rather than its `ExprStmt`. Over
  // the fixture corpus plus `txn_multi_read` it decides 134 coincident-span
  // groups, and the two general-looking alternatives — prefer the ancestor,
  // prefer the deepest non-leaf — change 70 and 67 of them respectively,
  // including those two for the worse. The unit clause changes 9, all of them
  // from a unit to the construct it stands for.
  //
  // Refinement predicates are excluded outright, as in `typesAt`: the tree
  // pane draws no row for one, so answering with a predicate node would name a
  // node the reader cannot see and leave the pane with no anchor at all. That
  // subsumes the tie-break this used to need — inference synthesizes a
  // singleton refinement *from* a literal, so the predicate's nodes inherit
  // the literal's span exactly, and deepest-wins would otherwise answer a
  // hover on `1` with a node inside `__elem == 1`.
  // The winning span row, not just its node id: `nodesInRange` needs the row's
  // extent to tell a border that cuts a node from one that sits on its edge.
  type SpanRow = { start: number; end: number; nodeId: number };
  const tightestRowAt = (byteOffset: number): SpanRow | null => {
    let best: SpanRow | null = null;
    let bestExtent = Infinity;
    let bestUnit = true;
    let bestDepth = -1;
    for (const row of spanRows) {
      if (predicateIds.has(row.nodeId)) continue;
      if (!spanContains(row.start, row.end, byteOffset)) continue;
      const extent = row.end - row.start;
      const unit = isSynthesizedUnit(nodeById.get(row.nodeId));
      const depth = depthById.get(row.nodeId) ?? -1;
      const better =
        best === null ||
        extent < bestExtent ||
        (extent === bestExtent &&
          ((bestUnit && !unit) || (bestUnit === unit && depth > bestDepth)));
      if (better) {
        best = row;
        bestExtent = extent;
        bestUnit = unit;
        bestDepth = depth;
      }
    }
    return best;
  };

  const tightestNodeAt = (byteOffset: number): number | null =>
    tightestRowAt(byteOffset)?.nodeId ?? null;

  // nodesInRange — the nodes a range **wholly covers**.
  //
  // Containment and nothing else, which is what makes it monotone: growing a
  // range can only add nodes. It used to also claim the single tightest node at
  // each border, as a stand-in for "the nodes this range partially covers", and
  // that stand-in is not monotone — whether an ancestor got claimed depended on
  // which node the border happened to land inside. Dragging to `dup(` claimed
  // the enclosing `Apply`, because the tightest node at `(` is that `Apply`;
  // dragging one byte further to `dup(1` claimed nothing, because the tightest
  // node at `1` is a width-1 literal that *ends* at the border; dragging to the
  // end of the line claimed it again by containment. Blue, then gone, then
  // blue. Partial coverage is `selectionRegion`'s business now.
  //
  // Compared on visible extents: a construct's span runs to the newline that
  // ends it, and a drag over those lines stops at the last character, so a raw
  // comparison dropped the construct out of a selection that covered it.
  // Whitespace tested in **byte** space, because spans are byte offsets while a
  // JavaScript string is indexed in UTF-16 code units. They coincide only for
  // ASCII, and `txn_multi_read` has two em dashes in its comments — enough to
  // shift every offset after them, so indexing the string with a span offset
  // read the wrong character and the trim below silently did nothing. That
  // crossing is what `offsets.ts` exists to route; here there is nothing to
  // convert, since every whitespace character is one ASCII byte and no byte of
  // a multi-byte character can be mistaken for one.
  const srcBytes = new TextEncoder().encode(sourceText);
  const isSpaceByte = (i: number): boolean => {
    const c = srcBytes[i];
    return c === 0x20 || c === 0x09 || c === 0x0a || c === 0x0d || c === 0x0b || c === 0x0c;
  };

  // A span's extent with surrounding whitespace discounted, so containment
  // turns on characters the reader can see. Falls back to the raw span when it
  // is nothing but whitespace, which keeps a synthetic table with no text
  // behaving as written.
  const visible = (start: number, end: number): { start: number; end: number } => {
    let s = start;
    let e = end;
    while (s < e && isSpaceByte(s)) s += 1;
    while (e > s && isSpaceByte(e - 1)) e -= 1;
    return s < e ? { start: s, end: e } : { start, end };
  };

  // selectionRegion — how much of the source a selection explains.
  //
  // Two clauses, because a selection relates to the tree in two ways and only
  // both together are monotone:
  //
  //   1. the construct it is *inside* — the tightest node containing it. A
  //      caret takes the node it is in, a drag part-way through an expression
  //      the statement around it, so both explain the whole construct.
  //   2. every construct it *cuts* — a node it overlaps without covering,
  //      taken whole. A range crossing two statements explains both.
  //
  // Clause 2 is what a single tightest-node-at-the-border test was reaching
  // for, and it is monotone where that was not. Clause 1 alone does not
  // suffice either: a `Let` chain's span covers its binding and not its body,
  // so **no node contains a range crossing two top-level statements** — every
  // such range fell through to itself, which collapsed the traces onto the
  // anchors and dropped the explain-the-construct behaviour exactly when a
  // drag spanned more than one line.
  //
  // Closed to a fixed point, since taking a cut node whole can leave a further
  // node partly inside. A node *containing* the region is never taken: that is
  // clause 1's job, and following it here would climb to the root. Capped
  // rather than looped, on the same reasoning as elsewhere — it terminates at
  // the root's extent, and saying so in the code beats trusting the argument.
  const selectionRegion = (from: number, to: number): { from: number; to: number } => {
    let lo = from;
    let hi = to;
    let inside: { start: number; end: number } | null = null;
    for (const row of spanRows) {
      if (predicateIds.has(row.nodeId)) continue;
      const v = visible(row.start, row.end);
      if (v.start > from || to > v.end) continue;
      if (inside === null || row.end - row.start < inside.end - inside.start) {
        inside = { start: row.start, end: row.end };
      }
    }
    if (inside !== null) {
      lo = Math.min(lo, inside.start);
      hi = Math.max(hi, inside.end);
    }
    for (let pass = 0; pass < 8; pass += 1) {
      let grew = false;
      for (const row of spanRows) {
        if (predicateIds.has(row.nodeId)) continue;
        const v = visible(row.start, row.end);
        const overlaps = v.start < hi && lo < v.end;
        const covered = lo <= v.start && v.end <= hi;
        const encloses = v.start <= lo && hi <= v.end;
        if (!overlaps || covered || encloses) continue;
        lo = Math.min(lo, row.start);
        hi = Math.max(hi, row.end);
        grew = true;
      }
      if (!grew) break;
    }
    return { from: lo, to: hi };
  };

  const nodesInRange = (from: number, to: number): number[] => {
    if (from >= to) {
      const at = tightestNodeAt(from);
      return at === null ? [] : [at];
    }
    const out = new Set<number>();
    for (const { start, end, nodeId } of spanRows) {
      if (predicateIds.has(nodeId)) continue;
      const v = visible(start, end);
      if (from <= v.start && v.end <= to) out.add(nodeId);
    }
    return [...out];
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
    nodesInRange,
    selectionRegion,
    typesAt,
    definitionAt,
  };
}
