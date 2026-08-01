import { describe, expect, it } from "vitest";

import { buildIndices } from "./indices";
import type { Definition, InspectNode, SpanIndexEntry } from "./types";

function node(
  nodeId: number,
  label: string,
  span: { start: number; end: number } | null,
  type: string | null,
  children: { edge: string; node: InspectNode }[] = [],
): InspectNode {
  return {
    label,
    type,
    annotations: [],
    nodeId,
    span,
    rewritten: null,
    tiling: null,
    children,
  };
}

// A small hand-built IR: an outer node [0,10) wrapping an inner node [2,5),
// which itself wraps a leaf [3,4). Plus a coincident-span pair: two nodes that
// share span [6,7) at different depths (the mono-clone / def case).
//   root #1 [0,10)
//     child #2 [2,5)
//       leaf  #3 [3,4)
//     dup-shallow #4 [6,7)   (depth 1)
//       dup-deep  #5 [6,7)   (depth 2)  <- innermost, wins ties
const leaf = node(3, "Leaf", { start: 3, end: 4 }, "Int");
const inner = node(2, "Inner", { start: 2, end: 5 }, "Int", [{ edge: "0", node: leaf }]);
const dupDeep = node(5, "DupDeep", { start: 6, end: 7 }, "Bool");
const dupShallow = node(4, "DupShallow", { start: 6, end: 7 }, "Int", [
  { edge: "0", node: dupDeep },
]);
const root = node(1, "Root", { start: 0, end: 10 }, "Int", [
  { edge: "0", node: inner },
  { edge: "1", node: dupShallow },
]);

const spanIndex: SpanIndexEntry[] = [
  { span: { start: 0, end: 10 }, nodeId: 1 },
  { span: { start: 2, end: 5 }, nodeId: 2 },
  { span: { start: 3, end: 4 }, nodeId: 3 },
  { span: { start: 6, end: 7 }, nodeId: 4 },
  { span: { start: 6, end: 7 }, nodeId: 5 },
];

const definitions: Definition[] = [
  { useSpan: { start: 8, end: 9 }, defSpan: { start: 0, end: 1 }, name: "x" },
];

const idx = buildIndices(root, spanIndex, definitions);

describe("buildIndices: flattening", () => {
  it("maps every node by id", () => {
    expect([...idx.nodeById.keys()].sort((a, b) => a - b)).toEqual([1, 2, 3, 4, 5]);
  });
  it("records nesting depth", () => {
    expect(idx.depthById.get(1)).toBe(0);
    expect(idx.depthById.get(2)).toBe(1);
    expect(idx.depthById.get(3)).toBe(2);
    expect(idx.depthById.get(4)).toBe(1);
    expect(idx.depthById.get(5)).toBe(2);
  });
});

describe("tightestNodeAt (D4 policy)", () => {
  it("picks the innermost (smallest extent) containing node", () => {
    expect(idx.tightestNodeAt(3)).toBe(3); // inside leaf [3,4)
    expect(idx.tightestNodeAt(2)).toBe(2); // inside inner [2,5) but not leaf
    expect(idx.tightestNodeAt(1)).toBe(1); // only root contains 1
  });
  it("breaks coincident-span ties by greatest depth (deepest in IR)", () => {
    // Both #4 and #5 span [6,7); the deeper #5 wins.
    expect(idx.tightestNodeAt(6)).toBe(5);
  });
  it("returns null outside every span (half-open: end excluded)", () => {
    expect(idx.tightestNodeAt(10)).toBeNull();
    expect(idx.tightestNodeAt(4)).toBe(2); // leaf [3,4) excludes 4 -> inner
  });
});

describe("typesAt (monomorphized type set)", () => {
  it("returns the single narrowest type at a point", () => {
    expect(idx.typesAt(3)).toEqual(["Int"]); // leaf
  });
  it("collects and dedupes types across coincident narrowest spans", () => {
    // [6,7): #4 is Int, #5 is Bool — both narrowest, so the set is both.
    expect(idx.typesAt(6)).toEqual(["Int", "Bool"]);
  });
  it("returns empty when no span contains the offset", () => {
    expect(idx.typesAt(10)).toEqual([]);
  });
});

describe("definitionAt", () => {
  it("finds the def whose useSpan contains the offset", () => {
    expect(idx.definitionAt(8)?.name).toBe("x");
  });
  it("returns null off any use-site", () => {
    expect(idx.definitionAt(0)).toBeNull();
    expect(idx.definitionAt(9)).toBeNull(); // useSpan [8,9) excludes 9
  });
});

describe("buildIndices: degraded (no IR)", () => {
  it("is empty but queries are safe", () => {
    const degraded = buildIndices(null, [], []);
    expect(degraded.nodeById.size).toBe(0);
    expect(degraded.tightestNodeAt(0)).toBeNull();
    expect(degraded.typesAt(0)).toEqual([]);
    expect(degraded.definitionAt(0)).toBeNull();
  });
});
