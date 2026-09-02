import { describe, expect, it } from "vitest";

import { buildIndices } from "./indices";
import type { Definition, IrNode } from "./types";

function node(
  nodeId: number,
  label: string,
  span: { start: number; end: number } | null,
  type: string,
  children: { id: number; predicate: boolean }[] = [],
): IrNode {
  return {
    label,
    nodeId,
    spans: span === null ? [] : [span],
    rewritten: null,
    type,
    children,
  };
}

// A small hand-built node table: an outer node [0,10) wrapping an inner node
// [2,5), which itself wraps a leaf [3,4). Plus a coincident-span pair: two nodes
// that share span [6,7) at different depths (the mono-clone / def case).
//   root #1 [0,10)
//     child #2 [2,5)
//       leaf  #3 [3,4)
//     dup-shallow #4 [6,7)   (depth 1)
//       dup-deep  #5 [6,7)   (depth 2)  <- innermost, wins ties
const value = (id: number) => ({ id, predicate: false });
const nodes: IrNode[] = [
  node(1, "Root", { start: 0, end: 10 }, "Int", [value(2), { id: 4, predicate: false }]),
  node(2, "Inner", { start: 2, end: 5 }, "Int", [value(3)]),
  node(3, "Leaf", { start: 3, end: 4 }, "Int"),
  node(4, "DupShallow", { start: 6, end: 7 }, "Int", [value(5)]),
  node(5, "DupDeep", { start: 6, end: 7 }, "Bool"),
];

const definitions: Definition[] = [
  { useSpan: { start: 8, end: 9 }, defSpan: { start: 0, end: 1 }, name: "x" },
];

const idx = buildIndices([1], nodes, definitions);

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

describe("buildIndices: predicate interiors", () => {
  // #10 is the value root; #11 is its operand; #12 is a refinement predicate
  // reached from #10 (its own type) AND from #11 (a binder's type) — one entry
  // named by two edges, which is what the node table buys. #13 lives inside it.
  const shared: IrNode[] = [
    node(10, "Root", null, "Int", [
      { id: 11, predicate: false },
      { id: 12, predicate: true },
    ]),
    node(11, "Operand", null, "Int", [{ id: 12, predicate: true }]),
    node(12, "BinOp(Comparison(Eq))", null, "Bool", [
      { id: 13, predicate: false },
    ]),
    node(13, "Lit(Int(2))", null, "Int@2"),
  ];
  const idx = buildIndices([10], shared, []);

  it("marks a predicate subtree and everything under it", () => {
    expect([...idx.predicateIds].sort((a, b) => a - b)).toEqual([12, 13]);
  });

  it("holds a shared predicate once, whichever parent names it", () => {
    expect(idx.nodeById.size).toBe(4);
    expect(idx.nodeById.get(12)!.label).toBe("BinOp(Comparison(Eq))");
  });

  it("depths are the first-visit position, value children before predicates", () => {
    expect(idx.depthById.get(11)).toBe(1);
    // #12 is first reached under the value child #11 (depth 2), not as the
    // root's own predicate child, because value children precede predicate ones.
    expect(idx.depthById.get(12)).toBe(2);
    expect(idx.depthById.get(13)).toBe(3);
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

describe("nodesInRange: predicate interiors are not seeds", () => {
  // The real synthesized shape: inference builds `__elem == 1` *from* the
  // literal, so the predicate's nodes inherit the literal's span exactly. The
  // tree draws no row for them, so a range over the literal must name the
  // literal and nothing else.
  const withPred: IrNode[] = [
    node(20, "Root", { start: 0, end: 6 }, "Int", [
      { id: 21, predicate: false },
      { id: 22, predicate: true },
    ]),
    node(21, "Lit(Int(1))", { start: 4, end: 5 }, "Int@1", [{ id: 22, predicate: true }]),
    node(22, "BinOp(Eq)", { start: 4, end: 5 }, "Bool", [{ id: 23, predicate: false }]),
    node(23, "Lit(Int(1))", { start: 4, end: 5 }, "Int@1"),
  ];
  const p = buildIndices([20], withPred, []);

  it("skips them in the containment pass", () => {
    expect(p.nodesInRange(4, 5)).toEqual([21]);
  });

  it("skips them when a border cuts", () => {
    // Asking at byte 4 must not answer with the predicate interior sharing
    // that span, and the cut must resolve to a drawn node.
    expect(p.nodesInRange(3, 5).sort((a, b) => a - b)).toEqual([20, 21]);
  });

  it("covering everything still names only the drawn nodes", () => {
    expect(p.nodesInRange(0, 6).sort((a, b) => a - b)).toEqual([20, 21]);
  });
});

describe("nodesInRange (source-selection seeds)", () => {
  it("a caret is exactly tightestNodeAt, so a click and a drag are one gesture", () => {
    expect(idx.nodesInRange(3, 3)).toEqual([3]);
    expect(idx.nodesInRange(1, 1)).toEqual([1]);
  });

  it("names every node wholly inside the range", () => {
    // [2,5) is Inner exactly, and Leaf [3,4) sits inside it.
    expect(idx.nodesInRange(2, 5).sort((a, b) => a - b)).toEqual([2, 3]);
    // Coincident spans both land, as both are drawn rows.
    expect(idx.nodesInRange(6, 7).sort((a, b) => a - b)).toEqual([4, 5]);
  });

  it("does not name the root unless the range covers it", () => {
    // The root [0,10) straddles every interior border. An overlap test would
    // answer every range with the whole tree; containment does not.
    expect(idx.nodesInRange(2, 5)).not.toContain(1);
    expect(idx.nodesInRange(0, 10)).toContain(1);
  });

  it("names a node its range cuts, whole", () => {
    // [4,7) starts inside Inner [2,5): the cut node comes in whole, exactly as
    // a click at byte 4 would have answered it.
    const cut = idx.nodesInRange(4, 7).sort((a, b) => a - b);
    expect(cut).toContain(2);
    expect(cut).toEqual([2, 4, 5]);
  });

  it("a border sitting on a node edge is not a cut", () => {
    // `from` on Inner's start and `to` past Leaf's end add nothing of their
    // own — the whole-containment pass already has them.
    expect(idx.nodesInRange(2, 5)).not.toContain(1);
    expect(idx.nodesInRange(3, 4)).toEqual([3]);
  });

  it("covers the whole document", () => {
    expect(idx.nodesInRange(0, 10).sort((a, b) => a - b)).toEqual([1, 2, 3, 4, 5]);
  });

  it("names nothing when the range holds no node and cuts none", () => {
    expect(idx.nodesInRange(20, 30)).toEqual([]);
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

describe("buildIndices: degraded (no nodes)", () => {
  it("is empty but queries are safe", () => {
    const degraded = buildIndices([], [], []);
    expect(degraded.nodeById.size).toBe(0);
    expect(degraded.tightestNodeAt(0)).toBeNull();
    expect(degraded.typesAt(0)).toEqual([]);
    expect(degraded.definitionAt(0)).toBeNull();
  });
});
