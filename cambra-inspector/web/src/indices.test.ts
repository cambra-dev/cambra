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

const idx = buildIndices([1], nodes, definitions, "");

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
  const idx = buildIndices([10], shared, [], "");

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


describe("nodesInRange: containment is decided on visible text", () => {
  // The `txn_multi_read` shape. `with begin():` and its body is one construct
  // whose span runs to the newline ending the last line; a drag over those
  // lines stops at the last character the reader can see, one byte short. The
  // enclosing construct then fell out of a selection that visibly covered it.
  const text = "a = 1\nblock:\n  body\n";
  //             0      6       13
  // `block:\n  body\n` is [6, 20): the trailing newline is the 19th byte.
  const nodes: IrNode[] = [
    node(60, "Root", { start: 0, end: 20 }, "Unit", [value(61), value(62)]),
    node(61, "Assign", { start: 0, end: 5 }, "Int"),
    node(62, "Block", { start: 6, end: 20 }, "Unit", [value(63)]),
    node(63, "Body", { start: 15, end: 19 }, "Unit"),
  ];
  const t = buildIndices([60], nodes, [], text);

  it("takes a construct whose span ends in the newline just past the drag", () => {
    // Dragging line 2 to the end of its visible text: [6, 19).
    expect(t.nodesInRange(6, 19).sort((a, b) => a - b)).toEqual([62, 63]);
  });

  it("agrees with the drag that does include the newline", () => {
    expect(t.nodesInRange(6, 20).sort((a, b) => a - b)).toEqual([62, 63]);
  });

  it("a sliced node arrives through the region, not through containment", () => {
    // Ending inside `body` covers no node whole, so containment finds nothing.
    // The slice is the region's business: it takes `Body` whole, and the nodes
    // in that region are what gets traced.
    expect(t.nodesInRange(6, 17)).toEqual([]);
    const region = t.selectionRegion(6, 17);
    expect(t.nodesInRange(region.from, region.to)).toContain(63);
  });

  it("a border on whitespace slices nothing", () => {
    // Ending a drag at a line end used to ask what contains the newline, which
    // is the enclosing construct — so stopping at the end of a line pulled in
    // the whole block around it.
    expect(t.nodesInRange(6, 19)).not.toContain(60);
    expect(t.nodesInRange(0, 6)).not.toContain(60);
  });

  it("does not let whitespace pull in a neighbour", () => {
    // The drag covers line 1 and the newline after it; the Block starts on the
    // next line and stays out.
    expect(t.nodesInRange(0, 6).sort((a, b) => a - b)).toEqual([61]);
  });
});

describe("nodesInRange: visible extents are measured in bytes", () => {
  // Spans are byte offsets; a JavaScript string is indexed in UTF-16 code
  // units. They coincide only for ASCII, so a source with one multi-byte
  // character shifts every offset after it — `txn_multi_read` has em dashes in
  // its comments, and indexing the text with a span offset read the wrong
  // character, which made the trim below silently do nothing and dropped the
  // enclosing construct out of a drag that covered it.
  const text = "# \u2014\nblock:\n  body\n";
  //             0 1      (3 bytes)      chars:  0 1 2  3 4...
  const bytes = (upTo: number): number => new TextEncoder().encode(text.slice(0, upTo)).length;
  const blockStart = bytes(text.indexOf("block:"));
  const blockEnd = bytes(text.length);
  const bodyStart = bytes(text.indexOf("body"));
  const bodyEnd = bytes(text.indexOf("body") + 4);

  const nodes: IrNode[] = [
    node(70, "Block", { start: blockStart, end: blockEnd }, "Unit", [value(71)]),
    node(71, "Body", { start: bodyStart, end: bodyEnd }, "Unit"),
  ];
  const t = buildIndices([70], nodes, [], text);

  it("trims the trailing newline of a span past a multi-byte character", () => {
    // The drag ends at the last visible byte, one short of the Block's span.
    expect(t.nodesInRange(blockStart, blockEnd - 1).sort((a, b) => a - b)).toEqual([70, 71]);
  });

  it("would have failed on a char-indexed trim", () => {
    // The byte offset of the newline is 2 past its char offset here, so a
    // char-indexed test reads a letter and trims nothing. Pinning the offsets
    // differ is what makes the test above meaningful.
    expect(blockEnd).toBe(text.length + 2);
  });
});

describe("selectionRegion (how much a selection explains)", () => {
  it("takes the tightest node containing a range", () => {
    // Inner is [2,5) with Leaf [3,4) inside it. A range covering part of Leaf
    // and part of Inner is inside Inner.
    expect(idx.selectionRegion(3, 4)).toEqual({ from: 3, to: 4 }); // Leaf exactly
    expect(idx.selectionRegion(2, 5)).toEqual({ from: 2, to: 5 }); // Inner exactly
    expect(idx.selectionRegion(2, 4)).toEqual({ from: 2, to: 5 }); // inside Inner
  });

  it("takes a caret's node, which is what a click already explained", () => {
    expect(idx.selectionRegion(3, 3)).toEqual({ from: 3, to: 4 });
    expect(idx.selectionRegion(8, 8)).toEqual({ from: 0, to: 10 }); // only the root
  });

  it("rises to the common parent for a range spanning siblings", () => {
    // Inner [2,5) and DupShallow [6,7) are siblings under Root [0,10). A drag
    // across both is inside the root, so the traces explain the root.
    expect(idx.selectionRegion(4, 7)).toEqual({ from: 0, to: 10 });
  });

  it("returns the range when nothing contains it", () => {
    expect(idx.selectionRegion(20, 30)).toEqual({ from: 20, to: 30 });
  });

  it("is what makes a partial drag explain the whole construct", () => {
    // The reported case, in miniature: a drag stopping part-way through Leaf
    // covers no node whole, so `nodesInRange` on the raw range finds only the
    // node it cuts. Over the enclosing extent it finds the construct's
    // contents, which is what a click inside it already found.
    const raw = idx.nodesInRange(2, 4).sort((a, b) => a - b);
    const region = idx.selectionRegion(2, 4);
    const widened = idx.nodesInRange(region.from, region.to).sort((a, b) => a - b);
    expect(widened).toEqual([2, 3]);
    expect(widened.length).toBeGreaterThan(raw.length);
  });
});

describe("growing a selection never un-selects anything", () => {
  // The property the old border rule broke. Dragging one byte further changed
  // which node was "the tightest at the border", so an enclosing `Apply` was
  // claimed at `dup(`, claimed by nothing at `dup(1`, and claimed again at the
  // end of the line — blue, gone, blue. Monotonicity is the invariant that
  // makes toggling impossible, so it is asserted directly rather than through
  // the cases that happened to expose it.
  const text = "dup = \\x -> (x, x)\na = dup(1)\nb = dup(2 == 2)\na\n";
  const nodes: IrNode[] = [
    node(80, "Let(dup)", { start: 0, end: 18 }, "_", [value(81)]),
    node(81, "Lambda(x)", { start: 6, end: 18 }, "_", [value(82)]),
    node(82, "Tuple", { start: 13, end: 18 }, "_"),
    node(83, "Let(a)", { start: 19, end: 29 }, "_", [value(84)]),
    node(84, "Apply", { start: 23, end: 29 }, "_", [value(85), value(86)]),
    node(85, "Var(dup)", { start: 23, end: 26 }, "_"),
    node(86, "Lit(Int(1))", { start: 27, end: 28 }, "_"),
  ];
  const m = buildIndices([80], nodes, [], text);

  it("nodesInRange only grows", () => {
    for (const from of [0, 6, 19, 23]) {
      let previous = new Set<number>();
      for (let to = from + 1; to <= text.length; to += 1) {
        const now = new Set(m.nodesInRange(from, to));
        for (const id of previous) {
          expect(now, `#${id} dropped out at [${from},${to})`).toContain(id);
        }
        previous = now;
      }
    }
  });

  it("selectionRegion only grows", () => {
    for (const from of [0, 6, 19, 23]) {
      let previous: { from: number; to: number } | null = null;
      for (let to = from + 1; to <= text.length; to += 1) {
        const now = m.selectionRegion(from, to);
        expect(now.from, `region start grew at [${from},${to})`).toBeLessThanOrEqual(from);
        expect(now.to, `region end shrank at [${from},${to})`).toBeGreaterThanOrEqual(to);
        if (previous !== null) {
          expect(now.from).toBeLessThanOrEqual(previous.from);
          expect(now.to).toBeGreaterThanOrEqual(previous.to);
        }
        previous = now;
      }
    }
  });

  it("the reported drag explains the Apply at every width", () => {
    // `dup(` is [0,27), `dup(1` is [0,28), the whole of both lines is [0,29).
    // The Apply must be part of what the selection explains in all three.
    for (const to of [27, 28, 29]) {
      const region = m.selectionRegion(0, to);
      expect(m.nodesInRange(region.from, region.to), `Apply at [0,${to})`).toContain(84);
    }
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
  const p = buildIndices([20], withPred, [], "");

  it("skips them in the containment pass", () => {
    expect(p.nodesInRange(4, 5)).toEqual([21]);
  });

  it("skips them in the region a cut produces", () => {
    // The predicate interior shares the literal's span, so a region taking the
    // cut node whole must still not offer it.
    const region = p.selectionRegion(3, 5);
    expect(p.nodesInRange(region.from, region.to).sort((a, b) => a - b)).toEqual([20, 21]);
  });

  it("covering everything still names only the drawn nodes", () => {
    expect(p.nodesInRange(0, 6).sort((a, b) => a - b)).toEqual([20, 21]);
  });
});

describe("tightestNodeAt: a synthesized unit is not what a click means", () => {
  // The `txn_multi_read` case. `if pool > r:` with no `else` mints a unit for
  // the statement's value, and that unit carries the *statement's* whole span —
  // so it ties the `ExprStmt` that owns the statement on width and wins on
  // depth. A click on `if` then answers with a node the reader never wrote.
  const withUnit: IrNode[] = [
    node(40, "ExprStmt", { start: 10, end: 30 }, "Unit", [value(41)]),
    node(41, "Lit(Unit)", { start: 10, end: 30 }, "Unit"),
  ];
  const u = buildIndices([40], withUnit, [], "");

  it("prefers the construct over the unit standing for its value", () => {
    expect(u.tightestNodeAt(15)).toBe(40);
  });

  it("still answers with the unit when nothing else covers the offset", () => {
    // A preference, not an exclusion: a unit that is the only candidate is
    // still the answer, so an explicitly written one stays reachable.
    const only = buildIndices([41], [node(41, "Lit(Unit)", { start: 2, end: 4 }, "Unit")], [], "");
    expect(only.tightestNodeAt(3)).toBe(41);
  });

  it("does not disturb the depth tie-break between two constructs", () => {
    // What depth-first is for: the innermost of two coincident constructs.
    expect(idx.tightestNodeAt(6)).toBe(5);
  });

  it("prefers a narrower unit over a wider construct", () => {
    // Width still decides first, so a unit that really is the tightest thing
    // at the offset wins over an enclosing construct.
    const mixed = buildIndices(
      [50],
      [
        node(50, "ExprStmt", { start: 0, end: 20 }, "Unit", [value(51)]),
        node(51, "Lit(Unit)", { start: 5, end: 7 }, "Unit"),
      ],
      [],
      "",
    );
    expect(mixed.tightestNodeAt(6)).toBe(51);
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

  it("covers only what it wholly contains", () => {
    // [4,7) starts inside Inner [2,5), so Inner is not covered. Taking a cut
    // node whole is `selectionRegion`'s job, and doing it here made the result
    // depend on which node each border landed in.
    expect(idx.nodesInRange(4, 7).sort((a, b) => a - b)).toEqual([4, 5]);
    const region = idx.selectionRegion(4, 7);
    expect(idx.nodesInRange(region.from, region.to).sort((a, b) => a - b)).toContain(2);
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
    const degraded = buildIndices([], [], [], "");
    expect(degraded.nodeById.size).toBe(0);
    expect(degraded.tightestNodeAt(0)).toBeNull();
    expect(degraded.typesAt(0)).toEqual([]);
    expect(degraded.definitionAt(0)).toBeNull();
  });
});
