// Unit tests for the PURE source-interaction decision logic extracted from the
// CodeMirror closures (`hoverPayloadAt`, `resolveSourceClick`). jsdom cannot do
// CM geometry (`posAtCoords`), so we drive bytes directly off known node spans /
// a use-site from the golden fixtures, over a real Store's anchor `Indices`.
//
// These cover the README "Interactions" headline gestures: hover-for-type,
// plain-click-selects-node, and Ctrl/Cmd-click-goto-definition. The production
// CM handlers call these same functions, so this is the real decision path.

import { describe, expect, it } from "vitest";

import { Store } from "./store";
import { flattenHighlights, hoverPayloadAt, resolveSourceClick } from "./sourceView";

import { fixture, irPaneById, theNode } from "./__fixtures__/helpers";
import type { Indices } from "./indices";

import arithmeticJson from "./__fixtures__/arithmetic.snapshot.json";
import listMinJson from "./__fixtures__/list_min.snapshot.json";

const arithmetic = fixture(arithmeticJson);
const listMin = fixture(listMinJson);

function anchorOf(store: Store): Indices {
  const idx = store.indicesFor(store.sourceAnchorPaneId!);
  if (!idx) throw new Error("no anchor indices");
  return idx;
}

describe("hoverPayloadAt", () => {
  it("returns the tightest node's label + type set at a literal span", () => {
    const store = new Store(listMin);
    const anchor = anchorOf(store);
    const lit = theNode(irPaneById(listMin, "post-inference"), "Lit(Int(1))"); // span [1,2)

    const payload = hoverPayloadAt(anchor, store.offsets, lit.spans[0]!.start);
    expect(payload).not.toBeNull();
    expect(payload!.label).toBe("Lit(Int(1))");
    // A literal is typed by which literal it is, so its type prints as `Int@1`.
    expect(payload!.types).toEqual(["Int@1"]);
    expect(payload!.rewritten).toBeNull(); // a directly-lowered source literal
    expect(payload!.gotoDefName).toBeNull(); // not a use-site
  });

  it("reports the def name when the byte is on a use-site", () => {
    const store = new Store(arithmetic);
    const anchor = anchorOf(store);
    // The use of `p` lives at byte 22 (definitions[0].useSpan = [22,23)).
    const payload = hoverPayloadAt(anchor, store.offsets, 22);
    expect(payload).not.toBeNull();
    expect(payload!.gotoDefName).toBe("p");
    // The tightest enclosing node there is the `Apply` spanning the single byte
    // of `p`, which inlining substituted with the call's `1` argument — so it
    // carries that literal's singleton type.
    expect(payload!.types).toEqual(["Int@1"]);
  });

  it("returns null where no node encloses the byte", () => {
    const store = new Store(listMin);
    const anchor = anchorOf(store);
    // Past the end of the source text (byte well beyond any span).
    expect(hoverPayloadAt(anchor, store.offsets, 9999)).toBeNull();
  });
});

describe("resolveSourceClick", () => {
  it("plain click leaves a caret at the clicked source byte", () => {
    const store = new Store(arithmetic);
    const anchor = anchorOf(store);
    expect(resolveSourceClick(anchor, 22, { goto: false })).toEqual({
      kind: "source",
      from: 22,
      to: 22,
    });
  });

  it("Ctrl/Cmd-click on a use-site jumps to the def-site start", () => {
    const store = new Store(arithmetic);
    const anchor = anchorOf(store);
    // Use of `p` at byte 22 -> def-site span starts at byte 13.
    expect(resolveSourceClick(anchor, 22, { goto: true })).toEqual({
      kind: "source",
      from: 13,
      to: 13,
    });
  });

  it("Ctrl/Cmd-click off any use-site falls back to a plain source selection", () => {
    const store = new Store(arithmetic);
    const anchor = anchorOf(store);
    const lit = theNode(irPaneById(arithmetic, "post-inference"), "Lit(Int(10))");
    // A literal is not a use-site, so goto has nothing to resolve.
    expect(resolveSourceClick(anchor, lit.spans[0]!.start, { goto: true })).toEqual({
      kind: "source",
      from: lit.spans[0]!.start,
      to: lit.spans[0]!.start,
    });
  });

  it("degrades to a plain source selection when there is no anchor", () => {
    expect(resolveSourceClick(undefined, 42, { goto: true })).toEqual({
      kind: "source",
      from: 42,
      to: 42,
    });
  });
});

describe("flattenHighlights", () => {
  const p = (from: number, to: number) => ({ from, to, primary: true });
  const l = (from: number, to: number) => ({ from, to, primary: false });

  it("joins two nested primary spans into one region", () => {
    // The `txn_multi_read` case: clicking the `if` gives post-inference the
    // statement [393,435) and the downstream panes the enclosing `with` block
    // [371,435). Rendered raw, the inner range paints twice and reads as a
    // shade that means nothing.
    expect(flattenHighlights([p(371, 435), p(393, 435)])).toEqual([p(371, 435)]);
  });

  it("joins overlapping and touching spans of the same tier", () => {
    expect(flattenHighlights([p(0, 5), p(3, 9)])).toEqual([p(0, 9)]);
    expect(flattenHighlights([p(0, 5), p(5, 9)])).toEqual([p(0, 9)]);
  });

  it("keeps disjoint spans apart", () => {
    expect(flattenHighlights([p(0, 2), p(6, 8)])).toEqual([p(0, 2), p(6, 8)]);
  });

  it("gives an offset to primary when both tiers cover it", () => {
    expect(flattenHighlights([l(0, 10), p(4, 6)])).toEqual([l(0, 4), p(4, 6), l(6, 10)]);
  });

  it("drops a linked span a primary one covers entirely", () => {
    expect(flattenHighlights([l(4, 6), p(0, 10)])).toEqual([p(0, 10)]);
  });

  it("subtracts several primary regions from one linked span", () => {
    expect(flattenHighlights([l(0, 20), p(2, 4), p(10, 12)])).toEqual([
      l(0, 2),
      p(2, 4),
      l(4, 10),
      p(10, 12),
      l(12, 20),
    ]);
  });

  it("emits nothing for empty input or empty spans", () => {
    expect(flattenHighlights([])).toEqual([]);
    expect(flattenHighlights([p(3, 3)])).toEqual([]);
  });

  it("returns spans ascending, whatever order they arrive in", () => {
    const out = flattenHighlights([p(20, 25), l(0, 30), p(5, 7)]);
    expect(out.map((x) => x.from)).toEqual([...out.map((x) => x.from)].sort((a, b) => a - b));
    expect(out.every((x, i) => i === 0 || out[i - 1].to <= x.from)).toBe(true);
  });
});

