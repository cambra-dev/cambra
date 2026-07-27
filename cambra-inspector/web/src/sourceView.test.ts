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
import { hoverPayloadAt, resolveSourceClick } from "./sourceView";

import { fixture, stageById, theNode } from "./__fixtures__/helpers";
import type { Indices } from "./indices";

import arithmeticJson from "./__fixtures__/arithmetic.snapshot.json";
import listMinJson from "./__fixtures__/list_min.snapshot.json";

const arithmetic = fixture(arithmeticJson);
const listMin = fixture(listMinJson);

function anchorOf(store: Store): Indices {
  const idx = store.indicesFor(store.sourceAnchorStageId!);
  if (!idx) throw new Error("no anchor indices");
  return idx;
}

describe("hoverPayloadAt", () => {
  it("returns the tightest node's label + type set at a literal span", () => {
    const store = new Store(listMin);
    const anchor = anchorOf(store);
    const lit = theNode(stageById(listMin, "post-inference"), "Lit(Int(1))"); // span [1,2)

    const payload = hoverPayloadAt(anchor, store.offsets, lit.span!.start);
    expect(payload).not.toBeNull();
    expect(payload!.label).toBe("Lit(Int(1))");
    // A literal is typed by which literal it is, so its type prints as `1`.
    expect(payload!.types).toEqual(["1"]);
    expect(payload!.rewritten).toBeNull(); // a directly-lowered source literal
    expect(payload!.gotoDefName).toBeNull(); // not a use-site
  });

  it("reports the def name when the byte is on a use-site", () => {
    const store = new Store(arithmetic);
    const anchor = anchorOf(store);
    // The use of `p` lives at byte 144 (definitions[0].useSpan = [144,145)).
    const payload = hoverPayloadAt(anchor, store.offsets, 144);
    expect(payload).not.toBeNull();
    expect(payload!.gotoDefName).toBe("p");
    // The tightest enclosing node there is the `Apply` spanning the single byte
    // of `p`, which inlining substituted with the call's `1` argument — so it
    // carries that literal's singleton type.
    expect(payload!.types).toEqual(["1"]);
  });

  it("returns null where no node encloses the byte", () => {
    const store = new Store(listMin);
    const anchor = anchorOf(store);
    // Past the end of the source text (byte well beyond any span).
    expect(hoverPayloadAt(anchor, store.offsets, 9999)).toBeNull();
  });
});

describe("resolveSourceClick", () => {
  it("plain click selects the clicked source byte", () => {
    const store = new Store(arithmetic);
    const anchor = anchorOf(store);
    expect(resolveSourceClick(anchor, 144, { goto: false })).toEqual({
      kind: "source",
      byteOffset: 144,
    });
  });

  it("Ctrl/Cmd-click on a use-site jumps to the def-site start", () => {
    const store = new Store(arithmetic);
    const anchor = anchorOf(store);
    // Use of `p` at byte 144 -> def-site span starts at byte 135.
    expect(resolveSourceClick(anchor, 144, { goto: true })).toEqual({
      kind: "source",
      byteOffset: 135,
    });
  });

  it("Ctrl/Cmd-click off any use-site falls back to a plain source selection", () => {
    const store = new Store(arithmetic);
    const anchor = anchorOf(store);
    const lit = theNode(stageById(arithmetic, "post-inference"), "Lit(Int(10))");
    // A literal is not a use-site, so goto has nothing to resolve.
    expect(resolveSourceClick(anchor, lit.span!.start, { goto: true })).toEqual({
      kind: "source",
      byteOffset: lit.span!.start,
    });
  });

  it("degrades to a plain source selection when there is no anchor", () => {
    expect(resolveSourceClick(undefined, 42, { goto: true })).toEqual({
      kind: "source",
      byteOffset: 42,
    });
  });
});
