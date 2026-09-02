// @vitest-environment jsdom
//
// View-integration test (the one that would have caught Bug 1). Mounts the REAL
// SourceView + per-pane TreeViews over a golden fixture, then drives the shared
// selection in both directions and asserts the cross-link reaches the DOM:
//   - a tree-node selection -> source span highlight (.cm-sel-node) + tree row
//   - a source selection      -> every tree pane highlights its node
//
// This is exactly the store->view subscriber path Bug 1 lived in: SourceView is
// the first subscriber, and its `renderSelection` threw (unbound `byteToChar`),
// aborting `setSelection`'s listener loop so NO pane updated. With the binding
// bug present this test fails (the source highlight never appears / the loop
// throws); with the fix it passes.

import { beforeAll, describe, expect, it } from "vitest";

import { Store } from "./store";
import { SourceView } from "./sourceView";
import { TreeView } from "./treeView";
import { validateSnapshot } from "./wireValidate";
import { paneById, theNode } from "./__fixtures__/helpers";
import type { Snapshot } from "./types";

import listMinJson from "./__fixtures__/list_min.snapshot.json";

const listMin = validateSnapshot(listMinJson);

// Mount the full app (source + one tree pane per pane entry) into a fresh
// container, returning the store and the per-pane tree-pane DOM roots.
function mountApp(snap: Snapshot): {
  store: Store;
  source: HTMLElement;
  trees: Map<string, HTMLElement>;
} {
  const root = document.createElement("div");
  document.body.appendChild(root);

  const store = new Store(snap);

  const sourceBody = document.createElement("div");
  root.appendChild(sourceBody);
  // SourceView is constructed FIRST (as in main.ts) — the ordering that let
  // Bug 1's throw starve every later subscriber.
  new SourceView(sourceBody, store);

  const trees = new Map<string, HTMLElement>();
  for (const pane of store.panes) {
    const body = document.createElement("div");
    root.appendChild(body);
    trees.set(pane.id, body);
    if (pane.nodes.length > 0) new TreeView(body, store, pane.id, pane.root);
  }
  return { store, source: sourceBody, trees };
}

describe("view integration: cross-pane source<->tree linking", () => {
  beforeAll(() => {
    // jsdom does not implement scrollIntoView; CodeMirror + TreeView call it.
    (Element.prototype as unknown as { scrollIntoView: () => void }).scrollIntoView = () => {};

    // jsdom has no layout, so CodeMirror's async measure pass (fired via
    // requestAnimationFrame after the test) calls getClientRects on a Range /
    // Element and throws an uncaught exception. Stub them with empty rects; we
    // never assert on geometry (we drive selection via the store directly).
    const emptyRects = () => ({ length: 0, item: () => null, [Symbol.iterator]: function* () {} });
    const emptyRect = () => ({ top: 0, left: 0, bottom: 0, right: 0, width: 0, height: 0, x: 0, y: 0 });
    (Range.prototype as unknown as { getClientRects: () => unknown }).getClientRects = emptyRects as never;
    (Range.prototype as unknown as { getBoundingClientRect: () => unknown }).getBoundingClientRect = emptyRect as never;
    (Element.prototype as unknown as { getClientRects: () => unknown }).getClientRects = emptyRects as never;
    (Element.prototype as unknown as { getBoundingClientRect: () => unknown }).getBoundingClientRect = emptyRect as never;
  });

  it("a tree-node selection highlights the source span AND the tree rows", () => {
    const { store, source, trees } = mountApp(listMin);
    const pre = paneById(listMin, "pre-inference");
    const lit = theNode(pre, "Lit(Int(1))"); // span [1,2), identity across panes

    store.setSelection({ kind: "node", paneId: "pre-inference", nodeId: lit.nodeId });

    // (i) The source editor picked up a node-selection decoration.
    expect(source.querySelectorAll(".cm-sel-node, .cm-link-node").length).toBeGreaterThan(0);

    // (ii) Each of the three tree panes highlights the node (identity twins).
    for (const [, body] of trees) {
      expect(body.querySelectorAll(".tree-row.selected, .tree-row.linked").length).toBeGreaterThan(0);
    }
  });

  it("a source selection highlights every tree pane (reverse direction)", () => {
    const { store, trees } = mountApp(listMin);
    const pre = paneById(listMin, "pre-inference");
    const lit = theNode(pre, "Lit(Int(1))");

    // posAtCoords is unusable in jsdom (no layout); drive the store directly,
    // which is the exact code path the bug lived in.
    store.setSelection({ kind: "source", byteOffset: lit.spans[0]!.start });

    for (const [, body] of trees) {
      expect(body.querySelectorAll(".tree-row.selected, .tree-row.linked").length).toBeGreaterThan(0);
    }
  });

  it("a source selection produces a primary source highlight (.cm-sel-node)", () => {
    const { store, source } = mountApp(listMin);
    const pre = paneById(listMin, "pre-inference");
    const lit = theNode(pre, "Lit(Int(1))");

    store.setSelection({ kind: "source", byteOffset: lit.spans[0]!.start });
    expect(source.querySelectorAll(".cm-sel-node").length).toBeGreaterThan(0);
  });
});

// The holes-pane (pre-inference) row's resolved type must NOT render inline (the `→` glyph
// was confusable with `⇒`/`⇀`); it shows on hover as a tooltip instead.
function rowByNodeId(treeBody: HTMLElement, nodeId: number): HTMLElement | null {
  for (const row of treeBody.querySelectorAll<HTMLElement>(".tree-row")) {
    if (row.querySelector(".node-id")?.textContent === `#${nodeId}`) return row;
  }
  return null;
}

describe("pre-inference resolved-type display (Bug 2)", () => {
  it("shows the resolved type as a hover tooltip on a pre-inference row", () => {
    const { store, trees } = mountApp(listMin);
    const pre = trees.get("pre-inference")!;
    const lit = theNode(paneById(listMin, "pre-inference"), "Lit(Int(1))");
    // Sanity: this hole resolves downstream to the literal's singleton type.
    expect(store.resolvedTypesFor("pre-inference", lit.nodeId)).toEqual(["Int@1"]);

    const row = rowByNodeId(pre, lit.nodeId);
    expect(row).not.toBeNull();
    expect(document.querySelector(".node-resolved-tooltip")).toBeNull();

    row!.dispatchEvent(new MouseEvent("mouseenter", { bubbles: true }));
    const tip = document.querySelector(".node-resolved-tooltip");
    expect(tip).not.toBeNull();
    expect(tip!.textContent).toBe("`_` resolves to `Int@1`");

    row!.dispatchEvent(new MouseEvent("mouseleave", { bubbles: true }));
    expect(document.querySelector(".node-resolved-tooltip")).toBeNull();
  });
});
