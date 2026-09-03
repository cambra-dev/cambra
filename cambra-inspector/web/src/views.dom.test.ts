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

import { afterEach, beforeAll, beforeEach, describe, expect, it, vi } from "vitest";

import { renderApp } from "./main";
import { Store } from "./store";
import { SourceView } from "./sourceView";
import { TreeView, serializeTree } from "./treeView";

import { fixture, paneById, stubLayout, theNode } from "./__fixtures__/helpers";
import type { Snapshot } from "./types";

import listMinJson from "./__fixtures__/list_min.snapshot.json";

const listMin = fixture(listMinJson);

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
  beforeAll(stubLayout);

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

// The per-pane copy button, mounted through the real `renderApp` — `mountApp`
// above hand-rolls the layout and never calls `renderPane`, so it cannot see
// the button at all. What is asserted here is the *wiring* (which pane hands
// over which string, and how the outcome is reported); the text each serializer
// produces is pinned by the pure tests in treeView.test.ts and main.test.ts.
describe("pane copy button", () => {
  let writeText: ReturnType<typeof vi.fn>;

  const flush = (): Promise<void> => new Promise((resolve) => setTimeout(resolve, 0));

  const mount = (): HTMLElement => {
    const root = document.createElement("div");
    document.body.appendChild(root);
    renderApp(root, new Store(listMin));
    return root;
  };

  beforeAll(stubLayout);

  beforeEach(() => {
    // jsdom implements no clipboard at all, so it is installed per test.
    writeText = vi.fn().mockResolvedValue(undefined);
    Object.defineProperty(navigator, "clipboard", { value: { writeText }, configurable: true });
  });

  afterEach(() => {
    Reflect.deleteProperty(navigator, "clipboard");
  });

  it("gives every pane a copy button", () => {
    const root = mount();
    expect(root.querySelectorAll(".pane-copy").length).toBe(1 + listMin.panes.length);
  });

  it("copies the source text verbatim from the source pane", () => {
    const root = mount();
    root.querySelector<HTMLButtonElement>(".panel.source .pane-copy")!.click();

    // Byte-for-byte, trailing newline included — the editor's own document is
    // not the source of truth here (CodeMirror normalizes line breaks).
    expect(writeText).toHaveBeenCalledWith(listMin.source.text);
  });

  it("copies the serialized tree from a tree pane", () => {
    const root = mount();
    // Panes render source-first, then one per pipeline pane in order.
    const panels = root.querySelectorAll<HTMLElement>(".panel.tree");
    expect(panels.length).toBe(listMin.panes.length);

    const pane = listMin.panes[1];
    panels[1].querySelector<HTMLButtonElement>(".pane-copy")!.click();
    expect(writeText).toHaveBeenCalledWith(
      serializeTree(pane.root, new Map(pane.nodes.map((n) => [n.nodeId, n]))),
    );
  });

  it("reports a successful copy on the button", async () => {
    const root = mount();
    const button = root.querySelector<HTMLButtonElement>(".panel.source .pane-copy")!;

    button.click();
    await flush();

    expect(button.dataset.state).toBe("copied");
    expect(button.textContent).toBe("Copied");
  });

  it("reports a refused copy rather than looking like it worked", async () => {
    writeText.mockRejectedValue(new DOMException("Denied", "NotAllowedError"));
    const root = mount();
    const button = root.querySelector<HTMLButtonElement>(".panel.source .pane-copy")!;

    button.click();
    await flush();

    expect(button.dataset.state).toBe("failed");
    expect(button.textContent).toBe("Copy failed");
  });

  it("reports failure when the clipboard API is absent", async () => {
    // The non-secure-origin case: a port-forwarded http://<lan-ip>:<port>.
    Reflect.deleteProperty(navigator, "clipboard");
    const root = mount();
    const button = root.querySelector<HTMLButtonElement>(".panel.source .pane-copy")!;

    button.click();
    await flush();

    expect(button.dataset.state).toBe("failed");
  });
});
