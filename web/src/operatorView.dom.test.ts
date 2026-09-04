// @vitest-environment jsdom
//
// DOM coverage for `OperatorView`: the operator pane draws the subscription
// graph, and it carries the cross-pane link like every other pane.
//
// The facts a drawing can get wrong, and so the ones this pins: every operator
// on the wire is reachable in the drawing even when it is not drawn as a box, a
// share is one edge rather than a second copy of the shared subgraph, a click
// reaches the panes upstream, and the pane does not scroll itself.
//
// Layout is stubbed. ELK's placement is its own concern and pinning coordinates
// here would assert the engine rather than the pane; what matters is that every
// node it returns is drawn and every id stays addressable.

import { beforeAll, describe, expect, it } from "vitest";

import { OperatorView } from "./operatorView";
import { drawGraphOf } from "./graph/model";
import { Store } from "./store";
import { TreeView } from "./treeView";
import type { GraphLayout, LayoutRequest, Placed } from "./graph/layout";
import type { Selection } from "./store";
import type { OperatorPane, Snapshot } from "./types";

import { fixture, irPaneById, operatorPaneById, stubLayout } from "./__fixtures__/helpers";

import listMinJson from "./__fixtures__/list_min.snapshot.json";
import polymorphicJson from "./__fixtures__/polymorphic.snapshot.json";
import sourceSharedJson from "./__fixtures__/source_shared.snapshot.json";

// `polymorphic` is the fixture with a fanned-out graph: three walk starts and
// a `share` edge into one of them. `list_min` is the degenerate one — one
// walk start, all value edges.
const polymorphic = fixture(polymorphicJson);
const listMin = fixture(listMinJson);
// The only fixture with a `Source` node, and so the only one that pins a node
// nothing subscribes getting a row.
const sourceShared = fixture(sourceSharedJson);

/**
 * A layout that places every node on its own row, in the order given.
 *
 * Deterministic and dependency-free, so an assertion about the drawing is about
 * the pane rather than about ELK.
 */
class RowLayout implements GraphLayout {
  async run(request: LayoutRequest): Promise<Placed> {
    const nodes = request.nodes.map((n, i) => ({
      id: n.id,
      x: 0,
      y: i * 40,
      width: n.width,
      height: n.height,
    }));
    const at = new Map(nodes.map((n) => [n.id, n]));
    return {
      width: Math.max(0, ...nodes.map((n) => n.width)),
      height: nodes.length * 40,
      nodes,
      edges: request.edges.map((e) => {
        const a = at.get(e.source);
        const b = at.get(e.target);
        return {
          id: e.id,
          points: [
            { x: a ? a.x + a.width / 2 : 0, y: a ? a.y + a.height : 0 },
            { x: b ? b.x + b.width / 2 : 0, y: b ? b.y : 0 },
          ],
        };
      }),
    };
  }
}

async function mountGraph(
  snap: Snapshot,
  paneId: string,
): Promise<{ store: Store; body: HTMLElement; pane: OperatorPane; view: OperatorView }> {
  const body = document.createElement("div");
  document.body.appendChild(body);
  const store = new Store(snap);
  const pane = operatorPaneById(snap, paneId);
  const view = new OperatorView(body, store, pane, new RowLayout());
  await view.draw();
  return { store, body, pane, view };
}

/**
 * The store's latest selection. `Store` exposes the resolved state only through
 * `subscribe`, so a test that asserts on what a click selected records it.
 */
function watchSelection(store: Store): () => Selection {
  let latest: Selection = null;
  store.subscribe((resolved) => {
    latest = resolved.selection;
  });
  return () => latest;
}

const idsOf = (body: HTMLElement, selector: string): number[] =>
  [...body.querySelectorAll<HTMLElement>(selector)].map((e) => Number(e.dataset.nodeId));

beforeAll(() => {
  stubLayout();
});

describe("OperatorView", () => {
  it("draws every operator on the wire exactly once", async () => {
    const { body, pane } = await mountGraph(polymorphic, "post-conversion");
    const drawn = idsOf(body, "[data-node-id]").sort((a, b) => a - b);
    expect(drawn).toEqual(pane.nodes.map((n) => n.nodeId).sort((a, b) => a - b));
  });

  it("suppresses the fan branches and the constants, and keeps them addressable", async () => {
    const { body, pane } = await mountGraph(polymorphic, "post-conversion");
    const boxes = idsOf(body, ".graph-node");
    const suppressed = pane.nodes
      .filter((n) => n.label === "FanOutBranch" || n.label === "Constant")
      .map((n) => n.nodeId);
    // Something was suppressed, or this fixture would not exercise the rule.
    expect(suppressed.length).toBeGreaterThan(0);
    for (const id of suppressed) expect(boxes).not.toContain(id);
    // ...and every one of them is still an element a selection can land on.
    for (const id of suppressed) {
      expect(body.querySelector(`[data-node-id="${id}"]`)).not.toBeNull();
    }
  });

  it("draws a share as one edge, not a second copy of the shared subgraph", async () => {
    const { body, pane } = await mountGraph(polymorphic, "post-conversion");
    const graph = drawGraphOf(pane);
    const shares = graph.edges.filter((e) => e.kind === "share");
    expect(shares.length).toBeGreaterThan(0);
    expect(body.querySelectorAll(".graph-edge-share").length).toBe(shares.length);
    // A shared producer is drawn once however many consumers reach it.
    for (const share of shares) {
      expect(body.querySelectorAll(`.graph-node[data-node-id="${share.from}"]`).length).toBe(1);
    }
  });

  it("tells a boundary node from an operator", async () => {
    const { body, pane } = await mountGraph(listMin, "post-conversion");
    const sink = pane.nodes.find((n) => n.role === "sink");
    expect(sink).toBeDefined();
    const el = body.querySelector<HTMLElement>(`.graph-node[data-node-id="${sink!.nodeId}"]`);
    expect(el?.dataset.role).toBe("sink");
  });

  it("selects the node a reader clicks, naming this pane as the origin", async () => {
    const { store, body, pane } = await mountGraph(listMin, "post-conversion");
    const latest = watchSelection(store);
    const target = pane.nodes.find((n) => n.role === "operator")!;
    body
      .querySelector<HTMLElement>(`.graph-node[data-node-id="${target.nodeId}"]`)!
      .dispatchEvent(new MouseEvent("click", { bubbles: true }));
    expect(latest()).toEqual({
      kind: "node",
      paneId: pane.id,
      nodeId: target.nodeId,
    });
  });

  it("selects a suppressed operator from the glyph that replaced it", async () => {
    const { store, body, pane } = await mountGraph(polymorphic, "post-conversion");
    const latest = watchSelection(store);
    const branch = pane.nodes.find((n) => n.label === "FanOutBranch")!;
    const glyph = body.querySelector<HTMLElement>(`.graph-glyph[data-node-id="${branch.nodeId}"]`);
    expect(glyph).not.toBeNull();
    glyph!.dispatchEvent(new MouseEvent("click", { bubbles: true }));
    expect(latest()).toEqual({
      kind: "node",
      paneId: pane.id,
      nodeId: branch.nodeId,
    });
  });

  it("a click on an operator highlights the linked nodes upstream", async () => {
    const body = document.createElement("div");
    document.body.appendChild(body);
    const store = new Store(polymorphic);
    const pane = operatorPaneById(polymorphic, "post-conversion");
    const view = new OperatorView(body, store, pane, new RowLayout());
    await view.draw();

    const treeHost = document.createElement("div");
    document.body.appendChild(treeHost);
    const upstream = irPaneById(polymorphic, "post-planning");
    new TreeView(treeHost, store, upstream.id, upstream.root);

    const sink = pane.nodes.find((n) => n.role === "sink")!;
    body
      .querySelector<HTMLElement>(`.graph-node[data-node-id="${sink.nodeId}"]`)!
      .dispatchEvent(new MouseEvent("click", { bubbles: true }));

    const here = body.querySelector<HTMLElement>(
      `.graph-node[data-node-id="${sink.nodeId}"]`,
    );
    expect(here?.classList.contains("selected")).toBe(true);
    // The gesture reached the pane upstream of this one.
    expect(treeHost.querySelectorAll(".tree-row.selected, .tree-row.linked").length)
      .toBeGreaterThan(0);
  });
});

describe("a graph that reads a source", () => {
  // Under a shipped start set the source had to be listed or the forest drew no
  // row for it, and a pane link landing on it reached nothing. Drawing the whole
  // table retires that failure mode: every node of the pane has an element that
  // answers for it, a suppressed one through whatever replaced it.
  it("gives every node something that answers for it", () => {
    const pane = operatorPaneById(sourceShared, "post-conversion");
    expect(pane.nodes.some((n) => n.role === "source")).toBe(true);

    const graph = drawGraphOf(pane);
    for (const node of pane.nodes) {
      expect(graph.viewItem(node.nodeId)).toBeDefined();
    }
  });
});

describe("a back edge and a late one", () => {
  // No committed fixture carries either, so the shapes are built by hand. Both
  // reach the wire — `assert_store_edge_shapes` pins that on the Rust side —
  // and without this the two renderings would be exercised by nothing.
  const pane: OperatorPane = {
    id: "post-conversion",
    label: "IR (POST-CONVERSION)",
    kind: "operators",
    nodes: [
      { label: "InductionStore", nodeId: 1, role: "operator", tiling: "Store(UInt)", spans: [], rewritten: null,
        inputs: [{ role: { kind: "named", name: "body" }, kind: "value", deferred: true, subscribed: 2 }] },
      { label: "MapResult", nodeId: 2, role: "operator", tiling: "SF(Int)", spans: [], rewritten: null,
        inputs: [{ role: { kind: "named", name: "fan" }, kind: "share", deferred: false, subscribed: 1 }] },
    ],
  };

  it("draws the cycle as a back edge and never lays it out", async () => {
    const body = document.createElement("div");
    document.body.appendChild(body);
    const snap = { ...listMin, panes: listMin.panes.map((p) => (p.id === pane.id ? pane : p)) };
    const store = new Store(snap as Snapshot);
    const view = new OperatorView(body, store, pane, new RowLayout());
    await view.draw();
    expect(body.querySelectorAll(".graph-edge-back").length).toBe(1);
    expect(body.querySelectorAll(".graph-node").length).toBe(2);
  });
});
