// @vitest-environment jsdom
//
// DOM coverage for `OperatorView`: the operator pane draws the dataflow graph
// as an indented forest, and it carries the cross-pane link like every other
// pane.
//
// The three facts a tree renderer would get wrong, and so the three this pins:
// a graph has several walk starts (one tree each), a share edge is a reference
// leaf rather than a second copy of the shared subtree, and a click in the pane
// reaches the panes upstream of it.
//
// Not covered: the `late` marker on a value edge wired through a `CycleSlot`.
// Only the two store programs build one and neither has a committed fixture, so
// `op-deferred` is unasserted here.

import { beforeAll, describe, expect, it } from "vitest";

import { OperatorView } from "./operatorView";
import { Store } from "./store";
import { TreeView } from "./treeView";
import type { Selection } from "./store";
import type { OperatorEdge, OperatorNode, OperatorPane, Snapshot } from "./types";
import { roleLabel } from "./types";

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

function mountGraph(snap: Snapshot, paneId: string): {
  store: Store;
  body: HTMLElement;
  pane: OperatorPane;
} {
  const body = document.createElement("div");
  document.body.appendChild(body);
  const store = new Store(snap);
  const pane = operatorPaneById(snap, paneId);
  new OperatorView(body, store, pane);
  return { store, body, pane };
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

/** The node id a row names, from its `.node-id` cell (`#4021` -> 4021). */
function rowNodeId(row: HTMLElement): number {
  return Number(row.querySelector(".node-id")!.textContent!.slice(1));
}

/** The rows drawing a node in its own right — reference leaves excluded. */
function nodeRows(body: HTMLElement): HTMLElement[] {
  return [...body.querySelectorAll<HTMLElement>(".tree-row")].filter(
    (row) => !row.classList.contains("op-ref"),
  );
}

function nodeRow(body: HTMLElement, nodeId: number): HTMLElement {
  const found = nodeRows(body).filter((row) => rowNodeId(row) === nodeId);
  if (found.length !== 1) {
    throw new Error(`expected exactly one row for #${nodeId}, found ${found.length}`);
  }
  return found[0];
}

/** The `.tree-node` box a row heads — the row plus its children. */
function subtreeOf(row: HTMLElement): HTMLElement {
  return row.parentElement as HTMLElement;
}

describe("OperatorView: the graph as a forest", () => {
  beforeAll(stubLayout);

  it("draws one tree per walk start", () => {
    for (const [snap, id] of [
      [polymorphic, "post-conversion"],
      [listMin, "post-conversion"],
    ] as const) {
      const { body, pane } = mountGraph(snap, id);
      const trees = [...body.querySelector(".tree-root")!.children];

      // The nodes no value edge subscribes, in table order — what the view
      // derives, recomputed here from the payload rather than taken from it.
      const subscribed = new Set(
        pane.nodes.flatMap((n) =>
          n.inputs.filter((e) => e.kind === "value").map((e) => e.subscribed),
        ),
      );
      const starts = pane.nodes.map((n) => n.nodeId).filter((id) => !subscribed.has(id));

      expect(trees.length).toBe(starts.length);
      // One tree per start, each headed by its own node, in table order.
      expect(trees.map((t) => rowNodeId(t.querySelector(".tree-row")!))).toEqual(starts);
    }
  });

  it("draws every node of the graph exactly once", () => {
    // The forest covers the table: a node no value edge subscribes heads a tree
    // of its own, so nothing is dropped and nothing is duplicated.
    // `source_shared` is the case that needs it — nothing subscribes a source
    // with a value edge, so it is drawn as a one-node tree or not at all, and a
    // node with no row has no selection handle for a pane link to land on.
    for (const [snap, id] of [
      [polymorphic, "post-conversion"],
      [sourceShared, "post-conversion"],
    ] as const) {
      const { body, pane } = mountGraph(snap, id);
      expect(nodeRows(body).map(rowNodeId).sort((a, b) => a - b)).toEqual(
        pane.nodes.map((n) => n.nodeId).sort((a, b) => a - b),
      );
    }
  });

  it("shows an operator's tiling and a boundary node's absence of one", () => {
    const { body, pane } = mountGraph(polymorphic, "post-conversion");
    const sink = pane.nodes.find((n) => n.role === "sink")!;
    const operator = pane.nodes.find((n) => n.role === "operator")!;

    expect(nodeRow(body, sink.nodeId).querySelector(".node-type")).toBeNull();
    expect(nodeRow(body, operator.nodeId).querySelector(".node-type")?.textContent).toBe(
      operator.tiling,
    );
  });
});

describe("OperatorView: share edges as reference leaves", () => {
  beforeAll(stubLayout);

  // The consumers of a share edge, and the edge each holds.
  const sharers = (pane: OperatorPane): [OperatorNode, OperatorEdge][] =>
    pane.nodes.flatMap((node) =>
      node.inputs
        .filter((e) => e.kind === "share")
        .map((e) => [node, e] as [OperatorNode, OperatorEdge]),
    );

  it("renders a share input as an `.op-ref` leaf naming its target", () => {
    const { body, pane } = mountGraph(polymorphic, "post-conversion");
    const shares = sharers(pane);
    expect(shares.length).toBeGreaterThan(0);

    for (const [consumer, edge] of shares) {
      const subtree = subtreeOf(nodeRow(body, consumer.nodeId));
      const refs = [...subtree.querySelectorAll<HTMLElement>(".op-ref")];

      expect(refs.length).toBe(1);
      expect(refs[0].classList.contains("op-ref-share")).toBe(true);
      expect(rowNodeId(refs[0])).toBe(edge.subscribed);
      expect(refs[0].querySelector(".op-ref-arrow")!.textContent).toBe("→");
      expect(refs[0].querySelector(".edge-label")!.textContent).toBe(`${roleLabel(edge.role)}:`);
      // The subscribed node's label, so the reference reads without chasing
      // the id.
      const subscribed = pane.nodes.find((n) => n.nodeId === edge.subscribed)!;
      expect(refs[0].querySelector(".node-label")!.textContent).toBe(subscribed.label);
    }
  });

  it("does not nest the shared subtree under its consumer", () => {
    const { body, pane } = mountGraph(polymorphic, "post-conversion");
    const [consumer, edge] = sharers(pane)[0];
    const subscribed = pane.nodes.find((n) => n.nodeId === edge.subscribed)!;
    // The shared node holds inputs of its own; those are what a nested draw
    // would duplicate.
    expect(subscribed.inputs.length).toBeGreaterThan(0);

    const subtree = subtreeOf(nodeRow(body, consumer.nodeId));
    // The consumer's row and the one reference leaf, and nothing below it.
    expect(subtree.querySelectorAll(".tree-row").length).toBe(2);
    expect(nodeRows(subtree).map(rowNodeId)).toEqual([consumer.nodeId]);
  });

  it("selects the subscribed node when a reference leaf is clicked", () => {
    const { store, body, pane } = mountGraph(polymorphic, "post-conversion");
    const [, edge] = sharers(pane)[0];
    const selection = watchSelection(store);

    body.querySelector<HTMLElement>(".op-ref")!.click();

    expect(selection()).toEqual({ kind: "node", paneId: pane.id, nodeId: edge.subscribed });
  });
});

describe("OperatorView: the cross-pane link", () => {
  beforeAll(stubLayout);

  it("a click on an operator row highlights the linked nodes upstream", () => {
    const container = document.createElement("div");
    document.body.appendChild(container);
    const store = new Store(polymorphic);

    const graphBody = document.createElement("div");
    container.appendChild(graphBody);
    const pane = operatorPaneById(polymorphic, "post-conversion");
    new OperatorView(graphBody, store, pane);

    // The pane immediately upstream of conversion — where the operator pane's
    // provenance edges land.
    const upstream = irPaneById(polymorphic, "post-planning");
    const treeBody = document.createElement("div");
    container.appendChild(treeBody);
    new TreeView(treeBody, store, upstream.id, upstream.root);

    const sink = pane.nodes.find((n) => n.role === "sink")!;
    const expected = new Set(
      polymorphic.paneLinks
        .filter((l) => l.from === upstream.id && l.to === pane.id)
        .flatMap((l) => l.edges.filter(([, down]) => down === sink.nodeId).map(([up]) => up)),
    );
    expect(expected.size).toBeGreaterThan(0);

    const selection = watchSelection(store);
    nodeRow(graphBody, sink.nodeId).click();

    // The clicked row is an anchor. Not the *only* one: an anchor's images
    // under the pane links are anchors too, and a round trip can bring several
    // back into this pane, so the row is asserted directly rather than by
    // taking the first `.selected` in the DOM.
    expect(selection()).toEqual({ kind: "node", paneId: pane.id, nodeId: sink.nodeId });
    expect(nodeRow(graphBody, sink.nodeId).classList.contains("selected")).toBe(true);

    // …and every node the link graph reaches upstream is highlighted there.
    const highlighted = new Set(
      [...treeBody.querySelectorAll<HTMLElement>(".tree-row.selected, .tree-row.linked")].map(
        rowNodeId,
      ),
    );
    for (const id of expected) expect(highlighted).toContain(id);
  });
});
