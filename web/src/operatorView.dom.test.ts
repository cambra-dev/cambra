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

import { readFileSync, readdirSync } from "node:fs";
import { resolve } from "node:path";
import { beforeAll, describe, expect, it, vi } from "vitest";

import { OperatorView, serializeOperatorGraph } from "./operatorView";
import { type Detail, drawGraphOf, isBackEdge } from "./graph/model";
import { COMPOSITE_NAMES, MAX_MEMBERS } from "./graph/rules";
import { Store } from "./store";
import { TreeView } from "./treeView";
import type { GraphLayout, LayoutRequest, Placed } from "./graph/layout";
import type { Selection } from "./store";
import type { OperatorPane, Snapshot } from "./types";

import { fixture, irPaneById, operatorPaneById, stubLayout } from "./__fixtures__/helpers";

import arithmeticJson from "./__fixtures__/arithmetic.snapshot.json";
import deferLiftJson from "./__fixtures__/defer_lift.snapshot.json";
import listMinJson from "./__fixtures__/list_min.snapshot.json";
import polymorphicJson from "./__fixtures__/polymorphic.snapshot.json";
import sourceSharedJson from "./__fixtures__/source_shared.snapshot.json";

// `polymorphic` is the fixture with a fanned-out graph: three walk starts and
// a `share` edge into one of them. `list_min` is the degenerate one — one
// walk start, all value edges.
const polymorphic = fixture(polymorphicJson);
const listMin = fixture(listMinJson);
const deferLift = fixture(deferLiftJson);
// The only fixture with a `Source` node, and so the only one that pins a node
// nothing subscribes getting a row.
const sourceShared = fixture(sourceSharedJson);
// Every committed fixture with an operator graph. `failed` has none.
const withOperators: [string, Snapshot][] = [
  ["arithmetic", fixture(arithmeticJson)],
  ["defer_lift", deferLift],
  ["list_min", listMin],
  ["polymorphic", polymorphic],
  ["source_shared", sourceShared],
];

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

/**
 * A layout that never places anything.
 *
 * The pane has to stay addressable when the engine fails: it is the only pane
 * whose content depends on a third-party algorithm resolving.
 */
class FailingLayout implements GraphLayout {
  async run(_request: LayoutRequest): Promise<Placed> {
    throw new Error("no layout");
  }
}

/** A `RowLayout` that records what it was asked to lay out. */
class RecordingLayout extends RowLayout {
  readonly requests: LayoutRequest[] = [];
  override async run(request: LayoutRequest): Promise<Placed> {
    this.requests.push(request);
    return super.run(request);
  }
}

/** Let the draw the constructor started settle, success or failure. */
function settled(): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, 0));
}

async function mountGraph(
  snap: Snapshot,
  paneId: string,
  detail: Detail = "Raw",
): Promise<{ store: Store; body: HTMLElement; pane: OperatorPane; view: OperatorView }> {
  const body = document.createElement("div");
  document.body.appendChild(body);
  const store = new Store(snap);
  const pane = operatorPaneById(snap, paneId);
  const view = new OperatorView(body, store, pane, new RowLayout(), detail);
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

  it("suppresses the fan slots and the constants, and keeps them addressable", async () => {
    const { body, pane } = await mountGraph(polymorphic, "post-conversion");
    const boxes = idsOf(body, ".graph-node");
    const suppressed = pane.nodes
      .filter((n) => n.label === "FanOutSlot" || n.label === "Constant")
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
    const branch = pane.nodes.find((n) => n.label === "FanOutSlot")!;
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
  it("shows each operator's tiling in its box", async () => {
    const { body, pane } = await mountGraph(listMin, "post-conversion");
    const tiled = pane.nodes.find((n) => n.tiling && n.label !== "Constant")!;
    const box = body.querySelector<HTMLElement>(`.graph-node[data-node-id="${tiled.nodeId}"]`)!;
    expect(box.querySelector(".node-type")?.textContent).toBe(tiled.tiling);
  });

  it("drops a layout that resolves after a later one", async () => {
    const pending: ((placed: Placed) => void)[] = [];
    const held: GraphLayout = {
      run: () => new Promise<Placed>((resolve) => pending.push(resolve)),
    };
    const body = document.createElement("div");
    document.body.appendChild(body);
    const pane = operatorPaneById(listMin, "post-conversion");
    const view = new OperatorView(body, new Store(listMin), pane, held);
    const second = view.draw();
    const request = drawGraphOf(pane).nodes.map((n) => ({ id: String(n.id), width: 80, height: 22 }));
    const placed = (width: number): Placed => ({
      width,
      height: 40 * request.length,
      nodes: request.map((n, i) => ({ ...n, x: 0, y: 40 * i })),
      edges: [],
    });
    pending[1](placed(500));
    await second;
    pending[0](placed(100));
    await settled();
    expect(body.querySelector<HTMLElement>(".graph-canvas")!.style.width).toBe(`${500 + 24}px`);
  });

  // The canvas outlives every drawing, so a listener bound per paint is a
  // second, third and fourth handler for one click.
  it("binds its click handler once, not once per draw", async () => {
    const { store, body, view } = await mountGraph(polymorphic, "post-conversion");
    const selections = vi.spyOn(store, "setSelection");
    await view.draw();
    await view.draw();

    body
      .querySelector<HTMLElement>(".graph-node")!
      .dispatchEvent(new MouseEvent("click", { bubbles: true }));
    expect(selections).toHaveBeenCalledTimes(1);
    selections.mockRestore();
  });
});

describe("every committed fixture", () => {
  // The model's two guarantees, over every operator graph the corpus pins
  // rather than the one a test happened to pick.
  it.each(withOperators)("%s: draws every id once and lays out no cycle", async (_, snap) => {
    const { body, pane } = await mountGraph(snap, "post-conversion");
    const drawn = idsOf(body, "[data-node-id]").sort((a, b) => a - b);
    expect(drawn).toEqual(pane.nodes.map((n) => n.nodeId).sort((a, b) => a - b));

    const graph = drawGraphOf(pane);
    const next = new Map<number, number[]>();
    for (const e of graph.edges.filter((e) => !isBackEdge(e))) {
      next.set(e.from, [...(next.get(e.from) ?? []), e.to]);
    }
    const state = new Map<number, "open" | "done">();
    const acyclic = (id: number): boolean => {
      if (state.get(id) === "done") return true;
      if (state.get(id) === "open") return false;
      state.set(id, "open");
      const ok = (next.get(id) ?? []).every(acyclic);
      state.set(id, "done");
      return ok;
    };
    expect(graph.nodes.every((n) => acyclic(n.id))).toBe(true);
  });
});

describe("the copy text", () => {
  // A share edge serializes as a reference row naming its role and target.
  it("names a reference row by its role", () => {
    const text = serializeOperatorGraph(operatorPaneById(polymorphic, "post-conversion"));
    const refs = text.split("\n").filter((l) => l.includes(": → "));
    expect(refs.length).toBeGreaterThan(0);
    for (const line of refs) expect(line.trim()).toMatch(/^fan: → \w+ #\d+$/);
  });
});

describe("a layout that fails", () => {
  // Every other pane degrades visibly. Without a catch this one stays `drawn`
  // false for good, every later selection queues into `pending` that nothing
  // reads, and the reader sees an empty panel with no account of why.
  it("lists the operators and reports the failure", async () => {
    const body = document.createElement("div");
    document.body.appendChild(body);
    const store = new Store(polymorphic);
    const pane = operatorPaneById(polymorphic, "post-conversion");
    const reported = vi.spyOn(console, "error").mockImplementation(() => {});

    new OperatorView(body, store, pane, new FailingLayout(), "Raw");
    // Selected while the layout was still in flight, so this also pins that the
    // held selection is released by the fallback and not only by a drawing.
    const sink = pane.nodes.find((n) => n.role === "sink")!;
    store.setSelection({ kind: "node", paneId: pane.id, nodeId: sink.nodeId });
    await settled();

    expect(reported).toHaveBeenCalled();
    reported.mockRestore();

    expect(body.querySelector(".graph-failed")?.textContent).toContain("Layout failed");
    // Every id the drawing would have carried is still a selection target.
    const drawn = new Set(idsOf(body, "[data-node-id]"));
    for (const node of pane.nodes) {
      expect(drawn.has(drawGraphOf(pane).viewItem(node.nodeId)!.id)).toBe(true);
    }
    expect(
      body
        .querySelector<HTMLElement>(`.graph-node[data-node-id="${sink.nodeId}"]`)
        ?.classList.contains("selected"),
    ).toBe(true);
  });
});

describe("a graph that reads a source", () => {
  // Every node of the pane has an element that answers for it, a suppressed one
  // through whatever replaced it. A source is not a node: its reads start at the
  // input-free `IterateExtent`s over its domain, which are drawn like any other.
  it("gives every node something that answers for it", () => {
    const pane = operatorPaneById(sourceShared, "post-conversion");
    expect(
      pane.nodes.some((n) => n.label === "IterateExtent" && n.inputs.length === 0),
    ).toBe(true);

    const graph = drawGraphOf(pane);
    for (const node of pane.nodes) {
      expect(graph.viewItem(node.nodeId)).toBeDefined();
    }
  });
});

// Hand-built operator panes, for shapes no committed fixture carries.
const op = (
  nodeId: number,
  label: string,
  inputs: OperatorPane["nodes"][number]["inputs"],
  tiling: string | null = "SF(Int)",
): OperatorPane["nodes"][number] => ({
  label,
  nodeId,
  role: label === "Sink" ? "sink" : "operator",
  tiling,
  spans: [],
  rewritten: null,
  inputs,
});
const value = (name: string, subscribed: number, deferred = false) => ({
  role: { kind: "named" as const, name },
  kind: "value",
  deferred,
  subscribed,
});
const fan = (subscribed: number) => ({
  role: { kind: "named" as const, name: "fan" },
  kind: "share",
  deferred: false,
  subscribed,
});
const paneOf = (nodes: OperatorPane["nodes"]): OperatorPane => ({
  id: "post-conversion",
  label: "IR (POST-CONVERSION)",
  kind: "operators",
  nodes,
});

describe("the simplified level", () => {
  // Merging is a drawing decision, so it may not cost a reader anything the
  // wire named. These are the three ways it could, over every fixture with an
  // operator graph.
  for (const [name, snap] of withOperators) {
    it(`answers for every operator of ${name}`, () => {
      const pane = operatorPaneById(snap, "post-conversion");
      const graph = drawGraphOf(pane, "Simplified");
      for (const node of pane.nodes) expect(graph.viewItem(node.nodeId)).toBeDefined();
    });

    it(`keeps every composite of ${name} within the size limit`, () => {
      const pane = operatorPaneById(snap, "post-conversion");
      for (const box of drawGraphOf(pane, "Simplified").nodes) {
        expect(box.members.length).toBeLessThanOrEqual(MAX_MEMBERS);
      }
    });

    it(`draws ${name} with no more boxes than the Raw level`, () => {
      const pane = operatorPaneById(snap, "post-conversion");
      const simplified = drawGraphOf(pane, "Simplified").nodes.length;
      expect(simplified).toBeLessThanOrEqual(drawGraphOf(pane, "Raw").nodes.length);
    });
  }

  it("attributes a chip to a member of the box that draws it", () => {
    const pane = operatorPaneById(polymorphic, "post-conversion");
    const graph = drawGraphOf(pane, "Simplified");
    const withChips = graph.nodes.filter((n) => n.chips.length > 0);
    expect(withChips.length).toBeGreaterThan(0);
    for (const box of withChips) {
      for (const chip of box.chips) expect(box.members).toContain(chip.owner);
    }
  });

  it("draws the level the reader asked for, and redraws on the other", async () => {
    const { body } = await mountGraph(sourceShared, "post-conversion", "Simplified");
    const simplified = body.querySelectorAll(".graph-node").length;
    const button = body.querySelector<HTMLElement>('[data-detail="Raw"]')!;
    button.dispatchEvent(new MouseEvent("click", { bubbles: true }));
    await settled();
    expect(body.querySelectorAll(".graph-node").length).toBeGreaterThan(simplified);
  });

  // A pinned card is the pane's, so a redraw that replaces the panels takes it
  // along, and a hidden pane hides it.
  it("keeps a pinned card inside the pane that pinned it", async () => {
    const { body } = await mountGraph(deferLift, "post-conversion", "Simplified");
    const box = body.querySelector<HTMLElement>(".graph-canvas .graph-node")!;
    box.dispatchEvent(new MouseEvent("dblclick", { bubbles: true, clientX: 5, clientY: 5 }));

    const card = document.querySelector<HTMLElement>(".graph-card.pinned");
    expect(card).not.toBeNull();
    expect(body.contains(card)).toBe(true);
  });
});

describe("each merge rule", () => {
  // One hand-built pane per rule shape, so a rule that stops firing fails here
  // rather than only drawing more boxes. `UnionOperator` starts a pane where a
  // rule-free start is wanted: no rule names it.
  const drawn = (pane: OperatorPane) =>
    drawGraphOf(pane, "Simplified").nodes.map((n) => `${n.label}[${[...n.members].sort((a, b) => a - b)}]`);

  it("folds a group-by's keyed aggregate pair into one box named for the fold", () => {
    const pane = paneOf([
      op(1, "UnionOperator", []),
      op(2, "MapAggregate", [value("input", 1)]),
      op(3, "MapExtractAggregate", [value("input", 2)]),
      op(4, "Sink", [value("out", 3)], null),
    ]);
    expect(drawn(pane)).toEqual(["UnionOperator[1]", "MapAggregate[2,3]", "Sink[4]"]);
  });

  it("merges a run of maps into a map chain", () => {
    const pane = paneOf([
      op(1, "UnionOperator", []),
      op(2, "MapResult", [value("input", 1)]),
      op(3, "MapResult", [value("input", 2)]),
      op(4, "Sink", [value("out", 3)], null),
    ]);
    expect(drawn(pane)).toEqual(["UnionOperator[1]", "MapChain[2,3]", "Sink[4]"]);
  });

  it("merges a guard's predicate into the guard", () => {
    const pane = paneOf([
      op(1, "UnionOperator", []),
      op(2, "UnionOperator", []),
      op(3, "MapResult", [value("input", 2)]),
      op(4, "Restrict", [value("input", 1), value("predicate", 3)]),
      op(5, "Sink", [value("out", 4)], null),
    ]);
    expect(drawn(pane)).toEqual(["UnionOperator[1]", "UnionOperator[2]", "Restrict[3,4]", "Sink[5]"]);
  });

  // The back edge runs from the reader into the box a rule would absorb, so
  // the merge would make it internal and drop the recurrence.
  it("does not absorb a box into a reader that feeds it back", () => {
    const pane = paneOf([
      op(1, "UnionOperator", []),
      op(2, "MapResult", [value("input", 1), value("body", 3, true)]),
      op(3, "MapResult", [value("input", 2)]),
      op(4, "Sink", [value("out", 3)], null),
    ]);
    const graph = drawGraphOf(pane, "Simplified");
    expect(graph.edges.filter(isBackEdge)).toHaveLength(1);
    expect(drawn(pane)).toEqual(["UnionOperator[1]", "MapResult[2]", "MapResult[3]", "Sink[4]"]);
  });
});

describe("the operator kinds the rules name", () => {
  // A rule matches a box by its kind, which is the Rust operator's type name
  // (`TileOperator::kind`, `short_type_name::<Self>()`). A rename there leaves
  // the rule matching nothing and the drawing silently less merged, so every
  // kind `rules.ts` names has to be an operator the interpreter defines.
  it("are all operators the interpreter defines", () => {
    const root = resolve(__dirname, "../..") + "/";
    const dir = `${root}src/interpreter`;
    const defined = new Set<string>();
    for (const file of readdirSync(dir, { recursive: true }) as string[]) {
      if (!file.endsWith(".rs")) continue;
      const text = readFileSync(`${dir}/${file}`, "utf8");
      for (const m of text.matchAll(/impl(?:<[^>]*>)? TileOperator for (\w+)/g)) defined.add(m[1]);
    }
    const rules = readFileSync(`${root}web/src/graph/rules.ts`, "utf8");
    const named = [...new Set([...rules.matchAll(/"([A-Z][A-Za-z]*)"/g)].map((m) => m[1]))];

    expect(defined.size).toBeGreaterThan(0);
    expect(named.filter((k) => !COMPOSITE_NAMES.has(k) && !defined.has(k))).toEqual([]);
  });
});

describe("a back edge and a late one", () => {
  // No committed fixture carries either: the programs that hold a store are
  // asserted structurally in `tests/it/inspector_goldens.rs` rather than pinned
  // whole. So the shapes are built by hand, after the ones
  // `assert_store_edge_shapes` pins on the Rust side.

  // These pin the `Raw` drawing, where a suppressed branch is a glyph on
  // its edge; `Simplified` moves that mark onto the producer.
  async function mountPane(pane: OperatorPane) {
    const body = document.createElement("div");
    document.body.appendChild(body);
    const snap = { ...listMin, panes: listMin.panes.map((p) => (p.id === pane.id ? pane : p)) };
    const layout = new RecordingLayout();
    const view = new OperatorView(body, new Store(snap as Snapshot), pane, layout, "Raw");
    await view.draw();
    const laidOut = layout.requests.flatMap((r) => r.edges.map((e) => `${e.source}>${e.target}`));
    return { body, laidOut };
  }

  // The store's cycle as `for_accumulator` builds it: the body reads the
  // store back through a branch of its fan, and the store's slot holds the
  // body's root.
  const store = paneOf([
    op(1, "InductionStore", [value("body", 3, true)], "Store(UInt)"),
    op(2, "FanOutSlot", [fan(1)]),
    op(3, "UnionOperator", [value("input", 2)]),
    op(4, "FanOutSlot", [fan(1)]),
    op(5, "Sink", [value("out", 4)], null),
  ]);

  it("keeps the back edge when the rules merge", () => {
    const back = (detail: Detail) => drawGraphOf(store, detail).edges.filter(isBackEdge).length;
    expect(back("Simplified")).toBe(back("Raw"));
    expect(back("Simplified")).toBe(1);
  });

  it("draws the cycle as a back edge and never lays it out", async () => {
    const { body, laidOut } = await mountPane(store);
    expect(body.querySelectorAll(".graph-edge-back").length).toBe(1);
    expect(laidOut).not.toContain("3>1");
    expect(body.querySelectorAll(".graph-node").length).toBe(3);
  });

  // The slot can hold a branch: a body whose root is a value it shares. The
  // joined edge's kind is the branch's `share`, and it is still the cycle.
  it("draws a late edge onto a branch as a back edge", async () => {
    const { body, laidOut } = await mountPane(
      paneOf([
        op(1, "InductionStore", [value("body", 6, true)], "Store(UInt)"),
        op(2, "FanOutSlot", [fan(1)]),
        op(3, "MapResult", [value("input", 2)]),
        op(6, "FanOutSlot", [fan(3)]),
        op(7, "FanOutSlot", [fan(3)]),
        op(4, "FanOutSlot", [fan(1)]),
        op(5, "Sink", [value("out", 4)], null),
        op(8, "Sink", [value("out", 7)], null),
      ]),
    );
    expect(body.querySelectorAll(".graph-edge-back").length).toBe(1);
    expect(laidOut).not.toContain("3>1");
    expect(body.querySelector(`.graph-glyph[data-node-id="6"]`)).not.toBeNull();
  });

  // A body that is the store's own branch joins into a loop on the store. The
  // edge is the only element that can answer for the branch.
  it("keeps a self-loop and the branch it replaced", async () => {
    const { body, laidOut } = await mountPane(
      paneOf([
        op(1, "InductionStore", [value("body", 2, true)], "Store(UInt)"),
        op(2, "FanOutSlot", [fan(1)]),
        op(4, "FanOutSlot", [fan(1)]),
        op(5, "Sink", [value("out", 4)], null),
      ]),
    );
    expect(body.querySelectorAll(".graph-edge-back").length).toBe(1);
    expect(laidOut).not.toContain("1>1");
    expect(body.querySelector(`.graph-glyph[data-node-id="2"]`)).not.toBeNull();
  });

  // The SVG paints outside its box, but painted overflow is ink only: it does
  // not extend the scrollable region, so a bow past the reserved width is
  // unreachable once the graph is wider than the pane.
  it("reserves the width its back edge bows into", async () => {
    const { body } = await mountPane(store);
    const canvas = body.querySelector<HTMLElement>(".graph-canvas")!;
    const reserved = Number.parseFloat(canvas.style.width);
    const reach = [...body.querySelectorAll<SVGPathElement>(".graph-edge-back")].flatMap((path) =>
      (path.getAttribute("d") ?? "")
        .split(/[ ,LM]+/)
        .filter((n) => n !== "")
        .map(Number)
        .filter((_, i) => i % 2 === 0),
    );
    expect(reach.length).toBeGreaterThan(0);
    expect(Math.max(...reach)).toBeLessThanOrEqual(reserved);
  });
});

describe("a constant behind a lone branch", () => {
  // Its one reader is a suppressed branch, so there is no box to hold it as a
  // chip. It stays a box, and the branch a glyph on its edge.
  it("keeps both ids addressable", () => {
    const pane: OperatorPane = {
      id: "post-conversion",
      label: "IR (POST-CONVERSION)",
      kind: "operators",
      nodes: [
        { label: "Constant", nodeId: 1, role: "operator", tiling: "Scalar(Int)", spans: [], rewritten: null, inputs: [] },
        { label: "FanOutSlot", nodeId: 2, role: "operator", tiling: "SF(Int)", spans: [], rewritten: null,
          inputs: [{ role: { kind: "named", name: "fan" }, kind: "share", deferred: false, subscribed: 1 }] },
        { label: "MapResult", nodeId: 3, role: "operator", tiling: "SF(Int)", spans: [], rewritten: null,
          inputs: [{ role: { kind: "named", name: "input" }, kind: "value", deferred: false, subscribed: 2 }] },
      ],
    };
    const graph = drawGraphOf(pane);
    expect(graph.viewItem(1)).toEqual({ kind: "node", id: 1 });
    expect(graph.viewItem(2)?.kind).toBe("glyph");
  });
});
