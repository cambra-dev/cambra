// The operator pane: the subscription graph, drawn.
//
// An edge runs from a producer to the consumer that subscribed it, which is the
// direction data moves. That is the same relation the wire calls an input, read
// the other way round: an operator's inputs are the operators it subscribes.
//
// Two kinds, both on the wire. `value` is an exclusively owned subscription and
// `share` one several consumers hold. A `value` edge wired late — the one a
// `CycleSlot` filled, carrying `deferred` — is what closes a cycle: removing
// those makes every graph acyclic, so they are withheld from the layout and
// drawn as back edges rather than broken by a heuristic.
//
// Two operator kinds are suppressed rather than drawn; see `./graph/model`. A
// suppressed node keeps its id on whatever replaced it, because every id in the
// pane is a cross-pane selection target.

import { ElkLayout } from "./graph/elk";
import type { GraphLayout, Placed, Point } from "./graph/layout";
import { type DrawEdge, type DrawGraph, drawGraphOf, isBackEdge } from "./graph/model";
import type { Resolved, Store } from "./store";
import type { OperatorEdge, OperatorNode, OperatorPane } from "./types";

const INDENT = "    ";
const NODE_HEIGHT = 22;
const NODE_GAP = 14;
const LAYER_GAP = 28;
const PAD = 12;
const MIN_WIDTH = 66;
const MAX_WIDTH = 240;

const SVG_NS = "http://www.w3.org/2000/svg";

/**
 * Width of a label at the pane's font.
 *
 * Canvas measurement where there is one, and a per-character estimate where
 * there is not. jsdom has no 2D context, and a layout that could not run under
 * it could not be asserted on.
 */
const measure: (text: string) => number = (() => {
  let ctx: CanvasRenderingContext2D | null = null;
  try {
    ctx = document.createElement("canvas").getContext("2d");
  } catch {
    // jsdom implements no 2D context and says so on stderr. The estimate below
    // is what makes the layout assertable there.
    ctx = null;
  }
  if (!ctx) return (text: string) => text.length * 6.6;
  ctx.font = '500 11px ui-monospace, SFMono-Regular, Menlo, Consolas, monospace';
  return (text: string) => ctx.measureText(text).width;
})();

function el(tag: string, className?: string, text?: string): HTMLElement {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

function svg(tag: string, attrs: Record<string, string>): SVGElement {
  const node = document.createElementNS(SVG_NS, tag);
  for (const [k, v] of Object.entries(attrs)) node.setAttribute(k, v);
  return node;
}

/**
 * The nodes no value edge subscribes, in table order — where each tree of the
 * forest starts.
 *
 * Derived rather than shipped: a node's owner is the one value edge naming it,
 * so the table already answers this. `wireValidate.ts` pins that these reach
 * every node.
 */
function walkStarts(pane: OperatorPane): number[] {
  const subscribed = new Set(
    pane.nodes.flatMap((n) => n.inputs.filter(isChildEdge).map((e) => e.subscribed)),
  );
  return pane.nodes.map((n) => n.nodeId).filter((id) => !subscribed.has(id));
}

// `Restrict [0,100] #4021`, or `Sink(main) #4103` for a boundary node, which has
// no tiling.
function rowText(node: OperatorNode): string {
  return node.tiling === null || node.tiling === undefined
    ? `${node.label} #${node.nodeId}`
    : `${node.label} ${node.tiling} #${node.nodeId}`;
}

/** An edge the wire draws as a spanning child relation. */
function isChildEdge(edge: OperatorEdge): boolean {
  return edge.kind === "value";
}

interface Handle {
  /** The element carrying the highlight for this id. */
  element: HTMLElement;
  /** Position in reading order, which decides which highlight is scrolled to. */
  order: number;
}

export class OperatorView {
  private readonly store: Store;
  private readonly paneId: string;
  private readonly graph: DrawGraph;
  private readonly layout: GraphLayout;
  private readonly canvas: HTMLElement;
  private readonly handles = new Map<number, Handle>();
  private marked: HTMLElement[] = [];
  private pending: Resolved | null = null;
  private drawn = false;

  constructor(parent: HTMLElement, store: Store, pane: OperatorPane, layout?: GraphLayout) {
    this.store = store;
    this.paneId = pane.id;
    this.graph = drawGraphOf(pane);
    this.layout = layout ?? new ElkLayout();

    this.canvas = el("div", "graph-canvas");
    parent.appendChild(this.canvas);

    store.subscribe((resolved) => {
      // A selection can land before the first layout resolves. Hold the last
      // one: a highlight for a node with no element yet is not a highlight
      // that should be dropped.
      if (!this.drawn) this.pending = resolved;
      else this.renderSelection(resolved);
    });

    void this.draw();
  }

  /** Lay the graph out and draw it. Resolves when the pane is on screen. */
  async draw(): Promise<void> {
    const sized = this.graph.nodes.map((n) => ({
      id: String(n.id),
      width: Math.min(
        MAX_WIDTH,
        Math.max(
          MIN_WIDTH,
          measure(n.label) +
            measure(`#${n.id}`) +
            n.chips.reduce((a, c) => a + Math.min(64, measure(c.text)) + 9, 0) +
            26,
        ),
      ),
      height: NODE_HEIGHT,
    }));
    const forward = this.graph.edges.filter((e) => !isBackEdge(e));
    const placed = await this.layout.run({
      nodes: sized,
      edges: forward.map((e) => ({ id: e.id, source: String(e.from), target: String(e.to) })),
      nodeGap: NODE_GAP,
      layerGap: LAYER_GAP,
    });
    this.paint(placed, forward);
    this.drawn = true;
    if (this.pending) {
      this.renderSelection(this.pending);
      this.pending = null;
    }
  }

  private paint(placed: Placed, forward: DrawEdge[]): void {
    this.canvas.textContent = "";
    this.handles.clear();
    this.canvas.style.width = `${placed.width + PAD * 2}px`;
    this.canvas.style.height = `${placed.height + PAD * 2}px`;

    const at = new Map(placed.nodes.map((n) => [n.id, n]));
    const wires = svg("g", { class: "graph-wires" });
    const sheet = svg("svg", {
      width: String(placed.width + PAD * 2),
      height: String(placed.height + PAD * 2),
    });
    sheet.appendChild(wires);
    this.canvas.appendChild(sheet);

    const routed = new Map(placed.edges.map((e) => [e.id, e.points]));
    for (const edge of this.graph.edges) {
      const points = isBackEdge(edge) ? this.backEdge(edge, at) : routed.get(edge.id);
      if (!points || points.length < 2) continue;
      wires.appendChild(this.wire(edge, points));
    }

    // Reading order is layout order: down first, then across. It decides which
    // of several highlights a selection scrolls to.
    const order = new Map<string, number>();
    [...placed.nodes]
      .sort((a, b) => a.y - b.y || a.x - b.x)
      .forEach((n, i) => order.set(n.id, i));

    for (const node of this.graph.nodes) {
      const box = at.get(String(node.id));
      if (!box) continue;
      const div = el("div", "graph-node selectable");
      div.dataset.nodeId = String(node.id);
      div.dataset.role = node.role;
      div.style.left = `${box.x + PAD}px`;
      div.style.top = `${box.y + PAD}px`;
      div.style.width = `${box.width}px`;
      div.style.height = `${box.height}px`;
      div.appendChild(el("span", "graph-strip"));
      div.appendChild(el("span", "node-label", node.label));
      for (const chip of node.chips) {
        const c = el("span", "graph-chip", chip.text);
        c.dataset.nodeId = String(chip.id);
        div.appendChild(c);
        this.handles.set(chip.id, { element: c, order: order.get(String(node.id)) ?? 0 });
      }
      div.appendChild(el("span", "node-id", `#${node.id}`));
      div.title = node.tiling === null ? node.label : `${node.label}\n${node.tiling}`;
      this.canvas.appendChild(div);
      this.handles.set(node.id, { element: div, order: order.get(String(node.id)) ?? 0 });
    }

    // A suppressed node draws as a glyph on the edge that replaced it. The edge
    // itself is a two-pixel target; the glyph is one a reader can hit.
    for (const edge of this.graph.edges) {
      const points = isBackEdge(edge) ? this.backEdge(edge, at) : routed.get(edge.id);
      if (!points || !edge.suppressed.length) continue;
      const mid = midpoint(points);
      edge.suppressed.forEach((id, i) => {
        const g = el("div", "graph-glyph selectable");
        g.dataset.nodeId = String(id);
        g.dataset.kind = edge.kind;
        g.style.left = `${mid.x + PAD + i * 11}px`;
        g.style.top = `${mid.y + PAD}px`;
        g.title = `#${id}, drawn on the edge that replaced it`;
        this.canvas.appendChild(g);
        const host = order.get(String(edge.to)) ?? 0;
        this.handles.set(id, { element: g, order: host });
      });
    }

    this.canvas.addEventListener("click", (event) => this.onClick(event));
    void forward;
  }

  private wire(edge: DrawEdge, points: Point[]): SVGElement {
    const d = points
      .map((p, i) => `${i === 0 ? "M" : "L"}${p.x + PAD} ${p.y + PAD}`)
      .join(" ");
    const cls = `graph-edge graph-edge-${edge.kind}${isBackEdge(edge) ? " graph-edge-back" : ""}`;
    const path = svg("path", { d, class: cls });
    (path as SVGElement & { dataset: DOMStringMap }).dataset.edgeId = edge.id;
    (path as SVGElement & { dataset: DOMStringMap }).dataset.from = String(edge.from);
    return path;
  }

  /** A back edge, bowed out to the side so it reads as a return. */
  private backEdge(edge: DrawEdge, at: Map<string, { x: number; y: number; width: number; height: number }>): Point[] | undefined {
    const a = at.get(String(edge.from));
    const b = at.get(String(edge.to));
    if (!a || !b) return undefined;
    const from = { x: a.x + a.width / 2, y: a.y + a.height / 2 };
    const to = { x: b.x + b.width / 2, y: b.y + b.height / 2 };
    const bow = Math.max(a.x + a.width, b.x + b.width) + 26;
    return [from, { x: bow, y: from.y }, { x: bow, y: to.y }, to];
  }

  private onClick(event: MouseEvent): void {
    const target = event.target as HTMLElement | null;
    const owner = target?.closest<HTMLElement>("[data-node-id]");
    if (owner) {
      const id = Number(owner.dataset.nodeId);
      this.store.setSelection({ kind: "node", paneId: this.paneId, nodeId: id }, this.paneId);
      return;
    }
    // An edge is a jump to what it comes from, so no origin: this pane scrolls
    // to the producer like any other pane does.
    const wire = target?.closest<SVGElement>("path[data-from]");
    if (wire) {
      const from = Number((wire as SVGElement & { dataset: DOMStringMap }).dataset.from);
      this.store.setSelection({ kind: "node", paneId: this.paneId, nodeId: from });
    }
  }

  // The same two highlight strengths the tree panes use: `selected` for the
  // pane's own anchor, `linked` for a node a pane link reached.
  private renderSelection(resolved: Resolved): void {
    for (const element of this.marked) element.classList.remove("selected", "linked");
    this.marked = [];

    const highlights = resolved.result.highlightsByPane.get(this.paneId);
    if (!highlights || highlights.size === 0) return;
    const primaries = resolved.primaryByPane.get(this.paneId);

    let topmost: Handle | null = null;
    for (const nodeId of highlights) {
      const handle = this.handles.get(nodeId);
      if (!handle) continue;
      handle.element.classList.add(primaries?.has(nodeId) ? "selected" : "linked");
      this.marked.push(handle.element);
      if (topmost === null || handle.order < topmost.order) topmost = handle;
    }

    // A suppressed node is highlighted where it is drawn; the layout never moves
    // under the reader, because a relayout would displace everything else they
    // were looking at.
    if (resolved.origin !== this.paneId) {
      topmost?.element.scrollIntoView({ block: "center", inline: "center" });
    }
  }
}

/**
 * The pane's text, one indented line per row, for the copy button.
 *
 * Walks the wire's node table rather than the drawing, so the copy is the whole
 * graph whatever the drawing suppressed — what is drawn is a display decision,
 * and a copy that varied with it would not be reproducible.
 */
export function serializeOperatorGraph(pane: OperatorPane): string {
  const nodeById = new Map(pane.nodes.map((n) => [n.nodeId, n]));
  const lines: string[] = [];
  const walk = (id: number, edge: OperatorEdge | null, depth: number): void => {
    const node = nodeById.get(id);
    if (!node) return;
    const prefix =
      edge === null ? "" : `${edge.role}: ${edge.deferred ? "late " : ""}`;
    lines.push(INDENT.repeat(depth) + prefix + rowText(node));
    for (const input of node.inputs) {
      if (isChildEdge(input)) {
        walk(input.subscribed, input, depth + 1);
      } else {
        const ref = nodeById.get(input.subscribed);
        lines.push(
          `${INDENT.repeat(depth + 1)}${input.role}: → ${ref ? ref.label : "?"} #${input.subscribed}`,
        );
      }
    }
  };
  for (const start of walkStarts(pane)) walk(start, null, 0);
  return lines.join("\n");
}

function midpoint(points: Point[]): Point {
  if (points.length % 2 === 1) return points[(points.length - 1) / 2];
  const a = points[points.length / 2 - 1];
  const b = points[points.length / 2];
  return { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
}
