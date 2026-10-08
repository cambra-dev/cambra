// The operator pane: the subscription graph, drawn.
//
// An edge runs from a producer to the consumer that subscribed it, which is the
// direction data moves. That is the same relation the wire calls an input, read
// the other way round: an operator's inputs are the operators it subscribes.
//
// Two kinds, both on the wire. `value` is an exclusively owned subscription and
// `share` one several consumers hold. An edge wired late — the one a
// `CycleSlot` filled, carrying `deferred` — is what closes a cycle: removing
// those makes every graph acyclic, so they are withheld from the layout and
// drawn as back edges rather than broken by the engine's heuristic.
//
// Two operator kinds are suppressed rather than drawn; see `./graph/model`. A
// suppressed node keeps its id on whatever replaced it, because every id in the
// pane is a cross-pane selection target.
//
// Two detail levels: `operators` draws one box per operator the suppressions
// leave, and `steps` merges recurring plumbing into composites (`./graph/rules`).
// Hovering a box expands what it could not fit; double-click pins that card.

import type { GraphLayout, Placed, PlacedNode, Point } from "./graph/layout";
import {
  type Detail,
  type DrawEdge,
  type DrawGraph,
  type DrawNode,
  drawGraphOf,
  isBackEdge,
} from "./graph/model";
import { browserStorage } from "./paneVisibility";
import type { Resolved, Store } from "./store";
import type { OperatorEdge, OperatorNode, OperatorPane } from "./types";
import { isChildEdge, roleLabel, walkStarts } from "./types";
import { el } from "./dom";

const INDENT = "    ";
const NODE_HEIGHT = 22;
const NODE_GAP = 14;
const LAYER_GAP = 28;
const PAD = 12;
/** Width a node's tiling may take before it is cut with an ellipsis, in px. */
const MAX_TILING = 110;
/**
 * How far a back edge bows out past the widest node in the layers it spans.
 *
 * Reserved in the canvas's width as well as used to route the bow. The SVG
 * paints outside its box (`overflow: visible`), but painted overflow is ink
 * only — it does not extend the scrollable region of the pane, so a bow drawn
 * past the reserved width is unreachable once the graph is wider than the pane.
 */
const BOW = 26;
const MIN_WIDTH = 66;
const MAX_WIDTH = 240;
/**
 * The box that carries a tiling on a line of its own, at `steps`.
 *
 * A tiling is 41 characters at the median against a box holding about 36, so it
 * does not fit beside a label. On its own line the box is as wide as its wider
 * line rather than as wide as their sum. 300px and 40 characters is the knee:
 * past it the width grows faster than the prefix does.
 */
const TILED_MAX_WIDTH = 300;
const TILED_HEIGHT = 34;
const TILING_CHARS = 40;
const DETAIL_KEY = "cambra-inspector:operator-detail:v1";

const DETAIL_TEXT: Record<Detail, string> = {
  steps: "Steps",
  operators: "Operators",
};

/** A bounded prefix of the tiling; the card carries all of it. */
function clipTiling(tiling: string): string {
  return tiling.length <= TILING_CHARS ? tiling : `${tiling.slice(0, TILING_CHARS - 1)}…`;
}

/**
 * What a tiling's outermost constructor means, after `Display for Tiling`.
 *
 * `Fn(…)` and `Store(…)` print in the same shape and mean opposite things —
 * read one position, or fold a changelog — which is the misreading this names.
 */
function tilingGloss(tiling: string): string {
  if (tiling.startsWith("Fn(")) return "a function: one value per position of each domain";
  if (tiling.startsWith("Store(")) {
    return "a changelog: fold the ticks to read a value, never index one";
  }
  if (tiling.startsWith("agg(")) return "an accumulator, not a stream";
  if (tiling.startsWith("{")) return "a record: one tile per field";
  return "a single cell";
}

/**
 * The reader's detail level, remembered per browser.
 *
 * A reading preference rather than a property of the program, so it survives a
 * recompile. A storage that cannot be used leaves the default.
 */
function readDetail(): Detail {
  try {
    return browserStorage()?.getItem(DETAIL_KEY) === "operators" ? "operators" : "steps";
  } catch {
    return "steps";
  }
}

function writeDetail(detail: Detail): void {
  try {
    browserStorage()?.setItem(DETAIL_KEY, detail);
  } catch {
    // A preference that cannot be stored still holds for this pane.
  }
}

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

function svg(tag: string, attrs: Record<string, string>): SVGElement {
  const node = document.createElementNS(SVG_NS, tag);
  for (const [k, v] of Object.entries(attrs)) node.setAttribute(k, v);
  return node;
}

// `Restrict [0,100] #4021`, or `Sink(main) #4103` for a boundary node, which has
// no tiling.
function rowText(node: OperatorNode): string {
  return node.tiling === null || node.tiling === undefined
    ? `${node.label} #${node.nodeId}`
    : `${node.label} ${node.tiling} #${node.nodeId}`;
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
  private readonly pane: OperatorPane;
  private graph: DrawGraph;
  private detail: Detail;
  private readonly layout: GraphLayout;
  private readonly canvas: HTMLElement;
  private readonly handles = new Map<number, Handle>();
  private marked: HTMLElement[] = [];
  private pending: Resolved | null = null;
  private drawn = false;
  /** Bumped per `draw`, so a layout that resolves after a later one is dropped. */
  private generation = 0;
  private card: HTMLElement | null = null;
  private cardPinned = false;

  /**
   * The engine is injected rather than chosen here, which is what confines it
   * to the one module that names it — see `./graph/NOTICE`. `detail` pins the
   * level; without it the pane opens at the reader's remembered one.
   */
  constructor(
    parent: HTMLElement,
    store: Store,
    pane: OperatorPane,
    layout: GraphLayout,
    detail?: Detail,
  ) {
    this.store = store;
    this.paneId = pane.id;
    this.pane = pane;
    this.detail = detail ?? readDetail();
    this.graph = drawGraphOf(pane, this.detail);
    this.layout = layout;

    parent.appendChild(this.detailControl());
    this.canvas = el("div", "graph-canvas");
    parent.appendChild(this.canvas);
    // On the canvas, which outlives every drawing: a listener bound per draw
    // accumulates one handler per paint.
    this.canvas.addEventListener("click", (event) => this.onClick(event));
    this.canvas.addEventListener("pointerover", (event) => this.onHover(event));
    this.canvas.addEventListener("pointerleave", () => this.hideCard());
    this.canvas.addEventListener("dblclick", (event) => this.onPin(event));

    store.subscribe((resolved) => {
      // A selection can land before the first layout resolves. Hold the last
      // one: a highlight for a node with no element yet is not a highlight
      // that should be dropped.
      if (!this.drawn) this.pending = resolved;
      else this.renderSelection(resolved);
    });

    void this.draw().catch((error: unknown) => this.drawAsList(error));
  }

  /** Whether this box draws its tiling on a second line rather than inline. */
  private showsTilingBelow(node: DrawNode): boolean {
    return this.detail === "steps" && node.tiling !== null;
  }

  /** The header control: how much of the graph to draw. */
  private detailControl(): HTMLElement {
    const bar = el("div", "graph-detail");
    bar.appendChild(el("span", "graph-detail-label", "Detail"));
    for (const level of ["steps", "operators"] as const) {
      const button = el("button", "graph-detail-option", DETAIL_TEXT[level]);
      button.dataset.detail = level;
      button.setAttribute("aria-pressed", String(level === this.detail));
      button.addEventListener("click", () => void this.setDetail(level, bar));
      bar.appendChild(button);
    }
    return bar;
  }

  /** Redraw at another level. The relayout is full: ELK layered has no incremental mode. */
  private async setDetail(detail: Detail, bar: HTMLElement): Promise<void> {
    if (detail === this.detail) return;
    this.detail = detail;
    writeDetail(detail);
    for (const b of bar.querySelectorAll<HTMLElement>("[data-detail]")) {
      b.setAttribute("aria-pressed", String(b.dataset.detail === detail));
    }
    this.graph = drawGraphOf(this.pane, detail);
    this.hideCard(true);
    this.drawn = false;
    // The held selection is the one the reader had, so the new drawing shows it.
    this.pending = this.store.getResolved();
    await this.draw().catch((error: unknown) => this.drawAsList(error));
  }

  /** Lay the graph out and draw it. Resolves when the pane is on screen. */
  async draw(): Promise<void> {
    const generation = ++this.generation;
    const sized = this.graph.nodes.map((n) => {
      const head = measure(n.label) + measure(`#${n.id}`) + 26;
      const chips = n.chips.reduce((a, c) => a + Math.min(64, measure(c.text)) + 9, 0);
      if (!this.showsTilingBelow(n)) {
        const inline = n.tiling === null ? 0 : Math.min(MAX_TILING, measure(n.tiling)) + 5;
        return {
          id: String(n.id),
          width: Math.min(MAX_WIDTH, Math.max(MIN_WIDTH, head + inline + chips)),
          height: NODE_HEIGHT,
        };
      }
      const below = measure(clipTiling(n.tiling!)) + 18;
      return {
        id: String(n.id),
        width: Math.min(TILED_MAX_WIDTH, Math.max(MIN_WIDTH, head + chips, below)),
        height: TILED_HEIGHT,
      };
    });
    const forward = this.graph.edges.filter((e) => !isBackEdge(e));
    const placed = await this.layout.run({
      nodes: sized,
      edges: forward.map((e) => ({ id: e.id, source: String(e.from), target: String(e.to) })),
      nodeGap: NODE_GAP,
      layerGap: LAYER_GAP,
    });
    if (generation !== this.generation) return;
    this.paint(placed);
    this.finish();
  }

  /**
   * The pane with no layout: one row per operator, in wire order.
   *
   * A rejected layout would otherwise leave `drawn` false for good, and every
   * later selection would queue into `pending` that nothing reads — a pane that
   * is silently empty where every other pane degrades visibly. The rows carry
   * the ids the drawing would have, so the pane stays a selection target and a
   * cross-pane link still lands on it.
   */
  private drawAsList(error: unknown): void {
    console.error("The operator pane could not lay its graph out", error);
    this.canvas.textContent = "";
    this.handles.clear();
    this.canvas.classList.add("graph-listed");
    this.canvas.style.width = "";
    this.canvas.style.height = "";
    this.canvas.appendChild(
      el("div", "graph-failed", "Layout failed — the operators are listed in wire order."),
    );
    this.graph.nodes.forEach((node, index) => {
      this.canvas.appendChild(this.nodeElement(node, index));
    });
    // At `operators` a suppressed operator is drawn on the edge that replaced
    // it, and there are no edges here. Every id in the pane is a selection
    // target, so it gets a row of its own instead. At `steps` its producer's
    // box already answers for it.
    const tail = this.graph.nodes.length;
    for (const edge of this.detail === "steps" ? [] : this.graph.edges) {
      for (const id of edge.suppressed) {
        const row = el("div", "graph-node selectable");
        row.dataset.nodeId = String(id);
        row.dataset.role = "suppressed";
        row.appendChild(el("span", "graph-strip"));
        const where = `on the ${edge.kind} edge #${edge.from} → #${edge.to}`;
        row.appendChild(el("span", "node-label", where));
        row.appendChild(el("span", "node-id", `#${id}`));
        this.canvas.appendChild(row);
        this.handles.set(id, { element: row, order: tail });
      }
    }
    this.finish();
  }

  /**
   * Expand a box: everything it could not fit.
   *
   * A box is 22 or 34 pixels tall and at most 300 wide, so it truncates a long
   * tiling, a `Filter` carrying four constants, and the fan-out branches
   * suppressed onto its outgoing edges. Hover shows all of it and double-click
   * pins it, because reading a six-member list means moving the pointer.
   */
  private describe(node: DrawNode): HTMLElement {
    const card = el("div", "graph-card");
    const line = (text: string, cls?: string) => card.appendChild(el("div", cls, text));
    if (node.members.length > 1) {
      line(`${node.label} — stands for ${node.members.length} operators`, "graph-card-head");
      node.members.forEach((id, i) => {
        const kind = this.labelOf(id) ?? "?";
        line(`  #${id} ${kind}${i === 0 ? "   (representative)" : ""}`, "graph-card-member");
        // A constant is an operand of one operator, so it hangs off the member
        // that reads it rather than sitting in one list nobody can attribute.
        for (const chip of node.chips.filter((c) => c.owner === id)) {
          line(`      #${chip.id} ${chip.text}`, "graph-card-chip");
        }
      });
    } else {
      line(`${node.label} #${node.id}`, "graph-card-head");
      for (const chip of node.chips) line(`  #${chip.id} ${chip.text}`, "graph-card-chip");
    }
    if (node.tiling !== null) {
      // The tiling is the shape of the tile every consumer receives, so it is
      // also the payload type of every edge leaving this box.
      line(`emits ${node.tiling}`, "graph-card-tiling");
      line(`  ${tilingGloss(node.tiling)}`, "graph-card-note");
    }
    if (node.fanOuts.length) {
      line(`fans out to ${node.fanOuts.map((f) => `#${f}`).join(", ")}`, "graph-card-note");
    }
    return card;
  }

  private labelOf(id: number): string | undefined {
    return this.pane.nodes.find((n) => n.nodeId === id)?.label;
  }

  private showCard(node: DrawNode, x: number, y: number, pin: boolean): void {
    this.hideCard(true);
    const card = this.describe(node);
    if (pin) card.classList.add("pinned");
    document.body.appendChild(card);
    const rect = card.getBoundingClientRect();
    const vw = document.documentElement.clientWidth;
    const vh = document.documentElement.clientHeight;
    card.style.left = `${Math.max(4, Math.min(x + 14, vw - rect.width - 8))}px`;
    card.style.top = `${Math.max(4, Math.min(y + 14, vh - rect.height - 8))}px`;
    this.card = card;
    this.cardPinned = pin;
  }

  private hideCard(force = false): void {
    if (this.cardPinned && !force) return;
    this.card?.remove();
    this.card = null;
    this.cardPinned = false;
  }

  /** The drawn box answering for the element under `event`, if any. */
  private nodeUnder(event: Event): DrawNode | undefined {
    const owner = (event.target as HTMLElement | null)?.closest<HTMLElement>("[data-node-id]");
    if (!owner) return undefined;
    // A chip or a member is drawn inside a box; a glyph rides an edge and has
    // no box to expand.
    const own = Number(owner.dataset.nodeId);
    const item = this.graph.viewItem(own);
    const id = item && (item.kind === "chip" || item.kind === "member") ? item.host : own;
    return this.graph.nodes.find((n) => n.id === id);
  }

  private onHover(event: PointerEvent): void {
    if (this.cardPinned) return;
    const node = this.nodeUnder(event);
    if (!node) return this.hideCard();
    this.showCard(node, event.clientX, event.clientY, false);
  }

  // Double-click also fires a `click`, so it moves the selection — the one that
  // click would have made anyway, so the reader loses nothing.
  private onPin(event: MouseEvent): void {
    const node = this.nodeUnder(event);
    if (!node) return this.hideCard(true);
    this.showCard(node, event.clientX, event.clientY, true);
  }

  /** Accept the drawing and release the selection held while it was in flight. */
  private finish(): void {
    this.drawn = true;
    if (this.pending) {
      this.renderSelection(this.pending);
      this.pending = null;
    }
  }

  private paint(placed: Placed): void {
    this.canvas.textContent = "";
    this.handles.clear();
    this.canvas.classList.remove("graph-listed");
    // A back edge bows `BOW` past the widest node it joins, so the canvas
    // reserves it; without a cycle there is none to reserve.
    const bowed = this.graph.edges.some(isBackEdge) ? BOW : 0;
    this.canvas.style.width = `${placed.width + PAD * 2 + bowed}px`;
    this.canvas.style.height = `${placed.height + PAD * 2}px`;

    const at = new Map(placed.nodes.map((n) => [n.id, n]));
    const wires = svg("g", { class: "graph-wires" });
    const sheet = svg("svg", {
      width: String(placed.width + PAD * 2),
      height: String(placed.height + PAD * 2),
    });
    sheet.appendChild(arrowheads(this.paneId));
    sheet.appendChild(wires);
    this.canvas.appendChild(sheet);

    const routed = new Map(placed.edges.map((e) => [e.id, e.points]));
    const route = new Map<string, Point[]>();
    for (const edge of this.graph.edges) {
      const points = isBackEdge(edge) ? backEdge(edge, at) : routed.get(edge.id);
      if (!points || points.length < 2) continue;
      route.set(edge.id, points);
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
      const div = this.nodeElement(node, order.get(String(node.id)) ?? 0);
      div.style.left = `${box.x + PAD}px`;
      div.style.top = `${box.y + PAD}px`;
      div.style.width = `${box.width}px`;
      div.style.height = `${box.height}px`;
      this.canvas.appendChild(div);
    }

    // At `operators` a suppressed node draws as a glyph on the edge that
    // replaced it: the edge itself is a two-pixel target, and the glyph is one a
    // reader can hit. At `steps` its producer's box carries the mark instead.
    for (const edge of this.detail === "steps" ? [] : this.graph.edges) {
      const points = route.get(edge.id);
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
  }

  /**
   * One operator's box, and the handles for every id drawn inside it.
   *
   * `order` is reading order, which decides which of several highlights a
   * selection scrolls to.
   */
  private nodeElement(node: DrawNode, order: number): HTMLElement {
    const div = el("div", "graph-node selectable");
    div.dataset.nodeId = String(node.id);
    div.dataset.role = node.role;
    if (node.members.length > 1) {
      // "Stands for N operators", drawn as a stack of cards rather than a
      // multiplier: "x2" beside a name reads as two of that name. It sits
      // outside the flow, so it never takes width from the label.
      div.classList.add("composite");
      div.appendChild(el("span", "graph-count", String(node.members.length)));
    }
    div.appendChild(el("span", "graph-strip"));
    const head = el("span", "graph-head");
    head.appendChild(el("span", "node-label", node.label));
    const below = this.showsTilingBelow(node);
    if (node.tiling !== null && !below) head.appendChild(el("span", "node-type", node.tiling));
    for (const chip of node.chips) {
      const c = el("span", "graph-chip", chip.text);
      c.dataset.nodeId = String(chip.id);
      head.appendChild(c);
      this.handles.set(chip.id, { element: c, order });
    }
    head.appendChild(el("span", "node-id", `#${node.id}`));
    if (below) {
      const body = el("span", "graph-body");
      body.appendChild(head);
      body.appendChild(el("span", "graph-tiling", clipTiling(node.tiling!)));
      div.appendChild(body);
    } else {
      div.appendChild(head);
    }
    // A fan-out happens at the producer, so one mark on the producer names
    // every branch reading it.
    if (node.fanOuts.length) div.appendChild(el("span", "graph-fan"));
    this.handles.set(node.id, { element: div, order });
    for (const member of node.members) this.handles.set(member, { element: div, order });
    for (const fan of node.fanOuts) this.handles.set(fan, { element: div, order });
    return div;
  }

  private wire(edge: DrawEdge, points: Point[]): SVGElement {
    const d = points
      .map((p, i) => `${i === 0 ? "M" : "L"}${p.x + PAD} ${p.y + PAD}`)
      .join(" ");
    const back = isBackEdge(edge);
    const cls = `graph-edge graph-edge-${edge.kind}${back ? " graph-edge-back" : ""}`;
    const head = back ? "back" : edge.kind === "share" ? "share" : "value";
    const path = svg("path", { d, class: cls, "marker-end": `url(#${arrowId(this.paneId, head)})` });
    (path as SVGElement & { dataset: DOMStringMap }).dataset.edgeId = edge.id;
    (path as SVGElement & { dataset: DOMStringMap }).dataset.from = String(edge.from);
    return path;
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
      edge === null ? "" : `${roleLabel(edge.role)}: ${edge.deferred ? "late " : ""}`;
    lines.push(INDENT.repeat(depth) + prefix + rowText(node));
    for (const input of node.inputs) {
      if (isChildEdge(input)) {
        walk(input.subscribed, input, depth + 1);
      } else {
        const ref = nodeById.get(input.subscribed);
        lines.push(
          `${INDENT.repeat(depth + 1)}${roleLabel(input.role)}: → ${ref ? ref.label : "?"} #${input.subscribed}`,
        );
      }
    }
  };
  for (const start of walkStarts(pane.nodes)) walk(start, null, 0);
  return lines.join("\n");
}

function midpoint(points: Point[]): Point {
  if (points.length % 2 === 1) return points[(points.length - 1) / 2];
  const a = points[points.length / 2 - 1];
  const b = points[points.length / 2];
  return { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
}

/**
 * A back edge, bowed out to the right so it reads as a return.
 *
 * It leaves the producer's right side and enters the consumer's, so the
 * arrowhead lands on a border rather than under a box. The bow clears every
 * node whose box overlaps the vertical span it crosses, not only its two ends:
 * nodes paint over the edge sheet, so a bow through a wider node between them
 * would be hidden. A self-loop — a store whose body is a branch of its own fan
 * — leaves and enters the one box a third of its height apart.
 */
function backEdge(edge: DrawEdge, at: Map<string, PlacedNode>): Point[] | undefined {
  const a = at.get(String(edge.from));
  const b = at.get(String(edge.to));
  if (!a || !b) return undefined;
  const self = a === b;
  const from = { x: a.x + a.width, y: a.y + a.height * (self ? 2 / 3 : 1 / 2) };
  const to = { x: b.x + b.width, y: b.y + b.height * (self ? 1 / 3 : 1 / 2) };
  const top = Math.min(a.y, b.y);
  const bottom = Math.max(a.y + a.height, b.y + b.height);
  let right = Math.max(from.x, to.x);
  for (const n of at.values()) {
    if (n.y < bottom && n.y + n.height > top) right = Math.max(right, n.x + n.width);
  }
  const bow = right + BOW;
  return [from, { x: bow, y: from.y }, { x: bow, y: to.y }, to];
}

// Marker ids are document-global, so each pane names its own rather than
// resolving to another pane's.
const arrowId = (paneId: string, kind: string) => `graph-arrow-${paneId}-${kind}`;

/** One arrowhead per edge class, coloured by the same tokens as the stroke. */
function arrowheads(paneId: string): SVGElement {
  const defs = svg("defs", {});
  for (const kind of ["value", "share", "back"]) {
    const marker = svg("marker", {
      id: arrowId(paneId, kind),
      class: `graph-arrow graph-arrow-${kind}`,
      viewBox: "0 0 8 8",
      refX: "7",
      refY: "4",
      markerWidth: "7",
      markerHeight: "7",
      markerUnits: "userSpaceOnUse",
      orient: "auto-start-reverse",
    });
    marker.appendChild(svg("path", { d: "M0 0.5 L7.5 4 L0 7.5 z" }));
    defs.appendChild(marker);
  }
  return defs;
}
