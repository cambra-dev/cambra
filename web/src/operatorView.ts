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
import {
  type Detail,
  type DrawEdge,
  type DrawGraph,
  type DrawNode,
  drawGraphOf,
  isBackEdge,
} from "./graph/model";
import type { Resolved, Store } from "./store";
import type { OperatorEdge, OperatorNode, OperatorPane } from "./types";
import { isChildEdge, roleLabel, walkStarts } from "./types";

const INDENT = "    ";
const NODE_HEIGHT = 22;
const NODE_GAP = 14;
const LAYER_GAP = 28;
const PAD = 12;
const MIN_WIDTH = 66;
const MAX_WIDTH = 240;
/**
 * The box that carries a tiling: two lines, and wider.
 *
 * A tiling is 41 characters at the median against a box holding about 36, so it
 * does not fit beside a label. On its own line the box is as wide as its wider
 * line rather than as wide as their sum, which is worth about 1100px of canvas
 * on `order_ledger`. 300px and 40 characters is the knee — past it the width
 * grows faster than the prefix does.
 */
const TILED_MAX_WIDTH = 300;
const TILED_HEIGHT = 34;
const TILING_CHARS = 40;
const DETAIL_KEY = "cambra.inspector.operatorDetail.v1";

const DETAIL_TEXT: Record<Detail, string> = {
  steps: "Steps",
  operators: "Operators",
};

/** A bounded prefix of the tiling; the card carries all of it. */
function clipTiling(tiling: string): string {
  return tiling.length <= TILING_CHARS ? tiling : `${tiling.slice(0, TILING_CHARS - 1)}…`;
}

/**
 * What a tiling's constructor means.
 *
 * `SF(...)` and `Store(...)` print in the same shape and mean opposite things —
 * read one position, or fold a changelog — which is the misreading this names.
 */
function tilingGloss(tiling: string): string {
  if (tiling.startsWith("SF(")) return "a sealed function: one value per position of the domain";
  if (tiling.startsWith("Store(")) {
    return "a changelog: fold the ticks to read a value, never index one";
  }
  if (tiling.startsWith("CF(")) return "curried: two domains before the value";
  if (tiling.startsWith("agg(")) return "an accumulator, not a stream";
  return "a single cell";
}

/**
 * The reader's detail level, remembered per browser.
 *
 * A reading preference rather than a property of the program, so it survives a
 * recompile. Storage can throw outright where site data is blocked, which is why
 * both halves are guarded.
 */
function readDetail(): Detail {
  try {
    return localStorage.getItem(DETAIL_KEY) === "operators" ? "operators" : "steps";
  } catch {
    return "steps";
  }
}

function writeDetail(detail: Detail): void {
  try {
    localStorage.setItem(DETAIL_KEY, detail);
  } catch {
    // A preference that cannot be stored is still a preference for this session.
  }
}

const SVG_NS = "http://www.w3.org/2000/svg";

/**
 * Width of a label at the pane's font.
 *
 * Canvas measurement where there is one, and a per-character estimate where
 * there is not. jsdom has no 2D context, and a layout that could not run under
 * it could not be asserted on.
 *
 * The size tracks `--fs-sm`, which is what `.graph-node` renders at. It cannot
 * read the token — the measurement happens before any node is in the document —
 * so it is duplicated here, and a change to the scale belongs in both places.
 * Measuring too wide only leaves slack inside the box; too narrow clips.
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
  /** Where each tree of the forest starts; the pane opens pointed at one. */
  private readonly starts: readonly number[];
  private readonly canvas: HTMLElement;
  private readonly handles = new Map<number, Handle>();
  private marked: HTMLElement[] = [];
  private pending: Resolved | null = null;
  private drawn = false;
  /** Rising with each `draw`, so a slower layout cannot paint over a newer one. */
  private generation = 0;
  private card: HTMLElement | null = null;
  private cardPinned = false;

  /**
   * `detail` pins the level; without it the pane opens at the reader's
   * remembered one. A test that asserts on a particular drawing passes it.
   */
  constructor(
    parent: HTMLElement,
    store: Store,
    pane: OperatorPane,
    layout?: GraphLayout,
    detail?: Detail,
  ) {
    this.store = store;
    this.paneId = pane.id;
    this.pane = pane;
    this.detail = detail ?? readDetail();
    this.graph = drawGraphOf(pane, this.detail);
    this.layout = layout ?? new ElkLayout();
    this.starts = walkStarts(pane.nodes);

    parent.appendChild(this.detailControl());
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

  /** Whether this box draws its tiling on a second line. */
  private showsTiling(node: DrawNode): boolean {
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

  /** Redraw at another level. A relayout is full: ELK layered has no incremental mode. */
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
    await this.draw();
    this.renderSelection(this.store.getResolved());
  }

  /** Lay the graph out and draw it. Resolves when the pane is on screen. */
  async draw(): Promise<void> {
    const generation = ++this.generation;
    const sized = this.graph.nodes.map((n) => {
      const head = measure(n.label) + measure(`#${n.id}`) + 26;
      if (!this.showsTiling(n)) {
        const chips = n.chips.reduce((a, c) => a + Math.min(64, measure(c.text)) + 9, 0);
        return {
          id: String(n.id),
          width: Math.min(MAX_WIDTH, Math.max(MIN_WIDTH, head + chips)),
          height: NODE_HEIGHT,
        };
      }
      const type = measure(clipTiling(n.tiling!)) + 18;
      return {
        id: String(n.id),
        width: Math.min(TILED_MAX_WIDTH, Math.max(MIN_WIDTH, Math.max(head, type))),
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
    // A level changed while this layout ran; the newer one owns the canvas.
    if (generation !== this.generation) return;
    this.paint(placed, forward);
    this.drawn = true;
    if (this.pending) {
      this.renderSelection(this.pending);
      this.pending = null;
    }
  }

  /**
   * Expand a box: everything it could not fit.
   *
   * A box is 22 or 34 pixels tall and at most 300 wide, so it truncates — a long
   * tiling, a `Filter` carrying four constants, the fan-out branches suppressed
   * onto its outgoing edges. Hover shows all of it and double-click pins it,
   * because reading a six-member list means moving the pointer.
   */
  private describe(node: DrawNode): HTMLElement {
    const card = el("div", "graph-card");
    const line = (text: string, cls?: string) => card.appendChild(el("div", cls, text));
    if (node.members.length > 1) {
      line(`${node.label} — stands for ${node.members.length} operators`, "graph-card-head");
      node.members.forEach((id, i) => {
        const own = this.graph.nodes.find((n) => n.id === id);
        const kind = own ? own.label : (this.labelOf(id) ?? "?");
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
      const rank = order.get(String(node.id)) ?? 0;
      const div = el("div", "graph-node selectable");
      div.dataset.nodeId = String(node.id);
      div.dataset.role = node.role;
      div.style.left = `${box.x + PAD}px`;
      div.style.top = `${box.y + PAD}px`;
      div.style.width = `${box.width}px`;
      div.style.height = `${box.height}px`;
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
      for (const chip of node.chips) {
        const c = el("span", "graph-chip", chip.text);
        c.dataset.nodeId = String(chip.id);
        head.appendChild(c);
        this.handles.set(chip.id, { element: c, order: rank });
      }
      head.appendChild(el("span", "node-id", `#${node.id}`));
      if (this.showsTiling(node)) {
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
      this.canvas.appendChild(div);
      this.handles.set(node.id, { element: div, order: rank });
      for (const member of node.members) this.handles.set(member, { element: div, order: rank });
      for (const fan of node.fanOuts) this.handles.set(fan, { element: div, order: rank });
    }

    // At `operators` a suppressed node draws as a glyph on the edge that
    // replaced it — the edge itself is a two-pixel target and the glyph is one a
    // reader can hit. At `steps` its producer's box carries the mark instead,
    // so the glyphs would be a second, scattered answer to the same question.
    for (const edge of this.graph.detail === "steps" ? [] : this.graph.edges) {
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
    this.canvas.addEventListener("pointerover", (event) => this.onHover(event));
    this.canvas.addEventListener("pointerleave", () => this.hideCard());
    this.canvas.addEventListener("dblclick", (event) => this.onPin(event));

    this.frameOnStart(at);
    void forward;
  }

  /**
   * Open the pane on the head of a tree rather than on the corner of the sheet.
   *
   * The sheet is as wide as the graph — thousands of pixels on a real program —
   * and the pane showing it is a few hundred. Nothing puts a node near the
   * origin: ELK orders the first layer by its own criteria, so on the demo's
   * program every leftmost node sits nine hundred pixels down and the pane
   * opened on blank canvas, which reads as a pane that failed to draw.
   *
   * The topmost walk start is the useful default: a node no value edge
   * subscribes is the head of a subscription tree, so the reader lands on a
   * source rather than in the middle of a fan. Falls back to whatever the
   * layout put topmost, for a graph whose starts are all suppressed.
   *
   * This is only the default view. `draw` applies a selection that arrived
   * before the first paint immediately afterwards, so a reader who followed a
   * link still lands on what they clicked.
   */
  private frameOnStart(at: Map<string, { x: number; y: number }>): void {
    const head =
      this.topLeftOf(this.starts, at) ??
      this.topLeftOf(this.graph.nodes.map((n) => n.id), at);
    if (head === null) return;
    // Centred across, not flush left: a start node's children fan both ways
    // under it, and a pane this narrow holds two nodes across, so hugging the
    // left edge cuts half the fan off screen.
    this.handles.get(head)?.element.scrollIntoView({ block: "start", inline: "center" });
  }

  /** The id the layout placed nearest the top-left, or null if none are drawn. */
  private topLeftOf(
    ids: readonly number[],
    at: Map<string, { x: number; y: number }>,
  ): number | null {
    let best: { id: number; x: number; y: number } | null = null;
    for (const id of ids) {
      const box = at.get(String(id));
      if (!box) continue;
      if (best === null || box.y < best.y || (box.y === best.y && box.x < best.x)) {
        best = { id, x: box.x, y: box.y };
      }
    }
    return best === null ? null : best.id;
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

  // Double-click also fires a `click`, so it moves the selection — which is the
  // selection that click would have made anyway, so the reader loses nothing.
  private onPin(event: MouseEvent): void {
    const node = this.nodeUnder(event);
    if (!node) return this.hideCard(true);
    this.showCard(node, event.clientX, event.clientY, true);
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
          `${INDENT.repeat(depth + 1)}${input.role}: → ${ref ? ref.label : "?"} #${input.subscribed}`,
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
