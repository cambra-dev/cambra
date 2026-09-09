// Render one snapshot's operator pane through the real front-end pipeline and
// report what the reader actually sees.
//
// The wire node count is not the drawn node count: `drawGraphOf` suppresses
// vertices and `OperatorView.paint` places what survives. An analysis that
// counts wire nodes is measuring the wrong graph, and a reimplementation of the
// suppression rules in another language is measuring a second implementation.
// This runs `drawGraphOf`, `ElkLayout` and `paint` themselves, under jsdom, and
// reports the DOM they produce.
//
//   npx vite-node scripts/render-graph.ts -- <snapshot.json> [--html <path>] [--quiet]
//
// `--html` writes the painted canvas markup. Stdout is a JSON report: the
// element census, the per-kind histograms of drawn and suppressed nodes, the
// drawn edges, and the placed geometry.

import { readFileSync, writeFileSync } from "node:fs";

import { JSDOM } from "jsdom";

interface Args {
  snapshot: string;
  html: string | null;
  quiet: boolean;
}

function parseArgs(argv: string[]): Args {
  const rest = argv.slice(2).filter((a) => a !== "--");
  let snapshot: string | null = null;
  let html: string | null = null;
  let quiet = false;
  for (let i = 0; i < rest.length; i++) {
    if (rest[i] === "--html") html = rest[++i] ?? null;
    else if (rest[i] === "--quiet") quiet = true;
    else snapshot = rest[i];
  }
  if (!snapshot) throw new Error("usage: render-graph.ts <snapshot.json> [--html <path>] [--quiet]");
  return { snapshot, html, quiet };
}

// jsdom must be the ambient document before `operatorView` is imported: its
// `measure` picks a canvas or an estimate at module-evaluation time.
function installDom(): void {
  const dom = new JSDOM("<!doctype html><html><body></body></html>", {
    pretendToBeVisual: true,
  });
  const g = globalThis as unknown as Record<string, unknown>;
  g.window = dom.window;
  g.document = dom.window.document;
  // Node defines `navigator` as a getter-only global; define over it.
  Object.defineProperty(globalThis, "navigator", {
    value: dom.window.navigator,
    configurable: true,
  });
  g.HTMLElement = dom.window.HTMLElement;
  g.SVGElement = dom.window.SVGElement;
  g.Element = dom.window.Element;
  g.Node = dom.window.Node;
  g.getComputedStyle = dom.window.getComputedStyle.bind(dom.window);
  g.requestAnimationFrame = (fn: FrameRequestCallback) => dom.window.setTimeout(() => fn(0), 0);
  g.cancelAnimationFrame = (id: number) => dom.window.clearTimeout(id);
}

function histogram(labels: string[]): Record<string, number> {
  const h: Record<string, number> = {};
  for (const l of labels) h[l] = (h[l] ?? 0) + 1;
  return Object.fromEntries(Object.entries(h).sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0])));
}

async function main(): Promise<void> {
  const args = parseArgs(process.argv);
  installDom();

  const { Store } = await import("../src/store");
  const { OperatorView } = await import("../src/operatorView");
  const { drawGraphOf, isBackEdge } = await import("../src/graph/model");
  const type = await import("../src/types");
  void type;

  const snapshot = JSON.parse(readFileSync(args.snapshot, "utf8"));
  const pane = snapshot.panes.find((p: { kind: string }) => p.kind === "operators");
  if (!pane) throw new Error(`${args.snapshot} has no operators pane`);

  const store = new Store(snapshot);
  const graph = drawGraphOf(pane);

  const host = document.createElement("div");
  document.body.appendChild(host);
  const view = new OperatorView(host, store, pane);
  await view.draw();

  const canvas = host.querySelector(".graph-canvas") as HTMLElement;
  const boxes = [...canvas.querySelectorAll(".graph-node")] as HTMLElement[];
  const chips = [...canvas.querySelectorAll(".graph-chip")] as HTMLElement[];
  const glyphs = [...canvas.querySelectorAll(".graph-glyph")] as HTMLElement[];
  const wires = [...canvas.querySelectorAll("path.graph-edge")] as unknown as SVGElement[];

  const byId = new Map<number, { label: string; tiling?: string | null; inputs: unknown[] }>(
    pane.nodes.map((n: { nodeId: number }) => [n.nodeId, n as never]),
  );
  const drawnIds = boxes.map((b) => Number(b.dataset.nodeId));
  const suppressedIds = pane.nodes
    .map((n: { nodeId: number }) => n.nodeId)
    .filter((id: number) => !drawnIds.includes(id));

  const report = {
    snapshot: args.snapshot,
    wire: {
      nodes: pane.nodes.length,
      edges: pane.nodes.reduce(
        (a: number, n: { inputs: unknown[] }) => a + n.inputs.length,
        0,
      ),
      kinds: histogram(pane.nodes.map((n: { label: string }) => n.label)),
    },
    drawn: {
      boxes: boxes.length,
      chips: chips.length,
      glyphs: glyphs.length,
      wires: wires.length,
      edges: graph.edges.length,
      backEdges: graph.edges.filter(isBackEdge).length,
      kinds: histogram(drawnIds.map((id) => byId.get(id)!.label)),
    },
    suppressed: {
      count: suppressedIds.length,
      kinds: histogram(suppressedIds.map((id: number) => byId.get(id)!.label)),
      asChips: chips.length,
      asGlyphs: glyphs.length,
    },
    // Every wire id must still be addressable; a nonzero count here is a bug.
    unaddressable: pane.nodes
      .map((n: { nodeId: number }) => n.nodeId)
      .filter((id: number) => graph.viewItem(id) === undefined),
    canvas: { width: canvas.style.width, height: canvas.style.height },
    drawnNodes: boxes.map((b) => ({
      id: Number(b.dataset.nodeId),
      label: byId.get(Number(b.dataset.nodeId))!.label,
      tiling: byId.get(Number(b.dataset.nodeId))!.tiling ?? null,
      role: b.dataset.role,
      x: parseFloat(b.style.left),
      y: parseFloat(b.style.top),
      width: parseFloat(b.style.width),
      chips: [...b.querySelectorAll(".graph-chip")].map((c) => ({
        id: Number((c as HTMLElement).dataset.nodeId),
        text: c.textContent,
      })),
    })),
    drawnEdges: graph.edges.map((e) => ({
      id: e.id,
      from: e.from,
      to: e.to,
      kind: e.kind,
      role: e.role,
      deferred: e.deferred,
      back: isBackEdge(e),
      suppressed: e.suppressed,
    })),
  };

  if (args.html) writeFileSync(args.html, canvas.outerHTML);
  if (!args.quiet) process.stdout.write(JSON.stringify(report, null, 2) + "\n");
}

await main();
