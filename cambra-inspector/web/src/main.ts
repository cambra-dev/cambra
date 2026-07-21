// Cambra program-inspector frontend — multi-pane (interactive, snapshot-first).
//
// On load it fetches `/api/snapshot` once and builds a `Store` (the source +
// per-stage indices + a shared, cross-stage selection). It then renders an
// N-pane layout:
//   - the program source in a read-only CodeMirror 6 editor, with hover types,
//     Ctrl/Cmd-click goto-def, diagnostic squiggles, and the resolved selection
//     highlight (see sourceView.ts);
//   - one collapsible, cross-linked IR tree per pipeline stage (treeView.ts),
//     ordered upstream -> downstream (pre-inference, post-inference,
//     post-desugar);
//   - or — on a degraded/failed snapshot — a diagnostics list in place of the
//     trees. Squiggles still render in the editor in the degraded case.
//
// Every interaction is a pure client-side lookup over the snapshot the client
// already loaded: zero round-trips, offline-capable. The shared selection in
// the store is the cross-pane link — a click anywhere resolves to a highlight
// set in every pane via the stage link graph (links.ts).

import "./style.css";
import { Store } from "./store";
import { SourceView } from "./sourceView";
import { TreeView } from "./treeView";
import { validateSnapshot } from "./wireValidate";
import type { Diagnostic, Snapshot, Span } from "./types";

function el(tag: string, className?: string, text?: string): HTMLElement {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

// Cambra `Span`s are UTF-8 *byte* offsets; for the diagnostics list we show
// ariadne-style `line:col` positions computed against the encoded byte stream.
export function byteLineStarts(text: string): number[] {
  const enc = new TextEncoder();
  const starts = [0];
  let byte = 0;
  for (const ch of text) {
    byte += enc.encode(ch).length;
    if (ch === "\n") starts.push(byte);
  }
  return starts;
}

export function lineCol(offset: number, starts: number[]): string {
  let line = 0;
  for (let i = 0; i < starts.length && starts[i] <= offset; i++) line = i;
  return `${line + 1}:${offset - starts[line] + 1}`;
}

export function formatSpan(span: Span | null, starts: number[]): string {
  return span ? `${lineCol(span.start, starts)}–${lineCol(span.end, starts)}` : "no span";
}

export function renderDiagnostics(
  parent: HTMLElement,
  diagnostics: Diagnostic[],
  lineStarts: number[],
): void {
  const box = el("div", "diagnostics");
  if (diagnostics.length === 0) {
    box.appendChild(el("div", "empty", "No diagnostics, but the IR is unavailable."));
    parent.appendChild(box);
    return;
  }
  for (const d of diagnostics) {
    const card = el("div", `diag ${d.severity}`);
    card.appendChild(el("div", "diag-head", `${d.severity} · ${d.stage}`));
    card.appendChild(el("div", "diag-msg", d.message));
    const loc = el("div", "diag-span", formatSpan(d.span, lineStarts));
    if (d.span) loc.title = `bytes ${d.span.start}..${d.span.end}`;
    card.appendChild(loc);
    box.appendChild(card);
  }
  parent.appendChild(box);
}

function renderHeader(parent: HTMLElement, snap: Snapshot): void {
  const header = el("div", "header");
  header.appendChild(el("span", "title", "Cambra Inspector"));
  header.appendChild(el("span", "name", snap.source.name));

  const failed = snap.meta.snapshotKind === "failed";
  header.appendChild(el("span", `badge${failed ? " failed" : ""}`, snap.meta.snapshotKind));

  // The meta.tick: null seam — M1 is the program, with no execution/values.
  header.appendChild(el("span", "badge", "static (no values)"));
  parent.appendChild(header);
}

// One pane (header title + optional badge + scrollable body). Returns the body
// element so the caller can mount a SourceView / TreeView into it.
function renderPane(
  panels: HTMLElement,
  paneClass: string,
  title: string,
  badge?: string,
): HTMLElement {
  const panel = el("div", `panel ${paneClass}`);
  const head = el("div", "panel-title");
  head.appendChild(el("span", "panel-title-text", title));
  if (badge) head.appendChild(el("span", "pane-badge", badge));
  panel.appendChild(head);
  const body = el("div", "panel-body");
  panel.appendChild(body);
  panels.appendChild(panel);
  return body;
}

export function renderApp(root: HTMLElement, store: Store): void {
  const snap = store.snapshot;
  root.replaceChildren();
  renderHeader(root, snap);

  const panels = el("div", "panels");
  root.appendChild(panels);

  const sourceBody = renderPane(panels, "source", "Source");

  // A degraded snapshot (failed compile) ships no stages: show diagnostics in
  // place of the IR panes. Squiggles still render in the editor below.
  const failed = snap.meta.snapshotKind === "failed" || store.stages.length === 0;

  // Source first (the editor lays out against its panel's final size). The
  // source view wires hover/goto-def/squiggles/selection over the store; the
  // squiggle path works even when there are no stages (degraded snapshot).
  new SourceView(sourceBody, store);

  if (failed) {
    const diagBody = renderPane(panels, "tree", "Diagnostics");
    renderDiagnostics(diagBody, snap.diagnostics, byteLineStarts(snap.source.text));
    return;
  }

  // One tree pane per stage, ordered upstream -> downstream. Holes-kind stages
  // (still hole-typed, pre-inference) carry a badge mirroring the
  // static-no-values one.
  for (const stage of store.stages) {
    const holes = stage.kind === "holes";
    const body = renderPane(
      panels,
      "tree",
      stage.label,
      holes ? "pre-inference (holes)" : undefined,
    );
    if (stage.ir) new TreeView(body, store, stage.id, stage.ir);
  }
}

async function main(): Promise<void> {
  const root = document.getElementById("app");
  if (!root) return;
  try {
    const resp = await fetch("/api/snapshot");
    if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
    // Validate the wire contract up front: a drifted backend surfaces as a
    // clear path-naming error here, not a confusing downstream crash.
    const snap = validateSnapshot(await resp.json());
    renderApp(root, new Store(snap));
  } catch (e) {
    root.replaceChildren(el("div", "fatal", `Failed to load /api/snapshot: ${String(e)}`));
  }
}

void main();
