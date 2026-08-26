// Cambra program-inspector frontend — multi-pane (interactive, snapshot-first).
//
// On load it fetches `/api/snapshot` once and builds a `Store` (the source +
// per-pane indices + a shared, cross-pane selection). It then renders an
// N-pane layout:
//   - the program source in a read-only CodeMirror 6 editor, with hover types,
//     Ctrl/Cmd-click goto-def, diagnostic squiggles, and the resolved selection
//     highlight (see sourceView.ts);
//   - one collapsible, cross-linked IR tree per pipeline pane (treeView.ts),
//     ordered upstream -> downstream (pre-inference, post-inference,
//     post-channelize);
//   - or — on a degraded/failed snapshot — a diagnostics list in place of the
//     trees. Squiggles still render in the editor in the degraded case.
//
// Every interaction is a pure client-side lookup over the snapshot the client
// already loaded: zero round-trips, offline-capable. The shared selection in
// the store is the cross-pane link — a click anywhere resolves to a highlight
// set in every pane via the pane link graph (links.ts).

import "./style.css";
import { copyToClipboard } from "./clipboard";
import { Store } from "./store";
import { SourceView } from "./sourceView";
import { TreeView, serializeTree } from "./treeView";
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

// What the Diagnostics pane shows when the compile failed without producing a
// diagnostic. Shared so the pane and its copy text cannot say different things.
const NO_DIAGNOSTICS = "No diagnostics, but the IR is unavailable.";

/**
 * One diagnostic's three rendered lines: heading, message, span. The renderer
 * and the copy serializer both read this, so a change to either reaches both.
 * The `bytes N..M` tooltip is not here — it is a hover affordance, not text the
 * pane displays.
 */
export function diagnosticLines(d: Diagnostic, lineStarts: number[]): [string, string, string] {
  return [`${d.severity} · ${d.stage}`, d.message, formatSpan(d.span, lineStarts)];
}

/** The Diagnostics pane as plain text: each card's lines, blank line between. */
export function serializeDiagnostics(diagnostics: Diagnostic[], lineStarts: number[]): string {
  if (diagnostics.length === 0) return NO_DIAGNOSTICS;
  return diagnostics.map((d) => diagnosticLines(d, lineStarts).join("\n")).join("\n\n");
}

export function renderDiagnostics(
  parent: HTMLElement,
  diagnostics: Diagnostic[],
  lineStarts: number[],
): void {
  const box = el("div", "diagnostics");
  if (diagnostics.length === 0) {
    box.appendChild(el("div", "empty", NO_DIAGNOSTICS));
    parent.appendChild(box);
    return;
  }
  for (const d of diagnostics) {
    const [head, message, span] = diagnosticLines(d, lineStarts);
    const card = el("div", `diag ${d.severity}`);
    card.appendChild(el("div", "diag-head", head));
    card.appendChild(el("div", "diag-msg", message));
    const loc = el("div", "diag-span", span);
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

  const failed = snap.meta.payloadKind === "failed";
  header.appendChild(el("span", `badge${failed ? " failed" : ""}`, snap.meta.payloadKind));

  // The payload describes the program, with no execution and no values.
  header.appendChild(el("span", "badge", "static (no values)"));
  parent.appendChild(header);
}

export interface PaneSpec {
  // The `.panel` modifier class: "source" or "tree".
  paneClass: string;
  title: string;
  badge?: string;
  // The pane's plain-text rendering, produced on click rather than at render
  // time — serializing every tree on load would cost the whole IR for a button
  // most sessions never press.
  copyText: () => string;
}

// How long the copy button holds its post-click state before reverting.
const COPY_FEEDBACK_MS = 1200;

// The per-pane copy affordance. It reports the outcome rather than assuming
// one: `copyToClipboard` resolves false on an absent API or a refused write,
// and a silent no-op there is indistinguishable from a successful copy.
function renderCopyButton(copyText: () => string): HTMLButtonElement {
  const button = document.createElement("button");
  button.type = "button";
  button.className = "pane-copy";
  button.title = "Copy pane text";
  button.setAttribute("aria-label", "Copy pane text");
  button.textContent = "Copy";

  // Each click takes a token. A revert whose token is stale belongs to an
  // earlier click, so a second click inside the feedback window keeps its own
  // label for the full duration instead of losing it to the first one's timer.
  let latest = 0;
  button.addEventListener("click", () => {
    const token = ++latest;
    void copyToClipboard(copyText()).then((copied) => {
      button.dataset.state = copied ? "copied" : "failed";
      button.textContent = copied ? "Copied" : "Copy failed";
      setTimeout(() => {
        if (token !== latest) return;
        delete button.dataset.state;
        button.textContent = "Copy";
      }, COPY_FEEDBACK_MS);
    });
  });
  return button;
}

// One pane (header title + optional badge + copy button + scrollable body).
// Returns the body element so the caller can mount a SourceView / TreeView.
function renderPane(panels: HTMLElement, spec: PaneSpec): HTMLElement {
  const panel = el("div", `panel ${spec.paneClass}`);
  const head = el("div", "panel-title");
  head.appendChild(el("span", "panel-title-text", spec.title));
  if (spec.badge) head.appendChild(el("span", "pane-badge", spec.badge));
  head.appendChild(renderCopyButton(spec.copyText));
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

  // The editor's document is built from this same string, but read it from the
  // snapshot rather than from CodeMirror: `Text` normalizes line breaks on
  // construction, so a CRLF source would come back with the CRs stripped.
  const sourceBody = renderPane(panels, {
    paneClass: "source",
    title: "Source",
    copyText: () => snap.source.text,
  });

  // A degraded snapshot (failed compile) ships no panes: show diagnostics in
  // place of the IR panes. Squiggles still render in the editor below.
  const failed = snap.meta.payloadKind === "failed" || store.panes.length === 0;

  // Source first (the editor lays out against its panel's final size). The
  // source view wires hover/goto-def/squiggles/selection over the store; the
  // squiggle path works even when there are no panes (degraded snapshot).
  new SourceView(sourceBody, store);

  if (failed) {
    const diagBody = renderPane(panels, {
      paneClass: "tree",
      title: "Diagnostics",
      copyText: () => serializeDiagnostics(snap.diagnostics, byteLineStarts(snap.source.text)),
    });
    renderDiagnostics(diagBody, snap.diagnostics, byteLineStarts(snap.source.text));
    return;
  }

  // One tree pane per pane entry, ordered upstream -> downstream. Holes-kind
  // panes (still hole-typed, pre-inference) carry a badge mirroring the
  // static-no-values one.
  for (const pane of store.panes) {
    const holes = pane.kind === "holes";
    const body = renderPane(panels, {
      paneClass: "tree",
      title: pane.label,
      badge: holes ? "pre-inference (holes)" : undefined,
      copyText: () => {
        const nodes = store.indicesFor(pane.id)?.nodeById;
        return nodes && pane.nodes.length > 0 ? serializeTree(pane.root, nodes) : "";
      },
    });
    if (pane.nodes.length > 0) new TreeView(body, store, pane.id, pane.root);
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
