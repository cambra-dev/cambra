// Cambra program-inspector frontend — multi-pane (interactive, snapshot-first).
//
// On load it fetches `/api/snapshot` once and builds a `Store` (the source +
// per-pane indices + a shared, cross-pane selection). It then renders an
// N-pane layout:
//   - the program source in a read-only CodeMirror 6 editor, with hover types,
//     Ctrl/Cmd-click goto-def, diagnostic squiggles, and the resolved selection
//     highlight (see sourceView.ts);
//   - one collapsible, cross-linked IR tree per tree-shaped pipeline pane
//     (treeView.ts), ordered upstream -> downstream;
//   - or — on a degraded/failed snapshot — a diagnostics list in place of the
//     trees. Squiggles still render in the editor in the degraded case.
//
// `describePanes` names that set once, and both the layout and the header's
// filter menu (paneMenu.ts) iterate it. A hidden pane keeps its view.
//
// Every interaction is a pure client-side lookup over the snapshot the client
// already loaded: zero round-trips, offline-capable. The shared selection in
// the store is the cross-pane link — a click anywhere resolves to a highlight
// set in every pane via the pane link graph (links.ts).

import "./style.css";
import { copyToClipboard } from "./clipboard";
import { renderPaneMenu } from "./paneMenu";
import {
  PaneVisibility,
  browserStorage,
  loadHiddenPanes,
  saveHiddenPanes,
} from "./paneVisibility";
import { Store } from "./store";
import { SourceView } from "./sourceView";
import { OperatorView, serializeOperatorGraph } from "./operatorView";
import { TreeView, serializeTree } from "./treeView";
import { type FrameSource, LiveStore, connectLive } from "./liveStore";
import { renderLiveMenu } from "./liveMenu";
import { LiveView, livePanelState, serializeLivePanel } from "./liveView";
import { validateSnapshot } from "./wireValidate";
import { isIrPane } from "./types";
import type { Diagnostic, Snapshot, Span } from "./types";

function el(tag: string, className?: string, text?: string): HTMLElement {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

// Cambra `Span`s are UTF-8 *byte* offsets; for the diagnostics list we show
// ariadne-style `line:col` positions computed against the encoded byte stream.
/**
 * How an inspect gesture names itself: the construct and the line it sits on,
 * e.g. `Var(words): L8`.
 *
 * The construct rather than the operator, because that is what the reader
 * pointed at — one gesture becomes several operators, and naming it by any one
 * of them would name something they never chose.
 */
export function tagLabel(store: Store, nodeId: number, lineStarts: number[]): string {
  const anchorId = store.sourceAnchorPaneId;
  const node = anchorId ? store.indicesFor(anchorId)?.nodeById.get(nodeId) : undefined;
  const label = node?.label ?? `#${nodeId}`;
  const start = node?.spans[0]?.start;
  if (start === undefined) return label;
  // The line alone, not `line:col`: two gestures on one line are the same
  // construct often enough that a column would split one tag into several.
  let line = 0;
  for (let i = 0; i < lineStarts.length && (lineStarts[i] ?? 0) <= start; i++) line = i;
  return `${label}: L${line + 1}`;
}

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

function renderHeader(
  parent: HTMLElement,
  snap: Snapshot,
  panes: readonly PaneDescriptor[],
  visibility: PaneVisibility,
): void {
  const header = el("div", "header");
  header.appendChild(el("span", "title", "Cambra Inspector"));
  header.appendChild(el("span", "name", snap.source.name));

  const failed = snap.meta.payloadKind === "failed";
  header.appendChild(el("span", `badge${failed ? " failed" : ""}`, snap.meta.payloadKind));

  // The payload describes the program, with no execution and no values.
  header.appendChild(el("span", "badge", "static (no values)"));

  header.appendChild(el("span", "spacer"));
  renderPaneMenu(header, panes, visibility);
  parent.appendChild(header);
}

export interface PaneDescriptor {
  // Stable identity: "source", "diagnostics", or a stage id. Keys visibility
  // and its persisted set.
  id: string;
  // The pane's one name — its title bar and its row in the filter menu.
  label: string;
  badge?: string;
  // The `.panel` modifier class: "source" or "tree".
  paneClass: string;
  // The pane's plain-text rendering, produced on click rather than at render
  // time — serializing every tree on load would cost the whole IR for a button
  // most sessions never press.
  copyText: () => string;
  // Build the pane's view into its body, once. A view that cannot lay itself
  // out while its panel is `display: none` returns a callback to run whenever
  // the pane is revealed.
  mount: (body: HTMLElement) => (() => void) | void;
}

/**
 * Every pane the layout renders, in order: the source pane, then one per
 * pipeline stage — or, on a degraded snapshot, a single diagnostics pane. A
 * stage is drawn by `TreeView` or, for the operator graph, by `OperatorView`.
 *
 * Source is first and mounted first, and that ordering is load-bearing:
 * CodeMirror lays out against its panel's size, so the editor is built while
 * its panel is the only one in the row.
 */
export function describePanes(
  store: Store,
  live?: LiveStore,
  // Pin the operators a position reaches, and reveal the values pane so the
  // reader sees the result of the gesture they just made.
  onInspect?: (nodeId: number, operators: readonly number[]) => void,
): PaneDescriptor[] {
  const snap = store.snapshot;
  const panes: PaneDescriptor[] = [
    {
      id: "source",
      label: "Source",
      paneClass: "source",
      // The editor's document is built from this same string, but read it from
      // the snapshot: `Text` normalizes line breaks on construction, so a CRLF
      // source would come back from CodeMirror with the CRs stripped.
      copyText: () => snap.source.text,
      mount: (body) => {
        const view = new SourceView(body, store, onInspect);
        // A revealed editor has never measured against a real box, and it does
        // not reliably measure itself: CodeMirror's ResizeObserver path drops a
        // resize within 75ms of a docView update, and a selection made while
        // hidden leaves a scrollTarget that defeats its hidden-editor bailout.
        return () => view.view.requestMeasure();
      },
    },
  ];

  // A degraded snapshot (failed compile) ships no panes: diagnostics take the
  // place of the IR panes. Squiggles still render in the editor.
  if (snap.meta.payloadKind === "failed" || store.panes.length === 0) {
    const lineStarts = byteLineStarts(snap.source.text);
    panes.push({
      id: "diagnostics",
      label: "Diagnostics",
      paneClass: "tree",
      copyText: () => serializeDiagnostics(snap.diagnostics, lineStarts),
      mount: (body) => renderDiagnostics(body, snap.diagnostics, lineStarts),
    });
    return panes;
  }

  for (const pane of store.panes) {
    // The operator pane holds a dataflow graph — a forest of subscription trees, and
    // inputs rather than children — so it gets its own view.
    if (!isIrPane(pane)) {
      panes.push({
        id: pane.id,
        label: pane.label,
        badge: "dataflow",
        paneClass: "tree",
        copyText: () => serializeOperatorGraph(pane),
        mount: (body) => {
          if (pane.nodes.length > 0) new OperatorView(body, store, pane);
        },
      });
      continue;
    }
    // Holes-kind panes (still hole-typed, pre-inference) carry a badge
    // mirroring the static-no-values one.
    const holes = pane.kind === "holes";
    const root = pane.root;
    const nodesOf = () => (pane.nodes.length > 0 ? store.indicesFor(pane.id)?.nodeById : undefined);
    panes.push({
      id: pane.id,
      label: pane.label,
      badge: holes ? "pre-inference (holes)" : undefined,
      paneClass: "tree",
      copyText: () => {
        const nodes = nodesOf();
        return nodes ? serializeTree(root, nodes) : "";
      },
      mount: (body) => {
        if (pane.nodes.length > 0) new TreeView(body, store, pane.id, root);
      },
    });
  }
  if (live !== undefined) {
    // Hideable and remembered like any other pane. Pinning reveals it, which
    // `applyVisibility` already does on a hidden-to-visible transition.
    panes.push({
      id: "values",
      label: "Values",
      badge: "live",
      paneClass: "tree",
      copyText: () =>
        serializeLivePanel(livePanelState(live.get(), (id) => store.operatorLabel(id))),
      mount: (body) => {
        // The menu first, so it reads as this pane's toolbar above its rows.
        renderLiveMenu(body, live);
        // No origin on either selection: the gesture happened in this pane,
        // which is not one the link graph knows, so every pane should scroll to
        // what it resolved — the same reason goto-def and the operator pane's
        // reference rows pass none.
        new LiveView(body, live, (id) => store.operatorLabel(id), {
          construct: (anchorId) => {
            const paneId = store.sourceAnchorPaneId;
            if (paneId) store.setSelection({ kind: "node", paneId, nodeId: anchorId });
          },
          operator: (nodeId) => {
            // `locate`, not `node`: an operator carries the span of the
            // construct that produced it, so asking the program about it
            // answers with that whole construct. This says "go to this
            // operator" and nothing more, and the operator pane scrolls it to
            // the top because it is the only row highlighted.
            const paneId = store.liveAnchorPaneId;
            if (paneId) store.setSelection({ kind: "locate", paneId, nodeId });
          },
        });
      },
    });
  }
  return panes;
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

interface MountedPane {
  panel: HTMLElement;
  reveal: (() => void) | void;
}

// One pane: title + optional badge + copy button + scrollable body, with its
// view mounted into that body.
function renderPane(panels: HTMLElement, pane: PaneDescriptor): MountedPane {
  const panel = el("div", `panel ${pane.paneClass}`);
  // The pane's identity in the DOM, so the menu and the tests never re-derive
  // it from a class name.
  panel.dataset.paneId = pane.id;

  const head = el("div", "panel-title");
  head.appendChild(el("span", "panel-title-text", pane.label));
  if (pane.badge) head.appendChild(el("span", "pane-badge", pane.badge));
  head.appendChild(renderCopyButton(pane.copyText));
  panel.appendChild(head);

  const body = el("div", "panel-body");
  panel.appendChild(body);
  panels.appendChild(panel);

  return { panel, reveal: pane.mount(body) };
}

/**
 * A source position an embedder asks to have pinned.
 *
 * Line and column, both 1-based, because a `NodeId` is not durable: ids are
 * minted per compile, and the values pane says so where it declines to persist
 * a tag. A position in the source text survives every compile of that text,
 * which is what a deck reopening the same program needs.
 */
export interface PinRequest {
  line: number;
  col: number;
}

/**
 * Resolve `pins` against `store` and pin what they name.
 *
 * The same path the source-hover gesture takes — `tightestNodeAt` then
 * `operatorsFor` — so a configured pin and a clicked one are the same pin. A
 * position naming no operator is skipped rather than reported: a deck whose
 * program has moved on should open with fewer pins, not with an error in front
 * of an audience.
 */
export function applyPins(
  store: Store,
  live: LiveStore,
  pins: readonly PinRequest[],
  lineStarts: number[],
): number {
  const paneId = store.sourceAnchorPaneId;
  if (paneId === null) return 0;
  const anchor = store.indicesFor(paneId);
  if (!anchor) return 0;
  let pinned = 0;
  for (const pin of pins) {
    const lineStart = lineStarts[pin.line - 1];
    if (lineStart === undefined) continue;
    const nodeId = anchor.tightestNodeAt(lineStart + (pin.col - 1));
    if (nodeId === null) continue;
    const operators = store.operatorsFor(nodeId);
    if (operators.length === 0) continue;
    live.inspect(tagLabel(store, nodeId, lineStarts), nodeId, operators);
    pinned += 1;
  }
  return pinned;
}

export function renderApp(
  root: HTMLElement,
  store: Store,
  live?: LiveStore,
  config?: { hiddenPanes?: readonly string[]; pins?: readonly PinRequest[] },
): void {
  // Set once the visibility controller exists, because pinning has to reveal
  // the pane and the controller is built from the pane list this produces.
  let reveal: ((paneId: string) => void) | null = null;
  // Built once: the tag label needs a line number, and scanning the source per
  // gesture would redo work the diagnostics list already pays for.
  const lineStarts = byteLineStarts(store.snapshot.source.text);
  const onInspect = live
    ? (nodeId: number, operators: readonly number[]) => {
        live.inspect(tagLabel(store, nodeId, lineStarts), nodeId, operators);
        reveal?.("values");
      }
    : undefined;
  const panes = describePanes(store, live, onInspect);

  // A storage that throws on access degrades the filter to one session.
  const storage = browserStorage();
  // An embedder's hidden set wins over the stored one: it is asking for a
  // particular layout on this page, where the stored set is whatever the last
  // reader of some other page chose.
  const visibility = new PaneVisibility(
    panes.map((pane) => pane.id),
    config?.hiddenPanes ?? (storage ? loadHiddenPanes(storage) : []),
  );
  if (live && config?.pins?.length) applyPins(store, live, config.pins, lineStarts);

  root.replaceChildren();
  renderHeader(root, store.snapshot, panes, visibility);

  const panels = el("div", "panels");
  root.appendChild(panels);

  // Mounted in order, each panel appended before the next is built — the source
  // editor measures itself against a panel that is briefly the whole row.
  const mounted = panes.map((pane) => renderPane(panels, pane));

  // Hidden panes keep their views. Tearing one down would leak its store
  // subscription (neither view keeps the unsubscribe handle), lose every
  // expand/collapse in a tree, and come back blank — the views react to
  // selection *changes*, and `setSelection` early-returns on an equal one.
  const applyVisibility = (): void => {
    const lastVisible = panes.reduce(
      (last, pane, i) => (visibility.isVisible(pane.id) ? i : last),
      -1,
    );
    mounted.forEach(({ panel, reveal }, i) => {
      const visible = visibility.isVisible(panes[i].id);
      const wasHidden = panel.classList.contains("hidden");
      panel.classList.toggle("hidden", !visible);
      // `.panel.last-visible` drops the divider on the rightmost pane. It
      // cannot be `:last-child`: that is DOM order, so hiding the rightmost
      // pane would leave a border against the window edge.
      panel.classList.toggle("last-visible", i === lastVisible);
      if (visible && wasHidden) reveal?.();
    });
  };

  // Pinning reveals the pane: an affordance that produced no visible result
  // would read as having done nothing.
  reveal = (paneId: string) => {
    visibility.setVisible(paneId, true);
  };

  visibility.subscribe(applyVisibility);
  if (storage) {
    visibility.subscribe(() => saveHiddenPanes(storage, visibility.hiddenIds()));
  }
  applyVisibility();
}

/**
 * What an embedder may hand the inspector instead of a server.
 *
 * The bundle is a single file with no external references, so a page can inline
 * it and drive it directly — a WebAssembly host holds the snapshot and the
 * frames already, and has no origin to fetch them from. Anything absent falls
 * back to the network, which is what the `cambra` binary serves.
 */
export interface InjectedHost {
  /** The `/api/snapshot` payload, unvalidated. */
  snapshot?: unknown;
  /** Where frames come from, in place of the websocket. */
  openLive?: () => FrameSource;
  /** Pane ids to open hidden, in place of whatever the reader last chose. */
  hiddenPanes?: readonly string[];
  /** Source positions to open pinned in the values pane. */
  pins?: readonly PinRequest[];
}

declare global {
  interface Window {
    __CAMBRA__?: InjectedHost;
  }
}

/** The snapshot an embedder supplied, or the one the server has. */
async function loadSnapshot(injected: InjectedHost | undefined): Promise<unknown> {
  if (injected?.snapshot !== undefined) return injected.snapshot;
  const resp = await fetch("/api/snapshot");
  if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
  return resp.json();
}

async function main(): Promise<void> {
  const root = document.getElementById("app");
  if (!root) return;
  const injected = window.__CAMBRA__;
  try {
    // Validate the wire contract up front, whichever side supplied it: a
    // drifted backend — or a drifted embedder — surfaces as a clear
    // path-naming error here, not a confusing downstream crash.
    const snap = validateSnapshot(await loadSnapshot(injected));
    // The live channel is opened alongside the snapshot, not instead of it, and
    // its failures never reach this `catch`: a run that ended must degrade the
    // values pane, where a snapshot that would not load has nothing to show at
    // all.
    const live = new LiveStore();
    if (injected?.openLive) connectLive(live, injected.openLive);
    else connectLive(live);
    renderApp(root, new Store(snap), live, {
      hiddenPanes: injected?.hiddenPanes,
      pins: injected?.pins,
    });
  } catch (e) {
    root.replaceChildren(el("div", "fatal", `Failed to load the snapshot: ${String(e)}`));
  }
}

void main();
