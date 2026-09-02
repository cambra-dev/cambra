// The read-only CodeMirror 6 source editor plus its interactivity.
//
// All interactivity is a pure client-side lookup over the snapshot, routed
// through the store's offset bridge and per-pane indices:
//   - hover tooltips: hovered pos -> tightest IR node -> label/type(s)/provenance
//     (anchored on the post-inference pane, which carries resolved types)
//   - goto-definition: Ctrl/Cmd-click a use-site -> jump the selection to its def
//   - diagnostic squiggles: the `lint` facet, driven by `diagnostics[]`
//   - selection highlight: a StateField that marks the resolved source spans,
//     distinguishing the primary anchor span from transitively-linked spans
//
// A source selection is `{ kind: "source", from, to }` over source bytes, taken
// from CodeMirror's own selection: a click leaves a caret (`from === to`) and a
// drag leaves a range. The store reseeds every pane from it, so all panes light
// up. Squiggles work on the degraded snapshot too (no IR, but diagnostics
// present).

import { EditorState, StateEffect, StateField } from "@codemirror/state";
import {
  Decoration,
  type DecorationSet,
  EditorView,
  drawSelection,
  hoverTooltip,
  lineNumbers,
  type Tooltip,
} from "@codemirror/view";
import { type Diagnostic as CMDiagnostic, linter } from "@codemirror/lint";

import type { Indices } from "./indices";
import type { OffsetMap } from "./offsets";
import { SOURCE_PANE, type Resolved, type Selection, type Store } from "./store";
import type { RewriteInfo } from "./types";

// The data a hover tooltip renders at a byte offset: the tightest enclosing
// node's label, its type set (`typesAt`), its rewrite tag, and — if the position
// is a use-site — the name of the definition it resolves to (the goto-def
// affordance). Null when no node encloses the offset. Pure (no DOM / no CM), so
// it is unit-tested directly; the CM `hoverTooltip` closure calls it.
export interface HoverPayload {
  label: string;
  types: string[];
  // The node's rewrite tag, or null for a lowering root.
  rewritten: RewriteInfo | null;
  gotoDefName: string | null;
}

export function hoverPayloadAt(
  anchor: Indices,
  _offsets: OffsetMap,
  byte: number,
): HoverPayload | null {
  const nodeId = anchor.tightestNodeAt(byte);
  if (nodeId === null) return null;
  const node = anchor.nodeById.get(nodeId);
  if (!node) return null;
  const def = anchor.definitionAt(byte);
  return {
    label: node.label,
    types: anchor.typesAt(byte),
    rewritten: node.rewritten,
    gotoDefName: def ? def.name : null,
  };
}

// The selection a source-side click produces, as a caret at one byte. With
// `mods.goto` set (Ctrl/Cmd) on a use-site it is the goto-definition jump — a
// caret at the def-site's start — and otherwise a caret at the clicked byte.
// Pure, so the decision is unit-tested without CM geometry. `anchor` may be
// undefined on a degraded snapshot.
export function resolveSourceClick(
  anchor: Indices | undefined,
  byte: number,
  mods: { goto: boolean },
): Selection {
  if (mods.goto && anchor) {
    const def = anchor.definitionAt(byte);
    if (def) return { kind: "source", from: def.defSpan.start, to: def.defSpan.start };
  }
  return { kind: "source", from: byte, to: byte };
}

export interface HighlightSpan {
  from: number;
  to: number;
  primary: boolean;
}

// A StateEffect carrying the char-offset spans (or null) to highlight.
const setHighlights = StateEffect.define<HighlightSpan[] | null>();

const primaryMark = Decoration.mark({ class: "cm-sel-node" });
const linkedMark = Decoration.mark({ class: "cm-link-node" });

type Interval = { from: number; to: number };

/** Overlapping and touching intervals joined into one, ascending. */
function merge(xs: Interval[]): Interval[] {
  const out: Interval[] = [];
  for (const x of [...xs].sort((a, b) => a.from - b.from || a.to - b.to)) {
    if (x.to <= x.from) continue;
    const last = out[out.length - 1];
    if (last && x.from <= last.to) last.to = Math.max(last.to, x.to);
    else out.push({ from: x.from, to: x.to });
  }
  return out;
}

/** `a` minus `b`, both already merged and ascending. */
function subtract(a: Interval[], b: Interval[]): Interval[] {
  const out: Interval[] = [];
  let j = 0;
  for (const iv of a) {
    let from = iv.from;
    while (j < b.length && b[j].to <= from) j += 1;
    for (let k = j; k < b.length && b[k].from < iv.to; k += 1) {
      if (b[k].from > from) out.push({ from, to: Math.min(b[k].from, iv.to) });
      from = Math.max(from, b[k].to);
      if (from >= iv.to) break;
    }
    if (from < iv.to) out.push({ from, to: iv.to });
  }
  return out;
}

/**
 * The highlight spans as a **partition** of the text: no offset is covered
 * twice, and a primary region wins over a linked one.
 *
 * The marks are translucent, so a doubly-covered offset paints its colour twice
 * and reads as a third shade nobody chose. That is not hypothetical: a source
 * click seeds every pane's tightest node, and the panes disagree about extent —
 * clicking the `if` in `txn_multi_read` gives `post-inference` the statement and
 * the two downstream panes the enclosing `with` block, two primary spans
 * nesting one inside the other. Flattening first is what makes the rendered
 * shade mean "primary" or "linked" rather than "however many spans happened to
 * land here".
 */
export function flattenHighlights(spans: HighlightSpan[]): HighlightSpan[] {
  const primary = merge(spans.filter((s) => s.primary));
  const linked = subtract(
    merge(spans.filter((s) => !s.primary)),
    primary,
  );
  return [
    ...primary.map((iv) => ({ ...iv, primary: true })),
    ...linked.map((iv) => ({ ...iv, primary: false })),
  ].sort((a, b) => a.from - b.from || a.to - b.to);
}

const highlightField = StateField.define<DecorationSet>({
  create() {
    return Decoration.none;
  },
  update(deco, tr) {
    let next = deco.map(tr.changes);
    for (const e of tr.effects) {
      if (e.is(setHighlights)) {
        if (!e.value || e.value.length === 0) {
          next = Decoration.none;
        } else {
          // Flattened first, so no offset carries two translucent marks; the
          // result is already sorted by `from`, which `Decoration.set` needs.
          const ranges = flattenHighlights(e.value).map((s) =>
            (s.primary ? primaryMark : linkedMark).range(s.from, s.to),
          );
          next = ranges.length === 0 ? Decoration.none : Decoration.set(ranges, true);
        }
      }
    }
    return next;
  },
  provide: (f) => EditorView.decorations.from(f),
});

export class SourceView {
  readonly view: EditorView;
  private readonly store: Store;
  // The post-inference pane's indices, used for hover types + goto-def. May be
  // undefined on a degraded snapshot (no panes); interactions then degrade.
  private readonly anchor: Indices | undefined;

  constructor(parent: HTMLElement, store: Store) {
    this.store = store;
    const { offsets, snapshot } = store;
    this.anchor = store.sourceAnchorPaneId
      ? store.indicesFor(store.sourceAnchorPaneId)
      : undefined;
    const anchor = this.anchor;

    // Diagnostic squiggles via the lint facet. A static source: we return the
    // snapshot's diagnostics regardless of doc state (the doc never changes).
    const diagnosticsLinter = linter(() => {
      const out: CMDiagnostic[] = [];
      for (const d of snapshot.diagnostics) {
        if (!d.span) continue;
        const from = offsets.byteToChar(d.span.start);
        const to = offsets.byteToChar(d.span.end);
        out.push({
          from,
          to: to > from ? to : from + 1,
          severity: d.severity === "error" ? "error" : "warning",
          message: d.message,
          source: d.stage,
        });
      }
      return out;
    });

    // Hover tooltip: hovered pos -> tightest node -> label / type set / prov,
    // over the post-inference pane.
    const hover = hoverTooltip((_view, pos): Tooltip | null => {
      if (!anchor) return null;
      const byte = offsets.charToByte(pos);
      const payload = hoverPayloadAt(anchor, offsets, byte);
      if (!payload) return null;

      // The node span is only needed to position the tooltip range; the
      // rendered content all comes from the pure `payload`.
      const node = anchor.nodeById.get(anchor.tightestNodeAt(byte)!);
      const def = anchor.definitionAt(byte);
      // The narrowest span is the first one a node carries.
      const nodeSpan = node?.spans[0];
      const start = offsets.byteToChar(nodeSpan ? nodeSpan.start : byte);
      const end = nodeSpan ? offsets.byteToChar(nodeSpan.end) : pos;

      return {
        pos: start,
        end,
        above: true,
        create() {
          const dom = document.createElement("div");
          dom.className = "cm-hover";
          const label = dom.appendChild(document.createElement("div"));
          label.className = "cm-hover-label";
          label.textContent = payload.label;
          if (payload.types.length > 0) {
            const ty = dom.appendChild(document.createElement("div"));
            ty.className = "cm-hover-type";
            ty.textContent = payload.types.join(" | ");
          }
          if (payload.rewritten) {
            const prov = dom.appendChild(document.createElement("div"));
            prov.className = "cm-hover-prov";
            // Inert richer rendering of the native rewrite tag: pass · nature ·
            // label (this replaced an earlier flat provenance string).
            const { via, nature, label: rwLabel } = payload.rewritten;
            prov.textContent = `${via} · ${nature} · ${rwLabel}`;
          }
          // Discoverable goto-def: a clickable link when this position is a
          // use-site that resolves to a definition (complements Ctrl/Cmd-click).
          if (payload.gotoDefName !== null && def) {
            const link = dom.appendChild(document.createElement("button"));
            link.type = "button";
            link.className = "cm-hover-gotodef";
            link.textContent = `→ jump to definition of ${payload.gotoDefName}`;
            // mousedown (not click) so it fires before the tooltip is torn down
            // by the pointer leaving the hovered range.
            link.addEventListener("mousedown", (e) => {
              e.preventDefault();
              e.stopPropagation();
              store.setSelection(resolveSourceClick(anchor, byte, { goto: true }));
            });
          }
          return { dom };
        },
      };
    });

    // Ctrl/Cmd-click a use-site -> goto-definition (the IDE/LSP-standard
    // gesture), which selects the def-site so all panes follow. Only that
    // gesture is handled here: a plain click and a drag both land as an
    // ordinary CodeMirror selection, which `selectionSync` below picks up.
    const interactions = EditorView.domEventHandlers({
      mousedown: (event, view) => {
        if (event.button !== 0) return false;
        if (!event.ctrlKey && !event.metaKey) return false;
        const pos = view.posAtCoords({ x: event.clientX, y: event.clientY });
        if (pos === null) return false;
        const byte = offsets.charToByte(pos);
        const selection = resolveSourceClick(anchor, byte, { goto: true });
        // Only a jump that actually landed elsewhere is consumed. Consuming it
        // keeps CodeMirror from placing a caret at the clicked byte, which
        // would re-enter `selectionSync` and overwrite the jump. A modified
        // click over a non-use falls through to the ordinary path.
        if (selection?.kind === "source" && selection.from !== byte) {
          store.setSelection(selection);
          event.preventDefault();
          return true;
        }
        return false;
      },
    });

    // CodeMirror owns the selection: it paints the drag and reports the range
    // even under `editable: false`, so the gesture needs no mouse handling of
    // its own and keyboard selection (shift+arrow) arrives the same way.
    //
    // Deferred through a microtask because `renderSelection` dispatches back
    // into this view, and CodeMirror refuses a dispatch made while an update is
    // in progress. The reply carries no selection change, so it does not
    // re-enter this listener.
    //
    // A pointer selection is left alone while the button is down: snapping
    // mid-drag would move the end of the range the reader is still dragging.
    // `mouseup` below snaps once the gesture is finished. A keyboard selection
    // has no such window, so it snaps as it arrives.
    const selectionSync = EditorView.updateListener.of((update) => {
      if (!update.selectionSet) return;
      const range = update.state.selection.main;
      const from = offsets.charToByte(range.from);
      const to = offsets.charToByte(range.to);
      queueMicrotask(() => store.setSelection({ kind: "source", from, to }, SOURCE_PANE));
    });

    const state = EditorState.create({
      doc: snapshot.source.text,
      extensions: [
        lineNumbers(),
        // CodeMirror draws no caret in non-editable content, so nothing showed
        // where the reader clicked; `drawSelection` draws both the caret and
        // the selection itself, and puts their colours under this app's CSS.
        drawSelection(),
        EditorState.readOnly.of(true),
        EditorView.editable.of(false),
        EditorView.lineWrapping,
        highlightField,
        diagnosticsLinter,
        hover,
        interactions,
        selectionSync,
      ],
    });
    this.view = new EditorView({ state, parent });

    // Re-highlight the resolved source spans whenever the selection changes.
    store.subscribe((resolved) => this.renderSelection(resolved));
  }

  /** Reflect the resolved selection as source-span highlights. */
  private renderSelection(resolved: Resolved): void {
    const spans = resolved.result.sourceSpans;
    const pointedAt = resolved.pointedAt;
    if (spans.length === 0 && pointedAt === null) {
      this.view.dispatch({ effects: setHighlights.of(null) });
      return;
    }

    // Call on the OffsetMap object: `byteToChar` reads `this.byteAt`, so a
    // destructured `const { byteToChar } = ...` would lose its binding and throw.
    const offsets = this.store.offsets;
    const mark = (from: number, to: number, primary: boolean): HighlightSpan => ({
      from: offsets.byteToChar(from),
      to: offsets.byteToChar(to),
      primary,
    });

    // Strong is what the reader pointed at, and nothing else — never a node's
    // extent. Every span the resolution reached is a trace, including the one
    // the pointed-at bytes sit inside; `flattenHighlights` subtracts the strong
    // region out of them, so the token reads as itself and the statement around
    // it as what it resolved to.
    const highlights: HighlightSpan[] = [];
    if (pointedAt !== null) highlights.push(mark(pointedAt.from, pointedAt.to, true));
    for (const span of spans) highlights.push(mark(span.start, span.end, false));

    // Not when the selection was made here: the caret is already where the
    // reader put it, and scrolling under a drag fights the gesture. A jump —
    // goto-definition, or a click in another pane — carries a different origin
    // and does move the editor.
    const effects: StateEffect<unknown>[] = [setHighlights.of(highlights)];
    if (resolved.origin !== SOURCE_PANE && highlights.length > 0) {
      const focus = highlights.reduce((a, b) => (b.from < a.from ? b : a));
      effects.push(EditorView.scrollIntoView(focus.from, { y: "start" }));
    }
    this.view.dispatch({ effects });
  }

}
