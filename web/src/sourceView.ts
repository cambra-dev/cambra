// The read-only CodeMirror 6 source editor plus its interactivity.
//
// All interactivity is a pure client-side lookup over the snapshot, routed
// through the store's offset bridge and per-pane indices:
//   - hover tooltips: hovered pos -> tightest IR node -> label/type(s)/provenance
//     (anchored on the post-inference pane, which carries resolved types)
//   - goto-definition: Ctrl/Cmd-click a use-site -> jump the selection to its def
//   - diagnostic squiggles: `diagnostics[]`, set on the view once at mount
//   - selection highlight: a StateField that marks the resolved source spans,
//     distinguishing the primary anchor span from transitively-linked spans
//
// A plain source click selects `{ kind: "source", byteOffset }`; the store
// reseeds every pane's tightest node from that offset, so all panes light up.
// Squiggles work on the degraded snapshot too (no IR, but diagnostics present).

import { EditorState, StateEffect, StateField } from "@codemirror/state";
import {
  Decoration,
  type DecorationSet,
  EditorView,
  highlightActiveLine,
  hoverTooltip,
  lineNumbers,
  type Tooltip,
} from "@codemirror/view";
import { type Diagnostic as CMDiagnostic, setDiagnostics } from "@codemirror/lint";

import type { Indices } from "./indices";
import type { OffsetMap } from "./offsets";
import type { Resolved, Selection, Store } from "./store";
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

// The selection a source-side click produces. With `mods.goto` set (Ctrl/Cmd)
// on a use-site, it is the goto-definition jump (a source selection at the
// def-site's start); otherwise a plain source selection at the clicked byte.
// Pure, so the decision is unit-tested without CM geometry; the CM `mousedown`
// handler calls it. `anchor` may be undefined on a degraded snapshot.
export function resolveSourceClick(
  anchor: Indices | undefined,
  byte: number,
  mods: { goto: boolean },
): Selection {
  if (mods.goto && anchor) {
    const def = anchor.definitionAt(byte);
    if (def) return { kind: "source", byteOffset: def.defSpan.start };
  }
  return { kind: "source", byteOffset: byte };
}

interface HighlightSpan {
  from: number;
  to: number;
  primary: boolean;
}

// A StateEffect carrying the char-offset spans (or null) to highlight.
const setHighlights = StateEffect.define<HighlightSpan[] | null>();

const primaryMark = Decoration.mark({ class: "cm-sel-node" });
const linkedMark = Decoration.mark({ class: "cm-link-node" });

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
          // CodeMirror requires ranges sorted by `from` (ties: startSide).
          const ranges = e.value
            .filter((s) => s.to > s.from)
            .sort((a, b) => a.from - b.from || a.to - b.to)
            .map((s) => (s.primary ? primaryMark : linkedMark).range(s.from, s.to));
          next = Decoration.set(ranges, true);
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

    // Diagnostic squiggles. The snapshot's diagnostics are fixed and the
    // document is read-only, so they are computed here and set on the view
    // below. `linter()` is the usual route and does not fit a constant source:
    // it re-lints on a 750 ms debounce, so the squiggles arrive that late and
    // its timer dispatches into the view after the caller has dropped it.
    const diagnostics: CMDiagnostic[] = [];
    for (const d of snapshot.diagnostics) {
      if (!d.span) continue;
      const from = offsets.byteToChar(d.span.start);
      const to = offsets.byteToChar(d.span.end);
      diagnostics.push({
        from,
        to: to > from ? to : from + 1,
        severity: d.severity === "error" ? "error" : "warning",
        message: d.message,
        source: d.stage,
      });
    }

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

    // Source-side click, on the primary (left) button:
    //   - Ctrl/Cmd-click a use-site -> goto-definition (the IDE/LSP-standard
    //     gesture); selects the def-site as a source selection so all panes
    //     follow.
    //   - plain click -> select the source byte offset (the store reseeds each
    //     pane's tightest node), without suppressing the editor's own cursor.
    const interactions = EditorView.domEventHandlers({
      mousedown: (event, view) => {
        if (event.button !== 0) return false;
        const pos = view.posAtCoords({ x: event.clientX, y: event.clientY });
        if (pos === null) return false;
        const byte = offsets.charToByte(pos);
        const goto = event.ctrlKey || event.metaKey;
        const selection = resolveSourceClick(anchor, byte, { goto });
        store.setSelection(selection);
        // A goto-def jump landed elsewhere than the clicked byte: suppress CM's
        // own ctrl/cmd-click handling and consume the event. A plain click lets
        // the editor place its cursor / select text.
        if (selection?.kind === "source" && selection.byteOffset !== byte) {
          event.preventDefault();
          return true;
        }
        return false;
      },
    });

    const state = EditorState.create({
      doc: snapshot.source.text,
      extensions: [
        lineNumbers(),
        highlightActiveLine(),
        EditorState.readOnly.of(true),
        EditorView.editable.of(false),
        EditorView.lineWrapping,
        highlightField,
        hover,
        interactions,
      ],
    });
    this.view = new EditorView({ state, parent });
    // `setDiagnostics` installs the lint state field alongside the diagnostics,
    // so this one synchronous dispatch is the whole squiggle mechanism.
    this.view.dispatch(setDiagnostics(this.view.state, diagnostics));

    // Re-highlight the resolved source spans whenever the selection changes.
    store.subscribe((resolved) => this.renderSelection(resolved));
  }

  /** Reflect the resolved selection as source-span highlights. */
  private renderSelection(resolved: Resolved): void {
    const spans = resolved.result.sourceSpans;
    if (spans.length === 0) {
      this.view.dispatch({ effects: setHighlights.of(null) });
      return;
    }

    // The primary span(s): the source spans of the per-pane primary anchors.
    const primaryKeys = new Set<string>();
    for (const [paneId, nodeId] of resolved.primaryByPane) {
      if (nodeId === null) continue;
      const span = this.store.indicesFor(paneId)?.nodeById.get(nodeId)?.spans[0];
      if (span) primaryKeys.add(`${span.start}:${span.end}`);
    }

    // Call on the OffsetMap object: `byteToChar` reads `this.byteAt`, so a
    // destructured `const { byteToChar } = ...` would lose its binding and throw.
    const offsets = this.store.offsets;
    const highlights: HighlightSpan[] = spans.map((span) => ({
      from: offsets.byteToChar(span.start),
      to: offsets.byteToChar(span.end),
      primary: primaryKeys.has(`${span.start}:${span.end}`),
    }));

    // Scroll to the first primary span (or the first span if none is primary).
    const focus = highlights.find((h) => h.primary) ?? highlights[0];
    this.view.dispatch({
      effects: [setHighlights.of(highlights), EditorView.scrollIntoView(focus.from, { y: "center" })],
    });
  }
}
