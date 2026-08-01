// One collapsible IR tree pane, cross-linked to the other panes via the store.
//
// A `TreeView` renders a single stage's IR tree. Forward: clicking a node row
// selects `{ kind: "node", stageId, nodeId }`, which the store resolves to a
// highlight set per stage. Reverse: when the resolved selection changes (from a
// click in any pane), this pane highlights *its* slice — the primary node (if
// the anchor lives in this stage) strongly, transitively-linked nodes lightly —
// and expands ancestors so they are visible.

import type { Resolved, Store } from "./store";
import type { InspectNode } from "./types";

// Auto-expand the tree to this depth; deeper nodes start collapsed but usable.
const DEFAULT_EXPAND_DEPTH = 2;

/**
 * The B5 hole→resolved-type tooltip text, e.g. `` `_` resolves to `Int` `` or
 * `` `_` resolves to `Int | String` `` for a mono fan-out set. Returns null when
 * there is nothing to show (no resolved types, or no local hole type) — only
 * holes-stage (pre-inference) nodes carry resolved types. Pure (no DOM) so it
 * is unit-tested directly.
 */
export function resolvedTypeTooltip(
  localType: string | null,
  resolved: string[],
): string | null {
  if (localType === null || resolved.length === 0) return null;
  return `\`${localType}\` resolves to \`${resolved.join(" | ")}\``;
}

function el(tag: string, className?: string, text?: string): HTMLElement {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

// Per-node view handles, so a selection change can drive highlight + expand
// without re-rendering the whole tree.
interface NodeHandle {
  row: HTMLElement;
  parentId: number | null;
  expand: () => void;
}

export class TreeView {
  private readonly store: Store;
  private readonly stageId: string;
  private readonly handles = new Map<number, NodeHandle>();
  private markedRows: HTMLElement[] = [];

  constructor(parent: HTMLElement, store: Store, stageId: string, ir: InspectNode) {
    this.store = store;
    this.stageId = stageId;
    const root = el("div", "tree-root");
    root.appendChild(this.renderNode(ir, null, 0, null));
    parent.appendChild(root);

    store.subscribe((resolved) => this.renderSelection(resolved));
  }

  private renderNode(
    node: InspectNode,
    edge: string | null,
    depth: number,
    parentId: number | null,
  ): HTMLElement {
    const container = el("div", "tree-node");
    const row = el("div", "tree-row selectable");
    const hasChildren = node.children.length > 0;

    const twisty = el("span", `twisty${hasChildren ? "" : " leaf"}`);
    row.appendChild(twisty);

    if (edge !== null) {
      row.appendChild(el("span", "edge-label", `${edge}:`));
    }
    row.appendChild(el("span", "node-label", node.label));

    const type = node.type;
    if (type !== null) {
      row.appendChild(el("span", "node-type", `: ${type}`));
    }
    // B5: in a holes-kind (pre-inference) pane the type is a hole (`_`/`?N`);
    // show what inference resolves it to downstream (a set on mono fan-out) on *hover*
    // rather than inline — the inline `→ T` glyph was confusable with the
    // function-type arrow `⇒` and partial-type arrow `⇀`.
    const resolved = this.store.resolvedTypesFor(this.stageId, node.nodeId);
    const tooltipText = resolvedTypeTooltip(type, resolved);
    if (tooltipText !== null) {
      this.attachResolvedTooltip(row, tooltipText);
    }
    row.appendChild(el("span", "node-id", `#${node.nodeId}`));
    container.appendChild(row);

    // Clicking the row selects this node in this stage (the cross-link). The
    // twisty toggles expand/collapse; we stop it from also selecting so the two
    // affordances stay distinct.
    row.addEventListener("click", (e) => {
      if (e.target === twisty) return;
      this.store.setSelection({ kind: "node", stageId: this.stageId, nodeId: node.nodeId });
    });

    if (!hasChildren) {
      twisty.textContent = "·";
      this.handles.set(node.nodeId, { row, parentId, expand: () => {} });
      return container;
    }

    const childrenBox = el("div", "tree-children");
    for (const child of node.children) {
      childrenBox.appendChild(this.renderNode(child.node, child.edge, depth + 1, node.nodeId));
    }
    container.appendChild(childrenBox);

    let expanded = depth < DEFAULT_EXPAND_DEPTH;
    const apply = () => {
      twisty.textContent = expanded ? "▾" : "▸";
      childrenBox.classList.toggle("collapsed", !expanded);
    };
    apply();
    twisty.classList.add("clickable");
    twisty.addEventListener("click", (e) => {
      e.stopPropagation();
      expanded = !expanded;
      apply();
    });

    this.handles.set(node.nodeId, {
      row,
      parentId,
      expand: () => {
        if (!expanded) {
          expanded = true;
          apply();
        }
      },
    });
    return container;
  }

  // A custom styled hover tooltip for a row's resolved-type text, mirroring the
  // source pane's `.cm-hover` tooltip (see style.css). Plain DOM, positioned at
  // the pointer; appended to <body> so the panel's `overflow:auto` doesn't clip
  // it. One tooltip at a time; torn down on leave.
  private attachResolvedTooltip(row: HTMLElement, text: string): void {
    let tip: HTMLElement | null = null;
    const place = (e: MouseEvent): void => {
      if (!tip) return;
      tip.style.left = `${e.clientX + 12}px`;
      tip.style.top = `${e.clientY + 12}px`;
    };
    const remove = (): void => {
      tip?.remove();
      tip = null;
    };
    row.addEventListener("mouseenter", (e) => {
      remove();
      tip = el("div", "node-resolved-tooltip", text);
      document.body.appendChild(tip);
      place(e);
    });
    row.addEventListener("mousemove", place);
    row.addEventListener("mouseleave", remove);
  }

  private expandAncestors(nodeId: number): void {
    const handle = this.handles.get(nodeId);
    if (!handle) return;
    let pid = handle.parentId;
    while (pid !== null) {
      const ph = this.handles.get(pid);
      if (!ph) break;
      ph.expand();
      pid = ph.parentId;
    }
  }

  private renderSelection(resolved: Resolved): void {
    for (const row of this.markedRows) row.classList.remove("selected", "linked");
    this.markedRows = [];

    const highlights = resolved.result.highlightsByStage.get(this.stageId);
    if (!highlights || highlights.size === 0) return;
    const primary = resolved.primaryByStage.get(this.stageId) ?? null;

    for (const nodeId of highlights) {
      const handle = this.handles.get(nodeId);
      if (!handle) continue;
      this.expandAncestors(nodeId);
      handle.row.classList.add(nodeId === primary ? "selected" : "linked");
      this.markedRows.push(handle.row);
    }

    // Scroll to the primary node if it lives here, else any highlighted node.
    const scrollTo = primary !== null && this.handles.has(primary)
      ? primary
      : highlights.values().next().value;
    if (scrollTo !== undefined) {
      this.handles.get(scrollTo)?.row.scrollIntoView({ block: "nearest" });
    }
  }
}
