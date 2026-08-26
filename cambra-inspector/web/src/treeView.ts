// One collapsible IR tree pane, cross-linked to the other panes via the store.
//
// A `TreeView` renders a single pane's node table as a tree, walking it from
// `root` through the child edges. Forward: clicking a node row selects
// `{ kind: "node", paneId, nodeId }`, which the store resolves to a highlight
// set per pane. Reverse: when the resolved selection changes (from a click in
// any pane), this pane highlights *its* slice — the primary node (if the anchor
// lives in this pane) strongly, transitively-linked nodes lightly — and expands
// ancestors so they are visible.

import type { Resolved, Store } from "./store";
import type { IrNode } from "./types";

// Auto-expand the tree to this depth; deeper nodes start collapsed but usable.
const DEFAULT_EXPAND_DEPTH = 2;

/**
 * The B5 hole→resolved-type tooltip text, e.g. `` `_` resolves to `Int` `` or
 * `` `_` resolves to `Int | String` `` for a mono fan-out set. Returns null when
 * there is nothing to show (no resolved types, or no local hole type) — only
 * holes-pane (pre-inference) nodes carry resolved types. Pure (no DOM) so it
 * is unit-tested directly.
 */
export function resolvedTypeTooltip(
  localType: string | null,
  resolved: string[],
): string | null {
  if (localType === null || resolved.length === 0) return null;
  return `\`${localType}\` resolves to \`${resolved.join(" | ")}\``;
}

// Indentation per depth level in `serializeTree`.
const TREE_INDENT = "  ";

/**
 * A pane's node table as plain text — one line per rendered row, `TREE_INDENT`
 * per depth level, no trailing newline. This is what the pane's copy button
 * yields.
 *
 * A line is the row's spans joined by a single space, which is what the row's
 * flex `gap` renders: `` 0: Lit(Int(1)) : Int@1 #13 ``. The twisty is dropped
 * because the indentation already carries the structure, and because it states
 * a collapse state the text has no notion of — the whole tree is serialized
 * regardless of what is expanded, so a copy does not depend on click history
 * (`renderSelection` expands ancestors as a side effect of selecting).
 *
 * Refinement-predicate children are walked like any other. `renderNode` gives
 * them rows, so filtering on the `predicate` flag here would silently make the
 * copy disagree with the pane it claims to reproduce. It walks from `root`
 * through the child edges with the same on-path guard `renderNode` uses, so a
 * node reached from several positions appears once per position, exactly as the
 * pane draws it.
 */
export function serializeTree(root: number, nodeById: Map<number, IrNode>): string {
  const lines: string[] = [];
  const walk = (id: number, edge: string | null, depth: number, onPath: Set<number>): void => {
    const node = nodeById.get(id);
    if (!node) return;
    const parts: string[] = [];
    if (edge !== null) parts.push(`${edge}:`);
    parts.push(node.label);
    parts.push(`: ${node.type}`);
    parts.push(`#${node.nodeId}`);
    lines.push(TREE_INDENT.repeat(depth) + parts.join(" "));
    const childPath = new Set(onPath).add(id);
    // The same derived label `renderNode` draws: a value child's index in
    // `children`, and nothing for a predicate.
    for (const [i, child] of node.children.entries()) {
      if (onPath.has(child.id)) continue;
      walk(child.id, child.predicate ? null : String(i), depth + 1, childPath);
    }
  };
  walk(root, null, 0, new Set());
  return lines.join("\n");
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
  private readonly paneId: string;
  private readonly nodeById: Map<number, IrNode>;
  private readonly handles = new Map<number, NodeHandle>();
  private markedRows: HTMLElement[] = [];

  constructor(parent: HTMLElement, store: Store, paneId: string, rootId: number) {
    this.store = store;
    this.paneId = paneId;
    this.nodeById = store.indicesFor(paneId)?.nodeById ?? new Map();
    const root = el("div", "tree-root");
    const rootNode = this.nodeById.get(rootId);
    if (rootNode) root.appendChild(this.renderNode(rootNode, null, 0, null, new Set()));
    parent.appendChild(root);

    store.subscribe((resolved) => this.renderSelection(resolved));
  }

  // `onPath` carries the ids between the tree root and this node. The node table
  // is a DAG — a shared refinement predicate hangs off several parents — so a
  // node renders once per position that reaches it, as it did when the wire
  // nested the subtree; the path set is what stops a cycle from recursing
  // forever if one ever reaches the wire.
  private renderNode(
    node: IrNode,
    edge: string | null,
    depth: number,
    parentId: number | null,
    onPath: Set<number>,
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
    row.appendChild(el("span", "node-type", `: ${type}`));
    // B5: in a holes-kind (pre-inference) pane the type is a hole (`_`/`?N`);
    // show what inference resolves it to downstream (a set on mono fan-out) on *hover*
    // rather than inline — the inline `→ T` glyph was confusable with the
    // function-type arrow `⇒` and partial-type arrow `⇀`.
    const resolved = this.store.resolvedTypesFor(this.paneId, node.nodeId);
    const tooltipText = resolvedTypeTooltip(type, resolved);
    if (tooltipText !== null) {
      this.attachResolvedTooltip(row, tooltipText);
    }
    row.appendChild(el("span", "node-id", `#${node.nodeId}`));
    container.appendChild(row);

    // Clicking the row selects this node in this pane (the cross-link). The
    // twisty toggles expand/collapse; we stop it from also selecting so the two
    // affordances stay distinct.
    row.addEventListener("click", (e) => {
      if (e.target === twisty) return;
      this.store.setSelection({ kind: "node", paneId: this.paneId, nodeId: node.nodeId });
    });

    // The edge label is computed here, not shipped: children arrive in order —
    // the value children, then the refinement predicates — so a value child's
    // index in `children` is its positional index. A predicate gets no label. A
    // number would be its position among the parent's type slots, which is not
    // where the reader is looking, and the same predicate reached from two
    // parents would carry two different ones; `predicate` is what marks it.
    const childNodes = hasChildren
      ? node.children
          .map((c, i) => ({ edge: c.predicate ? null : String(i), child: c }))
          .filter(({ child }) => !onPath.has(child.id))
          .map(({ edge, child }) => ({ edge, node: this.nodeById.get(child.id) }))
          .filter((c): c is { edge: string | null; node: IrNode } => c.node !== undefined)
      : [];
    if (childNodes.length === 0) {
      twisty.textContent = "·";
      twisty.classList.add("leaf");
      this.handles.set(node.nodeId, { row, parentId, expand: () => {} });
      return container;
    }

    const childPath = new Set(onPath).add(node.nodeId);
    const childrenBox = el("div", "tree-children");
    for (const child of childNodes) {
      childrenBox.appendChild(
        this.renderNode(child.node, child.edge, depth + 1, node.nodeId, childPath),
      );
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

    const highlights = resolved.result.highlightsByPane.get(this.paneId);
    if (!highlights || highlights.size === 0) return;
    const primary = resolved.primaryByPane.get(this.paneId) ?? null;

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
