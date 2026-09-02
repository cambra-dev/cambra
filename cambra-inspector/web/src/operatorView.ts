// The operator pane: the dataflow graph as an indented forest.
//
// The graph is a DAG with an explicit cycle set, not a tree, so the rendering
// picks one spanning relation and draws the rest as references:
//
// - **Value edges are the child relation.** They are exclusive ownership, so
//   they form a forest — that is asserted at the producer, in
//   `operator_graph::assert_graph_invariants`. Following them needs no cycle
//   guard.
// - **Share and feedback edges are reference rows.** A leaf naming its target,
//   clickable, so a reader follows sharing without the subtree being drawn
//   twice. Every cycle in the graph is a feedback edge, which is what keeps the
//   child relation acyclic.
//
// The roots are the nodes nothing owns: a sink per compiled output, and a fan
// input per share point. Each gets its own tree, which is why this is a forest
// and `TreeView`'s single root does not fit.

import type { OperatorEdge, OperatorNode, OperatorPane } from "./types";
import type { Resolved, Store } from "./store";

// Depth to expand to on first render, matching the tree panes'.
const DEFAULT_EXPAND_DEPTH = 3;

const INDENT = "    ";

function el(tag: string, className?: string, text?: string): HTMLElement {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

// An edge the child relation follows, as against one it renders as a reference.
function isChildEdge(edge: OperatorEdge): boolean {
  return edge.kind === "value";
}

// `Restrict [0,100] #4021`, or `Sink(main) #4103` for a boundary node, which has
// no tiling.
function rowText(node: OperatorNode): string {
  return node.tiling === null || node.tiling === undefined
    ? `${node.label} #${node.nodeId}`
    : `${node.label} ${node.tiling} #${node.nodeId}`;
}

interface NodeHandle {
  row: HTMLElement;
  parentId: number | null;
  expand: () => void;
  /** The row's position in render order — see the tree pane's `NodeHandle`. */
  order: number;
}

export class OperatorView {
  private readonly store: Store;
  private readonly paneId: string;
  private readonly nodeById: Map<number, OperatorNode>;
  // One handle per *position*, since a node reached through several value
  // parents cannot happen but a reference row can repeat. Keyed by id, so a
  // selection scrolls to the last position drawn — the same compromise
  // `TreeView` makes.
  private readonly handles = new Map<number, NodeHandle>();
  private markedRows: HTMLElement[] = [];
  private nextOrder = 0;

  constructor(parent: HTMLElement, store: Store, pane: OperatorPane) {
    this.store = store;
    this.paneId = pane.id;
    this.nodeById = new Map(pane.nodes.map((n) => [n.nodeId, n]));

    const root = el("div", "tree-root");
    for (const rootId of pane.roots) {
      const node = this.nodeById.get(rootId);
      if (node) root.appendChild(this.renderNode(node, null, 0, null));
    }
    parent.appendChild(root);

    store.subscribe((resolved) => this.renderSelection(resolved));
  }

  private renderNode(
    node: OperatorNode,
    edge: OperatorEdge | null,
    depth: number,
    parentId: number | null,
  ): HTMLElement {
    const container = el("div", "tree-node");
    const row = el("div", "tree-row selectable");
    const order = this.nextOrder++;
    const children = node.inputs.filter(isChildEdge);
    const references = node.inputs.filter((e) => !isChildEdge(e));
    const hasChildren = children.length > 0 || references.length > 0;

    const twisty = el("span", `twisty${hasChildren ? "" : " leaf"}`);
    row.appendChild(twisty);
    if (edge !== null) {
      row.appendChild(el("span", "edge-label", `${edge.role}:`));
      if (edge.deferred) {
        // Wired through a `CycleSlot` after its consumer was constructed, which
        // is how the store complexes close their cycles. Ownership is exclusive
        // either way, so the row nests like any value edge.
        row.appendChild(el("span", "op-deferred", "late"));
      }
    }
    row.appendChild(el("span", "node-label", node.label));
    if (node.tiling !== null && node.tiling !== undefined) {
      row.appendChild(el("span", "node-type", node.tiling));
    }
    row.appendChild(el("span", "node-id", `#${node.nodeId}`));
    container.appendChild(row);

    row.addEventListener("click", (e) => {
      if (e.target === twisty) return;
      this.store.setSelection({ kind: "node", paneId: this.paneId, nodeId: node.nodeId });
    });

    if (!hasChildren) {
      twisty.textContent = "·";
      twisty.classList.add("leaf");
      this.handles.set(node.nodeId, { row, parentId, order, expand: () => {} });
      return container;
    }

    const childrenBox = el("div", "tree-children");
    for (const childEdge of children) {
      const child = this.nodeById.get(childEdge.id);
      if (child) {
        childrenBox.appendChild(this.renderNode(child, childEdge, depth + 1, node.nodeId));
      }
    }
    for (const ref of references) {
      childrenBox.appendChild(this.renderReference(ref));
    }
    container.appendChild(childrenBox);

    let expanded = depth < DEFAULT_EXPAND_DEPTH;
    const apply = (): void => {
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
      order,
      expand: () => {
        if (!expanded) {
          expanded = true;
          apply();
        }
      },
    });
    return container;
  }

  // A share or feedback edge: a leaf naming its target, so the shared subtree is
  // drawn once at its own root rather than under every consumer. Clicking it
  // selects the target, which is how a reader follows the reference.
  private renderReference(edge: OperatorEdge): HTMLElement {
    const container = el("div", "tree-node");
    const row = el("div", `tree-row selectable op-ref op-ref-${edge.kind}`);
    row.appendChild(el("span", "twisty leaf", "·"));
    row.appendChild(el("span", "edge-label", `${edge.role}:`));
    row.appendChild(el("span", "op-ref-arrow", edge.kind === "feedback" ? "↺" : "→"));
    const target = this.nodeById.get(edge.id);
    row.appendChild(el("span", "node-label", target ? target.label : "?"));
    row.appendChild(el("span", "node-id", `#${edge.id}`));
    row.addEventListener("click", () => {
      this.store.setSelection({ kind: "node", paneId: this.paneId, nodeId: edge.id });
    });
    container.appendChild(row);
    return container;
  }

  private expandAncestors(nodeId: number): void {
    const seen = new Set<number>();
    let id: number | null = nodeId;
    while (id !== null && !seen.has(id)) {
      seen.add(id);
      const handle: NodeHandle | undefined = this.handles.get(id);
      if (!handle) return;
      handle.expand();
      id = handle.parentId;
    }
  }

  // The same two highlight strengths the tree panes use: `selected` for the
  // pane's own anchor, `linked` for a node a pane link reached.
  private renderSelection(resolved: Resolved): void {
    for (const row of this.markedRows) row.classList.remove("selected", "linked");
    this.markedRows = [];

    const highlights = resolved.result.highlightsByPane.get(this.paneId);
    if (!highlights || highlights.size === 0) return;
    const primaries = resolved.primaryByPane.get(this.paneId);

    // Scroll to the drawn row earliest in render order, as the tree panes do.
    let topmost: NodeHandle | null = null;
    for (const nodeId of highlights) {
      const handle = this.handles.get(nodeId);
      if (!handle) continue;
      this.expandAncestors(nodeId);
      handle.row.classList.add(primaries?.has(nodeId) ? "selected" : "linked");
      this.markedRows.push(handle.row);
      if (topmost === null || handle.order < topmost.order) topmost = handle;
    }

    topmost?.row.scrollIntoView({ block: "start" });
  }
}

/**
 * The pane's text, one indented line per row, for the copy button.
 *
 * Walks the wire's node table rather than the DOM, so the copy is the whole
 * graph whatever is collapsed — the visible set is a function of click history,
 * and a copy that varied with it would not be reproducible.
 */
export function serializeOperatorGraph(pane: OperatorPane): string {
  const nodeById = new Map(pane.nodes.map((n) => [n.nodeId, n]));
  const lines: string[] = [];
  const walk = (id: number, edge: OperatorEdge | null, depth: number): void => {
    const node = nodeById.get(id);
    if (!node) return;
    const prefix =
      edge === null ? "" : `${edge.role}: ${edge.deferred ? "late " : ""}`;
    lines.push(INDENT.repeat(depth) + prefix + rowText(node));
    for (const input of node.inputs) {
      if (isChildEdge(input)) {
        walk(input.id, input, depth + 1);
      } else {
        const target = nodeById.get(input.id);
        const arrow = input.kind === "feedback" ? "↺" : "→";
        lines.push(
          `${INDENT.repeat(depth + 1)}${input.role}: ${arrow} ${target ? target.label : "?"} #${input.id}`,
        );
      }
    }
  };
  for (const root of pane.roots) walk(root, null, 0);
  return lines.join("\n");
}
