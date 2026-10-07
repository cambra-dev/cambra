// What the operator pane draws, derived from the wire pane.
//
// The wire ships every operator the conversion built. Two of those kinds carry
// no step of the computation and cost the reader more than they tell:
//
// - **A `FanOutBranch` never has more than one consumer.** The fan-out happens
//   at the shared producer every branch points at, and `FanOut` is not a
//   `TileOperator`, so no node records it. Drawing the branches puts the name
//   "fan" on the one node in the star that does not fan. Suppressing a branch
//   and joining its two edges puts the fan-out back at the producer.
// - **A `Constant` with one consumer is that consumer's argument**, not a stage
//   ahead of it. It draws inside the consumer, labelled by its type.
//
// Both are *vertex suppression*: deleting a vertex of degree two and joining its
// neighbours. Neither may cost addressability. Every operator id in the pane is
// a possible cross-pane selection target, so suppression records where the id
// went and [`viewItem`](DrawGraph.viewItem) answers it. `drawGraphOf` checks
// that every id on the wire has a view item before it returns.

import type { OperatorNode, OperatorPane } from "../types";
import { isNamedRole, roleLabel } from "../types";

/** One drawn box. */
export interface DrawNode {
  id: number;
  label: string;
  tiling: string | null;
  role: string;
  /** Constants drawn inside this node. Each keeps its own id. */
  chips: DrawChip[];
}

export interface DrawChip {
  id: number;
  /** The constant's type, which is the only thing its node carried. */
  text: string;
}

/** One drawn edge, standing in for any nodes suppressed along it. */
export interface DrawEdge {
  id: string;
  from: number;
  to: number;
  kind: string;
  role: string;
  deferred: boolean;
  /** Operators this edge replaced, producer-side first. */
  suppressed: number[];
}

/**
 * Where one operator id is drawn.
 *
 * A suppressed node has no box, so the element that answers for it is the edge
 * that replaced it or the node that absorbed it. Named after yFiles'
 * `IFoldingView.getViewItem`, which is the same lookup.
 */
export type ViewItem =
  | { kind: "node"; id: number }
  | { kind: "chip"; id: number; host: number }
  | { kind: "glyph"; id: number; edge: string };

export class DrawGraph {
  constructor(
    readonly nodes: DrawNode[],
    readonly edges: DrawEdge[],
    private readonly view: Map<number, ViewItem>,
  ) {}

  /** The element drawing `id`, or `undefined` when the pane has no such node. */
  viewItem(id: number): ViewItem | undefined {
    return this.view.get(id);
  }
}

const isConstant = (n: OperatorNode) => n.label === "Constant";
const isBranch = (n: OperatorNode) => n.label === "FanOutBranch";

/** A constant's type, which is all its node carried. */
function constantText(node: OperatorNode): string {
  const t = node.tiling ?? "?";
  return t.startsWith("Scalar(") && t.endsWith(")") ? t.slice(7, -1) : t;
}

export function drawGraphOf(pane: OperatorPane): DrawGraph {
  const byId = new Map(pane.nodes.map((n) => [n.nodeId, n]));
  const consumers = new Map<number, number[]>();
  for (const n of pane.nodes) {
    for (const e of n.inputs) {
      if (!byId.has(e.subscribed)) continue;
      (consumers.get(e.subscribed) ?? consumers.set(e.subscribed, []).get(e.subscribed)!).push(
        n.nodeId,
      );
    }
  }
  const outDegree = (id: number) => consumers.get(id)?.length ?? 0;

  // A branch is suppressed when it holds one fan edge; a constant when exactly
  // one operator reads it and that operator is drawn. The conditions hold for
  // every such node measured, but none is an invariant the wire states, so all
  // are checked. Branches are decided first: a constant whose one reader is a
  // suppressed branch would be a chip on a box that does not exist.
  const suppressed = new Set<number>();
  const chipOf = new Map<number, number>();
  for (const n of pane.nodes) {
    if (isBranch(n) && n.inputs.some((e) => isNamedRole(e.role, "fan")) && outDegree(n.nodeId) === 1) {
      suppressed.add(n.nodeId);
    }
  }
  for (const n of pane.nodes) {
    if (!isConstant(n) || outDegree(n.nodeId) !== 1) continue;
    const reader = consumers.get(n.nodeId)![0];
    if (suppressed.has(reader)) continue;
    suppressed.add(n.nodeId);
    chipOf.set(n.nodeId, reader);
  }

  const nodes: DrawNode[] = [];
  const nodeById = new Map<number, DrawNode>();
  for (const n of pane.nodes) {
    if (suppressed.has(n.nodeId)) continue;
    const d: DrawNode = {
      id: n.nodeId,
      label: n.label,
      tiling: n.tiling ?? null,
      role: n.role,
      chips: [],
    };
    nodes.push(d);
    nodeById.set(n.nodeId, d);
  }
  for (const n of pane.nodes) {
    const host = chipOf.get(n.nodeId);
    if (host === undefined) continue;
    nodeById.get(host)?.chips.push({ id: n.nodeId, text: constantText(n) });
  }

  // Follow a suppressed branch back to the producer it stood in front of,
  // collecting what it replaced. The guard is for a wire that suppressed a
  // cycle of branches, which `assert_graph_invariants` forbids.
  const resolve = (id: number, acc: number[]): number => {
    const seen = new Set<number>();
    let at = id;
    while (suppressed.has(at) && !seen.has(at)) {
      seen.add(at);
      acc.push(at);
      const fan = byId.get(at)?.inputs.find((e) => isNamedRole(e.role, "fan"));
      if (!fan || !byId.has(fan.subscribed)) break;
      at = fan.subscribed;
    }
    return at;
  };

  const edges: DrawEdge[] = [];
  const edgeById = new Map<string, DrawEdge>();
  for (const n of pane.nodes) {
    if (suppressed.has(n.nodeId)) continue;
    for (const e of n.inputs) {
      if (!byId.has(e.subscribed) || chipOf.has(e.subscribed)) continue;
      const replaced: number[] = [];
      // A join may close on its own consumer — a store whose body is a branch
      // of the store's own fan — and is kept: it is a deferred edge, drawn as a
      // back edge, and the branch it replaced is addressable only through it.
      const from = resolve(e.subscribed, replaced);
      if (!nodeById.has(from)) continue;
      // A suppressed branch's own edge to the fan carries the sharing, so the
      // joined edge takes that kind rather than the branch's `value` role.
      const through = replaced.length
        ? byId.get(replaced[replaced.length - 1])!.inputs.find((x) => isNamedRole(x.role, "fan"))!
        : e;
      const id = `${from}>${n.nodeId}|${roleLabel(e.role)}`;
      // Two inputs whose role labels coincide draw as one edge, so the
      // operators either replaced are recorded on the edge that remains.
      const drawn = edgeById.get(id);
      if (drawn) {
        drawn.suppressed.push(...replaced);
        continue;
      }
      const edge: DrawEdge = {
        id,
        from,
        to: n.nodeId,
        kind: through.kind,
        role: roleLabel(e.role),
        deferred: e.deferred,
        suppressed: replaced,
      };
      edges.push(edge);
      edgeById.set(id, edge);
    }
  }

  const view = new Map<number, ViewItem>();
  for (const d of nodes) {
    view.set(d.id, { kind: "node", id: d.id });
    for (const c of d.chips) view.set(c.id, { kind: "chip", id: c.id, host: d.id });
  }
  for (const e of edges) {
    for (const s of e.suppressed) view.set(s, { kind: "glyph", id: s, edge: e.id });
  }
  const lost = pane.nodes.filter((n) => !view.has(n.nodeId)).map((n) => `${n.label} #${n.nodeId}`);
  if (lost.length > 0) {
    // A shape the suppression rules did not anticipate. The pane still draws;
    // the ids named here are the selections it cannot show.
    console.error("The operator pane suppressed operators it draws nowhere:", lost);
  }
  return new DrawGraph(nodes, edges, view);
}

/**
 * The wire edges a drawn graph never lays out: they close the cycles.
 *
 * An edge wired late is the one a `CycleSlot` filled, and a `CycleSlot` is the
 * only way an operator subscribes something built after it — so these are
 * exactly the edges whose removal leaves the graph acyclic. The test is
 * `deferred` alone. A joined edge takes its `kind` from the branch it replaced,
 * which is `share`, while `deferred` stays the consumer's.
 */
export const isBackEdge = (e: DrawEdge): boolean => e.deferred;
