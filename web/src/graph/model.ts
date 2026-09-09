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
// went and [`viewItem`](DrawGraph.viewItem) answers it.
//
// At the `steps` detail level the rules in `./rules` merge what survives into
// composites, which carries the same obligation one level up: a composite lists
// its members, and an operator suppressed onto an edge that a merge made
// internal is answered for by the composite that swallowed the edge.

import { Merge, applyRules } from "./rules";
import type { OperatorEdge, OperatorNode, OperatorPane } from "../types";
import { isNamedRole, roleLabel } from "../types";

/**
 * How much of the graph to draw.
 *
 * `operators` is the wire's own drawing — one box per operator the two
 * suppressions leave. `steps` merges the recurring plumbing shapes into
 * composites.
 */
export type Detail = "operators" | "steps";

/** One drawn box. */
export interface DrawNode {
  id: number;
  label: string;
  tiling: string | null;
  role: string;
  /** Constants drawn inside this node. Each keeps its own id. */
  chips: DrawChip[];
  /** Operators this box stands for, the representative first. */
  members: number[];
  /** `FanOutBranch` operators suppressed onto this box's outgoing edges. */
  fanOuts: number[];
}

export interface DrawChip {
  id: number;
  /** The constant's type, which is the only thing its node carried. */
  text: string;
  /** The member that reads it, which is what makes a chip attributable. */
  owner: number;
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
  /** Drawn edges this one stands for. More than one only under merging. */
  count: number;
}

/**
 * Where one operator id is drawn.
 *
 * A suppressed node has no box, so the element that answers for it is the edge
 * that replaced it, the node that absorbed it, or the composite it belongs to.
 * Named after yFiles' `IFoldingView.getViewItem`, which is the same lookup.
 */
export type ViewItem =
  | { kind: "node"; id: number }
  | { kind: "chip"; id: number; host: number }
  | { kind: "glyph"; id: number; edge: string }
  | { kind: "member"; id: number; host: number };

export class DrawGraph {
  constructor(
    readonly nodes: DrawNode[],
    readonly edges: DrawEdge[],
    readonly detail: Detail,
    private readonly view: Map<number, ViewItem>,
  ) {}

  /** The element drawing `id`, or `undefined` when the pane has no such node. */
  viewItem(id: number): ViewItem | undefined {
    return this.view.get(id);
  }

  /** Every operator id an element answers for, the element's own id first. */
  masterItems(item: ViewItem): number[] {
    if (item.kind === "glyph") {
      const edge = this.edges.find((e) => e.id === item.edge);
      return edge ? [item.id, ...edge.suppressed.filter((s) => s !== item.id)] : [item.id];
    }
    if (item.kind === "node") {
      const node = this.nodes.find((n) => n.id === item.id);
      if (!node) return [item.id];
      const rest = [...node.members, ...node.fanOuts].filter((x) => x !== item.id);
      return [item.id, ...rest];
    }
    return [item.id];
  }
}

const isConstant = (n: OperatorNode) => n.label === "Constant";
const isBranch = (n: OperatorNode) => n.label === "FanOutBranch";

/** A constant's type, which is all its node carried. */
export function constantText(node: OperatorNode): string {
  const t = node.tiling ?? "?";
  return t.startsWith("Scalar(") && t.endsWith(")") ? t.slice(7, -1) : t;
}

export function drawGraphOf(pane: OperatorPane, detail: Detail = "operators"): DrawGraph {
  const base = suppressedGraph(pane);
  return detail === "steps" ? merged(base) : addressed(base.nodes, base.edges, "operators");
}

interface Base {
  nodes: DrawNode[];
  edges: DrawEdge[];
}

/** The wire's own drawing: the two vertex suppressions, and nothing merged. */
function suppressedGraph(pane: OperatorPane): Base {
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
  // one operator reads it. Both conditions hold for every such node measured,
  // but neither is an invariant the wire states, so both are checked.
  const suppressed = new Set<number>();
  const chipOf = new Map<number, number>();
  for (const n of pane.nodes) {
    if (isBranch(n) && n.inputs.some((e) => isNamedRole(e.role, "fan")) && outDegree(n.nodeId) === 1) {
      suppressed.add(n.nodeId);
    } else if (isConstant(n) && outDegree(n.nodeId) === 1) {
      suppressed.add(n.nodeId);
      chipOf.set(n.nodeId, consumers.get(n.nodeId)![0]);
    }
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
      members: [n.nodeId],
      fanOuts: [],
    };
    nodes.push(d);
    nodeById.set(n.nodeId, d);
  }
  for (const n of pane.nodes) {
    const host = chipOf.get(n.nodeId);
    if (host === undefined) continue;
    nodeById.get(host)?.chips.push({ id: n.nodeId, text: constantText(n), owner: host });
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
  const seenEdge = new Set<string>();
  for (const n of pane.nodes) {
    if (suppressed.has(n.nodeId)) continue;
    for (const e of n.inputs) {
      if (!byId.has(e.subscribed) || chipOf.has(e.subscribed)) continue;
      const replaced: number[] = [];
      const from = resolve(e.subscribed, replaced);
      if (!nodeById.has(from) || from === n.nodeId) continue;
      // A suppressed branch's own edge to the fan carries the sharing, so the
      // joined edge takes that kind rather than the branch's `value` role.
      const through = replaced.length
        ? byId.get(replaced[replaced.length - 1])!.inputs.find((x) => isNamedRole(x.role, "fan"))!
        : e;
      const id = `${from}>${n.nodeId}|${roleLabel(e.role)}`;
      if (seenEdge.has(id)) continue;
      seenEdge.add(id);
      edges.push({
        id,
        from,
        to: n.nodeId,
        kind: through.kind,
        role: roleLabel(e.role),
        deferred: e.deferred,
        suppressed: replaced,
        count: 1,
      });
    }
  }
  return { nodes, edges };
}

/** Run the rules, then rebuild boxes and edges over the classes they leave. */
function merged(base: Base): DrawGraph {
  const m = new Merge(base.nodes, base.edges);
  applyRules(m);

  const byId = new Map(base.nodes.map((n) => [n.id, n]));
  const nodes: DrawNode[] = m.classes().map((c) => {
    // The representative leads: it is the box the others merged into, and the
    // one whose tiling is what the composite emits.
    const rest = m.members(c).filter((x) => x !== c);
    rest.sort((a, b) => a - b);
    const members = [c, ...rest];
    const rep = byId.get(c)!;
    return {
      id: c,
      label: m.name(c),
      tiling: rep.tiling,
      role: rep.role,
      chips: members.flatMap((x) => byId.get(x)!.chips),
      members,
      fanOuts: [],
    };
  });

  // An edge with both ends in one class is internal and is not drawn, so the
  // operators suppressed onto it have nowhere left to go. The composite that
  // swallowed the edge answers for them, which is what keeps every wire id
  // addressable. They are fan-outs rather than members: `members` counts
  // operators the rules merged and is bounded by `MAX_MEMBERS`.
  const swallowed = new Map<number, number[]>();
  const edges: DrawEdge[] = [];
  const byKey = new Map<string, DrawEdge>();
  for (const e of base.edges) {
    const from = m.find(e.from);
    const to = m.find(e.to);
    if (from === to) {
      if (e.suppressed.length) {
        (swallowed.get(from) ?? swallowed.set(from, []).get(from)!).push(...e.suppressed);
      }
      continue;
    }
    const id = `${from}>${to}|${e.role}`;
    const prior = byKey.get(id);
    if (prior) {
      prior.count += 1;
      // Join rather than keep the first: a merged edge is a `share` if any
      // constituent is and a back edge if any constituent is, so a recurrence
      // into a collapsed store still reads as one.
      if (e.kind === "share") prior.kind = "share";
      prior.deferred = prior.deferred || e.deferred;
      prior.suppressed.push(...e.suppressed);
      continue;
    }
    const drawn: DrawEdge = {
      id,
      from,
      to,
      kind: e.kind,
      role: e.role,
      deferred: e.deferred,
      suppressed: [...e.suppressed],
      count: 1,
    };
    byKey.set(id, drawn);
    edges.push(drawn);
  }

  for (const n of nodes) {
    const extra = swallowed.get(n.id);
    if (extra) n.fanOuts.push(...extra);
  }
  return addressed(nodes, edges, "steps");
}

/**
 * Attach every operator id to the element that draws it.
 *
 * At `steps` a suppressed branch draws as one mark on its producer rather than
 * as a diamond per branch along the wires, so the producer's box answers for it.
 */
function addressed(nodes: DrawNode[], edges: DrawEdge[], detail: Detail): DrawGraph {
  const view = new Map<number, ViewItem>();
  for (const d of nodes) {
    view.set(d.id, { kind: "node", id: d.id });
    for (const c of d.chips) view.set(c.id, { kind: "chip", id: c.id, host: d.id });
    for (const x of d.members) if (x !== d.id) view.set(x, { kind: "member", id: x, host: d.id });
  }
  const nodeById = new Map(nodes.map((n) => [n.id, n]));
  if (detail === "steps") {
    for (const d of nodes) {
      for (const s of d.fanOuts) view.set(s, { kind: "member", id: s, host: d.id });
    }
  }
  for (const e of edges) {
    if (detail === "steps") {
      const producer = nodeById.get(e.from);
      for (const s of e.suppressed) {
        producer?.fanOuts.push(s);
        view.set(s, { kind: "member", id: s, host: e.from });
      }
    } else {
      for (const s of e.suppressed) view.set(s, { kind: "glyph", id: s, edge: e.id });
    }
  }
  return new DrawGraph(nodes, edges, detail, view);
}

/**
 * The wire edges a drawn graph never lays out: they close the cycles.
 *
 * A `value` edge wired late is the one a `CycleSlot` filled, and a `CycleSlot`
 * is the only way an operator subscribes something built after it — so these
 * are exactly the edges whose removal leaves the graph acyclic.
 */
export const isBackEdge = (e: DrawEdge): boolean => e.kind === "value" && e.deferred;

export type { OperatorEdge, OperatorNode };
