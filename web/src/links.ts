// The cross-pane provenance resolver — the multi-pane cross-link engine.
//
// Given an ordered list of pipeline panes and the links between adjacent panes,
// this resolves a *seed* set of `(pane, node)` anchors to the full provenance
// chain: the set of nodes to highlight **in every pane**, plus the set of source
// spans those nodes project to.
//
// The adjacency between two consecutive panes is the backend's **dense**
// `paneLinks` map: every edge, self-edges included. A node reaches the same
// NodeId in a neighbouring pane via the shipped `[id, id]` self-edge (no
// identity special case), and a fan-out via its `u !== d` edges. Resolution is
// **bidirectional and transitive** — it walks both upstream and downstream and
// chases edges through intermediate panes, so e.g. clicking one mono clone
// reaches its pre-inference original *and* every sibling clone (the type-set).
//
// Everything here is a pure function over plain data; the unit tests in
// `links.test.ts` are its behavioural spec.

import type { PaneEdge, Span } from "./types";

/** A node anchor: a NodeId living in a specific pane. */
export interface PaneNode {
  paneId: string;
  nodeId: number;
}

/** The per-pane data the resolver needs: which ids exist, and their spans. */
export interface PaneInfo {
  id: string;
  /** Every NodeId present in this pane's node table. */
  nodeIds: Set<number>;
  /** A node's source span (null if it carries none). */
  spanOf(nodeId: number): Span | null;
}

/**
 * One adjacent pane pair's dense edges, indexed by each endpoint.
 *
 * Both directions, because resolution walks both. Built once per pair rather
 * than scanned per vertex: the walk asks "which edges touch this node" for
 * every node it dequeues, and answering that by scanning the pair's whole edge
 * array makes the walk `V·E` — 1.2 s in the `Store` constructor at 3200 nodes
 * per pane, before the first paint.
 */
export interface PaneAdjacency {
  /** Upstream id -> the downstream ids it reaches. */
  forward: Map<number, number[]>;
  /** Downstream id -> the upstream ids that reach it. */
  backward: Map<number, number[]>;
}

/** The full link graph: ordered panes + the indexed edges between them. */
export interface LinkGraph {
  /** Panes in pipeline order (upstream -> downstream). */
  panes: PaneInfo[];
  /**
   * Adjacency keyed by adjacent pane pair: `edges.get(\`${from}>${to}\`)` holds
   * that pair's edges, self-edges included, so identity is followed as an edge
   * like any other.
   */
  edges: Map<string, PaneAdjacency>;
}

export interface ResolveResult {
  /** paneId -> the set of NodeIds to highlight in that pane. */
  highlightsByPane: Map<string, Set<number>>;
  /** The union of source spans the highlighted nodes project to (deduped). */
  sourceSpans: Span[];
}

function pairKey(from: string, to: string): string {
  return `${from}>${to}`;
}

/**
 * Build a [`LinkGraph`] from the raw pane list + `paneLinks`. Each entry is
 * keyed by its `(from, to)` ids; the dense edge list (self-edges included) is
 * indexed by both endpoints, so the resolver follows identity and fan-out
 * uniformly and reads an endpoint's edges without scanning the pair.
 */
export function buildLinkGraph(
  panes: PaneInfo[],
  paneLinks: { from: string; to: string; edges: PaneEdge[] }[],
): LinkGraph {
  const edges = new Map<string, PaneAdjacency>();
  for (const link of paneLinks) {
    const forward = new Map<number, number[]>();
    const backward = new Map<number, number[]>();
    for (const [up, down] of link.edges) {
      push(forward, up, down);
      push(backward, down, up);
    }
    edges.set(pairKey(link.from, link.to), { forward, backward });
  }
  return { panes, edges };
}

function push(index: Map<number, number[]>, key: number, value: number): void {
  const at = index.get(key);
  if (at === undefined) index.set(key, [value]);
  else at.push(value);
}

/**
 * Resolve a set of seed anchors to the full provenance chain across all panes.
 *
 * Returns, per pane, the set of NodeIds reachable from the seeds via the dense
 * edges (transitively, both directions; self-edges carry identity), and the
 * union of source
 * spans those nodes carry. Unknown seed panes / ids are skipped gracefully.
 */
export function resolveLinks(graph: LinkGraph, seeds: PaneNode[]): ResolveResult {
  const indexOf = new Map<string, number>();
  graph.panes.forEach((s, i) => indexOf.set(s.id, i));

  // BFS over (paneIndex, nodeId) vertices. The visited set is keyed by
  // "paneIndex:nodeId"; we also accumulate per-pane highlight sets.
  const highlightsByPane = new Map<string, Set<number>>();
  for (const s of graph.panes) highlightsByPane.set(s.id, new Set());

  const visited = new Set<string>();
  const queue: Array<{ pane: number; node: number }> = [];

  const enqueue = (pane: number, node: number): void => {
    if (pane < 0 || pane >= graph.panes.length) return;
    if (!graph.panes[pane].nodeIds.has(node)) return;
    const key = `${pane}:${node}`;
    if (visited.has(key)) return;
    visited.add(key);
    highlightsByPane.get(graph.panes[pane].id)!.add(node);
    queue.push({ pane, node });
  };

  for (const seed of seeds) {
    const idx = indexOf.get(seed.paneId);
    if (idx !== undefined) enqueue(idx, seed.nodeId);
  }

  while (queue.length > 0) {
    const { pane, node } = queue.shift()!;

    // Downstream neighbour (pane + 1): forward edges. The dense map ships a
    // self-edge for every preserved id, so identity is followed as an edge —
    // there is no identity special case.
    if (pane + 1 < graph.panes.length) {
      const downId = graph.panes[pane + 1].id;
      const fwd = graph.edges.get(pairKey(graph.panes[pane].id, downId));
      const reached = fwd?.forward.get(node);
      if (reached) for (const down of reached) enqueue(pane + 1, down);
    }

    // Upstream neighbour (pane - 1): reverse edges (self-edges included).
    if (pane - 1 >= 0) {
      const upId = graph.panes[pane - 1].id;
      const back = graph.edges.get(pairKey(upId, graph.panes[pane].id));
      const reaching = back?.backward.get(node);
      if (reaching) for (const up of reaching) enqueue(pane - 1, up);
    }
  }

  // Project the highlighted nodes to their source spans (deduped by start/end).
  const sourceSpans: Span[] = [];
  const seenSpan = new Set<string>();
  for (const pane of graph.panes) {
    const ids = highlightsByPane.get(pane.id)!;
    for (const id of ids) {
      const span = pane.spanOf(id);
      if (!span) continue;
      const k = `${span.start}:${span.end}`;
      if (seenSpan.has(k)) continue;
      seenSpan.add(k);
      sourceSpans.push(span);
    }
  }

  return { highlightsByPane, sourceSpans };
}
