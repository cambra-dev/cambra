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

/** The full link graph: ordered panes + the dense edges between them. */
export interface LinkGraph {
  /** Panes in pipeline order (upstream -> downstream). */
  panes: PaneInfo[];
  /**
   * Dense edges keyed by adjacent pane pair. `edges.get(\`${from}>${to}\`)`
   * holds `[upstreamId, downstreamId]` pairs for that pair — self-edges
   * included, so identity is followed as an edge like any other.
   */
  edges: Map<string, PaneEdge[]>;
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
 * stored verbatim, so the resolver follows identity and fan-out uniformly.
 */
export function buildLinkGraph(
  panes: PaneInfo[],
  paneLinks: { from: string; to: string; edges: PaneEdge[] }[],
): LinkGraph {
  const edges = new Map<string, PaneEdge[]>();
  for (const link of paneLinks) {
    edges.set(pairKey(link.from, link.to), link.edges);
  }
  return { panes, edges };
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
      if (fwd) for (const [up, down] of fwd) if (up === node) enqueue(pane + 1, down);
    }

    // Upstream neighbour (pane - 1): reverse edges (self-edges included).
    if (pane - 1 >= 0) {
      const upId = graph.panes[pane - 1].id;
      const back = graph.edges.get(pairKey(upId, graph.panes[pane].id));
      if (back) for (const [up, down] of back) if (down === node) enqueue(pane - 1, up);
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
