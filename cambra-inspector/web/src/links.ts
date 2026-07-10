// The cross-stage provenance resolver — the multi-pane cross-link engine.
//
// Given an ordered list of pipeline stages and the non-identity links between
// adjacent stages, this resolves a *seed* set of `(stage, node)` anchors to the
// full provenance chain: the set of nodes to highlight **in every stage**, plus
// the set of source spans those nodes project to.
//
// The adjacency between two consecutive stages is **identity ∪ explicit edges**
// (D-MP1): a node highlights the same NodeId in any neighbouring stage that has
// it, plus whatever the backend's `stageLinks` records as a non-identity edge
// (monomorphization fan-out, generalized-let wrappers). Resolution is
// **bidirectional and transitive** — it walks both upstream and downstream and
// chases edges through intermediate stages, so e.g. clicking one mono clone
// reaches its pre-inference original *and* every sibling clone (the type-set).
//
// Everything here is a pure function over plain data; the unit tests in
// `links.test.ts` are its behavioural spec.

import type { Span } from "./types";

/** A node anchor: a NodeId living in a specific stage. */
export interface StageNode {
  stageId: string;
  nodeId: number;
}

/** The per-stage data the resolver needs: which ids exist, and their spans. */
export interface StageInfo {
  id: string;
  /** Every NodeId present in this stage's IR tree. */
  nodeIds: Set<number>;
  /** A node's source span (null if it carries none). */
  spanOf(nodeId: number): Span | null;
}

/** The full link graph: ordered stages + the non-identity edges between them. */
export interface LinkGraph {
  /** Stages in pipeline order (upstream -> downstream). */
  stages: StageInfo[];
  /**
   * Non-identity edges keyed by adjacent stage pair. `edges.get(\`${from}>${to}\`)`
   * holds `[upstreamId, downstreamId]` pairs for that pair (in pipeline order).
   */
  edges: Map<string, [number, number][]>;
}

export interface ResolveResult {
  /** stageId -> the set of NodeIds to highlight in that stage. */
  highlightsByStage: Map<string, Set<number>>;
  /** The union of source spans the highlighted nodes project to (deduped). */
  sourceSpans: Span[];
}

function pairKey(from: string, to: string): string {
  return `${from}>${to}`;
}

/**
 * Build a [`LinkGraph`] from the raw stage list + `stageLinks`. `stageLinks`
 * entries are keyed by their `(from, to)` ids; only pairs that are actually
 * adjacent in `stages` are used as edges (identity covers the rest).
 */
export function buildLinkGraph(
  stages: StageInfo[],
  stageLinks: { from: string; to: string; edges: [number, number][] }[],
): LinkGraph {
  const edges = new Map<string, [number, number][]>();
  for (const link of stageLinks) {
    edges.set(pairKey(link.from, link.to), link.edges);
  }
  return { stages, edges };
}

/**
 * Resolve a set of seed anchors to the full provenance chain across all stages.
 *
 * Returns, per stage, the set of NodeIds reachable from the seeds via identity
 * ∪ explicit edges (transitively, both directions), and the union of source
 * spans those nodes carry. Unknown seed stages / ids are skipped gracefully.
 */
export function resolveLinks(graph: LinkGraph, seeds: StageNode[]): ResolveResult {
  const indexOf = new Map<string, number>();
  graph.stages.forEach((s, i) => indexOf.set(s.id, i));

  // BFS over (stageIndex, nodeId) vertices. The visited set is keyed by
  // "stageIndex:nodeId"; we also accumulate per-stage highlight sets.
  const highlightsByStage = new Map<string, Set<number>>();
  for (const s of graph.stages) highlightsByStage.set(s.id, new Set());

  const visited = new Set<string>();
  const queue: Array<{ stage: number; node: number }> = [];

  const enqueue = (stage: number, node: number): void => {
    if (stage < 0 || stage >= graph.stages.length) return;
    if (!graph.stages[stage].nodeIds.has(node)) return;
    const key = `${stage}:${node}`;
    if (visited.has(key)) return;
    visited.add(key);
    highlightsByStage.get(graph.stages[stage].id)!.add(node);
    queue.push({ stage, node });
  };

  for (const seed of seeds) {
    const idx = indexOf.get(seed.stageId);
    if (idx !== undefined) enqueue(idx, seed.nodeId);
  }

  while (queue.length > 0) {
    const { stage, node } = queue.shift()!;

    // Downstream neighbour (stage + 1): identity + forward edges.
    if (stage + 1 < graph.stages.length) {
      const downId = graph.stages[stage + 1].id;
      enqueue(stage + 1, node); // identity
      const fwd = graph.edges.get(pairKey(graph.stages[stage].id, downId));
      if (fwd) for (const [up, down] of fwd) if (up === node) enqueue(stage + 1, down);
    }

    // Upstream neighbour (stage - 1): identity + reverse edges.
    if (stage - 1 >= 0) {
      const upId = graph.stages[stage - 1].id;
      enqueue(stage - 1, node); // identity
      const back = graph.edges.get(pairKey(upId, graph.stages[stage].id));
      if (back) for (const [up, down] of back) if (down === node) enqueue(stage - 1, up);
    }
  }

  // Project the highlighted nodes to their source spans (deduped by start/end).
  const sourceSpans: Span[] = [];
  const seenSpan = new Set<string>();
  for (const stage of graph.stages) {
    const ids = highlightsByStage.get(stage.id)!;
    for (const id of ids) {
      const span = stage.spanOf(id);
      if (!span) continue;
      const k = `${span.start}:${span.end}`;
      if (seenSpan.has(k)) continue;
      seenSpan.add(k);
      sourceSpans.push(span);
    }
  }

  return { highlightsByStage, sourceSpans };
}
