import { describe, expect, it } from "vitest";

import { buildLinkGraph, resolveLinks, type PaneInfo } from "./links";
import type { Span } from "./types";

// A two-pane fixture mirroring the real MVP shape: post-channelize -> post-inference.
//
// post-channelize has a polymorphic def body (node 2, span [2,5)). Inference
// deletes it and emits two monomorphization clones (nodes 4 and 5, both blaming
// the same origin span [2,5)). Nodes 1 (root) and 3 survive by identity.
//
//   post-channelize:  1[0,10)  2[2,5)  3[6,7)
//   post-inference: 1[0,10)         3[6,7)  4[2,5)  5[2,5)
//   paneLinks:  [[1,1],[3,3],[2,4],[2,5]]  (dense: self-edges for the survivors
//              1 and 3, plus node 2 fanning out to clones 4 and 5)
function pane(id: string, spans: Record<number, Span | null>): PaneInfo {
  const map = new Map<number, Span | null>(
    Object.entries(spans).map(([k, v]) => [Number(k), v]),
  );
  return {
    id,
    nodeIds: new Set(map.keys()),
    spanOf: (nodeId) => map.get(nodeId) ?? null,
  };
}

const channelize = pane("post-channelize", {
  1: { start: 0, end: 10 },
  2: { start: 2, end: 5 },
  3: { start: 6, end: 7 },
});
const infer = pane("post-inference", {
  1: { start: 0, end: 10 },
  3: { start: 6, end: 7 },
  4: { start: 2, end: 5 },
  5: { start: 2, end: 5 },
});

const graph = buildLinkGraph(
  [channelize, infer],
  [
    {
      from: "post-channelize",
      to: "post-inference",
      // Dense: self-edges for the identity-preserved survivors (1, 3) plus the
      // node-2 fan-out to clones 4 and 5. An edge is a bare pair — resolution is
      // bidirectional and transitive, so a label would change nothing here.
      edges: [
        [1, 1],
        [3, 3],
        [2, 4],
        [2, 5],
      ],
    },
  ],
);

function hl(paneId: string, result: ReturnType<typeof resolveLinks>): number[] {
  return [...(result.highlightsByPane.get(paneId) ?? [])].sort((a, b) => a - b);
}

function spanKeys(result: ReturnType<typeof resolveLinks>): string[] {
  return result.sourceSpans.map((s) => `${s.start}:${s.end}`).sort();
}

describe("resolveLinks: identity adjacency", () => {
  it("highlights the same NodeId in a neighbouring pane that has it", () => {
    const r = resolveLinks(graph, [{ paneId: "post-channelize", nodeId: 1 }]);
    expect(hl("post-channelize", r)).toEqual([1]);
    expect(hl("post-inference", r)).toEqual([1]); // identity
    expect(spanKeys(r)).toEqual(["0:10"]);
  });

  it("is bidirectional: a downstream identity node reaches its upstream twin", () => {
    const r = resolveLinks(graph, [{ paneId: "post-inference", nodeId: 3 }]);
    expect(hl("post-channelize", r)).toEqual([3]);
    expect(hl("post-inference", r)).toEqual([3]);
  });
});

describe("resolveLinks: explicit (mono fan-out) edges", () => {
  it("follows a 1->N fan-out downstream", () => {
    const r = resolveLinks(graph, [{ paneId: "post-channelize", nodeId: 2 }]);
    expect(hl("post-channelize", r)).toEqual([2]);
    expect(hl("post-inference", r)).toEqual([4, 5]); // both clones
    expect(spanKeys(r)).toEqual(["2:5"]); // clones + original all blame [2,5)
  });

  it("is transitive: one clone reaches its origin AND every sibling clone", () => {
    const r = resolveLinks(graph, [{ paneId: "post-inference", nodeId: 4 }]);
    // 4 -> (reverse) 2 -> (forward) {4, 5}: the whole type-set, both directions.
    expect(hl("post-channelize", r)).toEqual([2]);
    expect(hl("post-inference", r)).toEqual([4, 5]);
  });
});

describe("resolveLinks: source-span projection", () => {
  it("dedupes spans shared across highlighted nodes", () => {
    const r = resolveLinks(graph, [{ paneId: "post-inference", nodeId: 5 }]);
    // 2, 4, 5 all carry [2,5) -> a single deduped span.
    expect(spanKeys(r)).toEqual(["2:5"]);
  });

  it("skips nodes that carry no span", () => {
    // Node 1 survives a->b by identity: a dense self-edge carries the link even
    // though neither node has a span.
    const noSpan = buildLinkGraph(
      [pane("a", { 1: null }), pane("b", { 1: null })],
      [{ from: "a", to: "b", edges: [[1, 1]] }],
    );
    const r = resolveLinks(noSpan, [{ paneId: "a", nodeId: 1 }]);
    expect(r.sourceSpans).toEqual([]);
    expect(hl("a", r)).toEqual([1]);
    expect(hl("b", r)).toEqual([1]);
  });
});

describe("resolveLinks: graceful degradation", () => {
  it("ignores an unknown seed pane", () => {
    const r = resolveLinks(graph, [{ paneId: "nope", nodeId: 1 }]);
    expect(hl("post-channelize", r)).toEqual([]);
    expect(hl("post-inference", r)).toEqual([]);
  });

  it("ignores a seed node absent from its pane", () => {
    const r = resolveLinks(graph, [{ paneId: "post-channelize", nodeId: 999 }]);
    expect(hl("post-channelize", r)).toEqual([]);
  });

  it("merges multiple seeds (the source-click case)", () => {
    const r = resolveLinks(graph, [
      { paneId: "post-channelize", nodeId: 3 },
      { paneId: "post-inference", nodeId: 4 },
    ]);
    expect(hl("post-channelize", r)).toEqual([2, 3]);
    expect(hl("post-inference", r)).toEqual([3, 4, 5]);
  });
});
