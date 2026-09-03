import { beforeEach, describe, expect, it } from "vitest";

import { LiveStore, applyFrame, shownNodes, tagsFor, type LiveState } from "./liveStore";
import type { LiveFrame, LiveProducer } from "./types";

function producer(tick: number, value: string): LiveProducer {
  return {
    producerId: 1,
    producer: "P#1",
    shape: "SealedFunction",
    watermark: "True",
    note: null,
    tick,
    seq: 0,
    stale: false,
    total: 1,
    dropped: 0,
    rows: [{ key: "u0", value, deleted: false }],
  };
}

function frame(tick: number, nodes: [number, string][], final = false): LiveFrame {
  return {
    tick,
    published: tick,
    final,
    nodes: nodes.map(([nodeId, value]) => ({ nodeId, producers: [producer(tick, value)] })),
    sources: [],
  };
}

const empty: LiveState = {
  status: { kind: "connecting" },
  nodes: new Map(),
  sources: new Map(),
  tags: [],
  tick: 0,
};

describe("applyFrame", () => {
  // The property the cache exists for: a node the newest frame did not mention
  // keeps its rows, so pinning it answers from the last frame it did appear in
  // rather than waiting for a next frame that a converged program never sends.
  it("replaces the nodes a frame carries and leaves the others alone", () => {
    const first = applyFrame(empty, frame(1, [[10, '"a"'], [11, '"b"']]));
    const second = applyFrame(first, frame(2, [[10, '"c"']]));

    expect(second.nodes.get(10)?.producers[0]?.rows[0]?.value).toBe('"c"');
    expect(second.nodes.get(10)?.tick).toBe(2);
    expect(second.nodes.get(11)?.producers[0]?.rows[0]?.value).toBe('"b"');
    expect(second.nodes.get(11)?.tick).toBe(1);
  });

  // Staleness is the gap between the newest tick and the entry's own, so it is
  // a number the pane can state rather than a flag it has to trust.
  it("keeps each entry's own tick so staleness is a difference", () => {
    const state = applyFrame(applyFrame(empty, frame(1, [[10, '"a"'], [11, '"b"']])), frame(7, [[10, '"c"']]));
    expect(state.tick).toBe(7);
    expect(state.tick - (state.nodes.get(11)?.tick ?? 0)).toBe(6);
  });

  it("reads a final frame as a finished run", () => {
    const state = applyFrame(empty, frame(3, [[10, '"a"']], true));
    expect(state.status).toEqual({ kind: "finished", tick: 3 });
  });

  it("reads an ordinary frame as live", () => {
    const state = applyFrame(empty, frame(3, [[10, '"a"']]));
    expect(state.status.kind).toBe("live");
  });

  it("indexes a source by its graph node", () => {
    const withSource = applyFrame(empty, {
      ...frame(1, []),
      sources: [{ nodeId: 208, name: "stdin", total: 1, dropped: 0, rows: [] }],
    });
    expect(withSource.sources.get(208)?.name).toBe("stdin");
  });

  it("drops a source carrying no graph node, which nothing could select", () => {
    const withSource = applyFrame(empty, {
      ...frame(1, []),
      sources: [{ nodeId: null, name: "stdin", total: 0, dropped: 0, rows: [] }],
    });
    expect(withSource.sources.size).toBe(0);
  });
});

describe("LiveStore tags", () => {
  let store: LiveStore;
  beforeEach(() => {
    store = new LiveStore();
  });

  it("starts connecting with nothing inspected", () => {
    expect(store.get().status).toEqual({ kind: "connecting" });
    expect(store.get().tags).toEqual([]);
  });

  it("records a gesture as a tag naming its operators", () => {
    store.inspect("Var(words): L8", [10, 11, 12]);
    const tag = store.get().tags[0];
    expect(tag?.label).toBe("Var(words): L8");
    expect(tag?.nodes).toEqual([10, 11, 12]);
    expect(tag?.shown).toBe(true);
    expect(shownNodes(store.get())).toEqual(new Set([10, 11, 12]));
  });

  // Re-inspecting is the same gesture, not a new one, so it must not stack up
  // duplicate rows in the menu.
  it("re-inspecting one construct re-shows its tag and moves it to the front", () => {
    store.inspect("Var(a): L1", [1]);
    store.inspect("Var(b): L2", [2]);
    store.toggleTag("Var(a): L1");
    expect(store.get().tags.find((t) => t.id === "Var(a): L1")?.shown).toBe(false);

    store.inspect("Var(a): L1", [1]);
    expect(store.get().tags.length).toBe(2);
    expect(store.get().tags[0]?.label).toBe("Var(a): L1");
    expect(store.get().tags[0]?.shown).toBe(true);
  });

  it("hides a tag's operators without forgetting the tag", () => {
    store.inspect("Var(a): L1", [1, 2]);
    store.toggleTag("Var(a): L1");
    expect(store.get().tags.length).toBe(1);
    expect(shownNodes(store.get()).size).toBe(0);
  });

  it("forgets one tag", () => {
    store.inspect("Var(a): L1", [1]);
    store.inspect("Var(b): L2", [2]);
    store.removeTag("Var(a): L1");
    expect(store.get().tags.map((t) => t.label)).toEqual(["Var(b): L2"]);
  });

  it("clears every tag at once", () => {
    store.inspect("Var(a): L1", [1]);
    store.inspect("Var(b): L2", [2]);
    store.clearTags();
    expect(store.get().tags).toEqual([]);
    expect(shownNodes(store.get()).size).toBe(0);
  });

  // Two gestures can reach one operator, and a group names both rather than
  // picking one.
  it("reports every shown tag that asked for an operator", () => {
    store.inspect("Var(a): L1", [7, 8]);
    store.inspect("Var(b): L2", [8, 9]);
    expect(tagsFor(store.get(), 8).map((t) => t.label)).toEqual([
      "Var(b): L2",
      "Var(a): L1",
    ]);
    store.toggleTag("Var(b): L2");
    expect(tagsFor(store.get(), 8).map((t) => t.label)).toEqual(["Var(a): L1"]);
  });

  it("notifies subscribers and stops on unsubscribe", () => {
    const seen: number[] = [];
    const off = store.subscribe((s) => seen.push(s.tags.length));
    store.inspect("a", [1]);
    store.inspect("b", [2]);
    off();
    store.inspect("c", [3]);
    expect(seen).toEqual([1, 2]);
  });

  // A throwing subscriber must not starve the ones after it.
  it("isolates a throwing subscriber", () => {
    const seen: string[] = [];
    store.subscribe(() => {
      throw new Error("boom");
    });
    store.subscribe(() => seen.push("second"));
    store.inspect("a", [1]);
    expect(seen).toEqual(["second"]);
  });
});
