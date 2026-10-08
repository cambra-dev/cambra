import { beforeEach, describe, expect, it } from "vitest";

import { LiveStore, applyFrame, shownNodes, tagsFor, type LiveState } from "./liveStore";
import type { LiveFrame, LiveProbe } from "./types";

function probe(seq: number, value: string): LiveProbe {
  return {
    producerId: 1,
    producer: "P#1",
    shape: "DataFunction",
    completeness: "True",
    obsolete: null,
    note: null,
    seq,
    stale: false,
    total: 1,
    dropped: 0,
    rows: [{ key: "u0", value, deleted: false }],
  };
}

/** A frame whose every probe carries a new answer: its `seq` is the frame's count. */
function frame(published: number, nodes: [number, string][], final = false): LiveFrame {
  return {
    version: 0,
    published,
    final,
    nodes: nodes.map(([nodeId, value]) => ({ nodeId, probes: [probe(published, value)] })),
    sources: [],
  };
}

const empty: LiveState = {
  status: { kind: "connecting" },
  version: 0,
  nodes: new Map(),
  sources: new Map(),
  tags: [],
};

describe("applyFrame", () => {
  // The property the cache exists for: a node the newest frame did not mention
  // keeps its rows, so pinning it answers from the last frame it did appear in
  // rather than waiting for a next frame that a converged program never sends.
  it("replaces the nodes a frame carries and leaves the others alone", () => {
    const first = applyFrame(empty, frame(1, [[10, '"a"'], [11, '"b"']]));
    const second = applyFrame(first, frame(2, [[10, '"c"']]));

    expect(second.nodes.get(10)?.probes[0]?.rows[0]?.value).toBe('"c"');
    expect(second.nodes.get(11)?.probes[0]?.rows[0]?.value).toBe('"b"');
  });

  // Staleness is the gap between the newest frame and the one a producer's
  // rows arrived in, so it is a number the pane can state rather than a flag it
  // has to trust — and it is the producer's, because one operator's probes can
  // be behind by different amounts.
  it("records the frame each producer's rows arrived in", () => {
    const state = applyFrame(applyFrame(empty, frame(1, [[10, '"a"'], [11, '"b"']])), frame(7, [[10, '"c"']]));
    expect(state.status).toEqual({ kind: "live", published: 7 });
    expect(state.nodes.get(11)?.probes[0]?.changedAt).toBe(1);
    expect(state.nodes.get(10)?.probes[0]?.changedAt).toBe(7);
  });

  // The wire sends every probe's last answer in every frame, so a producer that
  // has produced nothing since reappears with the `seq` it had. That is the
  // same answer, and it keeps the frame it first arrived in.
  it("keeps the arrival frame of an answer a later frame repeats", () => {
    const first = applyFrame(empty, frame(1, [[10, '"a"']]));
    const repeat: LiveFrame = { ...frame(4, []), nodes: [{ nodeId: 10, probes: [probe(1, '"a"')] }] };
    const state = applyFrame(first, repeat);
    expect(state.nodes.get(10)?.probes[0]?.changedAt).toBe(1);
  });

  // A reload rebuilds operators under fresh ids and may hand an old id's
  // number to nothing, so entries from the version before it are dropped
  // rather than left to read as the new version's.
  it("drops every cached entry when a frame names another version", () => {
    const sourced: LiveFrame = {
      ...frame(1, [[10, '"a"']]),
      sources: [{ nodeIds: [20], name: "stdin", total: 1, dropped: 0, rows: [] }],
    };
    const before = applyFrame(empty, sourced);
    const after = applyFrame(before, { ...frame(2, [[11, '"b"']]), version: 2 });

    expect(after.version).toBe(2);
    expect(after.nodes.has(10)).toBe(false);
    expect(after.nodes.get(11)?.probes[0]?.rows[0]?.value).toBe('"b"');
    expect(after.sources.size).toBe(0);
  });

  it("reads a final frame as a finished run", () => {
    const state = applyFrame(empty, frame(3, [[10, '"a"']], true));
    expect(state.status).toEqual({ kind: "finished", published: 3 });
  });

  it("reads an ordinary frame as live", () => {
    const state = applyFrame(empty, frame(3, [[10, '"a"']]));
    expect(state.status.kind).toBe("live");
  });

  it("indexes a source under every iteration over its domain", () => {
    const withSource = applyFrame(empty, {
      ...frame(1, []),
      sources: [{ nodeIds: [208, 212], name: "stdin", total: 1, dropped: 0, rows: [] }],
    });
    expect(withSource.sources.get(208)?.name).toBe("stdin");
    expect(withSource.sources.get(212)?.name).toBe("stdin");
  });

  it("drops a source no iteration names, which nothing could select", () => {
    const withSource = applyFrame(empty, {
      ...frame(1, []),
      sources: [{ nodeIds: [], name: "stdin", total: 0, dropped: 0, rows: [] }],
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
    store.inspect("Var(words): L8", 10, [10, 11, 12]);
    const tag = store.get().tags[0];
    expect(tag?.label).toBe("Var(words): L8");
    expect(tag?.nodes).toEqual([10, 11, 12]);
    expect(tag?.shown).toBe(true);
    expect(shownNodes(store.get())).toEqual(new Set([10, 11, 12]));
  });

  // Re-inspecting is the same gesture, not a new one, so it must not stack up
  // duplicate rows in the menu.
  it("re-inspecting one construct re-shows its tag and moves it to the front", () => {
    store.inspect("Var(a): L1", 1, [1]);
    store.inspect("Var(b): L2", 2, [2]);
    store.toggleTag("Var(a): L1");
    expect(store.get().tags.find((t) => t.id === "Var(a): L1")?.shown).toBe(false);

    store.inspect("Var(a): L1", 1, [1]);
    expect(store.get().tags.length).toBe(2);
    expect(store.get().tags[0]?.label).toBe("Var(a): L1");
    expect(store.get().tags[0]?.shown).toBe(true);
  });

  it("hides a tag's operators without forgetting the tag", () => {
    store.inspect("Var(a): L1", 1, [1, 2]);
    store.toggleTag("Var(a): L1");
    expect(store.get().tags.length).toBe(1);
    expect(shownNodes(store.get()).size).toBe(0);
  });

  it("forgets one tag", () => {
    store.inspect("Var(a): L1", 1, [1]);
    store.inspect("Var(b): L2", 2, [2]);
    store.removeTag("Var(a): L1");
    expect(store.get().tags.map((t) => t.label)).toEqual(["Var(b): L2"]);
  });

  it("clears every tag at once", () => {
    store.inspect("Var(a): L1", 1, [1]);
    store.inspect("Var(b): L2", 2, [2]);
    store.clearTags();
    expect(store.get().tags).toEqual([]);
    expect(shownNodes(store.get()).size).toBe(0);
  });

  // Two gestures can reach one operator, and a group names both rather than
  // picking one.
  it("reports every shown tag that asked for an operator", () => {
    store.inspect("Var(a): L1", 7, [7, 8]);
    store.inspect("Var(b): L2", 8, [8, 9]);
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
    store.inspect("a", 1, [1]);
    store.inspect("b", 2, [2]);
    off();
    store.inspect("c", 3, [3]);
    expect(seen).toEqual([1, 2]);
  });

  // A throwing subscriber must not starve the ones after it.
  it("isolates a throwing subscriber", () => {
    const seen: string[] = [];
    store.subscribe(() => {
      throw new Error("boom");
    });
    store.subscribe(() => seen.push("second"));
    store.inspect("a", 1, [1]);
    expect(seen).toEqual(["second"]);
  });
});

describe("LiveStore.retag", () => {
  // A tag names ids minted per compile, so after a reload each is either found
  // again in the new payload or dropped; it is never left naming old ids.
  it("re-points the tags it can resolve and drops the rest, keeping their shown state", () => {
    const live = new LiveStore();
    const span = { start: 0, end: 1, text: "x" };
    live.inspect("Var(x): L1", 1, [10], span);
    live.inspect("Var(y): L2", 2, [20], span);
    live.toggleTag("Var(x): L1");

    live.retag((tag) =>
      tag.label === "Var(x): L1" ? { id: tag.id, label: tag.label, anchorId: 5, nodes: [50], span } : null,
    );

    expect(live.get().tags).toEqual([
      { id: "Var(x): L1", label: "Var(x): L1", anchorId: 5, nodes: [50], span, shown: false },
    ]);
  });
});
