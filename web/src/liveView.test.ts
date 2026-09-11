import { describe, expect, it } from "vitest";

import type { LiveState } from "./liveStore";
import { TAG_SLOTS, countOf, livePanelState, serializeLivePanel, staleText, tagColour } from "./liveView";
import type { LiveProducer, LiveSource } from "./types";

function producer(overrides: Partial<LiveProducer> = {}): LiveProducer {
  return {
    producerId: 1,
    producer: "MapResultWithSource#1",
    shape: "SealedFunction",
    watermark: "True",
    note: null,
    tick: 5,
    seq: 0,
    stale: false,
    total: 1,
    dropped: 0,
    rows: [{ key: "u0", value: '"a"', deleted: false }],
    ...overrides,
  };
}

function state(overrides: Partial<LiveState> = {}): LiveState {
  return {
    status: { kind: "live", tick: 5, published: 5 },
    nodes: new Map(),
    sources: new Map(),
    tags: [],
    tick: 5,
    generation: 0,
    ...overrides,
  };
}

const source: LiveSource = {
  nodeId: 208,
  name: "stdin",
  total: 2,
  dropped: 0,
  abandoned: 0,
  rows: [
    { key: "u0", value: '"a"', deleted: false },
    { key: "u1", value: '"b"', deleted: false },
  ],
};

describe("livePanelState", () => {
  // The four states are four different sentences, and conflating them is the
  // failure this union exists to prevent.
  it("says nothing is pinned before anything is", () => {
    expect(livePanelState(state()).kind).toBe("no-tags");
  });

  it("distinguishes a program that was not run from one that recorded nothing", () => {
    const notRun = state({ status: { kind: "connecting" }, tags: [{ id: "t10", label: "T10", anchorId: 10, nodes: [10], shown: true }] });
    expect(livePanelState(notRun).kind).toBe("not-run");

    const ranButSilent = livePanelState(state({ tags: [{ id: "t10", label: "T10", anchorId: 10, nodes: [10], shown: true }] }));
    expect(ranButSilent.kind).toBe("groups");
    if (ranButSilent.kind !== "groups") return;
    expect(ranButSilent.groups[0]?.kind).toBe("silent");
  });

  it("reports a lost connection ahead of anything else", () => {
    const lost = state({ status: { kind: "lost", clean: false }, tags: [{ id: "t10", label: "T10", anchorId: 10, nodes: [10], shown: true }] });
    const panel = livePanelState(lost);
    expect(panel.kind).toBe("lost");
    // The tags ride along, so the menu still lists them while the pane reports
    // the connection rather than emptying itself.
    if (panel.kind !== "lost") return;
    expect(panel.clean).toBe(false);
    expect(panel.tags.length).toBe(1);
  });

  it("orders groups by ascending node id, which is upstream first", () => {
    const panel = livePanelState(state({ tags: [{ id: "t30", label: "T30", anchorId: 30, nodes: [30], shown: true }, { id: "t10", label: "T10", anchorId: 10, nodes: [10], shown: true }, { id: "t20", label: "T20", anchorId: 20, nodes: [20], shown: true }] }));
    expect(panel.kind).toBe("groups");
    if (panel.kind !== "groups") return;
    expect(panel.groups.map((g) => g.nodeId)).toEqual([10, 20, 30]);
  });

  // Staleness is the gap between the newest tick and the entry's own, so it
  // survives as a number the pane can state.
  it("carries how far behind an entry is", () => {
    const panel = livePanelState(
      state({ tags: [{ id: "t10", label: "T10", anchorId: 10, nodes: [10], shown: true }], nodes: new Map([[10, { tick: 2, producers: [producer()] }]]) }),
    );
    if (panel.kind !== "groups") throw new Error("expected groups");
    const group = panel.groups[0];
    expect(group?.kind).toBe("operator");
    if (group?.kind !== "operator") return;
    expect(group.staleBy).toBe(3);
  });

  it("renders a pinned source as its retained window", () => {
    const panel = livePanelState(
      state({ tags: [{ id: "t208", label: "T208", anchorId: 208, nodes: [208], shown: true }], sources: new Map([[208, source]]) }),
    );
    if (panel.kind !== "groups") throw new Error("expected groups");
    const group = panel.groups[0];
    expect(group?.kind).toBe("source");
  });
});

describe("serializeLivePanel", () => {
  it("states shown-of-total whenever rows were dropped", () => {
    const panel = livePanelState(
      state({
        tags: [{ id: "t10", label: "T10", anchorId: 10, nodes: [10], shown: true }],
        nodes: new Map([
          [10, { tick: 5, producers: [producer({ total: 40, dropped: 39 })] }],
        ]),
      }),
    );
    expect(serializeLivePanel(panel)).toContain("1 of 40 rows");
  });

  it("marks a deleted row in words, not by colour alone", () => {
    const panel = livePanelState(
      state({
        tags: [{ id: "t10", label: "T10", anchorId: 10, nodes: [10], shown: true }],
        nodes: new Map([
          [
            10,
            {
              tick: 5,
              producers: [producer({ rows: [{ key: "u1", value: '"skip"', deleted: true }] })],
            },
          ],
        ]),
      }),
    );
    expect(serializeLivePanel(panel)).toContain('u1: "skip" (deleted)');
  });

  it("carries an unrendered shape's reason instead of pretending it is empty", () => {
    const panel = livePanelState(
      state({
        tags: [{ id: "t10", label: "T10", anchorId: 10, nodes: [10], shown: true }],
        nodes: new Map([
          [10, { tick: 5, producers: [producer({ shape: "Store", rows: [], total: 0, note: "a store is a changelog" })] }],
        ]),
      }),
    );
    expect(serializeLivePanel(panel)).toContain("a store is a changelog");
  });
});

describe("countOf and staleText", () => {
  it("omits the total when nothing was dropped", () => {
    expect(countOf(3, 3)).toBe("3 rows");
    expect(countOf(2, 9)).toBe("2 of 9 rows");
  });

  it("states staleness as ticks rather than a word", () => {
    expect(staleText(0, 5)).toBeNull();
    expect(staleText(4, 9)).toBe("last produced at tick 5 (now 9)");
  });
});

describe("tagColour", () => {
  // `TAG_SLOTS` and the stylesheet are two places that must agree: a slot with
  // no rule renders as slot 0's colour, silently collapsing two tags into one
  // hue. Vitest resolves a CSS import to a stub, so this cannot read the file
  // and check it — the pairing is manual, and `style.css` must define
  // `--tag-0`..`--tag-6` with their inks plus a `[data-colour]` rule for each
  // past the first.
  it("names as many slots as the stylesheet is documented to define", () => {
    expect(TAG_SLOTS).toBe(7);
  });

  it("stays in range and is stable for a label", () => {
    const labels = ["Var(words): L8", "MutWrite(total): L10", "Lit(Unit): L1", "Source(stdin)"];
    for (const label of labels) {
      const slot = tagColour(label, TAG_SLOTS);
      expect(slot).toBeGreaterThanOrEqual(0);
      expect(slot).toBeLessThan(TAG_SLOTS);
      expect(tagColour(label, TAG_SLOTS)).toBe(slot);
    }
  });
});
