// @vitest-environment jsdom
import { beforeAll, describe, expect, it } from "vitest";

import { fixture, stubLayout } from "./__fixtures__/helpers";
import listMinJson from "./__fixtures__/list_min.snapshot.json";
import { LiveStore } from "./liveStore";
import { LiveView } from "./liveView";
import { describePanes, renderApp } from "./main";
import { Store } from "./store";
import type { LiveFrame } from "./types";

const listMin = fixture(listMinJson);

// The view coalesces updates into one `requestAnimationFrame`, so an assertion
// made straight after a state change reads the frame before it. Awaiting one is
// the honest wait: it exercises the same path the browser takes.
function nextFrame(): Promise<void> {
  return new Promise((resolve) => requestAnimationFrame(() => resolve()));
}

function frame(overrides: Partial<LiveFrame> = {}): LiveFrame {
  return {
    tick: 3,
    published: 3,
    final: false,
    nodes: [
      {
        nodeId: 202,
        producers: [
          {
            producerId: 1,
            producer: "MapResultWithSource#1",
            shape: "SealedFunction",
            watermark: "True",
            note: null,
            tick: 3,
            seq: 0,
            stale: false,
            total: 3,
            dropped: 1,
            rows: [
              { key: "u1", value: '"skip"', deleted: true },
              { key: "u2", value: '"b"', deleted: false },
            ],
          },
        ],
      },
    ],
    sources: [],
    ...overrides,
  };
}

describe("the values pane", () => {
  beforeAll(stubLayout);

  it("joins the roster only when a live store is supplied", () => {
    expect(describePanes(new Store(listMin)).some((p) => p.id === "values")).toBe(false);
    expect(
      describePanes(new Store(listMin), new LiveStore()).some((p) => p.id === "values"),
    ).toBe(true);
  });

  it("renders as a pane in the row", () => {
    const root = document.createElement("div");
    renderApp(root, new Store(listMin), new LiveStore());
    const panel = root.querySelector('.panel[data-pane-id="values"]');
    expect(panel).not.toBeNull();
    expect(panel?.textContent).toContain("inspect data");
  });

  it("draws a pinned operator's rows, its counts, and the deleted mark", async () => {
    const live = new LiveStore();
    const body = document.createElement("div");
    new LiveView(body, live);
    live.apply(frame());
    live.inspect("Var(words): L8", [202]);
    await nextFrame();

    const text = body.textContent ?? "";
    expect(text).toContain("MapResultWithSource#1");
    expect(text).toContain("2 of 3 rows");
    expect(text).toContain('"skip"');
    // The marker for the rows truncation dropped, at the top of the list.
    expect(text).toContain("1 earlier rows not recorded");
    expect(body.querySelectorAll(".live-row.deleted").length).toBe(1);
  });

  // Retained-mode: a replacing frame updates the row in place rather than
  // rebuilding it, which is what preserves scroll position and selection.
  it("updates a row in place across frames", async () => {
    const live = new LiveStore();
    const body = document.createElement("div");
    new LiveView(body, live);
    live.inspect("Var(words): L8", [202]);
    live.apply(frame());
    await nextFrame();
    const before = body.querySelector(".live-row:not(.live-dropped)");

    live.apply(
      frame({
        tick: 4,
        nodes: [
          {
            nodeId: 202,
            producers: [
              {
                ...frame().nodes[0]!.producers[0]!,
                tick: 4,
                total: 2,
                dropped: 0,
                rows: [
                  { key: "u1", value: '"changed"', deleted: true },
                  { key: "u2", value: '"b"', deleted: false },
                ],
              },
            ],
          },
        ],
      }),
    );
    await nextFrame();
    const after = body.querySelector(".live-row:not(.live-dropped)");
    expect(after).toBe(before);
    expect(after?.textContent).toContain('"changed"');
  });

  // The query behind the hover affordance: relevance is "this position reaches
  // an operator", precomputed so a hover is a lookup rather than a graph walk.
  it("resolves anchor-pane nodes to the operators they reach", () => {
    const store = new Store(listMin);
    expect(store.liveAnchorPaneId).toBe("post-conversion");

    const anchorId = store.sourceAnchorPaneId!;
    const anchor = store.indicesFor(anchorId)!;
    const reaching = [...anchor.nodeById.keys()].filter(
      (id) => store.operatorsFor(id).length > 0,
    );
    expect(reaching.length).toBeGreaterThan(0);

    // Every answer is a node of the operator pane, never of the anchor pane.
    const operatorIds = new Set(
      store.panes.find((pane) => pane.id === "post-conversion")!.nodes.map((n) => n.nodeId),
    );
    for (const id of reaching) {
      for (const op of store.operatorsFor(id)) expect(operatorIds.has(op)).toBe(true);
    }

    // Ascending, so pinning several yields groups in upstream-first order.
    for (const id of reaching) {
      const ops = [...store.operatorsFor(id)];
      expect(ops).toEqual([...ops].sort((a, b) => a - b));
    }
  });

  it("offers nothing for a node that reaches no operator", () => {
    const store = new Store(listMin);
    expect(store.operatorsFor(-1)).toEqual([]);
  });

  it("says a pinned operator recorded nothing rather than showing an empty group", async () => {
    const live = new LiveStore();
    const body = document.createElement("div");
    new LiveView(body, live);
    live.apply(frame());
    live.inspect("Var(gone): L1", [999]);
    await nextFrame();
    expect(body.textContent).toContain("no values recorded");
  });
});
