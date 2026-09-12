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
    generation: 0,
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
    live.inspect("Var(words): L8", 202, [202]);
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
    live.inspect("Var(words): L8", 202, [202]);
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

  // The property the `locate` kind exists for. A `node` selection on an
  // operator answers with the construct that produced it — conversion gives a
  // whole recurrence the statement's span — so it lights up the loop. This asks
  // only to go there.
  it("locates an operator without resolving anything else", () => {
    const store = new Store(listMin);
    const paneId = store.liveAnchorPaneId!;
    const operators = store.panes.find((pane) => pane.id === paneId)!.nodes;
    const target = operators[Math.floor(operators.length / 2)]!.nodeId;

    store.setSelection({ kind: "locate", paneId, nodeId: target });
    const resolved = store.getResolved();

    // Exactly one node, in exactly one pane.
    for (const pane of store.panes) {
      const highlighted = resolved.result.highlightsByPane.get(pane.id) ?? new Set();
      const primary = resolved.primaryByPane.get(pane.id) ?? new Set();
      const expected = pane.id === paneId ? new Set([target]) : new Set<number>();
      expect([...highlighted].sort()).toEqual([...expected].sort());
      expect([...primary].sort()).toEqual([...expected].sort());
    }
    // And nothing in the source, whose span would be the whole construct.
    expect(resolved.result.sourceSpans).toEqual([]);
    expect(resolved.pointedAt).toBeNull();
  });

  // The contrast, on the same node: asking the program about it resolves wide.
  it("a node selection on the same operator resolves further", () => {
    const store = new Store(listMin);
    const paneId = store.liveAnchorPaneId!;
    const operators = store.panes.find((pane) => pane.id === paneId)!.nodes;
    const target = operators[Math.floor(operators.length / 2)]!.nodeId;

    store.setSelection({ kind: "locate", paneId, nodeId: target });
    const located = store.getResolved().result.highlightsByPane;
    const locatedTotal = [...located.values()].reduce((n, s) => n + s.size, 0);

    store.setSelection({ kind: "node", paneId, nodeId: target });
    const asked = store.getResolved().result.highlightsByPane;
    const askedTotal = [...asked.values()].reduce((n, s) => n + s.size, 0);

    expect(locatedTotal).toBe(1);
    expect(askedTotal).toBeGreaterThan(locatedTotal);
  });

  // Reading around in the pane must not disturb what it shows: a click selects
  // and nothing else, which is why the view listens to the live store and not
  // to the selection.
  it("selects a construct from its tag chip and an operator from its head", async () => {
    const live = new LiveStore();
    const body = document.createElement("div");
    const constructs: number[] = [];
    const operators: number[] = [];
    new LiveView(body, live, () => undefined, {
      construct: (id: number) => constructs.push(id),
      operator: (id: number) => operators.push(id),
    });
    live.apply(frame());
    live.inspect("Var(words): L8", 42, [202]);
    await nextFrame();

    const chip = body.querySelector<HTMLButtonElement>(".live-tag-button")!;
    expect(chip.textContent).toBe("Var(words): L8");
    chip.click();
    expect(constructs).toEqual([42]);
    // The chip sits inside the group, so its click must not also reach the head.
    expect(operators).toEqual([]);

    body.querySelector<HTMLButtonElement>("button.live-group-head")!.click();
    expect(operators).toEqual([202]);

    // Neither gesture touched the tags.
    expect(live.get().tags.length).toBe(1);
    expect(live.get().tags[0]?.shown).toBe(true);
  });

  // Without the callbacks the pane is inert text, which is what `--inspect-only`
  // gets: nothing is running, so there is nothing to select from.
  it("renders plain chips when no selection sink is supplied", async () => {
    const live = new LiveStore();
    const body = document.createElement("div");
    new LiveView(body, live);
    live.apply(frame());
    live.inspect("Var(words): L8", 42, [202]);
    await nextFrame();

    expect(body.querySelector(".live-tag")).not.toBeNull();
    expect(body.querySelector(".live-tag-button")).toBeNull();
    expect(body.querySelector("button.live-group-head")).toBeNull();
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
    live.inspect("Var(gone): L1", 999, [999]);
    await nextFrame();
    // No row has ever reached it. Whether nothing pulled it or every pull
    // answered empty is not something the frame separates.
    expect(body.textContent).toContain("nothing has flowed here yet");
  });

  // The operator's kind comes from the static payload, so a group is named even
  // with no recording — the frame names a *producer*, and only once one has run.
  it("names an operator that has recorded nothing", async () => {
    const live = new LiveStore();
    const body = document.createElement("div");
    new LiveView(body, live, (id) => (id === 999 ? "ExtractFinal" : undefined));
    live.apply(frame());
    live.inspect("Var(gone): L1", 999, [999]);
    await nextFrame();

    expect(body.textContent).toContain("#999 ExtractFinal");
    expect(body.textContent).toContain("nothing has flowed here yet");
  });

  // Once the run is over, having carried nothing is permanent rather than
  // pending, and reads differently.
  it("says a silent operator produced nothing once the run has finished", async () => {
    const live = new LiveStore();
    const body = document.createElement("div");
    new LiveView(body, live, () => "ExtractFinal");
    live.apply({ ...frame(), final: true });
    live.inspect("Var(gone): L1", 999, [999]);
    await nextFrame();

    expect(body.textContent).toContain("nothing flowed here during the run");
    expect(body.textContent).not.toContain("nothing has flowed here yet");
  });

  // A recorded operator shows both: what it is, and which producer ran.
  it("shows an operator's kind alongside its producer", async () => {
    const live = new LiveStore();
    const body = document.createElement("div");
    new LiveView(body, live, (id) => (id === 202 ? "MapResult" : undefined));
    live.apply(frame());
    live.inspect("Var(words): L8", 42, [202]);
    await nextFrame();

    const text = body.textContent ?? "";
    expect(text).toContain("#202 MapResult");
    expect(text).toContain("MapResultWithSource#1");
  });
});

/**
 * A panel that has said "no values yet" and then receives some drops the
 * message. Groups are appended to the root rather than replacing it, so a
 * message left behind would sit above live rows saying the run never started.
 */
it("drops the empty message once values arrive", async () => {
  const live = new LiveStore();
  const body = document.createElement("div");
  new LiveView(body, live);
  live.inspect("Var(words): L8", 202, [202]);
  await nextFrame();

  expect(body.querySelector(".live-empty")).not.toBeNull();

  live.apply(frame());
  await nextFrame();

  expect(body.querySelector(".live-empty")).toBeNull();
  expect(body.querySelectorAll(".live-group").length).toBe(1);
});
