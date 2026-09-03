import { describe, expect, it } from "vitest";

import { validateLiveFrame } from "./liveValidate";

function row(key: string | null, value: string, deleted = false) {
  return { key, value, deleted };
}

function producer(overrides: Record<string, unknown> = {}) {
  return {
    producerId: 1,
    producer: "MapResultWithSource#1",
    shape: "SealedFunction",
    watermark: "True",
    note: null,
    tick: 1,
    seq: 0,
    stale: false,
    total: 1,
    dropped: 0,
    rows: [row("u0", '"a"')],
    ...overrides,
  };
}

function frame(overrides: Record<string, unknown> = {}) {
  return {
    tick: 1,
    published: 1,
    final: false,
    nodes: [{ nodeId: 202, producers: [producer()] }],
    sources: [{ nodeId: 208, name: "stdin", total: 1, dropped: 0, rows: [row("u0", '"a"')] }],
    ...overrides,
  };
}

describe("validateLiveFrame", () => {
  it("accepts a frame and returns it typed", () => {
    const f = validateLiveFrame(frame());
    expect(f.tick).toBe(1);
    expect(f.nodes[0]?.producers[0]?.rows[0]?.value).toBe('"a"');
    expect(f.sources[0]?.name).toBe("stdin");
  });

  it("names the failing path", () => {
    expect(() => validateLiveFrame(frame({ tick: "1" }))).toThrow(/frame\.tick/);
    const bad = frame({ nodes: [{ nodeId: 1, producers: [producer({ rows: [{ key: "u0" }] })] }] });
    expect(() => validateLiveFrame(bad)).toThrow(/nodes\[0\]\.producers\[0\]\.rows\[0\]\.value/);
  });

  // The counts are the pane's only claim about completeness, so a frame that
  // disagrees with itself must not reach a renderer that would present it as
  // whole.
  it("rejects counts that disagree with the rows that arrived", () => {
    const bad = frame({ nodes: [{ nodeId: 1, producers: [producer({ total: 9, dropped: 0 })] }] });
    expect(() => validateLiveFrame(bad)).toThrow(/counts/);
  });

  // Ascending order is what keeps the pane's groups from reshuffling; the
  // backend sorts, and unsorted the array arrived differently on every run.
  it("rejects nodes that are not in ascending id order", () => {
    const bad = frame({
      nodes: [
        { nodeId: 9, producers: [producer()] },
        { nodeId: 2, producers: [producer()] },
      ],
    });
    expect(() => validateLiveFrame(bad)).toThrow(/nodes\[1\]\.nodeId/);
  });

  it("rejects a node whose producers repeat an id", () => {
    const bad = frame({
      nodes: [{ nodeId: 1, producers: [producer({ producerId: 3 }), producer({ producerId: 3 })] }],
    });
    expect(() => validateLiveFrame(bad)).toThrow(/distinct producerIds/);
  });

  it("accepts a keyless row, which a Scalar produces", () => {
    const f = validateLiveFrame(
      frame({ nodes: [{ nodeId: 1, producers: [producer({ rows: [row(null, '"x"')] })] }] }),
    );
    expect(f.nodes[0]?.producers[0]?.rows[0]?.key).toBeNull();
  });
});
