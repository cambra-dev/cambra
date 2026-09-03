// Unit tests for main.ts's pure helpers (byte/line/col math, span formatting)
// and a jsdom degraded-render test over the `failed` fixture.
//
// Importing main.ts runs its `void main()` auto-invocation, which is guarded on
// `document.getElementById("app")`. The unit-test DOM has no `#app`, so the
// import does not fire a `/api/snapshot` fetch.

// @vitest-environment jsdom

import { beforeAll, describe, expect, it } from "vitest";

import { byteLineStarts, formatSpan, lineCol, renderApp } from "./main";
import { Store } from "./store";
import { fixture } from "./__fixtures__/helpers";

import failedJson from "./__fixtures__/failed.snapshot.json";

describe("byteLineStarts / lineCol (byte offsets)", () => {
  it("records the byte offset of each line start (ASCII)", () => {
    // "ab\ncd\n" -> line starts at byte 0, 3, 6.
    expect(byteLineStarts("ab\ncd\n")).toEqual([0, 3, 6]);
  });

  it("counts multi-byte characters as their UTF-8 byte length", () => {
    // "é" is 2 UTF-8 bytes; "café\nx" -> next line starts at byte 5
    // (c=1,a=1,f=1,é=2 = 5, then "\n" is byte 5 so the next line starts at 6).
    const text = "café\nx";
    const starts = byteLineStarts(text);
    expect(starts).toEqual([0, 6]);
    // A position just before the newline (the "é", byte 3) is line 1.
    expect(lineCol(3, starts)).toBe("1:4");
    // The "x" on the second line is byte 6 -> line 2, col 1.
    expect(lineCol(6, starts)).toBe("2:1");
  });

  it("lineCol returns 1-based line:col on the first line", () => {
    const starts = byteLineStarts("hello");
    expect(lineCol(0, starts)).toBe("1:1");
    expect(lineCol(4, starts)).toBe("1:5");
  });
});

describe("formatSpan", () => {
  it("formats a non-null span as a line:col range", () => {
    const starts = byteLineStarts("ab\ncd\n");
    expect(formatSpan({ start: 0, end: 4 }, starts)).toBe("1:1–2:2");
  });

  it("returns 'no span' for a null span", () => {
    expect(formatSpan(null, byteLineStarts("x"))).toBe("no span");
  });
});

describe("renderApp: degraded snapshot (failed compile)", () => {
  const failed = fixture(failedJson);

  beforeAll(() => {
    // CodeMirror's SourceView (rendered even in the degraded case) calls these.
    (Element.prototype as unknown as { scrollIntoView: () => void }).scrollIntoView = () => {};
    const emptyRects = () => ({ length: 0, item: () => null, [Symbol.iterator]: function* () {} });
    const emptyRect = () => ({ top: 0, left: 0, bottom: 0, right: 0, width: 0, height: 0, x: 0, y: 0 });
    (Range.prototype as unknown as { getClientRects: () => unknown }).getClientRects = emptyRects as never;
    (Range.prototype as unknown as { getBoundingClientRect: () => unknown }).getBoundingClientRect = emptyRect as never;
    (Element.prototype as unknown as { getClientRects: () => unknown }).getClientRects = emptyRects as never;
    (Element.prototype as unknown as { getBoundingClientRect: () => unknown }).getBoundingClientRect = emptyRect as never;
  });

  it("renders a diagnostics list (with the error message) and no tree panes", () => {
    const root = document.createElement("div");
    document.body.appendChild(root);

    expect(failed.meta.payloadKind).toBe("failed");
    expect(failed.panes).toEqual([]);

    renderApp(root, new Store(failed));

    // The degraded branch renders a Diagnostics pane with the error.
    const diags = root.querySelectorAll(".diag");
    expect(diags.length).toBe(failed.diagnostics.length);
    expect(diags.length).toBeGreaterThan(0);
    expect(root.querySelector(".diag-msg")?.textContent).toBe(failed.diagnostics[0].message);

    // No IR tree panes render in the degraded case.
    expect(root.querySelectorAll(".tree-root").length).toBe(0);
  });
});
