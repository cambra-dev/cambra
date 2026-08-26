// Unit tests for main.ts's pure helpers (byte/line/col math, span formatting)
// and a jsdom degraded-render test over the `failed` fixture.
//
// Importing main.ts runs its `void main()` auto-invocation, which is guarded on
// `document.getElementById("app")`. The unit-test DOM has no `#app`, so the
// import does not fire a `/api/snapshot` fetch.

// @vitest-environment jsdom

import { beforeAll, describe, expect, it } from "vitest";

import {
  byteLineStarts,
  diagnosticLines,
  formatSpan,
  lineCol,
  renderApp,
  serializeDiagnostics,
} from "./main";
import { Store } from "./store";
import { fixture, stubLayout } from "./__fixtures__/helpers";

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

describe("serializeDiagnostics", () => {
  const starts = byteLineStarts("ab\ncd\n");
  const diag = (message: string, span: { start: number; end: number } | null) => ({
    severity: "error",
    stage: "Infer",
    message,
    span,
    labels: [],
  });

  it("renders severity · stage, message, and the line:col span", () => {
    expect(serializeDiagnostics([diag("mismatched types", { start: 0, end: 4 })], starts)).toBe(
      "error · Infer\nmismatched types\n1:1–2:2",
    );
  });

  it("renders 'no span' for a spanless diagnostic", () => {
    expect(serializeDiagnostics([diag("boom", null)], starts)).toBe("error · Infer\nboom\nno span");
  });

  it("separates cards with a blank line", () => {
    const text = serializeDiagnostics([diag("one", null), diag("two", null)], starts);
    expect(text).toBe("error · Infer\none\nno span\n\nerror · Infer\ntwo\nno span");
  });

  it("reports the empty case with the text the pane itself shows", () => {
    // The pane's `.empty` row and this string come from one constant; asserting
    // both against the same literal is what keeps them from drifting apart.
    expect(serializeDiagnostics([], starts)).toBe("No diagnostics, but the IR is unavailable.");
  });

  it("is built from the same lines the pane renders", () => {
    const d = diag("mismatched types", { start: 0, end: 4 });
    expect(serializeDiagnostics([d], starts)).toBe(diagnosticLines(d, starts).join("\n"));
  });
});

describe("renderApp: degraded snapshot (failed compile)", () => {
  const failed = fixture(failedJson);

  // CodeMirror's SourceView renders even in the degraded case.
  beforeAll(stubLayout);

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

  it("gives both degraded panes a copy button", () => {
    const root = document.createElement("div");
    document.body.appendChild(root);

    renderApp(root, new Store(failed));

    // Source and Diagnostics — the copy affordance is not a property of having
    // an IR tree.
    expect(root.querySelectorAll(".pane-copy").length).toBe(2);
    expect(root.querySelector(".pane-copy")?.textContent).toBe("Copy");
  });
});
