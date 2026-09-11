// Unit tests for main.ts's pure helpers (byte/line/col math, span formatting)
// and a jsdom degraded-render test over the `failed` fixture.
//
// Importing main.ts runs its `void main()` auto-invocation, which is guarded on
// `document.getElementById("app")`. The unit-test DOM has no `#app`, so the
// import does not fire a `/api/snapshot` fetch.

// @vitest-environment jsdom

import { EditorView } from "@codemirror/view";
import { afterEach, beforeAll, beforeEach, describe, expect, it, vi } from "vitest";

import {
  applyPins,
  byteLineStarts,
  describePanes,
  diagnosticLines,
  formatSpan,
  lineCol,
  renderApp,
  serializeDiagnostics,
} from "./main";
import { LiveStore } from "./liveStore";
import { Store } from "./store";
import { isIrPane } from "./types";
import { fixture, stubLayout } from "./__fixtures__/helpers";

import failedJson from "./__fixtures__/failed.snapshot.json";
import listMinJson from "./__fixtures__/list_min.snapshot.json";
import arithmeticJson from "./__fixtures__/arithmetic.snapshot.json";

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

  it("marks the diagnostic's source span the moment the view mounts", () => {
    const root = document.createElement("div");
    document.body.appendChild(root);

    renderApp(root, new Store(failed));

    // No timer, no await: the squiggles are in the DOM as `renderApp` returns.
    // A debounced re-lint would leave the mark absent here and dispatch into
    // the view later, after the caller has dropped it.
    const marks = root.querySelectorAll(".panel.source .cm-lintRange-error");
    expect(marks.length).toBe(failed.diagnostics.length);
    expect(marks[0].textContent).toBe(failed.source.text.slice(0, 7));
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

describe("describePanes", () => {
  const listMin = fixture(listMinJson);
  const failed = fixture(failedJson);

  it("names the source pane first, then one pane per pipeline pane in order", () => {
    // Source-first is not cosmetic: it is mounted first, so the CodeMirror
    // editor lays out against a panel that is briefly the whole row.
    const store = new Store(listMin);
    expect(describePanes(store).map((p) => p.id)).toEqual([
      "source",
      ...store.panes.map((s) => s.id),
    ]);
  });

  it("puts the operator pane last on the roster and mounts its renderer", () => {
    // The operator pane is a pane like any other now that `OperatorView` draws
    // the graph: it holds the roster slot its pipeline position gives it, which
    // is last — conversion is the most downstream pane.
    const store = new Store(listMin);
    const operatorPanes = store.panes.filter((pane) => !isIrPane(pane));
    expect(operatorPanes.length).toBe(1);

    const roster = describePanes(store);
    expect(roster[roster.length - 1].id).toBe(operatorPanes[0].id);

    // The descriptor mounts a real view, not an empty body. What that view draws
    // is `operatorView.dom.test.ts`'s to assert, against a layout it controls;
    // the roster's own claim is that the mount happened and put a graph there.
    const body = document.createElement("div");
    document.body.appendChild(body);
    roster[roster.length - 1].mount(body);
    expect(body.querySelectorAll(".graph-canvas").length).toBe(1);
  });

  it("badges the holes pane and the operator pane", () => {
    const panes = describePanes(new Store(listMin));
    const badged = panes.filter((p) => p.badge !== undefined);
    expect(badged.map((p) => [p.id, p.badge])).toEqual([
      ["pre-inference", "pre-inference (holes)"],
      ["post-conversion", "dataflow"],
    ]);
  });

  it("replaces the IR panes with a diagnostics pane on a degraded snapshot", () => {
    expect(describePanes(new Store(failed)).map((p) => p.id)).toEqual(["source", "diagnostics"]);
  });
});

describe("renderApp: pane visibility", () => {
  const listMin = fixture(listMinJson);

  let root: HTMLElement;

  const panelFor = (id: string): HTMLElement =>
    root.querySelector(`.panel[data-pane-id="${id}"]`)!;
  const boxFor = (id: string): HTMLInputElement =>
    root.querySelector(`.pane-menu-panel input[value="${id}"]`)!;
  const toggle = (id: string, checked: boolean): void => {
    const box = boxFor(id);
    box.checked = checked;
    box.dispatchEvent(new Event("change", { bubbles: true }));
  };

  beforeAll(stubLayout);

  beforeEach(() => {
    // This environment's `window.localStorage` is a stub with no methods, so
    // install a working one: renderApp persists the hidden set through it, and
    // each test starts from an empty store.
    const entries = new Map<string, string>();
    Object.defineProperty(window, "localStorage", {
      value: {
        getItem: (key: string) => entries.get(key) ?? null,
        setItem: (key: string, value: string) => void entries.set(key, value),
      },
      configurable: true,
    });

    document.body.replaceChildren();
    root = document.createElement("div");
    document.body.appendChild(root);
    renderApp(root, new Store(listMin));
  });

  afterEach(() => {
    vi.restoreAllMocks();
    Reflect.deleteProperty(window, "localStorage");
  });

  it("tags one panel per descriptor with its pane id", () => {
    const ids = [...root.querySelectorAll<HTMLElement>(".panel")].map((p) => p.dataset.paneId);
    expect(ids).toEqual(describePanes(new Store(listMin)).map((p) => p.id));
  });

  it("hides a pane without unmounting its view", () => {
    const panel = panelFor("post-inference");
    expect(panel.querySelector(".tree-root")).not.toBeNull();

    toggle("post-inference", false);

    expect(panel.classList.contains("hidden")).toBe(true);
    // The view stays: rebuilding it would leak its store subscription and lose
    // every expand/collapse the user set.
    expect(panel.querySelector(".tree-root")).not.toBeNull();
  });

  it("keeps a hidden pane tracking the selection, so revealing it is instant", () => {
    const panel = panelFor("post-inference");
    toggle("post-inference", false);

    // Select through a visible pane; the hidden one must follow.
    root.querySelector<HTMLElement>('.panel[data-pane-id="pre-inference"] .tree-row')!.click();

    expect(panel.querySelectorAll(".tree-row.selected, .tree-row.linked").length).toBeGreaterThan(0);
  });

  it("shows a hidden pane again", () => {
    toggle("post-inference", false);
    toggle("post-inference", true);
    expect(panelFor("post-inference").classList.contains("hidden")).toBe(false);
  });

  it("re-measures the CodeMirror editor when the source pane is revealed", () => {
    // A hidden editor never measured against a real box, and does not reliably
    // measure itself on reveal.
    const measure = vi.spyOn(EditorView.prototype, "requestMeasure");
    toggle("source", false);
    measure.mockClear();

    toggle("source", true);
    expect(measure).toHaveBeenCalled();
  });

  it("moves the last-visible marker off a hidden rightmost pane", () => {
    const panels = [...root.querySelectorAll<HTMLElement>(".panel")];
    const last = panels[panels.length - 1];
    expect(last.classList.contains("last-visible")).toBe(true);

    toggle(last.dataset.paneId!, false);

    expect(last.classList.contains("last-visible")).toBe(false);
    expect(panels[panels.length - 2].classList.contains("last-visible")).toBe(true);
  });

  it("persists the hidden set across a re-render", () => {
    toggle("post-inference", false);

    const next = document.createElement("div");
    document.body.appendChild(next);
    renderApp(next, new Store(listMin));

    expect(
      next.querySelector<HTMLElement>('.panel[data-pane-id="post-inference"]')!.classList.contains(
        "hidden",
      ),
    ).toBe(true);
  });
});

describe("an embedder's configuration", () => {
  beforeAll(stubLayout);

  /**
   * A pin travels as a source position, not a `NodeId`: ids are minted per
   * compile, which is why the values pane declines to persist a tag. A position
   * in the text survives every compile of that text.
   */
  it("resolves a pin at a source position to the operators there", () => {
    const store = new Store(fixture(arithmeticJson));
    const live = new LiveStore();
    const lineStarts = byteLineStarts(store.snapshot.source.text);

    // The first line's first identifier — whatever `arithmetic` binds there.
    const pinned = applyPins(store, live, [{ line: 1, col: 1 }], lineStarts);

    expect(pinned).toBe(1);
    const tags = live.get().tags;
    expect(tags).toHaveLength(1);
    expect(tags[0]?.nodes.length).toBeGreaterThan(0);
  });

  /**
   * A deck whose program has moved on opens with fewer pins rather than an
   * error in front of an audience.
   */
  it("skips a position that names no operator", () => {
    const store = new Store(fixture(arithmeticJson));
    const live = new LiveStore();
    const lineStarts = byteLineStarts(store.snapshot.source.text);

    expect(applyPins(store, live, [{ line: 9999, col: 1 }], lineStarts)).toBe(0);
    expect(live.get().tags).toHaveLength(0);
  });

  /**
   * The hidden set an embedder asks for wins over the stored one: it is asking
   * for a layout on this page, where the stored set is what some other reader
   * last chose.
   */
  it("opens with the panes an embedder hid", () => {
    const root = document.createElement("div");
    const store = new Store(fixture(arithmeticJson));
    const hidden = ["pre-inference", "post-inference"];
    renderApp(root, store, undefined, { hiddenPanes: hidden });

    const paneIds = (selector: string) =>
      Array.from(root.querySelectorAll(selector)).map(
        (p) => (p as HTMLElement).dataset.paneId,
      );
    const shown = paneIds(".panel:not(.hidden)");
    const all = paneIds(".panel");

    expect(all).toEqual(expect.arrayContaining(hidden));
    for (const id of hidden) expect(shown).not.toContain(id);
    expect(shown).toContain("source");
    expect(shown.length).toBe(all.length - hidden.length);
  });
});

describe("the header's values badge", () => {
  beforeAll(stubLayout);

  /**
   * The badge answers whether values are flowing, which is a different question
   * from whether the payload compiled. It was a constant reading "static (no
   * values)", which sat over a values pane filling up.
   */
  it("says values are waiting before a frame arrives", () => {
    const root = document.createElement("div");
    renderApp(root, new Store(fixture(arithmeticJson)), new LiveStore());
    const badges = Array.from(root.querySelectorAll(".badge")).map((b) => b.textContent);
    expect(badges).toContain("waiting for values");
    expect(badges).not.toContain("static (no values)");
  });

  it("says a run is live once it publishes", () => {
    const root = document.createElement("div");
    const live = new LiveStore();
    renderApp(root, new Store(fixture(arithmeticJson)), live);
    live.apply({ tick: 7, generation: 0, published: 3, final: false, nodes: [], sources: [] });
    const badges = Array.from(root.querySelectorAll(".badge")).map((b) => b.textContent);
    expect(badges).toContain("live · tick 7");
  });

  /** With no live store there is no run, and the badge still says so. */
  it("keeps the static wording when nothing is driving the program", () => {
    const root = document.createElement("div");
    renderApp(root, new Store(fixture(arithmeticJson)));
    const badges = Array.from(root.querySelectorAll(".badge")).map((b) => b.textContent);
    expect(badges).toContain("static (no values)");
  });
});
