// @vitest-environment jsdom
//
// The source pane under an `EditSession`: editable, reloading on `Mod-Enter`,
// switching the span lookups off while its text is not the compiled one,
// underlining a refused version, and carried across the redraw a reload causes.

import { beforeAll, describe, expect, it, vi } from "vitest";
import { EditorState } from "@codemirror/state";
import { EditorView, runScopeHandlers } from "@codemirror/view";
import { forEachDiagnostic } from "@codemirror/lint";

import { followReloads } from "./main";
import { LiveStore } from "./liveStore";
import { EditSession, type ReloadOutcome } from "./reload";
import { SourceView, editorDiagnostics, statusLine } from "./sourceView";
import { Store } from "./store";
import type { Snapshot } from "./types";

import { fixture, irPaneById, stubLayout, theNode } from "./__fixtures__/helpers";
import listMinJson from "./__fixtures__/list_min.snapshot.json";

const listMin = fixture(listMinJson);

/** `snap` describing `text` and the version `version` instead. */
function withSource(snap: Snapshot, text: string, version = snap.meta.version): Snapshot {
  return { ...snap, source: { ...snap.source, text }, meta: { ...snap.meta, version } };
}

/** A session whose sends answer `outcome`, and the mock recording them. */
function sessionAnswering(outcome: ReloadOutcome): { session: EditSession; send: ReturnType<typeof vi.fn> } {
  const send = vi.fn(async () => outcome);
  return { session: new EditSession(send), send };
}

function mount(snap: Snapshot, session?: EditSession): { view: SourceView; body: HTMLElement; store: Store } {
  const body = document.createElement("div");
  document.body.appendChild(body);
  const store = new Store(snap);
  return { view: new SourceView(body, store, undefined, session), body, store };
}

/** Press `Mod-Enter` in `view` (Ctrl, on jsdom's platform). */
function pressReload(view: SourceView): boolean {
  return runScopeHandlers(
    view.view,
    new KeyboardEvent("keydown", { key: "Enter", ctrlKey: true }),
    "editor",
  );
}

/** Press `Mod-Shift-Enter` in `view`. */
function pressRestart(view: SourceView): boolean {
  return runScopeHandlers(
    view.view,
    new KeyboardEvent("keydown", { key: "Enter", ctrlKey: true, shiftKey: true }),
    "editor",
  );
}

/** Type `text` at the end of `view`'s document. */
function typeAtEnd(view: SourceView, text: string): void {
  const end = view.view.state.doc.length;
  view.view.dispatch({ changes: { from: end, insert: text } });
}

const settle = () => new Promise((resolve) => setTimeout(resolve, 0));

describe("the source pane under an edit session", () => {
  beforeAll(stubLayout);

  it("is read-only without a session and editable with one", () => {
    expect(mount(listMin).view.view.state.facet(EditorState.readOnly)).toBe(true);
    const { session } = sessionAnswering({ kind: "reloaded", kept: 0, bound: 0 });
    expect(mount(listMin, session).view.view.state.facet(EditorState.readOnly)).toBe(false);
  });

  it("reloads the document on Mod-Enter, and reports the tally", async () => {
    const { session, send } = sessionAnswering({ kind: "reloaded", kept: 3, bound: 5 });
    const { view, body } = mount(listMin, session);
    typeAtEnd(view, "# edit\n");

    expect(pressReload(view)).toBe(true);
    expect(send).toHaveBeenCalledWith("reload", `${listMin.source.text}# edit\n`);
    await settle();
    // Still edited: the redraw that installs the version has not happened.
    expect(body.querySelector(".edit-status")?.textContent).toMatch(/^edited/);
    expect(statusLine(session.get(), false).text).toBe("reloaded · 3 of 5 operators kept");
  });

  // The payload's spans are bytes of the compiled text; over edited text they
  // would point at whatever now sits there.
  it("switches the span lookups off while the document is edited", async () => {
    const { session } = sessionAnswering({ kind: "reloaded", kept: 0, bound: 0 });
    const { view, body, store } = mount(listMin, session);
    const lit = theNode(irPaneById(listMin, "pre-inference"), "Lit(Int(1))");
    store.setSelection({ kind: "node", paneId: "pre-inference", nodeId: lit.nodeId });
    expect(body.querySelector(".cm-sel-node, .cm-link-node")).not.toBeNull();

    typeAtEnd(view, "x");
    await settle();
    expect(view.isEdited).toBe(true);
    expect(store.getResolved().selection).toBeNull();
    expect(body.querySelector(".cm-sel-node, .cm-link-node")).toBeNull();

    // A selection made in another pane paints nothing here.
    store.setSelection({ kind: "node", paneId: "pre-inference", nodeId: lit.nodeId });
    expect(body.querySelector(".cm-sel-node, .cm-link-node")).toBeNull();

    // Undoing the edit makes the document the compiled text again.
    view.view.dispatch({ changes: { from: view.view.state.doc.length - 1, to: view.view.state.doc.length } });
    await settle();
    expect(view.isEdited).toBe(false);
  });

  it("underlines a refused version's errors where the server put them", async () => {
    const text = "[1, 2, 3, 4]\nnowhere\n";
    const start = new TextEncoder().encode("[1, 2, 3, 4]\n").length;
    const { session } = sessionAnswering({
      kind: "rejected",
      message: "error: unbound `nowhere`",
      diagnostics: [{ severity: "error", message: "unbound", span: { file: 0, start, end: start + 7 } }],
      source: text,
    });
    const { view, body } = mount(listMin, session);
    view.view.dispatch({ changes: { from: 0, to: view.view.state.doc.length, insert: text } });

    pressReload(view);
    await settle();

    const marks: { from: number; to: number }[] = [];
    forEachDiagnostic(view.view.state, (_d, from, to) => marks.push({ from, to }));
    expect(marks.map(({ from, to }) => text.slice(from, to))).toEqual(["nowhere"]);
    expect(body.querySelector(".edit-status")?.textContent).toBe(
      "rejected · 1 error underlined · the running version is unchanged",
    );
  });
});

describe("the source pane once the run has finished", () => {
  beforeAll(stubLayout);

  // A finished program takes no reload, and a restart runs it again, so the
  // pane keeps taking typing and the strip says which chord is left.
  it("sends no reload, restarts on Mod-Shift-Enter, and says so", async () => {
    const { session, send } = sessionAnswering({ kind: "restarted" });
    const { view, body } = mount(listMin, session);
    session.finish();

    expect(view.view.state.facet(EditorState.readOnly)).toBe(false);
    expect(body.querySelector(".edit-status")?.textContent).toBe(
      "the program has finished · Ctrl+Shift+Enter restarts it with this text",
    );
    pressReload(view);
    expect(send).not.toHaveBeenCalled();

    typeAtEnd(view, "# again\n");
    expect(pressRestart(view)).toBe(true);
    expect(send).toHaveBeenCalledWith("restart", `${listMin.source.text}# again\n`);
    await settle();
    expect(statusLine(session.get(), false).text).toBe("restarted from a fresh compile");
  });
});

describe("editorDiagnostics", () => {
  it("converts byte spans to chars against the text that was sent", () => {
    const text = "é = nowhere\n";
    const start = new TextEncoder().encode("é = ").length;
    const [mark] = editorDiagnostics(
      [{ severity: "error", message: "m", span: { file: 0, start, end: start + 7 } }],
      text,
      text.length,
    );
    expect(text.slice(mark!.from, mark!.to)).toBe("nowhere");
  });

  // The reader keeps typing while a reload is in flight; CodeMirror throws on a
  // mark past the end of the document.
  it("clamps a span to a document that has since shrunk", () => {
    const [mark] = editorDiagnostics(
      [{ severity: "error", message: "m", span: { file: 0, start: 10, end: 20 } }],
      "0123456789abcdefghij",
      4,
    );
    expect(mark).toMatchObject({ from: 4, to: 4 });
  });
});

describe("a redraw under an edit session", () => {
  beforeAll(stubLayout);

  it("follows a new version, keeping the caret, when the pane was not edited", () => {
    const { session } = sessionAnswering({ kind: "reloaded", kept: 0, bound: 0 });
    const first = mount(listMin, session).view;
    first.view.dispatch({ selection: { anchor: 3 } });
    first.dispose();

    const next = withSource(listMin, "[1, 2, 3, 4, 5]\n", 2);
    const second = mount(next, session).view;
    expect(second.view.state.doc.toString()).toBe(next.source.text);
    expect(second.isEdited).toBe(false);
    expect(second.view.state.selection.main.head).toBe(3);
  });

  // A reload from elsewhere (another tab, the control port) must not throw away
  // text the reader typed and has not sent.
  it("keeps the reader's edit over a version they did not ask for", () => {
    const { session } = sessionAnswering({ kind: "reloaded", kept: 0, bound: 0 });
    const first = mount(listMin, session).view;
    typeAtEnd(first, "# mine\n");
    const edit = first.view.state.doc.toString();
    first.dispose();

    const second = mount(withSource(listMin, "[9]\n", 2), session).view;
    expect(second.view.state.doc.toString()).toBe(edit);
    expect(second.isEdited).toBe(true);
  });

  // The reader's own reload: the new version is the text they sent, so the
  // pane is no longer edited.
  it("is no longer edited once the version installed is the text sent", () => {
    const { session } = sessionAnswering({ kind: "reloaded", kept: 0, bound: 0 });
    const first = mount(listMin, session).view;
    typeAtEnd(first, "# mine\n");
    const sent = first.view.state.doc.toString();
    first.dispose();

    const second = mount(withSource(listMin, sent, 2), session).view;
    expect(second.isEdited).toBe(false);
  });

  it("is what followReloads does when a frame names a later version", async () => {
    const { session } = sessionAnswering({ kind: "reloaded", kept: 0, bound: 0 });
    const root = document.createElement("div");
    document.body.appendChild(root);
    const live = new LiveStore();
    const next = withSource(listMin, "[9]\n", 2);
    followReloads(root, live, listMin, async () => next, session);

    const view = () => EditorView.findFromDOM(root.querySelector<HTMLElement>(".cm-content")!)!;
    view().dispatch({ changes: { from: 0, insert: "# mine\n" } });

    live.apply({ version: 2, published: 1, final: false, nodes: [], sources: [] });
    await settle();
    await settle();

    expect(view().state.doc.toString()).toBe(`# mine\n${listMin.source.text}`);
    expect(root.querySelector(".edit-status")?.textContent).toMatch(/^edited/);
  });
});
