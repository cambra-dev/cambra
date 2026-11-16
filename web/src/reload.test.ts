import { describe, expect, it, vi } from "vitest";

import { LiveStore } from "./liveStore";
import {
  EditSession,
  type ReloadOutcome,
  followRun,
  outcomeOf,
  postVersion,
  reloadingOnRestart,
  serverCapabilities,
} from "./reload";

/** A `fetch` answering every call with `status` and `body`. */
function answering(status: number, body: unknown): typeof fetch & { mock: { calls: unknown[][] } } {
  return vi.fn(async () => new Response(JSON.stringify(body), { status })) as never;
}

describe("outcomeOf", () => {
  it("reads an accepted restart", () => {
    expect(outcomeOf(200, { message: "restarted" }, "src", "restart")).toEqual({ kind: "restarted" });
  });

  it("reads an accepted reload's tally", () => {
    expect(outcomeOf(200, { message: "reloaded", kept: 3, bound: 5 }, "src")).toEqual({
      kind: "reloaded",
      kept: 3,
      bound: 5,
    });
  });

  it("reads a refusal's diagnostics against the text that was sent", () => {
    const diagnostics = [{ severity: "error", message: "unbound", span: { file: 0, start: 1, end: 2 } }];
    expect(outcomeOf(400, { message: "error: unbound", diagnostics }, "src")).toEqual({
      kind: "rejected",
      message: "error: unbound",
      diagnostics,
      source: "src",
    });
  });

  // A run without a control port, an admission refusal, a finished program and
  // no program to reach are the request not reaching a program, not the program
  // refusing a version.
  it("reads every other status as a failure, with the server's message", () => {
    for (const status of [403, 404, 409, 415, 503]) {
      expect(outcomeOf(status, { message: "why" }, "src")).toEqual({ kind: "failed", message: "why" });
    }
    expect(outcomeOf(500, {}, "src")).toEqual({ kind: "failed", message: "HTTP 500" });
  });
});

describe("postVersion", () => {
  // JSON is what keeps a cross-site form or `no-cors` fetch out, so the page has
  // to send it.
  it("posts the source as JSON to this page's own server", async () => {
    const fetchImpl = answering(200, { kept: 1, bound: 1 });
    await postVersion(fetchImpl)("reload", "x = 1\n");

    const [url, init] = fetchImpl.mock.calls[0] as [string, RequestInit];
    expect(url).toBe("/api/reload");
    expect(init.method).toBe("POST");
    expect(new Headers(init.headers).get("Content-Type")).toBe("application/json");
    expect(JSON.parse(init.body as string)).toEqual({ source: "x = 1\n" });
  });

  it("posts a restart to its own route", async () => {
    const fetchImpl = answering(200, { message: "restarted" });
    expect(await postVersion(fetchImpl)("restart", "x = 1\n")).toEqual({ kind: "restarted" });
    expect((fetchImpl.mock.calls[0] as [string])[0]).toBe("/api/restart");
  });

  it("reports a body that is not JSON by its status", async () => {
    const fetchImpl = vi.fn(async () => new Response("<html>", { status: 502 })) as never;
    expect(await postVersion(fetchImpl)("reload", "x")).toEqual({ kind: "failed", message: "HTTP 502" });
  });
});

describe("serverCapabilities", () => {
  it("is the server's `reload` capability and its process's instance", async () => {
    expect(await serverCapabilities(answering(200, { reload: true, instance: "7-1" }))).toEqual({
      reload: true,
      instance: "7-1",
    });
    expect(await serverCapabilities(answering(200, { reload: false }))).toEqual({
      reload: false,
      instance: null,
    });
  });

  // A server that predates the route, or one that cannot be reached, leaves the
  // pane read-only rather than editable with nothing behind the chord.
  it("is null when the capabilities cannot be read", async () => {
    expect(await serverCapabilities(answering(404, {}))).toBeNull();
    const throwing = vi.fn(async () => {
      throw new Error("offline");
    }) as never;
    expect(await serverCapabilities(throwing)).toBeNull();
  });
});

describe("reloadingOnRestart", () => {
  /** A `fetch` answering `/api/capabilities` with each of `answers` in turn; `null` is a closed port. */
  function capabilitiesInTurn(answers: (string | null)[]): typeof fetch {
    return vi.fn(async () => {
      const instance = answers.length > 1 ? answers.shift()! : answers[0]!;
      if (instance === null) throw new Error("connection refused");
      return new Response(JSON.stringify({ reload: true, instance }), { status: 200 });
    }) as never;
  }

  // The old process answers until it is replaced, the port is closed while the
  // new one starts, and the new one answers its own instance.
  it("loads the page once the restarted process answers", async () => {
    const loadPage = vi.fn();
    const send = reloadingOnRestart(async () => ({ kind: "restarted" }), "old", {
      fetchImpl: capabilitiesInTurn(["old", null, "new"]),
      loadPage,
      pollMs: 0,
    });
    expect(await send("restart", "x")).toEqual({ kind: "restarted" });
    expect(loadPage).toHaveBeenCalledTimes(1);
  });

  it("reports a restarted process that never answers as a failure", async () => {
    const loadPage = vi.fn();
    const send = reloadingOnRestart(async () => ({ kind: "restarted" }), "old", {
      fetchImpl: capabilitiesInTurn([null]),
      loadPage,
      pollMs: 0,
      within: 20,
    });
    expect(await send("restart", "x")).toEqual({
      kind: "failed",
      message: "the restarted process never answered",
    });
    expect(loadPage).not.toHaveBeenCalled();
  });

  it("passes every other outcome through without waiting", async () => {
    const fetchImpl = capabilitiesInTurn(["new"]);
    const loadPage = vi.fn();
    const send = reloadingOnRestart(async () => ({ kind: "reloaded", kept: 1, bound: 1 }), "old", {
      fetchImpl,
      loadPage,
    });
    expect(await send("reload", "x")).toEqual({ kind: "reloaded", kept: 1, bound: 1 });
    expect(fetchImpl).not.toHaveBeenCalled();
    expect(loadPage).not.toHaveBeenCalled();
  });
});

describe("EditSession", () => {
  it("reports the reload in flight, then its outcome", async () => {
    let finish: (outcome: ReloadOutcome) => void = () => {};
    const session = new EditSession(() => new Promise((resolve) => (finish = resolve)));
    const seen: string[] = [];
    session.subscribe((status) => seen.push(status.kind));

    const pending = session.reload("x");
    expect(session.get().kind).toBe("reloading");
    finish({ kind: "reloaded", kept: 0, bound: 0 });
    await pending;

    expect(seen).toEqual(["reloading", "reloaded"]);
  });

  // A second reload would race the first to the branch table, and the one that
  // lost would be the one on screen.
  it("refuses a reload while one is in flight", async () => {
    let finish: (outcome: ReloadOutcome) => void = () => {};
    const send = vi.fn(() => new Promise<ReloadOutcome>((resolve) => (finish = resolve)));
    const session = new EditSession(send);

    const first = session.reload("a");
    expect(await session.reload("b")).toBeNull();
    finish({ kind: "reloaded", kept: 0, bound: 0 });
    await first;

    expect(send).toHaveBeenCalledTimes(1);
  });

  it("reports a send that throws as a failure", async () => {
    const session = new EditSession(async () => {
      throw new Error("network down");
    });
    expect(await session.reload("x")).toEqual({ kind: "failed", message: "Error: network down" });
  });

  // A finished program takes no reload, so the session sends none; it takes a
  // restart, which is what runs it again.
  it("sends a restart and no reload once the run has finished", async () => {
    const send = vi.fn(async (): Promise<ReloadOutcome> => ({ kind: "restarted" }));
    const session = new EditSession(send);
    session.finish();

    expect(await session.reload("x")).toBeNull();
    expect(send).not.toHaveBeenCalled();
    expect(session.get().kind).toBe("finished");

    expect(await session.restart("y")).toEqual({ kind: "restarted" });
    expect(send).toHaveBeenCalledWith("restart", "y");
    expect(session.get().kind).toBe("restarted");
  });

  it("follows the run: finished on the frame marked final", () => {
    const live = new LiveStore();
    const session = new EditSession(async () => ({ kind: "reloaded", kept: 0, bound: 0 }));
    followRun(live, session);

    live.apply({ version: 1, published: 1, final: false, nodes: [], sources: [] });
    expect(session.finished).toBe(false);
    live.apply({ version: 1, published: 2, final: true, nodes: [], sources: [] });
    expect(session.finished).toBe(true);
  });
});
