import { describe, expect, it, vi } from "vitest";

import { LiveStore } from "./liveStore";
import {
  EditSession,
  type ReloadOutcome,
  finishWithRun,
  outcomeOf,
  postReload,
  serverReloads,
} from "./reload";

/** A `fetch` answering every call with `status` and `body`. */
function answering(status: number, body: unknown): typeof fetch & { mock: { calls: unknown[][] } } {
  return vi.fn(async () => new Response(JSON.stringify(body), { status })) as never;
}

describe("outcomeOf", () => {
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

  // A run without a control port, an admission refusal and a stopped program
  // are the request not reaching a program, not the program refusing a version.
  it("reads every other status as a failure, with the server's message", () => {
    for (const status of [403, 404, 415, 503]) {
      expect(outcomeOf(status, { message: "why" }, "src")).toEqual({ kind: "failed", message: "why" });
    }
    expect(outcomeOf(500, {}, "src")).toEqual({ kind: "failed", message: "HTTP 500" });
  });
});

describe("postReload", () => {
  // JSON is what keeps a cross-site form or `no-cors` fetch out, so the page has
  // to send it.
  it("posts the source as JSON to this page's own server", async () => {
    const fetchImpl = answering(200, { kept: 1, bound: 1 });
    await postReload(fetchImpl)("x = 1\n");

    const [url, init] = fetchImpl.mock.calls[0] as [string, RequestInit];
    expect(url).toBe("/api/reload");
    expect(init.method).toBe("POST");
    expect(new Headers(init.headers).get("Content-Type")).toBe("application/json");
    expect(JSON.parse(init.body as string)).toEqual({ source: "x = 1\n" });
  });

  it("reports a body that is not JSON by its status", async () => {
    const fetchImpl = vi.fn(async () => new Response("<html>", { status: 502 })) as never;
    expect(await postReload(fetchImpl)("x")).toEqual({ kind: "failed", message: "HTTP 502" });
  });
});

describe("serverReloads", () => {
  it("is the server's `reload` capability", async () => {
    expect(await serverReloads(answering(200, { reload: true }))).toBe(true);
    expect(await serverReloads(answering(200, { reload: false }))).toBe(false);
  });

  // A server that predates the route, or one that cannot be reached, leaves the
  // pane read-only rather than editable with nothing behind the chord.
  it("is false when the capabilities cannot be read", async () => {
    expect(await serverReloads(answering(404, {}))).toBe(false);
    const throwing = vi.fn(async () => {
      throw new Error("offline");
    }) as never;
    expect(await serverReloads(throwing)).toBe(false);
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

  // A finished program takes no reload, so the session sends nothing.
  it("sends nothing once the run has finished", async () => {
    const send = vi.fn(async (): Promise<ReloadOutcome> => ({ kind: "reloaded", kept: 0, bound: 0 }));
    const session = new EditSession(send);
    session.finish();

    expect(await session.reload("x")).toBeNull();
    expect(send).not.toHaveBeenCalled();
    expect(session.get().kind).toBe("finished");
  });

  it("finishes with the run, on the frame marked final", () => {
    const live = new LiveStore();
    const session = new EditSession(async () => ({ kind: "reloaded", kept: 0, bound: 0 }));
    finishWithRun(live, session);

    live.apply({ version: 1, published: 1, final: false, nodes: [], sources: [] });
    expect(session.finished).toBe(false);
    live.apply({ version: 1, published: 2, final: true, nodes: [], sources: [] });
    expect(session.finished).toBe(true);
  });
});
