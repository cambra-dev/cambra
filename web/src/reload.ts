// Reloading and restarting the running program from the source pane.
//
// A reload swaps in the pane's text as `main`'s next version and carries its
// state forward; a restart discards every branch and runs the text from a fresh
// compile (`src/ccl/design/program-evolution.md`, "`/reload`" and
// "`/restart`"). The server says whether it takes them (`GET
// /api/capabilities`), which it does on a run with a control port. When it
// does, the page holds one `EditSession` for its lifetime, and every source pane
// it draws is editable and sends through it. The session outlives the panes: a reload redraws every
// pane, so the reload's outcome, and the reader's edit, have to be held
// somewhere the next source pane can read them back from.
//
// The page sees an accepted version the way it sees any reload of `main`: a
// frame names the new version and `followReloads` redraws. A restart is a new
// version of `main` too, numbered on from the last, so it is followed alike.
// Nothing here touches the panes.

import type { LiveStore } from "./liveStore";
import type { Diagnostic } from "./types";

/** What one reload or restart came to. */
export type ReloadOutcome =
  // `main` runs the version now. `kept` of `bound` is how much of the replaced
  // version it took over rather than built.
  | { kind: "reloaded"; kept: number; bound: number }
  // The version runs from a fresh compile as the only branch.
  | { kind: "restarted" }
  // The compiler or the branch table refused the version, and the version that
  // was running still is. `diagnostics` are the compile errors, as byte spans
  // into `source`, the text that was sent; a refusal that points at no span
  // carries none, and `message` says why.
  | { kind: "rejected"; message: string; diagnostics: Diagnostic[]; source: string }
  // The request did not reach a running program, or the server refused it.
  | { kind: "failed"; message: string };

/** What a version is sent to do: the server route it is posted to. */
export type Verb = "reload" | "restart";

/** Send a version to the server, and answer what came of it. */
export type Send = (verb: Verb, source: string) => Promise<ReloadOutcome>;

/**
 * What the source pane's status strip reports. `finished` is the run having
 * ended, after which the server takes a restart and no reload.
 */
export type EditStatus =
  | { kind: "idle" }
  | { kind: "reloading" }
  | { kind: "finished" }
  | ReloadOutcome;

/**
 * The source pane's editor as it was when a redraw disposed of it.
 *
 * `text` is the reader's edit: the document when it differed from the version
 * the pane was drawn for, and `null` when it did not. A redraw for a version
 * the reader did not ask for keeps an edit and follows an unedited pane, so a
 * reload from elsewhere does not throw away text the reader has typed.
 */
export interface CarriedEditor {
  text: string | null;
  anchor: number;
  head: number;
  focused: boolean;
}

export class EditSession {
  private status: EditStatus = { kind: "idle" };
  private readonly listeners = new Set<(status: EditStatus) => void>();
  /** Set by a disposed source pane, and taken by the next one. */
  carried: CarriedEditor | null = null;

  constructor(private readonly send: Send) {}

  get(): EditStatus {
    return this.status;
  }

  subscribe(fn: (status: EditStatus) => void): () => void {
    this.listeners.add(fn);
    return () => this.listeners.delete(fn);
  }

  /** Whether the run has ended, after which only a restart is sent. */
  get finished(): boolean {
    return this.status.kind === "finished";
  }

  /**
   * Reload with `source`, and answer the outcome; `null` when a version is
   * already in flight, which this one would race, or the run has ended.
   */
  reload(source: string): Promise<ReloadOutcome | null> {
    return this.post("reload", source);
  }

  /**
   * Restart from `source`, and answer the outcome; `null` when a version is
   * already in flight. A finished run takes a restart.
   */
  restart(source: string): Promise<ReloadOutcome | null> {
    return this.post("restart", source);
  }

  private async post(verb: Verb, source: string): Promise<ReloadOutcome | null> {
    if (this.status.kind === "reloading") return null;
    if (verb === "reload" && this.finished) return null;
    this.set({ kind: "reloading" });
    let outcome: ReloadOutcome;
    try {
      outcome = await this.send(verb, source);
    } catch (e) {
      outcome = { kind: "failed", message: String(e) };
    }
    // The run ending while the version was in flight outranks its outcome.
    if (!this.finished) this.set(outcome);
    return outcome;
  }

  /**
   * The run has ended. A finished program takes no reload
   * (`src/ccl/design/program-evolution.md`, "`/reload`"), and lasts until a
   * restart runs it again.
   */
  finish(): void {
    if (!this.finished) this.set({ kind: "finished" });
  }

  /** The run is going again, after a restart. */
  resume(): void {
    if (this.finished) this.set({ kind: "idle" });
  }

  private set(status: EditStatus): void {
    this.status = status;
    for (const fn of this.listeners) fn(status);
  }
}

/** The server's reply to `POST /api/reload` or `POST /api/restart`. */
interface ReloadReply {
  message?: unknown;
  diagnostics?: unknown;
  kept?: unknown;
  bound?: unknown;
}

/**
 * The outcome a reply to `verb`'s route reports.
 *
 * `200` is an accepted version and `400` a refused one. Every other status is
 * the request not reaching a program: a run without a control port (`404`), an
 * admission refusal (`403`, `415`), a finished program sent a reload (`409`),
 * or a program that has stopped (`503`).
 */
export function outcomeOf(
  status: number,
  reply: ReloadReply,
  source: string,
  verb: Verb = "reload",
): ReloadOutcome {
  const message = typeof reply.message === "string" ? reply.message : `HTTP ${status}`;
  if (status === 200 && verb === "restart") return { kind: "restarted" };
  if (status === 200 && typeof reply.kept === "number" && typeof reply.bound === "number") {
    return { kind: "reloaded", kept: reply.kept, bound: reply.bound };
  }
  if (status === 400) {
    const diagnostics = Array.isArray(reply.diagnostics)
      ? (reply.diagnostics as Diagnostic[])
      : [];
    return { kind: "rejected", message, diagnostics, source };
  }
  return { kind: "failed", message };
}

/**
 * A `Send` that posts to this page's own server, at `/api/reload` or
 * `/api/restart`.
 *
 * JSON, because the server takes nothing else: a cross-site page can only send
 * a CORS-safelisted type without a preflight, and `application/json` is not one
 * (`src/inspector_server/reload.rs`, "Admission").
 */
export function postVersion(fetchImpl: typeof fetch = fetch): Send {
  return async (verb, source) => {
    const resp = await fetchImpl(`/api/${verb}`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ source }),
    });
    let reply: ReloadReply = {};
    try {
      reply = (await resp.json()) as ReloadReply;
    } catch {
      // A body that is not JSON leaves the status to say what happened.
    }
    return outcomeOf(resp.status, reply, source, verb);
  };
}

/** Whether the server takes `POST /api/reload`. Any failure reads as no. */
export async function serverReloads(fetchImpl: typeof fetch = fetch): Promise<boolean> {
  try {
    const resp = await fetchImpl("/api/capabilities");
    if (!resp.ok) return false;
    const body = (await resp.json()) as { reload?: unknown };
    return body.reload === true;
  } catch {
    return false;
  }
}

/**
 * Keep `session` in step with the run `live` follows: finished on the frame
 * marked `final`, and going again on a frame that is not, which follows a
 * restart.
 */
export function followRun(live: LiveStore, session: EditSession): void {
  const check = (): void => {
    const status = live.get().status.kind;
    if (status === "finished") session.finish();
    else if (status === "live") session.resume();
  };
  live.subscribe(check);
  check();
}
