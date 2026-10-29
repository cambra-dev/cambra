// Reloading the running program from the source pane.
//
// The server says whether it takes a reload (`GET /api/capabilities`), which it
// does on a run with a control port. When it does, the page holds one
// `EditSession` for its lifetime, and every source pane it draws is editable and
// reloads through it. The session outlives the panes: a reload redraws every
// pane, so the reload's outcome, and the reader's edit, have to be held
// somewhere the next source pane can read them back from.
//
// The page sees an accepted version the way it sees any reload of `main`: a
// frame names the new version and `followReloads` redraws. Nothing here touches
// the panes.

import type { LiveStore } from "./liveStore";
import type { Diagnostic } from "./types";

/** What one reload came to. */
export type ReloadOutcome =
  // `main` runs the version now. `kept` of `bound` is how much of the replaced
  // version it took over rather than built.
  | { kind: "reloaded"; kept: number; bound: number }
  // The compiler or the branch table refused the version, and the version that
  // was running still is. `diagnostics` are the compile errors, as byte spans
  // into `source`, the text that was sent; a refusal that points at no span
  // carries none, and `message` says why.
  | { kind: "rejected"; message: string; diagnostics: Diagnostic[]; source: string }
  // The request did not reach a running program, or the server refused it.
  | { kind: "failed"; message: string };

/** Send a version to the server, and answer what came of it. */
export type Reload = (source: string) => Promise<ReloadOutcome>;

/**
 * What the source pane's status strip reports. `finished` is the run having
 * ended, after which the server takes no reload and the pane is read-only.
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

  constructor(private readonly send: Reload) {}

  get(): EditStatus {
    return this.status;
  }

  subscribe(fn: (status: EditStatus) => void): () => void {
    this.listeners.add(fn);
    return () => this.listeners.delete(fn);
  }

  /** Whether the run has ended, after which nothing reloads. */
  get finished(): boolean {
    return this.status.kind === "finished";
  }

  /**
   * Reload with `source`, and answer the outcome; `null` when a reload is
   * already in flight, which this one would race, or the run has ended.
   */
  async reload(source: string): Promise<ReloadOutcome | null> {
    if (this.status.kind === "reloading" || this.finished) return null;
    this.set({ kind: "reloading" });
    let outcome: ReloadOutcome;
    try {
      outcome = await this.send(source);
    } catch (e) {
      outcome = { kind: "failed", message: String(e) };
    }
    // The run ending while the reload was in flight outranks its outcome.
    if (!this.finished) this.set(outcome);
    return outcome;
  }

  /**
   * The run has ended. A finished program takes no reload
   * (`src/ccl/design/program-evolution.md`, "`/reload`"), so this is final.
   */
  finish(): void {
    if (!this.finished) this.set({ kind: "finished" });
  }

  private set(status: EditStatus): void {
    this.status = status;
    for (const fn of this.listeners) fn(status);
  }
}

/** The server's reply to `POST /api/reload`. */
interface ReloadReply {
  message?: unknown;
  diagnostics?: unknown;
  kept?: unknown;
  bound?: unknown;
}

/**
 * The outcome a reply to `POST /api/reload` reports.
 *
 * `200` is an accepted version and `400` a refused one. Every other status is
 * the request not reaching a program: a run without a control port (`404`), an
 * admission refusal (`403`, `415`), or a program that has stopped (`503`).
 */
export function outcomeOf(status: number, reply: ReloadReply, source: string): ReloadOutcome {
  const message = typeof reply.message === "string" ? reply.message : `HTTP ${status}`;
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
 * A `Reload` that posts to this page's own server.
 *
 * JSON, because the server takes nothing else: a cross-site page can only send
 * a CORS-safelisted type without a preflight, and `application/json` is not one
 * (`src/inspector_server/reload.rs`, "Admission").
 */
export function postReload(fetchImpl: typeof fetch = fetch): Reload {
  return async (source) => {
    const resp = await fetchImpl("/api/reload", {
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
    return outcomeOf(resp.status, reply, source);
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
 * End `session` when the run `live` follows finishes, which the frame marked
 * `final` says.
 */
export function finishWithRun(live: LiveStore, session: EditSession): void {
  const check = (): void => {
    if (live.get().status.kind === "finished") session.finish();
  };
  live.subscribe(check);
  check();
}
