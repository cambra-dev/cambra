// The live half of the frontend's state: what a running program's operators and
// sources currently hold, and which of them the reader pinned.
//
// A second observable beside `Store` rather than a field on it. `Store` is
// snapshot-derived and its one listener signature carries a `Resolved`; frames
// arrive while a program runs, and folding them into that store would notify
// every tree pane's `renderSelection` on each frame for a selection that did
// not change. Same rule `paneVisibility` states for its own domain: one
// observable per independent state domain, each with the same
// `subscribe(fn): () => void` shape.
//
// The frame is whole state and latest-wins, so this is not an incremental
// store: `apply` replaces a node's entry and leaves the others alone.

import { validateLiveFrame } from "./liveValidate";
import type { LiveFrame, LiveProducer, LiveSource } from "./types";

/** What one operator last produced, and when. */
export interface LiveEntry {
  /** The tick the answer came from, which lags the newest tick when the operator has since produced nothing. */
  tick: number;
  producers: LiveProducer[];
}

/**
 * Where the run is, as a state rather than a pair of booleans.
 *
 * `finished` and `lost` are the distinction the wire's `final` flag exists to
 * make: a socket that goes quiet looks the same either way, because the process
 * parks after a run rather than exiting.
 */
export type LiveStatus =
  | { kind: "connecting" }
  | { kind: "not-run" }
  | { kind: "live"; tick: number; published: number }
  | { kind: "finished"; tick: number }
  | { kind: "lost"; clean: boolean };

/**
 * One inspect gesture, named by the construct that made it.
 *
 * The tag rather than the operator is the unit the reader manages: one gesture
 * on `words` pins whatever operators that position became, and the reader
 * thinks of that as "the `words` I inspected", not as three unrelated ids.
 */
export interface LiveTag {
  /** Stable identity, so re-inspecting the same construct re-shows one tag. */
  id: string;
  /** What the reader sees, e.g. `Var(words): L8`. */
  label: string;
  /** The operators this gesture pinned. */
  nodes: readonly number[];
  /** Whether its operators are currently drawn. The menu's checkbox. */
  shown: boolean;
}

/** The cache and the tags, as one value a view can render from. */
export interface LiveState {
  status: LiveStatus;
  /** Latest rows per operator node. Bounded by the operator count, and does not grow over time. */
  nodes: Map<number, LiveEntry>;
  /** Latest retained window per source, by its graph node id. */
  sources: Map<number, LiveSource>;
  /** Inspect gestures, most recent first. */
  tags: readonly LiveTag[];
  /** The newest tick seen, against which an entry's own tick reads as staleness. */
  tick: number;
}

/** The operators the shown tags between them ask for. */
export function shownNodes(state: LiveState): Set<number> {
  const nodes = new Set<number>();
  for (const tag of state.tags) {
    if (!tag.shown) continue;
    for (const node of tag.nodes) nodes.add(node);
  }
  return nodes;
}

/** The shown tags that pinned one operator, so a group can name its origin. */
export function tagsFor(state: LiveState, nodeId: number): LiveTag[] {
  return state.tags.filter((tag) => tag.shown && tag.nodes.includes(nodeId));
}

type Listener = (state: LiveState) => void;

/**
 * Fold a frame into the cache.
 *
 * Per-node replace, not merge. The backend already collapsed each producer's
 * several `get`s within the tick to one answer, so a frame's entry for a node
 * *is* the current answer — nothing needs combining, which is what keeps the
 * `Tile::merge` double-count from reappearing on this side. A node absent from
 * the frame keeps its entry and its older tick, which is where staleness comes
 * from.
 */
export function applyFrame(state: LiveState, frame: LiveFrame): LiveState {
  const nodes = new Map(state.nodes);
  for (const node of frame.nodes) {
    nodes.set(node.nodeId, { tick: frame.tick, producers: node.producers });
  }
  const sources = new Map(state.sources);
  for (const source of frame.sources) {
    if (source.nodeId !== null) sources.set(source.nodeId, source);
  }
  return {
    ...state,
    nodes,
    sources,
    tick: frame.tick,
    status: frame.final
      ? { kind: "finished", tick: frame.tick }
      : { kind: "live", tick: frame.tick, published: frame.published },
  };
}

/**
 * The live cache, its pins, and the socket that feeds them.
 *
 * Caching is what makes pinning answer immediately: reading only the newest
 * frame would leave a freshly pinned operator blank until the next one, and a
 * converged program sends no next frame.
 */
export class LiveStore {
  private state: LiveState = {
    status: { kind: "connecting" },
    nodes: new Map(),
    sources: new Map(),
    tags: [],
    tick: 0,
  };
  private readonly listeners = new Set<Listener>();

  get(): LiveState {
    return this.state;
  }

  subscribe(fn: Listener): () => void {
    this.listeners.add(fn);
    return () => this.listeners.delete(fn);
  }

  /** Fold in a validated frame. */
  apply(frame: LiveFrame): void {
    this.state = applyFrame(this.state, frame);
    this.notify();
  }

  setStatus(status: LiveStatus): void {
    this.state = { ...this.state, status };
    this.notify();
  }

  /**
   * Record an inspect gesture.
   *
   * Re-inspecting the same construct re-shows its existing tag and moves it to
   * the front rather than adding a second one with the same name: the reader
   * made the same gesture, not a new one.
   *
   * Tags are not persisted. A tag names `NodeId`s and every id changes on the
   * next compile, so a remembered tag would point at nodes that no longer
   * exist. Pane visibility carries no ids, which is why that *is* persisted.
   */
  inspect(label: string, nodes: readonly number[]): void {
    const id = label;
    const rest = this.state.tags.filter((tag) => tag.id !== id);
    this.state = { ...this.state, tags: [{ id, label, nodes, shown: true }, ...rest] };
    this.notify();
  }

  /** Show or hide one tag's operators, leaving the tag in the list. */
  toggleTag(id: string): void {
    this.state = {
      ...this.state,
      tags: this.state.tags.map((tag) => (tag.id === id ? { ...tag, shown: !tag.shown } : tag)),
    };
    this.notify();
  }

  /** Drop one tag from the list entirely. */
  removeTag(id: string): void {
    this.state = { ...this.state, tags: this.state.tags.filter((tag) => tag.id !== id) };
    this.notify();
  }

  /** Drop every tag, which empties the pane and the list together. */
  clearTags(): void {
    if (this.state.tags.length === 0) return;
    this.state = { ...this.state, tags: [] };
    this.notify();
  }

  /** Whether an operator is drawn by some shown tag. */
  isShown(nodeId: number): boolean {
    return shownNodes(this.state).has(nodeId);
  }

  private notify(): void {
    const state = this.state;
    for (const fn of this.listeners) {
      // One throwing listener must not starve the ones after it, and the error
      // is reported rather than swallowed. Same guard `Store.setSelection` has.
      try {
        fn(state);
      } catch (e) {
        console.error("a live-store listener threw", e);
      }
    }
  }
}

/**
 * Connect to `/api/live` and feed `store`.
 *
 * Relative to the serving origin, so it needs no configured host. Returns a
 * disposer that closes the socket.
 *
 * A failure degrades the pane and nothing else: `main`'s `catch` replaces the
 * whole root with a fatal message, which is the right answer for a snapshot
 * that would not load and the wrong one for a run that ended.
 */
export function connectLive(store: LiveStore, open: () => WebSocket = openLive): () => void {
  let socket: WebSocket;
  try {
    socket = open();
  } catch (e) {
    console.error("live: could not open the socket", e);
    store.setStatus({ kind: "lost", clean: false });
    return () => {};
  }

  socket.addEventListener("message", (event) => {
    if (typeof event.data !== "string") return;
    let frame: LiveFrame;
    try {
      // Validated per message, not cast: a drifted backend surfaces as a
      // path-naming error rather than as an operator that appears to have
      // produced nothing.
      frame = validateLiveFrame(JSON.parse(event.data));
    } catch (e) {
      console.error("live: rejecting a frame", e);
      return;
    }
    store.apply(frame);
  });

  socket.addEventListener("close", (event) => {
    const current = store.get().status;
    // A `finished` status came from a frame that said so, and outranks the
    // close that follows it. Without that, a clean shutdown after the final
    // frame would read as a lost connection.
    if (current.kind === "finished") return;
    store.setStatus({ kind: "lost", clean: event.wasClean });
  });

  socket.addEventListener("error", () => {
    // `error` carries no detail by design; `close` follows it and decides.
    console.error("live: socket error");
  });

  return () => socket.close();
}

/** The socket, addressed relative to whatever origin served the page. */
function openLive(): WebSocket {
  const scheme = window.location.protocol === "https:" ? "wss:" : "ws:";
  return new WebSocket(`${scheme}//${window.location.host}/api/live`);
}
