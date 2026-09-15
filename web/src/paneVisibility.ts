// Which panes the layout shows. View state, deliberately not in the `Store`:
// the store is snapshot-derived and DOM-free, and its one listener signature
// carries a `Resolved` — the resolution of a *selection* through the link
// graph. Widening that to carry visibility would either make `Resolved` mean
// two things or give `Store` two unrelated observables.

import { SCHEMA_VERSION } from "./wireValidate";

/**
 * The visible/hidden state of a fixed, ordered set of panes.
 *
 * The one invariant is that the layout is never empty: the last visible pane
 * cannot be hidden. That is a property of the layout rather than of any
 * particular pane, so Source is an ordinary member here — nothing is pinned.
 */
export class PaneVisibility {
  /** The panes, in layout order. */
  readonly ids: readonly string[];

  private readonly hidden: Set<string>;
  private readonly listeners = new Set<() => void>();

  constructor(ids: readonly string[], hidden: Iterable<string> = []) {
    this.ids = [...ids];
    // An id naming no pane is dropped: a restored preference outlives the
    // roster that produced it, and a degraded snapshot ships a different one.
    this.hidden = new Set([...hidden].filter((id) => this.ids.includes(id)));
    // A restored set that would empty the layout is refused whole rather than
    // trimmed — which pane to spare would be an arbitrary choice.
    if (this.hidden.size >= this.ids.length) this.hidden.clear();
  }

  isVisible(id: string): boolean {
    return !this.hidden.has(id);
  }

  visibleCount(): number {
    return this.ids.length - this.hidden.size;
  }

  /** The hidden ids in layout order, so the persisted value is stable. */
  hiddenIds(): string[] {
    return this.ids.filter((id) => this.hidden.has(id));
  }

  /** False when `id` is already hidden, or is the last visible pane. */
  canHide(id: string): boolean {
    return this.isVisible(id) && this.visibleCount() > 1;
  }

  /**
   * Show or hide a pane, reporting whether the state changed. A hide `canHide`
   * refuses is a no-op, so the floor holds even for a caller that did not ask
   * first — a disabled checkbox still receives a scripted click.
   */
  setVisible(id: string, visible: boolean): boolean {
    if (!this.ids.includes(id)) return false;
    if (visible === this.isVisible(id)) return false;
    if (!visible && !this.canHide(id)) return false;

    if (visible) this.hidden.delete(id);
    else this.hidden.add(id);
    for (const fn of this.listeners) fn();
    return true;
  }

  /** Subscribe to visibility changes. Returns an unsubscribe fn (as `Store`). */
  subscribe(fn: () => void): () => void {
    this.listeners.add(fn);
    return () => this.listeners.delete(fn);
  }
}

// The roster can only change when a pane is added to or removed from the
// compiler's `PANES` table, and that is a wire change — which bumps
// SCHEMA_VERSION. Keying on it retires a stale set at exactly the moment its
// ids stop meaning what they meant.
export const HIDDEN_PANES_KEY = `cambra-inspector:hidden-panes:v${SCHEMA_VERSION}`;

/**
 * `window.localStorage`, or null where it is unusable — reading the property
 * throws (Firefox private browsing, `dom.storage.enabled=false`), or the object
 * is a stub without the methods (some embedders and test environments ship
 * one). A null storage degrades the filter to one session rather than breaking
 * the page.
 */
export function browserStorage(): Storage | null {
  try {
    const storage: Storage | undefined = window.localStorage;
    if (typeof storage?.getItem !== "function" || typeof storage.setItem !== "function") {
      return null;
    }
    return storage;
  } catch {
    return null;
  }
}

/**
 * The persisted hidden set. Anything unparseable reads as "nothing hidden" —
 * a corrupt key must not cost the user their panes.
 */
export function loadHiddenPanes(
  storage: Pick<Storage, "getItem">,
  key: string = HIDDEN_PANES_KEY,
): string[] {
  try {
    const raw = storage.getItem(key);
    if (raw === null) return [];
    const parsed: unknown = JSON.parse(raw);
    if (!Array.isArray(parsed)) return [];
    return parsed.filter((v): v is string => typeof v === "string");
  } catch {
    return [];
  }
}

/**
 * Persist the *hidden* set, not the visible one: a pane added by a later
 * release is then visible by default, where a stored visible set would hide
 * every future pane for everyone who ever opened this build.
 *
 * Write only on a user toggle. Writing what was loaded would let a page whose
 * roster is narrower than the stored one — a degraded snapshot, whose panes are
 * `source` and `diagnostics` — erase the stage preferences it cannot see.
 */
export function saveHiddenPanes(
  storage: Pick<Storage, "setItem">,
  hidden: readonly string[],
  key: string = HIDDEN_PANES_KEY,
): void {
  try {
    storage.setItem(key, JSON.stringify(hidden));
  } catch {
    // A full quota or a storage that refuses writes costs the preference, not
    // the toggle: the in-memory state already changed.
  }
}
