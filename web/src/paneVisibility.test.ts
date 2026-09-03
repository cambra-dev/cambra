// Pure unit tests for the pane-visibility state and its persistence. DOM-free:
// storage is a parameter, so the corrupt/absent/throwing cases are reachable
// without touching a global.

import { describe, expect, it, vi } from "vitest";

import {
  HIDDEN_PANES_KEY,
  PaneVisibility,
  loadHiddenPanes,
  saveHiddenPanes,
} from "./paneVisibility";
import { SCHEMA_VERSION } from "./wireValidate";

const IDS = ["source", "pre-inference", "post-inference"] as const;

describe("PaneVisibility", () => {
  it("starts with every pane visible", () => {
    const v = new PaneVisibility(IDS);
    for (const id of IDS) expect(v.isVisible(id)).toBe(true);
    expect(v.hiddenIds()).toEqual([]);
    expect(v.visibleCount()).toBe(3);
  });

  it("honours an initial hidden set", () => {
    const v = new PaneVisibility(IDS, ["pre-inference"]);
    expect(v.isVisible("pre-inference")).toBe(false);
    expect(v.isVisible("source")).toBe(true);
    expect(v.visibleCount()).toBe(2);
  });

  it("drops an initial hidden id that names no pane", () => {
    // A restored preference outlives the roster that produced it.
    const v = new PaneVisibility(IDS, ["post-planning", "pre-inference"]);
    expect(v.hiddenIds()).toEqual(["pre-inference"]);
  });

  it("refuses an initial set that would empty the layout", () => {
    const v = new PaneVisibility(IDS, IDS);
    expect(v.hiddenIds()).toEqual([]);
    expect(v.visibleCount()).toBe(3);
  });

  it("reports hidden ids in layout order, not toggle order", () => {
    // Keeps the persisted value stable, so a reload does not churn the key.
    const v = new PaneVisibility(IDS);
    v.setVisible("post-inference", false);
    v.setVisible("source", false);
    expect(v.hiddenIds()).toEqual(["source", "post-inference"]);
  });

  it("reports no change when the state already matches", () => {
    const v = new PaneVisibility(IDS);
    expect(v.setVisible("source", true)).toBe(false);
    v.setVisible("source", false);
    expect(v.setVisible("source", false)).toBe(false);
  });

  it("ignores an id that names no pane", () => {
    const v = new PaneVisibility(IDS);
    expect(v.setVisible("nope", false)).toBe(false);
    expect(v.hiddenIds()).toEqual([]);
  });

  it("refuses to hide the last visible pane", () => {
    const v = new PaneVisibility(IDS, ["source", "pre-inference"]);
    expect(v.visibleCount()).toBe(1);
    expect(v.canHide("post-inference")).toBe(false);
    expect(v.setVisible("post-inference", false)).toBe(false);
    expect(v.isVisible("post-inference")).toBe(true);
  });

  it("reports canHide false for a pane that is already hidden", () => {
    // One predicate drives both the disabled checkbox and the refusal.
    const v = new PaneVisibility(IDS, ["source"]);
    expect(v.canHide("source")).toBe(false);
    expect(v.canHide("pre-inference")).toBe(true);
  });

  it("notifies subscribers on a real change and on nothing else", () => {
    const v = new PaneVisibility(IDS);
    const seen = vi.fn();
    v.subscribe(seen);

    expect(v.setVisible("source", false)).toBe(true);
    expect(seen).toHaveBeenCalledTimes(1);

    v.setVisible("source", false); // already hidden
    v.setVisible("pre-inference", false);
    v.setVisible("post-inference", false); // refused: last visible
    expect(seen).toHaveBeenCalledTimes(2);
  });

  it("stops notifying after unsubscribe", () => {
    const v = new PaneVisibility(IDS);
    const seen = vi.fn();
    v.subscribe(seen)();
    v.setVisible("source", false);
    expect(seen).not.toHaveBeenCalled();
  });
});

describe("hidden-pane persistence", () => {
  const fakeStorage = (initial?: string) => {
    let value = initial ?? null;
    return {
      getItem: (): string | null => value,
      setItem: (_key: string, next: string): void => {
        value = next;
      },
      read: (): string | null => value,
    };
  };

  it("carries the schema version in its key", () => {
    // The roster changes only when PANES does, and that is a wire change.
    expect(HIDDEN_PANES_KEY).toBe(`cambra-inspector:hidden-panes:v${SCHEMA_VERSION}`);
  });

  it("round-trips a hidden set", () => {
    const storage = fakeStorage();
    saveHiddenPanes(storage, ["source", "post-planning"]);
    expect(loadHiddenPanes(storage)).toEqual(["source", "post-planning"]);
  });

  it("reads an absent key as nothing hidden", () => {
    expect(loadHiddenPanes(fakeStorage())).toEqual([]);
  });

  it.each(["{", "null", '{"a":1}', '"source"', "[1,2]"])(
    "reads the corrupt value %s as nothing hidden",
    (raw) => {
      // A corrupt key must not cost the user their panes.
      expect(loadHiddenPanes(fakeStorage(raw))).toEqual([]);
    },
  );

  it("keeps only the string entries of a mixed array", () => {
    expect(loadHiddenPanes(fakeStorage('["source",7,null]'))).toEqual(["source"]);
  });

  it("survives a storage that throws on read", () => {
    // Firefox private browsing / dom.storage.enabled=false.
    const throwing = {
      getItem: (): string | null => {
        throw new Error("SecurityError");
      },
    };
    expect(loadHiddenPanes(throwing)).toEqual([]);
  });

  it("survives a storage that throws on write", () => {
    // A full quota costs the preference, not the toggle.
    const throwing = {
      setItem: (): void => {
        throw new Error("QuotaExceededError");
      },
    };
    expect(() => saveHiddenPanes(throwing, ["source"])).not.toThrow();
  });
});
