// @vitest-environment jsdom
import { beforeEach, describe, expect, it } from "vitest";

import { LiveStore, shownNodes } from "./liveStore";
import { renderLiveMenu } from "./liveMenu";

function mount(): { root: HTMLElement; live: LiveStore } {
  const root = document.createElement("div");
  document.body.replaceChildren(root);
  const live = new LiveStore();
  renderLiveMenu(root, live);
  return { root, live };
}

function items(root: HTMLElement): HTMLElement[] {
  return [...root.querySelectorAll<HTMLElement>(".live-menu-item")];
}

describe("the Values pane menu", () => {
  let root: HTMLElement;
  let live: LiveStore;
  beforeEach(() => {
    ({ root, live } = mount());
  });

  it("starts closed, empty, and with clearing disabled", () => {
    const panel = root.querySelector<HTMLElement>(".live-menu-panel")!;
    expect(panel.hidden).toBe(true);
    expect(root.querySelector<HTMLButtonElement>(".live-menu-clear")!.disabled).toBe(true);
    expect(root.querySelector<HTMLElement>(".live-menu-empty")!.hidden).toBe(false);
  });

  it("opens and closes from its button", () => {
    const button = root.querySelector<HTMLButtonElement>(".live-menu-button")!;
    const panel = root.querySelector<HTMLElement>(".live-menu-panel")!;
    button.click();
    expect(panel.hidden).toBe(false);
    expect(button.getAttribute("aria-expanded")).toBe("true");
    button.click();
    expect(panel.hidden).toBe(true);
  });

  // The list has to follow the store, not only its own clicks: a gesture made
  // in the source pane must appear here too.
  it("lists a tag made elsewhere, most recent first", () => {
    live.inspect("Var(a): L1", 1, [1]);
    live.inspect("Var(b): L2", 2, [2, 3]);
    expect(items(root).map((i) => i.querySelector(".live-tag")?.textContent)).toEqual([
      "Var(b): L2",
      "Var(a): L1",
    ]);
    expect(items(root)[0]?.querySelector(".live-menu-count")?.textContent).toBe("2 operators");
    expect(items(root)[1]?.querySelector(".live-menu-count")?.textContent).toBe("1 operator");
  });

  it("hides a tag's operators from its checkbox without forgetting it", () => {
    live.inspect("Var(a): L1", 1, [1]);
    const box = items(root)[0]!.querySelector<HTMLInputElement>('input[type="checkbox"]')!;
    expect(box.checked).toBe(true);
    box.click();
    expect(shownNodes(live.get()).size).toBe(0);
    expect(live.get().tags.length).toBe(1);
    expect(items(root)[0]!.querySelector<HTMLInputElement>("input")!.checked).toBe(false);
  });

  it("forgets one tag from its ✕", () => {
    live.inspect("Var(a): L1", 1, [1]);
    live.inspect("Var(b): L2", 2, [2]);
    items(root)[0]!.querySelector<HTMLButtonElement>(".live-menu-remove")!.click();
    expect(live.get().tags.map((t) => t.label)).toEqual(["Var(a): L1"]);
    expect(items(root).length).toBe(1);
  });

  it("clears every tag, empties the list, and closes", () => {
    live.inspect("Var(a): L1", 1, [1]);
    live.inspect("Var(b): L2", 2, [2]);
    const button = root.querySelector<HTMLButtonElement>(".live-menu-button")!;
    button.click();
    root.querySelector<HTMLButtonElement>(".live-menu-clear")!.click();

    expect(live.get().tags).toEqual([]);
    expect(items(root).length).toBe(0);
    expect(root.querySelector<HTMLElement>(".live-menu-empty")!.hidden).toBe(false);
    expect(root.querySelector<HTMLButtonElement>(".live-menu-clear")!.disabled).toBe(true);
    // Left open, it would show an empty popover over an empty pane.
    expect(root.querySelector<HTMLElement>(".live-menu-panel")!.hidden).toBe(true);
  });

  // Deterministic so a construct keeps its colour across a session rather than
  // depending on the order gestures were made in.
  it("gives a tag the same colour however it was reached", () => {
    live.inspect("Var(a): L1", 1, [1]);
    const first = items(root)[0]!.querySelector<HTMLElement>(".live-tag")!.dataset["colour"];
    live.clearTags();
    live.inspect("Var(zzz): L9", 9, [9]);
    live.inspect("Var(a): L1", 1, [1]);
    const again = items(root)
      .map((i) => i.querySelector<HTMLElement>(".live-tag")!)
      .find((chip) => chip.textContent === "Var(a): L1")!.dataset["colour"];
    expect(again).toBe(first);
  });
});
