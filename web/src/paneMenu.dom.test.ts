// @vitest-environment jsdom
//
// The filter menu's DOM behaviour, over a `PaneVisibility` directly — no store,
// no fixture, no CodeMirror, so this file needs none of the layout stubs the
// view tests do.

import { beforeEach, describe, expect, it } from "vitest";

import { renderPaneMenu } from "./paneMenu";
import { PaneVisibility } from "./paneVisibility";

const ENTRIES = [
  { id: "source", label: "Source" },
  { id: "pre-inference", label: "IR (PRE-INFERENCE)" },
  { id: "post-inference", label: "IR (POST-INFERENCE)" },
];

describe("renderPaneMenu", () => {
  let root: HTMLElement;
  let visibility: PaneVisibility;

  const button = (): HTMLButtonElement => root.querySelector(".pane-menu-button")!;
  const panel = (): HTMLElement => root.querySelector(".pane-menu-panel")!;
  const boxes = (): HTMLInputElement[] => [...panel().querySelectorAll("input")];
  const boxFor = (id: string): HTMLInputElement =>
    boxes().find((b) => b.value === id) as HTMLInputElement;

  // jsdom fires `click` on a disabled input but not `change`; the app's floor
  // has to hold for a scripted toggle either way, so drive `change` directly.
  const toggle = (id: string, checked: boolean): void => {
    const box = boxFor(id);
    box.checked = checked;
    box.dispatchEvent(new Event("change", { bubbles: true }));
  };

  beforeEach(() => {
    document.body.replaceChildren();
    root = document.createElement("div");
    document.body.appendChild(root);
    visibility = new PaneVisibility(ENTRIES.map((e) => e.id));
    renderPaneMenu(root, ENTRIES, visibility);
  });

  it("renders one checkbox per pane, labelled and all checked", () => {
    expect(boxes().length).toBe(ENTRIES.length);
    expect(boxes().every((b) => b.checked)).toBe(true);
    expect(panel().textContent).toContain("IR (PRE-INFERENCE)");
  });

  it("starts closed, and the button says so", () => {
    expect(panel().hidden).toBe(true);
    expect(button().getAttribute("aria-expanded")).toBe("false");
  });

  it("opens on a button click and flips aria-expanded", () => {
    button().click();
    expect(panel().hidden).toBe(false);
    expect(button().getAttribute("aria-expanded")).toBe("true");

    button().click();
    expect(panel().hidden).toBe(true);
    expect(button().getAttribute("aria-expanded")).toBe("false");
  });

  it("hides a pane when its box is unchecked, and shows it again when re-checked", () => {
    toggle("pre-inference", false);
    expect(visibility.isVisible("pre-inference")).toBe(false);

    toggle("pre-inference", true);
    expect(visibility.isVisible("pre-inference")).toBe(true);
  });

  it("disables the last visible pane's box", () => {
    toggle("source", false);
    toggle("pre-inference", false);

    expect(boxFor("post-inference").disabled).toBe(true);
    expect(boxFor("source").disabled).toBe(false);
  });

  it("keeps the last visible pane visible even when its box is driven directly", () => {
    // The disabled attribute is an affordance, not the guard: a scripted change
    // still reaches the handler.
    toggle("source", false);
    toggle("pre-inference", false);
    toggle("post-inference", false);

    expect(visibility.isVisible("post-inference")).toBe(true);
    // The box flipped itself; the menu re-syncs it from the state.
    expect(boxFor("post-inference").checked).toBe(true);
  });

  it("re-syncs the checkboxes when visibility changes elsewhere", () => {
    // The menu reads the state rather than owning it.
    visibility.setVisible("pre-inference", false);
    expect(boxFor("pre-inference").checked).toBe(false);
  });

  it("closes on Escape and returns focus to the button", () => {
    button().click();
    panel().dispatchEvent(new KeyboardEvent("keydown", { key: "Escape", bubbles: true }));

    expect(panel().hidden).toBe(true);
    expect(document.activeElement).toBe(button());
  });

  it("closes on a mousedown outside, and stays open on one inside", () => {
    button().click();
    panel().dispatchEvent(new MouseEvent("mousedown", { bubbles: true }));
    expect(panel().hidden).toBe(false);

    document.body.dispatchEvent(new MouseEvent("mousedown", { bubbles: true }));
    expect(panel().hidden).toBe(true);
  });
});
