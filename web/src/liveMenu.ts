// The Values pane's own menu: clear every inspection, or show and hide them
// one at a time.
//
// A tag is the unit the reader manages, because it is the unit they created:
// one gesture on `words` pinned whatever operators that position became, and
// what they remember is the gesture. So the list is tags, not operators.
//
// Native `<input type="checkbox">` inside a `<label>`, mirroring `paneMenu`:
// `role="menu"` would obligate roving arrow-key focus, and the native controls
// already carry the keyboard and screen-reader semantics a checkbox list needs.

import type { LiveStore, LiveTag } from "./liveStore";
import { TAG_SLOTS, tagColour } from "./liveView";

const PANEL_ID = "live-menu-panel";

/**
 * Build the menu into `parent`, and keep it in step with the store.
 *
 * Every render path goes through `sync`, so a change made elsewhere — a
 * clear, a new inspection — reaches the checkboxes too rather than only the
 * pane.
 */
export function renderLiveMenu(parent: HTMLElement, live: LiveStore): void {
  const root = document.createElement("div");
  root.className = "live-menu";

  const button = document.createElement("button");
  button.type = "button";
  button.className = "live-menu-button";
  button.setAttribute("aria-haspopup", "true");
  button.setAttribute("aria-expanded", "false");
  button.setAttribute("aria-controls", PANEL_ID);
  button.textContent = "☰";
  button.title = "Inspected constructs";

  const panel = document.createElement("div");
  panel.className = "live-menu-panel";
  panel.id = PANEL_ID;
  panel.setAttribute("role", "group");
  panel.setAttribute("aria-label", "Inspected constructs");
  panel.hidden = true;

  const clear = document.createElement("button");
  clear.type = "button";
  clear.className = "live-menu-clear";
  clear.textContent = "Clear all";

  const list = document.createElement("div");
  list.className = "live-menu-list";

  const empty = document.createElement("div");
  empty.className = "live-menu-empty";
  empty.textContent = "Nothing inspected yet.";

  panel.append(clear, list, empty);
  root.append(button, panel);
  parent.appendChild(root);

  const open = (isOpen: boolean): void => {
    panel.hidden = !isOpen;
    button.setAttribute("aria-expanded", String(isOpen));
  };

  const sync = (): void => {
    const tags = live.get().tags;
    clear.disabled = tags.length === 0;
    empty.hidden = tags.length > 0;
    list.replaceChildren(...tags.map((tag) => item(tag, live)));
  };

  button.addEventListener("click", () => open(panel.hidden));

  clear.addEventListener("click", () => {
    live.clearTags();
    // Closed after clearing: the list it was showing is gone, so leaving it
    // open would leave the reader looking at an empty popover over an empty
    // pane.
    open(false);
  });

  // Dismissal matches `paneMenu`: Escape while open, or a pointer outside.
  panel.addEventListener("keydown", (event) => {
    if (event.key === "Escape") {
      open(false);
      button.focus();
    }
  });
  document.addEventListener("pointerdown", (event) => {
    if (panel.hidden) return;
    if (!root.contains(event.target as Node)) open(false);
  });

  live.subscribe(sync);
  sync();
}

/** One row: the checkbox, the tag, and the button that forgets it. */
function item(tag: LiveTag, live: LiveStore): HTMLElement {
  const row = document.createElement("div");
  row.className = "live-menu-item";

  const label = document.createElement("label");
  label.className = "live-menu-label";

  const box = document.createElement("input");
  box.type = "checkbox";
  box.checked = tag.shown;
  box.addEventListener("change", () => live.toggleTag(tag.id));

  const chip = document.createElement("span");
  chip.className = "live-tag";
  chip.textContent = tag.label;
  chip.dataset["colour"] = String(tagColour(tag.label, TAG_SLOTS));

  const count = document.createElement("span");
  count.className = "live-menu-count";
  // The operator count is what the gesture actually pinned, and it is the one
  // number that explains a tag showing more rows than the reader expected.
  count.textContent = tag.nodes.length === 1 ? "1 operator" : `${tag.nodes.length} operators`;

  label.append(box, chip, count);

  const remove = document.createElement("button");
  remove.type = "button";
  remove.className = "live-menu-remove";
  remove.textContent = "✕";
  remove.title = `Forget ${tag.label}`;
  remove.setAttribute("aria-label", `Forget ${tag.label}`);
  remove.addEventListener("click", () => live.removeTag(tag.id));

  row.append(label, remove);
  return row;
}
