// The header's pane filter: a dropdown of checkboxes, one per pane.
//
// It renders and reads `PaneVisibility` but never caches it — an external
// change (a restored preference, a refused hide) has to reach the checkboxes
// too, so every render path goes through `sync`.
//
// Native `<input type="checkbox">` inside a `<label>`, under `role="group"`,
// rather than an ARIA menu: `role="menu"` obligates roving arrow-key focus,
// which is real code, and the native controls already carry the keyboard and
// screen-reader semantics a checkbox list needs.

import type { PaneVisibility } from "./paneVisibility";

/** A pane as the menu sees it. `PaneDescriptor` is assignable to this. */
export interface PaneMenuEntry {
  id: string;
  label: string;
}

const PANEL_ID = "pane-menu-panel";

export function renderPaneMenu(
  parent: HTMLElement,
  entries: readonly PaneMenuEntry[],
  visibility: PaneVisibility,
): void {
  const root = document.createElement("div");
  root.className = "pane-menu";

  const button = document.createElement("button");
  button.type = "button";
  button.className = "pane-menu-button";
  button.setAttribute("aria-haspopup", "true");
  button.setAttribute("aria-expanded", "false");
  button.setAttribute("aria-controls", PANEL_ID);
  button.textContent = "☰ Panes";

  const panel = document.createElement("div");
  panel.className = "pane-menu-panel";
  panel.id = PANEL_ID;
  panel.setAttribute("role", "group");
  panel.setAttribute("aria-label", "Visible panes");
  panel.hidden = true;

  const boxes = new Map<string, HTMLInputElement>();

  // One predicate drives both halves of the floor: the last visible pane's box
  // is disabled, and `setVisible` refuses the hide regardless.
  const sync = (): void => {
    for (const [id, box] of boxes) {
      box.checked = visibility.isVisible(id);
      box.disabled = box.checked && !visibility.canHide(id);
    }
  };

  for (const entry of entries) {
    const item = document.createElement("label");
    item.className = "pane-menu-item";

    const box = document.createElement("input");
    box.type = "checkbox";
    box.value = entry.id;
    box.addEventListener("change", () => {
      // Re-sync unconditionally: a refused hide notifies no subscriber, and the
      // box has already flipped itself.
      visibility.setVisible(entry.id, box.checked);
      sync();
    });

    item.appendChild(box);
    item.appendChild(document.createTextNode(entry.label));
    panel.appendChild(item);
    boxes.set(entry.id, box);
  }

  // Registered only while the panel is open — a permanent document listener
  // would also fire for the click that opens the menu.
  let closeOnOutside: ((event: MouseEvent) => void) | null = null;

  const setOpen = (open: boolean): void => {
    panel.hidden = !open;
    button.setAttribute("aria-expanded", String(open));
    if (open) {
      sync();
      closeOnOutside = (event: MouseEvent) => {
        if (!root.contains(event.target as Node)) setOpen(false);
      };
      document.addEventListener("mousedown", closeOnOutside);
      [...boxes.values()].find((box) => !box.disabled)?.focus();
    } else if (closeOnOutside) {
      document.removeEventListener("mousedown", closeOnOutside);
      closeOnOutside = null;
    }
  };

  button.addEventListener("click", () => setOpen(panel.hidden));
  root.addEventListener("keydown", (event) => {
    if (event.key !== "Escape" || panel.hidden) return;
    setOpen(false);
    button.focus();
  });

  visibility.subscribe(sync);
  sync();

  root.appendChild(button);
  root.appendChild(panel);
  parent.appendChild(root);
}
