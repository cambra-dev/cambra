// The live values pane: what the operators the reader pinned currently hold.
//
// A vertical pane in the row, not a bottom drawer. Its content is a list of
// groups with headers and rows beneath, which is the shape the tree panes
// already are, and a full-height column carries a long list where a drawer
// carries a short one — a real program reaches many operators over many
// domains.
//
// The pane shows the *pinned* set rather than the live selection. A source click
// resolves to a dozen operators, so a pane driven by resolution would show all
// of them; pinning is the reader stating which ones they want, and it is what
// bounds this list.

import { type LiveEntry, type LiveState, type LiveStatus, type LiveTag, shownNodes, tagsFor } from "./liveStore";
import type { LiveProducer, LiveRow, LiveSource } from "./types";

/** One inspected operator, or one inspected source, as the pane draws it. */
export type LiveGroup = {
  /**
   * The tags that asked for this operator, in recency order.
   *
   * Several gestures can reach one operator, and the group names all of them
   * rather than picking one: which construct a reader is looking through is the
   * question the tag answers.
   */
  tags: readonly LiveTag[];
  /**
   * The operator's kind, from the static payload — `"ExtractFinal"`,
   * `"StoreDenseRead"`.
   *
   * Separate from a producer's name, and available whether or not the operator
   * has produced: the frame names a producer only once one has run, so without
   * this a group that recorded nothing could show nothing but its id.
   */
  label: string | undefined;
} & (
  | {
      kind: "operator";
      nodeId: number;
      /** Ticks between this entry and the newest one. Zero when it produced this tick. */
      staleBy: number;
      producers: LiveProducer[];
    }
  | {
      kind: "source";
      nodeId: number;
      source: LiveSource;
      /**
       * What crossed the channel, which the retained window cannot answer.
       *
       * A consumer releases a row from inside the pull that reads it, so the
       * window is what no reader has finished with rather than what arrived.
       * Empty for a source registered before anything was pushed.
       */
      producers: LiveProducer[];
    }
  // Asked for, but nothing has ever arrived for it. Rendered rather than
  // omitted: a group that vanishes is indistinguishable from one never asked
  // for.
  | {
      kind: "silent";
      nodeId: number;
      /** Whether the run has finished, making "produced nothing" final. */
      ran: boolean;
    }
);

/**
 * What the pane draws, as one value.
 *
 * A union rather than a set of booleans, so a state nobody handled is a compile
 * error at the `never` arm rather than a blank pane. The four cases are
 * genuinely different sentences, and conflating them is the failure this exists
 * to prevent.
 */
export type LivePanelState =
  | { kind: "no-tags" }
  // Tags exist but every one is unchecked, which is a choice rather than an
  // absence and reads differently from having inspected nothing.
  | { kind: "all-hidden"; tags: readonly LiveTag[] }
  | { kind: "not-run"; tags: readonly LiveTag[] }
  | { kind: "lost"; clean: boolean; tags: readonly LiveTag[] }
  | { kind: "groups"; status: LiveStatus; tags: readonly LiveTag[]; groups: LiveGroup[] };

/**
 * Join the pinned set against the cache.
 *
 * Pure, and takes no `Resolved`: pinning decoupled the pane from the selection,
 * which is what makes this testable with no DOM and no socket.
 */
export function livePanelState(
  state: LiveState,
  /** An operator's kind, from the static payload. */
  operatorLabel: (nodeId: number) => string | undefined = () => undefined,
): LivePanelState {
  const tags = state.tags;
  if (state.status.kind === "lost") return { kind: "lost", clean: state.status.clean, tags };
  if (tags.length === 0) return { kind: "no-tags" };
  const nodes = shownNodes(state);
  if (nodes.size === 0) return { kind: "all-hidden", tags };
  // Nothing has been published, so the program was compiled and not run. Said
  // separately from "asked for but silent": the machine is not in a state that
  // produces data, as against being in it and having produced none.
  if (state.status.kind === "connecting" || state.status.kind === "not-run") {
    return { kind: "not-run", tags };
  }

  // Ascending node id is construction order, so upstream sorts first.
  const groups: LiveGroup[] = [...nodes]
    .sort((a, b) => a - b)
    .map((nodeId) =>
      group(
        nodeId,
        state.nodes.get(nodeId),
        state.sources.get(nodeId),
        state.tick,
        tagsFor(state, nodeId),
        operatorLabel(nodeId),
        state.status,
      ),
    );
  return { kind: "groups", status: state.status, tags, groups };
}

function group(
  nodeId: number,
  entry: LiveEntry | undefined,
  source: LiveSource | undefined,
  tick: number,
  tags: readonly LiveTag[],
  label: string | undefined,
  status: LiveStatus,
): LiveGroup {
  if (source !== undefined) {
    return { kind: "source", nodeId, source, producers: entry?.producers ?? [], tags, label };
  }
  if (entry !== undefined) {
    return {
      kind: "operator",
      nodeId,
      staleBy: tick - entry.tick,
      producers: entry.producers,
      tags,
      label,
    };
  }
  // An operator with no recording has not been pulled. `get` is where a
  // recording is taken — that is what makes it non-perturbing — so an operator
  // whose demand path the run has not exercised has genuinely produced nothing.
  // Once the run is over that becomes permanent, and the two read differently.
  return { kind: "silent", nodeId, tags, label, ran: status.kind === "finished" };
}

/** The pane's plain-text rendering, for the copy button. */
export function serializeLivePanel(panel: LivePanelState): string {
  switch (panel.kind) {
    case "no-tags":
      return "nothing inspected";
    case "all-hidden":
      return `every tag hidden (${panel.tags.map((t) => t.label).join(", ")})`;
    case "not-run":
      return "static (no values) — compiled, not run";
    case "lost":
      return panel.clean ? "connection closed" : "connection lost";
    case "groups":
      return panel.groups.map(serializeGroup).join("\n\n");
  }
}

function serializeGroup(group: LiveGroup): string {
  const tags = group.tags.map((t) => `[${t.label}]`).join(" ");
  const prefix = tags === "" ? "" : `${tags} `;
  switch (group.kind) {
    case "silent":
      return `${prefix}${headText(group)}\n  ${
        group.ran ? "nothing flowed here during the run" : "nothing has flowed here yet"
      }`;
    case "source": {
      const retained = `retained ${countOf(group.source.rows.length, group.source.total)}`;
      const crossed = crossedText(group.producers);
      const meta = crossed === null ? retained : `${crossed} · ${retained}`;
      const head = `${prefix}${headText(group)} — ${meta}`;
      return [head, ...rowsOf(group).map((r) => `  ${rowText(r)}`)].join("\n");
    }
    case "operator":
      return group.producers
        .map((p) => {
          const head = `${prefix}#${group.nodeId}${
            group.label === undefined ? "" : ` ${group.label}`
          } · ${p.producer} ${p.shape} — ${countOf(
            p.rows.length,
            p.total,
          )}`;
          const note = p.note === null ? [] : [`  ${p.note}`];
          return [head, ...note, ...p.rows.map((r) => `  ${rowText(r)}`)].join("\n");
        })
        .join("\n");
  }
}

function rowText(row: LiveRow): string {
  const key = row.key === null ? "" : `${row.key}: `;
  return `${key}${row.value}${row.deleted ? " (deleted)" : ""}`;
}

/**
 * `shown of total`, or just the count when nothing was dropped.
 *
 * Stated whenever they differ, because the counts are the pane's only claim
 * about completeness.
 */
export function countOf(shown: number, total: number): string {
  return shown === total ? `${total} rows` : `${shown} of ${total} rows`;
}

/**
 * How a stale entry reads.
 *
 * A number, not the word: `stale` alone is uncheckable, while a tick difference
 * says how far behind and can be compared against the header's own tick.
 */
export function staleText(staleBy: number, tick: number): string | null {
  if (staleBy <= 0) return null;
  return `last produced at tick ${tick - staleBy} (now ${tick})`;
}

function el(tag: string, className?: string, text?: string): HTMLElement {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

/** A row's identity within its group, so a replacement frame updates in place. */
function rowKey(row: LiveRow, index: number): string {
  return row.key ?? `#${index}`;
}

/** A group's identity, stable across frames. */
function groupKey(group: LiveGroup): string {
  return group.kind === "operator"
    ? `op:${group.nodeId}`
    : group.kind === "source"
      ? `src:${group.nodeId}`
      : `silent:${group.nodeId}`;
}

interface RowHandle {
  row: HTMLElement;
  key: HTMLElement;
  value: HTMLElement;
}

interface GroupHandle {
  section: HTMLElement;
  tags: HTMLElement;
  head: HTMLElement;
  meta: HTMLElement;
  body: HTMLElement;
  rows: Map<string, RowHandle>;
}

/**
 * A tag's palette slot, from a stable hash of its label.
 *
 * Deterministic so the same construct keeps its colour across a session and
 * across re-inspection, rather than depending on the order tags were made in.
 */
export function tagColour(label: string, slots: number): number {
  // FNV-1a, offset basis included: seeding at zero measurably clumps short
  // labels, which is all these are (`Var(words): L8`). `>>> 0` takes the
  // unsigned value rather than folding the negative half onto the positive.
  let hash = 0x811c9dc5;
  for (let i = 0; i < label.length; i++) {
    hash = (hash ^ label.charCodeAt(i)) * 16777619;
    hash |= 0;
  }
  return (hash >>> 0) % slots;
}

/**
 * How many tag colours the stylesheet defines.
 *
 * Seven, not eight. The semantic tokens reserve the warm half of the wheel,
 * which is the half that survives colour-vision deficiency, so the free bands
 * are teal-cyan and violet-rose — and an eighth hue does not measurably improve
 * separation over the seventh. Past seven the modulo wraps, which is harmless
 * because a chip carries its label: colour groups, it never identifies.
 */
export const TAG_SLOTS = 7;

/**
 * The live values pane.
 *
 * Retained-mode: groups and rows are kept as handles and updated in place, so a
 * frame replacing a node's rows costs the text it changed rather than the DOM.
 * That is also what preserves scroll position, text selection and hover across
 * a frame — rebuilding the subtree every tick would lose all three.
 */
export class LiveView {
  private readonly root: HTMLElement;
  private readonly groups = new Map<string, GroupHandle>();
  private pending = 0;
  private readonly unsubscribe: () => void;

  constructor(
    parent: HTMLElement,
    private readonly live: {
      get(): LiveState;
      subscribe(fn: (state: LiveState) => void): () => void;
    },
    /** An operator's kind, from the static payload. */
    private readonly operatorLabel: (nodeId: number) => string | undefined = () => undefined,
    /**
     * Select the construct a tag names, and the operator a group is.
     *
     * Both are ordinary selections through the shared store, so they
     * cross-highlight every pane exactly as a click in a tree pane does. They
     * change no tag, so the pane's own contents are unaffected by reading
     * around in it — this view listens to the live store and not to the
     * selection, so a selection cannot even re-render it.
     */
    private readonly select?: {
      construct: (anchorId: number) => void;
      operator: (nodeId: number) => void;
    },
  ) {
    this.root = el("div", "live-root");
    parent.appendChild(this.root);
    // The pane never scrolls itself, so a replaced row must not slide the
    // content under the reader. `overflow-anchor` is the browser's own answer.
    this.root.style.overflowAnchor = "auto";
    this.render();
    this.unsubscribe = this.live.subscribe(() => this.schedule());
  }

  /** Stop listening. */
  dispose(): void {
    this.unsubscribe();
    if (this.pending !== 0) cancelAnimationFrame(this.pending);
  }

  /**
   * Coalesce frames into one paint.
   *
   * A run publishes on every tick that recorded something, which can be far
   * more often than a frame is worth drawing. Dropping intermediate frames is
   * correct here and only here: the wire is latest-wins, so the newest frame is
   * the whole answer. An append stream could not do this.
   */
  private schedule(): void {
    if (this.pending !== 0) return;
    this.pending = requestAnimationFrame(() => {
      this.pending = 0;
      this.render();
    });
  }

  private render(): void {
    const panel = livePanelState(this.live.get(), this.operatorLabel);
    if (panel.kind !== "groups") {
      this.groups.clear();
      this.root.replaceChildren(el("div", "live-empty", emptyText(panel)));
      return;
    }

    // The message the previous render left, if that render had no groups. It is
    // dropped rather than left in place: a run that has started publishing must
    // not still be saying it was compiled and not run, and groups are appended
    // to the root rather than replacing it.
    this.root.querySelector(".live-empty")?.remove();

    const seen = new Set<string>();
    for (const group of panel.groups) {
      const key = groupKey(group);
      seen.add(key);
      this.renderGroup(key, group, panel.status);
    }
    // A group whose pin was dropped goes; the rest stay, handles and all.
    for (const [key, handle] of this.groups) {
      if (!seen.has(key)) {
        handle.section.remove();
        this.groups.delete(key);
      }
    }
    // Order follows the pinned set's ascending ids, which `livePanelState`
    // already sorted. Re-append rather than diff positions: appending an
    // existing child moves it, and the list is short.
    for (const group of panel.groups) {
      const handle = this.groups.get(groupKey(group));
      if (handle) this.root.appendChild(handle.section);
    }
  }

  private renderGroup(key: string, group: LiveGroup, status: LiveStatus): void {
    let handle = this.groups.get(key);
    if (handle === undefined) {
      const section = el("section", "live-group");
      const tags = el("div", "live-group-tags");
      const head = el(
        this.select === undefined ? "div" : "button",
        "live-group-head",
      );
      if (head instanceof HTMLButtonElement) {
        head.type = "button";
        head.title = "Select this operator";
      }
      const meta = el("div", "live-group-meta");
      const body = el("div", "live-rows");
      section.append(tags, head, meta, body);
      handle = { section, tags, head, meta, body, rows: new Map() };
      this.groups.set(key, handle);
      this.root.appendChild(section);
    }

    const tick = status.kind === "live" || status.kind === "finished" ? status.tick : 0;
    // The tag chips say which construct asked for this operator, which is the
    // question a reader holding several inspections actually has.
    handle.tags.replaceChildren(
      ...group.tags.map((tag) => {
        const select = this.select;
        if (select === undefined) {
          const chip = el("span", "live-tag", tag.label);
          chip.dataset["colour"] = String(tagColour(tag.label, TAG_SLOTS));
          return chip;
        }
        const chip = el("button", "live-tag live-tag-button", tag.label) as HTMLButtonElement;
        chip.type = "button";
        chip.dataset["colour"] = String(tagColour(tag.label, TAG_SLOTS));
        chip.title = `Select ${tag.label}`;
        chip.addEventListener("click", (event) => {
          // The group head is also clickable, so a chip's click must not reach
          // it and select the operator instead of the construct.
          event.stopPropagation();
          select.construct(tag.anchorId);
        });
        return chip;
      }),
    );
    handle.tags.hidden = group.tags.length === 0;
    handle.head.textContent = headText(group);
    if (this.select !== undefined) {
      const select = this.select;
      const nodeId = group.nodeId;
      handle.head.onclick = () => select.operator(nodeId);
    }
    const meta = metaText(group, tick);
    handle.meta.textContent = meta ?? "";
    handle.meta.hidden = meta === null;
    this.renderRows(handle, rowsOf(group), droppedOf(group));
  }

  private renderRows(handle: GroupHandle, rows: LiveRow[], dropped: number): void {
    const seen = new Set<string>();
    // Truncation keeps the tail, so the rows that are missing are the earlier
    // ones and the marker belongs at the top of the list, in the list.
    if (dropped > 0) {
      seen.add("__dropped");
      const marker = this.rowHandle(handle, "__dropped", "live-row live-dropped");
      marker.key.textContent = "";
      marker.value.textContent = `${dropped} earlier rows not recorded`;
    }
    rows.forEach((row, index) => {
      const key = rowKey(row, index);
      seen.add(key);
      const rowHandle = this.rowHandle(handle, key, "live-row");
      rowHandle.key.textContent = row.key ?? "";
      rowHandle.value.textContent = row.value;
      // Three channels for one bit, not colour alone: the class carries the
      // dimming, the glyph is visible, and the word is readable.
      rowHandle.row.classList.toggle("deleted", row.deleted);
      rowHandle.row.dataset["deleted"] = row.deleted ? "deleted" : "";
    });
    for (const [key, row] of handle.rows) {
      if (!seen.has(key)) {
        row.row.remove();
        handle.rows.delete(key);
      }
    }
  }

  private rowHandle(handle: GroupHandle, key: string, className: string): RowHandle {
    const existing = handle.rows.get(key);
    if (existing) return existing;
    const row = el("div", className);
    const keyCell = el("span", "live-key");
    const valueCell = el("span", "live-value");
    row.append(keyCell, valueCell);
    handle.body.appendChild(row);
    const created = { row, key: keyCell, value: valueCell };
    handle.rows.set(key, created);
    return created;
  }
}

function rowsOf(group: LiveGroup): LiveRow[] {
  // What crossed the channel, falling back to what it still holds: a source
  // registered before anything was pushed has a window and no tail.
  if (group.kind === "source") {
    const crossed = group.producers.flatMap((p) => p.rows);
    return crossed.length > 0 ? crossed : group.source.rows;
  }
  if (group.kind === "operator") return group.producers.flatMap((p) => p.rows);
  return [];
}

function droppedOf(group: LiveGroup): number {
  if (group.kind === "source") {
    const crossed = group.producers.reduce((sum, p) => sum + p.dropped, 0);
    return group.producers.length > 0 ? crossed : group.source.dropped;
  }
  if (group.kind === "operator") {
    return group.producers.reduce((sum, p) => sum + p.dropped, 0);
  }
  return 0;
}

/** `shown of total` over a group's producers. */
function crossedText(producers: readonly LiveProducer[]): string | null {
  if (producers.length === 0) return null;
  const shown = producers.reduce((sum, p) => sum + p.rows.length, 0);
  const total = producers.reduce((sum, p) => sum + p.total, 0);
  return `${countOf(shown, total)} crossed`;
}

function headText(group: LiveGroup): string {
  // The operator's kind always, so a group that recorded nothing is still
  // named; a producer's instance name is extra, and only exists once one ran.
  const kind = group.label === undefined ? "" : ` ${group.label}`;
  switch (group.kind) {
    case "silent":
      return `#${group.nodeId}${kind}`;
    case "source":
      return `#${group.nodeId} ${group.source.name}`;
    case "operator": {
      const names = group.producers.map((p) => p.producer).join(", ");
      return `#${group.nodeId}${kind} · ${names}`;
    }
  }
}

function metaText(group: LiveGroup, tick: number): string | null {
  switch (group.kind) {
    case "silent":
      // What the pane knows is that no row has ever reached this node, not why.
      // A node whose last row-carrying answer is kept for the life of the run is
      // silent either because nothing pulled it or because every pull answered
      // empty, and the frame does not separate the two. An `ExtractFinal` over a
      // stream that never terminates is the permanent case, and after the run
      // ends every silent node is.
      return group.ran ? "nothing flowed here during the run" : "nothing has flowed here yet";
    case "source": {
      // Both, because they answer different questions: what the stream has
      // carried, and what the release protocol is still holding.
      const retained = `retained ${countOf(group.source.rows.length, group.source.total)}`;
      const crossed = crossedText(group.producers);
      return crossed === null ? retained : `${crossed} · ${retained}`;
    }
    case "operator": {
      const first = group.producers[0];
      if (first === undefined) return null;
      const shape = group.producers.length === 1 ? first.shape : "several producers";
      const shown = group.producers.reduce((sum, p) => sum + p.rows.length, 0);
      const total = group.producers.reduce((sum, p) => sum + p.total, 0);
      const parts = [shape, countOf(shown, total)];
      if (first.watermark !== null) parts.push(first.watermark);
      const stale = staleText(group.staleBy, tick);
      if (stale !== null) parts.push(stale);
      if (first.note !== null) parts.push(first.note);
      return parts.join(" · ");
    }
  }
}

/** The four states, each its own sentence. */
function emptyText(panel: LivePanelState): string {
  switch (panel.kind) {
    case "no-tags":
      return "Choose “inspect data” on a source or an operator to watch its values here.";
    case "all-hidden":
      return "Every tag is hidden. Check one in the ☰ menu to show its values.";
    case "not-run":
      return "static (no values) — this program was compiled, not run.";
    case "lost":
      return panel.clean ? "connection closed" : "connection lost";
    case "groups":
      // `render` never reaches this: a groups panel draws groups.
      return "";
  }
}
