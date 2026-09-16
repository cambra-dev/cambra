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
      /**
       * What each producer last answered.
       *
       * Several, because a `FanOut` branch is subscribed once per branch. Every
       * fact about an answer — its shape, its counts, its watermark, how far
       * behind it is — belongs to one of these and not to the operator, so the
       * pane draws a line per producer rather than one line per node.
       */
      producers: LiveProducer[];
    }
  | { kind: "source"; nodeId: number; source: LiveSource }
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
  // A lost socket is a banner over the values, not a replacement for them: the
  // cache still holds every row, there is no reconnect, and a reader who has
  // just watched a run wants what it last said rather than an empty pane. It
  // stands alone only when there is nothing left to stand over.
  const lost = state.status.kind === "lost" ? state.status : null;
  if (tags.length === 0) {
    return lost ? { kind: "lost", clean: lost.clean, tags } : { kind: "no-tags" };
  }
  const nodes = shownNodes(state);
  if (nodes.size === 0) {
    return lost ? { kind: "lost", clean: lost.clean, tags } : { kind: "all-hidden", tags };
  }
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
  tags: readonly LiveTag[],
  label: string | undefined,
  status: LiveStatus,
): LiveGroup {
  if (source !== undefined) return { kind: "source", nodeId, source, tags, label };
  if (entry !== undefined) {
    return { kind: "operator", nodeId, producers: entry.producers, tags, label };
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
      return panel.groups.map((g) => serializeGroup(g, tickOf(panel.status))).join("\n\n");
  }
}

function serializeGroup(group: LiveGroup, tick: number): string {
  const tags = group.tags.map((t) => `[${t.label}]`).join(" ");
  const prefix = tags === "" ? "" : `${tags} `;
  const meta = metaText(group);
  const head = `${prefix}${headText(group)}${meta === null ? "" : ` — ${meta}`}`;
  return [head, ...bodyLines(group, tick).map(lineText)].join("\n");
}

function lineText(line: BodyLine): string {
  // A producer's own line sits between the group head and the rows it answered,
  // so the rows indent under it.
  const indent = line.role === "producer" ? "  " : "    ";
  const key = line.key === "" ? "" : `${line.key}: `;
  return `${indent}${key}${line.value}${line.deleted ? " (deleted)" : ""}`;
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
 * How a producer's staleness reads, or `null` when its answer is the current one.
 *
 * Two signals, and the wire carries both per producer. The tick difference is
 * the one to state where there is one: a number says how far behind and can be
 * compared against the header's own tick, where the word `stale` alone is
 * uncheckable. `stale` catches what the difference cannot — a producer pulled
 * again within this same tick that answered nothing, so its rows are already
 * not what it holds.
 */
export function staleText(producer: LiveProducer, tick: number): string | null {
  if (producer.tick < tick) return `last produced at tick ${producer.tick} (now ${tick})`;
  return producer.stale ? "pulled again this tick and answered nothing" : null;
}

/** The newest tick, against which a producer's own tick reads as staleness. */
function tickOf(status: LiveStatus): number {
  return status.kind === "live" || status.kind === "finished" ? status.tick : 0;
}

function el(tag: string, className?: string, text?: string): HTMLElement {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

/**
 * One line of a group's body: a producer's own line, a dropped-rows marker, or
 * a row.
 *
 * One list rather than a loop per kind, because every line is keyed, drawn and
 * ordered the same way — which is also what makes the order the frame's rather
 * than the order the handles happened to be created in.
 */
interface BodyLine {
  /**
   * Identity across frames, so a replacement frame updates the line in place.
   *
   * Qualified by the producer that answered it, not by the domain key alone: an
   * operator builds one producer per `FanOut` branch, and two of them holding a
   * row at one key are two rows. The role leads, so a producer whose row is
   * keyed `__dropped` cannot collide with its own marker.
   */
  id: string;
  role: BodyRole;
  /** The domain key, or empty for a line that sits at no position. */
  key: string;
  value: string;
  /** Whether the tile marks this position deleted. */
  deleted: boolean;
  /** Whether the producer that answered this line is behind the newest tick. */
  stale: boolean;
}

type BodyRole = "producer" | "dropped" | "row";

const LINE_CLASS: Record<BodyRole, string> = {
  producer: "live-producer",
  dropped: "live-row live-dropped",
  row: "live-row",
};

/** A group's body, in the order it draws. */
function bodyLines(group: LiveGroup, tick: number): BodyLine[] {
  switch (group.kind) {
    case "silent":
      return [];
    case "source":
      return windowLines("src", group.source.rows, group.source.dropped, false);
    case "operator":
      return group.producers.flatMap((producer) => {
        const stale = staleText(producer, tick);
        const scope = `p${producer.producerId}`;
        const head: BodyLine = {
          id: `producer:${scope}`,
          role: "producer",
          key: "",
          value: producerText(producer, stale),
          deleted: false,
          stale: stale !== null,
        };
        return [head, ...windowLines(scope, producer.rows, producer.dropped, stale !== null)];
      });
  }
}

/**
 * A retained window's lines: the dropped-rows marker, then the rows.
 *
 * Truncation keeps the tail, so the rows that are missing are the earlier ones
 * and the marker belongs above the ones that survived, in the list.
 */
function windowLines(
  scope: string,
  rows: readonly LiveRow[],
  dropped: number,
  stale: boolean,
): BodyLine[] {
  const marker: BodyLine[] =
    dropped === 0
      ? []
      : [
          {
            id: `dropped:${scope}`,
            role: "dropped",
            key: "",
            value: `${dropped} earlier rows not recorded`,
            deleted: false,
            stale,
          },
        ];
  const kept = rows.map((row, index) => ({
    id: `row:${scope}:${row.key ?? `#${index}`}`,
    role: "row" as const,
    key: row.key ?? "",
    value: row.value,
    deleted: row.deleted,
    stale,
  }));
  return [...marker, ...kept];
}

/** What one producer answered, as the line above its rows. */
function producerText(producer: LiveProducer, stale: string | null): string {
  return [
    producer.producer,
    producer.shape,
    countOf(producer.rows.length, producer.total),
    producer.watermark,
    stale,
    producer.note,
  ]
    .filter((part): part is string => part !== null)
    .join(" · ");
}

/** A group's identity, stable across frames. */
function groupKey(group: LiveGroup): string {
  return group.kind === "operator"
    ? `op:${group.nodeId}`
    : group.kind === "source"
      ? `src:${group.nodeId}`
      : `silent:${group.nodeId}`;
}

/** One drawn body line, kept so a replacement frame updates its text in place. */
interface LineHandle {
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
  lines: Map<string, LineHandle>;
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
  //
  // `Math.imul` rather than `*`: the round's product reaches ~3.6e16, past the
  // 2^53 a float64 holds exactly, so `*` rounds the low bits away before the
  // truncation — and those are the bits the next round mixes. Half the rounds
  // came out wrong, which made this some other hash wearing FNV's name.
  let hash = 0x811c9dc5;
  for (let i = 0; i < label.length; i++) {
    hash = Math.imul(hash ^ label.charCodeAt(i), 16777619);
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
  /** The lost-connection banner while one is shown, so it is not rebuilt. */
  private banner: HTMLElement | null = null;
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
    // The banner leads, and the groups are appended after it, so a socket that
    // drops mid-run says so above the values it last carried rather than
    // replacing them.
    this.renderBanner(panel.status);

    // Order follows the pinned set's ascending ids, which `livePanelState`
    // already sorted. Re-append rather than diff positions: appending an
    // existing child moves it, and the list is short.
    for (const group of panel.groups) {
      const handle = this.groups.get(groupKey(group));
      if (handle) this.root.appendChild(handle.section);
    }
  }

  /** The lost-connection banner, present only while the socket is gone. */
  private renderBanner(status: LiveStatus): void {
    if (status.kind !== "lost") {
      this.banner?.remove();
      this.banner = null;
      return;
    }
    this.banner ??= el("div", "live-banner");
    this.banner.textContent = `${
      status.clean ? "connection closed" : "connection lost"
    } — these are the last values it carried`;
    this.root.prepend(this.banner);
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
      handle = { section, tags, head, meta, body, lines: new Map() };
      this.groups.set(key, handle);
      this.root.appendChild(section);
    }

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
    const meta = metaText(group);
    handle.meta.textContent = meta ?? "";
    handle.meta.hidden = meta === null;
    this.renderRows(handle, bodyLines(group, tickOf(status)));
  }

  private renderRows(handle: GroupHandle, lines: BodyLine[]): void {
    const seen = new Set<string>();
    for (const line of lines) {
      seen.add(line.id);
      const row = this.lineHandle(handle, line.id, LINE_CLASS[line.role]);
      row.key.textContent = line.key;
      row.value.textContent = line.value;
      // Three channels for one bit, not colour alone: the class carries the
      // dimming, the glyph is visible, and the word is readable.
      row.row.classList.toggle("deleted", line.deleted);
      row.row.dataset["deleted"] = line.deleted ? "deleted" : "";
      // A stale producer's rows are dimmed, and the producer's own line says
      // how far behind in ticks — the same two channels.
      row.row.classList.toggle("stale", line.stale);
      row.row.dataset["stale"] = line.stale ? "stale" : "";
    }
    for (const [id, row] of handle.lines) {
      if (!seen.has(id)) {
        row.row.remove();
        handle.lines.delete(id);
      }
    }
    // Order follows the frame's, which `bodyLines` already fixed. Re-append
    // rather than diff positions: appending an existing child moves it, and a
    // group's body is short.
    for (const line of lines) handle.body.appendChild(handle.lines.get(line.id)!.row);
  }

  private lineHandle(handle: GroupHandle, id: string, className: string): LineHandle {
    const existing = handle.lines.get(id);
    if (existing) return existing;
    const row = el("div", className);
    const keyCell = el("span", "live-key");
    const valueCell = el("span", "live-value");
    row.append(keyCell, valueCell);
    handle.body.appendChild(row);
    const created = { row, key: keyCell, value: valueCell };
    handle.lines.set(id, created);
    return created;
  }
}

function headText(group: LiveGroup): string {
  if (group.kind === "source") return `#${group.nodeId} ${group.source.name}`;
  // The operator's kind, from the static payload, so a group that recorded
  // nothing is still named. A producer's instance name names one answer rather
  // than the operator, and rides that answer's own line.
  return group.label === undefined ? `#${group.nodeId}` : `#${group.nodeId} ${group.label}`;
}

function metaText(group: LiveGroup): string | null {
  switch (group.kind) {
    case "silent":
      // Not "no values recorded", which reads as a defect. Nothing has pulled
      // this operator: a recording is taken inside `get`, so an unexercised
      // demand path has produced nothing. An `ExtractFinal` over a stream that
      // never terminates is the permanent case, and after the run ends every
      // silent operator is.
      return group.ran ? "produced nothing during the run" : "not pulled yet";
    case "source":
      return `retained ${countOf(group.source.rows.length, group.source.total)}`;
    case "operator":
      // Nothing an operator's answer says holds for the operator: shape,
      // counts, watermark and staleness are each one producer's, and a group
      // that summarised them read the first producer's as the node's.
      return null;
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
