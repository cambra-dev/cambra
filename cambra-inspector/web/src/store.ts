// The thin reactive layer that links the N panes.
//
// The shared `selection` IS the cross-link: a click in any pane (source or a
// tree) calls `setSelection`, the store resolves it through the `LinkGraph` to
// a highlight set *per pane* plus a set of source spans, and every pane
// re-renders its own slice of that resolved state. There is exactly one source
// of truth, so the panes never talk to each other directly.

import { buildIndices, type Indices } from "./indices";
import {
  buildLinkGraph,
  resolveLinks,
  type LinkGraph,
  type PaneNode,
  type ResolveResult,
} from "./links";
import { OffsetMap, wordRangeAt } from "./offsets";
import { isIrPane } from "./types";
import type { PaneEntry, Snapshot, Span } from "./types";

// A selection in any pane: a node in a specific pane, a half-open range of
// source bytes, or nothing selected.
//
// A source selection is a range because a click and a drag are one gesture:
// `from === to` is a caret, which is what a click leaves behind, and `from <
// to` is a dragged range. There is no separate point variant to keep in step.
export type Selection =
  | { kind: "node"; paneId: string; nodeId: number }
  | { kind: "source"; from: number; to: number }
  | null;

/**
 * The pane id a selection came from, or `null` when it came from a gesture that
 * means "go there" rather than "look here".
 *
 * A pane does not scroll itself: the reader is already looking at the row they
 * clicked, and moving it under them is the one motion they did not ask for.
 * Every other pane scrolls to its topmost highlighted row. `null` opts a
 * gesture out of the exemption — goto-definition and the operator pane's
 * reference rows are jumps, so their own pane has to move too.
 */
export const SOURCE_PANE = "source";

export interface Resolved {
  selection: Selection;
  /** Which pane the selection came from; see {@link SOURCE_PANE}. */
  origin: string | null;
  /**
   * The source bytes the reader **pointed at**, as opposed to what those bytes
   * resolve to: the token under a click, the dragged range, or the span of a
   * row clicked in a pane. `null` when nothing is selected.
   *
   * This is the source pane's strong highlight, and it is deliberately not
   * derived from any node's span. Painting the resolved node's extent strongly
   * is what made a click on `if` claim the whole statement, and a click
   * anywhere inside a block look identical.
   */
  pointedAt: { from: number; to: number } | null;
  /** Per-pane highlight sets + the union of source spans (see `links.ts`). */
  result: ResolveResult;
  /**
   * Per pane, the nodes that **are** the selection: the anchor and its images
   * under the pane links. Everything else in
   * [`highlightsByPane`](ResolveResult) is something the resolution reached
   * from it.
   *
   * A pane can hold none. `ExprStmt` is rewritten away by channelize, so a
   * click on a statement has no counterpart downstream at all — five panes
   * light up entirely as traces. That is the truth about the program rather
   * than a gap to paper over, and the tree pane says so instead of leaving the
   * reader to wonder.
   */
  primaryByPane: Map<string, Set<number>>;
}

const EMPTY_RESOLVED = (selection: Selection): Resolved => ({
  selection,
  origin: null,
  pointedAt: null,
  result: { highlightsByPane: new Map(), sourceSpans: [] },
  primaryByPane: new Map(),
});

type Listener = (resolved: Resolved) => void;

export class Store {
  readonly snapshot: Snapshot;
  readonly offsets: OffsetMap;
  /** The pipeline panes in order (empty on a degraded snapshot). */
  readonly panes: PaneEntry[];
  /**
   * Per-pane derived indices, keyed by pane id — tree panes only. The indices
   * are tree-shaped (depth, predicate interiors, a node's rendered type), and
   * the operator pane has none of that, so it has no entry here.
   */
  readonly indicesByPane: Map<string, Indices>;
  /** The pane the source view anchors its hover/goto-def/squiggles on. */
  readonly sourceAnchorPaneId: string | null;

  private readonly linkGraph: LinkGraph;
  // B5: for each holes-kind (pre-inference) pane, a node's downstream-resolved
  // type(s). A holes-pane node carries a hole (`_`/`?N`); inference resolves it
  // on the anchor-pane node it maps to (via the dense paneLinks). Mono fan-out →
  // the type *set*. Empty/absent for nodes with no downstream type. Precomputed.
  private readonly resolvedTypesByPane: Map<string, Map<number, string[]>>;
  private resolved: Resolved = EMPTY_RESOLVED(null);
  /**
   * Each pane's narrowest span per node. Keyed by pane id and read off the node
   * tables, so it answers for the operator pane too — `indicesFor` is
   * tree-shaped and has nothing for it.
   */
  private readonly narrowestByPane = new Map<string, Map<number, Span | null>>();
  private readonly listeners = new Set<Listener>();

  constructor(snapshot: Snapshot) {
    // M1 ship-everything: the whole model arrives in one payload and every index
    // below is built eagerly, once, here. This is correct only because M1 is
    // static (source + typed IR, no runtime values). The post-M1 live surface
    // can't ship everything — values are O(N·K·T) and stream per-query over the
    // CQRS transport — so adding live values will mean reworking this eager
    // construction into an incremental/streaming store rather than adding a
    // field. Scoped to M1 by design; see web/README.md.
    this.snapshot = snapshot;
    this.offsets = new OffsetMap(snapshot.source.text);
    this.panes = snapshot.panes;

    this.indicesByPane = new Map();
    for (const pane of this.panes) {
      if (!isIrPane(pane)) continue;
      this.indicesByPane.set(
        pane.id,
        buildIndices(pane.roots, pane.nodes, snapshot.definitions, snapshot.source.text),
      );
    }

    // Hover/goto-def/squiggles read fully-resolved types, so they anchor on the
    // post-inference pane — by *id* (the middle pane), never by kind (the
    // post-channelize pane is also "typed") or position. Fallback, for payloads
    // without that id: the most-downstream *tree* pane. The anchor answers type
    // and tightest-node queries, which the operator pane has no tree to serve.
    const post = this.panes.find((s) => s.id === "post-inference");
    this.sourceAnchorPaneId = post?.id ?? this.panes.filter(isIrPane).at(-1)?.id ?? null;

    // Every pane joins the link graph, the operator pane included: provenance is
    // an id relation over the whole pipeline, and both node shapes carry the id
    // and the spans the resolver reads. Built from the node tables directly, so
    // it needs no tree-shaped index.
    for (const pane of this.panes) {
      // The narrowest span, which is the first one a node carries.
      const narrowest = new Map<number, Span | null>();
      for (const node of pane.nodes) narrowest.set(node.nodeId, node.spans[0] ?? null);
      this.narrowestByPane.set(pane.id, narrowest);
    }
    this.linkGraph = buildLinkGraph(
      this.panes.map((pane) => {
        const narrowest = this.narrowestByPane.get(pane.id) ?? new Map();
        return {
          id: pane.id,
          nodeIds: new Set(narrowest.keys()),
          spanOf: (nodeId: number) => narrowest.get(nodeId) ?? null,
        };
      }),
      snapshot.paneLinks,
    );

    this.resolvedTypesByPane = this.buildResolvedTypes();
  }

  /** The derived indices for a pane (undefined for an unknown id). */
  indicesFor(paneId: string): Indices | undefined {
    return this.indicesByPane.get(paneId);
  }

  /**
   * B5 stitch: the downstream-resolved type(s) of a holes-pane node — the
   * type(s) of the post-inference node(s) it maps to (via the dense paneLinks; a
   * mono fan-out yields the set). Empty for typed-pane / unmapped nodes.
   */
  resolvedTypesFor(paneId: string, nodeId: number): string[] {
    return this.resolvedTypesByPane.get(paneId)?.get(nodeId) ?? [];
  }

  private buildResolvedTypes(): Map<string, Map<number, string[]>> {
    const out = new Map<string, Map<number, string[]>>();
    const anchorId = this.sourceAnchorPaneId;
    const anchor = anchorId ? this.indicesByPane.get(anchorId) : undefined;
    if (!anchorId || !anchor) return out;

    for (const pane of this.panes) {
      // Only holes-kind panes stitch: a typed pane already carries real
      // types, so there is nothing to resolve downstream.
      if (pane.kind !== "holes" || pane.id === anchorId) continue;
      const byNode = new Map<number, string[]>();
      const upstream = this.indicesByPane.get(pane.id)!;
      for (const nodeId of upstream.nodeById.keys()) {
        // A predicate interior is not a hole awaiting a type — it is part of
        // one. Neither end of the stitch reads them: not the seed here, and not
        // the downstream hits below.
        if (upstream.predicateIds.has(nodeId)) continue;
        // Seeding a holes-pane node resolves through the adjacent window(s)
        // toward the anchor (the pre-inference -> post-inference window, plus
        // identity); we read only the anchor (post-inference) pane's hits.
        const { highlightsByPane } = resolveLinks(this.linkGraph, [{ paneId: pane.id, nodeId }]);
        const downstream = highlightsByPane.get(anchorId);
        if (!downstream) continue;
        const types: string[] = [];
        const seen = new Set<string>();
        for (const id of downstream) {
          // Inference mints a literal's singleton refinement *from* the literal,
          // so the predicate's nodes descend from it and land in `downstream`.
          // They are the type's own machinery, not what the hole resolved to.
          if (anchor.predicateIds.has(id)) continue;
          const ty = anchor.nodeById.get(id)?.type;
          if (ty !== undefined && !seen.has(ty)) {
            seen.add(ty);
            types.push(ty);
          }
        }
        if (types.length > 0) byNode.set(nodeId, types);
      }
      out.set(pane.id, byNode);
    }
    return out;
  }

  getResolved(): Resolved {
    return this.resolved;
  }

  /**
   * A node's narrowest source span, in whichever pane holds it, or `null` when
   * the node traces to no source. Works for both node shapes.
   */
  spanOf(paneId: string, nodeId: number): Span | null {
    return this.narrowestByPane.get(paneId)?.get(nodeId) ?? null;
  }

  /**
   * Replace the selection and re-resolve it across all panes.
   *
   * `origin` is the pane the gesture happened in, which that pane reads to
   * leave its own scroll position alone; omit it for a jump (see
   * {@link SOURCE_PANE}).
   */
  setSelection(selection: Selection, origin: string | null = null): void {
    if (selectionsEqual(selection, this.resolved.selection)) return;
    this.resolved = this.resolve(selection, origin);
    // Notify every subscriber even if one throws: a single broken view must not
    // starve the others. We do NOT swallow the error — it is surfaced via
    // console.error so the bug stays visible (this is exactly how Bug 1 hid: a
    // throwing first subscriber aborted the whole loop).
    for (const fn of this.listeners) {
      try {
        fn(this.resolved);
      } catch (e) {
        console.error("Store listener threw during setSelection", e);
      }
    }
  }

  /** Subscribe to resolved-selection changes. Returns an unsubscribe fn. */
  subscribe(fn: Listener): () => void {
    this.listeners.add(fn);
    return () => this.listeners.delete(fn);
  }

  private resolve(selection: Selection, origin: string | null): Resolved {
    if (selection === null) return EMPTY_RESOLVED(null);

    const anchorPane = this.sourceAnchorPaneId;
    const anchorIdx = anchorPane === null ? undefined : this.indicesByPane.get(anchorPane);

    // Two extents, and the whole colouring rests on their being different:
    //   `pointedAt` is what the reader indicated — a token, a dragged range, a
    //     row's span — and is what the source pane paints strongly;
    //   `region` is the construct that extent sits inside, and is how much the
    //     traces explain.
    //
    // One rule computes the region for every gesture: the tightest node
    // containing what was pointed at (`selectionRegion`). A caret takes the node
    // it is in, a drag the node it is inside, a clicked row its own extent.
    // These were three separate computations and so disagreed about how much to
    // explain — a drag ending part-way through an expression traced only the
    // nodes it fully covered, while a click inside the same statement traced
    // the whole of it.
    let pointedAt: { from: number; to: number } | null = null;
    // The nodes that *are* the selection. Their images are the strong
    // highlight in the panes; everything else resolved is a trace.
    const anchorSeeds: PaneNode[] = [];

    if (selection.kind === "node") {
      anchorSeeds.push({ paneId: selection.paneId, nodeId: selection.nodeId });
      const span = this.spanOf(selection.paneId, selection.nodeId);
      pointedAt = span === null ? null : { from: span.start, to: span.end };
    } else if (selection.from < selection.to) {
      // A drag says its own extent: that is what was pointed at, however much
      // of a construct it happens to cover.
      pointedAt = { from: selection.from, to: selection.to };
      if (anchorPane !== null && anchorIdx) {
        for (const nodeId of anchorIdx.nodesInRange(pointedAt.from, pointedAt.to)) {
          anchorSeeds.push({ paneId: anchorPane, nodeId });
        }
      }
    } else {
      const char = this.offsets.byteToChar(selection.from);
      const word = wordRangeAt(this.snapshot.source.text, char);
      pointedAt = {
        from: this.offsets.charToByte(word.from),
        to: this.offsets.charToByte(word.to),
      };
      const nodeId = anchorIdx?.tightestNodeAt(selection.from) ?? null;
      if (anchorPane !== null && nodeId !== null) {
        anchorSeeds.push({ paneId: anchorPane, nodeId });
      }
    }

    const region =
      pointedAt === null
        ? null
        : (anchorIdx?.selectionRegion(pointedAt.from, pointedAt.to) ?? pointedAt);

    // Each tree pane's own answer over the region. Two things need it: a pane
    // whose nodes are all wider than the region would otherwise go dark, and
    // the enclosing construct's span — `with begin():` on the line above a
    // clicked `if` — reaches the source pane only this way. Both arrive as
    // traces, never as anchors, so a wide downstream node can no longer widen
    // the strong highlight.
    const traceSeeds: PaneNode[] = [];
    if (region !== null) {
      for (const pane of this.panes) {
        const idx = this.indicesByPane.get(pane.id);
        if (!idx) continue;
        for (const nodeId of idx.nodesInRange(region.from, region.to)) {
          traceSeeds.push({ paneId: pane.id, nodeId });
        }
      }
    }

    // Two walks over one graph: the anchors alone, then everything. The
    // difference is what "reached from here" means, and it cannot be recovered
    // from a single walk.
    const anchored = resolveLinks(this.linkGraph, anchorSeeds);
    const result = resolveLinks(this.linkGraph, [...anchorSeeds, ...traceSeeds]);
    const primaryByPane = new Map<string, Set<number>>();
    for (const pane of this.panes) {
      primaryByPane.set(pane.id, anchored.highlightsByPane.get(pane.id) ?? new Set());
    }

    return { selection, origin, pointedAt, result, primaryByPane };
  }
}

function selectionsEqual(a: Selection, b: Selection): boolean {
  if (a === null || b === null) return a === b;
  if (a.kind !== b.kind) return false;
  if (a.kind === "node" && b.kind === "node") {
    return a.paneId === b.paneId && a.nodeId === b.nodeId;
  }
  if (a.kind === "source" && b.kind === "source") {
    return a.from === b.from && a.to === b.to;
  }
  return false;
}
