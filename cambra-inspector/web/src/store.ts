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
import { OffsetMap } from "./offsets";
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
  /** Per-pane highlight sets + the union of source spans (see `links.ts`). */
  result: ResolveResult;
  /**
   * The strong-highlight anchors per pane: the directly-clicked node, or — for
   * a source selection — that pane's tightest enclosing node. A set rather
   * than one node because a selection can name several spans, and each
   * resolves per pane. Empty for a pane with no anchor of its own (it shows
   * only transitively-linked highlights).
   */
  primaryByPane: Map<string, Set<number>>;
}

const EMPTY_RESOLVED = (selection: Selection): Resolved => ({
  selection,
  origin: null,
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
        buildIndices(pane.roots, pane.nodes, snapshot.definitions),
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
    this.linkGraph = buildLinkGraph(
      this.panes.map((pane) => {
        // The narrowest span, which is the first one a node carries.
        const narrowest = new Map<number, Span | null>();
        for (const node of pane.nodes) narrowest.set(node.nodeId, node.spans[0] ?? null);
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

    const seeds: PaneNode[] = [];
    const primaryByPane = new Map<string, Set<number>>();
    for (const pane of this.panes) primaryByPane.set(pane.id, new Set());
    const anchor = (paneId: string, nodeId: number): void => {
      const set = primaryByPane.get(paneId);
      if (set) set.add(nodeId);
      else primaryByPane.set(paneId, new Set([nodeId]));
    };

    if (selection.kind === "node") {
      seeds.push({ paneId: selection.paneId, nodeId: selection.nodeId });
      anchor(selection.paneId, selection.nodeId);
    } else {
      // A source selection has no node: resolve the byte range to the nodes
      // each pane draws inside it, seed them all, and let the graph merge them.
      // The operator pane has no such index and so takes no seed of its own;
      // the graph still reaches it through the post-planning window.
      for (const pane of this.panes) {
        const nodes =
          this.indicesByPane.get(pane.id)?.nodesInRange(selection.from, selection.to) ?? [];
        for (const node of nodes) {
          seeds.push({ paneId: pane.id, nodeId: node });
          anchor(pane.id, node);
        }
      }
    }

    return { selection, origin, result: resolveLinks(this.linkGraph, seeds), primaryByPane };
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
