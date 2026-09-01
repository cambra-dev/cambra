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

// A click in any pane: a node in a specific pane, a raw source byte offset, or
// nothing selected.
export type Selection =
  | { kind: "node"; paneId: string; nodeId: number }
  | { kind: "source"; byteOffset: number }
  | null;

export interface Resolved {
  selection: Selection;
  /** Per-pane highlight sets + the union of source spans (see `links.ts`). */
  result: ResolveResult;
  /**
   * The strong-highlight anchor per pane: the directly-clicked node, or — for
   * a source click — that pane's tightest enclosing node. `null` for a pane
   * with no anchor (it shows only transitively-linked highlights).
   */
  primaryByPane: Map<string, number | null>;
}

const EMPTY_RESOLVED = (selection: Selection): Resolved => ({
  selection,
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

  /** Replace the selection and re-resolve it across all panes. */
  setSelection(selection: Selection): void {
    if (selectionsEqual(selection, this.resolved.selection)) return;
    this.resolved = this.resolve(selection);
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

  private resolve(selection: Selection): Resolved {
    if (selection === null) return EMPTY_RESOLVED(null);

    const seeds: PaneNode[] = [];
    const primaryByPane = new Map<string, number | null>();
    for (const pane of this.panes) primaryByPane.set(pane.id, null);

    if (selection.kind === "node") {
      seeds.push({ paneId: selection.paneId, nodeId: selection.nodeId });
      primaryByPane.set(selection.paneId, selection.nodeId);
    } else {
      // A source click has no node: resolve the byte offset to each pane's
      // tightest enclosing node, seed them all, and let the graph merge them.
      // The operator pane has no such index and so takes no seed of its own; the
      // graph still reaches it through the post-planning window.
      for (const pane of this.panes) {
        const node =
          this.indicesByPane.get(pane.id)?.tightestNodeAt(selection.byteOffset) ?? null;
        if (node !== null) {
          seeds.push({ paneId: pane.id, nodeId: node });
          primaryByPane.set(pane.id, node);
        }
      }
    }

    return { selection, result: resolveLinks(this.linkGraph, seeds), primaryByPane };
  }
}

function selectionsEqual(a: Selection, b: Selection): boolean {
  if (a === null || b === null) return a === b;
  if (a.kind !== b.kind) return false;
  if (a.kind === "node" && b.kind === "node") {
    return a.paneId === b.paneId && a.nodeId === b.nodeId;
  }
  if (a.kind === "source" && b.kind === "source") {
    return a.byteOffset === b.byteOffset;
  }
  return false;
}
