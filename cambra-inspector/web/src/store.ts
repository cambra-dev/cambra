// The thin reactive layer that links the N panes.
//
// The shared `selection` IS the cross-link: a click in any pane (source or a
// tree) calls `setSelection`, the store resolves it through the `LinkGraph` to
// a highlight set *per stage* plus a set of source spans, and every pane
// re-renders its own slice of that resolved state. There is exactly one source
// of truth, so the panes never talk to each other directly.

import { buildIndices, type Indices } from "./indices";
import {
  buildLinkGraph,
  resolveLinks,
  type LinkGraph,
  type ResolveResult,
  type StageNode,
} from "./links";
import { OffsetMap } from "./offsets";
import type { Snapshot, StageEntry } from "./types";

// A click in any pane: a node in a specific stage, a raw source byte offset, or
// nothing selected.
export type Selection =
  | { kind: "node"; stageId: string; nodeId: number }
  | { kind: "source"; byteOffset: number }
  | null;

export interface Resolved {
  selection: Selection;
  /** Per-stage highlight sets + the union of source spans (see `links.ts`). */
  result: ResolveResult;
  /**
   * The strong-highlight anchor per stage: the directly-clicked node, or — for
   * a source click — that stage's tightest enclosing node. `null` for a stage
   * with no anchor (it shows only transitively-linked highlights).
   */
  primaryByStage: Map<string, number | null>;
}

const EMPTY_RESOLVED = (selection: Selection): Resolved => ({
  selection,
  result: { highlightsByStage: new Map(), sourceSpans: [] },
  primaryByStage: new Map(),
});

type Listener = (resolved: Resolved) => void;

export class Store {
  readonly snapshot: Snapshot;
  readonly offsets: OffsetMap;
  /** The IR stages in pipeline order (empty on a degraded snapshot). */
  readonly stages: StageEntry[];
  /** Per-stage derived indices, keyed by stage id. */
  readonly indicesByStage: Map<string, Indices>;
  /** The stage the source view anchors its hover/goto-def/squiggles on. */
  readonly sourceAnchorStageId: string | null;

  private readonly linkGraph: LinkGraph;
  // B5: for each holes-kind (pre-inference) stage, a node's downstream-resolved
  // type(s). A holes-stage node carries a hole (`_`/`?N`); inference resolves it
  // on the anchor-stage node it maps to (via the dense paneLinks). Mono fan-out →
  // the type *set*. Empty/absent for nodes with no downstream type. Precomputed.
  private readonly resolvedTypesByStage: Map<string, Map<number, string[]>>;
  private resolved: Resolved = EMPTY_RESOLVED(null);
  private readonly listeners = new Set<Listener>();

  constructor(snapshot: Snapshot) {
    // M1 ship-everything: the whole model arrives in one payload and every index
    // below is built eagerly, once, here. This is correct only because M1 is
    // static (source + typed IR, no runtime values). The post-M1 live surface
    // can't ship everything — values are O(N·K·T) and stream per-query over the
    // CQRS transport — so adding live values is NOT just filling the meta.tick /
    // value-summary seams; it will mean reworking this eager construction into an
    // incremental/streaming store. Scoped to M1 by design; see web/README.md.
    this.snapshot = snapshot;
    this.offsets = new OffsetMap(snapshot.source.text);
    this.stages = snapshot.stages;

    this.indicesByStage = new Map();
    for (const stage of this.stages) {
      this.indicesByStage.set(
        stage.id,
        buildIndices(stage.ir, stage.spanIndex, snapshot.definitions),
      );
    }

    // Hover/goto-def/squiggles read fully-resolved types, so they anchor on the
    // post-inference stage — by *id* (the middle pane), never by kind (the
    // post-desugar stage is also "typed") or position. Fallback: the
    // most-downstream stage, for payloads without that id.
    const post = this.stages.find((s) => s.id === "post-inference");
    this.sourceAnchorStageId = post?.id ?? this.stages.at(-1)?.id ?? null;

    this.linkGraph = buildLinkGraph(
      this.stages.map((stage) => {
        const idx = this.indicesByStage.get(stage.id)!;
        return {
          id: stage.id,
          nodeIds: new Set(idx.nodeById.keys()),
          spanOf: (nodeId: number) => idx.nodeById.get(nodeId)?.span ?? null,
        };
      }),
      snapshot.paneLinks,
    );

    this.resolvedTypesByStage = this.buildResolvedTypes();
  }

  /** The derived indices for a stage (undefined for an unknown id). */
  indicesFor(stageId: string): Indices | undefined {
    return this.indicesByStage.get(stageId);
  }

  /**
   * B5 stitch: the downstream-resolved type(s) of a holes-stage node — the
   * type(s) of the post-inference node(s) it maps to (via the dense paneLinks; a
   * mono fan-out yields the set). Empty for typed-stage / unmapped nodes.
   */
  resolvedTypesFor(stageId: string, nodeId: number): string[] {
    return this.resolvedTypesByStage.get(stageId)?.get(nodeId) ?? [];
  }

  private buildResolvedTypes(): Map<string, Map<number, string[]>> {
    const out = new Map<string, Map<number, string[]>>();
    const anchorId = this.sourceAnchorStageId;
    const anchor = anchorId ? this.indicesByStage.get(anchorId) : undefined;
    if (!anchorId || !anchor) return out;

    for (const stage of this.stages) {
      // Only holes-kind stages stitch: a typed stage already carries real
      // types, so there is nothing to resolve downstream.
      if (stage.kind !== "holes" || stage.id === anchorId) continue;
      const byNode = new Map<number, string[]>();
      for (const nodeId of this.indicesByStage.get(stage.id)!.nodeById.keys()) {
        // Seeding a holes-stage node resolves through the adjacent window(s)
        // toward the anchor (the pre-inference -> post-inference window, plus
        // identity); we read only the anchor (post-inference) stage's hits.
        const { highlightsByStage } = resolveLinks(this.linkGraph, [{ stageId: stage.id, nodeId }]);
        const downstream = highlightsByStage.get(anchorId);
        if (!downstream) continue;
        const types: string[] = [];
        const seen = new Set<string>();
        for (const id of downstream) {
          const ty = anchor.nodeById.get(id)?.type ?? null;
          if (ty !== null && !seen.has(ty)) {
            seen.add(ty);
            types.push(ty);
          }
        }
        if (types.length > 0) byNode.set(nodeId, types);
      }
      out.set(stage.id, byNode);
    }
    return out;
  }

  getResolved(): Resolved {
    return this.resolved;
  }

  /** Replace the selection and re-resolve it across all stages. */
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

    const seeds: StageNode[] = [];
    const primaryByStage = new Map<string, number | null>();
    for (const stage of this.stages) primaryByStage.set(stage.id, null);

    if (selection.kind === "node") {
      seeds.push({ stageId: selection.stageId, nodeId: selection.nodeId });
      primaryByStage.set(selection.stageId, selection.nodeId);
    } else {
      // A source click has no node: resolve the byte offset to each stage's
      // tightest enclosing node, seed them all, and let the graph merge them.
      for (const stage of this.stages) {
        const node = this.indicesByStage.get(stage.id)!.tightestNodeAt(selection.byteOffset);
        if (node !== null) {
          seeds.push({ stageId: stage.id, nodeId: node });
          primaryByStage.set(stage.id, node);
        }
      }
    }

    return { selection, result: resolveLinks(this.linkGraph, seeds), primaryByStage };
  }
}

function selectionsEqual(a: Selection, b: Selection): boolean {
  if (a === null || b === null) return a === b;
  if (a.kind !== b.kind) return false;
  if (a.kind === "node" && b.kind === "node") {
    return a.stageId === b.stageId && a.nodeId === b.nodeId;
  }
  if (a.kind === "source" && b.kind === "source") {
    return a.byteOffset === b.byteOffset;
  }
  return false;
}
