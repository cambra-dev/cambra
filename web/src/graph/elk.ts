// The layered layout, on ELK.
//
// `elk.bundled.js` is the build with no worker: `vite-plugin-singlefile` emits
// one file, and a worker entry point does not survive that. It resolves its
// promise on the calling thread, so a layout blocks the frame it runs in — the
// graphs this pane draws are tens of nodes, where that is a few milliseconds.
//
// Feedback edges never reach here. They are the pane's cycle set, already named
// on the wire, and giving them to a layered algorithm as ordinary edges makes it
// rank around a cycle it cannot break. The caller draws them as back edges.

import ELK from "elkjs/lib/elk.bundled.js";
import type { ElkExtendedEdge, ElkNode } from "elkjs/lib/elk-api";

import type { GraphLayout, LayoutRequest, Placed } from "./layout";

const OPTIONS = {
  "elk.algorithm": "layered",
  "elk.direction": "DOWN",
  "elk.edgeRouting": "ORTHOGONAL",
  // The reader follows one edge at a time, so crossings cost more than area.
  "elk.layered.thoroughness": "10",
  "elk.layered.nodePlacement.strategy": "BRANDES_KOEPF",
};

export class ElkLayout implements GraphLayout {
  private readonly elk = new ELK();

  async run(request: LayoutRequest): Promise<Placed> {
    const graph: ElkNode = {
      id: "root",
      layoutOptions: {
        ...OPTIONS,
        "elk.spacing.nodeNode": String(request.nodeGap),
        "elk.layered.spacing.nodeNodeBetweenLayers": String(request.layerGap),
      },
      children: request.nodes.map((n) => ({ id: n.id, width: n.width, height: n.height })),
      edges: request.edges.map((e) => ({
        id: e.id,
        sources: [e.source],
        targets: [e.target],
      })),
    };
    const laid = await this.elk.layout(graph);
    return {
      width: laid.width ?? 0,
      height: laid.height ?? 0,
      nodes: (laid.children ?? []).map((c) => ({
        id: c.id,
        x: c.x ?? 0,
        y: c.y ?? 0,
        width: c.width ?? 0,
        height: c.height ?? 0,
      })),
      edges: ((laid.edges ?? []) as ElkExtendedEdge[]).map((e) => {
        const section = e.sections?.[0];
        const points = section
          ? [section.startPoint, ...(section.bendPoints ?? []), section.endPoint]
          : [];
        return { id: e.id, points: points.map((p) => ({ x: p.x, y: p.y })) };
      }),
    };
  }
}
