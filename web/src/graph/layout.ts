// The layout contract, stated without reference to who satisfies it.
//
// One implementation ships (`./elk`), under a licence the rest of this
// repository does not use. Everything the pane knows about layout is this file,
// so replacing the engine is replacing one module — see `./NOTICE`.

/** A box to place. Sizes are measured by the caller, which owns the fonts. */
export interface LayoutNode {
  id: string;
  width: number;
  height: number;
}

/** A connection to route. Only edges that may constrain rank belong here. */
export interface LayoutEdge {
  id: string;
  source: string;
  target: string;
}

export interface LayoutRequest {
  nodes: LayoutNode[];
  edges: LayoutEdge[];
  /** Gap between siblings in a layer, in px. */
  nodeGap: number;
  /** Gap between layers, in px. */
  layerGap: number;
}

export interface Point {
  x: number;
  y: number;
}

export interface PlacedNode extends Point {
  id: string;
  width: number;
  height: number;
}

/** A routed edge: producer end first, consumer end last. */
export interface PlacedEdge {
  id: string;
  points: Point[];
}

export interface Placed {
  width: number;
  height: number;
  nodes: PlacedNode[];
  edges: PlacedEdge[];
}

/**
 * Places boxes and routes edges, top to bottom.
 *
 * Asynchronous because the shipping implementation is. A caller must assume the
 * pane changed under it while a layout was in flight.
 */
export interface GraphLayout {
  run(request: LayoutRequest): Promise<Placed>;
}
