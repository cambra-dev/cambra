// Shared test helpers over the golden snapshot fixtures. These walk a snapshot's
// stage IR trees by *semantic* facts (stage id, node label) rather than raw
// NodeIds, so they survive id churn in the compiler.

import type { InspectNode, Snapshot, StageEntry } from "../types";

/** The stage with the given id (throws if absent). */
export function stageById(snap: Snapshot, id: string): StageEntry {
  const stage = (snap.stages ?? []).find((s) => s.id === id);
  if (!stage) throw new Error(`no stage ${id}`);
  return stage;
}

/** Every node in a stage's IR tree, flattened (empty if no IR). */
export function allNodes(ir: InspectNode | null): InspectNode[] {
  const out: InspectNode[] = [];
  const walk = (n: InspectNode): void => {
    out.push(n);
    for (const e of n.children) walk(e.node);
  };
  if (ir) walk(ir);
  return out;
}

/** The single node with `label` in a stage (throws unless exactly one). */
export function theNode(stage: StageEntry, label: string): InspectNode {
  const matches = allNodes(stage.ir).filter((n) => n.label === label);
  if (matches.length !== 1) {
    throw new Error(`expected exactly one "${label}" in ${stage.id}, found ${matches.length}`);
  }
  return matches[0];
}
