// Shared test helpers over the golden snapshot fixtures. These walk a snapshot's
// stage IR trees by *semantic* facts (stage id, node label) rather than raw
// NodeIds, so they survive id churn in the compiler.

import type { InspectNode, Snapshot, StageEntry } from "../types";
import { validateSnapshot } from "../wireValidate";

/**
 * Validate a golden fixture, enriching any wire error with the fixture
 * lifecycle: these JSONs are regenerated artifacts, so a mismatch here usually
 * means stale fixtures or a half-propagated schema change, not a frontend bug.
 * Production code keeps calling `validateSnapshot` directly — a live payload
 * error must not tell users to regenerate test fixtures.
 */
export function fixture(json: unknown): Snapshot {
  try {
    return validateSnapshot(json);
  } catch (e) {
    throw new Error(
      `${String(e)}\n` +
        "  This is a golden fixture. If the wire shape changed on purpose, regenerate via\n" +
        "  cambra-inspector/scripts/regen-fixtures.sh, updating SCHEMA_VERSION (wireValidate.ts)\n" +
        "  and any hand-written expectations together — re-bless discipline in\n" +
        "  web/src/__fixtures__/README.md.",
    );
  }
}

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
