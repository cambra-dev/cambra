// Shared test helpers: the golden snapshot fixtures, and the jsdom layout stubs
// every view test needs. The fixture walks reach a payload's pane node tables by
// *semantic* facts (pane id, node label) rather than raw NodeIds, so they
// survive id churn in the compiler.

import type { IrNode, PaneEntry, Snapshot } from "../types";
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
        "  cambra-inspector/scripts/regen-fixtures.sh, updating any hand-written\n" +
        "  expectations in the same change — re-bless discipline in\n" +
        "  web/src/__fixtures__/README.md.",
    );
  }
}

/** The pane with the given id (throws if absent). */
export function paneById(snap: Snapshot, id: string): PaneEntry {
  const pane = (snap.panes ?? []).find((s) => s.id === id);
  if (!pane) throw new Error(`no pane ${id}`);
  return pane;
}

/**
 * Every node of a pane's **value** tree, walked from `root` (empty if the pane
 * has no nodes).
 *
 * Refinement-predicate subtrees are skipped. They are real nodes on the wire,
 * but a test naming a node by its label means the one in the program: a literal
 * `1` carries a synthesized `__elem == 1` predicate holding a second
 * `Lit(Int(1))`, so walking into predicates makes almost every label ambiguous.
 * Use `allNodesWithPredicates` when the predicates are the point.
 */
export function allNodes(pane: PaneEntry): IrNode[] {
  return walk(pane, (child) => !child.predicate);
}

/** Every node of a pane's table, predicate interiors included. */
export function allNodesWithPredicates(pane: PaneEntry): IrNode[] {
  return walk(pane, () => true);
}

// Pre-order from `root`, following the child edges `follow` admits. The table is
// a DAG — a shared predicate hangs off several parents — so a visited set keeps
// each node to one appearance in the result.
function walk(pane: PaneEntry, follow: (child: { predicate: boolean }) => boolean): IrNode[] {
  const byId = new Map(pane.nodes.map((n) => [n.nodeId, n]));
  const out: IrNode[] = [];
  const seen = new Set<number>();
  const visit = (id: number): void => {
    if (seen.has(id)) return;
    seen.add(id);
    const node = byId.get(id);
    if (!node) return;
    out.push(node);
    for (const child of node.children) if (follow(child)) visit(child.id);
  };
  if (pane.nodes.length > 0) visit(pane.root);
  return out;
}

/**
 * The single value-tree node with `label` in a pane (throws unless exactly
 * one). Predicate interiors are not searched — see `allNodes`.
 */
export function theNode(pane: PaneEntry, label: string): IrNode {
  const matches = allNodes(pane).filter((n) => n.label === label);
  if (matches.length !== 1) {
    throw new Error(`expected exactly one "${label}" in ${pane.id}, found ${matches.length}`);
  }
  return matches[0];
}

/**
 * Give jsdom the geometry APIs the views call. Idempotent; jsdom-only tests
 * call it from a `beforeAll`.
 *
 * jsdom implements neither `scrollIntoView` (CodeMirror and TreeView call it)
 * nor layout, so CodeMirror's measure pass — fired from a requestAnimationFrame
 * *after* the test body — calls `getClientRects` on a Range or Element and
 * throws an uncaught exception that fails an unrelated test. The rects are
 * empty because no test asserts on geometry: selection is driven through the
 * store directly.
 */
export function stubLayout(): void {
  (Element.prototype as unknown as { scrollIntoView: () => void }).scrollIntoView = () => {};

  const emptyRects = () => ({ length: 0, item: () => null, [Symbol.iterator]: function* () {} });
  const emptyRect = () => ({
    top: 0,
    left: 0,
    bottom: 0,
    right: 0,
    width: 0,
    height: 0,
    x: 0,
    y: 0,
  });
  (Range.prototype as unknown as { getClientRects: () => unknown }).getClientRects =
    emptyRects as never;
  (Range.prototype as unknown as { getBoundingClientRect: () => unknown }).getBoundingClientRect =
    emptyRect as never;
  (Element.prototype as unknown as { getClientRects: () => unknown }).getClientRects =
    emptyRects as never;
  (Element.prototype as unknown as { getBoundingClientRect: () => unknown }).getBoundingClientRect =
    emptyRect as never;
}
