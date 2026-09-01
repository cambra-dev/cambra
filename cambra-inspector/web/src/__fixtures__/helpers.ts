// Shared test helpers: the golden snapshot fixtures, and the jsdom layout stubs
// every view test needs. The fixture walks reach a payload's pane node tables by
// *semantic* facts (pane id, node label) rather than raw NodeIds, so they
// survive id churn in the compiler.

import { isIrPane } from "../types";
import type { IrNode, IrPane, OperatorPane, PaneEntry, Snapshot } from "../types";
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
 * The tree pane with the given id (throws if absent, or if it holds a graph).
 * The tree walks below need `IrNode`s, so a test that reaches for one says so
 * here rather than narrowing at each use.
 */
export function irPaneById(snap: Snapshot, id: string): IrPane {
  const pane = paneById(snap, id);
  if (!isIrPane(pane)) throw new Error(`pane ${id} holds an operator graph, not a tree`);
  return pane;
}

/**
 * The operator pane with the given id (throws if absent, or if it holds a
 * tree). The mirror of `irPaneById`: `OperatorView` and
 * `serializeOperatorGraph` take an `OperatorPane`, so a test reaching for one
 * narrows here rather than at each use.
 */
export function operatorPaneById(snap: Snapshot, id: string): OperatorPane {
  const pane = paneById(snap, id);
  if (isIrPane(pane)) throw new Error(`pane ${id} holds a tree, not an operator graph`);
  return pane;
}

/**
 * Every node of a pane's **value** tree, walked from its root (empty if the
 * pane has no nodes).
 *
 * Refinement-predicate subtrees are skipped. They are real nodes on the wire,
 * but a test naming a node by its label means the one in the program: a literal
 * `1` carries a synthesized `__elem == 1` predicate holding a second
 * `Lit(Int(1))`, so walking into predicates makes almost every label ambiguous.
 * Use `allNodesWithPredicates` when the predicates are the point.
 */
export function allNodes(pane: IrPane): IrNode[] {
  return walk(pane, (child) => !child.predicate);
}

/** Every node of a pane's table, predicate interiors included. */
export function allNodesWithPredicates(pane: IrPane): IrNode[] {
  return walk(pane, () => true);
}

// Pre-order from the pane's one root, following the child edges `follow` admits. The table is
// a DAG — a shared predicate hangs off several parents — so a visited set keeps
// each node to one appearance in the result.
function walk(pane: IrPane, follow: (child: { predicate: boolean }) => boolean): IrNode[] {
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
  if (pane.nodes.length > 0) visit(pane.roots[0]);
  return out;
}

/**
 * The single value-tree node with `label` in a pane (throws unless exactly
 * one). Predicate interiors are not searched — see `allNodes`.
 */
export function theNode(pane: IrPane, label: string): IrNode {
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
