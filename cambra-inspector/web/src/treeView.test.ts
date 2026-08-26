// Pure unit tests for treeView.ts's DOM-free string logic:
//   - `resolvedTypeTooltip` (Bug 2): the B5 hole→resolved-type tooltip string.
//   - `serializeTree`: the plain-text rendering the pane's copy button yields.
// Both are extracted from the DOM so they can be covered directly; the jsdom
// view-integration test (views.dom.test.ts) exercises the rendering path.

import { describe, expect, it } from "vitest";

import { resolvedTypeTooltip, serializeTree } from "./treeView";
import { allNodesWithPredicates, fixture, paneById } from "./__fixtures__/helpers";
import type { IrChild, IrNode } from "./types";

import listMinJson from "./__fixtures__/list_min.snapshot.json";

describe("resolvedTypeTooltip", () => {
  it("renders a single resolved type", () => {
    expect(resolvedTypeTooltip("_", ["Int"])).toBe("`_` resolves to `Int`");
  });

  it("joins a mono fan-out type set with ` | `", () => {
    expect(resolvedTypeTooltip("_", ["Int", "String"])).toBe(
      "`_` resolves to `Int | String`",
    );
  });

  it("returns null when there are no resolved types", () => {
    expect(resolvedTypeTooltip("_", [])).toBeNull();
  });

  it("returns null when the local hole type is null", () => {
    expect(resolvedTypeTooltip(null, ["Int"])).toBeNull();
  });

  it("uses the actual local hole type in the message", () => {
    expect(resolvedTypeTooltip("(_ ⇒ _)", ["(Int ⇒ Int)"])).toBe(
      "`(_ ⇒ _)` resolves to `(Int ⇒ Int)`",
    );
  });
});

// A bare node-table entry. The serializer reads label / type / nodeId /
// children only; the rest of the wire shape is filled in so the literal
// typechecks.
function node(
  label: string,
  type: string,
  nodeId: number,
  children: IrChild[] = [],
): IrNode {
  return {
    label,
    nodeId,
    spans: [],
    rewritten: null,
    type,
    children,
  };
}

/** A node table keyed by id, from the entries a case declares. */
function table(...nodes: IrNode[]): Map<number, IrNode> {
  return new Map(nodes.map((n) => [n.nodeId, n]));
}

const value = (id: number): IrChild => ({ id, predicate: false });

describe("serializeTree", () => {
  it("renders the position, node label, type, and node id of a row", () => {
    const nodes = table(
      node("Let", "(Int ⇒ Int)", 12, [value(13)]),
      node("Lit(Int(1))", "Int@1", 13),
    );
    expect(serializeTree(12, nodes)).toBe("Let : (Int ⇒ Int) #12\n  0: Lit(Int(1)) : Int@1 #13");
  });

  it("omits the position on the root", () => {
    expect(serializeTree(1, table(node("Program", "Int", 1)))).toBe("Program : Int #1");
  });

  it("indents each depth level by two spaces", () => {
    const nodes = table(
      node("A", "Int", 1, [value(2), value(4)]),
      node("B", "Int", 2, [value(3)]),
      node("C", "Int", 3),
      node("D", "Int", 4),
    );
    expect(serializeTree(1, nodes)).toBe(
      "A : Int #1\n  0: B : Int #2\n    0: C : Int #3\n  1: D : Int #4",
    );
  });

  it("includes refinement-predicate children", () => {
    // The pane renders predicate subtrees as rows (renderNode walks children
    // unfiltered), so a serializer that filtered on the `predicate` flag would
    // silently disagree with the pane it claims to reproduce. A predicate row
    // carries no position prefix, exactly as the pane draws it.
    const nodes = table(
      node("Lit(Int(1))", "Int@1", 5, [{ id: 6, predicate: true }]),
      node("BinOp(Eq)", "Bool", 6),
    );
    expect(serializeTree(5, nodes)).toBe("Lit(Int(1)) : Int@1 #5\n  BinOp(Eq) : Bool #6");
  });

  it("gives a shared node one row per position that reaches it", () => {
    // The table holds a shared predicate once; the pane draws it under each
    // parent that names it, so the copy has to as well.
    const nodes = table(
      node("Root", "Int", 1, [value(2), { id: 3, predicate: true }]),
      node("Operand", "Int", 2, [{ id: 3, predicate: true }]),
      node("Pred", "Bool", 3),
    );
    expect(serializeTree(1, nodes)).toBe(
      "Root : Int #1\n  0: Operand : Int #2\n    Pred : Bool #3\n  Pred : Bool #3",
    );
  });

  it("emits no trailing newline", () => {
    expect(serializeTree(1, table(node("A", "Int", 1)))).not.toMatch(/\n$/);
  });

  it("reaches every node of a golden fixture's table, and invents none", () => {
    // Catches a dropped subtree, which the hand-built cases above cannot. Line
    // count is not the node count — a shared predicate gets a row per position —
    // so the check is on the id *set* the rows name.
    const snap = fixture(listMinJson);
    const pane = paneById(snap, "post-inference");
    const lines = serializeTree(pane.root, new Map(pane.nodes.map((n) => [n.nodeId, n]))).split(
      "\n",
    );
    expect(lines.length).toBeGreaterThan(1);
    const named = new Set(lines.map((l) => Number(l.trim().split("#").pop())));
    expect([...named].sort((a, b) => a - b)).toEqual(
      allNodesWithPredicates(pane)
        .map((n) => n.nodeId)
        .sort((a, b) => a - b),
    );
    // Every row is at least one node, and no node is missed.
    expect(lines.length).toBeGreaterThanOrEqual(named.size);
  });
});
