// Store-level tests over **golden `/api/snapshot` fixtures** produced by the
// real backend (`cambra-inspector <ex>.chl --dump-snapshot`, see
// `__fixtures__/README.md`). `Store` is DOM-free, so it constructs and resolves
// in plain vitest. These cover:
//   - T1: the B5 hole -> downstream-type stitch (`resolvedTypesFor`);
//   - T2: cross-pane resolution (`setSelection` -> `getResolved`);
//   - T3: the wire-shape contract — if the backend payload drifts from the TS
//     types, constructing the Store or these assertions break here.
//
// Assertions key on **semantic facts** (node labels / types), never raw NodeIds,
// so they survive id churn in the compiler; only a genuine behavioural or
// shape change should fail them.

import { describe, expect, it } from "vitest";

import { Store } from "./store";
import { PANE_IDS } from "./wireValidate";
import { allNodes, fixture, paneById, theNode } from "./__fixtures__/helpers";

import arithmeticJson from "./__fixtures__/arithmetic.snapshot.json";
import polymorphicJson from "./__fixtures__/polymorphic.snapshot.json";

const arithmetic = fixture(arithmeticJson);
const polymorphic = fixture(polymorphicJson);

const sorted = (xs: string[]): string[] => [...xs].sort();

describe("T3: wire-shape contract (golden fixture matches the TS types)", () => {
  for (const [name, snap] of [
    ["arithmetic", arithmetic],
    ["polymorphic", polymorphic],
  ] as const) {
    it(`${name}: the ordered panes + one paneLinks window per adjacent pair`, () => {
      // A literal, not SCHEMA_VERSION: `fixture()` already refused to load a
      // payload whose schema is not the constant, so reading the constant here
      // would assert it equals itself. The literal is the only spelling of this
      // line that can fail — it is what a version bump has to come back and
      // update.
      expect(snap.meta.schema).toBe(1);
      expect(snap.panes.map((s) => s.id)).toEqual([...PANE_IDS]);
      expect(snap.panes.map((s) => s.kind)).toEqual([
        "holes",
        "typed",
        "typed",
        "typed",
        "typed",
        "typed",
      ]);
      expect(snap.paneLinks.map((l) => [l.from, l.to])).toEqual([
        ["pre-inference", "post-inference"],
        ["post-inference", "post-channelize"],
        ["post-channelize", "post-as-of-read"],
        ["post-as-of-read", "post-lambda-elim"],
        ["post-lambda-elim", "post-planning"],
      ]);
      // Every edge is a [number, number, string[]] triple.
      for (const link of snap.paneLinks) {
        for (const [up, down] of link.edges) {
          expect(typeof up).toBe("number");
          expect(typeof down).toBe("number");
        }
      }
    });

    it(`${name}: Store builds non-empty per-pane indices, anchored post-inference`, () => {
      const store = new Store(snap);
      expect(store.panes.map((s) => s.id)).toEqual(PANE_IDS);
      expect(store.sourceAnchorPaneId).toBe("post-inference");
      for (const pane of store.panes) {
        const idx = store.indicesFor(pane.id)!;
        expect(idx.nodeById.size).toBeGreaterThan(0);
        // The table is the index: one entry per shipped node, no walk to lose
        // a node reached from several places.
        expect(idx.nodeById.size).toBe(pane.nodes.length);
      }
    });
  }
});

// NOTE: the exact type strings these tests pin (`"_"`, `"((Int@1, Int@2) ⇒ Int)"`,
// `"(Int@1, Int@1)"`, ...) are CCL's canonical type rendering —
// `Display for Type` in `src/ccl/mod.rs`. The coupling is intentional: if that
// formatting changes, these expectations must be updated in lockstep (the
// frontend reads the type as an opaque display string from `node.type`, so the
// only contract is the rendered text).
//
// A literal's type is its singleton refinement, which renders as base-at-value
// — `Int@1`, not `Int`. That is why several expectations below carry a value in
// a type position.
describe("T1: B5 hole -> downstream-type stitch (resolvedTypesFor)", () => {
  it("arithmetic: an identity hole resolves to its single downstream type", () => {
    const store = new Store(arithmetic);
    const pre = paneById(arithmetic, "pre-inference");

    const lit = theNode(pre, "Lit(Int(10))");
    expect(lit.type).toBe("_"); // local type is a hole pre-inference
    // Resolves to the literal's singleton type, which prints as `Int@10`.
    expect(store.resolvedTypesFor("pre-inference", lit.nodeId)).toEqual(["Int@10"]);

    const lambda = theNode(pre, "Lambda(__arg_tuple_0)");
    expect(lambda.type).toBe("(_ ⇒ _)"); // a function-shaped hole
    expect(store.resolvedTypesFor("pre-inference", lambda.nodeId)).toEqual([
      "((Int@1, Int@2) ⇒ Int)",
    ]);
  });

  it("polymorphic: a monomorphized hole resolves to the downstream type *set*", () => {
    const store = new Store(polymorphic);
    const pre = paneById(polymorphic, "pre-inference");

    // The `(x, x)` body: one pre-inference Tuple, two specialized clones.
    const tuple = theNode(pre, "Tuple");
    expect(tuple.type).toBe("_");
    // The Int specialization comes from `dup(1)`, so its element type is that
    // literal's singleton; `dup(2 == 2)`'s operand is a comparison, not a
    // literal, so the Bool specialization stays `(Bool, Bool)`.
    expect(sorted(store.resolvedTypesFor("pre-inference", tuple.nodeId))).toEqual(
      sorted(["(Int@1, Int@1)", "(Bool, Bool)"]),
    );

    // The `dup` lambda fans out to two specialized function types.
    const lambda = theNode(pre, "Lambda(x)");
    expect(sorted(store.resolvedTypesFor("pre-inference", lambda.nodeId))).toEqual(
      sorted(["(Int@1 ⇒ (Int@1, Int@1))", "(Bool ⇒ (Bool, Bool))"]),
    );
  });

  it("the typed panes do not stitch (they already carry real types)", () => {
    const store = new Store(arithmetic);
    for (const paneId of ["post-inference", "post-channelize"]) {
      const pane = paneById(arithmetic, paneId);
      for (const node of allNodes(pane)) {
        expect(store.resolvedTypesFor(paneId, node.nodeId)).toEqual([]);
      }
    }
  });
});

describe("T2: cross-pane resolution (setSelection -> getResolved)", () => {
  it("a node click highlights its identity twin in the downstream panes + a source span", () => {
    const store = new Store(arithmetic);
    const pre = paneById(arithmetic, "pre-inference");
    const lit = theNode(pre, "Lit(Int(10))"); // shared id (identity) across panes

    store.setSelection({ kind: "node", paneId: "pre-inference", nodeId: lit.nodeId });
    const { result, primaryByPane } = store.getResolved();

    expect(result.highlightsByPane.get("pre-inference")!.has(lit.nodeId)).toBe(true);
    // Identity: the same NodeId is highlighted in both downstream panes.
    expect(result.highlightsByPane.get("post-inference")!.has(lit.nodeId)).toBe(true);
    expect(result.highlightsByPane.get("post-channelize")!.has(lit.nodeId)).toBe(true);
    expect(primaryByPane.get("pre-inference")).toBe(lit.nodeId);
    // Projects to the literal's source span.
    expect(result.sourceSpans).toContainEqual(lit.spans[0]);
  });

  it("a mono-fan-out node click highlights every downstream clone", () => {
    const store = new Store(polymorphic);
    const pre = paneById(polymorphic, "pre-inference");
    const lambda = theNode(pre, "Lambda(x)");

    store.setSelection({ kind: "node", paneId: "pre-inference", nodeId: lambda.nodeId });
    const downstream = store.getResolved().result.highlightsByPane.get("post-inference")!;
    // Two specializations -> at least two distinct downstream nodes.
    expect(downstream.size).toBeGreaterThanOrEqual(2);
  });

  it("an inline-fan-out node click reaches the post-channelize copies (window 2)", () => {
    // polymorphic: one lambda applied at four sites — inference specializes it
    // per type and inline duplicates each body per call site, so the
    // post-inference -> post-channelize paneLinks window carries the
    // (copy, origin) edges (RT-3b at the store level).
    const window2 = polymorphic.paneLinks.find(
      (l) => l.from === "post-inference" && l.to === "post-channelize",
    )!;
    // A genuine (non-self) fan-out edge: origin !== copy.
    const fanout = window2.edges.find(([u, d]) => u !== d)!;
    expect(fanout).toBeDefined();

    const store = new Store(polymorphic);
    const [origin, copy] = fanout;
    store.setSelection({ kind: "node", paneId: "post-inference", nodeId: origin });
    const downstream = store.getResolved().result.highlightsByPane.get("post-channelize")!;
    expect(downstream.has(copy)).toBe(true);
  });

  it("a source click seeds each pane's tightest node (all panes light up)", () => {
    const store = new Store(arithmetic);
    const pre = paneById(arithmetic, "pre-inference");
    const lit = theNode(pre, "Lit(Int(10))");

    store.setSelection({ kind: "source", byteOffset: lit.spans[0]!.start });
    const { result, primaryByPane } = store.getResolved();
    for (const paneId of PANE_IDS) {
      expect(result.highlightsByPane.get(paneId)!.size).toBeGreaterThan(0);
      expect(primaryByPane.get(paneId)).not.toBeNull();
    }
  });

  it("clearing the selection empties the resolved state", () => {
    const store = new Store(arithmetic);
    const pre = paneById(arithmetic, "pre-inference");
    store.setSelection({
      kind: "node",
      paneId: "pre-inference",
      nodeId: theNode(pre, "Lit(Int(10))").nodeId,
    });
    store.setSelection(null);
    const { result } = store.getResolved();
    expect(result.sourceSpans).toEqual([]);
    expect(result.highlightsByPane.size).toBe(0);
  });
});
