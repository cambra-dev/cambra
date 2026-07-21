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
import { validateSnapshot } from "./wireValidate";
import { allNodes, stageById, theNode } from "./__fixtures__/helpers";

import arithmeticJson from "./__fixtures__/arithmetic.snapshot.json";
import polymorphicJson from "./__fixtures__/polymorphic.snapshot.json";
import udfFanoutJson from "./__fixtures__/udf_fanout.snapshot.json";

const arithmetic = validateSnapshot(arithmeticJson);
const polymorphic = validateSnapshot(polymorphicJson);
const udfFanout = validateSnapshot(udfFanoutJson);

const STAGE_IDS = ["pre-inference", "post-inference", "post-desugar"];

const sorted = (xs: string[]): string[] => [...xs].sort();

describe("T3: wire-shape contract (golden fixture matches the TS types)", () => {
  for (const [name, snap] of [
    ["arithmetic", arithmetic],
    ["polymorphic", polymorphic],
  ] as const) {
    it(`${name}: three ordered stages + the two paneLinks windows`, () => {
      expect(snap.meta.schema).toBe(3);
      expect(snap.stages.map((s) => s.id)).toEqual(STAGE_IDS);
      expect(snap.stages.map((s) => s.kind)).toEqual(["holes", "typed", "typed"]);
      expect(snap.paneLinks.map((l) => [l.from, l.to])).toEqual([
        ["pre-inference", "post-inference"],
        ["post-inference", "post-desugar"],
      ]);
      // Every edge is a [number, number] pair.
      for (const link of snap.paneLinks) {
        for (const [up, down] of link.edges) {
          expect(typeof up).toBe("number");
          expect(typeof down).toBe("number");
        }
      }
    });

    it(`${name}: Store builds non-empty per-stage indices, anchored post-inference`, () => {
      const store = new Store(snap);
      expect(store.stages.map((s) => s.id)).toEqual(STAGE_IDS);
      expect(store.sourceAnchorStageId).toBe("post-inference");
      for (const stage of store.stages) {
        expect(store.indicesFor(stage.id)!.nodeById.size).toBeGreaterThan(0);
      }
    });
  }
});

// NOTE: the exact type strings these tests pin (`"_"`, `"((1, Int) ⇒ Int)"`,
// `"(1, 1)"`, `"(Int ⇒ (1, 1))"`, ...) are CCL's *canonical* type rendering —
// `Display for Type` in `src/ccl/mod.rs`. The coupling is intentional: if that
// formatting changes, these expectations must be updated in lockstep (the
// frontend reads the type as an opaque display string from `node.type`, so the
// only contract is the rendered text).
//
// A literal's type is its *singleton* refinement, which renders as the literal
// itself — `1`, not `Int`. That is why several expectations below read as
// values where a base type might be expected.
describe("T1: B5 hole -> downstream-type stitch (resolvedTypesFor)", () => {
  it("arithmetic: an identity hole resolves to its single downstream type", () => {
    const store = new Store(arithmetic);
    const pre = stageById(arithmetic, "pre-inference");

    const lit = theNode(pre, "Lit(Int(10))");
    expect(lit.type).toBe("_"); // local type is a hole pre-inference
    // Resolves to the literal's singleton type, which prints as `10`.
    expect(store.resolvedTypesFor("pre-inference", lit.nodeId)).toEqual(["10"]);

    const lambda = theNode(pre, "Lambda(__arg_tuple_0)");
    expect(lambda.type).toBe("(_ ⇒ _)"); // a function-shaped hole
    expect(store.resolvedTypesFor("pre-inference", lambda.nodeId)).toEqual([
      "((1, Int) ⇒ Int)",
    ]);
  });

  it("polymorphic: a monomorphized hole resolves to the downstream type *set*", () => {
    const store = new Store(polymorphic);
    const pre = stageById(polymorphic, "pre-inference");

    // The `(x, x)` body: one pre-inference Tuple, two specialized clones.
    const tuple = theNode(pre, "Tuple");
    expect(tuple.type).toBe("_");
    // The Int specialization comes from `dup(1)`, so its element type is that
    // literal's singleton; `dup(2 == 2)`'s operand is a comparison, not a
    // literal, so the Bool specialization stays `(Bool, Bool)`.
    expect(sorted(store.resolvedTypesFor("pre-inference", tuple.nodeId))).toEqual(
      sorted(["(1, 1)", "(Bool, Bool)"]),
    );

    // The `dup` lambda fans out to two specialized function types.
    const lambda = theNode(pre, "Lambda(x)");
    expect(sorted(store.resolvedTypesFor("pre-inference", lambda.nodeId))).toEqual(
      sorted(["(Int ⇒ (1, 1))", "(Bool ⇒ (Bool, Bool))"]),
    );
  });

  it("the typed stages do not stitch (they already carry real types)", () => {
    const store = new Store(arithmetic);
    for (const stageId of ["post-inference", "post-desugar"]) {
      const stage = stageById(arithmetic, stageId);
      for (const node of allNodes(stage.ir)) {
        expect(store.resolvedTypesFor(stageId, node.nodeId)).toEqual([]);
      }
    }
  });
});

describe("T2: cross-pane resolution (setSelection -> getResolved)", () => {
  it("a node click highlights its identity twin in the downstream panes + a source span", () => {
    const store = new Store(arithmetic);
    const pre = stageById(arithmetic, "pre-inference");
    const lit = theNode(pre, "Lit(Int(10))"); // shared id (identity) across stages

    store.setSelection({ kind: "node", stageId: "pre-inference", nodeId: lit.nodeId });
    const { result, primaryByStage } = store.getResolved();

    expect(result.highlightsByStage.get("pre-inference")!.has(lit.nodeId)).toBe(true);
    // Identity: the same NodeId is highlighted in both downstream panes.
    expect(result.highlightsByStage.get("post-inference")!.has(lit.nodeId)).toBe(true);
    expect(result.highlightsByStage.get("post-desugar")!.has(lit.nodeId)).toBe(true);
    expect(primaryByStage.get("pre-inference")).toBe(lit.nodeId);
    // Projects to the literal's source span.
    expect(result.sourceSpans).toContainEqual(lit.span);
  });

  it("a mono-fan-out node click highlights every downstream clone", () => {
    const store = new Store(polymorphic);
    const pre = stageById(polymorphic, "pre-inference");
    const lambda = theNode(pre, "Lambda(x)");

    store.setSelection({ kind: "node", stageId: "pre-inference", nodeId: lambda.nodeId });
    const downstream = store.getResolved().result.highlightsByStage.get("post-inference")!;
    // Two specializations -> at least two distinct downstream nodes.
    expect(downstream.size).toBeGreaterThanOrEqual(2);
  });

  it("an inline-fan-out node click reaches the post-desugar copies (window 2)", () => {
    // udf_fanout: a scalar UDF called at two sites at the same type — inline
    // duplicates its body, and the post-inference -> post-desugar paneLinks
    // window carries the (copy, origin) edges (RT-3b at the store level).
    const window2 = udfFanout.paneLinks.find(
      (l) => l.from === "post-inference" && l.to === "post-desugar",
    )!;
    // A genuine (non-self) fan-out edge: origin !== copy.
    const fanout = window2.edges.find(([u, d]) => u !== d)!;
    expect(fanout).toBeDefined();

    const store = new Store(udfFanout);
    const [origin, copy] = fanout;
    store.setSelection({ kind: "node", stageId: "post-inference", nodeId: origin });
    const downstream = store.getResolved().result.highlightsByStage.get("post-desugar")!;
    expect(downstream.has(copy)).toBe(true);
  });

  it("a source click seeds each stage's tightest node (all panes light up)", () => {
    const store = new Store(arithmetic);
    const pre = stageById(arithmetic, "pre-inference");
    const lit = theNode(pre, "Lit(Int(10))");

    store.setSelection({ kind: "source", byteOffset: lit.span!.start });
    const { result, primaryByStage } = store.getResolved();
    for (const stageId of STAGE_IDS) {
      expect(result.highlightsByStage.get(stageId)!.size).toBeGreaterThan(0);
      expect(primaryByStage.get(stageId)).not.toBeNull();
    }
  });

  it("clearing the selection empties the resolved state", () => {
    const store = new Store(arithmetic);
    const pre = stageById(arithmetic, "pre-inference");
    store.setSelection({
      kind: "node",
      stageId: "pre-inference",
      nodeId: theNode(pre, "Lit(Int(10))").nodeId,
    });
    store.setSelection(null);
    const { result } = store.getResolved();
    expect(result.sourceSpans).toEqual([]);
    expect(result.highlightsByStage.size).toBe(0);
  });
});
