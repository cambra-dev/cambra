// Tests for the runtime wire-shape validator (schema 3). Every real fixture
// must validate (they are the source of truth for the shape); deliberately-
// broken objects must throw with a path-naming message.

import { describe, expect, it } from "vitest";

import { SCHEMA_VERSION, validateSnapshot } from "./wireValidate";

import arithmeticJson from "./__fixtures__/arithmetic.snapshot.json";
import polymorphicJson from "./__fixtures__/polymorphic.snapshot.json";
import listMinJson from "./__fixtures__/list_min.snapshot.json";
import failedJson from "./__fixtures__/failed.snapshot.json";
import udfFanoutJson from "./__fixtures__/udf_fanout.snapshot.json";
import txnMultiReadJson from "./__fixtures__/txn_multi_read.snapshot.json";
import mutationLoopJson from "./__fixtures__/mutation_loop.snapshot.json";
import deferLiftJson from "./__fixtures__/defer_lift.snapshot.json";

describe("validateSnapshot: real fixtures", () => {
  for (const [name, json] of [
    ["arithmetic", arithmeticJson],
    ["polymorphic", polymorphicJson],
    ["list_min", listMinJson],
    ["failed", failedJson],
    ["udf_fanout", udfFanoutJson],
    ["txn_multi_read", txnMultiReadJson],
    ["mutation_loop", mutationLoopJson],
    ["defer_lift", deferLiftJson],
  ] as const) {
    it(`${name} validates and round-trips identity`, () => {
      const snap = validateSnapshot(json);
      expect(snap).toBe(json);
      expect(snap.meta.schema).toBe(SCHEMA_VERSION);
    });
  }

  it("the failed (degraded) fixture validates with empty stages", () => {
    const snap = validateSnapshot(failedJson);
    expect(snap.meta.snapshotKind).toBe("failed");
    expect(snap.stages).toEqual([]);
    expect(snap.paneLinks).toEqual([]);
    expect(snap.diagnostics.length).toBeGreaterThan(0);
  });
});

describe("validateSnapshot: rejects malformed payloads with a path", () => {
  // A minimal valid *degraded* snapshot we can mutate per case (a successful
  // one needs the full three-stage shape — see minimalSuccess()).
  const minimalDegraded = (): Record<string, unknown> => ({
    source: { name: "x.chl", text: "1" },
    definitions: [],
    scopes: [],
    diagnostics: [],
    meta: { tick: null, snapshotKind: "failed", schema: SCHEMA_VERSION },
    stages: [],
    paneLinks: [],
  });

  // A minimal valid *successful* snapshot: the exact three stages + two
  // windows the schema-3 contract requires. Every stage's ir is `minimalNode`
  // (nodeId 0), so the (empty) paneLinks trivially satisfy endpoint liveness.
  const minimalNode = (): Record<string, unknown> => ({
    label: "Lit(Int(1))",
    type: "_",
    annotations: [],
    nodeId: 0,
    span: null,
    rewritten: null,
    tiling: null,
    children: [],
  });
  const minimalSuccess = (): Record<string, unknown> => ({
    source: { name: "x.chl", text: "1" },
    definitions: [],
    scopes: [],
    diagnostics: [],
    meta: { tick: null, snapshotKind: "post-inference", schema: SCHEMA_VERSION },
    stages: [
      { id: "pre-inference", label: "IR (PRE-INFERENCE)", kind: "holes" },
      { id: "post-inference", label: "IR (POST-INFERENCE)", kind: "typed" },
      { id: "post-desugar", label: "IR (POST-DESUGAR)", kind: "typed" },
    ].map((s) => ({ ...s, ir: minimalNode(), spanIndex: [] })),
    paneLinks: [
      { from: "pre-inference", to: "post-inference", edges: [] },
      { from: "post-inference", to: "post-desugar", edges: [] },
    ],
  });

  it("accepts the minimal valid degraded and successful snapshots", () => {
    expect(() => validateSnapshot(minimalDegraded())).not.toThrow();
    expect(() => validateSnapshot(minimalSuccess())).not.toThrow();
  });

  it("throws naming meta.schema when it is missing or not the supported version", () => {
    const missing = minimalDegraded();
    delete (missing.meta as Record<string, unknown>).schema;
    expect(() => validateSnapshot(missing)).toThrow(/meta\.schema/);

    const stale = minimalDegraded();
    (stale.meta as Record<string, unknown>).schema = 2;
    expect(() => validateSnapshot(stale)).toThrow(/meta\.schema.*exactly 3/);
  });

  it("throws on the retired schema-1 top-level ir / spanIndex", () => {
    const withIr = minimalDegraded();
    withIr.ir = null;
    expect(() => validateSnapshot(withIr)).toThrow(/snapshot\.ir.*absent/);

    const withIndex = minimalDegraded();
    withIndex.spanIndex = [];
    expect(() => validateSnapshot(withIndex)).toThrow(/snapshot\.spanIndex.*absent/);
  });

  it("throws when a successful payload's stages deviate from the pinned list", () => {
    const wrongOrder = minimalSuccess();
    (wrongOrder.stages as { id: string }[]).reverse();
    expect(() => validateSnapshot(wrongOrder)).toThrow(/stages.*in order/);

    const wrongKind = minimalSuccess();
    (wrongKind.stages as { kind: string }[])[0].kind = "pre-inference"; // the schema-1 value
    expect(() => validateSnapshot(wrongKind)).toThrow(/stages.*kinds/);

    const wrongWindows = minimalSuccess();
    (wrongWindows.paneLinks as unknown[]).pop();
    expect(() => validateSnapshot(wrongWindows)).toThrow(/paneLinks.*windows/);
  });

  it("throws when a degraded payload carries stages", () => {
    const bad = minimalDegraded();
    bad.stages = (minimalSuccess().stages as unknown[]).slice();
    expect(() => validateSnapshot(bad)).toThrow(/stages.*empty on a degraded/);
  });

  it("throws naming a node type field when mistyped", () => {
    const bad = minimalSuccess();
    ((bad.stages as { ir: Record<string, unknown> }[])[0].ir as Record<string, unknown>).type = 7;
    expect(() => validateSnapshot(bad)).toThrow(/stages\[0\]\.ir\.type/);
  });

  it("throws on a rewrite-tag via outside the pinned vocabulary", () => {
    const bad = minimalSuccess();
    ((bad.stages as { ir: Record<string, unknown> }[])[0].ir as Record<string, unknown>).rewritten =
      { via: "Planning", nature: "expansion", label: "x" }; // a pass not yet on the wire
    expect(() => validateSnapshot(bad)).toThrow(/rewritten\.via/);
  });

  it("throws on a rewrite-tag nature outside the pinned vocabulary", () => {
    const bad = minimalSuccess();
    ((bad.stages as { ir: Record<string, unknown> }[])[0].ir as Record<string, unknown>).rewritten =
      { via: "Mono", nature: "Expansion", label: "x" }; // must be lowercase
    expect(() => validateSnapshot(bad)).toThrow(/rewritten\.nature/);
  });

  it("throws when a paneLinks edge is not a [number, number] pair", () => {
    const bad = minimalSuccess();
    (bad.paneLinks as { edges: unknown[] }[])[0].edges = [[1]];
    expect(() => validateSnapshot(bad)).toThrow(/paneLinks\[0\]\.edges\[0\].*pair/);
  });

  it("throws naming source.text when missing", () => {
    const bad = minimalDegraded();
    delete (bad.source as Record<string, unknown>).text;
    expect(() => validateSnapshot(bad)).toThrow(/source\.text/);
  });
});
