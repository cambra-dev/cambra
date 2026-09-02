// Tests for the runtime wire-shape validator. Every real fixture
// must validate (they are the source of truth for the shape); deliberately-
// broken objects must throw with a path-naming message.

import { describe, expect, it } from "vitest";

import { PANE_IDS, SCHEMA_VERSION, validateSnapshot } from "./wireValidate";

import arithmeticJson from "./__fixtures__/arithmetic.snapshot.json";
import polymorphicJson from "./__fixtures__/polymorphic.snapshot.json";
import listMinJson from "./__fixtures__/list_min.snapshot.json";
import failedJson from "./__fixtures__/failed.snapshot.json";
import deferLiftJson from "./__fixtures__/defer_lift.snapshot.json";

describe("validateSnapshot: real fixtures", () => {
  for (const [name, json] of [
    ["arithmetic", arithmeticJson],
    ["polymorphic", polymorphicJson],
    ["list_min", listMinJson],
    ["failed", failedJson],
    ["defer_lift", deferLiftJson],
  ] as const) {
    it(`${name} validates and round-trips identity`, () => {
      const snap = validateSnapshot(json);
      expect(snap).toBe(json);
      expect(snap.meta.schema).toBe(SCHEMA_VERSION);
    });
  }

  it("the failed (degraded) fixture validates with empty panes", () => {
    const snap = validateSnapshot(failedJson);
    expect(snap.meta.payloadKind).toBe("failed");
    expect(snap.panes).toEqual([]);
    expect(snap.paneLinks).toEqual([]);
    expect(snap.diagnostics.length).toBeGreaterThan(0);
  });
});

describe("validateSnapshot: rejects malformed payloads with a path", () => {
  // A minimal valid *degraded* snapshot we can mutate per case (a successful
  // one needs the full pane shape — see minimalSuccess()).
  const minimalDegraded = (): Record<string, unknown> => ({
    source: { name: "x.chl", text: "1" },
    definitions: [],
    diagnostics: [],
    meta: { payloadKind: "failed", schema: SCHEMA_VERSION },
    panes: [],
    paneLinks: [],
  });

  // A minimal valid *successful* snapshot: the exact panes and windows the
  // pinned contract requires, built from `PANE_IDS` so a pane added upstream
  // fails the validator's own pin rather than this fixture's spelling. Every
  // pane's table is one `minimalNode` (nodeId 0) at `root`, so the (empty)
  // paneLinks trivially satisfy endpoint liveness.
  const minimalNode = (): Record<string, unknown> => ({
    label: "Lit(Int(1))",
    nodeId: 0,
    spans: [],
    rewritten: null,
    type: "_",
    children: [],
  });
  const minimalSuccess = (): Record<string, unknown> => ({
    source: { name: "x.chl", text: "1" },
    definitions: [],
    diagnostics: [],
    meta: { payloadKind: "program", schema: SCHEMA_VERSION },
    panes: PANE_IDS.map((id, i) => ({
      id,
      label: `IR (${id.toUpperCase()})`,
      kind: i === 0 ? "holes" : "typed",
      root: 0,
      nodes: [minimalNode()],
    })),
    paneLinks: PANE_IDS.slice(1).map((to, i) => ({
      from: PANE_IDS[i],
      to,
      edges: [],
    })),
  });

  // The nodes array of a `minimalSuccess()` pane, for the per-node cases below.
  const paneNodes = (bad: Record<string, unknown>, i = 0): Record<string, unknown>[] =>
    (bad.panes as { nodes: Record<string, unknown>[] }[])[i].nodes;

  it("accepts the minimal valid degraded and successful snapshots", () => {
    expect(() => validateSnapshot(minimalDegraded())).not.toThrow();
    expect(() => validateSnapshot(minimalSuccess())).not.toThrow();
  });

  it("throws naming meta.schema when it is missing or not the supported version", () => {
    const missing = minimalDegraded();
    delete (missing.meta as Record<string, unknown>).schema;
    expect(() => validateSnapshot(missing)).toThrow(/meta\.schema/);

    const stale = minimalDegraded();
    (stale.meta as Record<string, unknown>).schema = SCHEMA_VERSION - 1;
    expect(() => validateSnapshot(stale)).toThrow(
      new RegExp(`meta\\.schema.*exactly ${SCHEMA_VERSION}`),
    );
  });

  it("throws on the retired top-level ir tree", () => {
    const withIr = minimalDegraded();
    withIr.ir = null;
    expect(() => validateSnapshot(withIr)).toThrow(/snapshot\.ir.*absent/);
  });

  it("throws when a payload omits paneLinks", () => {
    const bad = minimalSuccess();
    delete bad.paneLinks;
    expect(() => validateSnapshot(bad)).toThrow(/paneLinks.*present/);
  });

  it("throws when a successful payload's panes deviate from the pinned list", () => {
    const wrongOrder = minimalSuccess();
    (wrongOrder.panes as { id: string }[]).reverse();
    expect(() => validateSnapshot(wrongOrder)).toThrow(/panes.*in order/);

    const wrongKind = minimalSuccess();
    (wrongKind.panes as { kind: string }[])[0].kind = "pre-inference"; // a pane id, not a kind
    expect(() => validateSnapshot(wrongKind)).toThrow(/panes.*kind/);

    const wrongWindows = minimalSuccess();
    (wrongWindows.paneLinks as unknown[]).pop();
    expect(() => validateSnapshot(wrongWindows)).toThrow(/paneLinks.*windows/);
  });

  it("throws when a degraded payload carries panes", () => {
    const bad = minimalDegraded();
    bad.panes = (minimalSuccess().panes as unknown[]).slice();
    expect(() => validateSnapshot(bad)).toThrow(/panes.*empty on a degraded/);
  });

  it("throws naming a node type field when mistyped", () => {
    const bad = minimalSuccess();
    paneNodes(bad)[0].type = 7;
    expect(() => validateSnapshot(bad)).toThrow(/panes\[0\]\.nodes\[0\]\.type/);
  });

  it("throws on the node fields the payload no longer carries", () => {
    // `annotations` and `tiling` were the renderer's tile-producer fields;
    // `typeKind` and `predicateRefs` rode beside the rendered type for a
    // consumer that read neither; `span` became `spans`. Their absence is the
    // contract, and a payload carrying any of them is an older wire.
    for (const [field, value] of [
      ["annotations", []],
      ["tiling", null],
      ["typeKind", "hole"],
      ["predicateRefs", []],
      ["span", null],
    ] as const) {
      const bad = minimalSuccess();
      paneNodes(bad)[0][field] = value;
      expect(() => validateSnapshot(bad)).toThrow(
        new RegExp(`nodes\\[0\\]\\.${field}.*absent`),
      );
    }
  });

  it("throws when a node's spans repeat one span or are not narrowest first", () => {
    const repeated = minimalSuccess();
    paneNodes(repeated)[0].spans = [
      { start: 0, end: 1 },
      { start: 0, end: 1 },
    ];
    expect(() => validateSnapshot(repeated)).toThrow(
      /nodes\[0\]\.spans\[1\].*not already on this node/,
    );

    const widest = minimalSuccess();
    paneNodes(widest)[0].spans = [
      { start: 0, end: 9 },
      { start: 2, end: 3 },
    ];
    expect(() => validateSnapshot(widest)).toThrow(/nodes\[0\]\.spans\[1\].*narrowest first/);
  });

  it("throws when a node names one predicate under two edges", () => {
    // The slot walk upstream reaches a `Lambda`'s own type and its binder's
    // type, which are the same `Type`, so this is the shape a missing dedup
    // ships.
    const bad = minimalSuccess();
    paneNodes(bad)[0].children = [
      { id: 0, predicate: true },
      { id: 0, predicate: true },
    ];
    expect(() => validateSnapshot(bad)).toThrow(
      /nodes\[0\]\.children\[1\]\.id.*not already named by this node/,
    );
  });

  it("throws when the payload carries a retired top-level field", () => {
    for (const field of ["scopes", "spanIndex"] as const) {
      const bad = minimalDegraded();
      bad[field] = [];
      expect(() => validateSnapshot(bad)).toThrow(new RegExp(`${field}.*absent`));
    }

    const withTick = minimalDegraded();
    (withTick.meta as Record<string, unknown>).tick = null;
    expect(() => validateSnapshot(withTick)).toThrow(/meta\.tick.*absent/);
  });

  it("throws when meta.payloadKind is a pane id rather than a document kind", () => {
    const bad = minimalSuccess();
    (bad.meta as Record<string, unknown>).payloadKind = "post-inference";
    expect(() => validateSnapshot(bad)).toThrow(/meta\.payloadKind.*program.*failed/);
  });

  it("throws when a pane still ships a nested `ir` tree or a span table", () => {
    const bad = minimalSuccess();
    (bad.panes as Record<string, unknown>[])[0].ir = minimalNode();
    expect(() => validateSnapshot(bad)).toThrow(/panes\[0\]\.ir.*absent/);

    const withIndex = minimalSuccess();
    (withIndex.panes as Record<string, unknown>[])[0].spanIndex = [];
    expect(() => validateSnapshot(withIndex)).toThrow(/panes\[0\]\.spanIndex.*absent/);
  });

  it("throws when a child edge names an id the pane's table does not hold", () => {
    const bad = minimalSuccess();
    paneNodes(bad)[0].children = [{ id: 99, predicate: false }];
    expect(() => validateSnapshot(bad)).toThrow(
      /panes\[0\]\.nodes\[0\]\.children\[0\]\.id.*present in this pane/,
    );
  });

  it("throws when `root` names an id the pane's table does not hold", () => {
    const bad = minimalSuccess();
    (bad.panes as Record<string, unknown>[])[0].root = 99;
    expect(() => validateSnapshot(bad)).toThrow(/panes\[0\]\.root.*present in this pane/);
  });

  it("throws when a node id appears twice in one pane's table", () => {
    const bad = minimalSuccess();
    paneNodes(bad).push(minimalNode());
    expect(() => validateSnapshot(bad)).toThrow(
      /panes\[0\]\.nodes\[1\]\.nodeId.*not already in the table/,
    );
  });

  it("throws when a child edge carries no `predicate` flag", () => {
    const bad = minimalSuccess();
    paneNodes(bad)[0].children = [{ id: 0 }];
    expect(() => validateSnapshot(bad)).toThrow(
      /panes\[0\]\.nodes\[0\]\.children\[0\]\.predicate/,
    );
  });

  it("throws on a rewrite-tag via outside the pinned vocabulary", () => {
    const bad = minimalSuccess();
    // `Uniquify` is a declared compiler phase that records nothing, so it is
    // deliberately absent from the pinned list: a phase reaching the wire for
    // the first time is exactly what this must catch.
    paneNodes(bad)[0].rewritten = { via: "Uniquify", nature: "expansion", label: "x" };
    expect(() => validateSnapshot(bad)).toThrow(/rewritten\.via/);
  });

  it("throws on a rewrite-tag nature outside the pinned vocabulary", () => {
    const bad = minimalSuccess();
    // A pinned `via`, so this reaches the nature check rather than failing
    // ahead of it. The nature must be lowercase.
    paneNodes(bad)[0].rewritten = { via: "Infer", nature: "Expansion", label: "x" };
    expect(() => validateSnapshot(bad)).toThrow(/rewritten\.nature/);
  });

  it("throws when a paneLinks edge is not a [number, number] pair", () => {
    const bad = minimalSuccess();
    (bad.paneLinks as { edges: unknown[] }[])[0].edges = [[1, 2, ["descends"]]];
    expect(() => validateSnapshot(bad)).toThrow(/paneLinks\[0\]\.edges\[0\].*pair/);
  });

  it("throws naming source.text when missing", () => {
    const bad = minimalDegraded();
    delete (bad.source as Record<string, unknown>).text;
    expect(() => validateSnapshot(bad)).toThrow(/source\.text/);
  });
});
