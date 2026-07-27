# Golden snapshot fixtures

Real `/api/snapshot` payloads (wire **schema 4**) emitted by the
`cambra-inspector` backend, used by `store.test.ts` to test the frontend's
derived logic (the B5 hole→type stitch, cross-pane resolution) **and** to guard
the wire-shape contract: if the Rust payload drifts from the TypeScript wire
types in `../types.ts`, these tests break. The corpus (fixture ↔ example
mapping, plus the per-fixture retention spec) lives in
`../../../scripts/fixtures.manifest`, shared by `regen-fixtures.sh`, the ci.sh
drift gate, and the cargo golden tests (`cambra-inspector/tests/goldens.rs`).

A successful **live** payload carries three stages —
`pre-inference` (kind `holes`), `post-inference` (kind `typed`, the anchor),
`post-desugar` (kind `typed`) — and two `paneLinks` windows
(`pre-inference → post-inference`: mono fan-out;
`post-inference → post-desugar`: inline fan-out). There is no top-level
`ir`/`spanIndex` (schema 1's aliases are retired).

## Schema 4: no `spanIndex` on the wire

Schema 4 removed the per-stage `spanIndex` array. It was pure derived data — a
pre-order walk of the stage tree emitting one `{span, nodeId}` per node origin
span — and every node already carries its origin span inline on `ir` (the
`span` field). The frontend rebuilds the index on load from the stage tree
(`buildSpanIndex` in `../indices.ts`, mirroring Rust's `SpanIndex::build`). This
halved the span-churn the byte-exact corpus pinned.

## Retention: full vs slimmed fixtures

Each manifest row may carry an optional retention spec —
`<fixture> <example> [panes=<comma-list>|all] [links=all|none]`, defaulting to
`panes=all links=all` (the full live wire). Slimming trims what the byte-exact
corpus pins on the big, volatile programs; it **never** changes the live wire
(the served payload and a flagless `--dump-snapshot` are always full). Two
relaxations, both fixture-only:

- `panes=a,b` retains only those pipeline stages (a subset, in pipeline order);
- `links=none` **omits** `paneLinks` entirely (the field is dropped, not shipped
  as an empty array — an empty array would falsely claim the wire has no edges).

The fixture loader (`fixture()` in `helpers.ts`) and `wireValidate.test.ts`
validate slimmed fixtures under `validateSnapshot(json, { fixtureSlimming: true })`
(the TS twin of Rust's `FixtureContext::Fixture`), which accepts a pane subset
and an absent `paneLinks`. Production callers pass no options and get the strict
live contract, so a live payload that drops a pane or its links still fails.

**Full (all panes + links):** `arithmetic`, `polymorphic`, `list_min`,
`udf_fanout`, `defer_lift`, and the degraded `failed` payload. `list_min` and
`arithmetic` are the deliberate end-to-end canaries pinning the whole wire
byte-for-byte; the web vitest suite imports
`arithmetic`/`polymorphic`/`udf_fanout`/`list_min`/`failed` and walks their stage
trees + `paneLinks`, so those must stay full.

**Slimmed (`panes=post-inference,post-desugar links=none`):** `txn_multi_read`
and `mutation_loop` — the two largest fixtures (heavy desugar synthesis;
`paneLinks` is ~4 lines/edge with super-linear growth: 813 edges over 39×77 nodes
in `txn_multi_read`'s desugar window, and stages are ~73% of its bytes). They pin
only the panes they uniquely exercise; `goldens.rs`
(`txn_multi_read_produces_dense_desugar_window` /
`mutation_loop_produces_dense_desugar_window`) asserts the dense-window fan-out
structurally over a full dump, replacing the pinned edge bytes.

- `arithmetic.snapshot.json` — `examples/arithmetic.chl`. Exercises the
  **identity** stitch (`_ → Int`, a hole resolved by the same NodeId downstream).
- `polymorphic.snapshot.json` — `examples/polymorphic.chl`. A let-polymorphic
  `dup` used at two types, so monomorphization fans out: exercises the
  **type-set** stitch (`_ → (Int, Int) | (Bool, Bool)`) and non-empty
  window-1 `paneLinks`.
- `list_min.snapshot.json` — `examples/list_min.chl` (just `[1, 2, 3, 4]`). The
  minimal cross-link anchor for the jsdom view-integration test
  (`src/views.dom.test.ts`): every node carries a `span` (from which the
  frontend rebuilds the index), identity-linked across the stages, so a
  node/source selection lights up every pane. Pre-inference holes (type `"_"`)
  resolve to `Int` downstream.
- `failed.snapshot.json` — `examples/type_error.chl` (`1 and 2`). The **degraded**
  payload: a program that fails to compile, so `stages`/`paneLinks` are empty,
  `meta.snapshotKind` is `"failed"`, and `diagnostics` is non-empty. Drives the
  degraded-render test (`main.test.ts`) and is validated by `wireValidate.test.ts`,
  proving the API can represent and the frontend can parse a failed compile.
- `udf_fanout.snapshot.json` — `examples/udf_fanout.chl`. A scalar UDF called at
  two sites at the same type: inline fan-out, non-empty **window-2**
  `paneLinks` (`post-inference → post-desugar`), `Derived(Inline)` provenance.
- `txn_multi_read.snapshot.json` — `examples/txn_multi_read.chl`. `with begin():`
  blocks reading a `Mut(_, Txn)` store at two sites (the transact-phase
  substitution corpus program). The largest fixture (heavy desugar synthesis).
- `mutation_loop.snapshot.json` — `examples/mutation_loop.chl`. A mutable
  accumulator loop reading the accumulator at two sites (the letrec-phase
  substitution corpus program).
- `defer_lift.snapshot.json` — `examples/defer_lift.chl`. A UDF that returns a
  defer channel, so inlining produces the `try_lift_defer` shape (the lifted
  feed head keeps its NodeId, preserving its source span).

Each IR node carries its type in the first-class `type` field (e.g. `"Int"`,
`"_"`), not the old positional `annotations[0]`.

## Regenerating

```bash
cambra-inspector/scripts/regen-fixtures.sh   # from the cambra/ repo root
```

This wraps the per-example `--dump-snapshot` dumps (one-shot — it does **not**
start the never-exiting HTTP server) and pretty-prints each fixture for
reviewable diffs. Regenerate after any backend change to the snapshot schema and
commit the result; CI fails if the committed fixtures drift from the backend
(the `ci_fixtures` gate in `ci.sh` regenerates to a temp dir and diffs), and the
cargo golden test compares each committed fixture against a fresh dump.
`store.test.ts` keys its assertions on node **labels/types**, not raw NodeIds, so
ordinary id churn does not require touching the tests — but a shape change will,
by design (and `wireValidate.ts` enforces the shape).

There is a second, **independent** ratchet on the Rust side: `census_ratchet`
in `src/ccl/context.rs` pins per-category node counts (source-attribution
kinds) per pane for its own corpus. It is unrelated to these wire fixtures but
often moved by the same provenance-affecting change — its re-bless procedure
lives in its doc comment. If a compiler change moves one, check the other.
