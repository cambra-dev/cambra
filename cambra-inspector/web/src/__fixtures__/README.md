# Golden snapshot fixtures

Real `/api/snapshot` payloads (wire **schema 3**) emitted by the
`cambra-inspector` backend, used by `store.test.ts` to test the frontend's
derived logic (the B5 hole→type stitch, cross-pane resolution) **and** to guard
the wire-shape contract: if the Rust payload drifts from the TypeScript wire
types in `../types.ts`, these tests break. The corpus (fixture ↔ example
mapping) lives in `../../../scripts/fixtures.manifest`, shared by
`regen-fixtures.sh`, the ci.sh drift gate, and the cargo golden tests
(`cambra-inspector/tests/goldens.rs`).

A successful payload carries three stages —
`pre-inference` (kind `holes`), `post-inference` (kind `typed`, the anchor),
`post-desugar` (kind `typed`) — and two `paneLinks` windows
(`pre-inference → post-inference`: mono fan-out;
`post-inference → post-desugar`: inline fan-out). There is no top-level
`ir`/`spanIndex` (schema 1's aliases are retired).

- `arithmetic.snapshot.json` — `examples/arithmetic.chl`. Exercises the
  **identity** stitch (`_ → Int`, a hole resolved by the same NodeId downstream).
- `polymorphic.snapshot.json` — `examples/polymorphic.chl`. A let-polymorphic
  `dup` used at two types, so monomorphization fans out: exercises the
  **type-set** stitch (`_ → (Int, Int) | (Bool, Bool)`) and non-empty
  window-1 `paneLinks`.
- `list_min.snapshot.json` — `examples/list_min.chl` (just `[1, 2, 3, 4]`). The
  minimal cross-link anchor for the jsdom view-integration test
  (`src/views.dom.test.ts`): every node has both a `span` and a `spanIndex`
  entry, identity-linked across the stages, so a node/source selection lights
  up every pane. Pre-inference holes (type `"_"`) resolve to `Int` downstream.
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
