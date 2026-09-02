# Golden snapshot fixtures

Real `/api/snapshot` payloads emitted by the
`cambra-inspector` backend, used by `store.test.ts` to test the frontend's
derived logic (the B5 hole→type stitch, cross-pane resolution) **and** to guard
the wire-shape contract: if the Rust payload drifts from the TypeScript wire
types in `../types.ts`, these tests break. The corpus (fixture ↔ program
mapping) lives in `../../../scripts/fixtures.manifest`, shared by
`regen-fixtures.sh`, the ci.sh drift gate, and the cargo golden tests
(`tests/inspector_goldens.rs`).

A successful payload carries one entry of `panes` per declared pane, in pipeline
order — `pre-inference` (kind `holes`) then `post-inference` (kind `typed`, the
anchor), `post-channelize`, `post-as-of-read`, `post-lambda-elim` and
`post-planning` (all `typed`) — and one `paneLinks` window per adjacent pair, so
`paneLinks` is always one shorter than `panes`. The pane set is the compiler's
`PANES` table; `wireValidate.ts` pins it rather than reading it, so an added pane
fails the validator instead of passing silently. There is no top-level
`ir`/`spanIndex` (the earlier aliases are retired).

A pane ships a **node table**: `nodes`, holding each node of that pane exactly
once in first-visit pre-order, and `root`, the id its walk starts from. A child
is `{ edge, id, predicate }` — the id names an entry of the same table, so a node
reached from several places is one entry that several edges name.

A refinement predicate riding a type slot is a node like any other, reached under
a `where.N`-labelled child edge instead of a positional index. `predicate: true`
on the edge is what distinguishes a subtree inside a type from an operand; the
edge label is for display.

- `arithmetic.snapshot.json` — `tests/programs/udf_closure/`. Exercises the
  **identity** stitch (`_ → Int`, a hole resolved by the same NodeId downstream).
- `polymorphic.snapshot.json` — `tests/programs/polymorphic/`. A let-polymorphic
  `dup` applied at four sites, three at `Int` and one at `Bool`, so both
  duplication mechanisms fire: monomorphization fans out per type, and `inline`
  duplicates the `Int` specialization's body per call site with
  `Derived(Inline)` provenance. Exercises the **type-set** stitch
  (`_ → (Int, Int) | (Bool, Bool)`), a non-empty
  `pre-inference → post-inference` window, and a non-empty
  `post-inference → post-channelize` one.
- `list_min.snapshot.json` — `tests/programs/list_min/` (just `[1, 2, 3, 4]`). The
  minimal cross-link anchor for the jsdom view-integration test
  (`src/views.dom.test.ts`): every node carries its own `spans`,
  identity-linked across the panes, so a node/source selection lights
  up every pane. Pre-inference holes (type `"_"`) resolve to `Int` downstream.
- `failed.snapshot.json` — `tests/programs/type_error/` (`1 and 2`). The **degraded**
  payload: a program that fails to compile, so `panes`/`paneLinks` are empty,
  `meta.payloadKind` is `"failed"`, and `diagnostics` is non-empty. Drives the
  degraded-render test (`main.test.ts`) and is validated by `wireValidate.test.ts`,
  proving the API can represent and the frontend can parse a failed compile.
- `defer_lift.snapshot.json` — `tests/programs/defer_lift/`. A UDF that returns a
  defer channel, so inlining produces the `try_lift_defer` shape (the lifted
  feed head keeps its NodeId, preserving its source span). A loop feeds the
  returned channel a second time, so channelization also builds the two-site
  channel union.

Each node carries its type as a rendered string in `type` (e.g. `"Int"`, `"_"`),
and reaches a predicate riding one of its type slots through a `children` entry
marked `predicate: true`, naming an id in the same pane's table.

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
