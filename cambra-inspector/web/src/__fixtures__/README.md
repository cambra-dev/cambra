# Golden snapshot fixtures

Real `/api/snapshot` payloads emitted by the `cambra` backend, used by
`store.test.ts` to test the frontend's derived logic (the B5 hole→type stitch,
cross-pane resolution) **and** to guard the wire-shape contract: if the Rust
payload drifts from the TypeScript wire types in `../types.ts`, these tests
break. The corpus lives in `../../../scripts/fixtures.manifest`: which program each
fixture is dumped from, and a comment per row saying what that row pins. It is
shared by `regen-fixtures.sh`, the ci.sh drift gate, and the cargo golden tests
(`tests/inspector_goldens.rs`), so a row and the thing it describes move
together.

Every fixture is the whole live wire. A program too large or too volatile to pin
byte-for-byte carries no fixture at all and a structural assertion over a fresh
dump instead, in `tests/inspector_goldens.rs`.

A successful **live** payload carries one entry of `panes` per declared pane, in
pipeline order — `pre-inference` (kind `holes`) then `post-inference` (kind
`typed`, the anchor), `post-channelize`, `post-as-of-read`, `post-lambda-elim`
and `post-planning` (all `typed`) — and one `paneLinks` window per adjacent pair,
so `paneLinks` is always one shorter than `panes`. The pane set is the compiler's
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

A re-bless pins more than the shape, and every diff in one has to be classified
before it is committed: see
[The golden fixtures](../../../CLAUDE.md#the-golden-fixtures).
