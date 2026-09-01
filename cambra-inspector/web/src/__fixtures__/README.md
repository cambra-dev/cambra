# Golden snapshot fixtures

Real `/api/snapshot` payloads emitted by the `cambra` backend, used by
`store.test.ts` to test the frontend's derived logic (the B5 hole→type stitch,
cross-pane resolution) **and** to guard the wire-shape contract: if the Rust
payload drifts from the TypeScript wire types in `../types.ts`, these tests
break. The corpus lives in `../../../scripts/fixtures.manifest`: which program
each fixture is dumped from, and a comment per row saying what that row pins. It
is shared by `regen-fixtures.sh`, the ci.sh drift gate, and the cargo golden
tests (`tests/inspector_goldens.rs`), so a row and the thing it describes move
together.

Every fixture is the full live wire. A program too large or too volatile to pin
byte-for-byte gets no fixture at all and a structural assertion over a fresh dump
instead, in `tests/inspector_goldens.rs`.

A successful **live** payload carries one entry of `panes` per declared pane, in
pipeline order — `pre-inference` (kind `holes`), then `post-inference` (kind
`typed`, the anchor), `post-channelize`, `post-as-of-read`, `post-lambda-elim`
and `post-planning` (all `typed`), then `post-conversion` (kind `operators`) —
and one `paneLinks` window per adjacent pair, so `paneLinks` is always one
shorter than `panes`. The pane set is the compiler's `PANES` table;
`wireValidate.ts` pins it rather than reading it, so an added pane fails the
validator instead of passing silently. There is no top-level `ir`/`spanIndex`
(the earlier aliases are retired).

## What a pane ships

`nodes` holds each node of that pane exactly once, and `roots` names the ids its
walk starts from. `kind` is the discriminant for which shape `nodes` holds.

A **tree pane** (`holes`, `typed`) holds expression nodes, in first-visit
pre-order, and names exactly one root. A child is `{ edge, id, predicate }` — the
id names an entry of the same table, so a node reached from several places is one
entry that several edges name. A refinement predicate riding a type slot is a
node like any other, reached under a `where.N`-labelled child edge instead of a
positional index; `predicate: true` on the edge is what distinguishes a subtree
inside a type from an operand, and the label is for display. Each node carries
its type as a rendered string in `type` (`"Int"`, `"_"`).

The **operator pane** (`operators`) holds the dataflow graph, in conversion
order, and names several roots — a sink per compiled output and a fan input per
share point, which are the nodes nothing owns. A node carries `role`
(`operator`, `source`, `sink`), a `tiling` for an operator and none for a
boundary, and `inputs`: `{ role, kind, deferred, id }`. An edge's `kind` is
`value` for an exclusively owned input, `share` for one several consumers may
reach, `feedback` for a share that closes a cycle. These are construction edges —
which operator holds which. Runtime dataflow follows `get` and `notify`, a
different relation, and nothing on this wire says the two coincide.

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
