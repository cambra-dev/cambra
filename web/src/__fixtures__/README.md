# Test payloads

The frontend's tests read real `/api/snapshot` payloads: the `--dump-snapshot`
output of every gallery program (`tests/programs/`). Vitest's global setup
(`dumps.ts`) dumps them before any test runs, by running `write_gallery_snapshots`
in `tests/it/inspector_wire.rs` through `cargo test`, into
`target/inspector-snapshots/`. A test reads one with `dumped("<program>")` from
`helpers.ts`, and `fixture` validates it against `wireValidate.ts`, so a payload
that drifts from the TypeScript wire types in `../types.ts` fails there.
`wireValidate.test.ts` validates every dumped program.

A successful **live** payload carries one entry of `panes` per declared pane, in
pipeline order — `pre-inference` (kind `holes`), then `post-inference` (kind
`typed`, the anchor), `post-channelize`, `post-lambda-elim`
and `post-planning` (all `typed`), then `post-conversion` (kind `operators`) —
and one `paneLinks` window per adjacent pair, so `paneLinks` is always one
shorter than `panes`. The pane set is the compiler's `PANES` table;
`wireValidate.ts` pins it rather than reading it, so an added pane fails the
validator instead of passing silently. There is no top-level `ir`/`spanIndex`
(the earlier aliases are retired).

## What a pane ships

`nodes` holds each node of that pane exactly once, and the pane's own walk-start
key names the ids a walk of it starts from. `kind` is the discriminant for which
shape `nodes` holds, and for which of the two keys the pane carries.

A **tree pane** (`holes`, `typed`) holds expression nodes, in first-visit
pre-order, and names its start under `root` — one id, since a tree has one by
construction. A child is `{ id, predicate }` — the id names an entry of the same
table, so a node reached from several places is one
entry that several edges name. A refinement predicate riding a type slot is a
node like any other, and `predicate: true` is what distinguishes a subtree
inside a type from an operand. The edge carries no label: the frontend derives a
value child's position from its index. Predicates stay on the wire because their
ids are endpoints of the pane links, and the tree pane draws no row for one —
the node's `type` already shows the predicate. Each node carries its type as a
rendered string in `type` (`"Int"`, `"_"`).

The **operator pane** (`operators`) holds the dataflow graph, in conversion
order, and names no walk start. A walk begins at the nodes no `value` edge
subscribes — a sink per compiled output and a fan input per share point —
which a consumer derives from `inputs`.
Every node is reachable from there following `value` edges alone, which is the
relation a consumer walks.

A node carries `role` (`operator`, `sink`), a `tiling` for an operator and none
for a sink, and `inputs`: `{ role, kind, deferred, subscribed }`. An
edge's `kind` is `value` for an exclusively owned input and `share` for one
several consumers may reach; `deferred` marks a `value` edge wired through a
`CycleSlot` after its consumer was constructed, which is when rather than how it
is held. An edge is a
subscription, stored on the consumer: `subscribed` names the operator it holds and
calls `get` on, so the relation runs against dataflow. `notify` runs the other
way.

## Dumping

`CAMBRA_SNAPSHOT_PROFILE` names the cargo profile `dumps.ts` dumps with, so CI
reuses the build its suite made; unset, it is the default test profile. A test
keys its assertions on what a payload means (pane ids, node labels, types), not
on `NodeId`s, which come from a process-global counter.

## The probe frame

`probe_frame.json` is one `/api/live` probe frame, built by
`a_probe_frame_matches_its_golden` in `src/inspector_model/frame.rs` from a
hand-built probe table rather than dumped from a program. Its `NodeId`s are
renumbered from 1 in the order the test minted them, and its keys are sorted, so
it is the same bytes in every process. Re-bless it with
`CAMBRA_BLESS=1 cargo test a_probe_frame_matches_its_golden`.
