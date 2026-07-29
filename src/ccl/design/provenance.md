# Provenance & lineage — node identity and source attribution

This doc is the reference for how Cambra keeps an IR node's connection to the
source the user wrote, through a pipeline that otherwise loses it (spans dropped
at lowering, monomorphization cloning subtrees, inline fanning UDF bodies out,
channelize rewriting defers, lambda-elim synthesizing combinators, planning
fusing clauses).

**Status markers.** The substrate — the identity primitives, the lineage model,
the recorder, and the always-on lowering projection — is in tree. Everything a
**Planned** marker introduces is designed but not yet built: the passes' adoption
of the recorder, the pane-boundary folds, and the inspector's consumption of
them. A reader on `main` can tell the two apart by the marker alone; unmarked
prose describes code you can go read.

> The design of record — the full decision log, the collapse algorithm, the
> recorder mechanism, and the adoption sequencing — is the lineage-redesign doc
> under projects/program-inspector in the internal vault. This file summarizes
> the shipped shape; where the two disagree, that doc wins.

## The two identity primitives (`src/ccl/provenance.rs`)

- **`NodeId`** — a `Copy` newtype giving each IR expression node a stable,
  never-reused identity (its own atomic counter, distinct from `Uid`). It rides
  inline on `TypedExpr`, whose hand-written `PartialEq` **skips it**: provenance
  is metadata, not part of a node's value, so two structurally-equal nodes stay
  equal even with distinct ids — which the passes' structural-equality checks
  depend on. (Nodes are never hashed by value: `TypedExpr` has no `Hash` impl.
  `NodeId` itself is `Hash`/`Ord`, as a map key.) `NodeId::PLACEHOLDER` is the reserved sentinel for
  `Default`/`mem::take` throwaways (ignored by the recorder; `assert_unique_node_ids`
  backstops that it never persists into a checked tree).
- **`Pass`** — the compiler stage that produced/rewrote a node (`Lower`,
  `Uniquify`, `Inline`, `Desugar`, `Transact`, `Letrec`, `Mono`, `LambdaElim`,
  `Planning`). It lives in the lineage *data* (each step's `via`), never in a
  type.

## The lineage model (`src/ccl/lineage.rs`)

Recording is a **byproduct of performing a rewrite**, never a post-pass diff. As
a pass runs it appends `RewriteStep`s to a `LineageLog`:

- `Op::Transform { consumed, produced }` — inputs vanish, outputs appear (empty
  `produced` = discard; an id in `consumed ∩ produced` survives while absorbing).
- `Op::Copy { origin, produced }` — outputs mirror `origin`'s lineage (freshened
  duplicates); silent on the origin's own fate.

Each step *separately* carries a `blame` set (the upstream ids the outputs
attribute to — **not** the same as `consumed`), a `nature` (the trinary fidelity
axis `Source` / `Expansion` / `Machinery`), and a stable `label`. `consumed`
drives fate/leak accounting; `blame` drives span resolution; the two are never
mixed. `Nature::Source` — a source construct's *direct image* — is emitted
**only by lowering**; the fold's attributing arms carry a debug guard that no
pass step ever carries it.

Lowering records the same way, into its own `LoweringLog` of `LoweringStep`s.
A `LoweringStep` is structurally a `RewriteStep` whose attribution channel is a
literal source-span `anchor` (attached at construction) rather than a NodeId
`blame` (resolved later through the accumulating projection) — that
attached-literal-vs-resolved-reference difference is why the two are sibling
structs, not one generic. Its log is folded **once** at the lowering boundary by
`collapse_lowering` into the always-on lowering projection (below).

### The recorder

An ambient thread-local step stack (`STEP_STACK`) + an installed log
(`ACTIVE_LOG`), mirroring `infer_var::ACTIVE_ARENA`:

- `Expr::new` calls `on_mint`; the freshen helpers call `on_copy` — so a `step(…)`
  RAII guard open around a rewrite *captures* the births/copies in its dynamic
  extent (innermost frame wins). Empty stack ⇒ recording off (a cheap emptiness
  check on the construction hot path).
- `RecorderSession` installs/drains the log at a pass boundary.

**Planned — the passes' adoption.** Production step sites in `infer` (mono — the
`specialize_use` clone `Copy`s and the `coalesce_generalized_let` wrapper
`Transform`), `inline` (beta/alias discard `Transform`s + fan-out `Copy`s), and
`channelize` (cluster/feed-union/lift/drop). Each boundary in `compile_program`
wraps the pass in a `RecorderSession` and retains its drained `LineageLog` on
`CompiledProgram::pass_lineage`, in pipeline order: `[(Mono, …), (Inline, …),
(Transact, …), (Letrec, …), (Desugar, …)]`.

Today the only production step frames are lowering's two `Copy`-capture frames
(below); every other rewrite runs unrecorded.

### The collapse

`collapse(logs, input_ids, output_ids, upstream_attr)` folds a set of logs once,
in pass order, into:

- a `LineageMap<NodeId, NodeId>` — a dense bidirectional node↔node relation
  (self-edge for every survivor), and
- the output pane's `SourceProjection` (`NodeId → SourceAttribution`, where an
  attribution is `{ spans, rewritten: RewriteTag{via, nature, label} }`). The
  `rewritten` tag is **mandatory**: a direct image is
  `RewriteTag::direct_image()` (`{via: Lower, nature: Source, label:
  "lower.image"}`), never an absence. On the wire a `Source`-nature tag
  **null-compresses** to `rewritten: null` (via `Nature::is_source`), so the wire
  stays byte-identical to the retired `Option<RewriteTag>` encoding — both
  validators carry a debug guard that a `"source"` nature never actually ships.

Transients (born + consumed within the phase) compose away. A two-sided leak
audit (`Leak`) guarantees no node silently loses its history: an output with no
lineage (`Unexplained`) and an input that vanished unconsumed (`Dropped`).

Both checks enumerate from the **tree**. There is deliberately no third check on
the *produced* side — "every id a step claims to produce is held by some node" —
because it is not decidable against the node set the fold works over: lowering
tags the nodes inside a refinement predicate, but that set is `collect_tree_ids`,
the `walk_children` domain, which excludes predicate interiors, so every
predicate id would read as a violation.

Two legitimate shapes would read as violations too. Uncurrying `def f(x, y)`
builds one `__arg_tuple_0.0` projection template and substitutes a freshened copy
of it at each `x`; every copy's root carries that occurrence's own id, so the
template's own root id is tagged and then held by no node. The read-your-writes
values the mutability phases keep in a substitution `env` work the same way. An
id retired like that leaves no trace — a *consumed* id shows up in the fold as
absence from `roots`, but a replaced one looks exactly like a live node the check
cannot see. Saying it explicitly means emitting the discard the model already
has, `Transform { consumed: [id], produced: [] }`, which neither site does today.

Construction closes the gap the check would have watched: a node is built either
by `TypedExpr::new` (mint, recorded) or `TypedExpr::preserve` (carry an existing
id, nothing recorded), so an id cannot be minted and then discarded.

The fold is in tree; **planned** is its use at the inspector's two pane
boundaries, which needs the pass logs above.

## The seam (`src/ccl/context.rs`)

- **The lowering log + fold.** Lowering records a `LoweringLog` under an
  always-on `RecorderSession::lowering()` (installed in every build across
  `lower_stmts`, drained before the first pass session). It records at **leaf
  grain**: `tag_source`/`tag_machinery` are thin shims appending a single-node
  leaf `LoweringStep` (`Transform { consumed: [], produced: [id] }`, anchored at
  the nearest real span) — `tag_source` with `Nature::Source` + `"lower.image"`
  (a source construct's *direct image*), `tag_machinery` with `Nature::Machinery`
  + `"lower.<rule>"` (one label per rule; nature is uniform and refinable later
  by a label-keyed remap). Ordinary mints open **no** frame, so `on_mint` stays a
  no-op on the hot path; frames open only where ambient `Copy` capture is needed
  — uncurry's template discharge and the chained-comparison operand freshens,
  whose interior re-mints land as `Copy` LoweringSteps mirroring their origins.

  At the lowering→pipeline handoff (before uniquify/inference, so the release
  `InferError` read timing is unchanged) `collapse_lowering` folds the log
  **once** into the always-on **lowering projection** (`NodeId →
  SourceAttribution`, covering every `walk_children` node — refinement-predicate
  interiors stay outside). This is the degenerate lowering case of `collapse`
  (shared `RootTracker` core): no input pane (roots start empty, leaves are pure
  insertions attributed from their literal anchor), no `LineageMap` output, no
  upstream attr (a `Copy` mirrors its origin's already-folded entry). `Pass::Lower`
  is lowering-projection vocabulary only — it never appears in `pass_lineage` or
  the inter-pane `RewriteStep` logs, which stay homogeneous `NodeId → NodeId`
  (the lowering projection constrains the **product**, not the producer).
  Release `InferError` diagnostics read the projection one-hop (no fold, before
  any pane exists). `CompiledProgram` retains it as `lowering_projection`.
- **The lowering leak gate.** `collapse_lowering`'s leak taxonomy replaces the
  retired `assert_seed_coverage` (and its `SEED_EMPTY_SPANS_ALLOWLIST`): an
  unrecorded lowering mint surfaces as `Leak::Unexplained` (every output-tree
  node must be explained by a leaf or a copy); a born-copied-discarded template
  id composes away (live but neither placed nor an output). The fold is always-on
  (its product is release-critical); the leak *checks* are debug/test-gated at
  the boundary via `assert_leaks_clean`. Orphaned projection keys are
  structurally impossible — the projection is *produced by* the fold, never
  mutated incrementally.
- **Planned — materialization (cold, inspector-only).** `CompiledProgram::materialize_panes`
  folds `pass_lineage` at the two pane boundaries: the Mono log bridges
  pre → post-inference; the Inline + Transact + Letrec + Desugar logs bridge
  post-inference → post-desugar. It returns the three per-pane
  `SourceProjection`s and the two pane-pair `LineageMap`s. **Both boundaries are
  fully recorded** — every pass emits its mints/consumes/copies as `RewriteStep`s
  — so there is no catch-all bridge — every node is explained by a recorded step.
- **Planned — the pane leak gate.** `assert_leaks_clean` is in tree and gates the
  lowering boundary today; planned is applying it at both **pane** boundaries,
  which assert **zero** leaks of every class: an `Unexplained` (uncaptured mint)
  or a `Dropped` (unconsumed vanishing node) is a recording bug, not tolerated
  residue. With the
  full-coverage lowering projection, `unresolved` projection entries are a hard
  zero at every pane too — to be asserted structurally by the census ratchet.

## Planned — inspector consumers (`src/inspector_model/`)

None of this layer exists yet. The inspector is to be the only consumer of the
pane folds; the release compiler reads the lowering projection and nothing else.

- `SpanIndex::build(ir, projection)` inverts a pane's projection to span → node.
- `build_inspect_tree` / `resolve` / `hover` read the pane projection and ship
  each attribution as it is stored: a node's spans plus its `rewritten` tag
  (`{ via, nature, label }`). `/api/resolve` and `/api/hover` carry the same
  `{ spans, rewritten }` shape. The tag serializes as `null` for a direct image
  — `Nature::Source` null-compresses at the emission sites via
  `Nature::is_source`, and both validators guard that a `"source"` nature never
  actually ships. The wire carries no flat `Source`/`Derived`/`Synthetic` label
  string; the frontend formats the tag itself.
- `paneLinks` ship each pane-pair `LineageMap` **dense** — self-edges included,
  no identity-edge filter — via `stage::dense_edges`; the frontend only follows
  edges, never reconstructing them. Both validators check that every edge
  endpoint is a live node id in its respective pane.

The snapshot payload carries its own version in `meta.schema`, owned by the
inspector crate along with the fixture corpus pinned to it. Nothing under
`ccl/` reads or depends on that number: this layer produces attributions and
maps, and the serialization shape is the inspector's contract with its
frontend.
