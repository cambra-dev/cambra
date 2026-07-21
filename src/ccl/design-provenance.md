# provenance & lineage — design and implementation

This doc is the as-built reference for how Cambra keeps an IR node's connection
to the source the user wrote, through a pipeline that otherwise loses it (spans
dropped at lowering, monomorphization cloning subtrees, inline fanning UDF
bodies out, channelize rewriting defers, lambda-elim synthesizing combinators,
planning fusing clauses).

> The design of record — the full decision log, the collapse algorithm, the
> recorder mechanism, and the adoption sequencing — lives in the lineage-redesign
> design doc in the internal vault. This file summarizes
> the shipped shape; where they disagree, that doc wins.

## The two identity primitives (`src/ccl/provenance.rs`)

- **`NodeId`** — a `Copy` newtype giving each IR expression node a stable,
  never-reused identity (its own atomic counter, distinct from `Uid`). It rides
  inline on `TypedExpr` and is **excluded from `PartialEq`/`Hash`** — provenance
  is metadata, not part of a node's value, and the passes' structural-equality
  memoization depends on that. `NodeId::PLACEHOLDER` is the reserved sentinel for
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

Production step sites: `infer` (mono — the `specialize_use` clone `Copy`s and the
`coalesce_generalized_let` wrapper `Transform`), `inline` (beta/alias discard
`Transform`s + fan-out `Copy`s), `channelize` (cluster/feed-union/lift/drop).
Each boundary in `compile_program` wraps the pass in a `RecorderSession` and
retains its drained `LineageLog` on `CompiledProgram::pass_lineage`, in pipeline
order: `[(Mono, …), (Inline, …), (Transact, …), (Letrec, …), (Desugar, …)]`.

### The collapse

At each inspector pane boundary, `collapse(logs, input_ids, output_ids,
upstream_attr)` folds the intervening logs once, in pass order, into:

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
audit (`Leak`) guarantees no node silently loses its history.

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
- **Materialization (cold, inspector-only).** `CompiledProgram::materialize_panes`
  folds `pass_lineage` at the two pane boundaries: the Mono log bridges
  pre → post-inference; the Inline + Transact + Letrec + Desugar logs bridge
  post-inference → post-desugar. It returns the three per-pane
  `SourceProjection`s and the two pane-pair `LineageMap`s. **Both boundaries are
  fully recorded** — every pass emits its mints/consumes/copies as `RewriteStep`s
  — so there is no catch-all bridge — every node is explained by a recorded step.
- **The leak gate (`assert_leaks_clean`).** Debug/test only. Both boundaries
  assert **zero** leaks of every class: an `Unexplained` (uncaptured mint) or
  `Dropped` (unconsumed vanishing node) is a recording bug, not tolerated
  residue. With the full-coverage lowering projection, `unresolved` projection
  entries are a hard zero at every pane too — asserted structurally by the
  census ratchet.

## Inspector consumers (`src/inspector_model/`)

- `SpanIndex::build(ir, projection)` inverts the pane projection to span → node.
- `build_inspect_tree` / `resolve` / `hover` read the pane projection and ship
  the native attribution: per `ir` node the spans channel (`span` field) plus a
  `rewritten` tag (`null | { via, nature, label }`); `/api/resolve` and
  `/api/hover` carry the same `{ spans, rewritten }` `SourceAttribution` shape.
  `rewritten` is `null` for a direct image — the mandatory `Nature::Source` tag
  null-compresses at these emission sites, so the wire is byte-identical to the
  retired `rewritten: None` encoding and no fixtures/validators/frontend moved.
- `paneLinks` ship each pane-pair `LineageMap` **dense** — self-edges included —
  via `stage::dense_edges`; the frontend follows edges only.

## Wire (schema 3)

Schema 3 is the native attribution wire shape:

- `SourceAttribution` carries no flat `Source`/`Derived`/`Synthetic` label
  string; the frontend formats the native `rewritten` tag itself.
- `SourceAttribution`'s serde impl emits the native `{ spans, rewritten }`
  shape.
- there is no non-identity edge filter — `stage::dense_edges` ships the map
  verbatim, self-edges included; validators check every edge endpoint is a live
  node id in its respective pane.
