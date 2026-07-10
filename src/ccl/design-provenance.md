# `provenance` — design and implementation

This doc describes the provenance substrate: `src/ccl/provenance.rs` (the
data-structure core) and the machinery in the compiler and `inspector_model`
that populates and consumes it. It is the as-built reference; it summarizes the
design at a level useful for working in the code, not the full decision history.

> The design rationale and decision log (referred to below as decisions **D1**–**D5**,
> the milestone plan, and open questions) live in internal docs at
> `vault/projects/program-inspector/`. This file does not depend on them.

## What the substrate is

A way to keep an IR expression node's connection to the source the user wrote,
through a pipeline that otherwise loses it (spans dropped at lowering,
monomorphization cloning subtrees, lambda-elim synthesizing combinators,
planning fusing clauses).

Two pieces:

- **`NodeId`** — a `Copy` newtype giving each IR expression node a stable,
  never-reused identity. Minted via `NodeId::fresh()` using the same atomic-
  counter idiom as `Uid`/`FRESH_UID` in `names.rs`, but on its own counter (node
  identity and binder identity are different id spaces). It rides inline on
  `TypedExpr`, is excluded from the type's `PartialEq` (provenance is metadata,
  not part of a node's value — including it would defeat structural-equality
  memoization in `uniquify`/`planning`).
- **`ProvenanceTable`** — a `HashMap<NodeId, Provenance>` side table with
  `insert` / `resolve` / `origins`. `resolve` returns `Option`: a missing entry
  is `None` ("source unknown"), never a panic. A forgotten registration is a
  quality bug, not a correctness bug.

`Provenance` records three orthogonal axes — kept separate so the enum does not
sprawl:

- **WHERE** — `origins: Vec<Span>`. One span = blame (the common case); many =
  fusion/fan-in. The representation is full-capable but populated at blame level
  (singletons) for the MVP, with zero migration to grow.
- **WHO** — `Pass` (the producing stage: `Lower`, `Uniquify`, `Mono`, `Desugar`,
  `LambdaElim`, `Planning`).
- **HOW** — `Derivation`: `Source` (1:1, shown), `Derived { via }` (traceable
  synthesis, inspector collapses under source), `Synthetic { via }` (plumbing,
  inspector hides).

### `NodeRecord` is the per-pass primitive; `Derivation` is the composed view

`Derivation` is not the ground-truth unit of construction — it is a *derived
view*. The primitive is `node_recorder::NodeRecord`: a single **per-pass
construction edge** describing how one output node relates to *that pass's input
tree* in one hop, classified by input/output cardinality — `Preserved` (1→1),
`Fused` (n→1), `Minted` (0→1, new), `Discarded` (1→0, an input removed with no
counterpart; distinct from `Fused` in that it produces no stage edge), or
`Replicated` (1→N, one origin duplicated into N freshened copies that each mirror
it — mono clone, inline fan-out, substitution). `NodeRecord`
and `Derivation` are the **same axis** (how a node came to exist) at two
**scopes**: `NodeRecord` is one hop against the pass's inputs (its `origins`/`from`
are input `NodeId`s, never spans); `Derivation` (`Source`/`Derived`/`Synthetic`)
is that relation **transitively composed** back to source and resolved to spans.
A `NodeRecord` therefore deliberately does *not* carry a `Derivation` — that would
conflate the scopes. `Derived`/`Synthetic` entries are *produced by composing* the
per-pass records: `NodeRecorder::to_provenance_entries` takes a resolver that maps
each `Minted` origin id to the spans it reaches through the already-composed table.
(See `node_recorder.rs` and `vault/.../node-recorder-plan.md`.)

### Display is decoupled from `Synthetic`

The inspector's show / collapse / hide behavior is a *presentation* decision, not
a property welded to the `Derivation` kind. The recorder records only the one bit
the composed graph cannot recover — `MintNature::{Expansion, Scaffolding}`
(faithful expansion of a user construct vs. pure machinery) — and leaves whether a
node is hidden or collapsed to the presentation layer. The "collapses / hides"
notes on the `Derivation` variants above describe the *current default* mapping,
not an invariant: do not treat `Synthetic` as synonymous with "hidden".

> **Adoption status.** `inline` is adopted construction-threaded
> (`Pass::Inline`, id-preserving + `Replicated`/`Discarded` records, reconciled
> *and applied* at its boundary — its fan-out copies resolve
> `Derived { via: Inline }` and its stage remap is retained; see the
> application-order and multi-pane sections below). **`desugar` is NOT yet adopted**
> — it still uses `apply_desugar_synthetic_sweep` + the channel fan-in records
> described in the sweep and application-order sections below (those remain the
> as-built reference for the code that runs); the application *order* of those
> records is already dataflow-derived and assertion-guarded (see the
> application-order section). The desugar adoption (which retires the sweep and
> gives desugar a leak oracle) is deferred to the `desugar_defers`
> **channelization rewrite**,
> since that pass is an explicit prototype slated for rework. `transact`/`letrec`
> are likewise uninstrumented (id-preserving for defer-/txn-free programs).

## Dual use (explicit, first-class)

The table is the single mechanism behind both the program inspector (`resolve`
*is* the source-map projection) and compiler diagnostics (a location-poor pass
captures a `NodeId` at the error site; rendering resolves it to a span through
this same table). Both call `ProvenanceTable::resolve` — there is no parallel
ad-hoc path.

## How the table is populated through the pipeline

Pipeline order: lowering → uniquify → infer → (mut/txn checks) → inline →
transact_phase → letrec_phase → `desugar_defers` → typecheck → lambda_elim →
planning. (`desugar_defers` runs *after* inference — the transactional-mutability
work moved it post-inference; it ends with a `retype` synthesis so the tree stays
typed.) The substrate covers `lowering → typecheck` today;
lambda_elim/planning/operators are future work.

The recurring mechanism is **emit-and-apply**: a pass that changes node identity
surfaces `NodeId` remap/blame records rather than touching the table itself;
`compile_program` applies them against the retained table at the pass boundary.
This keeps the intricate passes (inference, defer desugaring) ignorant of
`ProvenanceTable`, and lets mono, desugar, and (later) lambda-elim/planning share
one resolution primitive (`resolve_origins_through_chain`).

### Lowering tags `Source(span)`

Lowering is the first and primary populator. A `ProvenanceTable` lives on
`LoweringContext` (drained by `take_provenance`, mirroring `take_sources` /
`take_sink_bindings`); `compile_program` takes it while still populated and
retains it on `CompiledProgram::provenance`. Two tagging surfaces, both
blame-level `Source(span)`:

1. **Every expression node**, via the `lower_expr` wrapper over `lower_expr_inner`:
   it tags the one node it returns with the `Spanned<ChlExpr>.span` it carries.
   Each call tags exactly its own root, so children are tagged by their own calls.
2. **Statement-level `Let`/lambda nodes** built outside `lower_expr` (the
   assignment / annotated / augmented / `def` sites, the http_serve `requests`
   binding, the function lambda wrapper) — tagged with the construct span via the
   `ctx.tag_source(expr, span)` helper.

Synthetic interior nodes a single arm builds (the `Proj` inside a subscript, the
`Case` scaffolding for a ternary, generator/mutation-loop accumulator lets) are
left untagged and `resolve` to `None` gracefully.

### `uniquify` preserves ids in place

`uniquify` is a 1:1 in-place α-rename, so it preserves every `NodeId` without
change (the one node-rebuilding path — a type-borne refinement predicate — clones
first, so `Clone` carries the id). A debug-only assert in `uniquify::run` snapshots
the sorted `node_id()` multiset before and after and requires equality.

### Monomorphization freshens ids and emits a remap

Inference is *not* tree-shape-preserving: monomorphization (`specialize_use` in
`infer/solve.rs`) deep-clones a generalized def's subtree once per resolved
type and replaces the polymorphic original. `Clone` copies `node_id`, so the N
specializations would collide on one id. Monomorphization therefore freshens
every cloned node's id (`TypedExpr::freshen_node_id`) and records a
`(fresh → original)` remap on `CoalesceCtx`, surfaced from `infer` via
`take_mono_remap`. `compile_program::apply_mono_remap` resolves each chain
transitively against the table and tags the clone `Derived { via: Mono }` with
the original node's origins.

Consequence for the inspector: hover on a polymorphic definition shows the *set*
of specialized types ("used at `Int` and `String`"), not one general type — the
general type is consumed during coalescing.

`coalesce_generalized_let` (which rebuilds per-specialization wrapper `Let`s with
fresh ids) also records a `(wrapper, generalized-let)` pair on the same remap, so
each wrapper is tagged `Derived { via: Mono }` (or `Synthetic { via: Mono }` when
the chain can't reach a known node — honest mono plumbing, correctly attributed so
the desugar sweep below never mislabels it).

### The shared deep-freshen walk

Freshening a *clone's* ids — re-minting every node so N copies of one subtree do
not collide on a single id — is done by one walk, `TypedExpr::freshen_node_ids_deep`
(in `expr.rs`, beside the per-node `freshen_node_id` primitive). It covers the
exact `uniquify::collect_node_ids` node-set: the main tree, the `TypedExpr`s
inside type-borne refinement predicates (reached through `.ty`, the user
annotation, and a `Cast`'s target type — predicate `Rc`s split via `Rc::make_mut`,
one freshen per `PredicateId`), and `Cast` targets. It invokes a caller callback
`on_freshen(old, new)` per node.

Two consumers share it, so there is no second, subtly-different walk:

- **Monomorphization** records: `freshen_clone_node_ids` calls it with
  `|old, new| remap.push((new, old))`, feeding `apply_mono_remap`
  (`Derived { via: Mono }`).
- **The transact / letrec phases** discard the pairs: their `subst_env` and
  scaffolding copies are *unattributed* (see below).

### transact / letrec: freshen substituted copies to keep ids unique

`transact_phase` and `letrec_phase` splice stored values into the output at
multiple positions — a read-your-writes env value substituted at every store /
accumulator read (`subst_env`), each store key's `init` spliced at both its
history default and its continuation rebind, and the induction `step` view /
loop source cloned into the guard and each trailing read. A bare `clone` stamps
the **same** `NodeId`s into every position, breaking the tree-wide id-uniqueness
invariant (a node substituted at N sites appeared N times with one id). Each such
copy is now id-freshened (`freshen_node_ids_deep`, via each phase's `fresh_copy`
helper, and directly in `subst_env`). `letrec_phase`'s `flatten_spine`
bare-writer arm is the dual fix: it now **carries** the input write's id (a
preserve) instead of minting, so the repositioned write keeps its source link.

These freshened copies are **unattributed** — they carry fresh ids with no
record, so the desugar `Synthetic { via: Desugar }` sweep tags them (the `via` is
knowingly wrong: they are transact/letrec nodes, not desugar nodes). Attribution
awaits the per-phase transact/letrec `NodeRecorder` adoption (a documented
follow-up). Discarding the freshen pairs is safe: no downstream pass reads
`node_id`, and `inline::dedup` (the only consumer that ever exploited shared ids)
runs *before* these phases.

### Id-uniqueness tripwire + census ratchet

Two class-level guardrails catch id-churn bugs going forward:

- **Uniqueness tripwire.** `assert_unique_node_ids(expr, boundary)` (in
  `context.rs`) panics if a boundary tree carries a duplicated `NodeId`, naming
  the boundary and the offending ids + kinds. It walks the same main-tree
  `walk_children` node-set as `node_recorder::collect_ids` — **predicates
  excluded**, so it does not false-fire on inline's known predicate blind spot.
  It encodes no pass order (a moved pass carries its check with it) and is gated
  `cfg!(any(debug_assertions, test))` as an *expression* (no gated item that a
  release-clippy pass would flag). Installed at: **post-inline** (after dedup),
  **post-transact**, **post-letrec-run**, **post-letrec-recognize**, and
  **post-desugar gated to defer-free inputs**. The post-desugar gate mirrors
  `desugar_defers::is_pure_structural` / the `run_with_provenance` preservation
  assert: `desugar_substitute` legitimately leaves duplicate ids on defer-bearing
  programs (`Defer`/`Feed`/`Define`) until the channelization rewrite, so the
  check runs only when the desugar input is defer-free (`contains_defer_nodes`).
- **Census ratchet.** `provenance_census(stage_ir, table)` (test-side, in
  `context.rs`) counts every main-tree node by resolution category
  (`Source` / `Derived(via)` / `Synthetic(via)` / `unresolved`) over a stage
  tree. One table-driven test pins exact counts per representative program
  (arithmetic / polymorphic / UDF fan-out / mutation-loop / txn) per retained
  stage. A pass that churns ids without recording shows up as `Synthetic` /
  `unresolved` inflation and fails the pin; a deliberate provenance improvement
  moves a row (the diff is the commit's provenance-impact statement). The txn /
  loop rows document the current heavy-`Synthetic{Desugar}` state from the
  unattributed transact/letrec copies described above.

### `desugar_defers`: preserve ids, tag plumbing

`desugar_defers` runs after `infer` (see the pipeline order above). It preserves
and tags every node it touches, rather than reconstructing the whole tree with
fresh ids:

- **(P) 1:1 sites carry the original id.** The `desugar` `other`/`Let` arms, the
  whole-tree spine walk in `rewrite_chains_in_scope`, `drop_expr_stmts` (an
  explicit structural match that collapses a plain `ExprStmt` to its body and
  preserves `node_id` on every other rebuilt envelope), the channelization spine
  helpers, the prefix-spine of `extract_defer_binding`, and the lifted
  `Feed`/`Define` prefix heads rebuilt by `try_lift_defer` (the defer-returning-
  let lift renames only the target handle `x → y`, so each head keeps the id of
  the node the user wrote) all capture and reuse
  `node_id`. The
  owned-rebuild builder `TypedExpr::map_node(self, f)` (transform the node, keep
  `node_id`/`ty`/`user_annotation`) completes the
  `walk_children`/`map_children`/`map_node` family and is the recommended
  mechanic for envelope-preserving restructures.
- **(M) merges carry the surviving binding's id.** The cluster peel threads
  `Vec<(Name, NodeId)>`, so a rebuilt `let d_i = channel_i` carries the original
  `let d_i = Defer` node's id (via `TypedExpr::with_node_id`) — single-origin
  blame to the user's construct.
- **(S) synthesis is tagged, never left `None`.** Via emit-and-apply:
  `combine_feed_values` emits a `DesugarFanin { target, sources }` for each channel
  `CollectionUnion`, applied post-inference by `apply_desugar_fanins`. Fan-ins
  resolve their `sources` (feed-value node ids) to origins → multi-origin
  `Derived { via: Desugar }` (the many-to-one feed→channel lineage). Everything
  else synthesized is caught by `apply_desugar_synthetic_sweep` →
  `Synthetic { via: Desugar }`.

A debug-only `is_pure_structural`-gated assert in `run_with_provenance` requires
strict before/after id-set equality when the input is a genuine 1:1 transform
(no defers, no defer-mediating UDFs); defer/UDF inputs legitimately drop and add
ids.

**Synthesized-node origin enrichment.** Two classes of synthesized node that were
originally span-less are now given `Derived` origins:

- **Channel fan-in** blames the feed sites. `DesugarFanin.sources` is
  `Vec<Vec<NodeId>>` (a pre-order id list per feed); the applier takes the *first
  id that resolves* per feed, so the union blames exactly the feed-site
  expressions the user wrote.

> **No defer-mediating UDF wrapper-blame enrichment.** `inline` beta-reduces
> every defer-mediating UDF to its call sites before desugar runs, so the
> synthesized `Lambda`/`Record`/`Compose`/`Var` chain from
> `rewrite_lambda_to_return_contributions` is never reachable — a wrapper-blame
> record set for it would never fire. If that path is ever reached, its wrapper
> nodes fall to the `Synthetic` sweep — graceful; proper attribution is
> re-derived at the `desugar_defers` channelization rewrite via the
> `node_recorder` recorder.

**Application order (per-boundary appliers in `context.rs`).** The record sets
are applied at their pipeline boundaries, in **pipeline dataflow order**: *mono
remap (infer boundary) → inline fan-out (inline boundary) → channel fan-ins →
synthetic sweep (desugar boundary)*. The rule (see
"Application order is data-derived, never a frozen pass order" in
`node_recorder.rs`): the order is **derived from the current pipeline's record
data-dependencies, never a frozen pass order** — a set applies only after every
set that tags the ids its records name as sources.

- The **mono remap** is drained right after `infer` and applied *then*
  (`apply_mono_remap`): its `source` ids are pre-mono lowered ids already tagged
  by lowering, so it depends on nothing later, and applying it early puts it in
  place before the inline boundary.
- The **inline fan-out** is applied at the inline boundary
  (`apply_inline_records`): each `Replicated` copy mirrors a post-mono origin, so
  it resolves `Derived { via: Inline }` through the mono-tagged origin (and
  degrades to `Synthetic { via: Inline }` when the origin resolves to nothing).
  This is why the mono remap moved earlier — a replica of a mono clone must
  resolve through the mono tag. The inline `(copy, origin)` stage remap is
  retained on `CompiledProgram::pass_remaps` keyed `Pass::Inline` (see the
  multi-pane section).
- The **desugar fan-ins** are applied at the desugar boundary
  (`apply_desugar_records`): their `sources` name post-mono/post-inline content
  (possibly mono-fresh clone ids or inline copy ids) and resolve only once those
  sets have tagged them. The sweep runs last and skips any id the earlier
  boundaries tagged *by table membership alone* — every declared-set target is a
  table member by then, so no separate already-tagged set is threaded;
  `apply_desugar_fanins` never overwrites a known id, keeping preserved-`Source`
  feed nodes intact and the pass idempotent.

The order is additionally **enforced structurally** by a record-dependency
assertion (`PendingRecordTargets` in `context.rs`), a single instance threaded
across all three boundaries: each *declared* set (mono remap, inline fan-out,
channel fan-ins — not the fallback sweep) is `declare`d with the ids it
will tag as it becomes known, and marked applied before it runs; when a record's
origin id fails to resolve, the applier checks it against the union of the
not-yet-applied sets' targets. A hit is an ordering violation and panics in
debug/test builds (every compile in the suite probes the ordering); a
genuinely-unknown id keeps the graceful `None` path. This distinguishes
"legitimately unresolvable" from "asked too early": applying the fan-ins before
the mono remap would silently produce fan-in records with empty origins, since
their `sources` name mono-fresh ids the remap has not tagged yet.

> ⚠ **Known limitation — the catch-all sweep masks id-preservation leaks.**
> `apply_desugar_synthetic_sweep` tags *whatever* is untagged as
> `Synthetic { via: Desugar }`. An overlooked (P) site that rebuilt with
> `NodeId::fresh()` — which should surface as a detectable `None` — is instead
> silently mislabeled `Synthetic`. The `node_recorder::NodeRecorder` (see above)
> is the structural fix: routing `desugar_defers` through it, as `inline`
> already does, would make every construction self-declaring so a mismatch is
> caught by `reconcile` rather than masked by the sweep. A code-adjacent note
> lives on `apply_desugar_synthetic_sweep`.

## The inspector anchor: the post-inference snapshot

The inspector and diagnostics anchor on the IR **right after `infer`/`typecheck`**
— fully typed but still source-shaped (lambdas intact, pre-inline/lambda-elim/
planning). `compile_program` clones `expr` at that point (before `inline` consumes
it) onto `CompiledProgram::post_inference_ir`. This is distinct from
`CompiledProgram::ast` (`join_planned`), whose ids lambda-elim/planning re-minted
(→ `None` in the table) and whose shape is point-free/fused — the wrong tree for a
source-level view.

## The inspector read model (`inspector_model`)

A core-crate module (serde-free by default) that turns the snapshot + table into
the read-only query surface. `ProvenanceTable::resolve` is the *forward* direction
(node → span); the inspector also needs *backward* (span → node) and source-level
name resolution.

- **`SpanIndex` — span → node.** Built by walking the snapshot and indexing each
  node under every span in `provenance.origins(node)`. `enclosing(pos)` returns the
  whole **containment set/chain**, ordered outermost → innermost by span extent
  (coincident spans tie-break on structural depth); `tightest(pos)` is the chain
  tip. Containment is the trivial `start <= pos < end` test over a flat `Vec` scan
  (not `intervalsets`, which targets numeric value-domains and has a known
  half-bounded `contains` bug); swappable for an interval tree behind the same API.
- **`NameBinderIndex` — source-level name resolution.** Goto-definition and the
  binder half of scope-at are *source-language* lexical questions, resolved over
  the parsed CHL `Module` (retained on `CompiledProgram::source_ast`), **not** the
  lowered tree. Reason: `uncurry_params` rewrites a multi-param reference `Var(x)`
  to a projection `__arg_tuple_N ▷ .i` before uniquify runs, so an IR-based binder
  table structurally cannot resolve a multi-param parameter (no surviving `Var(x)`,
  no use-span); the surface AST still has `x` with its `Param.name_span`. The index
  walks lexical scopes mirroring CHL's sequential let-style scoping (a binder is
  visible only after its site; RHS sees the prior binder; inner shadows outer;
  `def`/`lambda` names are not visible in their own bodies). Queries:
  `definition_of(use_span) → Option<Span>` and `bindings_in_scope(at) → Vec<Binding>`.
- **Query handlers + `Snapshot` bundle.** `Snapshot<'a>` borrows the projections
  (source text, post-inference IR, `ProvenanceTable`, surface `Module`) and owns
  the indices; `Snapshot::new(&CompiledProgram)` is the single construction point.
  Handlers are pure functions: `resolve`, `hover`/`type_of`, `goto_definition`,
  `scope_at`, `expand`. `hover` returns the type *set* for monomorphized defs (see
  above). Live seams `tick`/`value_summary` are declared as `Option` of
  uninhabited placeholder enums (`Tick`/`ValueSummary`) — so the static M1 model is
  a compile-time-guaranteed subset of the eventual live model, always `None` today.
  Node-by-id lookup is a per-query walk over `TypedExpr::child_exprs()` (the
  borrow-returning form; a cached id→&node map runs into `&mut`-invariance).

`expand` reuses `pretty_tree::InspectNode`, extended with optional source-linking
fields — `node_id`, `span`, `provenance`, and a first-class `ty` field (all stored
as primitives to keep `pretty_tree` free of `ccl` deps). The CLI Unicode renderer
and the existing `to_json` are unaffected.

## Serialization and the `/api/snapshot` payload

Serde is isolated: every wire type lives in `cambra` core behind
`#[cfg_attr(feature = "serde", derive(serde::Serialize))]` (+ camelCase renames);
`serde_json` and the `to_string` live in the `cambra-inspector` crate
(`snapshot_json(&CompiledProgram, name) -> String`). The default `cambra` build
compiles zero serde (verified in CI via `cargo tree -p cambra`).

Per-type serialization: `Type` → its `Display` string (structural would leak
`Infer` ids/holes); `Span` → `{start,end}`; `NodeId` → a bare number;
`Provenance` → flat `{kind, via, origins}`. The `SnapshotPayload` bundle carries
`source`, `definitions`, `scopes`, `stages`/`stageLinks` (see below),
`diagnostics`, and `meta {tick, snapshotKind, schema}`. A failed compile flows
through `SnapshotPayload::degraded(...)` — the same type as success (empty
stages/indices, `snapshotKind: "failed"`) — so there is one schema source of
truth. `stageLinks[].edges` are sorted for a deterministic payload;
`meta.schema` is a documented wire-version constant.

**Wire schema 2** (current). Its delta from schema 1: the legacy top-level
`ir`/`spanIndex` aliases — byte-for-byte duplicates of the post-inference stage,
retained for the pre-3-stage frontend — are **removed**; a client reads the
per-stage `stages[].ir`/`stages[].spanIndex`. And the `StageEntry.kind`
vocabulary was renamed `"pre-inference"/"post-inference"` → **`"holes"/"typed"`**
(the old values collided with stage *ids* and read as a copy-paste bug on the
post-desugar stage, which is honestly `"typed"`). The Rust
`assert_snapshot_shape` (`cambra-inspector/src/lib.rs`) and the frontend's
`validateSnapshot` pin this one contract on both sides. `meta.schema`'s source
of truth is `inspector_model::SCHEMA_VERSION`.

**Golden corpus.** `cambra-inspector/scripts/fixtures.manifest` maps the
committed frontend fixtures (`web/src/__fixtures__/*.snapshot.json`) to the
example programs they are dumped from — the single corpus source shared by
`regen-fixtures.sh` (the regen/fix path) and the cargo golden tests
(`cambra-inspector/tests/goldens.rs`). The corpus includes one program per
recorder-fixes regression shape (inline fan-out, txn multi-read, mutation
loop, defer-lift). The golden tests spawn the real `--dump-snapshot` CLI
**once per program per dump** — `NodeId`s come from a process-global counter,
so only a fresh single-compile process reproduces a fixture's ids — and pin
that every corpus dump is cross-process deterministic (two spawns,
byte-identical) and well-formed at the current schema. A golden is a
*ratchet, not a specification*: it pins whatever the code did at blessing
time; semantic unit tests state intent, the boundary invariants (uniqueness
tripwire, record-dependency assertion) enforce error classes suite-wide, and
the goldens are the coarse everything-composed backstop against drift.

## Multi-pane / N-stage view: the 4-pane model

The inspector shows a generic N-stage view, with panes
**`source → pre-inference → post-inference → post-desugar`** (design home:
internal docs at `vault/projects/program-inspector/`, `build-status.md` is
the fine-grained SoT) — chosen because `desugar_defers` runs *after* inference,
so post-inference is the last fully source-shaped snapshot and post-desugar is
the last one before lambda-elim/planning fuse the tree. Four things support it:

- **Three IR snapshots are retained on `CompiledProgram`.** `pre_inference_ir` —
  cloned right after `uniquify`, **before `infer`**: the pre-mono, source-shaped,
  still-hole-typed tree. `post_inference_ir` — right after `infer`/`typecheck`,
  before `inline` consumes it: fully typed, source-shaped, the query **anchor**.
  `post_desugar_ir` — right after `desugar_defers` (which now runs after
  `infer`/`inline`/`transact`/`letrec`): fully typed, post-mono, structurally final
  for the source view (Defer/Feed/Define gone, channelization artifacts present).
- **Per-stage provenance projections.** `pre_inference_ir` and `post_inference_ir`
  resolve against `CompiledProgram::provenance`; `pre_inference_ir`'s ids are the
  pre-mono originals (keyed by lowering `Source` tags in that table). `post_desugar_ir`
  resolves against the **shared `CompiledProgram::provenance` table** directly — that
  table already carries `apply_mono_remap` + the desugar channel fan-in records
  + a `Synthetic { via: Desugar }` sweep applied *over the desugared tree*, so it
  resolves every post-desugar node id (shared preserved/mono ids and
  desugar-introduced ids alike). A separate per-stage post-desugar table returns only
  when per-pass record composition makes the projections actually diverge; until then
  a clone would be pure duplication of the shared table. A lowering-only
  projection would not work here: lowering's pre-mono ids don't match this
  post-mono/post-inline tree, so its span index would resolve nothing.
- **Node→node stage adjacency, per pane-pair.** Cross-pane links decompose into
  **identity edges** (a `NodeId` in both trees — recomputed by the consumer) and
  **non-identity edges** (where a pass changes identity), via
  `inspector_model::StageAdjacency::from_remap`. The compiler retains the
  non-identity remaps **keyed by pass** (`CompiledProgram::pass_remaps` —
  `Pass::Mono` for monomorphization fan-out, one upstream def → N downstream
  clones; `Pass::Inline` for inline fan-out, one UDF body → N freshened copies):
  the compiler knows passes, not panes, so stage vocabulary never leaks into
  `ccl`. `inspector_model` owns the pair→pass association
  (`stage::remap_between_stages`): each consecutive stage pair's `stageLinks`
  entry is built from the remaps of the passes that run between its two
  snapshots — `pre-inference → post-inference` from `Pass::Mono`,
  `post-inference → post-desugar` from `Pass::Inline` — keyed by the pair's
  stage *ids*, never by window position, so the association cannot silently rot
  when stages are added or reordered. `SnapshotPayload` carries
  `stages: [{id, label, kind, ir, spanIndex}]` and
  `stageLinks: [{from, to, edges}]` (non-identity only); the anchor is set
  explicitly to the `post-inference` stage (the middle pane, not "last").
- **Inline is id-preserving + recorded (`Pass::Inline`).** `inline` carries every
  input `NodeId` through and records its fan-out (`Replicated`) and
  drops (`Discarded`) via a `NodeRecorder`; `context.rs` reconciles at the inline
  boundary (debug-gated), **applies** its records
  (`apply_inline_records` → `Derived { via: Inline }` for each fan-out copy,
  resolved through the mono-tagged origins), and **retains** its `(copy, origin)`
  stage remap on `CompiledProgram::pass_remaps` (keyed `Pass::Inline`). This is what makes
  `post_desugar_ir`'s preserved ids trace back to `post_inference_ir`, so the
  post-desugar span index resolves — and makes the inline copies resolve to their
  UDF-body spans instead of being swept `Synthetic { via: Desugar }`.

  > **Deferred — the rich `post-inference ⇄ post-desugar` cross-edges.** Inline
  > fan-out is attributed (node→span `Derived { via: Inline }`) and its
  > `(copy, origin)` remap is retained (`pass_remaps`, keyed `Pass::Inline`) and
  > consumed by the wire (the pane-pair's `stageLinks` carry the fan-out
  > edges). The desugar-*minted* nodes (channel
  > `CollectionUnion`s, DI wrappers, contribution records) are not yet linked
  > node→node to their post-inference origins (channel unions are covered as
  > node→span by the existing `DesugarFanin`s; the rest fall to the `Synthetic`
  > sweep). Full attribution + a leak oracle + sweep retirement ride the **desugar
  > `NodeRecorder` adoption**, itself deferred to the `desugar_defers` **channelization
  > rewrite** (the pass is an explicit prototype — see its module header). Of the
  > five tests covering this gap, four pass (mono fan-out, defer `CollectionUnion`
  > coverage, stage ordering, polymorphic stage links); the fifth,
  > `generator_coverage_maps_wrapper_chain`, stays `#[ignore]`d because the
  > current generator lowers to a plain `Compose` map whose wrappers the sweep
  > leaves origin-less — it re-enables only once the deferred desugar recorder
  > lands.

## Unified diagnostics (dual-use, as-built)

Type-inference errors route through the same `provenance.origins` resolution the
inspector uses, driving two consumers from one resolve: ariadne source-context
rendering (terminal) and structured JSON `Diagnostic`s (web).

- **Location is metadata, not error identity.** `InferError` is unchanged
  (`PartialEq`, no span field, all its `assert_eq!` tests untouched). The inner
  simple-sub `infer` pairs each error with an `Option<NodeId>`; the public `infer`
  keeps its signature and splits the ids onto a side-channel
  (`TypeInferenceContext::infer_error_nodes`), positionally aligned — mirroring the
  mono remap side-channel exactly.
- **Capturing the blame node.** `emit_node` wraps `emit_node_inner`, recording
  `current_node_id` on entry and restoring it only on success; inference is
  fail-fast, so on error the field points at the innermost failed node. Only the
  pass-1 emit site carries a real id (the high-value `UnboundVariable` /
  `TypeMismatch` / `ExpectedFunction` variants); pass-2 coalesce errors use
  `node_id: None` → graceful plain-text fallback.
- **Resolution at the boundary.** `compile_program` drains the blame ids and
  resolves each via `provenance.origins(id)` while the table is in scope,
  producing `CompileError::Infer { error, span: Option<Span> }`.
- **Two renderers, one model.** `CompileError::render`/`eprint` build an ariadne
  `Report` for `span: Some` and keep the plain line for `None`; the web half is
  `Diagnostic { severity, stage, message, span, labels }` via
  `diagnostics_from_compile_errors`. The infer diagnostic's span is the same
  boundary-resolved range the terminal underlines.

(Gotcha: `1 + "a"` is a *pass-2* `IncompatibleBounds` with no single blame node
→ `None`; the pass-1 span path is exercised by errors failing during constraint
emission, e.g. `1 and 2`, `not 1`, an unbound variable.)

## `Pass` and `SyntheticKind` stay separate

`names::SyntheticKind` and `provenance::Pass` are distinct enums, neither wrapping
the other, because they answer different questions about different subjects:

- **`SyntheticKind` tags `Name`s — compiler-introduced *binders*** (keyed by
  `Uid`), and is binder-*role*-rich: `Pair` (lambda-elim's tupled binder),
  `Mono(Box<Name>)` (carrying the source binding's `Name`), `ShadowRename`,
  `FloatedDefer`, `SolverArg`.
- **`Pass` tags `NodeId`s — *expression nodes*** (a different id space), and is
  the coarse WHO axis: just the producing stage, no role payload.

Merging them would force binder-roles into the node-origin axis (or `Pass` to
carry binder payloads) — the axis-conflation the WHERE/WHO/HOW separation avoids.
They *compose* at goto-def for a monomorphized binder: read
`SyntheticKind::Mono(source_name)` to recover the original `Name`, resolve it via
the name index, then resolve that node through the `ProvenanceTable` for a span.

## Deferred / future work

- Populate the table from lambda-elim (1→many) and planning (many→1) via the same
  emit-and-apply pattern, plus an `OperatorId → NodeId` tag in
  `operator_conversion.rs` — the source↔operator (dataflow) layer.
- The substituted-parameter span fix: carry the replaced `Var`'s span onto the
  `__arg_tuple_N ▷ .i` projection (per-occurrence fresh ids) so hover-type on a
  multi-param parameter *use* resolves via `SpanIndex`. Goto-def on such params
  already works (source-level).
- Harden the `Synthetic` sweep against masking preservation leaks (see the known
  limitation above).
- `SmallVec<[Span; 1]>` for `origins` (the common case is one origin) — deferred to
  avoid adding a dependency.
- **Per-phase `NodeRecorder` for transact / letrec.** Their spliced/freshened
  copies are currently unique but unattributed (swept `Synthetic { via: Desugar }`
  with a knowingly-wrong `via`). Adopting the recorder there would attribute them
  (`Replicated`/`Derived`) and yield real stage edges. The census ratchet is in
  place to verify that change when it lands.
- **A pre-existing id-duplication out of lowering/uniquify.** An
  `a, b = http_serve(...)` tuple-assign program carries a duplicated `Var`
  `NodeId` at post-uniquify (and thus post-infer). No tripwire is installed at
  that boundary, and the issue is orthogonal to the transact/letrec phases —
  recorded here as a finding for a lowering-side fix.
