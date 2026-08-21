# Provenance & lineage — node identity and source attribution

This doc is the reference for how Cambra keeps an IR node's connection to the
source the user wrote, through a pipeline that otherwise loses it (spans dropped
at lowering, monomorphization cloning subtrees, inline fanning UDF bodies out,
channelize rewriting defers, lambda-elim synthesizing combinators, planning
fusing clauses).

A **pane** is a snapshot of the AST at one point in compilation. `CompiledProgram` retains three —
`pre_inference_ir`, `post_inference_ir`, `post_desugar_ir` — and the inspector renders each in one
UI pane, which is where the name comes from. **Below** a pane means later in the pipeline, on a more
lowered tree; it is not tree depth and not a layering.

**Status markers.** The substrate — the identity primitives, the lineage model,
the recorder, and the always-on lowering projection — is in tree. Everything a
**Planned** marker introduces is designed but not yet built: the passes' adoption
of the recorder, the pane-boundary folds, and the inspector's consumption of
them. A reader on `main` can tell the two apart by the marker alone; unmarked
prose describes code you can go read.

> This file is the reference for the shipped shape and wins on what the code
> does. The decision log behind it — the rejected alternatives, the measurements,
> and the adoption sequencing — is the `lineage-design` note under
> projects/program-inspector in the internal vault.

## Node identity (`src/ccl/provenance.rs`)

**`NodeId`** is a `Copy` newtype giving each IR expression node an identity: stable, never reused,
and off its own atomic counter. It rides inline on `TypedExpr`. Lineage and source attribution are
both keyed by it, which is what lets an inference error on a node minted three passes ago resolve to
the source span the user wrote. It is distinct from `Uid` because `Uid` identifies binders and a
`NodeId` identifies expression nodes.

A node is **live** when it is reachable from the expression tree a pass hands on — the node set
`walk_children` enumerates, called the **main tree** throughout this doc. A refinement predicate is
a term hanging off a *type* slot, so its nodes are reachable from the tree without being in it; the
distinction is what the two walks below split on.

Four properties define a `NodeId`.

- **It is not part of a node's value.** `TypedExpr`'s hand-written `PartialEq` skips `node_id`, so
  two structurally-equal nodes compare equal with distinct ids, which the passes'
  structural-equality checks depend on. Nodes are never hashed by value: `TypedExpr` has no `Hash`
  impl. `NodeId` itself is `Hash`/`Ord`, as a map key.
- **Two live nodes never share one.** This is what makes an id an identity rather than a label. Two
  nodes at one id collapse to a single entry in every `NodeId`-keyed walk, and give the
  `SourceProjection` — the `NodeId → SourceAttribution` map the lineage fold produces
  ([The collapse](#the-collapse)) — one attribution for two nodes.
- **Construction and copying both mint.** `Expr::new` mints, and `Clone` mints for every node it
  copies. A call site duplicating a subtree gets distinct identities without asking for them, so no
  site has to work out which of its copies is the survivor — reaching a shared id takes writing one
  through a named primitive ([Duplication](#duplication)).
- **Uniqueness is asserted on the main tree only.** `assert_unique_node_ids` walks children and
  stops there, so predicate interiors are outside the uniqueness walk.

`NodeId::PLACEHOLDER` is the reserved sentinel for `Default`/`mem::take` throwaways. The recorder —
the ambient session that logs every mint and copy ([The recorder](#the-recorder)) — ignores it, and
`assert_unique_node_ids` backstops that it never persists into a checked tree.

### Maintaining uniqueness

`Clone` freshens: it mints a new `NodeId` for every node it copies and reports each `(origin,
fresh)` pair through `on_copy`, the recorder's copy hook. The alternative is a call site that
decides — keep the id here, freshen there — and a site that decides wrong puts two nodes on one id,
which surfaces at a boundary assert far from the site, if at all. Freshening removes the decision
rather than answering it.

`assert_unique_node_ids` enforces uniqueness at every pass boundary in `compile_program`:
post-lowering, -inline, -transact, -letrec-run, -desugar, -as-of-read, -lambda-elim, -planning,
gated on `cfg!(any(debug_assertions, test))`. The walk is `O(nodes)` per boundary and compiles out
of a release build, along with the leak checks (`assert_leaks_clean` is gated the same way, so
nothing enforces either property in release). The lineage fold that produces the release-critical
projection — [The collapse](#the-collapse) — stays always-on. A boundary check states a property of
the tree rather than of the pass that produced it, so reordering the passes leaves the checks where
they are and still bounds every pass between two of them. A clean run is therefore evidence about
the boundaries, not about any individual pass.

### Walking the ids

Three walks answer three questions.

| Walk | Question | Domain |
|---|---|---|
| `assert_unique_node_ids` | may two live nodes share an id? | children |
| `collect_tree_ids` | which ids must the lineage fold account for? | children, plus refinement predicates |
| `uniquify::collect_node_ids` | did a `PredMemo` rebuild drop or re-mint an id? | the same, as a multiset |

`collect_tree_ids` reaches a predicate through a type slot, a `user_annotation`, or a `Cast` target.
It is the operative definition of what the fold must explain: the leak classes and every
`SourceProjection` enumerate from it, so a node it returns is a node the fold explains or reports as
a leak. A refinement predicate is program text the user wrote — `[x for x in xs if x > k]` puts `x >
k` in one — so it earns the same attribution as any other node. Lowering sweeps a finished predicate
through `LoweringContext::tag_predicate`, which is what makes a guard error resolve to a caret.

That sweep is the predicate domain's **entry** crossing, and the only crossing that is recorded. A
predicate being rewritten (uniquify and inference rebuild them through a `PredMemo`) and a predicate
being raised back into the main tree (planning) both still mint under no recording. No boundary
check reads the ids they mint: the uniqueness walk stops at children, and the leak checks run only
at the lowering boundary, upstream of both crossings.

`uniquify::collect_node_ids` checks multiset preservation across uniquify's own `PredMemo` rebuilds,
which is where ids could be dropped or re-minted.

`Rc` sharing is load-bearing and constrains how recording may be done. One predicate term rides many
type slots as a shared `Rc`, and planning's compile memo is `Rc`-keyed, so splitting the sharing
compiles one predicate once per occurrence. Recording is therefore idempotent per id rather than per
slot the id is reached through: `lowering_predicate_leaf` skips an id already recorded, which also
stops a sweep replacing precise attribution with a coarse label. For the same reason a duplication
path may share a predicate `Rc` with its source rather than rebuild one (see
`design/type-inference.md`, "Sharing is an invariant, not an optimization detail").

### Duplication

Three primitives, chosen by what the copy denotes.

- **`clone`** — the copy is a *sibling*: same value, distinct identity, `annot(p) = annot(o)`. The
  default. Every re-minted node fires `on_copy`, so a freshen is captured as `Op::Copy`, the
  lineage step whose outputs mirror an origin's history
  ([The lineage model](#the-lineage-model-srcccllineagers)). Capture is live the moment a session is
  installed and a no-op before that; no call site needs to know which.
- **`clone_preserving_ids`** — the copy *is the same node*, so it keeps its ids. Sound because the
  copy is never reachable from a tree beside its source, and narrow: a `Subst` discharge template,
  which is not a tree node and is copied again at every read; a throwaway the normal path discards,
  such as a rollback copy or a scratch tree; and a test comparing trees across a pass. Not a way to
  silence a **leak**, the fold's report of a node whose history it cannot account for
  ([The collapse](#the-collapse)): an `Unexplained` or a `CopyOfUnknown` means a copy was made with
  no step open, or against an origin the log never recorded, which is a recording gap whose fix is
  to record the copy.
- **a copy at the occurrence's id** — the root takes an id the tree already holds and the interior
  freshens: substitution, and the one copy that shares an id. The replacement for a `Var(𝑥)`
  occurrence denotes what the occurrence denoted, the value of 𝑥 at that position, so attribution
  there is the occurrence's; N reads give N subtrees under N ids the tree already holds. One site,
  `Subst`'s compound-replacement arm in `as_expr_preserving`, which carries the alternative it is
  chosen over: recording the copy against the occurrence instead of sharing its id resolves to the
  same entry, at a death per occurrence and an ordering constraint on the record.

**Freshen at placement, not at construction.** Most passes build intermediate structures — guard
vectors, path conjunctions, per-branch environments — whose entries are aliased and then copied into
the output. Placement is where a copy's multiplicity is known; freshening earlier assumes an answer,
and the three outcomes carry different costs.

- **Moved** into the output: no cost. The output node holds the fresh id, and its parent is the
  original.
- **Copied again** into the output: a defect the *lineage* fold catches, not the uniqueness walk.
  The intermediate copy is stranded, so the placed copy's `Op::Copy` names an origin no node holds,
  walking `parents` for a span dead-ends, and the fold reports `Leak::CopyOfUnknown`. Freshening the
  substitution engine's `Subst`-resident templates produces exactly this.
- **Dropped**: one spent id and one row no query reaches. No check reports it — both leak checks
  enumerate from the tree, there is no produced-side check (below), and a node absent from the tree
  is outside `assert_unique_node_ids`. Construction is the only constraint: `new` mints and records,
  `preserve` carries.

**A term crossing out of the predicate domain must not land aliased ids.** The uniqueness walk does
not reach predicate interiors, so a pass lifting one into the main tree owes a freshen at the point
of entry — `planning::iterate`'s `fn_of_bare_predicate` lift does exactly that. A lift that
*rebuilds* the term is already safe: `planning::groupby`'s key extraction goes through
`lambda_elim::run`, which re-mints every node. The requirement is that nothing aliased arrives;
rebuilding is one mechanism that satisfies it. `groupby_recognition_lifts_the_key_without_aliasing`
pins the property at the group-by site, so an elim that started preserving ids fails there rather
than at a boundary. The `iterate` lift has no such test.

## The lineage model (`src/ccl/lineage.rs`)

Recording is a **byproduct of performing a rewrite**, never a post-pass diff. As
a pass runs it appends `RewriteStep`s to a `LineageLog`:

- `Op::Transform { consumed, produced }` — inputs vanish, outputs appear (empty
  `produced` = discard; an id in `consumed ∩ produced` survives while absorbing).
- `Op::Copy { origin, produced }` — outputs mirror `origin`'s lineage (freshened
  duplicates); silent on the origin's own fate.

**`Pass`** names the compiler stage that produced or rewrote a node (`Lower`, `Uniquify`, `Inline`,
`Desugar`, `Transact`, `Letrec`, `Mono`, `LambdaElim`, `Planning`). It lives in the lineage data, as
each step's `via`, and never in a type.

Each step *separately* carries a `blame` set (the upstream ids the outputs
attribute to — **not** the same as `consumed`), a `nature` (the trinary fidelity
axis `Source` / `Expansion` / `Machinery`), and a stable `label`. `consumed`
drives fate/leak accounting; `blame` drives span resolution; the two are never
mixed. `Nature::Source` — the root of a lowered source expression — is emitted
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

Both checks enumerate from the **tree**. There is no third check on the *produced*
side — "every id a step refinements to produce is held by some node" — because
legitimate shapes violate it.

Uncurrying `def f(x, y)`
builds one `__arg_tuple_0.0` projection template and substitutes a freshened copy
of it at each `x`; every copy's root carries that occurrence's own id, so the
template's own root id is tagged and then held by no node. The read-your-writes
values the mutability phases keep in a substitution `env` work the same way. An
id retired like that leaves no trace — a *consumed* id shows up in the fold as
absence from `roots`, but a replaced one looks exactly like a live node the check
cannot see. Saying it explicitly means emitting the discard the model already
has, `Transform { consumed: [id], produced: [] }`, which neither site does today.

Construction closes the gap the check would have watched: a node is built either
by `Expr::new` (mint, recorded) or `Expr::preserve` (carry an existing
id, nothing recorded), so an id cannot be minted and then discarded.

The fold is in tree; **planned** is its use at the inspector's two pane
boundaries, which needs the pass logs above.

## The seam (`src/ccl/context.rs`)

- **The lowering log + fold.** Lowering records a `LoweringLog` under an
  always-on `RecorderSession::lowering()` (installed in every build across
  `lower_stmts`, drained before the first pass session). It records at **leaf
  grain**: `tag_source` / `tag_image` / `tag_machinery` are thin shims appending
  a single-node leaf `LoweringStep` (`Transform { consumed: [], produced: [id] }`,
  anchored at the nearest real span). Ordinary mints open **no** frame, so
  `on_mint` stays a no-op on the hot path; frames open only where ambient `Copy`
  capture is needed — uncurry's template discharge and the chained-comparison
  operand freshens, whose interior re-mints land as `Copy` LoweringSteps
  mirroring their origins (`copy_frame`, which declares that shape and so has no
  inert blame/nature arguments).

  **The rule for `Nature::Source` is structural: `Source` ⟺ the node is the root
  of a lowered `Spanned<ChlExpr>`.** It is decided in exactly one place — the
  `lower_expr` wrapper re-tags every lowered expression's root, last tag wins via
  the fold's re-image path — so no lowering arm makes a judgment call. An arm
  records its own nodes with `tag_image` (`"lower.image"`, an image of source
  text) or `tag_machinery` (`"lower.<rule>"`, manufactured plumbing), both at
  `Nature::Machinery`.

  The cost is deliberate and worth stating: a node can be a one-to-one image of
  something the user wrote and still not be `Source`, because it is not an
  expression *root* — a call's callee `Var`, each comparison of `a < b < c`, the
  projection of `x[i]`, and every statement-level image (statements are not
  `Spanned<ChlExpr>`s, so a statement has no `Source` node at all). The converse
  holds too: a comprehension lowers to a `Cast` wrapper the user never wrote, and
  as the expression's root that `Cast` *is* `Source`. What is lost from `nature`
  is preserved in the `label` — `"lower.image"` marks an image either way.

  **`label`, unlike `nature`, has no rule: it is per-rule judgment, and carries no
  cross-site guarantee.** Making `Source` structural moved the judgment call from
  `nature` onto `label` rather than removing it, and the disagreement moved with
  it: an `ExprStmt` at a statement's span is `"lower.image"` at five sites and
  `tag_machinery(…, "lower.stmt_seq")` at nine — the same node kind in the same
  span role, tagged both ways. So the guarantee is stated weakly on purpose.
  `"lower.image"` means *the rule that minted this node considered it an image*,
  and nothing more; no consumer may read it as a cross-site classification. A
  consumer needing "this has a 1:1 source construct" needs a datum that
  guarantees that, and none exists yet.

  **The whole nature/label taxonomy is provisional.** Nothing branches on it
  today, which is precisely why it drifted into two disagreeing rules in the first
  place, and why a third of this doc's history is spent re-deciding it. Expect it
  to change — most plausibly `nature` collapsing to what is decidable, with a
  finer taxonomy recomputed by a label-keyed remap — as the inspector's real
  consumption shows which distinction is load-bearing. Treat both axes as
  unstable until then.

  At the lowering→pipeline handoff (before uniquify and inference, so the release
  `InferError` read timing is unchanged) `collapse_lowering` folds the log
  **once** into the always-on **lowering projection** (`NodeId →
  SourceAttribution`, covering every id `collect_tree_ids` enumerates, refinement
  predicates included). This is the degenerate lowering case of `collapse`
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
