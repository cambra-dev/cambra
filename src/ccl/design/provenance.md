# Provenance — node identity and source attribution

Provenance relates compiler nodes to their inputs and source spans. `src/ccl/provenance.rs`
defines node identities, recording, tables and folds. `src/ccl/context.rs` installs the sessions;
`src/ccl/panes.rs` declares retained snapshots and the relations between them.
See [The seam](#the-seam) for pipeline integration and
[Operator conversion](#operator-conversion) for operator identities.

Unmarked sections describe the implementation. **Planned** marks proposed features.

## Mechanism at a glance

Expression nodes and operators carry `NodeId`s. A rewrite that preserves a logical node keeps
its identity; a duplicate receives a fresh identity. The [identity rules](#node-identity) define
which copies may preserve IDs and how shared predicate terms are checked.

A [recording](#the-recorder) names the node being rewritten. Construction hooks capture new
nodes and copies under the innermost recording. The [table](#the-provenance-model) stores one
row per produced ID, with ancestry, additional attribution and a rewrite tag.

[Folding](#the-fold) selected phases produces a node relation, source attribution, deaths and
recording leaks. Pane folds relate retained snapshots. `ProvenanceAudit` instead measures a
chosen span against live trees. [Gate and audit coverage](#gate-and-audit-coverage) specifies
the checks and switches; enabling capture and asserting the absence of leaks are distinct.

## Terms

| Term | Meaning |
|---|---|
| **pane** | A retained compiler snapshot: an expression tree or operator graph. An expression pane retains a full-tree clone; the operator graph is already retained by compilation. A pane **below** another is later in the pipeline, not deeper in a tree. |
| **walk start** | An operator-pane node with no incoming `value` subscription edge: a sink or share point where a consumer starts a walk. Both wire producer and consumer derive these from edges. A tree pane instead ships its expression root. |
| **boundary node** | An operator-pane node representing a sink, with a label and identity but no tiling. A data source is not a node; an `IterateExtent` reads its domain. |
| **recording** | The dynamic scope opened by `provenance::enter` and held by a `RecordingGuard`. The innermost recording captures a mint or copy. A recording site is the code location that opens it. |

## Node identity

`NodeId` is a `Copy` newtype allocated from a process-global atomic counter separate from the
counter for binder `Uid`s. `TypedExpr` stores it inline. Provenance rows and source attribution
are keyed by this identity; equal expression values may have different IDs.

`TypedExpr::PartialEq` compares `ty`, `node` and `user_annotation`, excluding `node_id`.
`TypedExpr` has no `Hash` implementation. `NodeId` has `Hash` and `Ord` for keyed collections
and the fold's mint-order traversal. Its numeric value is serialized as an inspector handle;
it is not stable across compilations or changes to allocation counts.

The **main tree** consists of nodes reachable through `walk_children`. Refinement predicates
contain additional expression nodes reachable through type slots. A predicate term may be shared
by several slots through one `Rc`; distinct live terms must not share IDs. Two terms with one ID
would collapse to one row and one source attribution. [Walking the ids](#walking-the-ids) specifies
the different traversal rules for these two domains.

`Expr::new` mints an ID and reports it to the recorder. Ordinary `Clone` freshens each expression
node it copies and reports its origin; type-slot predicates retain their `Rc` sharing.
The explicit preserving operations and diagnostic-only exceptions are specified under
[Duplication](#duplication).

`NodeId::PLACEHOLDER` is zero; the counter starts at one. `Default`, `mem::take` placeholders and
diagnostic throwaways use this sentinel without recording a birth. It must not persist in the
main tree; the boundary check asserts that condition in debug/test builds.

`Phase` identifies the compiler stage in a row's `via` field. Its declaration order is pipeline
order, which phase-range queries use. A phase identifies where a rewrite runs, not the module
containing its implementation: `AsOfRead`, for example, is implemented in `transact_phase`.
`PANES` in `src/ccl/panes.rs` assigns phases to snapshot intervals.

### Walking the ids

`collect_tree_ids` enumerates the main tree and refinement-predicate interiors. It uses
`walk_type_slots`, including user annotations and `Cast` targets, and recursively visits the
predicates' own types. This is the ID domain used by expression-pane folds and source projections.
`collect_main_tree_ids` excludes predicates and supports the narrower audit mode.

`assert_unique_node_ids` checks the same two domains with different sharing rules:

- `duplicate_node_ids` visits each main-tree occurrence without pointer deduplication. Repeated
  IDs are collisions.
- `predicate_id_collisions` collects one ID set per distinct predicate `Rc`. It reports IDs
  shared by distinct predicate terms and IDs shared between a predicate and the main tree.
  Reaching one predicate through several type slots is permitted.

The predicate check compares sets across distinct terms; it is not a multiplicity check within
one predicate's ID set. Treating every type-slot occurrence as a distinct term would reject
permitted `Rc` sharing. The corpus test `distinct_predicate_terms_never_share_a_node_id`
also checks retained panes, including snapshots taken between pipeline boundary checks.

Predicate nodes require attribution when introduced, rewritten or raised into the main tree.
Lowering's `tag_predicate` sweeps a completed predicate through `lowering_predicate_leaf`.
That hook skips already-recorded IDs, preserving existing precise attribution when a shared term
is reached again. Inference records singleton-predicate construction against a literal site.

`PredMemo::rebuild` normally derives a fresh predicate under `predicate.rebuild`, naming the
original predicate as its parent. Replacing one `Refinement`'s `Rc` does not prove that the
original term is dead: another type slot may still hold it. `PredMemo::replacing` permits
id-preserving rebuilds only when the traversal replaces every occurrence. `uniquify` uses this
mode and separately checks ID-multiset preservation with `uniquify::collect_node_ids`; that walk
does not deduplicate by `PredicateId`.

Planning raises predicates through `fn_of_bare_predicate`, group-by key extraction and hash-join
key morphisms. A copied predicate keeps its own parentage through the copy hook, rather than
acquiring the enclosing rewrite site's parentage. The test
`both_raising_paths_attribute_the_predicate_to_the_predicate` covers both
`fn_of_bare_predicate` paths. In its slower path, the site's eta wrapper is consumed during
elimination and composes away as a transient.

Copies preserve predicate `Rc` sharing because planning memoizes compilation by that identity.
Rebuilding a separate predicate per occurrence would repeat compilation. The invariant and
memoization contract are specified in
[Sharing is an invariant, not an optimization detail](type-inference.md#sharing-is-an-invariant-not-an-optimization-detail).

### Duplication

Ordinary `TypedExpr::Clone` mints a new ID for each copied expression node and reports every
`(origin, fresh)` pair through `on_copy`. A recording writes each copy against its origin.
With no recording open, the copy has a fresh ID but no new provenance row; under an active phase,
the hook's debug coverage assertion detects that missing recording.

The explicit copying operations have different identity contracts:

- `clone` duplicates the value at fresh expression IDs. Its type slots share their predicates
  with the source through `Rc`; they do not duplicate those predicate terms.
- `clone_preserving_ids` retains every copied expression ID and emits no copy events. Source
  and copy must not become distinct occurrences in one reachable tree. Permitted uses include
  substitution templates, separately rooted pane snapshots, rollback/comparison snapshots,
  tests comparing a phase's input with its output, and copies that replace a borrowed source
  which is then dropped. A substitution template is not itself a live tree node; materializing
  a read gives that occurrence fresh identities. A snapshot remains a separate tree.
- `clone_at(id)` copies a subtree with the supplied root ID and ordinary cloning of its children.
  Substitution uses it to retain a replaced variable occurrence's identity while freshening the
  replacement's interior. Distinct occurrences retain distinct roots. Recording a wholly fresh
  copy against the occurrence could preserve attribution, but would also report the occurrence
  dead and require an ordering-compatible record.

`preserve(id, node)` constructs a node directly at an existing ID without minting or recording.
It defaults the type to `Hole` and the user annotation to `None`. A field-wise rebuild that must
retain those fields can carry the original `node_id` in its struct literal; exhaustive field
checking then prevents an omitted type or annotation from being silently defaulted.
Minting a root and overwriting its ID would leave a recorded birth that no node carries.

`clone_preserving_ids` is not a repair for an `Unrecorded` or `DanglingParent` leak. A duplicated
term needs a recording around the copy and a recorded origin. Preserving its IDs would instead
hide the missing recording and may create collisions.

`run_debug_check` is a separate diagnostic-only scope: clones preserve IDs and `Expr::new`
constructs a `PLACEHOLDER` throwaway. Nothing built in this scope may enter a live tree.
The scope prevents diagnostic work from shifting later allocation IDs and serialized fixtures.

Every duplicated arm freshens, including the first. Choosing an arm to retain the source ID by
position assumes that arm survives; later transformations may discard it.

Intermediate templates and per-branch environments may be copied several times before placement.
Freshening at placement records the identity of the occurrence that reaches the output. An
earlier freshening has three possible outcomes:

- Moved into the output: the placed node holds the fresh ID and names the original as its parent.
- Copied again: the placed copy names the intermediate ID. If that intermediate was not recorded
  and is not in the input tree, the fold reports `DanglingParent`. A recorded intermediate instead
  composes away. A template copied without an open recording must preserve its IDs. A copy under
  a recording may freshen: `Subst::discharge_env_in_place` and `discharge_env_in_binder` copy
  templates this way under their callers' recordings before materialization.
- Dropped: the ID and any recorded row may be unused. Uniqueness checks visit reachable nodes;
  there is no requirement that every recorded birth survive into an output tree.

A predicate lifted into the main tree must have fresh expression IDs because the predicate may
remain on its original type slot or be lifted at another site. `fn_of_bare_predicate` freshens
the placed term. Group-by key extraction uses `predicates::eliminate_lifted`, including lambda
elimination, before planning the lifted key. `groupby_recognition_lifts_the_key_without_aliasing`
checks the resulting IDs. The attribution test named above covers the iterate lift's parentage,
not a separate uniqueness assertion there. The required lowering passes are specified under
[Planning a lifted term](optimization.md#planning-a-lifted-term).

`compile_program` checks uniqueness after lowering and at the later boundaries handled by
`settle`. `assert_unique_node_ids` and `gate_leaks` return without asserting when neither
`debug_assertions` nor `test` is enabled. A passing boundary check establishes the invariant
for that checked tree, not for every intermediate tree built within the phase.

## The provenance model

A `ProvenanceTable` stores one row per produced `NodeId`. Recordings populate the table during
rewriting; a post-phase tree diff does not construct the rows.

| Column | Meaning |
|---|---|
| `parents` | Ancestry: IDs from which this node was produced. |
| `blame` | Additional attribution: IDs related to the product without an ancestry claim. |
| `tag` | An interned `RewriteTag` containing the producing `Phase`, `Nature` and `RewriteLabel`. |

The columns describe the product, not the later fate of an input. A parent or blamed node may
survive in the output tree. Naming a surviving node as a parent gives an overly broad ancestry
edge, not a death report. The fold reports deaths from the difference between input and output
ID sets.

One parent can describe either one product or several products with the same parent. Several
parents describe fusion. A pure insertion may have no parents if its blame column anchors it.
An in-place rewrite that retains its ID writes no new row; the fold can relate an unchanged ID
to itself.

The table stores no source spans. Attribution resolves through parents and then distinct blame
additions, using the available upstream projection. A blame edge can add a span absent from the
parents. For example, `mut_elim` can name a statement as the parent and blame the enclosing loop
keyword. The node relation retains the two edge labels so a consumer can distinguish ancestry
from related source material; [The edge labels](#the-edge-labels) specifies composition.

### Table access and write invariants

`parents` and `blame` return empty slices for an unrecorded ID; `tag` and `tag_id` return
`None`. An allocated or addressed ID need not have a row in this table. The backing store is
a `HashMap` with a separate tag-interning table. Paged or delta-encoded storage remains a
possible representation change, not the implemented layout.

`ProvenanceTable::record` debug-asserts three write preconditions:

- The produced ID has no previous row. Attribution has one rewrite tag and no join for two
  competing producers.
- At least one of `parents` or `blame` is nonempty.
- The produced ID is not one of its own parents.

The row insertion is unconditional; these checks are not release-build validation. Several
recordings may name the same input ID because they produce distinct output IDs. The same input
may also appear as a parent in later recordings.

`tag_in(id, phases)` exposes a row only when its producing phase is selected.
The fold must stop at an input pane's IDs rather than following their rows from earlier phases.
Private `rows_in` enumerates recorded rows in a phase set, not the process-wide ID key space.

`deaths(start, end, live)` returns sorted recorded IDs produced in the inclusive phase range
and absent from `live`; a reversed range triggers a debug assertion. This differs from the
fold's `input_ids ∖ output_ids`: the table query includes intra-span products later discarded,
while the fold can report the loss of an input node produced before the selected phases.

Predicate IDs use the same row representation. `PredMemo` records derived predicates against
their source terms; copies raised into the main tree keep their predicate origins.
The [predicate traversal contract](#walking-the-ids) specifies the required sharing.

### The recorder

`RECORDING_STACK` is a thread-local stack of open recordings.
`Expr::new` calls `on_mint`; expression cloning reaches `on_copy`.
Each hook captures into the innermost frame. A mint has that recording's named node and extra
consumed IDs as parents. A copy instead has its own origin as its sole parent and no added blame.
Naming blame on the enclosing recording therefore widens its minted products, not its copies.

A recording is opened before the local rewrite and held until its products have been built:

```rust
let _g = provenance::enter(named_id, "inline.beta", Nature::Machinery);
```

`named_id` identifies the input before rewriting; the guard does not inspect the output value.
This works for both consuming and in-place rewrites. An attempt that mints and copies nothing
writes no row. Nesting assigns each product to the innermost recording active when its hook runs.

Closing a guard first appends to an active `DerivationLog`, if present. It then routes the
captured products to the active lowering log, or otherwise to the active phase's table.
Without either sink, captured events produce no table or lowering rows.
A `TableSession` alone does not supply the phase or open a recording.

The installed scopes have different lifetimes:

| Scope | Installed state and lifetime |
|---|---|
| `TableSession` | One table for the compile when provenance capture is enabled. |
| `PhaseScope` | The ambient producing phase for the enclosed phase's recordings. |
| `LoweringSession` | The always-on lowering log, drained at the lowering handoff. |
| `DerivationSession` | A phase-local log for error attribution, also written when table capture is disabled. |

Session installation is non-reentrant, checked with debug assertions. A phase scope cannot open
while lowering's log is installed. A derivation session also excludes lowering. Guards clear
their installed state on drop, including ordinary unwinding.

The mint and copy hooks ignore `NodeId::PLACEHOLDER`. Outside lowering, they debug-assert that
an active phase has an open recording to capture each event. Without that phase, an uncaptured
event is permitted and writes nothing. The coverage assertion checks the open frame, not the
correctness of the node it names.

`RecordingGuard` provides two additional channels:

- `also_consumes(id)` adds an ancestor for minted products, supporting fusion. It ignores the
  placeholder sentinel. It is not a death declaration.
- `blame(ids)` adds related IDs whose spans augment the minted products' ancestry attribution.

Both methods require their guard to be innermost; a debug assertion checks its stack depth.
Drop has the same LIFO precondition. In release builds these assertions do not protect a caller
that addresses or drops the wrong frame.

`copy_frame(label)` opens a recording with no named node and `Nature::Machinery`.
It is for standalone duplication: each copy hook supplies the origin that the frame lacks.
It cannot capture consumed IDs or mints; `assert_copy_only` debug-asserts that restriction.
A rewrite that also creates nodes uses `enter` instead.
Under lowering, captured copies become `LoweringStep::Copy` entries; their folded attribution
mirrors the origin verbatim. Under a phase scope, each copy becomes its own table row.

Lowering leaf mints use `lowering_leaf` directly, supplying a literal source span.
`lowering_predicate_leaf` skips already-recorded IDs so a sweep does not overwrite precise
existing attribution. `fold_lowering` processes the log at the lowering handoff.
The distinct log and fold contracts are specified under [The seam](#the-seam).

`PANES` in `src/ccl/panes.rs` and the phase scopes opened by `compile_program` in
`src/ccl/context.rs` define the retained boundaries and the phases whose recordings each pair
folds. Lowering records leaf appends and copies through its separate log. Rewrite labels are
supplied at recording sites, not enumerated here.

Table capture is enabled by default and disabled by `CAMBRA_PROVENANCE=0` or a named audit span.
When enabled, pipeline boundaries install the phase scopes. Shared helpers record under their
caller's phase, not under a phase inferred from the helper's module or label.
A phase that produces no nodes writes no rows.

An audit selected by `CAMBRA_PROVENANCE_AUDIT` opens its own scope over the chosen span and
prints coverage and leak measurements on completion. Naming an audit disables ordinary pane
capture so the two modes do not install competing phase scopes.
See [Gate and audit coverage](#gate-and-audit-coverage) for endpoints and configuration.

### Where to open a recording

A recording names the node whose rewrite produces the captured material. It surrounds the
local rewrite, after recursive child work and early returns that abandon the rewrite.
If every recursive frame opens its own recording, an outer frame may surround recursion:
the inner frame captures its own products while it is active. Operator conversion uses this
pattern through `converting`; [Operator conversion](#operator-conversion) specifies it.

A rule-table wrapper can record every attempt:

```rust
fn ruled(label: RewriteLabel, expr: &mut Expr, rule: impl FnOnce(&mut Expr) -> bool) -> bool {
    let _g = provenance::enter(expr.node_id(), label, Nature::Machinery);
    rule(expr)
}
```

A declined rule costs a push and pop but writes nothing if it minted or copied nothing.
The recorder does not use the returned Boolean. A consuming traversal reads the input ID
before destructuring the node; the ID is sufficient to open the recording.

The recording's scope follows the attribution required by its products:

- A product replacing several constructs names their enclosing input node, not a synthetic
  stand-in minted only for attribution.
- A recording may name a node just produced by this phase, provided its creation was recorded.
  The fold then composes that intermediate ancestry.
- Arms with different `Nature` values open separate recordings on the same input ID.
  Each recording carries one nature and label and writes its own products.
- An expansion with products attributable to different source constructs opens nested recordings
  per construct. `mut_elim` records accumulator slots and feeds inside the enclosing loop.
  The outer recording retains only the products it builds outside those nested scopes.

An accumulator slot can represent several writes to one variable. Its recording names the first
write and blames later writes; all contribute attribution, but only the named write contributes
ancestry. Conversely, one product spanning several constructs cannot be divided into per-construct
products: a conditional feed's lambda over the loop body stays on the enclosing recording.

When an enclosing construct mints nothing, its source can still be blamed by its children's
products. An accumulator-free mutation loop uses `StmtSite::blamed_in` for that case.
A recording does not manufacture an ancestry edge merely to make the enclosing construct visible.

#### Choosing between `Expansion` and `Machinery`

`Expansion` identifies products that express the source construct's meaning.
`Machinery` identifies an implementation strategy or administrative transformation.
The choice is made at each recording site and carried into attribution.

`planning.groupby` is `Expansion`: its bucketize chain implements the meaning of `groupby`.
`planning.hash_join` is `Machinery`: an equality-refined comprehension admits that strategy,
with iteration and restriction as the fallback when recognition does not apply.
`lambda_elim.filter` is `Expansion` because the guard becomes a domain refinement;
algebraic simplification is `Machinery`.

`Nature::Source` is lowering-only and marks a lowered source expression's root.
The phase-table attribution helper debug-asserts that a phase row does not use it.
`planning_labels_carry_their_declared_nature` checks the group-by and hash-join labels.

An empty leak vector checks recording coverage, not attribution precision. A recording on the
program root can explain IDs while attributing them to the wrong source construct. Recording-site
correctness therefore needs source-specific tests as well as the fold's structural checks.

### The fold

`fold(table, phases, input_ids, output_ids, upstream_attr)` returns four products:

| Product | Meaning |
|---|---|
| `ProvenanceMap<NodeId, NodeId>` | Bidirectional, labelled relation from input IDs to output IDs. |
| `SourceProjection` | Available source attribution restricted to output IDs. |
| Deaths | Sorted `input_ids ∖ output_ids`, independent of the recorded rows. |
| Leaks | Sorted, deduplicated recording-integrity failures. |

Only rows tagged with a phase in `phases` participate. An input node's row from an earlier
phase is not followed: the relation stops at this fold's input boundary. Recorded intermediate
nodes compose away from the emitted relation when they are absent from the output.

An input ID with no selected row contributes an ancestry self-edge if it survives into the
output. Its attribution passes through unchanged. Re-minting a pass-through node instead
creates a new ID and records a rewrite, so a consumer cannot distinguish that case from other
rewrites by identity alone.

#### The edge labels

Each endpoint pair has one nonempty set of labels. A `parents` hop contributes ancestry;
a `blame` hop contributes relatedness without ancestry. Naming the same ID in both columns
produces one hop with both labels.

Path composition is defined by `EdgeLabels::then`:

- Ancestry is present only if both the accumulated path and the next hop have ancestry.
- Blame is present if either the accumulated path or the next hop has blame.

Alternative paths between the same endpoints union their labels. Thus a pair can carry both
labels, whether one hop has both or separate paths supply them. An ancestry-only self-edge
is the identity for path composition.

Unknown ancestry endpoints produce `DanglingParent`. Unknown blame-only endpoints contribute
neither an edge nor a leak. Source attribution likewise ignores unknown source IDs, but combines
known spans from both columns.

#### The fold is order-free

The table's row insertion order does not determine the result. Recordings flush when their
guards close, so an enclosing rewrite can write its rows after nested rewrites have written
rows for later products.

The fold uses these sets:

- Vertices: selected rows' IDs together with `input_ids`.
- Roots of a vertex: input IDs reachable through its parents or blame, with path labels.
- Attribution: upstream entries extended with each selected row's derived attribution.

Before the sweep, every vertex without a selected row is assigned itself as an ancestry root.
These are input-boundary nodes. Pre-seeding them permits a selected row to name an input ID
greater than its own ID, as can happen when operator conversion reuses an existing operator.

Selected rows are then processed in ascending `NodeId` order. A dependency whose upstream ID
also has a selected row must have a smaller ID than its product. The sweep debug-asserts this
condition for both parent and blame hops. Dependencies on pre-seeded input IDs need not satisfy
that numerical order. One row per product and this ordering requirement permit a single sweep;
monotone allocation alone does not validate every manually constructed row.

For a selected row `x`, the fold extends each upstream root's path label by the hop into `x`
and unions labels at common roots. A recorded vertex retains an entry even if its root map is
empty. This distinguishes known material with no input ancestry from an unknown output ID.

Label union is associative, commutative and idempotent; path composition distributes over it.
Together with unique rows and the dependency ordering, these properties make the relation
independent of row insertion order. Attribution also requires unique rows: competing rewrite
tags have no merge operation.

`sweep_metrics` counts vertices, distinct upstream hops per row and dependencies that violate
the selected-row ordering. Its `backward_edges` count is a count of edges, not vertices to revisit
or the cost of a hypothetical fixed-point algorithm.
`the_write_order_of_the_rows_does_not_change_the_fold` checks insertion-order independence.

#### Source attribution

A row's attribution combines spans from its parents in order, then from its blame IDs in order,
retaining the first occurrence of each span. Unknown source IDs contribute nothing.
The row's tag becomes the product's `rewritten` tag; it is not inherited from its parents.

An attributed node may have an empty span vector. This is distinct from an ID absent from the
projection. At the output boundary, the fold retains only entries for `output_ids`; it does
not create an entry for an output whose attribution is unknown.

`SourceAttribution::rewritten` is mandatory. `RewriteTag::direct_image()` represents a lowered
expression root with `{via: Lower, nature: Source, label: "lower.image"}`.
A preserved ID can carry that tag through later panes. A new phase row must not use
`Nature::Source`; `attribute` debug-asserts the restriction. Wire encoding is owned by
[The inspector consumers](#the-inspector-consumers-srcinspector_model), not the fold.

#### Recording leaks

The two leak classes identify where missing recording becomes visible:

| Leak | Detection |
|---|---|
| `Unrecorded { output }` | An output ID is neither an input ID nor the product of a selected row. |
| `DanglingParent { parent }` | A selected row names an ancestry ID absent from the input and selected products. |

`DanglingParent` is checked while visiting every selected row, including rows whose products
do not survive into the output. `Unrecorded` is checked only for output IDs. A missing mint
can therefore cause either class or both, depending on whether it survives or is named by
another row. Neither class alone identifies the missing recording site.

Zero `Unrecorded` entries do not prove that every mint was recorded: an unrecorded intermediate
may have been discarded or may appear only as a dangling parent. Likewise, zero leaks establish
neither precise attribution nor correctness of the rewritten program.

Leaks are deduplicated by class and ID, so several rows naming one unknown parent produce one
`DanglingParent` entry. Deaths are a separate product, not an error. Duplicate live IDs are
checked by the tree-identity checks under [Node identity](#node-identity), not by the fold.

There is no requirement that every recorded product survive. A substitution template can be
recorded, copied into several occurrences and then discarded. Its row still explains the
copies. Unused rows are permitted; a row with an unknown parent is still checked even when
its product is unused. Write-time row preconditions are specified under
[Table access and write invariants](#table-access-and-write-invariants).

`fold_lowering` uses a sequential log rather than this phase-filtered table algorithm.
Its last-write-wins attribution and copy ordering are specified under [The seam](#the-seam).

### Gate and audit coverage

The leak classes above can only be asserted zero where the phases in between
record, which is what fixes both the audit spans and the set of gated pane pairs.

An audit's endpoint is **chosen**, because a span running past the last
instrumented phase counts everything the uninstrumented tail mints as a defect — a
number that cannot reach zero however correct the recording is, which makes the
audit read as a broken gate rather than a measurement. Every phase that rewrites
expression nodes now records, so the `full` span reaches the end of the pipeline,
`post-inference..join-planned`. Operator conversion is past it and has no node
identity to measure against.

**The same discipline governs the gate.** `CAMBRA_PROVENANCE_GATE=1` makes *every*
compile fold every pane pair and gate the leak classes, so the gate's corpus
becomes whatever the caller compiles — point it at the test suite and it covers
every program there instead of the handful `context.rs`'s `corpus()` lists. That
sample is what let two recording gaps live: `transact_phase` calling
`mut_elim::fold_induction_loop` with nothing recording, and `flatten_spine`'s
value-position writer hoist. Both are shapes the listed programs do not have. CI runs with it on; it costs about 4% of the test step.

It gates `gated_pane_pairs()`, which is now every pair: the leak classes hold at
zero from the lowering handoff to the end of the pipeline over whatever the
caller compiles.

**Move the endpoint when a phase becomes instrumented, in the commit that
instruments it.** The rule has no outstanding move left in the CCL pipeline; the
next one is operator conversion, which needs an identity first. Leaving an
endpoint behind understates coverage; moving it ahead reintroduces the
unreachable zero.

#### What gating every pair does not retire

A span is redundant with a gated pair when the pair covers the same phases, and
not otherwise. The `planning` span went for that reason: it ran
`recognized..join-planned` inside `post-lambda-elim → post-planning`, whose phase
list is `Planning` alone, so the wider gated pair measured the same phase and
keeping both invited trusting the wrong one.

`letrec` and `mutelim` stay because their pair bundles more phases than either
span isolates. Both sit
inside `post-inference → post-channelize`, over `Inline`, `Transact`, `Letrec` and
`Channelize`, and `mutelim` runs `post-transact..post-letrec`, isolating `Letrec`.
That pair holding at zero reports nothing about how much of `mut_elim` alone its
recordings explain, and neither endpoint is a pane, so no pair can be gated to ask
it. `ProvenanceAudit`, `CAMBRA_PROVENANCE_AUDIT`, `CAMBRA_PROVENANCE_PREDICATES`
and the audit clause in `provenance_capture_enabled` stay with them.

`PaneSpec::gated` stays for a separate reason. A pane may be issued at any point
during compilation, so the next pane added arrives with its pair ungated, and the
bit is what says so until every phase in the pair records.

## The seam

- **The lowering log + fold.** Lowering records a `LoweringLog` under an
  always-on `LoweringSession` (installed in every build across `lower_stmts`,
  drained before the first phase scope opens). It records at **leaf grain**:
  `tag_source` / `tag_image` / `tag_machinery` are thin shims appending a
  `LoweringStep::Leaf` (one id, anchored at the nearest real span). Ordinary
  mints record **nothing**, so
  `on_mint` stays a no-op on the hot path; a recording opens only where ambient
  `Copy`
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
  holds too: `groupby(c, key)` lowers to a `Lambda` the user never wrote, and as
  the expression's root that `Lambda` is `Source`. The comprehension phase's
  encoding is rooted at the `Comprehension` node's id, so the `Cast` or `Lambda`
  there keeps that node's `Source` entry. What is lost from `nature` is preserved
  in the `label` — `"lower.image"` marks an image either way.

  **`label`, unlike `nature`, has no rule: it is per-rule judgment, and carries no
  cross-site guarantee.** Making `Source` structural moved the judgment call from
  `nature` onto `label` rather than removing it, and the disagreement moved with
  it: an `ExprStmt` at a statement's span is `"lower.image"` at several sites and
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
  `InferError` read timing is unchanged) `fold_lowering` folds the log
  **once** into the always-on **lowering projection** (`NodeId →
  SourceAttribution`, covering every id `collect_tree_ids` enumerates, the ids
  inside refinement predicates included). This is the degenerate lowering case of
  `fold`, and the one fold that stays sequential: no input pane (leaves are pure
  insertions attributed from their literal anchor), no `ProvenanceMap` output, no
  upstream attr (a copy mirrors its origin's already-folded entry), and no
  one-record-per-id requirement (a re-image is a second entry for one id and the
  later tag deliberately wins). `Phase::Lower` is lowering-projection vocabulary
  only — it never tags a `ProvenanceTable` row, and the map between two panes
  stays a homogeneous `NodeId → NodeId` (the lowering projection constrains the
  **product**, not the producer).
  Every diagnostic a pass after lowering raises carries a blame node and resolves
  it against the projection (no fold, before any pane exists): the node's own
  entry, else the entry of a node it was derived from in the active
  `ProvenanceTable`, else that of a node enclosing it in the tree it was found
  in. `CompiledProgram` retains the projection as `lowering_projection`.
- **The lowering leak gate.** `fold_lowering`'s leak taxonomy replaces the
  retired `assert_seed_coverage` (and its `SEED_EMPTY_SPANS_ALLOWLIST`): an
  unrecorded lowering mint surfaces as `Leak::Unrecorded` (every output-tree
  node must be explained by a leaf or a copy), and a copy of an origin no earlier
  record covered as `Leak::DanglingParent`; a born-copied-discarded template id
  composes away (live but neither placed nor an output). The fold is always-on
  (its product is release-critical); the leak *checks* are debug/test-gated at
  the lowering handoff via `gate_leaks`. Orphaned projection keys are
  structurally impossible — the projection is *produced by* the fold, never
  mutated incrementally.
- **Materialization (cold, inspector-only).** `CompiledProgram::materialize_panes`
  folds `provenance_table` across every adjacent pane pair, restricting it by
  phase. `PANES` is the topology and declares it once: each entry names a pane,
  the phases that produced it from the pane before it, and whether its pair is
  gated. It returns a `SourceProjection` per pane and a `PanePair` per pair, each
  carrying that pair's map, deaths and leak vector. There is no catch-all bridge:
  a node is explained by a recorded row or it is not explained at all, and the
  gate is what says which. Materialization returns the leaks rather than
  asserting on them: a pair is clean only once every phase inside it records.

  The first entry is the anchor — it has no predecessor, and its projection is
  the lowering projection rather than a fold product. Read `PANES` for the
  current set rather than a list here; today it runs `pre-inference` through
  `post-planning`. Projections chain: each pair folds
  against the projection of the pane above it, so the first pair whose phases do
  not record leaves every pane below it with nothing to carry forward.
- **The pane leak gate.** `gate_leaks` asserts the whole `Leak` vector empty at
  the lowering handoff and at each gated pane pair. `Unrecorded` (an output node
  no capture explains) and `DanglingParent` (a parent edge to an id the fold has
  never heard of) are the only two classes. A death is not one of them: it is an
  ordinary product of any rewrite that replaces a node, carried on its own
  `PanePair::deaths` channel and never asserted on.

  **`PaneSpec::gated` says whether a pair is asserted to carry neither class.**
  Two checks read the same set at different widths:
  `pane_pair_folds_have_no_structural_leaks` over the programs `corpus()` lists,
  on every test run, and `CAMBRA_PROVENANCE_GATE=1` over whatever the caller
  compiles, which is strictly stronger because the wider corpus reaches shapes
  the listed programs do not.

  **The flag does not license a nonzero residue where it is false.** A leak is a
  bug wherever it appears; the flag says whether an assertion has been turned on.
  A pair goes ungated only while some phase inside it does not record, where the
  residue is a count of how little that phase records — a constant no correct
  recording elsewhere can drive down, so gating it would pin churn rather than
  catch a defect.

  Where it stands: **every pair is gated**, from `pre-inference → post-inference`
  down to `post-planning → post-conversion`. Capture is total across the whole
  pipeline.

### The derivation log

A phase run under a `DerivationSession` writes every recording that closes inside it to a
`DerivationLog` as well as to the table, in every compile. The session exists for a phase whose
mints inference can raise an error at, and whose mints no lowering-projection node encloses more
tightly than the construct they encode. Without it, a compile that captures nothing (`compile_to`)
resolves such an error to the enclosing construct's span or, when the blame node is outside the
tree, to no span at all. The comprehension phase (`ccl/comprehension.rs`) is the one phase run under
it.

`fold_derivation` folds the log into a projection over the lowering projection. A mint takes the
spans of the node its recording named and the recording's own tag; a copy mirrors its origin. The
steps are read in closing order, so a recording that names or copies a node an inner recording
minted finds that node already folded. A step whose named node or origin is in neither projection
contributes no entry. `Blame` consults this projection after the lowering projection and before the
table.

A recording under the session names no blame and consumes nothing beyond its named node, which
`log_derivation` debug-asserts. The fold attributes a birth to the named node alone, so either
channel would make it narrower than the table's attribution.

## Operator conversion

A pane may be issued at any point during compilation, and the panes run through
operator conversion: `Phase::Convert` records, `post-conversion` holds the
operator graph, and its pair is gated like every pair above it.

Four properties carry a pane past the last expression tree, each independent of
the others:

- An operator carries a `NodeId` drawn from the same counter as an expression
  node's (`OperatorBase`), so a row has something to resolve against.
- `PaneSpec::content` declares what a pane holds, and `CompiledProgram::pane_ids`
  is all the fold reads from a pane — never its content — so a pane holding an
  operator graph costs the fold nothing.
- `OperatorGraph` enumerates its own nodes, which is the output id set `fold`
  needs.
- A `CycleSlot`'s edge is recorded when the slot is filled. `subscribe` consumes
  the slot, so no traversal of a finished `CompiledProgram` can recover it.

Planning's raising crossing was an entry here and is resolved. The three sites
that lift a term out of a type — `planning/iterate`'s `fn_of_bare_predicate`
lift, the group-by key extraction, and the hash-join key morphisms — each keep the
predicate's parentage, because a clone's copy names the node it was freshened
from rather than the node the recording named. What had looked like a missing
re-rooting channel was the predicate ids being outside the enumerated domain,
which the binder-slot widening fixed;
`both_raising_paths_attribute_the_predicate_to_the_predicate` pins it.

## The inspector consumers (`src/inspector_model/`)

The inspector model is the only consumer of the folds' projections and maps; the
leak gate reads the same folds' `leaks` under `CAMBRA_PROVENANCE_GATE`, and a
release compile reads the lowering projection and nothing else. The model's own
reference is
[design.md](../../inspector_model/design.md), which owns the payload shape, the
usage model and the wire's versioning; what follows is what that layer reads out
of this one.

- `build_node_table` ships each attribution as it is stored: every span the
  attribution records, narrowest first, plus its `rewritten` tag
  (`{ via, nature, label }`). The tag serializes as
  `null` for a direct image — `Nature::Source` null-compresses at the emission
  site via `Nature::is_source`, and the consumer's validator guards that a
  `"source"` nature never actually ships. The wire carries no flat
  `Source`/`Derived`/`Synthetic` label string; the frontend formats the tag
  itself.
- `paneLinks` ship each pane-pair `ProvenanceMap` **dense** — self-edges included,
  no identity-edge filter — via `dense_edges`; the frontend only follows edges,
  never reconstructing them. An edge's label set stays here and does not reach
  the wire: resolution is bidirectional and transitive, so a consumer treats
  `descends` and `relates` alike, while `has_ancestry` drives leak accounting in
  this layer. Every edge endpoint is a live node id in the pane it points into,
  which
  `every_pane_link_endpoint_is_a_node_of_the_tree_it_points_into` pins at the
  producer and the consumer's validator re-checks on the shipped payload.
- Ids inside refinement predicates are endpoints like any other, so every walk
  that builds the payload descends into them
  ([Walking the ids](#walking-the-ids)).

The payload carries its own version in `meta.schema`. Nothing under `ccl/` reads
or depends on that number: this layer produces attributions and maps, and the
serialization shape is the inspector's contract with its frontend.
