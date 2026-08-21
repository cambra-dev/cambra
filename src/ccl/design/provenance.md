# Provenance — node identity and source attribution

This doc is the reference for how Cambra keeps an IR node's connection to the
source the user wrote.

`src/ccl/provenance.rs` holds all of it — the node id, the pass tag, the
recorder, the table, and the folds. `src/ccl/context.rs` is where the pipeline
opens the sessions and materializes the panes
([The seam](#the-seam-srccclcontextrs)).

**Status markers.** The the provenance model,
the recorder, some passes' adoption of it, the lowering projection, the ([`NodeId`-keyed table](#the-node-table)), and the fold over 
it — is in tree. **Planned** markers introduce designed but not yet built-features:
the inspector's consumption of the panes, adoption in further passes. A reader can tell the two apart by the
marker alone; unmarked prose describes code you can go read.

Adoption is complete across the five passes the two pane relations span — `Mono`,
`Inline`, `Transact`, `Letrec`, `Channelize`. The always-on gate holds at zero on
both relations over `context.rs`'s eleven-program `corpus()`; the whole-suite gate
covers the second relation only, for the reason below.

Three further sites record without reaching any table in a normal build, because
`compile_program` opens no `PassScope` around them: `simplify`,
`planning/iterate`, and `transact_phase`'s as-of-read rewrite. `lambda_elim`
records nothing at all, and operator conversion has no identity to record
against; see
[Known prerequisites for panes past `post-channelize`](#known-prerequisites-for-panes-past-post-channelize).

## Mechanism at a glance

Every node carries a `NodeId`, unique for the process and preserved across a
rewrite that keeps the node. Identity is the only thing the pipeline threads; the
rest is derived from it.

A rewrite **records**: it names the node it is about to rewrite, and every node
minted while that recording is the innermost open one takes the named node as a
parent. A site declares nothing else. It does not declare what it produced — the
produced side is discovered through the mint and copy hooks — and it does not
declare what it destroyed, because a death is the difference between the ids live
before and after.

Those rows accumulate in one `NodeId`-keyed table per compile, one row per node:
its `parents`, its `blame`, and an interned rule tag. Folding the rows of a chosen
set of passes turns the table into a relation between the trees at each end of
those passes, labelling every edge and reporting the ids it could not explain.

Two things fold. A **pane** is a retained snapshot the inspector displays,
materialized after a set of passes; the fold over the passes between two adjacent
panes is the **pane relation**, and the leak classes are asserted empty there on
every compile. A `ProvenanceAudit` folds between two chosen points against the live
tree rather than a snapshot, and measures instead of gating: it is how a pass's
recording is checked before any pane spans it, and how a suspected gap is located
without waiting for the gate to be extended.

Source spans enter at one place. Lowering projects every id `collect_tree_ids`
enumerates onto the span of the CHL it came from, and every later span is derived
by walking `parents` back into that projection.

## Terms

| term | what it is |
|---|---|
| **pane** | A retained AST snapshot the inspector displays, materialized after a set of passes. Each one costs a retained full-tree clone. |
| **pane relation** | What folding the passes between two adjacent panes produces: an id-to-id relation with labelled edges. The **durable, gated** artifact — the leak classes are asserted here. |
| **recording** | The scope `provenance::enter` opens over one rewrite, held as a `FrameGuard`. Every node minted while it is the innermost open one takes the node it names as a parent. Prose here says "a recording" for the scope, "the recording site" for the code location, and "records against X"; the guard is the RAII value that closes it. |
| **slot** | The node a recording names — `provenance::enter(slot_id, …)` — read off the tree *before* the rewrite runs. Normally a main-tree node. A predicate interior *may* be one, but work **on** a predicate is usually recorded against the predicate's own root, and work that *produces* one against the main-tree node whose type will carry it. |
| **predicate interior** | A `NodeId` on a `TypedExpr` inside a `Type::Refinement`'s predicate. Ordinary ids from the same counter, and inside the id domain a fold must explain: `collect_tree_ids` enumerates them. They are the one place explanation and uniqueness come apart — `assert_unique_node_ids` walks the main tree only, because a predicate interior may legitimately carry a main-tree id. See "Walking the ids". |

An audit's endpoint is **chosen**, because a span running past the last
instrumented pass counts everything the uninstrumented tail mints as a defect — a
number that cannot reach zero however correct the recording is, which makes the
audit read as a broken gate rather than a measurement. The `full` span therefore
ends at the last instrumented pane, `post-inference..post-as-of-read`, stopping in
front of `lambda_elim`.

**The same discipline governs the gate.** `CAMBRA_PROVENANCE_GATE=1` makes *every*
compile fold its pane relations and gate the leak classes, so the gate's corpus
becomes whatever the caller compiles — point it at the test suite and it covers
every program there instead of the handful `context.rs`'s `corpus()` lists. That
sample is what let two recording gaps live: `transact_phase` calling
`mut_elim::fold_induction_loop` with nothing recording, and `flatten_spine`'s
value-position writer hoist. Both are shapes the eleven listed programs do not
have. CI runs with it on; it costs about 4% of the test step.

It gates `gated_pane_relations()`, not both, for the reason above: the first
relation spans monomorphization and inference, and **inference's predicate
producers do not record**. `specialize_use` clones a definition per
instantiation, and the copies of a predicate term inside it row against interior
ids no pass produced. Over `tests/compilation_pipeline` that is 5 programs, all
UDF-with-filter or poly-wrapper shapes. Gating it today would report a constant,
not a regression. **Add it to `gated_pane_relations()` in the commit that makes
inference record**, the same way an endpoint moves.

**Move the endpoint when a pass becomes instrumented, in the commit that
instruments it:** to `post-lambda-elim` when the elim pass records, and to
`join-planned` when planning does. Leaving it behind understates coverage; moving
it ahead reintroduces the unreachable zero.

> This file is the reference for the shipped shape and wins on what the code
> does. The decision log behind it — the rejected alternatives, the measurements,
> and the adoption sequencing — is the `lineage-design` note under
> projects/program-inspector in the internal vault.

## Node identity

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
  `Uniquify`, `Inline`, `Channelize`, `Transact`, `Letrec`, `Mono`, `LambdaElim`,
  `Planning`). It lives in the provenance *data* (each row's `via`), never in a
  type.

### Walking the ids

**Two questions, two domains.** Keep them apart, because they used to have the
same answer and no longer do:

- **Explanation** — *which ids must the fold account for?* The main tree **and
  its refinement predicates**. `collect_tree_ids` enumerates both (children,
  plus the predicate reachable through a type slot, a `user_annotation`, or a
  `Cast` target) and is the operative definition: the fold's leak classes and
  every `SourceProjection` enumerate from it, so a node it returns is a node the
  fold must explain or report as a leak.
- **Uniqueness** — *may two live nodes share an id?* The main tree, and nothing
  else. `assert_unique_node_ids` walks children only, and deliberately: a
  predicate interior may legitimately alias a main-tree id at inline's blind
  spot, so a predicate-inclusive uniqueness walk would false-fire. Uniqueness
  *across distinct predicate terms* is asserted instead, by the corpus test
  `distinct_predicate_terms_never_share_a_node_id`.

Predicates were previously outside *both* domains — "carried, never checked" —
and free to alias their source's ids. Being in the explanation domain is a
deliberate change: a refinement predicate is program text the user wrote
(`[x for x in xs if x > k]` puts `x > k` in one), so it deserves the same
attribution as any other node. The "cost, accepted" this section used to record —
a guard error reporting without a caret, because its id was not in the lowering
projection — is exactly what explanation buys back.

Three crossings, and each one has to record:

1. **Entry** — a term is put *into* a predicate. Lowering's three
   `refined_data_fun` sites sweep the finished term through
   `LoweringContext::tag_predicate`; inference's `singleton_predicate` is
   recorded against the literal's own node, which is also the edge that links
   a singleton refinement back to the literal the user wrote.
2. **Transformation** — a predicate is rewritten. The rewritten term *replaces*
   the original in its `Refinement`, so it is the same logical node.
3. **Raising** — a predicate is materialized back into the main tree, which
   planning does. **Not yet recorded**, and not urgent here: those nodes are
   minted below the last pane, so nothing gates them. Lands with the planning
   commit upstack.

`Rc` sharing stays load-bearing and constrains how recording may be done. One
predicate term rides many type slots as a shared `Rc`, and planning's compile
memo is `Rc`-keyed, so splitting the sharing compiles one predicate once per
occurrence. Recording must therefore be idempotent **per id**, not per slot the
id is reached through: `lowering_predicate_leaf` skips an id already recorded,
which also stops a sweep replacing precise attribution with a coarse label.

`uniquify::collect_node_ids` is a third walk for a third question: a debug
tripwire asserting **multiset preservation** across uniquify's own `PredMemo`
rebuilds. It is neither explanation nor uniqueness, and it deliberately does not
dedup by `PredicateId`.

`distinct_predicate_terms_never_share_a_node_id` asserts the uniqueness property
predicates can satisfy: dedup by `Rc` pointer first, then require the ids of the
deduped set to be distinct. One term riding N slots is one term and shares its
ids with itself legitimately, while two *different* predicate terms sharing an id
is a defect. What it catches is a rebuild that preserves ids when the walk did not
reach every occurrence.

### Duplication

**Every pass yields unique `NodeId`s.** `Clone` is hand-written and
**freshens**: it mints a new `NodeId` for every node it copies and reports each
`(origin, fresh)` pair through `on_copy`. Two live nodes therefore cannot share an
identity by accident, and sharing one is something a site has to ask for.

That inverts the standing hazard rather than removing the reason for the rule. A
derived `Clone` copied `node_id`, so a bare `.clone()` of a subtree landing at two
live positions emitted two nodes with one identity — collapsing them to one entry
in every `NodeId`-keyed walk, giving the `SourceProjection` one attribution for
two nodes, and making a `NodeId → OperatorId` map non-functional. Uniqueness is
still what makes an id an *identity* rather than a label; it is just no longer
the call site's job to remember.

`assert_unique_node_ids` enforces it at every pass boundary in `compile_program`
— post-lowering, -inline, -transact, -letrec-run, -channelize, -as-of-read,
-lambda-elim, -planning — gated on `cfg!(any(debug_assertions, test))`. The walk
is `O(nodes)` per pass boundary and buys nothing in a release compile, where the
fold's leak classes cover the same ground. The check is a tree invariant and
encodes no pass order, so a reordered pass carries its check with it. It also
means a pass is implicated only at a boundary that looks at it: a clean run is
evidence about the gates, not about the passes between them.

Three shapes, and the choice between them is about what the copy *denotes*:

- **`clone`** — duplication, and the default. The copy is a *sibling*: same
  value, distinct identity, `annot(p) = annot(o)`. Every re-minted node fires
  `on_copy`, so an open recording rows the copy on the node it duplicated, and
  with none open nothing is written. No call site needs to know which.
- **`clone_preserving_ids`** — the copy *is the same node*, so it keeps its ids.
  Sound because no shape puts the source and the copy in one tree. Four shapes
  qualify: a `Subst` discharge template, which is never a tree node and whose
  every read mints its own identity; a retained pane snapshot, which exists to be
  joined to its neighbour by shared id; a snapshot taken for rollback or
  comparison, which the normal path discards; and a test comparing trees across a
  pass. The moves-out-of-a-borrow — where Rust forces a copy to get a value out of
  a map or a slice and the source is then dropped — rides along on the same
  reasoning. `TypedExpr::clone_preserving_ids` carries each with its sites.

  **Not a way to silence a leak.** An `Unexplained` or `ParentUnknown` means a
  copy was made with nothing recording, or against an origin the table never
  recorded. That is a *recording* gap, and the fix is to record around the copy.
- **`clone_at`** — root-carry, for substitution. The replacement for a `Var(𝑥)`
  occurrence denotes what the occurrence denoted — the value of 𝑥 *at that
  position* — so the occurrence keeps its own id while the interior becomes a
  fresh node-set. N reads give N distinct roots, so uniqueness holds without
  deleting the read sites from the output. `Subst`'s compound-replacement arm is
  the engine.

  The root is built **at** the carried id rather than minted and overwritten, so
  carrying costs nothing. The earlier `clone().re_root(id)` spelling minted a root
  id, fired `on_copy` for it and then discarded it — one stranded id and one
  stranded row per substituted occurrence. `re_root` is deleted; a field-wise
  rebuild that wants an existing id uses `preserve`, which mints nothing either.

**Freshen every copy, not all-but-one-by-position.** Which copy retains the
original id is a *fate* question, and keep-first guesses it wrong exactly when
position 0 is the copy that later dies. Freshening needs no knowledge of
downstream fates: the original either survives in place and keeps its id, or dies
and is consumed by the rewrite that dropped it. (Lowering's `fan_out_copy` is
keep-first on purpose — it is the pass that *mints* the originals, so position 0
is the source image by construction.)

**Freshen at placement, not at construction.** Most passes build intermediate
structures — guard vectors, path conjunctions, per-branch environments — whose
entries are aliased and then copied into the output. Placement is where a copy's
multiplicity is known; freshening earlier assumes an answer, and the three
outcomes carry different costs.

- **Moved** into the output: no cost. The output node holds the fresh id, and its
  parent is the original.
- **Copied again** into the output: a defect the gate catches. The intermediate
  generation is stranded, so the placed copy names an origin no node holds, a
  `parents` walk for a span dead-ends, and the fold reports `ParentUnknown`.
  Freshening the substitution engine's `Subst`-resident templates produces
  exactly this, and the pane-relation gate fails.
- **Dropped**: one spent id and one row no query reaches. No check reports it —
  both leak checks enumerate from the tree, there is no produced-side check
  (below), and a node absent from the tree is outside `assert_unique_node_ids`.
  Construction is the only constraint: `new` mints and records, `preserve`
  carries.

**A term crossing out of the predicate domain must not land aliased ids.**
Predicate interiors are outside the *uniqueness* domain (above) and may already
alias main-tree ids, so a pass that lifts one into the term tree owes a freshen at
the point of entry — `planning::iterate`'s `fn_of_bare_predicate` lift does
exactly that. A lift that *rebuilds* the term is already safe:
`planning::groupby`'s key extraction goes through `lambda_elim::run`, which
re-mints every node. That is the mechanism, not the requirement; the requirement
is that nothing aliased arrives, and each site pins it with a test.

## The provenance model

Recording is a **byproduct of performing a rewrite**, never a post-pass diff. As
a pass runs, every node it *produces* gets a row in the `ProvenanceTable`:

| column | what it holds |
|---|---|
| `parents` | the ids the rewrite consumed to produce this node: the node the recording named, or a fusion's whole consumed set |
| `blame` | the upstream ids the node is *related to but did not consume* — **not** the same as `parents` |
| `rule` | an interned `RewriteTag` — the `{via, nature, label}` triple |

**No column records a fate.** Both columns make a claim about the *product* — one
that it was consumed from these ids, one that it is about them — and neither says
whether any named id survived. Deaths come from one place only: `input_ids ∖
output_ids` across a pane relation. Nothing predicts a fate, so no pass can
over-claim one.

That silence is what makes *adopt-a-live-subtree* expressible: a rewrite that
keeps a node's id while minting a wrapper over one of its children must not be
read as declaring that node dead. It is equally what makes a fusion's parent set
safe — naming a survivor there costs an over-broad edge, never a phantom death.

The parents column's **cardinality** carries the rewrite's shape, and nothing
else about the shape is recorded: one parent is a 1:1 or 1:many rewrite (several
products each rowing on the same slot), several parents is a genuine fusion. A
node cannot be its own parent — an in-place rewrite that keeps its id is a
*preserve*, which records nothing, because identity here is referent identity
and the pane resolves it by shared id. The *closure* of `parents` is reflexive
even so, which is why a surviving node carries an ancestry self-edge
([The edge labels](#the-edge-labels)).

Attribution resolves through **`parents` ∪ `blame`** — parentage first, then
blame's distinct additions, so the span order is deterministic and blame is never
dropped when it names a node the parents do not. Blame is named at a handful of
sites, all in the mutability phases, so for almost every node this is simply the
spans of what it was made from, which is why walking the parent edges recovers a
source location at all.

**Two labels on one relation, which is why they stay separate columns.** Both
relate a node to other nodes; what differs is what the relation *asserts* — a
label on the edge, not the presence of one. `parents` says **descends from**;
`blame` says **related to, but not consumed**. Blame may name a node that
*survives* the rewrite, so welding it into `parents` would answer "what was this
made from" with a live node elsewhere in the tree. Both columns reach the
pane relation, each labelling the edges it contributes, and the leak audit reads
the ancestry label alone (see
[The edge labels](#the-edge-labels)).

Keeping the two apart is what lets a consumer render each faithfully — show the
blame, or prune it — rather than receiving one unlabelled edge set it
cannot take apart again. `mut_elim`'s `enter(stmt_id)` + `blame(for_id)` is the
shape: the products descend from the statement and are *about* the loop keyword.

`Nature::Source` — the root of a lowered source expression — is emitted **only by
lowering**; the fold's attributing helper carries a debug guard that no pass row
ever carries it.

Three invariants are properties of the *write*, and are asserted at
`ProvenanceTable::record`, at the site that would violate one, rather than in a
fold that only runs when a pane is materialized: **one row per id** (attribution
has no join, so a second claimant has no answer), **every row anchored through
some channel** (consumption or blame — a row with neither cannot explain where
its node came from), and **no node is its own parent**. All three are
`debug_assert!`s: `record` is the construction hot path, so what is gated is the
checking, never the row.

Lowering records separately, into a `LoweringLog` of `LoweringStep`s, because
its attribution channel is different in kind: a **literal source span attached
at construction** (lowering knows the source token it is imaging right there)
rather than a NodeId reference resolved later through the accumulating
projection. A `LoweringStep` is therefore not a row but one of the two shapes
lowering actually has — a **leaf mint** (one id, one span, a nature and a label)
or a **copy** (an origin and its freshened duplicates, mirroring the origin's
folded entry verbatim). Its log is folded **once** at the lowering handoff by
`collapse_lowering` into the always-on lowering projection (below).

### The recorder

An ambient thread-local stack of open recordings (`STEP_STACK`) plus an installed
sink, mirroring `infer_var::ACTIVE_ARENA`:

- `Expr::new` calls `on_mint` and the freshen helpers call `on_copy`, so a
  recording open around a rewrite *captures* the births and copies in its dynamic
  extent, innermost first. An empty stack means recording is off, which costs one
  emptiness check on the construction hot path.
- `TableSession` installs the table for a **whole compile**; `PassScope` names
  the pass rows are tagged with, for **one pass**. The two nest that way because a
  row's key is a process-unique `NodeId` and needs no pass set to disambiguate
  it, while a `RewriteTag` needs a pass the recording site cannot supply: the site
  knows its `label` and `nature` but not which pass is running, and the pass
  boundary that opens the scope knows exactly that.
- `LoweringSession` installs lowering's log instead, and is always-on.

**A site declares nothing.** It names the node it is *about to rewrite*:

```rust
let _g = provenance::enter(slot_id, "inline.beta", Nature::Machinery);
```

`slot_id` is read off the node before the rewrite runs; every id minted while the
guard is innermost gets a row naming `slot_id` as its parent. The pairing is
**(id before, minted during)**, not (value in, value out), so one recording fits
an `fn(Expr) -> Expr` rewrite and an `&mut Expr` one alike. A recording that mints
nothing writes nothing — that is the preserve case.

Two escape hatches are **inherent methods on the guard**, so a site can only ever
address the recording it holds (each debug-asserts it is the innermost open one,
turning a channel fired into a callee's recording or an enclosing recursion's into
a loud failure rather than a silent misattribution):

- `also_consumes(id)` — genuine fusion (many:1), the only thing that puts a
  second parent on a row and the only place any id is named at record time.
- `blame(ids)` — nodes this rewrite is **related to but did not consume to
  produce** its outputs. Attribution unions them with the parents; the pane
  relation carries them as *blame* edges. Blame is named at a handful of sites,
  all in the mutability phases, so `parents` alone is what recovers a source
  location for almost every node.

`enter` is the only constructor a pass uses. `copy_frame` is the one recording
that names **no** node: uncurry's template-interior freshens and the compare-chain
operand freshens duplicate nodes with no slot being rewritten, and each captured
copy carries its own origin from the hook. A recording that names no node has
nowhere to attach a mint or a consume, which `OpenStep::assert_copy_only`
enforces.

**Where recordings are open today.** Lowering's leaf appends and copy sinks, plus
recordings inside the two pane relations: `infer/solve` (`mono.specialize`,
`mono.coalesce_let`), `infer/emit` (`infer.lit_singleton`), `inline`
(`inline.alias`, `inline.udf`, `inline.beta`), `mut_elim` (`letrec.loop`,
`letrec.bare_write`, `letrec.hoist_writer_body`, `letrec.terminalize_write`),
`transact_phase` (strip, unwrap block, writer, commit record, history binding,
key rebind, key-init stash, carrier, the cross-domain and await-final rules), and
`channelize` (`channelize.cluster`, `channelize.defer_lift`,
`channelize.defer_collapse`). Two shared helpers record under whichever pass
scope is open around them: `subst` (`subst.vacuous`, `subst.transport`,
`subst.force_refinement`) and `ccl_utils`' `PredMemo::rebuild`
(`predicate.rebuild`).

Three sites record **below** `post_channelize_ir`, so no pane relation folds their
rows:
`simplify` (one combinator covering all thirteen `&mut` rule invocations, with no
rule-body edits), `planning/iterate`, and `transact_phase`'s as-of-read rewrite.
`compile_program` opens no `PassScope` around any of them, so their recordings
are inert in a normal build and land only under an audit a caller opens.
`CAMBRA_PROVENANCE_AUDIT=full` (`post-inference..post-as-of-read`) covers the
as-of-read rewrite; reaching `simplify` and `planning/iterate` needs
`CAMBRA_PROVENANCE_AUDIT=planning` (`recognized..join-planned`), which is what the
coverage figures below were measured with. `lambda_elim` records nothing, which
is what an audit's endpoint stops in front of.

### Where to open a recording

> **Name the node the product replaces, not the pass. One recording per rewrite,
> and split until every product has one.**

Every pass instrumented so far reduces to one of two forms.

**Rule-table pass → one wrapper combinator.** `simplify::ruled` wraps all
thirteen rule invocations, with **no rule body edited at all**:

```rust
fn ruled(label: RewriteLabel, expr: &mut Expr, rule: impl FnOnce(&mut Expr) -> bool) -> bool {
    let _g = provenance::enter(expr.node_id(), label, Nature::Machinery);
    rule(expr)
}
```

This works because a recording declares nothing, so wrapping every *attempt*
rather than every *firing* costs one push and pop when the rule declines. The
`bool` is never consulted: nothing needs to know whether the rule fired.

**Recursive traversal → one recording at each traversal entry.**
`planning::iterate` names the marker site it rewrites, and `transact_phase`'s
fourteen recordings are one per rewrite it performs. A recording takes only an
**id**, so a site that has already moved `expr.node` out can still open one —
read `expr.node_id()` before the destructure.

Three refinements the shapes above do not cover:

- **A product spanning several nodes** — the transaction carrier is what a set of
  scattered `with begin():` blocks and register declarations collectively became.
  Parent it on the **outermost** node it replaces, never on a synthetic stand-in.
- **The named node may be one the pass itself just minted**, provided it was
  minted under a recording: it is then produced by a pass the fold reads, and the fold reaches
  the original in two hops. Reading `slot_id` *before* the rewrite does not
  require it to be an input-pane node.
- **One entry serving arms of different `Nature`** — open a **second recording on
  the same node** inside the arm. The two write disjoint sets of rows on one
  parent, which is what two rewrites attributed to one node should look like. A
  recording carries one label and one nature for its whole extent by design.

**And a caution about what the gate can tell you.** `Unexplained == 0` is a
*coverage* property — was anything recording when a node was minted — not a
statement about where the recording pointed. Measured: replacing a pass's
carefully placed recordings with a **single** `enter` on the program root scores
identically on every leak class. Sites are placed correctly because the
attribution *is* the product; the number will not tell you when they are wrong.

`compile_program` opens one `PassScope` per pass — `Mono`, then `Inline`,
`Transact`, `Letrec`, `Channelize` — inside the single `TableSession` that spans the
whole compile, and retains the drained table as
`CompiledProgram::provenance_table`. A pass that rewrites nothing on a given program
writes no rows, which is the preserve case and not a gap.

### The node table

The recording, keyed by the node it describes. `ProvenanceTable` is
`NodeId → {parents, blame, rule}`: one row per **produced** node, written by
`OpenStep::flush_into_table` as each guard drops. `parents` are the ids the
rewrite consumed (the node the recording named; a fusion's whole consumed set),
`blame` the second edge kind, and `rule` an interned `RewriteTag` — the `{via,
nature, label}` triple is one value because the recording site and its enclosing
`PassScope` settle all three before a row is written, and there are on the order
of fifty distinct triples in the compiler.

Four properties, each load-bearing:

- **No `span` column.** Spans are derived by walking `parents` back to a node
  the lowering projection covers, which is a handful of hops and does not
  lengthen as programs grow. Storing spans per row would denormalize that onto
  every row ever minted.
- **"No row" is a legitimate state.** The key space is `NodeId`, and a `NodeId`
  can be addressed without ever having been recorded: an id minted by a pass that
  records nothing, or one whose producer lies outside the passes a fold reads.
  Reads answer empty / `None`; nothing panics.
- **Deaths are taken over rows, never over the key space.** `deaths(live)` is
  `recorded ∖ live`, and row enumeration is private so it cannot be taken any
  other way: a difference over addressed-but-unrecorded ids would report a death
  for every id no pass produced.
- **One table per compile, one pass scope per pass.** A row's key is
  process-unique, so no pass set is needed to disambiguate it. That is also why
  the pass reaches the write as an *ambient* fact: a recording site knows its
  `label` and `nature` but not which pass is running, so `PassScope::enter(pass)`
  carries it for the scope's extent and the tag is completed from it.

**There is deliberately no rewrite-kind column.** A 1:1 copy and a many:1 fusion
differ only in a claim about the origins' *fate*, and driver capture already
decided fate is never declared — it is the live-set difference. What is
load-bearing is the parents column's cardinality, which already carries 1:1,
1:many and many:1. A site that finds itself needing to know the kind is asking a
fate question that nothing here answers.

The backing store is a `HashMap`; the paged, delta-encoded form is a later pure
re-encoding behind the same accessors.

A row's `via` is what restricts the whole-compile table to one pane relation: an
id produced by a pass the relation does not span is, to that relation, an ordinary
un-produced id. The restriction is load-bearing — at the second relation a
`Mono`-produced input-pane id has a row, and walking through it would resolve
past the pane.

Predicate interiors are rows like any other. Lowering's projection covers every
id `collect_tree_ids` enumerates, and `PredMemo::rebuild` records a derived
predicate against the one it was built from. What is **not** recorded is planning
raising a predicate back into the main tree; see
[Known prerequisites for panes past `post-channelize`](#known-prerequisites-for-panes-past-post-channelize).

### The collapse

`collapse(table, passes, input_ids, output_ids, upstream_attr)` folds the rows
those passes wrote into:

- a `ProvenanceMap<NodeId, NodeId>` — a dense bidirectional node↔node relation
  (self-edge for every survivor), each edge carrying the **label set** described
  in [The edge labels](#the-edge-labels), and
- the output pane's `SourceProjection` (`NodeId → SourceAttribution`, where an
  attribution is `{ spans, rewritten: RewriteTag{via, nature, label} }`). The
  `rewritten` tag is **mandatory**: a direct image is
  `RewriteTag::direct_image()` (`{via: Lower, nature: Source, label:
  "lower.image"}`), never an absence. On the wire a `Source`-nature tag
  **null-compresses** to `rewritten: null` (via `Nature::is_source`), so the wire
  stays byte-identical to the retired `Option<RewriteTag>` encoding — both
  validators carry a debug guard that a `"source"` nature never actually ships.

Transients (born + consumed within the phase) compose away. A two-sided leak
audit (`Leak`) reports both sides of the live-set difference: an output with no
provenance (`Unexplained` — a capture defect) and an input absent from the output
pane (`Died` — the death report, data rather than a defect, since under driver
capture nothing declares a fate).

#### The edge labels

An edge carries a **set** of labels, not one, and the set is stored once per
`(upstream, downstream)` pair: a pair that is both ancestry and blame is one
edge asserting both, never two edges disagreeing about one pair. Two labels
exist, one per column — `parents` contributes *descends from*, `blame`
contributes *related to, but not consumed* — and a row naming one id in both
columns contributes a single hop carrying both.

Both are closed transitively, in the same sweep, and the closure composes
**weakest link**: a path is ancestry only while *every* hop on it is an ancestry
hop, and one blame hop anywhere makes the whole path blame. That is what
makes the label mean something at distance — you do not descend from something
you are merely related to two hops back — and it is why the sweep carries a label
alongside each root rather than running two closures whose results could not be
recombined afterwards. Paths meeting at one root union their labels, which is the
other way a pair comes to carry both.

The dense self-edge is **ancestry**: a surviving node descends from itself, which
is the identity of the weakest-link composition, so density needs no special
case.

The leak audit reads the ancestry label alone. `ParentUnknown` is a claim about
`parents` — an ancestry hop stopping at an id that describes nothing — while a
blamed id the fold never heard of contributes no edge and no class, the same
silence attribution keeps for a blamed id with no known spans.

#### The fold is order-free

`collapse` reads the rows as an **edge set**: a row contributes a hop `p → x` for
every `p ∈ parents(x) ∪ blame(x)`, labelled by the column(s) that named it, and
`roots(x)` maps each `u ∈ input_ids` with `u ⇝ x` to the label of the paths that
reach it. A node's annotation lives in the commutative monoid of labelled root
maps under union, which together with one row per id is what makes the result
independent of the order the rows were written in.

That is not a nicety: write order is **not** chronology, since rows are written
when their guard drops, so an enclosing rewrite's rows land after the rows of the
rewrites nested inside it.

Two invariants make the fold a single ascending-`NodeId` sweep — no fixed point,
no memoisation, no cycle guard:

- **one row per id**, and **no node is its own parent**, so no edge runs
  backwards out of a self-referential definition;
- **monotone minting** — `NodeId`s come from one process-global counter and a
  row's node is *captured* (via `on_mint`) after its upstream ids were read, so
  every id a row names is older than the node naming it — both columns alike
  (debug-asserted at the sweep).

Together, ascending `NodeId` *is* a topological order of the definition graph.
`sweep_metrics` measures the falsifier: a non-zero backward-edge count is exactly
the number of vertices a sweep would have to revisit.

The leak taxonomy follows the set reading, and has three classes. `Unexplained`
is an output-pane id no row produced and the input pane does not hold. `Died` is
the input-pane set difference. `ParentUnknown` is a parent that is neither an
input-pane id nor produced by a pass the fold reads — **one** class for both edge
shapes, because a lone parent and one of a fusion's several are the identical
condition, and telling them apart would mean recording the rewrite's shape.

The classes that are properties of a *record* rather than of a fold live at
the write instead: one row per id, and every row anchored through consumption or
blame, are asserted in `ProvenanceTable::record` (see
[The provenance model](#the-provenance-model)). "Two rewrites claimed
one id's death" has no class at all — a fate claim is not something a row makes,
and an id appearing in two rows' `parents` is an ordinary shared ancestor.

`collapse_lowering` is **sequential**, and is the one fold that should be: its
leaf entries are appended at construction rather than when a guard drops, so its
log
genuinely is chronology, and its last-tag-wins re-imaging (`lower_expr` re-tagging
an arm's already-tagged root) is real semantics rather than an artifact. It also
has no ancestry to compose — lowering mints from scratch, so what would be a set
of input-pane roots per id degenerates to a plain live set.

Both checks enumerate from the **tree**. There is deliberately no third check on
the *produced* side — "every recorded id is held by some node" — because two
legitimate shapes would read as violations. Uncurrying `def f(x, y)`
builds one `__arg_tuple_0.0` projection template and substitutes a freshened copy
of it at each `x`; every copy's root carries that occurrence's own id, so the
template's own root id is tagged and then held by no node. The read-your-writes
values the mutability phases keep in a substitution `env` work the same way. An
id retired like that leaves no trace: it looks exactly like a live node the check
cannot see.

Construction closes the gap the check would have watched: a node is built either
by `TypedExpr::new` (mint, recorded) or `TypedExpr::preserve` (carry an existing
id, nothing recorded), so an id cannot be minted **unrecorded**. Minting one and
then discarding it stays possible, and costs the stranded row named under
"Freshen at placement, not at construction".

The fold runs over the inspector's two pane relations today; **planned** is the
inspector's consumption of what it produces.

## The seam (`src/ccl/context.rs`)

- **The lowering log + fold.** Lowering records a `LoweringLog` under an
  always-on `LoweringSession` (installed in every build across `lower_stmts`,
  drained before the first pass scope opens). It records at **leaf grain**:
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

  At the lowering→pipeline handoff (before uniquify/inference, so the release
  `InferError` read timing is unchanged) `collapse_lowering` folds the log
  **once** into the always-on **lowering projection** (`NodeId →
  SourceAttribution`, covering every id `collect_tree_ids` enumerates,
  refinement-predicate interiors included). This is the degenerate lowering case
  of `collapse`,
  and the one fold that stays sequential: no input pane (leaves are pure
  insertions attributed from their literal anchor), no `ProvenanceMap` output, no
  upstream attr (a copy mirrors its origin's already-folded entry), and no
  one-record-per-id requirement (a re-image is a second entry for one id and the
  later tag deliberately wins). `Pass::Lower` is lowering-projection vocabulary
  only — it never tags a `ProvenanceTable` row, and the inter-pane relation stays a
  homogeneous `NodeId → NodeId` (the lowering projection constrains the
  **product**, not the producer).
  Release `InferError` diagnostics read the projection one-hop (no fold, before
  any pane exists). `CompiledProgram` retains it as `lowering_projection`.
- **The lowering leak gate.** `collapse_lowering`'s leak taxonomy replaces the
  retired `assert_seed_coverage` (and its `SEED_EMPTY_SPANS_ALLOWLIST`): an
  unrecorded lowering mint surfaces as `Leak::Unexplained` (every output-tree
  node must be explained by a leaf or a copy), and a copy of an origin no earlier
  record covered as `Leak::ParentUnknown`; a born-copied-discarded template id
  composes away (live but neither placed nor an output). The fold is always-on
  (its product is release-critical); the leak *checks* are debug/test-gated at
  the lowering handoff via `gate_leaks`. Orphaned projection keys are
  structurally impossible — the projection is *produced by* the fold, never
  mutated incrementally.
- **Materialization (cold, inspector-only).** `CompiledProgram::materialize_panes`
  folds `provenance_table` across the two pane relations, restricting it by pass:
  `MONO_PASSES` bridges pre → post-inference; `CHANNELIZE_PASSES` (Inline, Transact,
  Letrec, Channelize) bridges post-inference → post-channelize. It returns the three per-pane
  `SourceProjection`s, the two pane-pair `ProvenanceMap`s, and each relation's leak
  vector. There is no catch-all bridge: a node is explained by a recorded row or
  it is not explained at all, and the gate is what says which. Materialization
  cannot assert its own gate — with `Died` as a payload the leak vector is a
  *product*, not an error channel — so it returns the leaks and callers gate.
- **The pane leak gate.** `gate_leaks` gates the lowering handoff and both
  **pane relations** on the *defect* classes: `Unexplained` (an output node no
  capture explains) and `ParentUnknown` (an ancestry edge to an id the fold has
  never heard of). The split lives on `Leak::is_defect`. `Died` is excluded by
  construction — it is the death report, and gating on it would be unsatisfiable
  now that no pass declares what it consumes.

  Where the gate stands: **zero on every gated class, at both pane relations,
  for every program in `corpus()`** — that being what
  `pane_relations_fold_with_no_structural_leaks` asserts, as a property rather
  than a pinned residue count. Capture is total over the adopted span: every
  output-pane node has an origin. The whole-suite gate
  (`CAMBRA_PROVENANCE_GATE=1`) is the wider corpus and the narrower relation — it
  holds at zero over every program the caller compiles, at the second relation
  only.

## Known prerequisites for panes past `post-channelize`

A pane may be issued at **any** point during compilation — the current adoption
point is an artifact of what has been built, not a statement about the design.
Three things block extending it, all acknowledged and none blocking the two panes
that exist:

- **`lambda_elim` records nothing, and re-mints** nearly every pass-through
  node, so a pane pair spanning it would have no id correspondence to join on.
  Its catch-all traversal arm carries a `TODO(preserve)`, and `planning/groupby`
  relies on that re-minting to launder predicate-interior ids it lifts out of a
  type — `groupby_recognition_lifts_the_key_without_aliasing` pins the reliance —
  so a preserve there owes `groupby` an explicit freshen.
- **Operator conversion has no identity.** `TileOperator` carries none and there
  is no `OperatorId`, so a pane after it has nothing to resolve against.
- **Planning does not record what it raises out of the predicate domain.** Three
  sites cross: `planning/iterate`'s `fn_of_bare_predicate` lift, the group-by key
  extraction, and the hash-join key morphisms. Each would record against its
  term-tree site, that being the node the raised material becomes, but the
  `on_copy` hook reports the *origin it freshened*, and no channel re-roots a
  captured copy onto the node the site named. Only `planning/iterate` records at
  all, and no pass scope covers it.

  Measured at `post-inference..join-planned`, when that was `full`'s span: over
  the 11-program corpus the residue was 1184 `ParentUnknown` edges and nothing
  else, every unknown parent a predicate-interior id of the input tree, and
  widening the audit's live set (`CAMBRA_PROVENANCE_PREDICATES=1`) took every gated
  class to zero. (The count is from before the endpoint moved and has not been
  re-taken.) That says the recording is total for the span and the narrow live
  set is what makes the crossing read as a leak. It says nothing about the two
  pane relations, whose passes rebuild predicates through `PredMemo` and are
  recorded there.

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
- `paneLinks` ship each pane-pair `ProvenanceMap` **dense** — self-edges included,
  no identity-edge filter — via `stage::dense_edges`; the frontend only follows
  edges, never reconstructing them, and reads each edge's label set to decide
  whether to render the blame or prune it. Both validators check that every
  edge endpoint is a live node id in its respective pane.

The snapshot payload carries its own version in `meta.schema`, owned by the
inspector crate along with the fixture corpus pinned to it. Nothing under
`ccl/` reads or depends on that number: this layer produces attributions and
maps, and the serialization shape is the inspector's contract with its
frontend.
