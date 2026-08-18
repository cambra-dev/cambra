# Provenance & lineage — node identity and source attribution

This doc is the reference for how Cambra keeps an IR node's connection to the
source the user wrote, through a pipeline that otherwise loses it (spans dropped
at lowering, monomorphization cloning subtrees, inline fanning UDF bodies out,
channelize rewriting defers, lambda-elim synthesizing combinators, planning
fusing clauses).

**Status markers.** The substrate — the identity primitives, the lineage model,
the recorder, the passes' adoption of it, the always-on lowering projection, the
`NodeId`-keyed table that is the sink
([The node table](#the-node-table-srcccllineagers)), and the pane-boundary fold
over it — is in tree. Everything a **Planned** marker introduces is designed but
not yet built: the inspector's consumption of the panes. A reader can tell the
two apart by the marker alone; unmarked prose describes code you can go read. Adoption is complete through `post-desugar`: every pass inside
the two pane boundaries brackets, and the gate holds at zero on both. It now
extends further — `lambda_elim` and `planning` bracket too, though no pane
boundary folds them yet. Operator conversion is the one pass below the span still
unadopted; see
[Known prerequisites for panes past `post-desugar`](#known-prerequisites-for-panes-past-post-desugar).

## Terms

Five words do most of the work here, and two pairs of them are easy to run
together. Pinned once, used consistently below.

| term | what it is |
|---|---|
| **pane** | One of the three retained AST snapshots on `CompiledProgram`: `pre_inference_ir`, `post_inference_ir`, `post_desugar_ir`. A pane is a *thing the inspector displays*. There are three, and adding one costs a retained full-tree clone. |
| **pane boundary** | The fold between two **adjacent panes** — `pre → post-inference` and `post-inference → post-desugar`. Produced by `materialize_panes`, which restricts the table by the boundary's passes. This is the **durable, gated** artifact: the leak classes are asserted here. |
| **window** | A set of passes a fold restricts the table by, and by extension the `LineageAudit` measurement span that opens one at an arbitrary point and folds at another, reading the *live tree* at each end rather than a retained snapshot. An audit is env-selected, and a **measurement, never a gate**. |
| **slot** | The node a bracket names — `lineage::enter(slot_id, …)` — read off the tree *before* the rewrite runs. Normally a main-tree node. A predicate interior *may* be one now that predicate ids are in the id domain, but work **on** a predicate is usually bracketed on the predicate's own root, and work that *produces* one on the main-tree node whose type will carry it. |
| **predicate interior** | A `NodeId` carried by a `TypedExpr` inside a `Type::Refinement`'s predicate. Real ids from the same counter, and **in the id domain**: `collect_tree_ids` enumerates them, so the fold must *explain* them. It does **not** follow that they are unique — `assert_unique_node_ids` still walks the main tree only. See "Walking the ids". |

The distinction that matters most: **a window may extend past the last pane, and
it may not extend past the last instrumented pass.** A window's endpoint is not a
pane and nothing in a normal build folds it, so a pass below `post_desugar_ir` can
be fully bracketed and still contribute to no gate — the current state of
`lambda_elim` and `planning`.

That freedom cuts both ways, so the endpoint is **chosen, and it is the window's
whole point.** An audit measures what the brackets explain, so a window running
past the last instrumented pass counts everything the uninstrumented tail mints as
a defect: a number that cannot reach zero however correct the recording is, which
makes the audit read as a broken gate rather than a measurement. The `full` window
therefore ends at the last instrumented pane — `post-inference..post-as-of-read`
today, stopping in front of `lambda_elim`, which records nothing because it
re-mints nearly every pass-through node.

**The same discipline governs the gate.** `CAMBRA_LINEAGE_GATE=1` makes *every*
compile fold its pane boundaries and gate the leak classes, so the gate's corpus
becomes whatever the caller compiles — point it at the test suite and it covers
every program there instead of the handful `context.rs`'s `corpus()` lists. That
sample is what let two recording gaps live: `transact_phase` calling
`mut_elim::fold_induction_loop` with no frame open, and `flatten_spine`'s
value-position writer hoist. Both are shapes the eleven listed programs do not
have. CI runs with it on; it costs about 4% of the test step.

It gates `gated_boundaries()`, not both boundaries, for the reason above: the
first boundary spans monomorphization and inference, and **inference's predicate
producers do not record**. `specialize_use` clones a definition per
instantiation, and the copies of a predicate term inside it row against interior
ids no pass produced. Over `tests/compilation_pipeline` that is 5 programs, all
UDF-with-filter or poly-wrapper shapes. Gating it today would report a constant,
not a regression. **Add it to `gated_boundaries()` in the commit that makes
inference record**, the same way an endpoint moves.

**Move the endpoint when a pass becomes instrumented, in the commit that
instruments it:** to `post-lambda-elim` when the elim pass records, and to
`join-planned` when planning does. Leaving it behind understates coverage; moving
it ahead reintroduces the unreachable zero.

> This file is the reference for the shipped shape and wins on what the code
> does. The decision log behind it — the rejected alternatives, the measurements,
> and the adoption sequencing — is the `lineage-design` note under
> projects/program-inspector in the internal vault.

## Node identity (`src/ccl/provenance.rs`)

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
  `Planning`). It lives in the lineage *data* (each row's `via`), never in a
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
  spot, so a predicate-inclusive uniqueness walk would false-fire. **Predicate
  uniqueness is not asserted at all today.**

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
   bracketed on the literal's own node, which is also the edge that finally links
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

**Open, and worth doing:** assert uniqueness *across distinct predicate terms* —
dedup by `PredicateId` first, then require the ids of the deduped set to be
unique. That is the uniqueness property predicates can actually satisfy: one term
riding N slots is one term and shares its ids with itself legitimately, while two
*different* predicate terms sharing an id is a real defect nothing currently
catches.

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
— post-lowering, -inline, -transact, -letrec-run, -desugar, -as-of-read,
-lambda-elim, -planning — gated on `cfg!(any(debug_assertions, test))`. The walk
is `O(nodes)` per boundary and buys nothing in a release compile, where the fold's
leak classes cover the same ground. A boundary check is a tree invariant and
encodes no pass order, so a reordered pass carries its check with it. It also
means a pass is implicated only at a boundary that looks at it: a clean run is
evidence about the gates, not about the passes between them.

Three shapes, and the choice between them is about what the copy *denotes*:

- **`clone`** — duplication, and the default. The copy is a *sibling*: same
  value, distinct identity, `annot(p) = annot(o)`. Every re-minted node fires
  `on_copy`, so an open frame rows the copy on the node it duplicated and no open
  frame records nothing; no call site needs to know which.
- **`clone_preserving_ids`** — the copy *is the same node*, so it keeps its ids.
  Sound because the copy replaces or shadows its source: the two are never both
  reachable from one tree. Two shapes qualify — a snapshot taken for rollback or
  comparison, which the normal path discards, and a test comparing trees across a
  pass — plus the moves-out-of-a-borrow, where Rust forces a copy and the source
  is dropped.

  **Not a way to silence a leak.** An `Unexplained` or `ParentUnknown` means a
  copy was made with no frame open, or against an origin the table never
  recorded. That is a *recording* gap, and its fix is a bracket.
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
  exactly this, and the boundary gate fails.
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

## The lineage model (`src/ccl/lineage.rs`)

Recording is a **byproduct of performing a rewrite**, never a post-pass diff. As
a pass runs, every node it *produces* gets a row in the `LineageTable`:

| column | what it holds |
|---|---|
| `parents` | the ids the rewrite consumed to produce this node — a bracket's slot, or a fusion's whole consumed set |
| `blame` | the upstream ids the node is *related to but did not consume* — **not** the same as `parents` |
| `rule` | an interned `RewriteTag` — the `{via, nature, label}` triple |

A row is **silent on its parents' own fate**. That silence is what makes
*adopt-a-live-subtree* expressible: a rewrite that keeps a node's id while
minting a wrapper over one of its children must not be read as declaring that
node dead. It is equally what makes a fusion's parent set safe — naming a
survivor there costs an over-broad edge, never a phantom death.

The parents column's **cardinality** carries the rewrite's shape, and nothing
else about the shape is recorded: one parent is a 1:1 or 1:many rewrite (several
products each rowing on the same slot), several parents is a genuine fusion. A
node cannot be its own parent — an in-place rewrite that keeps its id is a
*preserve*, which records nothing, because identity here is referent identity
and the pane resolves it by shared id.

Deaths are recorded by **nobody**: they are `input_ids ∖ output_ids` at the
boundary. Nothing predicts a fate, so no pass can over-claim one.

`blame` says nothing about any node's fate. Attribution resolves through
**`parents` ∪ `blame`** — parentage first, then blame's distinct additions, so
the span order is deterministic and blame is never dropped when it names a node
the parents do not. Blame is named at four sites in the whole tree, so for almost
every node this is simply the spans of what it was made from, which is why
walking the lineage recovers a source location at all.

**Two labels on one relation, which is why they stay separate columns.** Both
relate a node to other nodes; what differs is what the relation *asserts* — a
label on the edge, not the presence of one. `parents` says **descends from**;
`blame` says **related to, but not consumed**. Blame may name a node that
*survives* the rewrite, so welding it into `parents` would answer "what was this
made from" with a live node elsewhere in the tree. Both columns reach the
pane-to-pane relation, each labelling the edges it contributes, and the leak
audit reads the descent column alone (see
[The edge labels](#the-edge-labels)).

Keeping the two apart is what lets a consumer render each faithfully — show the
relatedness, or prune it — rather than receiving one unlabelled edge set it
cannot take apart again. `mut_elim`'s `enter(stmt_id)` + `blame(for_id)` is the
shape: the products descend from the statement and are *about* the loop keyword.

`Nature::Source` — the root of a lowered source expression — is emitted **only by
lowering**; the fold's attributing helper carries a debug guard that no pass row
ever carries it.

Three invariants are properties of the *write*, and are asserted at
`LineageTable::record`, at the site that would violate one, rather than in a
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
folded entry verbatim). Its log is folded **once** at the lowering boundary by
`collapse_lowering` into the always-on lowering projection (below).

### The recorder

An ambient thread-local frame stack (`STEP_STACK`) + an installed sink,
mirroring `infer_var::ACTIVE_ARENA`:

- `Expr::new` calls `on_mint`; the freshen helpers call `on_copy` — so a frame
  open around a rewrite *captures* the births and copies in its dynamic extent
  (innermost frame wins). Empty stack ⇒ recording off (a cheap emptiness check on
  the construction hot path).
- `TableSession` installs the table for a **whole compile**; `PassScope` names
  the pass a frame's rows are tagged with, for **one pass**. The two nest that
  way because a row's key is a process-unique `NodeId` and needs no window to
  disambiguate it, while a `RewriteTag` needs a pass and a frame cannot supply
  one: a bracket site knows its `label` and `nature` but not which pass is
  running, and the boundary that opens the scope knows exactly that.
- `LoweringSession` installs lowering's log instead, and is always-on.

**A site declares nothing.** It brackets the node it is *about to rewrite*:

```rust
let _g = lineage::enter(slot_id, "inline.beta", Nature::Machinery);
```

`slot_id` is read off the node before the rewrite runs; every id minted while the
guard is innermost gets a row naming `slot_id` as its parent. The pairing is
**(id before, minted during)**, not (value in, value out), so the same bracket
fits an `fn(Expr) -> Expr` rewrite and an `&mut Expr` one. A bracket that mints
nothing writes nothing — that is the preserve case.

Two escape hatches are **inherent methods on the guard**, so a site can only ever
address the frame it holds (each debug-asserts it is the innermost open frame,
turning a channel fired into a callee's frame or an enclosing recursion's into a
loud failure rather than a silent misattribution):

- `also_consumes(id)` — genuine fusion (many:1), the only thing that puts a
  second parent on a row and the only place any id is named at record time.
- `blame(ids)` — nodes this rewrite is **related to but did not consume to
  produce** its outputs. Attribution unions them with the parents; the lineage
  relation carries them as *relatedness* edges. Blame is named at four sites in
  the whole tree, so `parents` alone is what recovers a source location for
  almost every node.

`enter` is the only frame constructor a pass uses. The one frame with **no**
origin is `copy_frame`, lowering's copy sink: uncurry's template-interior
freshens and the compare-chain operand freshens duplicate nodes with no slot
being rewritten, and each captured copy carries its own origin from the hook, so
the frame needs none. A frame with no origin has nowhere to attach a mint or a
consume, which `OpenStep::assert_copy_only` enforces.

**Where frames are open today.** Lowering's copy frames, plus driver brackets in
`infer/solve` (`specialize_use`, `coalesce_generalized_let`), `inline`
(alias/udf/beta), `mut_elim` (`letrec.loop`, `letrec.bare_write`),
`transact_phase` (strip, writer, commit record, history binding, key rebind,
carrier, as-of read), `channelize` (the defer cluster), `simplify` (one combinator
covering all 17 `&mut` rule sites, with no rule-body edits), `lambda_elim` (its
two recursive entry points — the traversal keyed on the node in the slot, the
abstraction walk keyed on the lambda body node — plus a relabel of the filter and
value-`Case` arms), and every rewrite in `planning`: loop recognition (the
`LetRec` in the slot, plus a finer bracket per continuation read), the group-by
recognizer and the hash-join rewrite (each keyed on the term-tree site, never on
the predicate the pattern is read out of), predicate compilation (keyed on the
term node whose type slot holds the refinement), and the iterate/restrict chain.

`lambda_elim` and `planning` sit **below** `post_desugar_ir`, so no boundary
folds their rows today: `compile_program` opens no `PassScope` around them and
their brackets are inert in a normal build. They record only under a scope a
caller opens, and **not** under `CAMBRA_LINEAGE_AUDIT=full`, which stops in front
of `lambda_elim` (see "a window may not extend past the last instrumented pass").
Reaching them needs the window that spans them — `CAMBRA_LINEAGE_AUDIT=planning`,
`recognized..join-planned` — which is what the coverage figures below were
measured with.

### Where to put a bracket

> **Bracket the node the product replaces, not the pass. One bracket per
> rewrite, and split until every product has one.**

Every pass instrumented so far reduces to one of two forms.

**Rule-table pass → one wrapper combinator.** `simplify::ruled` wraps all
fourteen rule invocations, with **no rule body edited at all**:

```rust
fn ruled(label: RewriteLabel, expr: &mut Expr, rule: impl FnOnce(&mut Expr) -> bool) -> bool {
    let _g = lineage::enter(expr.node_id(), label, Nature::Machinery);
    rule(expr)
}
```

This works because a bracket declares nothing, so wrapping every *attempt* rather
than every *firing* costs one push/pop when the rule declines. The `bool` is never
consulted; nothing needs to know whether the rule fired.

**Recursive traversal → one bracket at each traversal entry.** `lambda_elim` has
exactly two, one per mutually-recursive entry point, keyed on different things:
`elim_lambdas_impl` on the node in the slot, `elim_lambda_impl` on the node being
abstracted over. `planning::plan_loops` has one on the `LetRec` it recognizes.
The bracket takes only an **id**, so a site that has already moved `expr.node`
out can still bracket — read `expr.node_id()` before the destructure.

Three refinements the shapes above do not cover:

- **A product spanning several nodes** — the transaction carrier is what a set of
  scattered `with begin():` blocks and register declarations collectively became.
  Parent it on the **outermost** node it replaces, never on a synthetic stand-in.
- **A slot may be a node the pass itself just minted**, provided that node was
  minted under a frame: it is then produced-in-window and the fold reaches the
  original in two hops. Four arms of `lambda_elim` rely on this. The rule that
  `slot_id` is read *before* the rewrite does not mean the slot must be an
  input-pane node.
- **One entry serving arms of different `Nature`** — open a **second frame on the
  same origin** inside the arm. The two write disjoint sets of rows on one
  parent, which is exactly what two rewrites attributed to one slot should look
  like. Not a workaround; a frame carries one label and one nature for its whole
  extent by design.

**And a caution about what the gate can tell you.** `Unexplained == 0` is a
*coverage* property — was any frame open when a node was minted — not a
correctness-of-slot property. Measured: replacing a pass's carefully placed
brackets with a **single** `enter` on the program root scores identically on every
leak class. Slots are placed correctly because the attribution *is* the product;
the number will not tell you when they are wrong.

`compile_program` opens one `PassScope` per pass — `Mono`, then `Inline`,
`Transact`, `Letrec`, `Desugar` — inside the single `TableSession` that spans the
whole compile, and retains the drained table as
`CompiledProgram::lineage_table`. A pass that rewrites nothing on a given program
writes no rows, which is the preserve case and not a gap.

### The node table (`src/ccl/lineage.rs`)

The recording, keyed by the node it describes. `LineageTable` is
`NodeId → {parents, blame, rule}`: one row per **produced** node, written by
`OpenStep::flush_into_table` as each frame closes. `parents` are the ids the
rewrite consumed (a bracket's slot; a fusion's whole consumed set), `blame` the
second edge kind, and `rule` an interned `RewriteTag` — the `{via, nature,
label}` triple is one value because a bracket site fixes all three at once, and
there are on the order of thirty distinct triples in the compiler.

Four properties, each load-bearing:

- **No `span` column.** Spans are derived by walking `parents` back to a node
  the lowering projection covers, which is a handful of hops and does not
  lengthen as programs grow. Storing spans per row would denormalize that onto
  every row ever minted.
- **"No row" is a legitimate state.** The key space is `NodeId`, and a `NodeId`
  can be addressed without ever having been recorded — every
  refinement-predicate interior is (see [Walking the ids](#walking-the-ids)). Reads
  answer empty / `None`; nothing panics.
- **Deaths are taken over rows, never over the key space.** `deaths(live)` is
  `recorded ∖ live`, and row enumeration is private so it cannot be taken any
  other way: a difference over addressed-but-unrecorded ids would report a death
  per predicate node in the program.
- **One table per compile, one pass scope per pass.** A row's key is
  process-unique, so no window is needed to disambiguate it. That is also why
  the pass reaches the flush as an *ambient* fact: a frame knows its `label` and
  `nature` but not which pass is running, so `PassScope::enter(pass)` carries it
  for the scope's extent and the flush completes the tag from it.

**There is deliberately no rewrite-kind column.** A 1:1 copy and a many:1 fusion
differ only in a claim about the origins' *fate*, and driver capture already
decided fate is never declared — it is the boundary set difference. What is
load-bearing is the parents column's cardinality, which already carries 1:1,
1:many and many:1. A site that finds itself needing to know the kind is asking a
fate question that nothing here answers.

The backing store is a `HashMap`; the paged, delta-encoded form is a later pure
re-encoding behind the same accessors.

A row's `via` is what restricts the whole-compile table to one boundary: an id
whose row lies outside a boundary's window is, to that boundary, an ordinary
un-produced id. The restriction is load-bearing — at the post-desugar boundary a
`Mono`-produced input-pane id has a row, and walking through it would resolve
past the pane.

**Planned** is admitting predicate interiors as rows — a *population* change,
not a schema change, since those ids already have addresses in the key space.

### The collapse

`collapse(table, window, input_ids, output_ids, upstream_attr)` folds the rows
`window`'s passes wrote into:

- a `LineageMap<NodeId, NodeId>` — a dense bidirectional node↔node relation
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
audit (`Leak`) reports both sides of the boundary difference: an output with no
lineage (`Unexplained` — a capture defect) and an input absent from the output
pane (`Died` — the death report, data rather than a defect, since under driver
capture nothing declares a fate).

#### The edge labels

An edge carries a **set** of labels, not one, and the set is stored once per
`(upstream, downstream)` pair: a pair that is both descent and relatedness is one
edge asserting both, never two edges disagreeing about one pair. Two labels
exist, one per column — `parents` contributes *descends from*, `blame`
contributes *related to, but not consumed* — and a row naming one id in both
columns contributes a single hop carrying both.

Both are closed transitively, in the same sweep, and the closure composes
**weakest link**: a path is descent only while *every* hop on it is a descent
hop, and one relatedness hop anywhere makes the endpoint related. That is what
makes the label mean something at distance — you do not descend from something
you are merely related to two hops back — and it is why the sweep carries a label
alongside each root rather than running two closures whose results could not be
recombined afterwards. Paths meeting at one root union their labels, which is the
other way a pair comes to carry both.

The dense self-edge is **descent**: a surviving node descends from itself, which
is the identity of the weakest-link composition, so density needs no special
case.

The leak audit reads the descent column alone. `ParentUnknown` is a claim about
`parents` — a descent hop stopping at an id that describes nothing — while a
blamed id the boundary never heard of contributes no edge and no class, the same
silence attribution keeps for a blamed id with no known spans.

#### The fold is order-free

`collapse` reads the rows as an **edge set**: a row contributes a hop `p → x` for
every `p ∈ parents(x) ∪ blame(x)`, labelled by the column(s) that named it, and
`roots(x)` maps each `u ∈ input_ids` with `u ⇝ x` to the label of the paths that
reach it. A node's annotation lives in the commutative monoid of labelled root
maps under union, which together with one row per id is what makes the result
independent of the order the rows were written in.

That is not a nicety: write order is **not** chronology, since a frame's rows are
written when the frame *closes*, so an enclosing rewrite's rows land after the
rows of the rewrites it contains.

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
input-pane id nor produced inside the window — **one** class for both edge
shapes, because a lone parent and one of a fusion's several are the identical
condition, and telling them apart would mean recording the rewrite's shape.

The classes that are properties of a *record* rather than of a boundary live at
the write instead: one row per id, and every row anchored through consumption or
blame, are asserted in `LineageTable::record` (see
[The lineage model](#the-lineage-model-srcccllineagers)). "Two rewrites claimed
one id's death" has no class at all — a fate claim is not something a row makes,
and an id appearing in two rows' `parents` is an ordinary shared ancestor.

`collapse_lowering` is **sequential**, and is the one fold that should be: its
leaf entries are appended at construction rather than at frame close, so its log
genuinely is chronology, and its last-tag-wins re-imaging (`lower_expr` re-tagging
an arm's already-tagged root) is real semantics rather than an artifact. It also
has no lineage to compose — lowering mints from scratch, so what would be a set
of input-pane roots per id degenerates to a plain live set.

Both checks enumerate from the **tree**. There is deliberately no third check on
the *produced* side — "every recorded id is held by some node" —
because it is not decidable against the node set the fold works over: lowering
tags the nodes inside a refinement predicate, but that set is `collect_tree_ids`,
the `walk_children` domain, which excludes predicate interiors, so every
predicate id would read as a violation.

Two legitimate shapes would read as violations too. Uncurrying `def f(x, y)`
builds one `__arg_tuple_0.0` projection template and substitutes a freshened copy
of it at each `x`; every copy's root carries that occurrence's own id, so the
template's own root id is tagged and then held by no node. The read-your-writes
values the mutability phases keep in a substitution `env` work the same way. An
id retired like that leaves no trace: it looks exactly like a live node the check
cannot see.

Construction closes the gap the check would have watched: a node is built either
by `TypedExpr::new` (mint, recorded) or `TypedExpr::preserve` (carry an existing
id, nothing recorded), so an id cannot be minted and then discarded.

The fold runs at the inspector's two pane boundaries today; **planned** is the
inspector's consumption of what it produces.

## The seam (`src/ccl/context.rs`)

- **The lowering log + fold.** Lowering records a `LoweringLog` under an
  always-on `LoweringSession` (installed in every build across `lower_stmts`,
  drained before the first pass scope opens). It records at **leaf grain**:
  `tag_source` / `tag_image` / `tag_machinery` are thin shims appending a
  `LoweringStep::Leaf` (one id, anchored at the nearest real span). Ordinary
  mints open **no** frame, so
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

  At the lowering→pipeline handoff (before uniquify/inference, so the release
  `InferError` read timing is unchanged) `collapse_lowering` folds the log
  **once** into the always-on **lowering projection** (`NodeId →
  SourceAttribution`, covering every `walk_children` node — refinement-predicate
  interiors stay outside). This is the degenerate lowering case of `collapse`,
  and the one fold that stays sequential: no input pane (leaves are pure
  insertions attributed from their literal anchor), no `LineageMap` output, no
  upstream attr (a copy mirrors its origin's already-folded entry), and no
  one-record-per-id requirement (a re-image is a second entry for one id and the
  later tag deliberately wins). `Pass::Lower` is lowering-projection vocabulary
  only — it never tags a `LineageTable` row, and the inter-pane relation stays a
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
  the boundary via `gate_leaks`. Orphaned projection keys are
  structurally impossible — the projection is *produced by* the fold, never
  mutated incrementally.
- **Materialization (cold, inspector-only).** `CompiledProgram::materialize_panes`
  folds `lineage_table` at the two pane boundaries, restricting it by pass:
  `MONO_WINDOW` bridges pre → post-inference; `DESUGAR_WINDOW` (Inline, Transact,
  Letrec, Desugar) bridges post-inference → post-desugar. It returns the three per-pane
  `SourceProjection`s, the two pane-pair `LineageMap`s, and each boundary's leak
  vector. There is no catch-all bridge: a node is explained by a recorded row or
  it is not explained at all, and the gate is what says which. Materialization
  cannot assert its own gate — with `Died` as a payload the leak vector is a
  *product*, not an error channel — so it returns the leaks and callers gate.
- **The pane leak gate.** `gate_leaks` gates the lowering boundary and both
  **pane** boundaries on the *defect* classes: `Unexplained` (an output node no
  capture explains) and `ParentUnknown` (a lineage edge to an id the window has
  never heard of). The split lives on `Leak::is_defect`. `Died` is excluded by
  construction — it is the death report, and gating on it would be unsatisfiable
  now that no pass declares what it consumes.

  Where the gate stands on a real corpus: **zero on every gated class, at both
  pane boundaries, for every program.** Capture is total over the adopted span —
  every output-pane node has an origin — and the corpus test asserts it as a
  property rather than pinning a residue count.

## Known prerequisites for panes past `post-desugar`

A pane may be issued at **any** point during compilation — the current adoption
boundary is an artifact of what has been built, not a statement about the design.
Three things block extending it, all acknowledged and none blocking the two panes
that exist:

- **`lambda_elim` re-mints** nearly every pass-through node, so any pane pair
  spanning it is vacuous. It carries a `TODO(preserve)`, and `planning/groupby`
  documents the same re-minting as load-bearing id-laundering, so the two
  interact and neither can be fixed alone.
- **Operator conversion has no identity.** `TileOperator` carries none and there
  is no `OperatorId`, so a pane after it has nothing to resolve against.
- **The predicate domain is unrecorded.** `PredMemo::rebuild` bare-clones and
  fires no hook, so a predicate interior's id is carried but never produced under
  a frame. That is what a *crossing* out of the domain runs into, and it is the
  whole of the residue at a window spanning planning: over the 11-program corpus
  the residue is 1184 `ParentUnknown` edges and nothing else, and every one of
  those unknown parents is a predicate-interior id of the input tree. (Measured
  at `post-inference..join-planned`, when that was `full`'s span; the count is
  from before the endpoint moved and has not been re-taken.)
  Three sites cross: `planning/iterate`'s `fn_of_bare_predicate` lift, the
  group-by key extraction, and the hash-join key morphisms. Each brackets on its
  term-tree site — which is the right slot, a predicate interior being nothing a
  pane enumerates — but the `on_copy` hook reports the *origin it freshened*, and
  no channel lets a frame re-root a captured copy onto its own slot.

  Admitting predicate interiors to the live set is what closes it: with the
  window's live set widened (`CAMBRA_LINEAGE_PREDICATES=1`), the same corpus
  scores zero on every gated class for every program, with the projection
  covering every output node. So for *this* window
  the ordering constraint no longer holds — the recording is total and the
  narrow live set is what makes it read as a leak. The measurement says nothing
  about the two pane boundaries, whose passes rebuild predicates through
  `PredMemo` and would still need the hook.

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
  edges, never reconstructing them, and reads each edge's label set to decide
  whether to render the relatedness or prune it. Both validators check that every
  edge endpoint is a live node id in its respective pane.

The snapshot payload carries its own version in `meta.schema`, owned by the
inspector crate along with the fixture corpus pinned to it. Nothing under
`ccl/` reads or depends on that number: this layer produces attributions and
maps, and the serialization shape is the inspector's contract with its
frontend.
