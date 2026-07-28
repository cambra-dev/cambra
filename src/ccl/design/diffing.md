# Program diffing — the shared/changed analysis

Cambra programs evolve, and the *diff between two versions* is meant to be a
first-class object the compiler and runtime can reason about: run two versions
concurrently, share storage and compute between them, and make the transition
denotationally precise. This document covers the analysis that everything else
is built on — deciding, for two compiled programs, which parts are **the same
computation** and where exactly they diverge — plus the semantic model the
analysis is a step toward.

Implemented by [`ccl/content_hash.rs`](../content_hash.rs) (the equivalence) and
[`ccl/diff.rs`](../diff.rs) (the correspondence). Neither is wired into
[`compile_program`](../context.rs) — the analysis is a library the versioning
work will consume, not a pipeline pass.

---

## Why the diff is semantic, not operational

Standard deployment treats a new version as opaque: old code stops, new code
starts, state migration is ad hoc. Cambra programs are pure functions of
time-indexed tilings ([mutability.md](mutability.md)), so both versions are
denotations over the same time domain and the diff between them is tractable at
the semantic level — it is *the set of points in the computation graph where the
denotations diverge*.

That buys three things:

- **Sharing.** Unchanged parts of the computation have the same inputs and the
  same code, so they can be one execution and one storage entry.
- **Retroactive change.** A branch point in the past is expressible in the same
  framework as one in the future; both are statements about which version's
  denotation applies at which commit timestamps.
- **Branching as the user story.** v1 and v2 are sibling branches of a shared
  history: old clients stay on v1, new clients move to v2, v1 eventually drains.

The nearest operational analogy is blue/green deployment with shared state,
lifted from infrastructure to program semantics.

### Versions as branches

Once v2 is proposed on top of v1 the commit-timestamp space is no longer one
total order but a tree rooted at the branch point `t_new`. Each branch has its
own commit-time space; the total-order claim holds *within* a branch. Readers
are version-tagged, and v2's store is defined piecewise: it agrees with v1's
below `t_new` and is defined by v2's body at or above it. Two distinct times
govern a version's life — `t_new`, the branch point (a property of the v2
program, possibly historic), and `t_live`, the wall-clock time at which v2
begins serving. The gap between them is the **backfill window**.

None of that is implemented. It is the destination; what follows is the first
step.

---

## Content addressing modulo α

The whole analysis rests on one primitive: a hash under which two subterms
collide **iff** they are the same computation. `content_hash` assigns every
subterm a 64-bit `ContentHash` such that two subterms hash equal iff they are
structurally identical up to (a) consistent renaming of variables *bound within*
the subterm and (b) the identity of variables *free* in it.

### Why α-invariance is the problem

Two independently compiled programs do not share their binders' identities.
Before uniquification a source binder is a `Name::Raw` spelling, so the same
source binder yields the same name in both versions — but after uniquification
every binder carries a globally fresh `uid`, and identical code compares
unequal. A hash meant to recognize "the same computation" across versions
therefore cannot hash a bound variable by its name at all. It hashes it
positionally:

- a variable whose binder lies *inside* the subterm contributes its De Bruijn
  index, which is invisible to α-renaming;
- a variable *free* in the subterm contributes its stable **spelling**
  (`Name::base`), which is what survives independent compilation.

Lexical shadowing then falls out for free: a name resolves against the innermost
enclosing binder, which is the one a reader would pick.

The free-variable rule is deliberately crude — two genuinely distinct binders
that share a spelling compare equal. It is isolated in one function
(`hash_free_var`) precisely so a finer cross-version binder correspondence can
replace it without touching anything else.

### Two hashes, two questions

The free-variable rule is the one place the hash's meaning is a choice rather
than a consequence of the term, and two different questions want two different
answers.

**Matching** asks *where else does this subterm appear?* — of two programs that
do not share binder identities. That needs a **context-free** answer, so a
subterm hashes the same wherever it sits: free variables go by **spelling**
(`content_hash`). Everything the matcher does is built on this.

**Classification** asks *is this the same computation?* — of two nodes already
known to correspond. Spelling is both too strict and too loose for that. Too
strict: renaming a binding is a denotational no-op, but every subterm mentioning
it hashes differently, so `x = 1; x + 2` → `y = 1; y + 2` reports every mention
changed even though the two roots hash equal. Too loose: two same-spelled
variables bound to different things hash the same, which is exactly the trap the
original model warned about — "the hash must be taken over the subterm together
with its resolved bindings, not over AST text alone".

So classification uses `resolved_hash`, which identifies a free variable by
**which binder it resolves to**, taken up to the correspondence: each binder
carries a *class* token shared by its counterpart in the other program, and a
free variable hashes to its binder's class. A renamed binding is then invisible,
and a same-spelled binding of something else is not confused with it. This
presupposes a correspondence, which is why it classifies a matching rather than
producing one.

*What this deliberately is not.* Threading the binder chain from the root and
using raw De Bruijn indices throughout looks equivalent and is not: inserting a
binder *above* a subterm shifts the index of every reference that reaches past
it, so adding one statement would report the entire tail below it as changed.
Binder classes are stable under that, because they name the binder rather than
the distance to it.

*Direction of error.* Where the matching itself is suboptimal, resolved hashing
reports change rather than sharing. Reordering two independent bindings, for
instance, pairs the spine positionally, so the bindings genuinely do differ
under the correspondence produced and the uses read as changed. That is the safe
direction: over-reporting change costs a sharing opportunity, under-reporting it
would make an unsound share.

### Standalone hashing is the matcher's precondition

Every subterm is hashed *standalone*: free variables are resolved against the
empty environment, so a variable bound above the subterm counts as free. This is
what lets a subterm match its twin in the other program regardless of how deeply
each one sits — which is exactly what the top-down matcher needs.

The cost is `O(𝑛 · depth)`, since each subterm's hash is recomputed with a fresh
binder environment. That is comfortable for real programs even with their deep
`let`-spine; the asymptotically tight scheme (Maziarz et al., *Hashing Modulo
Alpha-Equivalence*, PLDI 2021 — `O(𝑛 log²𝑛)`) slots in behind the same interface
if a program ever grows large enough to feel it.

### The hash is type-aware

A node's inferred type, its user annotation, its binders' types, and a `Cast`'s
target all participate. Two terms differing only in a type are *not* the same
computation — a change from `{Int | __elem >= 18}` to `{Int | __elem >= 21}` is
a change to the program even though the term structure is untouched. Types are
hashed with the same uid-robust discipline: refinement predicates (which are
*terms* living in type positions) go back through the term hasher, `Fun`
Pi-binder names are ignored, and a `ChanDom`'s channel name folds by spelling.

`Hole` and `Infer` hash to a bare tag. Before inference every type is `Hole`,
and a resolved tree contains no `Infer`, so collapsing unresolved structure to
one value is a safe fallback rather than a determinism hazard — the diff never
runs mid-inference.

### A rendered name is a hash the seam cannot reach

Uid-robustness lives in exactly one place: a free variable is identified by
`Name::base()`, never by its `uid`. That holds as long as a name *is* a `Name`.
Once a pass renders one into a `String`, the hash sees an ordinary string and
the seam no longer applies — nothing downstream can tell a run-varying identity
from a user-written one.

Loop planning used to do exactly that. The register record a `Transact` denotes
was typed with `Name::field_key()` labels that folded the binder uid in, so one
compilation produced `{acc#9: ([0, 2] ⇒ Int)}` and the next `{acc#19: …}`, with
`.acc#9` against `.acc#19` reading it. Two compilations of the *same* source
diffed as different, which made every stage from planning down unusable.

The label had no need of a uid. It has to be distinct only among the keys of one
register record — every consumer resolves it against a `keys_map` built per
`Transact` node, so accumulators in sibling loops live in different records and
cannot collide. `field_key` is now the plain spelling, and the per-record
uniqueness it relies on is asserted where the record is built rather than left
implicit in a global naming scheme.

The general rule this leaves: **a name rendered into a string is an identity the
hash cannot normalize**, so a pass that needs a label should derive it from
something already stable, and state where its uniqueness is enforced.

### Order-insensitivity where the language is

Records and `CollectionUnion` operands are *sets*, not sequences, so their child
hashes are sorted before folding and a reorder is a no-op. Tuples, lists, and
`Compose` chains are ordered and fold in position order. The differ mirrors this
exactly: a record field swap is not reported as a move.

### Scoping comes from one place

`hash_rel` extends the binder environment over exactly the scoped children, and
which children those are is *not* decided in `content_hash.rs`. It folds over
[`ccl/scope.rs`](../scope.rs)'s `for_each_scoped_item`, the crate's single
statement of CCL's binding structure, which the free-variable walkers
(`ccl_utils`'s `count_free` / `count_free_in_value`, `subst`'s `collect_expr_fv`)
and capture-avoiding substitution (`Subst::rewrite_expr`) fold over too. The
sharing matters most for the hash: a divergence would be a **correctness bug**,
not a style question, because the hash would stop agreeing with α-equivalence
and the differ would silently report identical programs as different.

`content_hash.rs` keeps the two things that are *not* scoping — a node's
non-child payload (`hash_payload`, exhaustive so a new variant's payload must be
declared) and the associative–commutative folding of `Record` /
`CollectionUnion`, which is a property of their algebra.

---

## The correspondence: a GumTree matcher

`diff` computes a node correspondence between two trees and classifies it. It is
a GumTree-style matcher (Falleri et al., *Fine-grained and accurate source code
differencing*, ASE 2014) run over the content hash, in five phases.

**1. Top-down anchoring.** Map the largest subtrees whose content hash is equal.
Equal hash means isomorphic modulo α, so the whole subtree is shared and its
descendants are mapped along with it (paired by hash, not position, so the
order-insensitive nodes come out right). Tallest-first, so a big anchor claims
its descendants before anything inside it is considered separately.

*Duplicate resolution.* Small subtrees always repeat — `0`, `true`, `x`. Every
equal-hash pairing is an equally valid "shared" classification, but not an
equally *useful* one: the copy chosen decides whether the node reads as sitting
still or as having moved, and which siblings are left over for the later phases.
Among free candidates the matcher takes the one in the most structurally
corresponding position — parent already matched to this node's parent, then the
longest agreeing chain of ancestor node kinds, then the closest depth. An
arbitrary choice here manufactures a spurious move *plus* a spurious
delete/insert pair for the copy it displaced.

**2. Root anchoring.** Two programs being diffed are two versions of *one*
program, so their roots correspond by construction and are anchored to each
other if phase 1 has not already done it. Nothing else can establish that: a
root that gained a statement fails phase 3's similarity test (see below), and
the result is that the entire program reads as deleted-and-reinserted for a
one-statement edit. The anchor requires the two roots to be the same node kind,
so two genuinely unrelated programs still correspond nowhere.

**3. Bottom-up container recovery.** An interior node left unmatched is paired
with the best same-kind candidate in the other tree that *contains* enough of
its already-matched descendants, processed children-before-parents. This is what
keeps an inserted statement from desynchronizing the whole `let`-spine below it:
the unchanged tail anchors in phase 1, and the containers above it are recovered
here instead of being reported as wholesale rewrites.

*Containment and tightness are separate questions.* GumTree gates this on the
Dice coefficient, `2·common / (|desc 𝑢| + |desc 𝑤|)`, which asks "how much of
these two subtrees is shared" — and that is the wrong question when one side
deliberately grew. A container that gained a statement has its own contribution
swamped by the new material and scores below the threshold, so the very edit the
phase exists to absorb is the one it rejects. The gate is therefore the
**overlap coefficient**, `common / min(|desc 𝑢|, |desc 𝑤|)`: "is one of these
essentially inside the other", which is exactly the insertion (and, symmetrically,
the deletion) question. Dice stays as the *ranking* among candidates that pass —
the candidates all contain the same matched descendants and so are nested in one
another, and Dice's growing denominator picks the innermost, the container that
fits tightest.

**4. Optimal recovery inside a paired container.** Phases 1–3 match by
whole-subtree equality and by container similarity; neither can pair two
subtrees that are nearly identical but differ somewhere inside. That gap is what
makes a one-token edit read as a delete plus an insert. This phase closes it: as
each container pair is established, compute the minimum-cost edit mapping between the
two subtrees and adopt every pair it aligns whose nodes are same-kind and still
unmatched. Node labels are content hashes, so relabelling is free when the
hashes agree and costs one otherwise. Pairs from phases 2 and 3 are the only
ones that need this — a phase-1 pair is isomorphic by construction, so there is
nothing left unmatched beneath it.

The mapping is *optimal* under unit edit costs, computed with the Zhang–Shasha
dynamic program. GumTree reaches for RTED, which computes the same optimal
mapping faster by choosing a better decomposition strategy — the difference is
asymptotic cost, not the result. Pairs above a size ceiling (100 nodes,
GumTree's default) are skipped, since tree edit distance is `O(𝑛²𝑚²)` in the
worst case; those keep only what phases 1–3 found.

**5. Classification along two axes.** Every correspondence is labelled with
whether its **content** changed and whether its **placement** did. These are
independent: a node can keep its content and move, or stay put and change.

- *Content* is just hash equality: `Same` (identical computation, reusable
  wholesale) or `Changed` (the same place in both programs with different
  content — the divergence lives in the children, and these are where a
  `Versioned` node would sit).
- *Placement* is the child-alignment step from Chawathe et al.'s edit-script
  derivation, which GumTree inherits. A node is `InPlace` iff it hangs off the
  corresponding parent *and* did not cross any of its matched siblings. Within
  one matched container pair, "did not cross" is decided by taking a longest
  increasing subsequence of the matched children's destination slots: the
  children on it kept their relative order, and the rest are the minimum set of
  moves that explains the permutation. Order-insensitive containers skip the
  test entirely.

A source-only node is **deleted**; a target-only node is **new**. A relocated
subtree is reported as moved once, at its root — its descendants stay in place
relative to it.

### The actionable form: divergences and shared roots

The classification is complete but not minimal. Every *ancestor* of an edit has
changed content, and every *descendant* of an inserted subtree is itself new —
one literal edited at the bottom of a forty-binding spine leaves forty-two
changed nodes, of which exactly one is the edit. A consumer that read `matched`
directly would have to re-derive the interesting set every time, so the differ
derives it once.

**`divergences()`** is the minimal set of places the two programs disagree, at
the granularity a `Versioned` node would sit. No divergence contains another,
so the set partitions the disagreement: everything not under one corresponds.
Three kinds —

- *Changed* — both programs have a node here, its content differs, and nothing
  below it differs. A changed node with a changed descendant is not a site: the
  deeper node is the better explanation. Insertions and deletions do **not**
  suppress it, because a node whose own payload changed *and* which gained a
  child has two separate things to say.
- *Inserted* — the root of a subtree the new program has and the old does not.
  Reported where the new region begins, not once per node in it. The walk
  continues underneath: a matched node can sit inside a new region — a new
  expression wrapping content that survived — and what diverges under it still
  counts.
- *Deleted* — the mirror image, at the root of what the old program had.

For the forty-binding spine that is one divergence, against forty-two changed
nodes.

**`shared_roots()`** is the other side: every node whose content is unchanged
and whose parent's is not — the largest subtrees the two versions have in
common, and so the units of reuse. A `Same` node's whole subtree is `Same`, so
its descendants add nothing.

Reuse here means *the term is the same term*, which is what a unified tree
needs. It does not mean the term evaluates to the same value in both versions:
`let x = 1 in x` and `let x = 2 in x` share the body `x`, and that is right —
the two `let`s are the divergence, and it is the binding that differs, not the
read. Value-level sharing is the key-level storage question, decided at
runtime, not a property of the tree.

### Reading a diff

A [`Diff`](../diff.rs) renders itself: it prints as an annotated tree of the
**new** program, so the output doubles as the shape a unified `Versioned` tree
would take, followed by whatever the old program had that the new one dropped.

```text
2 shared · 1 changed · 1 moved · 0 deleted · 16 new

~ let a = 1…
  = 1
  + let b = Sum(λ __iter_record → __iter_record ▷ [1, 2, 3] ▷ (λ i → i *…
    + Sum(λ __iter_record → __iter_record ▷ [1, 2, 3] ▷ (λ i → i * 2))    (+12 nodes)
    + a + b
      = a »
      + b
```

Markers are `=` unchanged, `~` content changed, `+` new, `-` deleted, and a
trailing `»` for a node whose placement changed. Two rules keep it readable:
an unchanged subtree is not descended into (it is unchanged all the way down),
and a wholly-new or wholly-deleted region collapses to its root with a node
count. A node that gained or lost only *itself* — a wrapper around content that
survived — is deliberately *not* collapsed: above, the new `a + b` is shown with
the reused `a` under it, because claiming that `a` changed would be false.

Each node is shown by rendering its subterm with `symbolic` and keeping the
first line, cut to a fixed width. A leaf prints exactly; an interior node prints
its head. That costs `O(𝑛²)` text and is an inspection surface, not a hot path —
but it means the rendering cannot drift out of step with the AST the way a
second, shallow node vocabulary would.

### Worked example

`1 if v > 0 else 2` → `1 if v > 1 else 2`, diffed at the lowered stage. The
ternary lowers to a guard-based `Case`, so both trees contain a literal `1` (the
then-branch value) *and*, in the new version, a second literal `1` (the guard
threshold):

```
Changed/InPlace   let v = 5
Same/InPlace      5      ->  5
Changed/InPlace   { v > 0 → 1; true → 2 }  ->  { v > 1 → 1; true → 2 }
Changed/InPlace   v > 0  ->  v > 1
Same/InPlace      v      ->  v
Changed/InPlace   0      ->  1
Same/InPlace      1      ->  1
Same/InPlace      true   ->  true
Same/InPlace      2      ->  2
```

Nothing deleted, nothing new, nothing moved: one literal changed and the
containers above it are marked as the places that changed with it. Both of the
gap-closing phases are load-bearing here — duplicate resolution keeps the
branch-body `1` matched to the branch-body `1` rather than to the new guard
threshold, and optimal recovery pairs `0` with `1` instead of reporting a
delete and an insert.

---

## Which stage to diff

`compile_to(code, stage)` compiles to a nominated pipeline stage and hands back
the tree. Every stage runs through the *same* `diff` core — nothing in the
matcher is stage-specific, because the content hash is uid-robust and
type-aware, which is exactly what one core needs to handle all of them.

| Stage | Tree | What it shows |
| --- | --- | --- |
| `Lowered` | `Raw` names, pre-uniquify, pre-inference; most types `Hole` | Closest to source, minimal diffs. Type sensitivity comes only from annotations and lowering-built types (cast refinements). |
| `Inferred` | α-uniquified, every node carrying its resolved type | Everything above, plus type-level divergence the earlier stage cannot see. |
| `Inlined` | inferred, then UDF-inlined | Everything above, with function boundaries erased — see "How much to normalize". |
| `Channelized` | mutability eliminated: `LetRec` recurrences, feeds routed | The compiler's shape rather than the user's — `For`/`MutWrite`/`Begin`/`Defer` are gone. |
| `LambdaElim` | point-free combinators | No binders in the term at all. |
| `Planned` | recurrences on the `Transact` carrier, joins planned | The shape operator conversion consumes, and where compute sharing is decided. |

The payoff of the later stage is real: in `x = 1` / `(x, x)` versus `x = "a"` /
`(x, x)`, the bodies are structurally identical and hash *equal* before
inference. After inference the element type diverges and the same subterm no
longer matches — types carry signal the term structure alone does not.

`compile_to` stops *above* the mutability and channelization phases
deliberately. Those rewrite the user's loops and feeds into `LetRec` recurrences
whose shape is an artifact of the compiler, not of the program the user edited;
a diff there would report churn the user cannot act on. `LetRec` and `Transact`
are consequently unreachable from source at any of these stages.

The later stages are where `LetRec` and `Transact` finally appear, and they are
selectable — but the whole pipeline is not. The transaction, mutability and
channelization phases are one rewrite of the user's loops and feeds; stopping
between them exposes a half-rewritten tree no consumer wants, so `Channelized`
is the point at which that rewrite is complete.

## How much to normalize

Two programs can be the same computation written differently. The more of that
the diff sees through, the more the two versions share — and the less
localized the answer becomes when they genuinely differ. Choosing a stage is
choosing where on that curve to sit; the compiler's own passes do the work, so
there is no separate rewriting system to keep honest.

Measured on the refactors that actually occur, in divergences reported:

| Edit | `Inferred` | `Inlined` |
| --- | --- | --- |
| rename a binding | 0 | 0 |
| extract a subexpression into a `def` | 6 | **0** |
| edit a body inside a `def` called once | 1 | 1 |
| edit a body inside a `def` called **twice** | 1 | **4** |
| reorder two independent bindings | 2 | 2 |
| extract a subexpression into a `let` | 5 | 5 |

Inlining is a trade, not an improvement: it makes moving code across a function
boundary invisible, and in exchange reports an edit inside a shared helper once
per call site, because the body it changed now appears once per call site. Take
it when refactoring across functions is the noise you want gone.

Below `Inlined` the trade keeps going the same way, and the measurements say so
plainly. Every pass that rewrites the user's shape spreads one edit over more of
the tree:

| Edit | `Inlined` | `Channelized` | `LambdaElim` | `Planned` |
| --- | --- | --- | --- | --- |
| a literal | 1 | 1 | 1 | 1 |
| a comprehension's filter threshold | 1 | 1 | 2 | 4 |
| an accumulator loop's body | 2 (2 new) | 2 (2 new) | 2 (**14 new**) | 2 (14 new) |
| a transactional register's write | 2 (2 new) | 2 (2 new) | 3 (8 new) | 3 (8 new) |

So the default is the earliest stage that answers the question. The reason to
reach past `Inlined` is not a better diff of the source — it is that `Planned`
is the shape operator conversion consumes, so it is where a claim about *sharing
compute* is actually a claim about the graph that runs. Diffing there answers a
different question, not the same question better.

### What deliberately is *not* normalized

**Extracting a subexpression into a `let`.** `(a + 2) * (a + 2)` and
`let t = a + 2 in t * t` have the same value and are *not* the same program
here: naming a subexpression is how CCL says "compute this once". The two
compile to different operator graphs — one shared node against two — so for a
system whose whole point is sharing compute between versions, this is a real
change and reporting it is correct. (Which is also why the `Inlined` stage stops
at UDFs: `inline` beta-reduces *function* bindings, not value bindings.)

**Commutativity.** `a + b` and `b + a` differ by one divergence. Normalizing
them would need type direction, because `+` is string concatenation as well as
addition and is not commutative there — so it is available only post-inference,
for a rare edit, at the cost of making the hash type-conditional. Not worth it.

**Constant folding, β/η reduction beyond UDF inlining.** Each widens the
equivalence class and costs locality the same way inlining does. Nothing
observed yet asks for them; the roadmap is driven by missed sharing that shows
up in practice, not by completeness.

### The one that needs more than a stage

Reordering two independent bindings is a true no-op — CCL's `let` is
non-recursive and pure, so the operator graph depends on the dependency DAG, not
on the written order — and no stage fixes it, because *the nesting is the
order*. `let a = 1 in let b = 2 in body` and `let b = 2 in let a = 1 in body`
have different tree shapes, and the matcher pairs the spine positionally, so the
reads underneath resolve to non-corresponding binders and report as changed. See
"Open threads".

---

## Beyond the analysis: branching

The analysis stops at the classification. What gets built from it — running two
versions with their common work shared, and upgrading one to the next without
rewriting the history the old one produced — is worked out in
[branching.md](branching.md).

Three things there bear on this document.

*The divergence frontier is the input.* `divergences()` says where a version
guard goes; `shared_roots()` says what the two versions can compute once. That
is why both are derived here rather than left to the consumer.

*A guard needs a clock, and the domain says whether there is one.* A divergence
inside a domain that is both ordered and event-anchored (`Txn`, a live source)
can be guarded; one inside a batch region — literal data, a finite loop — cannot,
because there is no position at which its answer changes. Neither property is
carried in the type today, so this is an approximation read off the domain of
the enclosing function rather than something checkable; branching.md tabulates
which of today's domains fall where.

*No `Versioned` node.* An earlier draft of the branching design proposed one,
along with backfill and retroactive branch points. A branch turns out to be an
ordinary `Case` on the sequencing domain, and the retroactive cases are cut —
see branching.md for why.

### The next analysis: divergence reachability

Running two versions side by side means giving each its own copy of any state
they could disagree about — and *only* of that state. The question is per
register and per sink: **is any divergence upstream of it in the dataflow
graph?** If none is, the two versions provably write it identically and it needs
one store; if one is, it needs a store per version (or copy-on-write, where the
values happen to agree anyway — a runtime concern, not this one).

It is a reachability query over `divergences()` rather than new matching work,
and it is what makes a second version cost the diff rather than 2×. Not built.

---

## Open threads

**Substitution's transport mode still restates the scoping rules.**
[`ccl/scope.rs`](../scope.rs) now holds them once and every *observing* walk
folds over it, but `subst`'s `Subst::apply_expr_inner` — the mode that returns a
rewritten copy rather than mutating in place — cannot: it rebuilds each node,
and a rebuild is a per-variant `match` by construction. Folding it over the
shared walk would mean cloning the whole subtree at every binding node (clone
the node, then overwrite its children), which turns substitution down a `let`
spine from linear into quadratic in the spine's depth — the one shape Cambra
programs are reliably deep in. Its arms are guarded only by review; if a binding
form is ever added, `scope.rs` is the compile error that should prompt a look
here.

**Child enumeration is written out twice.** `diff`'s `child_exprs` mirrors
`TypedExpr::walk_children` arm for arm, differing only in that it descends into
a `Cast` target's refinement predicate (a load-bearing term that
`walk_children` treats as a type child). Both matches are exhaustive, so a new
node variant is a compile error in both places — the duplication is visible
rather than silent, which is why it stands.

**A `let`-spine encodes an order it does not have.** A run of independent
bindings is a dependency DAG, but CCL spells it as nested `Let`s, so reordering
two of them changes the tree shape and the matcher pairs the spine by depth.
The reads underneath then resolve to non-corresponding binders and report as
changed — conservative, but noise (two divergences for two reordered bindings).
**Decided: leave it.** What follows is why, so the ground already covered is not
covered again.

*It is not a matcher-tuning problem.* Three plausible fixes were tried and
measured, and none moved the reordering case:

- running bottom-up container recovery *before* the root edit-distance step, so
  a content-aware phase gets first refusal on container pairings — made it
  worse (three reordered bindings went from two divergences to three);
- ranking candidates by how many of their children are already matched to each
  other — byte-identical results on every case in the corpus;
- a rule that a `Let`'s identity is its *binding* rather than its body, pairing
  each `Let` with the one whose bound expression its own matched — no change to
  reordering, and worse on three bindings.

The consistency is the finding: the nesting *is* the order, so no amount of
matcher tuning recovers what the representation does not distinguish.

*The two real options both cost more than the noise.* A canonical pre-diff
reordering needs a sort key stable under ordinary edits, and neither candidate
is: sorting by content hash is chaotic — editing one literal permutes the spine,
trading reorder noise for value-edit noise, which is far more common — and
sorting by binder spelling is stable under value edits but makes a rename that
crosses another binding alphabetically produce exactly the noise being removed.
Either way it moves noise rather than removing it. The other option is to stop
spelling a binding group as a nest: an n-ary group node would make the order
disappear at the source and give `Record`-style order-insensitivity for free,
but it is a new concept threaded through parse, lowering, inference and every
pass. That cost is only worth paying if something other than diffing wants it
too — which is the trigger to revisit this.

**The free-variable seam is crude.** Two distinct binders sharing a spelling
compare equal. A real cross-version binder correspondence — matching v1's binder
to v2's by position in the correspondence being computed — is circular with the
matcher and needs thought.
