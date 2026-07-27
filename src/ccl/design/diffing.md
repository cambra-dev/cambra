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
the tree. Both supported stages run through the *same* `diff` core — nothing in
the matcher is stage-specific, because the content hash is uid-robust and
type-aware, which is exactly what one core needs to handle both.

| Stage | Tree | What it shows |
| --- | --- | --- |
| `Lowered` | `Raw` names, pre-uniquify, pre-inference; most types `Hole` | Closest to source, minimal diffs. Type sensitivity comes only from annotations and lowering-built types (cast refinements). |
| `Inferred` | α-uniquified, every node carrying its resolved type | Everything above, plus type-level divergence the earlier stage cannot see. |

The payoff of the later stage is real: in `x = 1` / `(x, x)` versus `x = "a"` /
`(x, x)`, the bodies are structurally identical and hash *equal* before
inference. After inference the element type diverges and the same subterm no
longer matches — types carry signal the term structure alone does not.

`compile_to` stops *above* the mutability and channelization phases
deliberately. Those rewrite the user's loops and feeds into `LetRec` recurrences
whose shape is an artifact of the compiler, not of the program the user edited;
a diff there would report churn the user cannot act on. `LetRec` and `Transact`
are consequently unreachable from source at either stage — the hash covers them
structurally anyway, so the later stages are available if the versioning work
turns out to want them.

---

## Beyond the analysis: Versioned nodes

The analysis stops at the classification. The next milestone is a **unified CCL
AST**: both versions compile to one tree, identical subterms shared directly and
each divergence wrapped in a `Versioned` node carrying the two arms. The
`Changed` correspondences are exactly the sites where such a node would sit.

The semantic requirements, from the original model:

1. Both arms must type-check. If their types do not unify the diff is
   *type-breaking*: the node's type is a time-indexed union — `𝑇₁` for reads
   below `t_new`, `𝑇₂` at or above it — and storage cannot be shared at the key
   level.
2. Each `Versioned` node needs a stable identity across the two versions, so
   downstream passes can map it back to user-visible source locations.
3. Runtime evaluation is parameterized by the reader's version and the branch
   point: a v1 reader sees v1's arm; a v2 reader sees v2's arm subject to
   `t_new` / `t_live`.

"Compilable" admits three depths, each a superset of the last — *type-checks*
(the unified AST passes the checker), *lowers* (it survives to CCL, which forces
deciding how `Versioned` appears in lowered form), and *executes* (the runtime
serves the correct arm, which needs a branch-selection tile operator). Which one
is the milestone is open.

Storage sharing is **key-level**: a key written identically under both branches
at a given logical step is one physical entry; a key that differs gets one entry
per branch. The per-key read-set/write-set machinery the commit operator already
maintains ([mutability.md](mutability.md)) operates at exactly this granularity.
Sharing therefore scales with the *unchanged* surface area, not with the size of
the diff.

Compute sharing is the analogue, and it is what the content hash approximates:
subterms that are denotationally equivalent between versions can be evaluated
once. The approximation is deliberately minimal — α-equivalence plus lexical
canonicalization. More aggressive normalizations (β/η reduction, constant
folding, AC-normalization of associative-commutative operators) widen the
equivalence class at compiler cost; the plan is to let observed missed sharing
drive that roadmap rather than to speculate.

### Deferred

- **Move labelling into an edit script.** Placement is classified, but no
  `Insert`/`Delete`/`Move`/`Update` script is emitted. The unified-tree work
  needs the correspondence, not a script.
- **Stacked diffs.** A v2→v3 diff on top of an already-diffed v1→v2. Squashed to
  a single base-to-tip diff for now.
- **Live backfill.** When `t_new` is historic and v1 is still writing, `t_live`
  is a moving target and v2 must replay v1's commit log through its own body
  until it catches up. Backfilling at all requires reproducible inputs over the
  window, which bounds the legal range of `t_new` by prior release/obsoletion
  decisions.
- **Blast radius.** A retroactive change propagates: every commit that *read* a
  changed key must be recomputed transitively. The blast radius is the diff's
  transitive closure through the read-dependency graph, not the diff itself.

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

**The free-variable seam is crude.** Two distinct binders sharing a spelling
compare equal. A real cross-version binder correspondence — matching v1's binder
to v2's by position in the correspondence being computed — is circular with the
matcher and needs thought.
