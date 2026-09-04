# Program diffing — content addressing and correspondence

For two compiled programs, this analysis decides which parts are **the same
computation** and where they diverge. Running two versions concurrently with
their storage and compute shared rests on it, as does a denotationally precise
transition between them. Neither is built; the model they need is recorded
below.

Implemented by [`ccl/content_hash.rs`](../content_hash.rs) (the equivalence) and
[`ccl/diff.rs`](../diff.rs) (the correspondence). Neither is wired into
[`compile_program`](../context.rs) — the analysis is a library the versioning
work will consume, not a pipeline pass.

---

## Inputs, output, and what holds of it

**In**: two [`TypedExpr`](../expr.rs) trees, each a whole program compiled to the
same [`Phase`](../context.rs). They are taken to be two versions of one program;
nothing requires that, and unrelated programs share little.

**Out**: a [`Diff`](../diff.rs) — a correspondence between the two trees' nodes,
each pair classified on content and on placement, plus the nodes of each side
left unpaired. Two derived forms are what a consumer reads: `divergences()`, the
places the two programs disagree, and `shared_roots()`, the largest subtrees they
compute the same way.

What holds of the output, and the test that holds it:

| | Held by |
| --- | --- |
| Two compilations of one source diff as identical, at every phase | `every_phase_diffs_identical_source_as_identical` |
| Identical trees have no divergences, and one shared root: the program | `identical_programs_have_no_divergences` |
| An identity that varies between compilations (a `Name` uid) never reaches the result | `diff_is_robust_to_uid_nondeterminism` |
| Renaming a binding is not a change | `renaming_a_binding_is_not_a_change` |
| One edit is one divergence, however deep in the `let` spine it sits | `one_edit_is_one_divergence` |
| Shared roots are pairwise disjoint, each the top of its region | `shared_roots_are_maximal_and_disjoint` |
| Two terms differing only in an inferred type hash apart | `inference_adds_type_signal` |

Two properties are absent, and stated as absent rather than approximated.
`divergences()` is not minimal: it is small on the shapes the tests measure, and
the two reduction rules are not a minimality theorem
([The actionable form](#the-actionable-form-divergences-and-shared-roots)).
Sharing is not maximal: where the matching is suboptimal the result reports
change, which costs a sharing opportunity rather than producing an unsound share
([Direction of error](#direction-of-error)).

---

## Diffing at a glance

Two compiled trees in, a classified node correspondence out, in four steps.

1. **Hash every subterm by content, modulo α** (`content_hash`). A variable free
   in the subterm is identified by its spelling, so a subterm hashes the same
   wherever it sits and in whichever program.
2. **Match the two trees on those hashes**, GumTree-style: anchor equal-hash
   subtrees largest-first, anchor the two roots to each other, recover the
   containers above an anchor by how much of it they hold, then close the
   remaining gaps inside a paired container with tree edit distance.
3. **Re-hash every matched node against the correspondence.** `resolved_hash`
   identifies a free variable by which binder it resolves to, so a binding
   renamed between versions is invisible; `own_hash` takes what is authored at
   the node alone, which separates "this node changed" from "something under it
   did".
4. **Classify** each correspondence on two axes, content and placement, and
   reduce the result to `divergences()` — where the two programs disagree — and
   `shared_roots()` — what they can compute once.

The order is fixed: step 2 has no correspondence to resolve names through, and
step 3 exists only because step 2 produced one. Matching never consults a
classification.

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
- **A version's extent is a predicate over commit positions**, and the predicate
  is not required to start at the present one. Applying v2 from a commit
  timestamp already in the past is the same statement as applying it from a
  future one, so a correction to history and a forward deployment are one
  mechanism.
- **Two versions run at once**, over overlapping ranges of the commit domain:
  clients holding v1 keep being answered by v1 while new clients are answered by
  v2, until nothing selects v1 any more. There is no branch *structure* — no
  parent version, no ordering between v1 and v2 beyond the predicates each one
  carries — so which version was written first says nothing about which applies
  where.

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
source binder yields the same name in both versions. After uniquification every
binder carries a globally fresh **`uid`**, allocated in traversal order, so the
same source binder gets a different one in each compilation and identical code
compares unequal. A hash meant to recognize "the same computation" across versions
therefore cannot hash a bound variable by its name at all. It hashes it
positionally:

- a variable whose binder lies *inside* the subterm contributes its De Bruijn
  index, which is invisible to α-renaming;
- a variable *free* in the subterm contributes its stable **spelling**
  (`Name::base`), which is what survives independent compilation.

Lexical shadowing then falls out for free: a name resolves against the innermost
enclosing binder, which is the one a reader would pick.

Under this rule a rename is a change: `x = 1; x + 2` → `y = 1; y + 2` hashes
every mention of the binding differently, even though the two programs denote
the same thing. That is correct for the matcher, which is looking for a
subterm's twin and has no correspondence to consult, and wrong for the
classifier, which does — hence the second hash below. Reordering two independent
bindings is a separate problem, in the representation rather than the hash; see
[Open threads](#open-threads).

The free-variable rule is also crude in the other direction: two distinct
binders that share a spelling compare equal. It is isolated in one function
(`hash_free_var`) so a finer cross-version binder correspondence can replace it
without touching anything else.

### Three hashes, three questions

Three questions come up, and each wants a different answer to "what is this
node's identity". Everything else about the fold — the traversal, the De Bruijn
treatment of bound variables, the type-awareness, the order-insensitivity — is
shared, so the table below is the whole difference between them.

| | `content_hash` | `resolved_hash` | `own_hash` |
| --- | --- | --- | --- |
| Question | where else does this subterm appear? | is this the same computation? | did *this node* change? |
| Used by | matching (phases 1–4) | classification (phase 5) | classification (phase 5) |
| A **free variable** identified by | its spelling (`Name::base`) | the binder it resolves to | the binder it resolves to |
| The node's **children** | fold in | fold in | left out |
| Needs a correspondence | no | yes | yes |

**Matching** asks *where else does this subterm appear?* — of two programs that
do not share binder identities. That needs a **context-free** answer, so a
subterm hashes the same wherever it sits: free variables go by **spelling**
(`content_hash`). Everything the matcher does is built on this.

**Classification** asks *is this the same computation?* — of two nodes already
known to correspond. Spelling is both too strict and too loose for that. Too
strict: a rename hashes every mention differently, as above. Too loose: two
same-spelled variables bound to different things hash the same, so the hash has
to be taken over the subterm together with its resolved bindings rather than
over its AST text alone.

So classification uses `resolved_hash`, which identifies a free variable by
**which binder it resolves to**, taken up to the correspondence. Each binder
carries a **correspondent**: a 64-bit token naming the binder it corresponds to
in the other program, minted from the correspondence itself. A src binder's is
the index of the dst node its owner matched; an unmatched binder gets a token
outside dst's index range, so it corresponds to nothing and can never look like a
match. A free variable hashes to the correspondent of the binder it resolves to.
A renamed binding is then invisible, and a same-spelled binding of something else
is not confused with it. A node introducing several binders at once — a `LetRec`
group — gives each its own correspondent, keyed by position within the group,
since they are distinct binders.

**Localizing** asks *did this node change, or only something under it?* — of a
node already known to differ. `own_hash` answers it by folding what is authored
at the node and stopping there: its discriminant, its literal value, operator,
variant tag, binder annotation or record labels, and the correspondents its
variable occurrences resolve to.

Derivedness, not child-ness, is the boundary, and three things fall outside it.
The children, which is the point. The node's inferred `ty`, computed from the
node and its children — folding it would report `let a = 1` → `let a = 2` at the
`Let` as well as at the literal, since the `Let`'s type is the literal's
singleton. And a binder's declared `ty`, on the same ground. A reader who takes
the boundary to be children alone gets the two type exclusions wrong, and those
are where the design decision sits.

A container therefore has close to no own content. A `Let`'s is its discriminant
plus two `user_annotation`s — the binder's name is De Bruijn and its type is
skipped — so `let a = 1 in a`, `let a = 2 in a`, `let b = 1 in b` and
`let a = 1 + 5 in a` all share one own hash at the `Let`, and only an annotation
moves it. A container is never a disagreement site on its own, which is what
puts the site on the literal that changed.

*What a correspondent is not.* Threading the binder chain from the root and
using raw De Bruijn indices throughout looks equivalent and is not: inserting a
binder above a subterm shifts the index of every reference that reaches past it,
so adding one statement would report the entire tail below it as changed. A
correspondent is stable under that, because it names the binder rather than the
distance to it.

#### Direction of error

Where the matching itself is suboptimal, resolved hashing reports change rather
than sharing. Reordering two independent bindings, for instance, pairs the `let`
**spine** — the chain of nested `Let` nodes a run of statements lowers to —
positionally, so the bindings genuinely do differ under the correspondence
produced and the uses read as changed. That is the safe direction:
over-reporting change costs a sharing opportunity, under-reporting it makes an
unsound share.

### Standalone hashing is the matcher's precondition

Every node of the tree gets a hash, and each one is computed over that node's
whole subterm: a node's hash folds its children's, so the root's hash covers the
program. `hash_all` walks the tree once and returns the map.

Each of those hashes is *standalone*: free variables are resolved against the
empty environment, so a variable bound above the subterm counts as free. This is
what lets a subterm match its twin in the other program regardless of how deeply
each one sits — which is exactly what the top-down matcher needs.

The cost is `O(𝑛 · depth)`, since each subterm's hash is recomputed with a fresh
binder environment. That is comfortable for real programs even with their deep
`let` spine; the asymptotically tight scheme (Maziarz et al., *Hashing Modulo
Alpha-Equivalence*, PLDI 2021 — `O(𝑛 log²𝑛)`) slots in behind the same interface
if a program ever grows large enough to feel it.

### The hash is type-aware

A node's inferred type, its user annotation, its binders' types, and a `Cast`'s
target all participate. Two terms differing only in a type are not the same
computation — a change from `{Int | __elem >= 18}` to `{Int | __elem >= 21}` is
a change to the program even though the term structure is untouched.

This section describes `content_hash` and `resolved_hash`, which agree on all of
it. `own_hash` keeps the user annotation and drops the rest: a node's `ty`
and a binder's `ty` because both are derived from the node and its children,
and a `Cast`'s target because the differ reaches that target's refinement
predicate as a *child* of the cast — the one place `diff`'s child enumeration
departs from `TypedExpr::walk_children` — so folding it here too would report one
threshold edit at the literal and again at the cast above it.

Types are hashed with the same **uid-robust** discipline as terms: no identity
that varies between two compilations of one source reaches the hash. Refinement
predicates (which are *terms* living in type positions) go back through the term
hasher, `Fun` Pi-binder names are ignored, and a `ChanDom`'s channel name
contributes its spelling rather than its `Name`.

A `Fun`'s `FunKind` participates. `A ⇒ B` and `A ⤇ B` are different
computations — a data function's domain is its data, which is what drives
iteration and forces its joins to be lossless — so the two must not collide. A
`FunKind::Var` contributes what it was pinned to and not its `uid`, on the same
grounds as `Infer`: the pin is determined by the one value that reaches the
variable, the `uid` by allocation order.

`Hole` and `Infer` hash to a bare tag. Before inference every type is `Hole`,
and a resolved tree contains no `Infer`, so collapsing unresolved structure to
one value is a safe fallback rather than a determinism hazard — the diff never
runs mid-inference.

### A name rendered into a string is past the point uid-robustness applies

Uid-robustness is enforced in exactly one place: a free variable is identified by
`Name::base()`, never by its `uid`. That works only while the name is still a
`Name`. Once a pass renders one into a `String` — a record label, a key — the
hash sees an ordinary string, and nothing downstream can tell a run-varying
identity from a user-written one.

Loop planning is where this bites. The mutable variable record a `Transact`
denotes is typed with `Name::field_key()` labels, and folding the binder uid in
would type the node `{acc#9: ([0, 2] ⇒ Int)}` in one compilation and `{acc#19:
…}` in the next, with `.acc#9` against `.acc#19` reading it — two compilations
of the same source diffing as different, and every phase from planning down
unusable.

The label has no need of a uid. It must be distinct only among the keys of one
mutable variable record: every consumer resolves it against a `keys_map` built
per `Transact` node, so accumulators in sibling loops live in different records
and cannot collide. `field_key` is therefore the plain spelling. That leaves the
distinctness as a property of spellings rather than of construction — a key is
the user's own variable name, distinct within the block or loop that declares
it, or a writer's reply tap (`to_<base>_<n>`), which shares the record with them
— so each site that builds a record from these labels asserts it in debug
(`hist_record` in `planning/loops.rs`, the two `keys_map` inserts in
`interpreter/operator_conversion.rs`).

The general rule this leaves: **a name rendered into a string is an identity the
hash cannot normalize**, so a pass that needs a label derives it from something
already stable and states where its uniqueness is enforced.

### Order-insensitivity where the language is

A record's fields, a `DisjointJoin`'s operands and a refined type's
[`RefinementSet`](../ty.rs) are sets, not sequences, so their child hashes are
sorted before folding and a reorder is a no-op. Tuples, lists, `Compose` chains,
and `Copair` operands are ordered and fold in position order. The differ mirrors
this exactly: a record field swap is not reported as a move.

A refinement set is where the mirroring takes work rather than falling out. The
differ descends into a cast target's predicates as children of the cast, and
children are paired by position, so the enumeration is sorted by `content_hash`
(`cast_target_predicates`) — the set's physical order is meaningless by contract,
and `CAMBRA_REFINEMENT_ORDER=reverse` flips it globally to prove that.

`Copair` sits on the ordered side because operand position picks the coproduct
tag: `a ++ b` has domain `A + B` and `b ++ a` has `B + A`, so the two are not the
same computation. `DisjointJoin` is the join in the partial-function order, which
is associative and commutative outright
([ir.md](ir.md#copair-and-disjointjoin--two-collection-combining-operations-not-one)
separates the two operations).

### Scoping comes from one place

`hash_rel` extends the binder environment over exactly the scoped children, and
which children those are is not decided in `content_hash.rs`. It reads them from
[`ccl/scope.rs`](../scope.rs)'s `for_each_scoped_item`, the crate's single
statement of CCL's binding structure, which the free-variable walkers
(`ccl_utils`'s `count_free` / `count_free_in_value`, `subst`'s `collect_expr_fv`)
and capture-avoiding substitution (`Subst::rewrite_expr`) read from too. A
divergence between the hash's idea of the binding structure and the language's
would be a **correctness bug** rather than a style question: the hash would stop
agreeing with α-equivalence, and the differ would report identical programs as
different.

`content_hash.rs` keeps the two things that are not scoping — a node's
non-child payload (`hash_payload`, exhaustive so a new variant's payload must be
declared) and the associative–commutative folding of `Record` / `DisjointJoin`,
which is a property of their algebra.

---

## The correspondence: a GumTree matcher

`diff` computes a node correspondence between two trees and classifies it. It is
a GumTree-style matcher (Falleri et al., *Fine-grained and accurate source code
differencing*, ASE 2014) run over the content hash, in five phases.

Two words recur below and mean different things. A **subtree** is a node
together with everything under it. A **container** is a node considered as the
thing that holds other nodes — the word is used where the point is what a node
contains rather than what it is, and every container is the root of a subtree.

**1. Top-down anchoring.** Map the largest subtrees whose content hash is equal.
Equal hash means isomorphic modulo α, so a single hash comparison at the root
settles the whole subtree: the two are the same computation node for node, and
the matcher maps the descendants along with it in one pass without comparing
them again. Tallest-first, so a big anchor claims its descendants before
anything inside it is considered separately.

Equal hash does not fix child order. The hash canonicalizes the nodes whose
order carries nothing — a `Record`'s fields fold sorted by label, a
`DisjointJoin`'s operands and a refinement set's members fold by sorted child
hash — so two subtrees can hash equal while holding the same children in
different physical positions. The descent within an anchor therefore pairs each
child with an equal-hash child still free on the other side (`map_isomorphic`),
not with the child at the same index, which would pair a record's field `a`
against its field `b`.

*Duplicate resolution.* Small subtrees always repeat — `0`, `true`, `x`. Every
equal-hash pairing is an equally valid "shared" classification, but not an
equally *useful* one: the copy chosen decides whether the node reads as sitting
still or as having moved, and which siblings are left over for the later phases.
Among free candidates the matcher takes the one in the most structurally
corresponding position — parent already matched to this node's parent, then the
longest agreeing chain of ancestor node kinds, then the closest depth. An
arbitrary choice here manufactures a spurious move and a spurious delete/insert
pair for the copy it displaced.

**2. Root anchoring.** Two programs being diffed are two versions of one
program, so their roots correspond by construction and are anchored to each
other if phase 1 has not already done it. Nothing else can establish that: a
root that gained a statement fails phase 3's similarity test (see below), and
the result is that the entire program reads as deleted-and-reinserted for a
one-statement edit. The anchor requires the two roots to be the same node kind,
so two genuinely unrelated programs still correspond nowhere.

**3. Bottom-up container recovery.** An interior node left unmatched is paired
with the best same-kind candidate in the other tree that *contains* enough of
its already-matched descendants, processed children-before-parents. This is what
keeps an inserted statement from desynchronizing the whole `let` spine below it:
the unchanged tail anchors in phase 1, and the containers above it are recovered
here instead of being reported as wholesale rewrites.

*Containment and tightness are separate questions.* GumTree gates this on the
Dice coefficient, `2·common / (|desc 𝑢| + |desc 𝑤|)`, which asks "how much of
these two subtrees is shared" — and that is the wrong question when one side is
the side that grew. A container that gained a statement has its own
contribution swamped by the new material and scores below the threshold, so the
very edit the phase exists to absorb is the one it rejects. The gate is
therefore the **overlap coefficient**, `common / min(|desc 𝑢|, |desc 𝑤|)`: "is
one of these essentially inside the other", which is exactly the insertion (and,
symmetrically, the deletion) question. Dice stays as the *ranking* among
candidates that pass — the candidates all contain the same matched descendants
and so are nested in one another, and Dice's growing denominator picks the
innermost, the container that fits tightest.

**4. Optimal recovery inside a paired container.** Phases 1–3 match by
whole-subtree equality and by container similarity; neither can pair two
subtrees that are nearly identical but differ somewhere inside. That gap is what
makes a one-token edit read as a delete plus an insert. This phase closes it: as
each container pair is established, compute the **tree** edit distance between
the two subtrees — Zhang–Shasha, the tree analogue of Levenshtein, over trees
rather than strings — and adopt every pair its minimum-cost script aligns whose
nodes are same-kind and still unmatched. The **label** the distance compares at
each node is that node's content hash, so relabelling is free when the hashes
agree and costs one otherwise, alongside unit costs for deleting and inserting a
node. Pairs from phases 2 and 3 are the only ones that need this — a phase-1
pair is isomorphic by construction, so there is nothing left unmatched beneath
it.

GumTree reaches for RTED, which computes the same optimal mapping faster by
choosing a better decomposition strategy — the difference is asymptotic cost,
not the result. Recovery declines when either subtree holds more than 100 nodes
(GumTree's default), since tree edit distance is `O(𝑛²𝑚²)` in the worst case;
those pairs keep only what phases 1–3 found, and their still-unmatched interiors
are reported as deleted and new rather than aligned.

**5. Classification along two axes.** Every correspondence is labelled with
whether its **content** changed and whether its **placement** did. These are
independent: a node can keep its content and move, or stay put and change.

*Content* compares two hashes, giving three outcomes:

| `resolved_hash` | `own_hash` | | |
| --- | --- | --- | --- |
| equal | equal | `Same` | identical computation, reusable wholesale |
| differs | equal | `ChangedBelow` | the node's own content is intact; what differs is under it |
| differs | differs | `Changed` | the node itself differs, whatever its children did |

*Placement* is the child-alignment step from Chawathe et al.'s edit-script
derivation, which GumTree inherits. A node is `InPlace` iff it hangs off the
corresponding parent and kept its order relative to its matched siblings.
Order-insensitive containers skip the test.

Ordering is decided per matched container pair. Number the container's matched
children by where their counterparts sit under the corresponding container in
the other tree — a child's **destination position**. Taking the children in
source order gives a sequence of destination positions, and a *longest
increasing subsequence* of it is the largest set of children whose relative
order both versions agree on. Those are `InPlace`; every child left off it is
`Moved`, and the set left off is minimal, so the classification names the fewest
moves that account for the permutation. Two children **cross** when one precedes
the other in the source container and follows it in the destination; a
crossing is what forces at least one of the pair off the subsequence.

A source-only node is **deleted**; a target-only node is **new**. A relocated
subtree is reported as moved once, at its root — its descendants stay in place
relative to it.

### The actionable form: divergences and shared roots

The classification is complete but says the same thing many times. `Diff::matched`
holds every node correspondence and `deleted` / `new` hold the unmatched nodes of each side, so
every *ancestor* of an edit is in `matched` with changed content and every
*descendant* of an inserted subtree is in `new` — one literal edited at the
bottom of a forty-binding spine leaves forty-two changed correspondences, of
which exactly one is the edit. A consumer reading `matched` directly would have
to re-derive the interesting set every time, so the differ derives it once.

**`divergences()`** is the set of places the two programs disagree, at the
granularity a version guard is placed. Three kinds —

- *Changed* — both programs have a node here and it is the node that changed.
  Reported when the node's own content differs (`Content::Changed`), and also
  when only its subtree differs (`Content::ChangedBelow`) and nothing under it
  was reported — a reordering of unchanged children, or a type resolved from
  outside the subtree, has nowhere deeper to point.
- *Inserted* — the root of a subtree the new program has and the old does not.
  Reported where the new region begins, not once per node in it. The walk
  continues underneath: a matched node can sit inside a new region — a new
  expression wrapping content that survived — and what diverges under it still
  counts.
- *Deleted* — the mirror image, at the root of what the old program had.

Those two rules cut the set in each direction, and neither is a minimality
theorem: the result is small on the shapes the tests measure, not provably
smallest. A node whose own content is intact is not reported beside the child
that explains it, so a container that only gained a statement yields one site,
the insertion, rather than two. A node whose own content changed is reported
even when a child changed too, so a record that relabelled one field and edited
another yields both. Suppressing the second would be the unsound direction: a
real change left with no site, hidden behind the one below it.

Each kind is reported at its own root, so no two divergences of the same kind
nest. Across kinds they can: a `Changed` may sit inside an `Inserted` or a
`Deleted`, because the walk descends under a new region to find what survived
inside it. A consumer placing one guard per divergence gets nested guards there.

**`shared_roots()`** is the other side: every node whose content is unchanged
and whose parent's is not — the largest subtrees the two versions have in
common, and so the units of reuse. A `Same` node's whole subtree is `Same`, so
its descendants add nothing.

Reuse here means *the term is the same term*, which is what a unified tree
needs. It does not mean the term evaluates to the same value in both versions:
`let x = 1 in x` and `let x = 2 in x` share the body `x`, and that is right —
the two `let`s are the divergence, and it is the binding that differs, not the
read. Whether the two versions' *values* can share one storage entry is decided
per store key at runtime, by comparing what each version wrote; nothing in the
tree answers it. See
[The next analysis: divergence reachability](#the-next-analysis-divergence-reachability).

### Reading a diff

A [`Diff`](../diff.rs) renders itself as an annotated tree of the **new**
program, followed by whatever the old program had that the new one dropped.

Take these two versions:

```
# v1                      # v2
a = 1                     a = 1
a                         b = sum([i * 2 for i in [1,2,3]])
                          a + b
```

Diffed at the lowered phase they render as:

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

Every line of the tree is one node of v2, indented by its depth, and the marker
in the first column says what the diff concluded about it. The `-` lines after
the tree are v1 nodes, which is why the program above — it deletes nothing —
shows none:

| Marker | Meaning |
| --- | --- |
| `=` | matched, content unchanged |
| `~` | matched, content changed — the node itself, or something under it |
| `+` | in v2 only |
| `-` | in v1 only, listed after the tree since it has no place in v2 |
| `»` | suffix: this node's placement changed |

A node carries a column marker and, when it moved, the suffix: `= a »` is v1's
`a` unchanged but relocated, which is what happens when `a` becomes the left
operand of `a + b`. Only v2's side of a move is shown, because the rendering is
v2's tree; the node's position in v1 is reached through `Match::src`.

The trailing `…` is truncation, not a marker. Each line renders that node's
subterm with `symbolic` and keeps the first line, cut to a fixed width, so a
leaf prints exactly and an interior node prints its head — `let a = 1…` is the
whole `let`, elided after its bound expression. That costs `O(𝑛²)` text and is
an inspection surface rather than a hot path, but it keeps the rendering from
drifting out of step with the AST the way a second, shallow node vocabulary
would.

Two rules keep the tree short. An unchanged subtree is not descended into, since
it is unchanged all the way down. A wholly-new or wholly-deleted region collapses
to its root with a node count — `(+12 nodes)` above. A node that appeared or
vanished *around* content that survived does not collapse: the new `a + b` is
shown with the reused `a` under it, because claiming `a` changed would be false.

### Worked example: one literal, and the duplicates around it

A changed literal with the guard threshold edited to `1`, diffed at the lowered
phase:

```
# v1                      # v2
v = 5                     v = 5
1 if v > 0 else 2         1 if v > 1 else 2
```

The ternary lowers to a guard-based `Case`, so v1 already contains a literal `1`
as the then-branch value, and v2 contains a second one as the guard threshold.

| v1 | | v2 | Content / Placement |
| --- | --- | --- | --- |
| `let v = 5` | ~ | `let v = 5` | `ChangedBelow` / `InPlace` |
| `5` | = | `5` | `Same` / `InPlace` |
| `{ v > 0 → 1; true → 2 }` | ~ | `{ v > 1 → 1; true → 2 }` | `ChangedBelow` / `InPlace` |
| `v > 0` | ~ | `v > 1` | `ChangedBelow` / `InPlace` |
| `v` | = | `v` | `Same` / `InPlace` |
| `0` | ~ | `1` | `Changed` / `InPlace` |
| `1` | = | `1` | `Same` / `InPlace` |
| `true` | = | `true` | `Same` / `InPlace` |
| `2` | = | `2` | `Same` / `InPlace` |

Nothing deleted, nothing new, nothing moved. One node is `Changed` — the
literal — and `divergences()` reports that one; the three `ChangedBelow`
containers above it are reflecting it, not adding to it.

Both gap-closing phases are load-bearing here. Duplicate resolution keeps the
branch-body `1` matched to the branch-body `1` rather than to the new guard
threshold, and optimal recovery pairs `0` with `1` instead of reporting a delete
and an insert.

---

## Which phase to diff

`compile_to(code, phase)` runs the pipeline to `phase`'s output and hands back
the tree. It runs `run_frontend`, the same function `compile_program` runs, with
a stop phase instead of a continuation into operator conversion — so the tree a
diff is taken over is the tree the real pipeline produces, and a program
`compile_program` refuses yields no tree. `both_entry_points_compile_to_one_tree`
pins that at `Planning` using this differ.

The axis is [`Phase`](../context.rs), the compiler's own enumeration of its
phases, whose declaration order is pipeline order. A **position** in the pipeline
is a phase's output, and there is exactly one vocabulary for it: a stop for a
diff, a pane the inspector retains, and the range endpoint
`ProvenanceTable::deaths` reads are the same thing named the same way. `run_passes`
expresses each one as a single `at_phase_output` call.

Every phase output is a legal stop — each has a consistency wall after it, so
none of them is a half-formed tree. What follows is which ones answer which
question, not which ones are well-formed.

| Phase output | Tree | What it shows |
| --- | --- | --- |
| `Lower` | `Raw` names, pre-uniquify, pre-inference; most types `Hole` | Closest to source, minimal diffs. Type sensitivity comes only from annotations and lowering-built types (cast refinements). |
| `Uniquify` | the same tree with every binder α-renamed | Nothing a diff can see: the hash is uid-robust, so this diffs identically to `Lower`. It is a position because the inspector's upstream pane is taken here. |
| `Infer` | every node carrying its resolved type | Everything above, plus type-level divergence the earlier positions cannot see. |
| `Inline` | inferred, then UDF-inlined | Everything above, with function boundaries erased — see "How much to normalize". |
| `Transact` | `with begin():` writers rewritten to `LetRec` | Half of the mutability rewrite. Diffing here reports a shape no source construct corresponds to; the position exists for provenance and debugging. |
| `Letrec` | induction loops folded to `LetRec` too | The other half. Same caveat. |
| `Channelize` | mutability eliminated, feeds routed | The compiler's shape rather than the user's — `For`/`MutWrite`/`Begin`/`Defer` are gone. Taken *before* the as-of-read rewrite. |
| `AsOfRead` | fed-out mutable reads rewritten to as-of joins | **The last tree that still has binders**, and the one `lambda_elim` consumes. Fully typed and fully mutability-eliminated, while an edit still localizes the way it does at the phases above — see below. |
| `LambdaElim` | point-free combinators | No binders in the term at all. |
| `Planning` | recurrences on the `Transact` carrier, joins planned | The shape operator conversion consumes, and where compute sharing is decided. |

A later phase carries signal the term structure alone does not: in `x = 1` /
`(x, x)` versus `x = "a"` / `(x, x)` the bodies are structurally identical and
hash equal before inference, and after inference the element type diverges so
the same subterm no longer matches (`inference_adds_type_signal`).

`AsOfRead` is the position to reach for when the question is about a compiled
program rather than a source edit. It is the last point before the term goes
point-free — measured on a transaction program, three `Lambda` nodes survive
there and none survive `LambdaElim` — so it is the deepest tree in which a
binder still names something the user wrote. An edit costs the same there as at
`Channelize` and less than below it: a filter-threshold change is one site at
`AsOfRead`, two at `LambdaElim`, ten at `Planning`.

`Transact` and `Letrec` are the two positions to avoid for a source-level diff.
They are one rewrite of the user's loops and feeds into `LetRec` recurrences, and
stopping between them reports the compiler's shape mid-rewrite; `Channelize` is
where that rewrite is complete. The tree is consistent at both, which is why they
are reachable at all — a caller debugging a phase wants them.

## How much to normalize

Two questions want two different phases, and neither one dominates.

**What runs together** is a question about the operator graph, so it is asked at
`Planning` — the shape operator conversion consumes, and therefore the only phase
where a claim about sharing compute is a claim about what executes. Anything a
version guard or a shared store is derived from is read there.

**Which source edit is this** is a question about the program the user wrote, so
it is asked at the earliest phase that can see the edit at all. Every pass
between the two rewrites the user's shape, and a rewrite spreads one edit over
more of the tree: at `Planning` a comprehension's threshold change is four sites
rather than one, and an accumulator's body change carries fourteen new nodes
rather than two. Those extra sites are the same edit, reported once per place
the compiler copied it to, which is signal about the graph and noise about the
source.

Two programs can also be the same computation written differently. The more of
that the diff sees through, the more the two versions share — and the less
localized the answer becomes when they genuinely differ. Choosing a phase is
choosing where on that curve to sit; the compiler's own passes do the work, so
there is no separate rewriting system to keep honest.

Divergences reported, measured on the refactors that occur. The counts are
measurements rather than invariants: `inlining_erases_function_boundaries` and
`inlining_costs_locality_in_a_shared_helper` pin the direction of each contrast,
not the numbers. Each row names the pair it was measured on, so the numbers can
be reproduced and a drift in them is visible.

| Edit | Measured on | `Infer` | `Inline` |
| --- | --- | --- | --- |
| rename a binding | `x = 1; y = x + 2; y` → `q = 1; y = q + 2; y` | 0 | 0 |
| extract a subexpression into a `def` | `a = 1; (a + 2) * 3` → the same via `def g(y): y + 2` | 5 | **0** |
| edit a body inside a `def` called once | `y + 2` → `y + 5`, one call site | 1 | 1 |
| edit a body inside a `def` called **twice**, one specialization | the same edit, called at `a = 1 + 1` and `b = 2 + 2` | 1 | **2** |
| edit a body inside a `def` called **twice**, two specializations | the same edit, called at `g(1)` and `g(2)` | **2** | 3 |
| reorder two independent bindings | `a = 1; b = 2; a + b` → `b = 2; a = 1; a + b` | 2 | 2 |
| extract a subexpression into a `let` | `(a + 2) * (a + 2)` → `t = a + 2; t * t` | 6 | 6 |

Inlining is a trade, not an improvement: it makes moving code across a function
boundary invisible, and in exchange reports an edit inside a shared helper once
per call site, because the body it changed now appears once per call site. It is
the phase to pick when refactoring across function boundaries is the noise to
remove.

### `Infer` has already spent some of that locality

The two "called twice" rows are the *same edit to the same helper*, and they
differ only in whether the two call sites share a specialization. That is the
whole content of the second row's `Infer` cell being 2 rather than 1:
**monomorphization runs inside `infer`**, so a definition used at two distinct
instantiation identities is already two clones before the differ sees it, and
the edit is reported at both.

Whether two uses share a specialization is decided by a
[`SpecKey`](type-inference.md#keying-a-specialization), which is
polarity-complete and therefore sees an argument's *lower-bound* refinements. A
literal argument carries its singleton, so `g(1)` and `g(2)` key apart and split
the helper; `g(a)` and `g(b)` for two computed `Int`s key together and do not.
Inlining then costs one further duplication per call site on top of whatever
monomorphization already did — 1 → 2 in the shared row, 2 → 3 in the split one.

`Infer` is therefore the earliest phase this differ offers, not a phase that
has normalized nothing: the curve starts before its column.

Below `Inline` the trade continues — every pass that rewrites the user's shape
spreads one edit over more of the tree. No test pins these counts either:

| Edit | Measured on | `Inline` | `Channelize` | `LambdaElim` | `Planning` |
| --- | --- | --- | --- | --- | --- |
| a literal | `a = 1; b = 2; a + b` → `b = 3` | 2 | 2 | 3 | 3 |
| a comprehension's filter threshold | `FILTER_AGG` → `FILTER_AGG_21` (`>= 18` → `>= 21`) | 1 | 1 | 2 | **10** |
| an accumulator loop's body | `ACCUM` → `acc + i * 2` | 1 (2 new) | 1 (2 new) | 1 (**14 new**) | 1 (14 new) |
| a transactional register's write | `TXN` → `pool - r - 1` | 1 (2 new) | 1 (2 new) | 2 (8 new) | 2 (8 new) |

Two of those columns need reading carefully.

**A literal edit is two sites, not one, from `Infer` down.** A literal's type
is its singleton (`Int@2`), and that singleton rides the type of every *read* of
the binding, so editing `b = 2` to `b = 3` changes the literal and every `b`
that mentions it. Both are real: a consumer sharing the read would be sharing a
value that differs.

**The `Planning` cell for the filter threshold is 10 because a term inside a type
is reported wherever that type is mentioned.** A comprehension filter lowers to
a refinement predicate, which is a term living in a type. The differ gives that
term one home — the `Cast` whose target holds it, reached as a child — but by
`Planning` the same predicate rides the type of every operator the refined domain
flows through: `sum`, `restrict`, and a `zip`/`const`/`ge` triple per leg. Each
of those is a leaf, so each is its own site, and the count scales with how far
the domain travels rather than with the size of the edit. Eight of the ten carry
the *same* predicate term. Collapsing them is a real option — `Refinement`'s
predicate is a shared `Rc` by design (`src/ccl/ty.rs`), so the mentions are
identifiable — and it is not done here. See
[Open threads](#open-threads).

The rule this leaves: diff at the earliest phase that can see the edit, unless
the answer is about the graph that runs, in which case diff at `Planning`.
Reaching past `Inline` is not a better diff of the source; it is a diff of a
different object.

### What is not normalized

**Extracting a subexpression into a `let`.** `(a + 2) * (a + 2)` and
`let t = a + 2 in t * t` have the same value and are not the same program here:
naming a subexpression is how CCL says "compute this once".

The two compile to different operator graphs. A `Let` binding compiles to
`FanOut(Memo(bound_op))` and every use of the binder branches that one fan
([`operator_conversion.rs`](../../interpreter/operator_conversion.rs)), while a
repeated subterm is converted once per occurrence — operator conversion has no
common-subexpression pass. So `a = 5; (a + 2) * (a + 2)` builds two `BinOp(+)`
operators over one shared `a`, and `a = 5; t = a + 2; t * t` builds one, with the
second use a back-reference to its fan. For a system that shares compute between
versions that difference is the change, and reporting it is correct.

The `Inline` phase does not erase it: `inline` beta-reduces function bindings,
not value bindings.

**Commutativity.** `a + b` and `b + a` differ by one divergence. Normalizing
them would need type direction, because `+` is string concatenation as well as
addition and is not commutative there — so it is available only post-inference,
for a rare edit, at the cost of making the hash type-conditional. Not worth it.

**Constant folding, β/η reduction beyond UDF inlining.** Each widens the
equivalence class and costs locality the same way inlining does. Nothing
observed yet asks for them; the roadmap is driven by missed sharing that shows
up in practice, not by completeness.

### The one that needs more than a phase

Reordering two independent bindings is a true no-op — CCL's `let` is
non-recursive and pure, so the operator graph depends on the dependency DAG, not
on the written order — and no phase fixes it, because the nesting is the order.
See "Open threads".

---

## Beyond the analysis: branching

The analysis stops at the classification. What gets built from it is running two
versions with their common work shared, and upgrading one to the next without
rewriting the history the old one produced. Three constraints follow.

*The divergence frontier is the input.* `divergences()` says where a version
guard goes; `shared_roots()` says what the two versions can compute once. That
is why both are derived here rather than left to the consumer.

*A guard needs a clock, and the domain says whether there is one.* A divergence
inside a domain that is both ordered and event-anchored (`Txn`, a live source)
can be guarded; one inside a batch region — literal data, a finite loop — cannot,
because there is no position at which its answer changes. Neither property is
carried in the type today, so this is an approximation read off the domain of
the enclosing function rather than something checkable.

*A branch needs no new node.* It is an ordinary `Case` on the sequencing
domain, so nothing in the diff's output has to be a construct the rest of the
pipeline does not already understand.

### The next analysis: divergence reachability

Running two versions side by side means giving each its own copy of any state
they could disagree about, and of no other state. The question is per mutable
variable and per sink: **is any divergence upstream of it in the dataflow
graph?** If none is, the two versions provably write it identically and it needs
one store; if one is, it needs a store per version (or copy-on-write, where the
values happen to agree anyway — a runtime concern, not this one).

It is a reachability query over `divergences()` rather than new matching work,
and it is what makes a second version cost the diff rather than 2×. Not built.

---

## Open threads

**Substitution's transport mode still restates the scoping rules.**
[`ccl/scope.rs`](../scope.rs) now holds them once and every *observing* walk
reads from it, but `subst`'s `Subst::apply_expr_inner` — the mode that returns a
rewritten copy rather than mutating in place — cannot: it rebuilds each node,
and a rebuild is a per-variant `match` by construction. Routing it through the
shared walk would mean cloning the whole subtree at every binding node (clone
the node, then overwrite its children), which turns substitution down a `let`
spine from linear into quadratic in the spine's depth — the one shape Cambra
programs are reliably deep in. Its arms are guarded only by review; if a binding
form is ever added, `scope.rs` is the compile error that should prompt a look
here.

**A term inside a type is reported at every node whose type mentions it.** A
refinement predicate is a term, and the same predicate `Rc` rides the type of
every node the refined domain reaches. The differ gives the term one home — the
`Cast` whose target holds it — but the other mentions are leaves, so each is its
own divergence, and one threshold edit is ten sites at `Planning` (measured in
"How much to normalize"). Eight of those ten carry one predicate.

The direction of a fix is available rather than speculative: `Refinement`'s
predicate is a shared `Rc` by design (`src/ccl/ty.rs`), so a mention is
identifiable by pointer, and a node whose only change is a predicate already
reported at its home need not be its own site. What that costs is a
correspondence between the two versions' predicates — `Rc` identity is
per-compilation, so the two sides have to be related through the matching, which
is the same circularity the free-variable seam has. Not attempted.

Separately, the `sum` and `restrict` mentions in that measurement carry *three*
distinct `Rc`s holding one predicate, where `Refinement::predicate`'s own doc
comment says a predicate rides many slots as one shared `Rc`. Whether some pass
rebuilds per occurrence there, or those are legitimately independent mints, is
unexamined.

**Child enumeration is written out twice.** `diff`'s `child_exprs` mirrors
`TypedExpr::walk_children` arm for arm, differing only in that it descends into
a `Cast` target's refinement predicate (a load-bearing term that
`walk_children` treats as a type child). Both matches are exhaustive, so a new
node variant is a compile error in both places.

The exhaustiveness is not the whole risk, and one defect has already come from
the other half: nothing checks that a given walk picks the *right* one of the
two. `subtree_entirely_in` and `size_note` walked `walk_children` while their
callers walked `child_exprs`, so a deleted `Cast` whose predicate still held a
matched node tested as wholly deleted. Both now walk `child_exprs`
(`a_deleted_cast_with_a_surviving_predicate_is_not_wholly_deleted`), and the
selection stays a review-time judgment at each call site.

**A `let` spine encodes an order it does not have.** A run of independent
bindings is a dependency DAG, but CCL spells it as nested `Let`s. Order
insensitivity does not reach it: that rule is about the *children of one node* —
a `Record`'s fields, a `DisjointJoin`'s operands — and a run of bindings is not
one node's children but a chain of nodes, each the body of the one above. So
reordering two bindings changes the tree's shape rather than a child order, the
matcher pairs the spine by depth, and the reads underneath resolve to
non-corresponding binders and report as changed. Conservative, but noise: two
divergences for two reordered bindings. **Decided: leave it.**

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

The consistency is the finding: the nesting is the order, so no amount of
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
