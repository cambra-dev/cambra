# Program diffing — content addressing and correspondence

[`diff`](../diff.rs) matches nodes in two CCL trees and classifies changes to their content and
placement. It uses [`content_hash`](../content_hash.rs) to select candidate matches, then resolves
free variables through the resulting binder correspondence to classify them.

The result identifies candidates for shared computation; it does not construct shared operators,
migrate state or switch running versions. The analysis is a library, not a pass called by
[`compile_program`](../context.rs). Runtime uses are described separately under
[Beyond the analysis: branching](#beyond-the-analysis-branching).

---

## Inputs, output, and what holds of it

`diff` accepts two [`TypedExpr`](../expr.rs) trees. Callers comparing program versions supply
trees from the same [`Phase`](../context.rs); the function does not inspect phase metadata or
require a shared source history. `diff_programs` compiles both source programs to one requested
phase and passes the borrowed result to a callback. Compilation errors are returned before diffing.

[`Diff`](../diff.rs) borrows both trees. Its `matched` entries classify content and placement
independently; `deleted` and `new` contain source-only and target-only nodes. `divergences()`
reduces these entries to change sites. `shared_roots()` returns the maximal disjoint regions
classified as unchanged under this correspondence, not a globally maximal sharing arrangement.

The following tests cover the stated cases:

| | Held by |
| --- | --- |
| Two compilations of each corpus source diff as identical, at every phase | `every_phase_diffs_identical_source_as_identical` |
| Identical programs have no divergences and one shared root | `identical_programs_have_no_divergences` |
| Two lowerings that differ only in binder uids diff as identical | `diff_is_robust_to_uid_nondeterminism` |
| A renamed binding retains its correspondence | `renaming_a_binding_is_not_a_change` |
| One edit deep in a `let` spine is exactly one divergence, at the edited node | `one_edit_is_one_divergence` |
| Shared roots are pairwise disjoint, each the top of its region | `shared_roots_are_maximal_and_disjoint` |
| Two terms differing only in an inferred type hash apart | `inference_adds_type_signal` |

There is no minimality guarantee for `divergences()`; its reduction rules are specified under
[The actionable form](#the-actionable-form-divergences-and-shared-roots). A correspondence can
miss sharing opportunities; see [Direction of error](#direction-of-error). Hash comparison also
assumes no collisions; see [Content addressing modulo α](#content-addressing-modulo-α).

---

## Diffing at a glance

1. `Indexed::build` hashes each subterm independently. Variables bound outside that subterm
   contribute their spellings; variables bound inside it contribute positional references.
2. `top_down` anchors equal-hash subtrees largest-first. `anchor_roots` pairs the roots only
   when both are unmatched and have the same node kind. `bottom_up` recovers containers from
   matched descendants. `recover` aligns unmatched interiors of selected container pairs by
   tree edit distance, subject to its size limit.
3. `classify` computes `resolved_hash` and `own_hash` using the binder correspondence. The first
   includes the subtree; the second excludes children and selected type slots to distinguish
   a local edit from changes propagated from descendants.
4. `classify` assigns content and placement independently. The `Diff` methods derive change
   sites and shared roots from these classifications.

Matching precedes classification: it has no binder correspondence to resolve free names through.
The matching algorithm and recovery limits are specified under
[The correspondence: a GumTree matcher](#the-correspondence-a-gumtree-matcher).

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

`ContentHash` is a 64-bit fingerprint computed with `DefaultHasher`. Bound term variables are
hashed positionally; free-variable identity depends on the selected hash operation. Hashing also
normalizes the order of designated set-shaped structures and omits unresolved type identities.
The rules below define those comparisons, not general denotational equivalence.

The matcher and classifier compare fingerprints without a subsequent structural equality check.
Their interpretation of equal hashes assumes no collisions; 64-bit equality is not a proof of
equivalence. A collision can produce a false match or a false unchanged classification.

### Why α-invariance is the problem

Uniquification gives binders fresh uids that can differ between compilations of the same source.
`hash_name_ref` therefore searches the current binder environment from innermost to outermost
and hashes the matching De Bruijn index. Renaming a binder and its bound references does not
change that index; lexical shadowing resolves to the innermost matching name.

In `content_hash`, a reference with no binder inside the hashed subterm contributes `Name::base`
through `hash_free_var`. Consequently, the standalone hash of `x + 2` differs from that of
`y + 2`, even when the surrounding programs differ only by renaming that binding. Hashing the
whole binding scope still treats its bound references positionally.

Conversely, standalone references to distinct external binders with the same spelling hash alike.
Classification resolves this ambiguity through the binder correspondence described below.
Reordering independent bindings can change the correspondence; see [Open threads](#open-threads).

### Three hashes, three questions

The operations differ in their treatment of external binders and the fields they include:

| Property | `content_hash` | `resolved_hash` | `own_hash` |
| --- | --- | --- | --- |
| Purpose | Select candidate matches | Classify a matched subtree | Localize a change to a node |
| External reference found in supplied scope | No supplied scope; use `Name::base` | Use binder token | Use binder token |
| External reference absent from supplied scope | Use `Name::base` | Use tagged spelling fallback | Use tagged spelling fallback |
| Child terms | Include | Include | Exclude |
| Node and binder `ty`; cast target | Include | Include | Exclude |
| Node and binder `user_annotation` | Include | Include | Include |

`resolved_hashes` builds the external scope from the node correspondence. A matched source node
uses its destination node's index as its owner token. An unmatched source node uses an index
outside the destination tree's range. `mix` combines that token with each binder's position
within its owner, distinguishing the binders of a `LetRec` group. `hash_free_var` searches this
scope from innermost to outermost. A reference absent from the scope falls back to its spelling,
with a tag distinct from the resolved-token case.

Corresponding binders can therefore have different spellings without changing the resolved hash.
Distinct binders with the same spelling are distinguished by their tokens. Using a root-relative
De Bruijn index instead would make an inserted enclosing binder change references to otherwise
unchanged outer bindings; correspondence tokens identify the binder rather than its distance.

`own_hash` includes the node discriminant, local payload from `hash_payload`, direct variable
and register-key references, and user annotations. Local payload includes literal values,
operators, variant tags, record labels, binding transparency and the domain and parameter types
of `Transact`. Excluding a node's inferred `ty` does not exclude every type-valued payload.

The excluded node and binder types can change because a descendant changed. Including them
would report the same edit at both the descendant and its enclosing binding. Cast targets are
also excluded: the differ visits their domain-refinement predicates as children, so including
the target again would duplicate a predicate edit at the cast.

For a `Let`, the own hash includes its discriminant, binding transparency and the node's and
binder's user annotations. It excludes the binder's name, inferred type, definition and body.
Changing only the definition's literal or consistently renaming the binder leaves this own hash
unchanged. Changing an annotation or binding transparency can change it.

`classify` compares the resolved hashes first. Equality gives `Content::Same`; otherwise, equal
own hashes give `Content::ChangedBelow`, and unequal own hashes give `Content::Changed`.
`divergences()` can still report a `ChangedBelow` node when no descendant explains the change.
Thus a type-only change can be reported at a container even though `own_hash` excludes its `ty`.

#### Direction of error

A suboptimal correspondence can report unchanged work as changed. For example, positional
matching of reordered independent `Let` bindings can assign different tokens to corresponding
uses. This loses a sharing opportunity. An incorrect `Content::Same` would instead permit sharing
different computations. The intended conservative direction of matching errors does not remove
the [hash-collision assumption](#content-addressing-modulo-α).

### Standalone hashing is the matcher's precondition

`hash_all` enumerates expression nodes and computes each node's whole-subterm `content_hash`
with a fresh binder environment. Its map keys are pointers into the input tree and are valid
only while that tree remains at those addresses. The matcher computes standalone hashes during
`Indexed::build` rather than consuming this map.

A binder above the subterm is absent from the fresh environment, so its references hash as free.
This lets the matcher compare a subterm at different depths without incorporating its enclosing
binder chain. The classifier adds that context after matching.

The sum of subterm sizes bounds the repeated term visits by `O(𝑛 · depth)` for a tree of `𝑛`
nodes. This is not a complete running-time bound: binder lookup scans the environment, types
can contain predicate terms, and set-shaped structures sort their hash contributions. The
implementation does not cache per-subterm free-variable summaries.

### The hash is type-aware

`content_hash` and `resolved_hash` include each node's inferred type, user annotation, binder
types and cast target. `hash_type` hashes the type discriminant and the payload selected by
its constructor. A changed refinement predicate can therefore change the fingerprint without
changing the enclosing expression's term structure. The exclusions for `own_hash` are listed
under [Three hashes, three questions](#three-hashes-three-questions).

Refinement predicates are terms and are hashed by `hash_rel` with the current term environment
and free-variable policy. Their hashes are sorted before folding. Record and variant fields
likewise contribute sorted hashes of their key/type pairs; variant openness also participates.
Tuple fields remain positional. A `ChanDom` contributes its channel's spelling, not its uid or
channel level. Function Pi-binder names are not hashed.

A function contributes its `FunKind` discriminant. A kind variable additionally contributes its
resolved kind, but not its allocation identity. Sum binders contribute their count, kinds and
kind children; their IDs extend a witness environment over the domain and codomain. A
`WitnessRef` found in that environment contributes its innermost-first position.

Recursive type fields and refinement predicate terms retain the enclosing witness environment,
including the types attached to predicate nodes. Nested sums extend that environment for their
body and restore it on return. A witness absent from the environment contributes only the
`WitnessRef` discriminant, so external witness identities remain indistinguishable. This limitation
is separate from accidental 64-bit collisions.

`Hole`, `SharedHole` and `Infer` contribute their respective discriminants, without IDs or
inference bounds. A `BoundedHole` includes its bound. Before inference, annotations and
lowering-built types can already contribute concrete structure; node types are not uniformly
`Hole`. The public hashing functions do not enforce a compiler-phase precondition, so callers
must not use these fingerprints as a complete comparison of unresolved inference state.

### A name rendered into a string is past the point uid-robustness applies

Hashing can ignore a `Name`'s uid only while the value is represented as a name. A record label or
projection key is a string; its bytes participate in the hash without name normalization.

`Name::field_key` therefore uses the base spelling for mutable-variable record fields. A
`Transact` consumer resolves those labels in its own `keys_map`, so labels need to be unique
within that record, not across all transactions or loops. Including a uid would make independently
compiled copies of the same source produce different labels and hashes.

User variable spellings provide the record's key labels. Generated reply taps use
`Name::defer_tap_field` and the reserved double-underscore namespace. The construction sites
must preserve distinctness: `hist_record` in `planning/loops.rs` and key-map insertion sites in
`interpreter/operator_conversion.rs` check it with debug assertions. The spelling-only label
does not itself enforce uniqueness.

A pass that converts a name to a string must establish both label stability across compilations
and uniqueness within the consuming record. Hashing cannot recover either property afterward.

### Order-insensitivity where the language is

The hash folds record fields as sorted label/hash pairs, `DisjointJoin` operands as sorted child
hashes, and refinement sets as sorted predicate hashes. These operations ignore a permutation of
the entries they sort. They do not flatten nested joins or prove general algebraic equivalence.

Tuples, lists, `Compose` chains and `Copair` operands retain position order. In particular,
copair operand order determines the coproduct tags; it is not the same operation as
[disjoint join](ir.md#copair-and-disjointjoin--two-collection-combining-operations-not-one).

The matcher handles unordered children in two places:

- `map_isomorphic` pairs free children by equal hash, not physical position.
- `align_children` skips the order test for `Record` and `DisjointJoin` parents.

A cast has a separate convention. `cast_target_predicates` exposes predicates only when its
target is a function with an immediately refined domain. It returns those predicates sorted by
standalone content hash, after the cast's value child. This gives the ordered matcher a
canonical predicate enumeration under the hash assumptions. It is not a traversal of every
predicate in every type slot, and colliding predicate hashes have no structural tie-break.

`records_are_order_insensitive_tuples_are_not`, `disjoint_join_is_order_insensitive` and
`copair_is_order_sensitive` test the corresponding hash cases. Reversed-refinement-order tests
exercise independence from a refinement set's physical order; they are not a collision proof.

### Scoping comes from one place

`hash_rel` reads term references, key references and scoped children from
[`for_each_scoped_item`](../scope.rs). It extends the binder environment only for the binders
reported on each child and restores the previous depth afterward.

`resolved_hashes` uses the same scoped-child information to attach correspondence tokens to
introduced binders. The matcher also visits cast-target predicates, which are absent from the
ordinary term-child scope walk. Such a predicate inherits the cast's surrounding term scope;
the walk introduces no additional term binders for it.

Payload hashing and child-order normalization remain local to `content_hash.rs`. They are not
scope rules. In particular, the shared term-scope walk does not remove the separate
[type-witness hashing limitations](#the-hash-is-type-aware).

## The correspondence: a GumTree matcher

[`diff.rs`](../diff.rs) implements a greedy structural correspondence followed by classification.
It uses equal-hash anchors, descendant overlap and bounded tree-edit recovery. It does not
establish a globally optimal correspondence or check denotational equivalence.

`Indexed` assigns each visited node a pre-order index. A node at index `i` occupies
`[i, i + size)` with its descendants; the root counts toward `size`. The index also records
height, depth, parent, direct children, node kind and standalone hash. `child_exprs` defines
the visited tree, including the cast predicates described above.

### Equal-hash anchoring

The interpretation of hash equality is specified in
[Content addressing modulo α](#content-addressing-modulo-α). The matcher pairs the descendants
by hash without a structural equality check. Tallest-first traversal lets an anchor claim its
descendants before they are considered separately.

`top_down` processes source nodes by decreasing height, then decreasing subtree size. It
looks up unmatched destination nodes with the same standalone hash. `best_candidate` ranks
multiple free candidates by:

1. Whether their parents already correspond, treating two roots as corresponding.
2. The length of the equal-kind prefix of their ancestor chains, starting at the parents.
3. The smallest depth difference.
4. The earliest destination pre-order index.

The selected pair enters `map_isomorphic`. Its children are paired greedily with unused,
unmatched destination children of equal hash. Already-matched source children are skipped.
Existing matches are not overwritten during that descent.

The helper's name expresses the intended interpretation of equal hashes, not a structural
verification. A root pair is selected by hash without an additional node-kind test. The
[hash collision and identity qualifications](#content-addressing-modulo-α) apply throughout.

### Root anchoring and container recovery

`anchor_roots` pairs the roots only if both remain unmatched and their node kinds agree.
It then invokes `recover`. This provides a recovery boundary even when no descendant anchor
exists. Same-kind roots need not have a shared source history; different-kind roots can still
contain descendants matched by the preceding pass.

`bottom_up` processes unmatched interior source nodes in increasing height. Nodes without
matched descendants are skipped. A candidate destination must be unmatched, interior and of
the same kind.

Let `common` count source descendants whose matches lie strictly inside the candidate, and
let `s` and `d` be the two descendant counts, excluding the roots. Candidate selection uses:

| Test | Formula | Effect |
|---|---|---|
| Admission | `common / min(s, d) >= 0.5` | At least half of the smaller descendant set must correspond inside the other subtree. |
| Ranking | `2 * common / (s + d)` | Select the admitted candidate with the greatest Dice score. |

A zero-common candidate is rejected. Equal ranking scores retain the earliest destination
candidate. Candidates need not be nested or contain exactly the same matched descendants.
The smaller-denominator admission test admits growth that a Dice threshold could reject;
Dice remains a ranking rule, not an admission threshold.

Each selected pair is recorded immediately, then passed to `recover`. Later decisions therefore
depend on earlier matches; this is not a global assignment.

### Bounded tree-edit recovery

`recover` runs when root anchoring or bottom-up recovery establishes a pair. It declines if
either subtree exceeds `MAX_RECOVERY_SIZE`, currently 100 nodes including the root. Earlier
matches remain; unmatched nodes may still be considered by later bottom-up iterations.

`ted::mapping` computes an ordered tree-edit mapping using a Zhang–Shasha dynamic program.
Deletion and insertion each cost one. Relabelling depends on existing anchors:

| Pair | Relabel cost |
|---|---:|
| Already matched to each other | 0 |
| Both unmatched, equal standalone hashes | 0 |
| Both unmatched, unequal standalone hashes | 1 |
| Either matched to a different node | 3 |

The conflicting-anchor cost exceeds deleting and inserting the pair. Backtracking prefers
deletion, then insertion, before relabelling when costs tie. `recover` adopts only returned
pairs whose nodes remain unmatched and have the same kind.

The dynamic program minimizes that edit cost within the selected subtrees. The retained
same-kind subset and the complete matcher are not therefore globally optimal. The size cap
bounds the inputs to the expensive recovery step; it is not a limit on the overall diff size.

### Content classification

Classification follows matching. `resolved_hashes` gives both sides of a matched binder owner
the same destination-index token. An unmatched source owner receives a token outside the
destination index range. `mix` combines the owner token with the binder's position when a node
introduces several binders. This distinguishes references to different members of one group.

Each correspondence is classified using the two scope-resolved hashes:

| Whole-subtree hash | Own-content hash | Classification |
|---|---|---|
| Equal | Not used to select the result | `Same` |
| Different | Equal | `ChangedBelow` |
| Different | Different | `Changed` |

The own-content boundary is specified under
[Three hashes, three questions](#three-hashes-three-questions). It excludes selected type slots,
so `ChangedBelow` does not imply that a visited child must explain the difference.
`classify` debug-asserts that equal whole-subtree hashes imply equal own-content hashes; it
does not perform a structural equality check.

### Placement classification

Placement is independent of content. Two matched roots are `InPlace`. Under a matched parent
pair, a matched source child is eligible to stay in place only if its destination is a direct
child of the corresponding parent. A child matched elsewhere is `Moved`.

For an unordered parent, every eligible child is in place. Otherwise `align_children` takes
one longest strictly increasing subsequence of the children's destination positions, in source
child order. Children on that subsequence are `InPlace`; the rest are `Moved`.
This minimizes moves for that fixed sibling correspondence, not for all possible matchings.

A child can remain in place relative to its parent when the parent moved. A crossing pair
requires at least one move, not necessarily both. `longest_increasing` selects one solution
when several longest subsequences exist.

### The actionable form: divergences and shared roots

`Diff::matched` contains every correspondence in source pre-order. `deleted` and `new`
contain unmatched nodes in their respective tree orders. These are node inventories, not
minimal edit scripts.

`divergences()` derives a smaller set of sites with two traversals:

1. The source traversal collects deleted nodes. A wholly deleted subtree is represented by
   its root. A deleted wrapper with surviving descendants is reported and still traversed.
2. The destination traversal reports an inserted node when its parent is matched or it is
   the root. It traverses inserted regions to find surviving matches below them.

For a matched destination node, the traversal visits its children before deciding whether to
report `Changed`. A change to own content is always reported. `ChangedBelow` is reported only
if no descendant site or mapped direct-child deletion explains it.

Inserted sites therefore precede their descendants, matched changed sites follow their
descendants, and deletions are appended afterward. The result is not uniformly pre-order or
post-order.

The reductions do not imply that divergences of one kind never nest. A changed record label
and a changed field value produce nested `Changed` sites, as exercised by
`a_relabelled_field_is_reported_beside_an_edited_sibling`. Deleted wrappers can also be reported
above deleted descendants when the wrapper contains a surviving match. An inserted region can
contain another inserted region below a surviving matched node. There is no minimality theorem.

`shared_roots()` walks the destination tree and stops at each `Same` node it finds. Its results
are disjoint destination regions, maximal within the selected correspondence. The method does
not separately validate every descendant's classification before stopping.

A shared root denotes matching term content under the hash and correspondence rules. It does
not establish equal values across versions. For example, a reference can resolve to corresponding
binders whose definitions changed. Runtime storage sharing requires information beyond this API;
see [divergence reachability](#the-next-analysis-divergence-reachability).

### Reading a diff

`Display for Diff` renders the destination tree followed by deleted source regions.
Its summary counts all shared, updated, moved, deleted and new nodes. The counts are not
disjoint: a matched node can be both updated and moved. Nor do they count rendered lines or
divergence sites.

| Marker | Meaning |
|---|---|
| `=` | Matched node with `Same` content. |
| `~` | Matched node with `Changed` or `ChangedBelow` content. |
| `+` | Destination-only node. |
| `-` | Source-only node, printed after the destination tree. |
| `»` | Suffix on a matched node classified as moved. |

For example, the rendering of these sources shows the surviving `a` reference below its new
`a + b` parent:

```python
# Old source
a = 1
a
```

```python
# New source
a = 1
b = sum([i * 2 for i in [1,2,3]])
a + b
```

`render_collapses_whole_regions_but_not_wrappers` checks this case. The summary begins
`2 shared · 1 changed`, and the moved reference is rendered as `= a »`.

The renderer stops below a `Same` node. It also collapses a wholly inserted or deleted subtree
to its root, with `(+N nodes)` counting omitted descendants, not the root. A wrapper containing
surviving nodes is not wholly new or deleted and is not collapsed on that basis.
All these decisions use `child_exprs`, including its cast predicates.

Each node's label is the first line of its symbolic rendering, truncated to `RENDER_WIDTH`
(currently 68 characters). A trailing `…` indicates truncation or additional symbolic lines.
The function renders the full subterm before taking that prefix, so printing many overlapping
subterms can perform quadratic work in term visits. Embedded type rendering adds its own cost.

### Worked example: one literal, and the duplicates around it

Consider a guard threshold changing from `0` to `1`:

```python
# Old source
v = 5
1 if v > 0 else 2
```

```python
# New source
v = 5
1 if v > 1 else 2
```

At `Lower`, the ternary is a guard-based `Case`. Both versions already contain `1` as a
branch value; only the new version also has it as the threshold. Candidate ranking preserves
the branch-value match, and recovery pairs the old `0` with the new threshold `1`.
The changed literal is `Changed / InPlace`. Its enclosing comparison, case and binding are
`ChangedBelow / InPlace`. Other nodes remain unchanged, with no inserted, deleted or moved nodes.
The one literal is the sole divergence.

This example exercises both duplicate resolution and recovery. It does not imply that every
one-token source edit yields one divergence at every compiler phase.

## Which phase to diff

`diff` accepts trees without checking their phase. `diff_programs` instead compiles both
sources to one requested stop via `compile_to`. That entry point shares `run_frontend` and
`run_passes` with full compilation; it stops before operator conversion and subscription.

[Program Execution Pipeline](../../../docs/design.md#program-execution-pipeline) owns the
complete phase order. The following table states which representation a diff observes:

| Output | Representation relevant to diffing |
|---|---|
| `Lower` | Raw names and lowering-built types/annotations; inference has not run. |
| `Uniquify` | Binder identities made distinct. Hashing ignores the fresh uid component. |
| `Anf` | Compound operands named by fresh bindings before inference. |
| `MutRead` | Mutable reads named so refinements can reference immutable bindings. |
| `Infer` | Types inferred and definitions specialized; mutable-read naming has been undone. |
| `Inline` | Capability bindings inlined and calls beta-reduced. |
| `Transact` / `Letrec` | Intermediate transaction/induction history rewrites. |
| `Channelize` | Deferred collections and feeds rewritten; as-of-read rewriting has not run. |
| `AsOfRead` | Fed-out mutable reads rewritten, before lambda elimination. |
| `LambdaElim` | Point-free term representation before loop recognition and join planning. |
| `Planning` | Planned CCL consumed by operator conversion. |

A stop has passed only the checks reached before it. An immutable write can be returned at
`Lower` and rejected when compilation reaches inference. The
`compile_to_rejects_what_compile_program_rejects` regression distinguishes those cases.
An early snapshot is not evidence that full compilation or execution will succeed.

`Phase` also includes operator conversion for provenance, but `compile_to` returns a CCL
tree, not an operator graph. Asking for a stop beyond the frontend still returns its final
planned tree. Capture boundaries do not each run a universal consistency check.

`both_entry_points_compile_to_one_tree` compares full compilation's AST with `compile_to`
at `Planning` for its tested programs. `inference_adds_type_signal` shows that inferred types
can distinguish structurally similar terms that matched before inference.

## How much to normalize

Choose a stop by the object being compared. Source-edit inspection needs a representation close
to lowering. Comparing planned computations needs `Planning`, but even that CCL correspondence
does not establish runtime state reuse.

Compiler transformations can both remove structural differences and duplicate changed content.
For example, inlining can erase an extracted function boundary while copying an edited helper
body to several call sites. The tests `inlining_erases_function_boundaries` and
`inlining_costs_locality_in_a_shared_helper` cover those two effects.

`Transact` and `Letrec` expose intermediate history rewrites. They are useful for debugging
those passes, but a source edit can appear in machinery with no direct source counterpart.
`AsOfRead` is the last listed stop before lambda elimination; it retains the pointful shape
needed to inspect bindings. Neither phase choice guarantees that one source edit stays one site.

### `Infer` has already spent some of that locality

Inference specializes generalized definitions before the diff sees `Phase::Infer`.
The [specialization key](type-inference.md#keying-a-specialization) includes polarity-complete
type information, so argument refinements can split uses that share a base type.
Two calls with distinct literal singletons can therefore clone one helper before inlining.

A literal edit can also change types on its references. Later passes can repeat a refinement
predicate in several node types. Whole-subtree hashing includes those type slots, while
`child_exprs` exposes only selected cast predicates as separate nodes. One source predicate
edit can consequently yield several sites without representing several independent source edits.

These effects depend on the program, its inferred types and the current transformations.
Historical site-count tables are not API contracts. Tests of a particular contrast do not
establish fixed counts for other programs or a monotonic increase at every phase.

### What is not normalized

The differ has no normalization pass of its own. It compares the trees supplied by the caller.
Any normalization already performed by the selected compiler phase affects those trees.

- Extracting a value expression into a `let` changes the tree and can change operator sharing.
  Operator conversion uses a shared fan for a let-bound value, whereas repeated term occurrences
  are converted separately. The differ does not erase that distinction as common-subexpression
  equivalence.
- Integer `a + b` and `b + a` are not canonicalized by the hash. The same token also denotes
  string concatenation, so a general commutativity rewrite would be wrong.
- The differ does not add constant folding or beta/eta normalization. This does not mean the
  compiler lacks those transformations; phase selection determines which have already run.

### The one that needs more than a phase

Independent immutable bindings are represented by a nested `Let` sequence. Reordering them
changes nesting, not merely the children of an unordered node. A resulting correspondence can
pair different binder owners and classify dependent reads as changed.

The current policy leaves this conservative difference visible. A canonical dependency order
or a different binding-group representation would be separate compiler or analysis work;
see [Open threads](#open-threads).

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
graph?** If none is, the proposed analysis would share one store under the comparison assumptions
in [Content addressing modulo α](#content-addressing-modulo-α). Otherwise it would use a store per
version, or copy-on-write when runtime values agree. Hash-based classification alone does not prove
that the versions write identical values.

It is a reachability query over `divergences()` rather than new matching work,
and it is what makes a second version cost the diff rather than 2×. Not built.

---

## Open threads

The following limitations concern the analysis. They do not authorize runtime-sharing decisions.

### Repeated predicates in types

A predicate can affect the hashes of several nodes while being exposed as a child only at a cast.
The same source edit can therefore produce several divergence sites. Collapsing those sites would
require a cross-version predicate correspondence and a rule proving that the retained site accounts
for every suppressed difference.

A shared `Rc` can identify repeated mentions within one compilation, but not corresponding
predicates across compilations. Some structurally equal predicates can also have distinct
allocations. Pointer identity alone is not the proposed cross-version relation. No such reduction
is implemented, and historical measurements of predicate counts are not invariants.

### Child enumeration and scope maintenance

`child_exprs` and `TypedExpr::walk_children` both enumerate term children exhaustively, with
cast-target predicates added by the differ. Rendering and deletion reduction must use the
differ's enumeration. The regression
`a_deleted_cast_with_a_surviving_predicate_is_not_wholly_deleted` checks that a surviving
predicate prevents its cast from being reported as wholly deleted.

The shared observer in `scope.rs` does not eliminate rebuilding matches in substitution.
`Subst::apply_expr_inner` still reconstructs nodes by variant; changes to binding forms require
review of that traversal as well as the shared scope walk. A unification that clones each entire
subtree before replacing its children would add repeated work on nested binding spines.
No traversal refactor is part of this analysis.

### Independent binding order

Independent `Let` bindings retain their written nesting. Candidate tuning does not remove that
representational difference. The current decision is to leave conservative reorder differences
visible rather than add normalization solely for this case.

Two alternatives remain separate proposals:

- Canonically reorder independent bindings. A content-hash key can reorder unrelated bindings
  after a value edit; a spelling key can do so after a rename. Either key introduces new edit
  sensitivity.
- Introduce a binding-group representation whose independent members are unordered. That would
  affect lowering, inference and subsequent passes, not only the matcher.

Revisit the representation if another compiler requirement also needs such a group. Earlier
candidate-ranking experiments are not an impossibility proof for all matchers.

### Standalone free names

Standalone hashes identify external term references by spelling. Distinct binders sharing a
spelling can therefore supply the same initial anchor key. Classification uses the subsequently
built correspondence, but candidate matching has no such correspondence yet. Improving candidate
identity without assuming the result of matching remains unresolved.
