# Program branching

Cambra programs evolve, and the point of the system is that the *diff between
two versions* is something the compiler and runtime can act on rather than an
opaque redeploy. [diffing.md](diffing.md) works out what changed. This document
works out what to build from it.

Nothing here is implemented. The diff analysis it consumes is.

---

## Why replay makes this a real problem

In an ordinary stack, upgrading is easy to describe: stop the old binary, start
the new one, and the database is still there. State survives because it is
*stored*.

Cambra's state is not stored, it is **derived**. A mutable variable *is* a
function from a sequencing domain to a value ([mutability.md](mutability.md)),
so a register's contents are a function of the inputs that produced them. Start
the program again and the history is recomputed from those inputs.

That is what makes an upgrade non-trivial: **replaying yesterday's inputs
through today's code rewrites yesterday**. If v0 priced an order at list and v1
discounts it, restarting under v1 does not just change future prices — it
changes what the ledger says happened last week.

So the artifact an upgrade needs is a program that replays the past *as it
actually happened* and the future under the new logic. That is what branching
builds, and it is why the feature exists at all.

---

## Three features, not one

"Program branching" has been used for three things with different costs and
different prerequisites. They are worth separating before designing any of them.

**Compute sharing.** Run two versions; evaluate what they have in common once.
No time, no state, no cutover — an optimization, and the diff already answers it
(`shared_roots()`).

**Upgrade.** *One* timeline. The logic changes at a branch point; there is one
store, one output stream, one set of clients. This is the feature this document
is about.

**Fork.** *Two* timelines from a common ancestor, both live, each with its own
state and its own readers. Genuinely different: it needs state duplication,
reader routing, and a drain or merge policy. Deferred.

And one deliberately cut: **retroactive change**, a branch point in the past. It
needs durable, replayable inputs reaching back to that point, and it is
incoherent for anything with external effects — an HTTP response already sent
cannot be unsent. Most of the machinery an earlier draft of this design carried
(backfill windows, streaming catch-up, blast radius through the read-dependency
graph, obsoletion oracles) existed only to serve it. Cutting it removes that
machinery rather than deferring it.

---

## A branch is a guard on the sequencing domain

The central claim: **branching needs no new AST node and no new runtime
operator.**

A writer's decision body is already evaluated at a known position of its
sequencing domain. So "v0's logic before 𝑡ₙ, v1's after" is

```
λ t → if t < t_new then body_v0(t) else body_v1(t)
```

— an ordinary `Case`. It type-checks by the existing rule (both arms the same
type), lowers by the existing rules, and runs on the existing commit operator,
which already evaluates the body once per transaction.

This is not hypothetical. For a register written from a stream, the compiled
group is

```
__commits = λ __r : source(stdin) →
    let __t : Txn = __r ▷ begin
    in (time:          __t,
        write_targets: (last),
        decision:      (__r ▷ source(stdin)) ▷ (λ __txp → (commit: true, writes: (__txp.0))))
```

Editing what the block stores lands on `writes: (__txp.0)`, and `__t : Txn` is
bound by a `let` directly above it — lexically in scope at the divergence, and
captured by an inserted guard exactly as any other free variable would be.
Lambda elimination already threads captures.

So a **`Versioned` node is the wrong shape**. It would be a runtime mechanism
for something the substrate can already express. What *would* force one is
branching on **who is observing** rather than **when** — that is the fork case,
and an observer is not a position in any of the program's domains.

---

## Timeline regions and batch regions

A guard needs something to compare against, and not every part of a program has
one. Take four edits to one program:

```
last: Mut(String, Txn) := "(none)"     # (d) the seed

for msg in stdin():
    with begin():
        last := msg                     # (a) inside the transaction

total := 0
for x in [1, 2, 3]:
    total := total + 1                  # (c) a batch loop

["> " + m for m in stdin()]             # (b) a stream-indexed view
```

**(a) has a clock.** `__t : Txn` is in scope, as above. Guardable.

**(b) could have one, and does not.** The edit lands inside
`λ __iter_record : source(stdin) → __iter_record ▷ source(stdin) ▷ (λ m → "> " + m)`,
where the only thing in scope is the element. Guarding it needs the element to
carry a time — `req.time`, which the [CHL spec](../../../docs/chl-spec.md) marks
**[Tentative]** along with `restrict`. A clock is *conceivable* here; it is not
implemented.

**(c) cannot have one.** The edit lands in a loop over `[1, 2, 3]`, domain
`UIntRange(3)`. This is not a missing clock — the loop is not a timeline. It is
recomputed from scratch on every run, and there is no position at which its
answer stops being v0's and starts being v1's. No clock can be added, because
there is nothing for a clock to index.

**(d) is inert.** The seed compiles to the `get_prev_txn` default — the value
used when no commit precedes 𝑡. Every position where it matters is before the
branch point, so a changed seed silently never takes effect. Not an error;
worth a diagnostic.

So a program partitions into

- **timeline regions**, indexed by a domain that advances with real time (`Txn`,
  live sources) — a cutover is meaningful; and
- **batch regions**, over literal data and finite loops — a cutover is
  *meaningless*, not merely unavailable.

The differ classifies this for free: the region kind is the domain of the
enclosing function, which is already on the node's type. `Divergence` plus that
domain gives the partition with no new analysis.

---

## Where the guard goes

For each divergence, walk up to the **nearest enclosing timeline region** and
put the guard there.

That rule is what dissolves the awkward case. A batch region cannot cut over,
but a batch region *consumed by* a timeline region can still be versioned — at
the point of consumption, where a clock exists. Both versions of the batch
region are computed; the guard selects between their results as they enter the
timeline. Only the *differing* part is duplicated, because everything the diff
calls shared is literally one subtree.

A divergence with no enclosing timeline region — a batch region feeding only an
output, or a wholly batch program — has no guard site, and the whole region
takes v1. That is the right answer: a program with no history has no past to
preserve.

---

## The branch point is deployment time

**𝑡ₙ is fixed at the moment of deployment.** It is not a parameter the user
chooses. Four reasons, in descending order of force.

**It is the only value with no mixture window.** Batch regions switch at
restart, because they have no clock to hold them back. Timeline regions switch
at 𝑡ₙ. If 𝑡ₙ is later than the restart, then between the two the running program
is *neither version* — v1's batch answers feeding v0's transaction logic. Where
a batch region computes something the transaction logic depends on (a pricing
table, a threshold), that mixture can violate an invariant both versions
individually satisfy. Setting 𝑡ₙ to the deployment makes the window empty. The
alternative — holding batch regions at v0 until 𝑡ₙ — means running both, which
is a fork, not an upgrade.

**A future 𝑡ₙ only buys scheduling.** The reason to want one is "cut over at
midnight". That is a deployment-orchestration concern, and it is served just as
well by deploying at midnight. It does not need to be in the language.

**There is no way to denote a commit position anyway.** `Txn` is an anonymous
total order whose positions exist only in the tile; there is no syntax for a
specific one. "The next commit after deploy" is a sentinel rather than a value —
and at deployment, that sentinel is exactly what is at hand.

**A past 𝑡ₙ is already cut**, for the reasons above.

### What must be durable

Once 𝑡ₙ is the deployment, it is the **one fact that has to outlive the process**.
Everything else is derived: state is a function of the inputs, and the inputs
are replayed. 𝑡ₙ is not, because it records something about the world — when the
operator deployed — that no input contains.

So a deployed program carries a small durable **deployment log**: the branch
points of the versions merged into it, as positions in the replayed timeline.
This is a much weaker requirement than persisting state, and it is the only
persistence the upgrade model needs.

### What this gives up

Scheduled cutover, and with it any story where the branch point is a first-class
value the program can reason about. Re-introducing a future 𝑡ₙ later means
solving the mixture window, which means holding both versions' batch regions —
i.e. it becomes a fork. That is a coherent extension, not a contradiction, but
it is the fork feature and should be priced as one.

---

## State belongs to the program, not the version

There is one `inventory`, and both versions write it. State is state *of the
program*, not of a version — which is what an operator expects (you do not fork
your database to ship a pricing change) and what distinguishes upgrade from
fork.

Consequences worth accepting explicitly:

- **A changed initializer is inert.** A seed applies at position 0, which is
  always before the branch point.
- **A type-breaking store change cannot be guarded.** The store has one type. It
  is a rejection, or it needs an explicit migration; a guard cannot express two
  types for one register.
- **Adding a register is fine** — unwritten, it reads its seed. **Removing one is
  fine if unread.**

---

## What this needs that does not exist yet

In dependency order.

1. **A value-selecting `Case` must compile.** Only the filter form does today; a
   value `Case` errors at lambda elimination. This is an existing gap with a
   planned fix — the path-condition fan-out to a union of restricts described in
   [mutability.md](mutability.md), "General in-transaction conditionals (and
   conditional writes)". Its shape *is* the branch shape: `⧺ᵢ (source | pathᵢ ≫ 𝑒ᵢ)`
   is "v0 restricted below 𝑡ₙ, unioned with v1 at or above it". Branching
   motivates that work rather than adding to it.
2. **`http_serve` must stop binding at lowering.** It binds its socket while
   lowering, so two versions of one service cannot be compiled in the same
   process — the second fails with `Address already in use`. That blocks
   *diffing* a real serving program, let alone merging one. Binding belongs at
   graph construction. Small, and on the critical path for demonstrating any of
   this.
3. **A clock on stream elements** (`req.time`), for divergences in stream-indexed
   regions outside a block. Without it those divergences have no guard site and
   fall back to whole-region replacement.

---

## Milestones

**M1 — merge.** Two programs plus a branch point in, one CCL tree out: guards at
the divergences, everything else shared literally. Testable with no persistence,
because replay *is* the model — run the merged program over a full input stream
and assert the prefix matches v0's output and the suffix v1's. Needs (1) and (2)
above; the corpus is `http_counter` and the accumulator loops, since the
transactional serving programs are still gap programs.

**M2 — measure the sharing.** What fraction of the merged graph is one node.
This is the actual value proposition, and nothing currently quantifies it.

**M3 — fork.** Only after M1 and M2, and only if the version-as-a-domain sketch
below survives scrutiny.

---

## Open questions

**Is a fork a domain?** The tidiest sketch: a forked program is
`Version ⇒ Outputs`, versions are positions of an index domain, stores become
`Version ⇒ Txn ⇒ V`, and sharing falls out of subterms being *constant* over the
version dimension — the same tiling machinery as everything else, rather than a
bolted-on sharing mechanism. Unknown whether the machinery supports a
non-causal index domain used this way, and whether the engine can exploit
constancy over it. Attractive enough to test before designing an alternative.

**A retry that crosses 𝑡ₙ.** Optimistic concurrency assigns a fresh commit time
on retry, so a transaction can begin under v0's logic and commit under v1's.
Defensible — a retry is a fresh attempt — but it should be a decision, not an
accident.

**Do we still want a marker?** Once a branch is a plain `Case`, "which version
produced this output" is not recoverable from the tree. Attribution, rendering,
and per-version diagnostics may want a marker that the runtime ignores. That is
a different justification from the one this document rejects.

**Stacking.** v0 → v1 → v2. Squash to base-to-tip, or compose guards? Composing
gives per-version attribution and a growing conditional; squashing keeps the
tree flat and loses the intermediate history. Interacts with the marker
question.

**Diagnostics for unguardable divergences.** A changed seed is inert; a changed
batch region silently rewrites its part of the past on replay. Both are cases
where the user's edit does not mean what they think. The merge should say so,
and the wording matters more than the mechanism.
