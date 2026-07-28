# Program branching

Cambra programs evolve, and the point of the system is that the *diff between
two versions* is something the compiler and runtime can act on rather than an
opaque redeploy. [diffing.md](diffing.md) works out what changed. This document
works out what to build from it: upgrading a running program without rewriting
the history it already produced, and running two versions side by side.

Those are not two designs. They are settings of the same three knobs, and the
bulk of this document is one model with upgrade and fork as configurations of
it.

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

## Three knobs, not two features

"Upgrade" and "fork" are not two designs. They are two settings of the same
three knobs, and the other settings are useful too. A **version attachment** is:

1. **Arms** — the versions. From the diff: one tree with selected sites, so the
   arms share everything they have in common rather than being two programs.
2. **A selector** — what decides which arm applies at a given position. Its
   domain is an *existing* domain of the program: the commit clock, or a
   property of an input element.
3. **A state policy** — **shared** (one history, both arms write it) or
   **partitioned** (one history per arm).

|  | shared state | partitioned state |
| --- | --- | --- |
| **time selector** | **upgrade** | rollback-capable cutover |
| **input selector** | **live experiment** — some users get v1's pricing, one inventory | **canary** |
| **no selector** (both arms see everything) | not a version attachment: every input writes twice | **shadow** |

Compute sharing is not a fourth configuration. It is what makes the others
affordable: the arms are one tree, so the marginal cost of a second version is
proportional to the diff rather than to the program.

### Effect ownership is the well-formedness condition

An external sink is a single resource — two versions cannot both answer one HTTP
request. So at every position, **each external effect must have exactly one
owning version**, and the selector has to determine which.

That is not a fourth knob; it is a constraint the three must jointly satisfy,
and two rows of the table fall out of it rather than being posited. The
bottom-left cell is excluded because both arms would drive the same sink (and
write the same register twice per input). **Shadow** is derived, not invented:
it is "v0 owns every effect while v1's state evolves anyway" — which is also why
shadow *must* partition state, since a v1 write into the shared store would
corrupt production.

### Why upgrade is cheap: the dimension collapses

Version is always a dimension. What differs is whether it survives.

Under a **time selector** the version is *functionally determined by the commit
clock*: a register's value at 𝑡 was written by whichever arm the selector picked
at 𝑡. The dimension collapses, and one history `Txn ⇒ 𝑉` suffices — no
duplication, no copy, no reconciliation.

Under an **input selector** the version is independent of 𝑡, so the dimension
survives and the state carries it. That single fact is the whole difference in
cost between upgrade and fork, and it is why they are one design rather than
two.

### What is cut: retroactive change

A branch point in the *past*, because it is incoherent for anything with
external effects — an HTTP response already sent cannot be unsent. Supporting
it would mean backfill windows, streaming catch-up, tracking a change's blast
radius through the read-dependency graph, and an oracle for which inputs are
still replayable; none of that is needed for anything else here.

The exclusion is narrower than it first looks; see "Why the past is still out".

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

What *would* need more than a guard is branching on **who is observing**
rather than **when**: an observer is not a position in any of the program's
domains, so there is nothing to compare against. That is the fork case, and it
is handled by partitioning state rather than by selecting on a clock.

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

### Two properties, not one

The dividing line is sharper than "advances with real time", and it is two
independent properties of the enclosing domain:

- **Ordered** — positions are comparable, so "before the cut" is expressible.
- **Event-anchored** — positions correspond to things that *happened once*, so
  "before the cut" is a fact about history rather than about this run.

A cut is meaningful iff the domain is **both**. Orderedness alone is not enough,
and `UIntRange` is the counterexample: it is perfectly ordered, and cutting a
loop over `[1, 2, 3]` mid-way is still incoherent, because the loop is
recomputed every run and the answer would depend on when someone deployed. A
source arrival is both. Program start is event-anchored — it is an event, and it
happens once — but **not ordered**: §8.5 makes it a *single* event, so it
imposes no relative order among the blocks it triggers, and there is no "before"
within it to cut at.

So a program partitions into **timeline regions** — ordered and event-anchored,
where a cutover is meaningful — and **batch regions**, where it is *meaningless*
rather than merely unavailable.

Both properties are currently implicit. The model already distinguishes them
(§8.5 separates program start from source arrivals precisely on this), but the
type does not carry them, so nothing can check the distinction. Putting them in
the domain's type makes "can this divergence be versioned?" a type question,
which is how the rest of the system already works — mutability is the type, and
the sequencing domain is in the type. Until then the differ approximates it from
the domain of the enclosing function, which is on the node's type already:

| Domain | Ordered | Event-anchored | Cut-overable |
| --- | --- | --- | --- |
| `DataSource(_)` | yes — arrival order | yes | **yes** |
| `Txn` | yes — a total commit order | yes | **yes** |
| `UIntRange(_)` | yes | no — recomputed each run | no |
| program start | no — a single event | yes | no |
| `ChanDom(_, _)` | inherits from the feeding domain | inherits | inherits |

The approximation is exactly this table, and it is an approximation because
`DataSource` is one type covering sources that genuinely differ: a live stream
is ordered, a table snapshot or a sharded stream is not. Splitting that is what
prerequisite (3) below asks for.

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

## The branch point: any cut at or after the frontier, defaulting to now

For a **time selector**, 𝑡ₙ is a consistent cut supplied at deployment. The
**mechanism accepts any cut at or after the current frontier**; the **default
policy** is the frontier at install — cut over now. (An input selector has no 𝑡ₙ
at all — it selects on a property of the input, so nothing here applies to it.)

Defaulting to *now* and *permitting* later are different claims, and only the
first is a simplification worth making. Three reasons the mechanism must not be
restricted to "now":

**"Now" is not available in the distributed case.** Deployment is not a single
event across replicas: each would cut at its own instant, and the merged program
would not be the same program everywhere. Replicas have to *agree* on a cut, and
agreement is not instantaneous — so the agreed cut is necessarily slightly in
the future. A mechanism that only accepts the present cannot express a
replicated deployment at all, and the concurrency section puts distribution
explicitly in scope.

**Loading and switching are separately valuable.** Deploying the merged program
warms it, validates it, and gets it running; choosing when its behaviour changes
is a second decision. Collapsing them forces the risky operation to happen at
the moment you least want to be doing operations.

**Nothing about a future cut is mechanically harder.** The guard is the same
comparison either way. Restricting to "now" would not simplify the compiler; it
would only remove a parameter.

### A future cut leaves no mixture window

Batch regions switch at restart, because nothing can hold them back; timeline
regions switch at 𝑡ₙ. Between the two the program might be expected to run v1's
batch answers against v0's transaction logic, which would break invariants each
version satisfies alone.

The guard-placement rule rules that out. A batch region *consumed by* a timeline
region is versioned at the point of consumption, so v0's transaction logic
consumes v0's batch answer. The apparent residue — a batch region feeding only
an output — is empty too: in a program that has a timeline at all, its sinks are
timeline-driven, so a batch value reaching an output enters a timeline and is
guarded there. A program with no timeline anywhere has nothing to be
inconsistent *with*.

So defaulting to "now" is the obvious default, not the only safe value.

### Why the past is still out

Not for lack of durable inputs — the retention window now supplies those. The
blocker is **effects**: a response already sent cannot be unsent, so recomputing
a past that had external consequences produces a history that disagrees with
what the world already saw.

That narrows the exclusion rather than removing it. A retroactive cut is
incoherent for anything with external sinks; for purely internal state, inside
the retention window, it is not. Whether that narrower case is worth supporting
is open — it is the only remaining route to "fix the bug and recompute what it
corrupted", which is the thing retroactivity was ever wanted for.

### 𝑡ₙ is a consistent cut, not a timestamp

A scalar branch point presumes a global total order over events. That is more
than the model needs and more than a distributed engine can cheaply provide, so
𝑡ₙ is a **consistent cut of the event partial order**: a frontier past which
every event belongs to the new version and before which every event belongs to
the old. A scalar is the degenerate case where the order happens to be total.

A cut is representable — the durability section requires recording one — but
there is no *source syntax* for a commit position, and none is needed: 𝑡ₙ is a
deployment parameter, not something a program mentions.

The alternative — a cut point per source — reintroduces the mixture window
*across sources*: for an interval `/order` runs v1 while `/restock` runs v0, and
if they meet at a shared register that can break an invariant both versions
satisfy alone. The cut has to be consistent with respect to everything that
interacts, which is exactly what a consistent cut means.

The runtime already has the concept: an as-of read "waits only for the
*frontier* (that no earlier-or-equal commit is still outstanding)" (§8.5).

### What must be durable

Everything about *state* is derived — a register is a function of the inputs, and
the inputs are replayed. Three things are not derived, and have to outlive the
process.

**The inputs, with enough order to reproduce the conflicts.** Not a global
arrival order: two events with disjoint footprints commute, so their relative
order is unobservable and reproducing it is wasted work. What must be reproduced
is the transitive closure of the *conflict* relation — which is what the commit
operator already computes for validation. Per-key **write** order does not
suffice: for `T₁` reading 𝐴 and writing 𝐵 against `T₂` writing 𝐴, per-key
sequences record no relation between them, yet their order decides whether `T₁`
saw the new 𝐴. The recorded unit is therefore a position per **footprint** key,
over read ∪ write. That is bounded by the footprint, which the compiler knows
completely — the same fact the concurrency section leans on for distributed
commit, and the reason this stays shardable where a global clock would not.

**The branch points**, as consistent cuts. They record something about the world
— when an operator deployed — that no input contains.

**Nothing else.** In particular, not the state itself, up to the retention
window below.

### Retention, and checkpoints beyond it

Replaying from position 0 keeps state re-derivable and keeps the input log
unbounded, which collides head-on with the store-bounding work (writer-window
compaction, release-driven GC) whose whole purpose is to stop retaining
everything. Both cannot hold.

The resolution is a **retention window**. Inputs are kept for the window; beyond
it a **checkpoint** stands in for them. A checkpoint is the bounded store
contents at a consistent cut, plus the cut — and since as-of reads can reach
backwards, "bounded store contents" means whatever is still readable, which is
exactly what store bounding already computes. So checkpointing is mostly
persisting what is in memory at a frontier, not new machinery.

The window is a **dial, and the user sets it**, up to and including infinity.
That is a cost decision — retaining inputs forever is what buys unlimited
re-derivation — and not one the language should make. What matters is that one
dial governs three things at once:

- **how far back state can be re-derived**,
- **how far back a shadow is meaningful** — "what would v1 have done all along"
  becomes "…since the window opened", and
- **how many arms a merged program carries** (below).

### Why the window is what bounds the version chain

Replaying from a checkpoint rather than from 0 means v0's arm is only needed for
the interval between the checkpoint and 𝑡ₙ. Take a checkpoint *at* the
deployment and that interval is empty — and the merged program is not needed at
all. Deploying v1 against a checkpoint is what an ordinary system does.

So checkpoint-at-deploy would make this whole feature evaporate. What it costs
is the thing the feature exists for: **re-derivability**. A checkpoint that
replaces its inputs is a source of truth, not a cache, and with it go
auditability ("why is this balance 7?" is answerable only by replaying the logic
that was live at the time) and shadow, which needs replay from further back than
the last checkpoint to say anything interesting.

Inside a retention window both hold at once, and the consequence is a clean
answer to how versions stack: **a merged program needs an arm only for versions
deployed inside the window.** Anything older folds into the checkpoint. The
version chain is bounded by retention rather than by history, and v0 → v1 → v2
needs no squash policy — the window does it.

**One concrete failure mode.** A type-breaking store change makes an existing
checkpoint unreadable. It then requires either a migration applied to the
checkpoint or a full re-derive from inputs, which is possible only inside the
window. That gives the type-breaking case an operational meaning rather than a
flat rejection.

### What the default gives up

Only the *interface* for choosing a cut, not the capability. A program cannot
reason about its own branch point, and there is no scheduling UX; both are
additions on top of a mechanism that already accepts the value.

---

## State: shared, or partitioned

### Shared — one history, both arms write it

There is one `inventory`, and both versions write it. That is what an operator
expects (you do not fork your database to ship a pricing change), and under a
time selector it is not merely convenient — the version dimension has collapsed,
so there is nothing to partition.

Consequences worth accepting explicitly:

- **A changed initializer is inert.** A seed applies at position 0, which is
  always before the branch point.
- **A type-breaking store change cannot be guarded.** The store has one type. It
  is a rejection, or it needs an explicit migration; a guard cannot express two
  types for one register.
- **Adding a register is fine** — unwritten, it reads its seed. **Removing one is
  fine if unread.**

### Partitioned — one history per arm

For two versions this is not a new type or a new domain: **instantiate the
writer graph twice, share the subgraph the diff calls common, and give each its
own store.** The "version dimension" is two copies, and sharing is ordinary
graph sharing — the same thing compute sharing already is. `Mut` is untouched.

The alternative — making `Version` a real index domain, so a register is
`Version ⇒ Txn ⇒ 𝑉` and sharing is *constancy over that dimension* — is the
generalization, and it only earns its keep past a handful of versions
(per-tenant, say). Build duplication; keep the domain framing in reserve.

### How much is actually shared

Two answers, and only the first is a compiler question:

- **Static.** The diff *proves* a register can never diverge, because no
  divergence is upstream of it in the dataflow graph. Share unconditionally: one
  store, one writer.
- **Dynamic.** The values happen to agree though the code differs. Copy-on-write
  at the key level — a runtime concern.

The static half is a small new analysis, **divergence reachability**: for each
register and sink, is any divergence upstream? It is the natural next thing to
build on `divergences()` (see [diffing.md](diffing.md)), and it is what makes a
fork cost the diff rather than 2×.

---

## Two things replay decides for us

The replay model settles two questions that would otherwise be free choices, and
in both cases the answer is not the obvious one.

**A shadow forks from the start of the retention window, not from the
deployment.** Seeding v1's store from v0's current state looks natural and is the
*unnatural* move here: it copies state the model says is a function of inputs.
The natural thing is to replay every retained input through v1 — which is also
the honest answer to "what would this change have done?", bounded by how far
back the inputs go. So upgrade and shadow share the replay machinery entirely:
upgrade replays one timeline with a cut-switched selector, shadow replays two.

**The selector must be a deterministic function of inputs.** A canary routing
10% of traffic *randomly* would route differently on replay, so the two runs
would disagree about what happened. Either the selector is derived from
something already in the input (a user-id hash), or the routing decision is
itself recorded as an input. This is forced, not stylistic, and it is much
cheaper to know before someone ships a random split.

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
3. **Ordered, event-anchored positions on source domains**, for divergences in
   stream-indexed regions outside a block — where a `Txn` is not in scope but a
   position is. The spec's `req.time` is one spelling of this; the requirement is
   the two properties, carried in the domain's type so an unordered source
   (a sharded stream, a table snapshot) cannot be cut on by mistake. Imposing an
   order on a source that has none would let a program depend on an ordering that
   does not survive replay — the same class of error as rendering a run-varying
   identity into a stable-looking string. Without this, such divergences have no
   guard site and fall back to whole-region replacement.
4. **A durable input log with per-footprint-key ordering**, and **checkpoints**
   at consistent cuts beyond the retention window. Both are described above; the
   engine already computes the footprints and the bounded store contents, so
   this is mostly persistence rather than new analysis.

---

## Milestones

**M1 — merge (upgrade).** Two programs plus a branch point in, one CCL tree out:
guards at the divergences, everything else shared literally. Testable with no
persistence, because replay *is* the model — run the merged program over a full
input stream and assert the prefix matches v0's output and the suffix v1's.
Needs (1) and (2) above; the corpus is `http_counter` and the accumulator loops,
since the transactional serving programs are still gap programs.

**M2 — measure the sharing.** What fraction of the merged graph is one node,
plus divergence reachability over the registers. This is the actual value
proposition and nothing currently quantifies it.

**M3 — shadow.** Partitioned state, no selector, v0 owns every effect.

Shadow before canary, and before fork generally. It is the differentiated
capability — answering "what would this change have done to production?" without
deploying it is hard to get anywhere else. It has no routing and no
effect-ownership complexity, since v0 owns everything. And it is precisely where
sharing pays: both arms process every input, so the marginal *compute* is
proportional to the divergent part rather than to the program. Storage is the
weaker claim and the one to state carefully — a register is duplicated when
*any* divergence is upstream of it, so a one-token edit high in the dataflow can
duplicate the whole store. The measure to hold M3 to is **divergence
reachability**, not diff size.

**M4 — canary.** An input selector, and with it routing and per-position effect
ownership.

---

## Open questions

**What does a shadow report?** "v1 would have priced 4% of orders differently"
is the output people want. It aligns on **event identity** — for request 𝑅, v0
said 𝑋 and v1 said 𝑌 — not on any position or timestamp, so each arm having its
own commit clock costs nothing here. Divergence in *state* and divergence in
*effects* are probably different reports.

**Are replayed effects suppressed, and by what?** The model rests on replay, and
every serving program has sinks — replaying last week's requests would re-send
last week's responses. There must be a rule, and it is a *third* phase the
document does not have: during replay no version owns effects; past the frontier
the live one does. It also weakens M1's test, which can assert on the replayed
prefix only because a test has no already-emitted past; production replay cannot
observe that prefix at all. This is the largest gap here.

**How does a merge over more than two versions work?** The retention window
implies a merged program carries an arm per version deployed inside it, so N
arms — but the diff is pairwise and the partitioned-state realization is written
for two. An N-way guard and a merge over N trees with maximal sharing are both
undescribed. Chaining pairwise diffs is the obvious approach and is not
obviously the right one.

**What does comparing against a cut mean at a single site?** 𝑡ₙ is a consistent
cut, but the guard is a comparison. Presumably each site compares its own
position against the cut's projection onto its domain — but that is not worked
out, and neither is what the "event partial order" concretely *is* in terms of
the domains a program actually has.

**How does a fork end?** Scoping it to "pick a winner, discard the loser's
state" keeps merging two diverged histories out of the compiler, where it does
not belong. Worth stating rather than assuming.

**Should a shared-state experiment be opt-in separately?** An input selector over
shared state means the experiment is *real* — v1's writes affect v0's users. It
is legitimate and occasionally exactly right, but it should not be reachable by
adjusting a flag that reads like a routing detail.

**A retry that crosses 𝑡ₙ.** Optimistic concurrency assigns a fresh commit time
on retry, so a transaction can begin under v0's logic and commit under v1's.
Defensible — a retry is a fresh attempt — but it should be a decision, not an
accident.

**Does attribution want a marker?** A branch is a plain `Case`, so "which
version produced this output" is not recoverable from the tree. Attribution,
rendering, and per-version diagnostics may want a marker the runtime ignores —
which is a tooling need, distinct from anything the execution model requires.

**Does a global arrival order survive distribution?** Per-footprint-key
sequencing is per-shard, so it should preserve the concurrency section's claim
that a distributed commit is decided from complete local knowledge. Establishing
a *consistent cut* across shards is a weaker requirement than a global clock but
is not free either, and the cost has not been worked out.

**What happens at the window boundary during an upgrade?** A merged program
carries an arm per version deployed inside the retention window. When the window
advances past a branch point, that arm becomes unreachable and should be
collected — which is a live rewrite of a running program, or a redeploy. Neither
is obviously right.

**Diagnostics for unguardable divergences.** A changed seed is inert; a changed
batch region silently rewrites its part of the past on replay. Both are cases
where the user's edit does not mean what they think. The merge should say so,
and the wording matters more than the mechanism.
