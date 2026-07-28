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

## What an upgrade has to solve

**State is stored.** A mutable variable *denotes* a function from a sequencing
domain to a value ([mutability.md](mutability.md)) — derivation is the
*specification* — but the runtime materializes it incrementally as an MVCC
commit log `Txn ⇀ (Key ⇀ Value)` that compacts by the MVCC law and GCs its
released prefix. Persisting state is making that existing structure durable, not
inventing a snapshot format, and the object persisted is a **bounded history**
rather than a point-in-time value. A restart loads it; it does not recompute the
world.

So the hard part of an upgrade is not the past. It is the **transition**:

- **Replicas do not swap atomically.** Each picks up the new binary at its own
  wall-clock moment. Without an agreed switch point they disagree about which
  logic applied to which work, and the disagreement is invisible until something
  downstream depends on it.
- **Work is in flight.** A transaction that begins under one version and commits
  after the swap has to belong to exactly one of them, by a rule stated in
  advance rather than by whichever thread got there first.
- **Draining is not acceptable.** The conventional answer — stop accepting, let
  the old version finish, swap, resume — is downtime, and it gets worse the
  busier the system is.

A version guard on the sequencing domain turns all three into one denotational
fact: both arms are live at once, and each unit of work is assigned to an arm by
its own position. There is no drain because nothing has to stop, and replicas
agree because they compare against the same cut rather than against their own
clocks.

None of that needs the past to be recomputed. What the *past* buys — audit,
shadow over history, correcting derived state after a fix — is a separate
capability with a separate cost, and it is what
["Retention"](#retention-what-keeping-inputs-buys) is about.

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

Not for lack of durable inputs — a retention window supplies those. The
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

**The store**, because that is how the program runs at all — it is the MVCC
commit log made durable, retaining as much history as the program's own as-of
reads can reach. How much that is is not a policy choice: the compiler derives
it from the reads, and the runtime already computes the corresponding compaction
and GC.

**The branch points**, as consistent cuts. They record something about the
world — when an operator deployed — that no input contains, and a replica
joining later has to arrive at the same answer as one that was already running.

**The inputs, optionally**, and that is the subject of the next section.

### Retention: what keeping inputs buys

Nothing above requires retaining inputs. A program that only ever runs *forward*
needs the store and the cuts, and can discard every event once it has been
folded in.

Keeping them is a separate dial, and it buys four things:

- **Audit.** "Why is this balance 7?" is answerable only by replaying the inputs
  that produced it through the logic that was live at the time — which is also
  the one thing that requires *old versions' arms* to stay reachable.
- **Shadow over history.** "What would v1 have done all along", as against the
  cheaper "what will v1 do from here" — see below.
- **Correction.** Re-deriving state after fixing a bug in the logic that
  produced it. Bounded to internal state, for the reasons in "Why the past is
  still out".
- **Checkability.** The store is a materialization of a derivation. With the
  inputs retained, the two can be compared and the materialization falsified;
  without them, the cache is the only account of itself and a bug in incremental
  maintenance is undetectable. This is the reason worth caring about even when
  none of the other three are exercised.

The window is a **cost decision the user makes**, up to and including infinity.
Retaining forever is what buys unlimited audit, and it is a real bill; retaining
nothing is a perfectly coherent configuration that gives up the four items
above and keeps everything else in this document.

Two consequences of whatever value is chosen:

**Replay needs the logic, not just the inputs.** So a merged program keeps an
arm for each version whose branch point is inside the window, and drops it when
the window passes. That bounds the version chain by retention rather than by
history: v0 → v1 → v2 needs no squash policy, because the window is the policy.

**A shadow can only reach as far back as the window.** "What would v1 have done
all along" degrades to "…since the window opened", which for a short window is
close to "from here".

### When persisted state does not fit the new version

Deploying v1 against a store v0 wrote is an implicit claim that the store is a
valid starting point for v1. Usually it is: the values are just values, and v1
reads them the way v0 left them. Two cases where it is not.

**A type-breaking change.** v1 gives a register a type the persisted history is
not in. A guard cannot express two types for one register, so this needs a
**migration** — a function applied to the stored history — or a re-derive from
inputs, which is possible only inside the retention window. The migration is the
normal answer; the re-derive is the one available when the migration is not
expressible.

**A changed initializer.** A seed applies at position 0, which every branch point
is after, so a changed seed is inert against an existing store. Not an error, but
worth a diagnostic: it is a case where the edit does not mean what it looks like.

### What the default gives up

Only the *interface* for choosing a cut, not the capability. A program cannot
reason about its own branch point, and there is no scheduling UX; both are
additions on top of a mechanism that already accepts the value.

---

## State: shared, or partitioned

### Shared — one history, both arms write it

There is one `inventory`, and both versions write it — the store carries on
across the boundary, which is what an operator expects (you do not fork your
database to ship a pricing change). Under a time selector this is not merely
convenient: the version dimension has collapsed, so there is nothing to
partition.

**Adding a register is fine** — absent from the store, it reads its seed.
**Removing one is fine if unread**; its history stops being extended and ages
out under the ordinary GC. Changes the store *cannot* absorb are in "When
persisted state does not fit the new version" above.

### Partitioned — one history per arm

For two versions this is not a new type or a new domain: **instantiate the
writer graph twice, share the subgraph the diff calls common, and give each its
own store.** The "version dimension" is two copies, and sharing is ordinary
graph sharing — the same thing compute sharing already is. `Mut` is untouched.

The second store has to start somewhere, and there are two answers to different
questions:

- **Fork the existing store** at the branch point and run v1 forward from it.
  Cheap, immediate, and copy-on-write — and it answers the question a deployment
  decision actually asks: *given the state we are in, how will v1 behave?* This
  is the default.
- **Replay retained inputs** through v1 from the start of the window. Expensive,
  bounded by retention, and answers a different question: *would v1 have
  produced a different history?* That is an audit question, not a shipping one.

The first is not an approximation of the second. v1 is going to run against
v0's state whatever happens, so starting there is the faithful simulation of
deploying it.

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

## The selector must be a deterministic function of inputs

A canary routing 10% of traffic *randomly* routes differently every time it is
re-run, so a replayed history disagrees with the one that happened, and two
replicas disagree with each other. Either the selector is derived from something
already in the input (a user-id hash), or the routing decision is itself
recorded as an input and becomes part of what the system retains.

This is forced by replicas alone, before retention enters the picture, and it is
much cheaper to know before someone ships a random split.

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
4. **A durable store.** The runtime holds the MVCC commit log and already
   computes its compaction and GC; persisting it is what makes a restart resume
   rather than recompute, and it is a prerequisite for every configuration here.
   Nothing in the analysis changes — this is persistence, not new analysis.
5. **A durable input log with per-footprint-key ordering** — only if audit,
   historical shadow, or correction are wanted. Optional in a way (4) is not,
   and the engine already computes the footprints it needs to be ordered by.

---

## Milestones

**M1 — merge (upgrade).** Two programs plus a branch point in, one CCL tree out:
guards at the divergences, everything else shared literally. Testable ahead of
durable state, because a single process run *is* a timeline — feed one input
stream through the merged program with the cut partway along, and assert the
prefix matches v0's output and the suffix v1's. That is the transition semantics
under test, which is the part that matters; persistence changes where the
timeline starts, not what the guard does. Needs (1) and (2) above; the corpus is
`http_counter` and the accumulator loops, since the transactional serving
programs are still gap programs.

**M2 — measure the sharing.** What fraction of the merged graph is one node,
plus divergence reachability over the registers. This is the actual value
proposition and nothing currently quantifies it.

**M3 — shadow.** Partitioned state, no selector, v0 owns every effect. Forked
from the live store, which needs (4) but not (5): the question is "given the
state we are in, how will v1 behave?", and answering it does not require
retaining a single input. The historical variant comes with (5) and is not part
of this milestone.

Shadow before canary, and before fork generally. It is the differentiated
capability — answering "what will this change do to production?" without
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

**Are replayed effects suppressed, and by what?** Only arises once inputs are
retained and something replays them, but then it arises hard: every serving
program has sinks, and replaying last week's requests would re-send last week's
responses. Effect ownership is defined per *version*; replay needs it defined
per *phase* as well — during a replay no version owns effects, and past the
frontier the live one does. The largest gap in the retention half of this
document, and the reason audit is further off than the forward-running
configurations.

**How does a merge over more than two versions work?** Only with retention: a
forward-running program needs one arm, but keeping inputs means keeping an arm
per version whose branch point is still inside the window, so N. The diff is
pairwise and the partitioned-state realization is written for two. An N-way guard and a merge over N trees with maximal sharing are both
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

**Diagnostics for unguardable divergences.** A changed seed is inert against an
existing store; a changed batch region takes effect wholesale at the next
restart rather than at the cut. Both are cases where the user's edit does not
mean what it looks like. The merge should say so, and the wording matters more
than the mechanism.
