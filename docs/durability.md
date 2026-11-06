# Durability

A run is a function of its **observations**: the values its denotation leaves to the world or to the
runtime. Durability is the guarantee that the run's (non-telemetry) outputs are indistinguishable
under a crash and a pause: after recovery the run continues from what it persisted, which can be
earlier than what it held at the crash. Outputs emitted before and after the crash are parts of one
computation, computed from one set of observations, and no observation an output depends on takes a
second value.

The guarantee covers the run's outputs: the rows its sinks take, its HTTP responses and the
requests of its calls ([Escape](#escape)). The runtime's own reports are not outputs of the run.
Process logs, telemetry and the inspector may record a crash and the recovery after it. The
guarantee holds up to one physical limit: a crash between an effect and the record of it loses an
input or repeats an output
([An effect and its record are not atomic](#an-effect-and-its-record-are-not-atomic)).

In the run's outputs, a crash changes when things happen, never what was observed: an output not yet
emitted at the crash is emitted later, after recovery.

A crash changes no timestamp the run has already shown. A `time::now()` reading that an output
depends on keeps its value, and recomputation answers it from the kept observation, not from the
clock. The only readings a crash may replace are ones no output depends on yet. Nothing that saw the
value left the run, so no outputs conflict with program state ([Escape](#escape)).

A reading taken after recovery can be earlier than one taken before the crash, as two readings
within one process can be ([7.5 Time](chl-spec.md#75-time-decided)). In
`elapsed = time::now() - started`, where `started` is a kept reading of 10:05, a reading of 10:03
after recovery makes `elapsed` negative.

Two conditions follow:

- **Immutable history.** An observation the run keeps has one value for the life of the run,
  across crashes and reloads.
- **Recomputation is limited to determined values.** The runtime recomputes a term only where the
  kept observations determine its value, so the recomputed value is the one already computed.

This document separates what the model requires ([The model](#the-model)) from how a runtime meets
it ([Runtime obligations](#runtime-obligations), [Implementation](#implementation)).

**Status.** Nothing here is implemented. The runtime persists nothing today: a restart starts every
source at position `0` and every store at its declared initializer. The model is **[Tentative]**
except where a section marks a point **[Decided]**. Readings (`__now`, `__random`) and sites, the
keys this document uses, are designed in the effects work and are not on main. This document states
their keying where it needs it.

## Terms

- **Observation.** A value no term of the program determines: a clock reading, a source's arrival or
  end, a transaction's decision, a reload's boundary ([Observations](#observations)).
- **Operator term.** A term whose tile is a function of its inputs' tiles
  ([Observations](#observations)).
- **Observation point.** A term that is not an operator term. The world or the runtime's engine
  supplies its tile, and each entry of the tile is an observation ([Observations](#observations)).
- **Source position.** An element of a source's domain: the number a source gives an element when
  it takes it, or a number the source states no element will take ([Observations](#observations)).
- **Position path.** The position of each loop around a term, outermost first. A loop over a
  source, or over a filter of one, iterates the source's positions, so a term in its body is keyed
  by them. A loop over another collection, such as the keys of a `group_by`, iterates that
  collection's keys ([Observations](#observations)).
- **Program state.** A tile for each term of a program version
  ([The program state an observation map determines](#the-program-state-an-observation-map-determines)).
- **Producer state.** What one runtime producer retains between pulls, which
  `TileProducer::state_info` measures. Once the producer has compacted, it is not a tile of the
  producer's term. "Producer" here means any operator, as in `TileProducer`, and not the producer
  side of a release.
- **Stable storage.** Storage whose contents survive the failures the runtime is built to
  tolerate: a local disk, or a quorum of replicas held in memory.
- **Crash.** A failure that stable storage survives, such as the loss of the process. A failure
  beyond that, such as the loss of every replica, is outside the guarantee, so the choice of stable
  storage decides which failures are crashes.
- **Persist.** Write to stable storage and wait until it confirms the write, so that the write
  survives a crash. An observation is **durable** when stable storage holds it: the run's, or that
  of the system a source reads, which holds it until the source releases it.
- **Escape.** An output escapes when it leaves the run and reaches the world, where the run cannot
  take it back ([Escape](#escape)).
- **Release.** A consumer releases a region of its input to that input's producer, promising never
  to ask for it again. Every operator is a producer to its consumers and a consumer of its inputs.
  A producer compacts a region once every consumer has released it
  ([Compaction](operational-semantics/semantics.md#compaction)). An operator releases a region of
  its own input only once it has persisted what its future outputs need of it
  ([Persisted producer state](#persisted-producer-state)). A source is a consumer of the system it
  reads and releases to it the same way.
- **Persisted producer state.** One producer's producer state and the guard it has released to
  each of its inputs, persisted in one write before a release reaches its input
  ([Persisted producer state](#persisted-producer-state)). Each producer persists its own, and no
  two need to describe one moment of the run.
- **Recovery.** The start of a process after a crash. Each producer starts from its latest
  persisted producer state, or from `⊥` where it has none, and each observation point from its
  persisted observations.

[The life of one arrival](#the-life-of-one-arrival) shows how the steps an arrival goes through,
persisting it, escaping, persisting the producer states it fed, and releasing it, are ordered.

---

## The model

### Observations

An **observation** is a value that no term of the program determines. Every term of a program
version is an operator term or an observation point:

- An **operator term**'s tile is a function of its inputs' tiles, computed by the term's operator
  ([The Operator Contract](operational-semantics/semantics.md#the-operator-contract)). A literal is
  an operator term with no inputs.
- An **observation point** is any other term. The world or the runtime's engine supplies its tile,
  as the world supplies a data source's elements
  ([Integrity properties](operational-semantics/semantics.md#integrity-properties)). Each entry of
  an observation point's tile is an observation.

Every observation has a key built from a site and positions the program already has, so no
construct is added to name one. A source's key is its source position. Every other observation
point is keyed by its site and the position path of the loops around it, and where those loops
iterate a source, the path holds source positions.

| Observation                                                                                                     | Key                                                     | Chosen by              |
| --------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------- | ---------------------- |
| A reading: the clock, a random value, the reply to a call made outside the program                              | the reading's site and its position path                | the world              |
| A source element: the element at a position, or `none` where no element will take it                            | the source and the source position                      | the world              |
| A transaction's decision: `` `commit `` at a tick, or `` `abort `` after one                                    | the block's site and the writer's position path `𝑖`    | the commit engine      |
| An as-of read's sample: the tick a fed-out read latches at                                                      | the read's site and the reading loop's position path    | the `AsOf` operator    |
| A reload: the new version, the boundary guard of each term it pairs, and the seed of each tile it carries whole | the reload's place in its branch's sequence of versions | the runtime's schedule |

- **A reading.** A reading has one value per position path and call path. Its site is the call's
  place and the calls that reached it.
- **A source element.** A source defines a domain: its positions exist because elements arrive.
  The element at a position and the position an element takes are both the world's choice
  ([7.3 Sources](chl-spec.md#73-sources)). A reading is indexed by positions that already exist,
  which is the difference between the two. A source also states `none` at each position no element
  will take: every position past its last element once it ends, and each position its numbering
  skips, such as an offset a compacted topic removed. An output can depend on a `none`: a `sum`
  over a source is final only once the source has ended.
- **A transaction's decision.** `Txn` is a total order that no writer's domain supplies. The
  per-site oracle `begin_<site> : 𝐼 ⇒ Txn` places iteration `𝑖` of a writing site in it
  ([mutability.md](../src/ccl/design/mutability.md#the-model-histories-and-causal-recursion)), and
  each transaction reads the commit history strictly before its place
  ([Semantics](../src/ccl/design/mutability.md#semantics)). The engine realizes `Txn` as the commit
  clock of the store the block writes. The clock is stated as a source is: each position of the
  store's commit order, a **tick**, holds a commit, or `none` where the engine states no commit will
  land. Tick `0` holds the store's seed. One sequencer per store, as the engine has today, gives
  each commit the next tick and states no `none`. A transaction that writes nothing takes no tick.
  Stores that share no mutable variable share no clock. The decisions of every site that writes one
  store form one observation point, the store's **commit clock**, because two of its sites must not
  commit at one tick. The `Transact` node carries the clock, and `CommitOperator` realizes it. A
  decision is `` `commit(𝑇) ``, for a transaction that read the history through tick `𝑇−1`, wrote,
  and committed at `𝑇`, or `` `abort(𝑆) ``, for one that read the history through tick `𝑆` and wrote
  nothing. An abort is a deny, which takes no writing path, or a grant whose write set is empty: it
  writes no store key and fires no in-block reply, and `TransactWriterProducer` finishes it as it
  finishes a deny. The body computes the tag and the writes from what it read, and the engine's
  schedule chooses the tick.
- **An as-of sample.** `AsOf` latches a store's value as of the moment a trigger's position path is
  first observed ([The runtime engines](../src/ccl/design/mutability.md#the-runtime-engines)). The
  sample is the tick on that store's clock it latched at, `0` where nothing had committed. The tick
  depends on the schedule, so it is an observation.
- **A reload.** A reload replaces the operators of one version of a branch with those of the next
  while the terms hold tiles ([4. Reload](operational-semantics/semantics.md#4-reload)). Each term
  the reload pairs is split at a boundary guard, which denotes what the earlier version had decided
  at the swap, or carries its tile whole into the new version as a seed. How far each term had got
  at the swap depends on the schedule
  ([What the properties do not settle](operational-semantics/semantics.md#what-the-properties-do-not-settle)),
  so the guards and the seeds are an observation, taken at the swap.

Operator terms compute every other tile from observations and literals. In the effects work, the
capability `ObserveWorld` marks every reading and every source the program opens, so the compiler
can list the program's world-chosen observation points. The engine-chosen points are the commit
clocks and the as-of samples. The runtime takes a reload's entry when it swaps versions.

### The observation map

The **observation map** `𝑂` is a program state limited to the observation points: it assigns each
observation point `𝑡` a tile `𝑂(𝑡)` of `𝑡`'s tiling. Maps are ordered point by point by the
progress order, as program states are ordered term by term
([The program state an observation map determines](#the-program-state-an-observation-map-determines)).

| Observation point                      | Its tiling                                                                                                                                                                   |
| -------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| A source whose elements have type `𝐸` | partial functions `ℕ ⇀ Option(𝐸)`: `some(𝑒)` where `𝑒` took the position, `none` where the source states no element will                                                  |
| A reading                              | partial functions from call path and position path to value                                                                                                                  |
| A store's commit clock                 | partial functions from site and position path to `` {`commit{ℕ} \| `abort{ℕ}} ``, beside the ticks stated `none`, that commit no tick twice and commit no tick stated `none` |
| An as-of read                          | partial functions from position path to the tick it latched, in `ℕ`                                                                                                          |
| A branch's reloads                     | partial functions from a reload's place in the branch's versions to its version, boundary guards and seeds                                                                   |

A source's tiling is the sparse function tiling of
[The Direction: Tilings for Sparse Functions](operational-semantics/deprecation.md#the-direction-tilings-for-sparse-functions),
whose `nones` predicate holds the `none` entries. A reading's call path is the calls that reached
it, the part of its site the term does not fix: a function that is not inlined holds one reading
term that several call paths reach. A commit clock's tiling is the partial function tiling with `⊕`
defined on fewer pairs: `𝑥 ⊕ 𝑦` is their union when their domains are disjoint, no tick is committed
in both, and no tick committed in one is stated `none` in the other. The sub-tiles of a tile `𝑧` are
still the restrictions of `𝑧` to subsets of its
domain, so the tiling keeps cancellativity and the sub-tile meet
([Universal Split-Determinism](operational-semantics/semantics.md#universal-split-determinism)).

The run's map only grows, and an entry, once present, keeps its value. Writing `𝑂 : Key ⇀ Value`
lists the entries of every `𝑂(𝑡)` under the keys of [Observations](#observations).

### The program state an observation map determines

A **program state** assigns each term of a program version a tile of the term's tiling, as
[The Model](operational-semantics/summary.md#the-model) describes the state of a running program.
A term's tiling is the tiling of its type
([Denotational–Operational Correspondence](operational-semantics/semantics.md#denotationaloperational-correspondence)).
Program states are ordered term by term by the progress order, and the least one holds `⊥` at
every term. `𝜎` stands for a program state and `𝜎(𝑡)` for its tile at term `𝑡`.

Each term has an equation that a program state `𝜎` satisfies or does not:

- **An operator term** `𝑡` with inputs `𝑢₁ … 𝑢ₙ`: `𝜎(𝑡) = op_𝑡(𝜎(𝑢₁), …, 𝜎(𝑢ₙ))`, where `op_𝑡`
  is `𝑡`'s operator, which is monotone
  ([The Operator Contract](operational-semantics/semantics.md#the-operator-contract)).
- **An observation point** `𝑡`: `𝜎(𝑡)` holds the entries of `𝑂(𝑡)` at the keys in `𝑡`'s domain in
  `𝜎`, and no others. A key is in `𝑡`'s domain when, for each loop around `𝑡`, `𝜎` holds the key's
  position in that loop's domain, and the condition of each branch and filter around `𝑡` holds there
  in `𝜎`. A key in `𝑡`'s domain is **reached**.

A source is under no loop or branch, so every key is reached and `𝜎(𝑡)` is `𝑂(𝑡)`. A reading under a
filter or an `if` is reached only at the positions where the condition holds, so an entry of `𝑂` at
a position the program never evaluates is not part of `𝜎`. A reading's key also carries its call
path, and each call path has its own conditions. A function that is not inlined, called from a site
under `if r.ok:` and from a site under no condition, reaches its reading through the second call
path at every position and through the first only where `r.ok` holds. A commit clock's key is
reached through its site's writer loop and the conditions around its `with begin():`. In the
semantics' terms, `𝜎(𝑡)` is the part of `𝑂(𝑡)` inside the guard that selects the reached keys
([The `split` Operation](operational-semantics/semantics.md#the-split-operation)).

**`𝐹(𝑂)`** is the least program state that satisfies every equation. Each right-hand side is
monotone in `𝜎` and in `𝑂`, so every program state reached by applying equations from the least
one, in any order, is below every program state that satisfies them. An iteration that stops with
no tile left to extend
([Termination and Extraction](operational-semantics/semantics.md#termination-and-extraction)) has
reached `𝐹(𝑂)`. In a program with no cycle the equations have one solution; the least one matters
where a cycle, such as a store and its writers, admits several.

For example, in

```python
reqs = stdin()                         # a source: one element per line of standard input
out: Feed((String, time::Instant))     # a feed: the rows the loop appends to it
for r in reqs:
    started = time::now()
    out << (r, started)
```

`reqs` and `time::now()` are observation points, and the pair and `out` are operator terms. Let
`𝑂(reqs)` be `{0 ↦ some(𝑎), 1 ↦ some(𝑏)}` and let the reading's tile in `𝑂` be
`{0 ↦ 10:00, 1 ↦ 10:01}`. Evaluating the terms in dependency order:

1. `reqs` is a source and is under no loop, so every key is reached:
   `𝜎(reqs) = 𝑂(reqs) = {0 ↦ some(𝑎), 1 ↦ some(𝑏)}`.
2. `time::now()` is under `for r in reqs:`, whose domain is `𝜎(reqs)`, holding positions `0` and
   `1`. The reading's keys `0` and `1` are reached, so `𝜎(time::now()) = {0 ↦ 10:00, 1 ↦ 10:01}`.
3. The pair gives `{0 ↦ (𝑎, 10:00), 1 ↦ (𝑏, 10:01)}`, and `out` follows.

This program state satisfies every equation. In a program with no cycle it is the only one, so it
is `𝐹(𝑂)`. An operator term's equation mentions only its inputs, and an observation point's
mentions only `𝑂` and the domains of the loops around it. Every term those equations mention comes
earlier in dependency order.

A store's commit clock supplies the oracles `begin_<site>` of the sites that write the store. A
writer's body at a decided position path reads the store through its decision's snapshot: tick `𝑇−1`
for `` `commit(𝑇) `` and tick `𝑆` for `` `abort(𝑆) ``. The store holds the writes of
`` `commit(𝑇) `` at tick `𝑇`, and its value at `𝑇` is decided once every tick from `1` through `𝑇`
holds a commit or `none`. An operator that read a missing tick as one with no commit would decide a
value at a later tick that the missing commit then changes, and would not be monotone.
`CommitEngine::read_as_of` answers nothing past its watermark.

Two properties follow:

- **`𝐹` is monotone.** `𝑂 ≤ 𝑂′` gives `𝐹(𝑂) ≤ 𝐹(𝑂′)` term by term: iterating the equations for
  `𝑂` from the least program state stays below `𝐹(𝑂′)`.
- **The schedule decides progress, not the answer.** The schedule is the order and timing in which
  the runtime runs operators. Under any schedule, every program state the run reaches while holding
  observations `𝑂` is below `𝐹(𝑂)` term by term. At any moment, an operator's output (its tile in
  `𝐹(𝑂)`) is below the operator applied to its input's tile in `𝐹(𝑂)`. The schedule decides only
  how much of `𝐹(𝑂)` the run has computed. It reaches the answer only through the observations
  it chooses, a clock reading, a commit tick, an as-of sample or a reload's boundary, and those are
  in `𝑂`.

`Out(𝑂)` is `𝐹(𝑂)` at the sink terms: the outputs `𝑂` determines. The durability condition is stated
on `Out`, because sinks outlive versions and internal terms do not.

**Across reloads**, `𝐹(𝑂)` composes over the reload entries in `𝑂`. Before a branch's first reload,
its terms satisfy the first version's equations. A term a reload pairs then holds
`𝑦₁ ⊕ split(inject(𝑓₂), 𝑔₁).outside`, where `𝑦₁ = split(𝐹_𝑣₁(𝑂)(𝑡), 𝑔₁).inside`
([What a reload computes](operational-semantics/semantics.md#what-a-reload-computes)):

- `𝐹_𝑣₁` is `𝐹` for the earlier version's equations, and `𝑡` is the term in that version.
- `𝑔₁` is the reload's boundary guard for the term, from its entry in `𝑂`: the region the earlier
  version had decided at the swap.
- `split(𝑥, 𝑔)` divides a tile `𝑥` at a guard `𝑔` into `.inside`, the part of `𝑥` within `𝑔`, and
  `.outside`, the rest
  ([The `split` Operation](operational-semantics/semantics.md#the-split-operation)).
- `𝑓₂` is the function the new version's term computes, and `inject(𝑓₂)` is the terminal tile that
  holds its whole answer
  ([Formal Definition](operational-semantics/semantics.md#formal-definition)).
- `⊕` combines the two parts, which are disjoint.

The term holds what the earlier version decided inside `𝑔₁` and what the new version computes
outside it. For `doubled = [2 * x for x in orders]` reloaded as `[3 * x for x in orders]` with `𝑔₁`
holding the positions below `500`, the term holds `2 * x` at positions `0` through `499` and `3 * x`
from `500` on. A term the reload carries whole starts from the entry's seed. Each later reload
composes the same way.

### Well-formed maps

`𝑂` is **well-formed** when each of its entries is reached and valid in `𝐹(𝑂)`
([The program state an observation map determines](#the-program-state-an-observation-map-determines)):

- **Reached.** `𝐹(𝑂)` holds the entry at its observation point: its key is in the point's domain in
  `𝐹(𝑂)`.
- **Valid.** A source's `some` or `none` and a reading are valid wherever they are reached. A
  decision is valid when its snapshot is decided in `𝐹(𝑂)` and its writer's body, reading the store
  at that snapshot, computes it: `` `commit(𝑇) `` when the body writes at snapshot `𝑇−1`, and
  `` `abort(𝑆) `` when the body writes nothing at snapshot `𝑆`. An as-of sample at `𝑆` is valid when
  tick `𝑆` is decided. A reload's entry is valid when `𝐹` of the version before it decides, at each
  term the reload pairs, the tile inside the entry's boundary guard.
- **Ordered.** A writer decides the positions of its domain in order
  ([8.5 Ordering and concurrency](chl-spec.md#85-ordering-and-concurrency)). A decision at position
  `𝑝` is valid only when its writer's decision at every earlier position is in `𝑂` and placed no
  later on the clock. A commit at `𝑇` is placed at `𝑇`, and an abort at `𝑆` just after `𝑆`.

`𝐹(𝑂)` is the least solution, so no entry is reached only through itself.

The run's map is well-formed at every moment:

- an arrival is taken before any observation keyed through its source position;
- a writer decides one position before it drives the next;
- the engine takes each clock's ticks in order;
- an as-of sample reads a tick already taken;
- a reload's entry is taken at the swap, from what the earlier version had computed.

Well-formed sub-maps of one map are closed under union. Reach is monotone in `𝑂`, a decided snapshot
keeps its value as `𝑂` grows, and a tag is a terminal scalar, so an entry valid in a smaller map is
valid in a larger one. The durable observations at a crash therefore have a largest well-formed
sub-map, and recovery restores it ([The durability condition](#the-durability-condition)).

Consequences of the definition:

- **A key through a source position needs the element there.** Without `some` at position `7`, a
  loop over the source does not reach `7`, so a reading at position path `7` is not reached. A
  reading kept without its element would answer whichever element takes position `7` after recovery.
- **A clock's commits are contiguous.** `` `commit(𝑇) `` reads through `𝑇−1`, which is decided only
  once every tick below `𝑇` holds a commit or `none`. A well-formed map therefore commits each
  clock's ticks through some `𝑘`, and for well-formed `𝑂 ≤ 𝑂′` the commits of `𝑂` on a clock are
  those of `𝑂′` through `𝑘`.
- **A reading under a condition needs the condition.** A reading inside `if r.ok:` is reached at
  position `7` only where `r.ok` holds there in `𝐹(𝑂)`. That needs the element at `7` and everything
  `r.ok` reads.
- **A decision needs what its body reads.** A body that reads `time::now()` computes its tag only
  where the reading at its key is in `𝑂`. Without that reading, `` `commit(5) `` at position `7` is
  not valid.
- **A key through a derived domain needs what formed it.** In `for g in group_by(orders, sku):`, a
  reading at key `A` is reached only where `𝐹(𝑂)` holds group `A`. After the orders that formed `A`
  are lost, the reading is not reached.
- **A writer's decisions are kept in order.** Suppose a withdrawal at position `𝑝` is denied with
  `` `abort(4) `` and a deposit at `𝑝+1` commits at tick `5`. If the abort is lost because the
  reading its body took was not durable, and the commit is kept, recovery decides `𝑝` again at
  snapshot `5` and grants the withdrawal. It then lands behind the deposit, an order no crash-free
  run produces. The ordering condition makes `` `commit(5) `` invalid without the decision at `𝑝`,
  so the largest well-formed sub-map drops both.
- **Well-formed maps are not downward-closed.** Removing `` `commit(1) `` from a well-formed map
  leaves `` `commit(2) `` reading through an undecided tick, so no guard denotes the well-formed
  maps. Well-formedness says which maps the run can hold; the order between maps is the progress
  order.

### Immutable history

**An observation the run keeps has one value for the life of the run.** The run is the sequence of
versions a program passes through, with every crash and every reload between them. An observation a
crash loses was never part of the run ([Escape](#escape) says which ones may be lost).

- **A crash.** The run after recovery holds the same observation at every key it kept.
- **A reload [Decided].** A reading at a site the reload keeps keeps its value. A site the new
  version moves or adds is a new key and reads anew. Which sites a reload keeps is the site
  stability rule: a site moves only when a place before it with the same module, bindings, kind
  and spelling is added or removed, or when a binding around it is renamed. The version that takes
  a reading does not own it; the run does.

A program needs no mutable variable to keep a reading. In `started = time::now()`, `started` is one
instant for the run, and a reload that keeps the binding keeps the instant, as
[7.5 Time](chl-spec.md#75-time-decided) already states for a top-level binding.

A reading the new version takes can be earlier than one the run kept from an earlier version. In
`deployed = time::now()`, a binding the reload adds, `deployed` reads the clock when the new version
starts, and a kept `started` can be later than it. Readings carry no order
([7.5 Time](chl-spec.md#75-time-decided)).

### Escape

An output **escapes** when it leaves the run and reaches the world, where the run cannot take it
back: a row a sink takes, an HTTP response, or the request of a call made outside the program. A
source's release to the system it reads is a release, not an escape: it withdraws a copy that no
consumer will ask for again, under the rule every release follows
([Persisted producer state](#persisted-producer-state)).

A **support** for a set of outputs `𝐸` is a well-formed map `𝑂ₛ`, below the run's map, with
`𝐸 ≤ Out(𝑂ₛ)` ([Well-formed maps](#well-formed-maps)): observations that determine every output in
`𝐸`. An output can have several supports, and no observation need be in all of them. In
`sum(a ++ b) >= 100`, over two sources `a` and `b` of non-negative numbers, early termination
decides the comparison `true` once the elements seen sum to `100`. With `a₀ = 60`, `b₀ = 50` and
`b₁ = 70`, `true` holds under `{a₀, b₀}`, `{b₀, b₁}` and `{a₀, b₁}`, and no element is in all three.
The supports within one map are closed under union ([Well-formed maps](#well-formed-maps)), so the
runtime can keep any of them.

The alarm sink of `time::alarms()` is not an escape. Its path from sink to source runs through the
runtime, and its held rows are a producer state
([`time::alarms()`](chl-spec.md#timealarms)).

**[Decided]** — an observation in `𝑂ᵣ` keeps its value for the rest of the run; one outside it was
never observed ([The durability condition](#the-durability-condition)). Recovery asks an observation
point again for a key outside `𝑂ᵣ`. The clock answers with a new reading. A source that holds its
elements answers with the same element, because it has not released it. No output can tell the
second answer from the first, because `𝑂ᵣ` holds a support for every output that escaped.

### The durability condition

Let `𝑂₁` be the observation map at a crash and `𝐸` the outputs that escaped before it. Recovery
continues the run from an observation map `𝑂ᵣ` and from restored producer states that satisfy three
conditions:

1. **`𝑂ᵣ` is part of what was observed.** `𝑂ᵣ` is well-formed and `𝑂ᵣ ≤ 𝑂₁`
   ([Well-formed maps](#well-formed-maps)): each entry of `𝑂ᵣ` is an entry of `𝑂₁`, and the commits
   of `𝑂ᵣ` are those of `𝑂₁` through its greatest tick. The runtime invents no observation.
2. **`𝑂ᵣ` accounts for every escape.** `𝐸 ≤ Out(𝑂ᵣ)`: `𝑂ᵣ` holds a support for `𝐸`
   ([Escape](#escape)).
3. **The restored producers stand for `𝑂ᵣ`.** For each producer `𝑢` and each consumer `𝑡` of it:
   - `𝑡`'s restored state stands for a tile below `𝐹(𝑂ᵣ)` at `𝑡`.
   - What `𝑡` has released to `𝑢` is covered by `𝑡`'s restored state.
   - `𝑢` has compacted only regions that the restored guard of every consumer covers. It holds
     everything else, or computes it again from input it has not released.
   - `𝑡`'s restored state and the guard it released come from one write.

The run then grows `𝑂ᵣ` to some final `𝑂` with `𝑂ᵣ ≤ 𝑂`. Condition 3 makes the restored run behave
as a run that held `𝑂ᵣ` from the start: no restored producer holds more than `𝐹(𝑂ᵣ)`, and every
region a restored consumer asks for is held by its producer or computed again from that producer's
input. The run stays below `𝐹(𝑂)` and can reach it. Every output before the crash is below
`Out(𝑂ᵣ)`, every output after it is below `Out(𝑂)`, and `Out(𝑂ᵣ) ≤ Out(𝑂)`, so all of them are parts
of the one answer `Out(𝑂)`. An observation in `𝑂₁` and not in `𝑂ᵣ` is an input the run lost, and
since `𝑂ᵣ` accounts for every escaped output without it, losing it is indistinguishable from never
having received it.

Conditions 1 and 2 alone do not give this. A `sum` over standard input that has released positions
`0` through `900` to its source and is restored at `⊥` meets both: `𝑂ᵣ` holds the lines, and every
escaped output is below `Out(𝑂ᵣ)`. The source has dropped the lines the `sum` released, so the
restored `sum` totals only the lines from `901` on, which no `Out(𝑂)` holds. The second clause of
condition 3 rules this recovery out.

### An effect and its record are not atomic

Durability has a physical limit. The runtime cannot take an observation or emit an output in the
same instant that it persists a record of it, and a crash between the two loses the record:

- **An input is lost.** An arrival from a source that releases on arrival is gone if the run
  crashes before persisting it. Recovery cannot ask the source for it again.
- **An output is repeated.** An output sent before the run records that it was sent is sent again
  after recovery.

**[Decided]** — of the two orders for an output and its record, the runtime sends first, so a
crash repeats an output and never drops one. Losing an input stays the one unavoidable loss, for a
source whose system keeps no copy.

The gap lasts as long as one write to stable storage, and the runtime does not narrow it further.
Closing it needs a record on the other side: a source that holds its elements until released turns a
loss into a redelivery, and a sink that drops keys it has delivered turns a repeat into a recognized
duplicate ([Outputs are keyed](#outputs-are-keyed)).

### Transactions are keyed by their site and position

A transaction's identity is its block's site and its writer's position path. Its decision,
`` `commit(𝑇) `` or `` `abort(𝑆) ``, is the observation at that key ([Observations](#observations)).
The commit record, `` `commit(⟨writes, replies⟩) `` or `` `abort ``, is a function of the commit
history through the decision's snapshot, which is immutable.

So a transaction commits at most once at each key, in every program and not only in a workflow. A
second commit at key `(𝑠, 𝑖)` would be a second value of its decision, which immutable history
forbids. Recomputing a kept transaction's body is permitted: it reads the history through its
snapshot and the readings at its own keys, all kept, and yields the record it yielded before. No
keyed-transaction construct is needed, because the key is the position path every transaction
already has.

An abort is kept as a commit is. `await_final` reads a mutable variable once every writer of it has
drained ([8.6 `await_final`](chl-spec.md#86-await_final)), so its value depends on each writer's
aborts. An abort recomputed against a later snapshot can commit, and the run would then contradict
an `await_final` that escaped.

An optimistic retry inside the engine is not a second commit. A retried body reads the same readings
at the same keys, and only the final decision is an observation. Whether a body may make a call
outside the program is open ([Open questions](#open-questions), a call inside a block).

A decision that writes nothing never reaches the engine's validation, which checks a proposal's read
set against the commits after its snapshot. It counts only once its writer has decided every earlier
position and no commit after its snapshot wrote a key it read; otherwise its writer decides it again
at a later snapshot. A writer with at most one position in flight meets this, as
`TransactWriterProducer` does today: it drives a position only after the one before it is
acknowledged. Without either, a withdrawal decided against a snapshot from before an earlier
deposit's commit is denied for want of money that arrived first
([Well-formed maps](#well-formed-maps)). A writer's commits follow the same order: the engine
commits a writer's proposal at position `𝑝+1` only once the writer's decision at `𝑝` is placed, so a
pipelined `𝑝+1` cannot commit first and leave `𝑝` to retry against its writes.

### Outputs are keyed

A feed is a function over its domain
([8.4 Feeds are the second form of mutability](chl-spec.md#84-feeds-are-the-second-form-of-mutability)),
so every output has a key: the reading loop's position path for a reply outside a block, and the
writer's site and position path for a reply inside one, ordered by its commit's tick. An output at a
key has one value, determined by `𝑂ᵣ`. An output re-emitted after a crash is the same key with the
same value, so a sink, or a remote that accepts an idempotency key, recognizes it.

A sink receives the key with the value, so a re-emitted output can be recognized. A sink records an
output as sent only after sending it, so a crash may at worst repeat an output but never loses one.
The key lets the recipient recognize the repeat
([An effect and its record are not atomic](#an-effect-and-its-record-are-not-atomic)).

The model states which outputs exist. Delivery is the sink's contract. A sink that delivers at
least once and drops a key it has delivered delivers each output once. A remote that acts on a
request it has acted on before is outside what any layer of the run controls.

A call made outside the program is an output and a reading at one key: the request escapes at the
call's site and position path, and the reply is a reading at the same site and position path. A
recomputed call finds its reply in `𝑂ᵣ` and sends nothing.

---

## Runtime obligations

A runtime satisfies [the durability condition](#the-durability-condition) when it meets six
obligations. Each is a requirement on any implementation.

1. **Observation points are enumerable.** Every term whose tile depends on more than its inputs'
   tiles is an observation point, and each of its observations has a key. An operator that reads
   the wall clock, a socket, a random source or the scheduler makes its term an observation point
   the runtime does not know of, which breaks every other obligation silently.

2. **Recovery restores the largest well-formed sub-map of the durable observations, and observation
   points answer its keys from it.** After recovery, and after a reload that keeps a site, a reading
   at a kept key returns the kept value, a source delivers the kept element or `none` at the kept
   source position, and the commit engine reuses a kept decision
   ([Well-formed maps](#well-formed-maps)).

3. **Before an output escapes, the durable observations hold a support for every output escaped so
   far, it included.** An observation is durable when the run has persisted it, or when a source
   that has not released it holds it ([Escape](#escape)).

4. **A kept key is never given to another element, and a redelivered element takes its kept key.** A
   replay or a redelivery returns an element at the source position it took ([Sources](#sources)). A
   message identity maps to the source position the element took on its first arrival. A source that
   numbers arrivals from `0` in each process breaks this obligation: after a restart, a new request
   takes the position of a request that committed before the crash.

5. **Restored producer states meet the third condition of
   [the durability condition](#the-durability-condition).** A consumer releases a region of its
   input only once it has persisted, in one write, the guard it releases and what its future outputs
   need of the region, `compact(𝑜)` in [Compaction](operational-semantics/semantics.md#compaction).
   It persists that only once the observations it was computed from are durable. A summary restored
   without its guard counts the region a second time when the consumer pulls it again. A guard
   restored without its summary omits the region from every future output, because the consumer does
   not pull it again.

   A source is a consumer of the system it reads. It releases a position once its persisted producer
   state holds the element itself, or once every consumer of the source has released the position. A
   source that releases on arrival is the one release the run cannot hold back
   ([An effect and its record are not atomic](#an-effect-and-its-record-are-not-atomic)).

6. **A reload's entry is durable before any output of the new version escapes.** The entry holds the
   new version, its boundary guards and its seeds, and recovery needs them to compute what the
   earlier version decided
   ([The program state an observation map determines](#the-program-state-an-observation-map-determines)).

Recomputation needs no obligation of its own. The operator contract makes an operator term's tile a
function of its inputs, and enumerable observation points answering kept keys make the inputs the
same.

---

## Implementation

The obligations leave the runtime free in what it persists and when. This section gives one design
for a single process that meets them without tracking which outputs depend on which observations.

Every term runs as a producer. An observation point's producer is a producer whose output is not a
function of its inputs: the source buffer, a reading's producer, `CommitOperator` for a commit
clock, `AsOfProducer` for an as-of sample ([Observations](#observations)). Its observations are its
producer state, and no input gives them back, so it persists them. Whatever persists them meets two
requirements:

- **An output waits for its observations.** An output leaves the run only once the durable
  observations hold a support for it and for every output before it
  ([Runtime obligations](#runtime-obligations), the durable observations hold a support for every
  escaped output).
- **Recovery finds a well-formed map.** The persisted observations hold a well-formed map below
  `𝑂₁` ([The durability condition](#the-durability-condition)).

This design persists every observation point's observations in one observation log. The open
question on several processes describes persisting each observation point separately
([Open questions](#open-questions)).

The design is uncoordinated checkpointing with log-based rollback recovery, in the terms of
[A Survey of Rollback-Recovery Protocols in Message-Passing Systems](https://www.cs.utexas.edu/~lorenzo/papers/SurveyFinal.pdf).
Each
producer persists its own state with no coordination among producers, and the observation log
records every value the run does not determine, so recomputation from the restored states
reproduces the run. Holding an output until the log is durable is that survey's output commit.
Uncoordinated checkpointing alone is subject to the domino effect, in which restoring one producer
from an older write forces its inputs back to older writes in turn. Log-based recovery avoids it
where a restored producer can serve every region its consumers have not released
([Persisted producer state](#persisted-producer-state)).

One process writes a run's stable storage at a time. A process takes an exclusive lock on the
storage before recovery and holds it while it runs, so a process started while another is running
cannot persist state or release a source alongside it.

### The observation log

The **observation log** holds every observation the run takes, as a sequence of entries in the
order the run takes them, persisted in that order. It is distinct from a commit store's per-key
changelogs. Each entry is a key and what its observation point needs to restore the observation at
that key, which is the observation point's choice
([Persisted producer state](#persisted-producer-state)).

An entry's **log position** is its place in the observation log: each entry's is one more than the
entry's before it. A log position is not a source position. The entry for position 7 of `orders`
can be at log position 1043, after the readings, decisions and other sources' arrivals taken before
it. A persisted entry keeps its log position through recovery and after the entries around it are
dropped, and no other entry takes it. Recovery numbers from the end of the durable prefix, so an
entry lost in a crash leaves its log position to the next observation taken, as a lost arrival
leaves its source position. Write `𝑂[<𝐿]` for the map held by the entries before log position `𝐿`.

**An observation is appended when it is taken, and it is taken when its observation point answers.**
A source's arrival is taken when the source assigns its source position, a reading when its site is
evaluated at a position path, a decision when the commit engine decides a writer's proposal or the
writer decides a position that writes nothing, an as-of sample when `AsOf` latches, and a reload
when the runtime swaps versions. Taking and appending are one step, and no term computes from an
observation before it. So everything the run holds at a moment, outputs and producer states alike,
is computed from observations the observation log has already been given.

Every prefix of the observation log holds a well-formed map, because the run's map is well-formed
at every moment ([Well-formed maps](#well-formed-maps)). The observation log is a chain of
well-formed maps, each one entry larger than the one before, and the last holds `𝑂`.

The observation log is **durable through** `𝐿` when every entry before `𝐿` is persisted. Each write
to stable storage appends entries in log-position order and records the log position through which
the observation log is durable, so recovery finds one durable prefix.

**An output escapes once the observation log is durable through every entry appended before the
output was produced.** The observations taken before an output was computed hold a support for it,
so the durable prefix holds a support for it and for every output computed before it. The obligation
that the durable observations hold a support for every escaped output is met with no record of
dependencies. The prefix over-approximates what
each output needs, and the cost is latency: an output waits until observations it does not depend on
are persisted too. Group commit amortizes one write to stable storage over every output waiting on
it.

The rule also yields `𝑂ᵣ` directly. Every prefix of the observation log is well-formed and the
entries after the durable prefix are lost, so the durable prefix is the largest well-formed sub-map
of the durable observations, and it is below `𝑂₁`.

A finer rule is possible and not required. The compiler knows which observation points reach which
sinks, so an observation log partitioned by sink lets an output wait only for its own partition.
That rule tracks dependencies statically, per sink, rather than per output.

An observation point compacts its entries as any producer compacts its tile
([Compaction](operational-semantics/semantics.md#compaction)). Once every consumer has released a
key, the observation point drops the key's entry and folds it into a summary. Dropping an entry
changes no other entry's log position and removes nothing from `𝑂ᵣ`: the observation was taken and
persisted, and no consumer asks for it again. A reading at a site a reload keeps is answered from
the observation log, so its consumers include those of every version that keeps the site
([The release model](../src/ccl/design/program-evolution.md#the-release-model)).

Recovery restores each observation point from its entries and its summary, and its consumers pull
from it as during the run:

- **The entries not released** are served again. Consumers are restored from writes made at
  different times, so they pull again from different source positions. Where a source's consumer
  `A` has persisted producer state covering positions `0` through `9` and consumer `B` positions
  `0` through `4`, the restored source serves positions from `5` on.
- **The summary** is what the observation point continues from: a source's next source position and
  a commit clock's latest committed tick. A reading's summary is empty.

A reading is restored the same way. When a loop reaches a position path again, the reading answers
from its restored entry at that key; at a key it holds no entry for, it asks the world. An
observation point answering a kept key from the observation map
([Runtime obligations](#runtime-obligations)) is this restoration.

### Persisted producer state

A producer persists its producer state and the guard it has released to each of its inputs in one
write, before a release reaches its input. A join holds one guard per input. A producer does not
persist the guard its consumers have released to it: recovery rebuilds that from the consumers'
own persisted guards. Each producer persists its own producer state when it releases, and no two
producers' writes need to describe one moment of the run.

The write holds the producer's tile in the shape
[Compaction](operational-semantics/semantics.md#compaction) gives it: `compact(𝑜)` for the region
`𝑜` every consumer has released, beside the tile `𝑟` no consumer has released yet. The write can
leave out `𝑟`, or part of it, only where the producer can compute it again from input it has not
released.

**A restored producer can serve every region its consumers have not released.** A summary covers
only regions every consumer has released, and a consumer releases a region only once its own
persisted state covers it. So every region a restored consumer asks for again is in its restored
producer's `𝑟`, or the producer computes it again from its input. A running sum whose consumer has
released positions `0` through `900` does not persist its sum through position `1000` and release
its input through `1000`. After a crash the consumer would ask for position `901` again, and the
restored sum would hold only the total through `1000`. A runtime that restored the sum from an
older write instead would have to restore the sum's input from an older write too, and so on up
the chain: the domino effect. The rule's cost is lag: a release reaches a source one persist per
producer after the sink's release, so the lag of a source's release to the system it reads grows
with the number of producers between the source and the sinks.

A producer persists enough to restore its producer state after a crash, given what its inputs still
hold unreleased. What it writes is its own choice. An observation point's restored state holds
each kept observation with its kept value.

A producer persists its state only once the observation log is durable through every entry
appended before the state was computed, as an output escapes
([The observation log](#the-observation-log)). The observations the state was computed from are
then in `𝑂ᵣ`, and because `𝐹` is monotone the restored state stands for a tile below `𝐹(𝑂ᵣ)` at its
term.

These rules establish the third condition of [the durability condition](#the-durability-condition).
A restored state stands for a tile below `𝐹(𝑂ᵣ)`, covers what its producer released, and comes from
one write with its guard, and a summary covers only regions every consumer has released.

What the write holds depends on the producer:

- **An observation point** writes its entries to the observation log. A source over a topic
  partition writes only that a position is taken, because the position is the offset and the
  partition holds the record. A standard-input source writes the line itself, because nothing
  upstream holds it ([Sources](#sources)). A random reading can write one random seed and derive
  each reading from it and its key. A source releases a position to the system it reads once its
  entry holds the element itself, or once every consumer of the source has released the position.
- **A producer that compacts** persists nothing until it releases, and then its summary of the
  regions every consumer has released: an aggregate's value, a store's seed, changelog and
  frontier. A running average over released points
  holds their count and their sum, because the count alone does not give the next average. A
  `Memo` holds its cache, because it releases everything it merges
  ([A `Memo` releases everything it takes](../src/interpreter/design-operators.md#a-memo-releases-everything-it-takes)).
- **A producer that holds rows it has not released**, such as a join's open rows or an alarm
  source's held rows, may persist them and then release what they cover. Until it does, its inputs
  keep what the rows were computed from.
- **A producer whose released region is obsolete** holds `⊥` for it and persists only the guard. A
  sink is this case ([Sinks persist their release](#sinks-persist-their-release)).
- **A producer with no state**, such as a `map`, a `filter` or a `FanOut`, persists nothing. Its
  release is the one its consumers' releases permit, and a `FanOut`'s is the intersection of its
  slots' releases
  ([The release contract](../src/interpreter/design-operators.md#the-release-contract)).

The list is what `TileProducer::state_info` counts
([What a producer holds](../src/interpreter/design-operators.md#what-a-producer-holds)). The count
is an inventory of what to persist. The in-process reload already hands a successor its
predecessor's producer states through `OperatorMap::handover`, but the handover holds live
producers. Persisting needs each producer state as data that can be written to stable storage and
read back, which no producer defines today.

A producer chooses when to persist. Persisting once the input it has taken since its last write
passes a bound keeps what recovery recomputes for that producer below the bound, which persisting
on a timer alone does not.

A store, its writers and its driver form a cycle, and two of the releases around it are
acknowledgements: the commit operator's release to a writer acknowledges its commit
([The runtime engines](../src/ccl/design/mutability.md#the-runtime-engines)), and a writer's release
to its driver finishes a position (`TransactWriterProducer` in
`src/interpreter/commit_operator.rs`). Each is a release, so each is persisted before it goes out,
which puts one write to stable storage in every commit. A transaction reads only earlier ticks, so
restoring the cycle's producers in tick order has no domino effect. The induction loop,
`InductionDriver` and `InductionStore` through a cyclic `FanOut`, is a cycle in the same way.
Persisting a cycle as one unit is an open question ([Open questions](#open-questions)).

At a reload, the runtime appends the reload's entry to the observation log, and each term the reload
pairs persists its state at its boundary guard, in the same write as the entry or before it. An
output of the new version waits for that write as for any entry
([The observation log](#the-observation-log)). Recovery installs the version the latest reload entry
of each branch names, and restores each producer from a state persisted under that version, so it
never runs a retired version's operators. Without that write, a producer whose latest persisted
state predates the boundary would need the retired version's operators to compute again what that
version decided after the state was written.

Recovery restores each producer from its latest persisted producer state, or at `⊥` where it has
none, and each observation point from the observation log. Each restored consumer issues its
persisted guard to its input as a release, and a producer with no state forwards it as during the
run. Consumers then pull as during the run. A producer restored from an older write than its
latest in-memory state pulls again the regions it had not released, and its input still holds them
because the release never went out.

### Sinks persist their release

A sink persists the guard it releases each time it releases, after sending the outputs in the
region and before the release reaches its input. Its state holds nothing else. An external call is
a sink for its requests and persists the same way; its replies are readings in the observation log.

Recovery restores each sink's latest persisted release. Under the release model, a term upstream
computes a released position only where another consumer still asks for it ([The release
model](../src/ccl/design/program-evolution.md#the-release-model)). An output already sent is
neither recomputed nor sent again. An output sent and not yet recorded is sent again ([An effect and
its record are not atomic](#an-effect-and-its-record-are-not-atomic)).

The observations a sent output depends on were persisted in the observation log before it escaped,
and their entries are dropped only once every consumer of their observation point has released
them ([The observation log](#the-observation-log)). A request whose reply was sent is still
recomputed when its transaction feeds a counter that later requests read, and only its reply is
skipped.

### Sources

A source meets three runtime obligations through how it numbers its elements and how it keeps them
available to recovery: observation points answer kept keys, a kept key is never given to another
element, and restored producer states meet the third condition
([Runtime obligations](#runtime-obligations)). **A source persists what the system it reads cannot
give back.**

**Numbering.** Each element takes one source position, and a redelivery returns it at the source
position it took. A redelivered element at a fresh position would be a second arrival, and a
transaction it drives would commit a second time.

A source numbers positions in the order it first takes elements. A loop over a source runs in
position order and emits a position only once every earlier position is decided
([Sequencing domains](../src/ccl/design/mutability.md#sequencing-domains)), so positions ordered by
anything else, such as a message identity, leave the loop waiting on positions no element may take.

**Keeping elements available.** Recovery needs an element only where an escaped output or a
persisted producer state depends on it, and the runtime obligations make the element durable before
either. What the source persists for it depends on what the system it reads gives back:

| What the system it reads gives back                                          | Example                                     | The source position an element takes                   | What the source persists   | A crash before the element's entry is persisted                              |
| ---------------------------------------------------------------------------- | ------------------------------------------- | ------------------------------------------------------ | -------------------------- | ---------------------------------------------------------------------------- |
| The element at a permanent address, until the source releases it             | a topic partition                           | its address, the offset                                | that the position is taken | the source reads the address again, and the element takes the same position  |
| The element again, until the source acknowledges it                          | a message queue                             | the position the run recorded for its message identity | the message identity       | the queue delivers it again, and another element may take its position first |
| The row again, from the alarm pair's held rows, until its entry is persisted | `time::alarms()`                            | its release order                                      | the row                    | the pair releases the row again, at the next position                        |
| Nothing                                                                      | standard input, a UDP feed, an HTTP request | its arrival order                                      | the element                | the element is lost                                                          |

Two rules apply to every kind:

- **A system that holds an element only up to a limit.** A topic's retention by time or by size, and
  a queue's limit on deliveries, discard an element whether or not the source has released it. The
  source persists the element itself before such a limit can pass while the element is unreleased,
  and recovery then finds the element in its entry.
- **A missing element fails recovery.** A source that finds an element it took and has not released
  missing from the system it reads stops recovery. It does not state `none` at that position,
  because an escaped output or a persisted producer state may depend on the element.

None of these says anything about delivery to whoever produced an element, or about the order in
which elements arrive beyond numbering them in it. A different element at a position whose entry was
lost is permitted, because `𝑂ᵣ` accounts for every escaped output without the first.

#### A topic partition

A topic source reads one partition, and an element's source position is its offset in the partition.
A topic with several partitions is several sources. Offsets are numbered per partition, and the
order in which a consumer receives records from different partitions changes from one run to the
next, so a position numbered across partitions would have to be persisted element by element. The
offset is already the partition's permanent address for its record.

A partition's offsets skip. A transaction's commit and abort markers take offsets and hold no
record, a consumer that reads only committed records skips an aborted transaction's records,
compaction removes records, and retention removes every offset below the partition's start. The
source states `none` at each offset it reaches that holds no record. A read from an offset returns
the next record the partition holds, so a read that returns a later offset than the one requested
states `none` at the offsets between. An offset the source took and has not released, and that
retention has since removed, fails recovery under the rule above.

#### `time::alarms()`

An alarm source reads the run itself. The alarm pair holds each row fed to its sink, and releases a
row from its source once the clock reads at or after the row's `at`
([`time::alarms()`](chl-spec.md#timealarms)). The held rows are the pair's producer state, persisted
as any producer's is ([Persisted producer state](#persisted-producer-state)). A released row takes
the next source position, and its entry in the observation log holds the row.

A row is in one of two persisted records, and its release moves it from the first to the second:

- **Before its release,** the row is in the held rows of the pair's latest persisted producer state.
  Where that write predates the row, the row is in the pair's input instead: the feed that holds it,
  which the pair has not released.
- **After its release,** the row is in its entry in the observation log.

The pair persists held rows without a row only once the row's entry is persisted. A crash after the
release and before the entry is persisted leaves the row in the first record: recovery restores the
pair holding it, and the pair releases it again once the clock reads at or after its `at`, at the
next source position. That position can differ from the one the lost entry had, and nothing that saw
the first release escaped, because an output computed from the row waits for its entry.

#### HTTP requests

`http::serve`'s requests release on arrival. Each connection is a new source position, and nothing
holds the request. A crash closes the connection, and a response computed for it has no recipient
and is dropped. The request's effects stay kept once persisted, because another output may depend on
them. The client's resend is a new arrival at a new position, so a transaction the first request
committed commits a second time.

#### The life of one arrival

An element arrives on partition 0 of the topic `orders` at offset 120, so it takes source position
120 of the source that reads that partition. Its entry in the observation log is at log position
1043 and records that position 120 is taken; the partition holds the element.

| Step                       | What happens                                                                                                                                                                                    | Copies of the element                                                                             |
| -------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------- |
| 1. Arrival                 | The source receives the element at position 120. Its entry is appended to the observation log at log position 1043, in process memory.                                                          | the partition; process memory                                                                     |
| 2. Persist the entry       | The observation log is persisted through log position 1043. Position 120 is kept.                                                                                                               | the partition; process memory                                                                     |
| 3. Escape                  | Outputs computed from position 120 leave the run.                                                                                                                                               | unchanged                                                                                         |
| 4. Persist producer states | Each consumer of the source persists its producer state covering position 120, then releases position 120.                                                                                      | the partition; process memory; what position 120 fed, in each consumer's persisted producer state |
| 5. The source's release    | Every consumer has released position 120. The source drops its buffered copy, commits its progress through offset 120 to the partition, and drops the entry at log position 1043, in any order. | what position 120 fed; the partition, until its retention passes                                  |

Three rules order the steps:

- **Persisting the entry comes before escaping.** An output computed from position 120 leaves the
  run only once its entry is persisted (step 2 before step 3).
- **Persisting the entry comes before persisting producer states.** A producer state computed from
  position 120 stands for observations recovery keeps only once its entry is persisted (step 2
  before step 4).
- **A consumer persists before it releases.** Until every consumer has released position 120,
  recovery may restore one that pulls position 120 again, and the entry holds no element, so the
  partition still has to hold it (step 4 before step 5).

Steps 3 and 4 can occur in either order.

A source that releases on arrival releases to the system it reads at step 1. Its entry holds the
element, and between steps 1 and 2 process memory holds the only copy
([An effect and its record are not atomic](#an-effect-and-its-record-are-not-atomic)).

### Requirement and implementation side by side

| The model requires                                       | This design provides                                                                                                        |
| -------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------- |
| A kept observation has one value for the run             | Observation points answer kept keys from the observation log                                                                |
| A support for every escaped output is kept               | Outputs wait for the observation log's durable prefix                                                                       |
| An output is sent once, up to the limit                  | Each sink persists its release when it releases                                                                             |
| `𝑂ᵣ` is well-formed and `𝑂ᵣ ≤ 𝑂₁`                     | `𝑂ᵣ` is the durable prefix                                                                                                 |
| Restored producer states stand for tiles below `𝐹(𝑂ᵣ)` | A producer persists its state only once the observation log is durable through the entries it was computed from             |
| A released region is not needed again                    | A consumer persists its producer state and its released guard in one write before it releases                               |
| A reload's boundary is kept                              | The reload's entry, and each paired term's state at its boundary, are persisted before an output of the new version escapes |
| Determined values only are recomputed                    | Restored producers pull from inputs restored from persisted producer states and the observation log                         |
| Outputs are recognizable when re-emitted                 | Sinks receive each output's key                                                                                             |

---

## Consequences for other documents

These statements conflict with the model or depend on it. None is edited here.

- **[Instances](operational-semantics/semantics.md#instances)** lists partial functions but not
  the commit clock's tiling, a partial function tiling with `⊕` defined on fewer pairs, that
  [The observation map](#the-observation-map) uses.

- **[The Operator Contract](operational-semantics/semantics.md#the-operator-contract)** makes an
  operator's output a function of its input tiles. The runtime realizes two observation points as
  operators that break it: `CommitOperator` decides ticks and `AsOfProducer` latches samples by the
  schedule. The semantics has no term kind for them ([Observations](#observations)).

- **[What a producer holds](../src/interpreter/design-operators.md#what-a-producer-holds)** counts
  the values a producer retains, and `OperatorMap::handover` passes live producers. No producer
  defines its producer state as data that can be persisted and read back with the guard it has
  released. Persisting producer state needs that for every stateful producer
  ([Persisted producer state](#persisted-producer-state)).

- **[How a reload works](../src/ccl/design/program-evolution.md#how-a-reload-works)** swaps versions
  without recording where each term's boundary was taken. Under the model a reload is an observation
  ([Observations](#observations)). The swap appends the reload's entry, with its boundary guards and
  seeds, before the new version computes anything, and recovery rebuilds
  [the branch table](../src/ccl/design/program-evolution.md#the-branch-table), which holds each
  branch's version in process memory, from those entries.

- **[A `Memo` releases everything it takes](../src/interpreter/design-operators.md#a-memo-releases-everything-it-takes)**
  releases each region as it merges it. Under
  [Persisted producer state](#persisted-producer-state) a consumer releases only once its producer
  state is persisted, so a `Memo`'s release, and every compacting producer's, waits for a write to
  stable storage. Compaction in memory does not wait: a crash before the write leaves the region
  unreleased, and the restored producer pulls it again.

- **Observations are taken in separate producers.** The source buffer assigns positions
  (`src/interpreter/stream_buffer.rs`), `CommitEngine::attempt` decides proposals, and
  `AsOfProducer` latches samples. None appends to a shared sequence, and the observation log needs
  each to append at the moment it answers ([The observation log](#the-observation-log)). Three of
  them do not see what the entry needs:
  - An abort, and a grant that writes nothing, is decided in `TransactWriterProducer` and never
    reaches the commit engine.
  - `AsOfProducer` latches values, not the tick that is the sample.
  - `CommitEngine::attempt` sees a step local to the writer, not the writer's site and position
    path.

- **[`mutability-walkthrough.md`](mutability-walkthrough.md)** calls a commit store's per-key
  changelogs "the commit log". The observation log is a different thing, and the two names differ
  only in their first word.

- **[Builtins](../src/ccl/design/mutability.md#builtins)** says `begin_<site>` is injective over
  iterations and that a denied iteration's record carries a time. On the commit clock a transaction
  that writes nothing takes no tick, so its decision records the tick it read through instead
  ([Observations](#observations)).

- **[mutability.md](../src/ccl/design/mutability.md)** does not say whether a block may make a call
  outside the program. A retried body would reuse the call's reply
  ([Open questions](#open-questions), a call inside a block).

- **[8.4 Feeds are the second form of mutability](chl-spec.md#84-feeds-are-the-second-form-of-mutability)**
  indexes a reply inside a block by commit tick, a store's private counter that a rebuilt store
  restarts at `0` ([Vocabulary](../src/ccl/design/program-evolution.md#vocabulary)).
  [Outputs are keyed](#outputs-are-keyed) keys the reply by the writer's site and position path,
  which a reload that keeps the site keeps, and orders it by tick.

- **[`time::alarms()`](chl-spec.md#timealarms)** says a process exit discards held rows. Held rows
  are a producer state and are recovered.

- **The effects work's readings** state that a reading belongs to its version of the program, that
  a reload may take it again, and that a reading survives a crash only as the producer state
  holding it does. The model replaces all three with [Immutable history](#immutable-history). Main's
  [7.5 Time](chl-spec.md#75-time-decided) agrees with the model for a top-level binding.

- **The workflow library's durability requirements** ask that a transaction in a workflow body
  commit at most once per key. [Transactions are keyed by their site and
  position](#transactions-are-keyed-by-their-site-and-position) gives this for every transaction.
  The library also says code between two calls can compute a different `time::now()` when
  recomputed. Under the model the recomputation reads the kept reading.

- **`http::serve`'s positions** restart at `0` in each process
  (`src/interpreter/stream_buffer.rs`), which breaks the rule that a kept key is never given to
  another element.

- **`http::serve`'s requests** release on arrival, so the runtime persists each request body as it
  arrives and drops a response whose connection died in a crash ([Sources](#sources)).

- **[7.3 Sources](chl-spec.md#73-sources)** lists `stdin()` and `http_serve`, and lets a host
  embedding register more. Every source states what the system it reads gives back
  ([Sources](#sources)), and `stdin()` and `http_serve` read systems that give back nothing. A
  host-registered source states which kind of system it reads and any limit on how long that system
  holds an element, and a topic source names the one partition it reads.

- **A writer whose body a reload changes.** A decision the earlier version took keeps its value
  ([Immutable history](#immutable-history)), and the reload's boundary guard on the commit clock
  places it inside what the earlier version decided, so the new body does not decide it again.
  [How a reload works](../src/ccl/design/program-evolution.md#how-a-reload-works) does not say
  whether a reload that changes a writer's body keeps its site.

- **Reading keys and the collection a loop iterates.** A reading's key is its site and position
  path, which do not name the collection the loop iterates. A reload that changes `for o in orders:`
  to `for o in refunds:` and keeps the site gives position `7` of `refunds` the reading taken at
  position `7` of `orders`. A rebuilt `range(3)` that becomes `range(4)` reaches keys `0` through
  `2` again after [the release model](../src/ccl/design/program-evolution.md#the-release-model) let
  their entries be dropped. The effects work's site stability rule decides whether either change
  moves the site.

---

## Open questions

- **[Open] Several processes.** The observation log's escape rule needs one take order, which
  processes that keep separate logs do not share. An observation log kept in a replicated store is
  still one observation log with one take order. The alternative is for each observation point to
  persist its own observations, and one log per process is the case where a process's observation
  points share one stream:
  - **An output waits for one count per observation point.** When an output is computed, the
    runtime records how many entries each observation point that reaches the output's sink has
    taken, and the output leaves once each point's storage has confirmed that many. A point's count
    is its own append count. It follows a source's source positions and a commit clock's ticks, and
    it is not a reading's position path, because a reading is taken in schedule order.
  - **Recovery drops orphaned entries.** Each point's persisted entries can hold an entry that is
    not reached or not valid without an entry another point lost: a reading at position path 7
    without the source's element at source position 7, or a commit whose writer's decision at an
    earlier position was lost. Recovery drops it and every entry that needs it, such as each later
    decision of its writer and each later commit on its clock, which leaves the largest well-formed
    sub-map ([Well-formed maps](#well-formed-maps)). No escaped output or persisted producer state
    depends on a dropped entry, because each waited for the entries it needs as well.
  - **Each point uses its own storage.** A topic source can keep its entries in the topic's
    committed offsets, and a commit clock in its store's changelog. Each point drops its released
    entries from its own stream, where one log holds entries of mixed lifetimes.
  - **An output can wait for several writes.** An output depending on three points waits for three
    confirmations, where one write to the observation log releases every output waiting on it.
  - **A reload is a cut.** A reload's entry has to be ordered against every observation point, so
    with separate logs a reload is a cut across them.

  Persisted producer state needs no coordination across processes, because each producer persists
  its own.
- **[Open] A call inside a block.** A retried body reads the same readings at the same keys
  ([Transactions are keyed by their site and position](#transactions-are-keyed-by-their-site-and-position)),
  and a call's reply is a reading. A body retried at a later snapshot can compute a different
  request: the first attempt sends `charge(100)`, the retry computes `charge(80)`, the reply to
  `charge(100)` answers it, and `charge(80)` is never sent. The options are to refuse a call inside
  a block, to key a call's reply by its request as well as its site and position path, or to send a
  block's calls only once it commits, as its in-block replies are.
- **[Open] Persisting a cycle as one unit.** [Persisted producer state](#persisted-producer-state)
  persists before each release inside a cycle, which puts one write in every commit. Persisting the
  cycle as one unit at the positions of the loop around it keeps the acknowledgements in memory, as
  Falkirk Wheel persists a loop at its outer timestamps
  ([Falkirk Wheel](https://icgog.github.io/data/papers/2021-socc-falkirk.pdf)). That needs a cut
  that says what happens to the transactions in flight. Without one, a driver restored as having
  finished positions through `9` beside a store restored at tick `5` never drives positions `6`
  through `9` again, and the store cannot pass tick `5`.
- **[Open] When a cycle reaches `𝐹(𝑂)`.** `𝐹(𝑂)` is the least program state that satisfies the
  equations of
  [The program state an observation map determines](#the-program-state-an-observation-map-determines).
  An iteration reaches it only if the iteration stops, and the semantics defines a stopped program
  as one with no tile left to extend
  ([Termination and Extraction](operational-semantics/semantics.md#termination-and-extraction)). A
  cycle of operators, such as a store and its writers, has no rule in the semantics for when it
  stops. A source that never ends needs no such rule:
  [The durability condition](#the-durability-condition) needs only `𝐹(𝑂ᵣ) ≤ 𝐹(𝑂ₖ)` for each finite
  map `𝑂ₖ` the run reaches later, which monotonicity gives.
