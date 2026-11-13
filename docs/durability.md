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

The current `time::now()` is a **weak clock** ([Terms](#terms)), which a follow-up renames
`time::weak_now()`: a reading taken after recovery can be earlier than one taken before the crash,
as two readings within one process can be ([7.5 Time](chl-spec.md#75-time-decided)). In
`elapsed = time::now() - started`, where `started` is a kept reading of 10:05, a reading of 10:03
after recovery makes `elapsed` negative. The model also admits a **transactional clock**, whose
readings the commit engine places in commit order, because each attempt of a transaction takes its
own readings ([Transactions are keyed](#transactions-are-keyed-by-their-site-and-position)).

Two conditions follow:

- **Immutable history.** An observation the run keeps has one value for the life of the run,
  across crashes and reloads.
- **Recomputation is limited to determined values.** The runtime recomputes a term only where the
  kept observations determine its value, so the recomputed value is the one already computed.

This document separates what the model requires ([The model](#the-model)) from how a runtime meets
it ([Runtime obligations](#runtime-obligations), [Implementation](#implementation)).

**Status.** Nothing here is implemented. The runtime persists nothing today: a restart starts every
source at position `0` and every store at its declared initializer. The model is **[Tentative]**
except where a section marks a point **[Decided]**. Sites are on main for feeds, yields and calls.
The effects work, in pull requests #656 and #691 and not yet merged, adds readings (`__now`,
`__random`), the spec's position, and sites for stores and loops. This document uses
those terms provisionally, as [Terms](#terms) defines them, until their definitions land on main. A
transaction has no site in either.

## Terms

Site, position and reading are provisional: they follow the effects work (#656, #691) and are
replaced by its definitions once those land on main.

- **Observation.** A value no term of the program determines: a reading, a source's arrival or end,
  a transaction's decision, a reload's entry ([Observations](#observations)).
- **Operator term.** A term whose tile is a function of its inputs' tiles
  ([Observations](#observations)).
- **Observation point.** A term that is not an operator term. The world or the runtime's engine
  supplies its tile, and each entry of the tile is an observation ([Observations](#observations)).
- **Reading.** An observation a call takes from outside the program: a clock reading, a random
  value, or the reply to a call made outside the program. In the effects work a reading is the body
  of a `@Builtin` standard-library function whose value comes from outside the program, such as
  `std::time::clock`, which `time::now()` calls (#656).
- **Weak clock.** A clock whose readings carry no order: a reading can be earlier than one taken
  before it, and commit order never consults a reading. The current `time::now()` is a weak clock,
  and a follow-up renames it `time::weak_now()`
  ([Consequences for other documents](#consequences-for-other-documents)).
- **Transactional clock.** A clock whose readings the commit engine places in commit order. A
  follow-up names it `time::now()`.
- **Site.** Where an evaluation stands in the program: a place, the places of the calls that reached
  it, outermost first, and the run ([Sites](../src/ccl/design/sites.md#sites)). Inlining gives each
  call its own site, and every site is fixed when the program is compiled. On main a site (`Site`,
  `src/ccl/site.rs`) names a feed, a `yield` or a call. The
  effects work adds sites for readings, loops, assignments and stores (#656, #691). A transaction
  has no site yet.
- **Source position.** An element of a source's domain: the number a source gives an element when
  it takes it, or a number the source states no element will take ([Observations](#observations)).
- **Generation.** One build of an operator in the run. The operators of the run's first version
  start the first generation, and a reload that rebuilds an operator starts a new one. A reload
  that keeps an operator, in any branch, keeps its generation, and recovery never starts one. A
  generation is named by an opaque ID that the implementation chooses: the first generation by one
  fixed ID, and each later one by an ID its reload's entry records. Every key an operator mints
  carries its generation, so two generations at one node share no key. No key carries a branch: an
  operator that several branches hold mints one set of keys, and every branch holding it reads the
  same observations. The generations at one node are ordered as the reload entries that started
  them are in the observation log, after the first.
- **Kept and rebuilt.** A reload **keeps** a term when it keeps the earlier version's operator at
  the term's corresponding node, and **rebuilds** it when it builds a new operator there: because
  the term changed, because it reads a rebuilt binding, or because the reload cannot carry the
  operator ([How a reload works](../src/ccl/design/program-evolution.md#how-a-reload-works)). A
  rebuilt store starts from a **seed**, the value its predecessor held at the swap. "Rebuilt"
  describes only a reload. After a crash the runtime **recovers** a term in the same version and
  generation, with the same keys.
- **Position.** The iteration of each loop around an evaluation, outermost first, as the effects
  work's spec defines it (#656). Each component is a pair: the loop's **domain**, which is the
  operator the loop iterates, in its generation, and the loop's **iteration position** in it, an
  index into the sequence the loop reads
  ([Vocabulary](../src/ccl/design/program-evolution.md#vocabulary)). A reload keeps a domain when it
  keeps the operator, and a source is kept by its module path and binding name. A loop over a
  source, or over a filter of one, is at a source position. A loop over another collection, such as
  the keys of a `group_by`, is at that collection's key. Inside a transaction's body, the position
  of a reading or of the transaction's decision ends with the attempt index
  ([Transactions are keyed](#transactions-are-keyed-by-their-site-and-position)). An evaluation
  under no loop has the empty position. Examples write a component by its iteration position alone
  where no reload intervenes.
- **Body.** The statements under a `with begin():` block. A transaction evaluates its body once
  per attempt, at the attempt's snapshot, and the engine decides the attempt only once the body has
  finished ([Observations](#observations)).
- **Key.** A source's observations are keyed by source position, and a reload's by its index among
  its branch's versions. Every other observation is keyed by a site `𝑠` and a position `𝑝`,
  `(𝑠, 𝑝)` ([Observations](#observations)). A tick is the value of a decision and is not part of its
  key.
- **Feed key.** The key of a row appended to a feed: the site of the `<<` and the position at which
  it ran, `(𝑠, 𝑝)`. A row appended inside a transaction's body takes the transaction's position,
  without the attempt index ([Outputs are keyed](#outputs-are-keyed)).
- **Log sequence number (LSN).** An entry's number in the observation log: one more than the
  entry's before it ([The observation log](#the-observation-log)).
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
  its own input only once what its future outputs need of it is durable, in its checkpoint or in
  the observation log ([Checkpoints](#checkpoints)). A source is a consumer of the system it reads
  and releases to it the same way.
- **Checkpoint.** One write of a producer's producer state and the guard it has released to each of
  its inputs ([Checkpoints](#checkpoints)). Each producer checkpoints on its own schedule while the
  run continues, so checkpoints are fuzzy: no two need to describe one moment of the run.
- **Write-ahead log.** A log of changes to state, durable before anything computed from those
  changes is persisted or escapes. The observation log is the write-ahead log of the observation
  points: each entry is one observation, the change to one observation point's tile. Every other
  term is computed from observations, and its checkpoints wait for the entries they were computed
  from. A commit clock's entry also holds the decision's commit record, a computed value, so that a
  store recovers past its checkpoint without evaluating a body again
  ([The observation log](#the-observation-log)).
- **Recovery.** The start of a process after a crash. Each producer is **recovered** from its latest
  checkpoint, or starts from `⊥` where it has none, and each observation point is recovered from
  its persisted observations.
- **Evaluation boundary.** The region of a term's tiling the run has decided at that term: what the
  term holds, together with what its consumers have released to it. It only grows while a process
  runs. A crash can shrink it, because a recovered producer holds only what it persisted, and
  recovery catch-up grows it to cover each sink's recovery set before a reload that waits for
  catch-up ([Recovery catch-up](#recovery-catch-up)). A reload's boundary guard at the term is the
  evaluation boundary at the swap ([Across reloads](#across-reloads)).
- **Recovery set.** The outputs at a sink that the recovered map `𝑂ᵣ` determines, `Out(𝑂ᵣ)` at that
  sink ([The durability condition](#the-durability-condition)).

[The life of one arrival](#the-life-of-one-arrival) shows how the steps an arrival goes through,
persisting it, escaping, checkpointing the producers it fed, and releasing it, are ordered.

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
construct is added to name one ([Terms](#terms)). A source's key is its source position, and a
reload's is its index among its branch's versions. Every other observation point is keyed by its
site and its position, `(𝑠, 𝑝)`. Where a loop around it iterates a source, the position holds that
source's positions.

| Observation                                                                                                        | Key                                                        | Chosen by              |
| ------------------------------------------------------------------------------------------------------------------ | ---------------------------------------------------------- | ---------------------- |
| A reading: the clock, a random value, the reply to a call made outside the program                                 | the reading's site and position                            | the world              |
| A source element: the element at a position, or `none` where no element will take it                               | the source and the source position                         | the world              |
| A transaction's decision: `` `commit `` or `` `retry ``                                                            | the transaction's site and position, its attempt innermost | the commit engine      |
| A reload: the new version, the generations it starts and their seeds, and the boundary guard of each term it pairs | its index among its branch's versions                      | the runtime's schedule |

- **A reading.** A reading has one value per position. Its site is the place of the `@Builtin`
  function, reached through each call that inlining copied it through, so two calls of one function
  are two sites and two observation points.
- **A source element.** A source defines a domain: its positions exist because elements arrive.
  The element at a position and the position an element takes are both the world's choice
  ([7.3 Sources](chl-spec.md#73-sources)). A reading is indexed by positions that already exist,
  which is the difference between the two. A source also states `none` at each position no element
  will take: every position past its last element once it ends, and each position its numbering
  skips, such as an offset a compacted topic removed. An output can depend on a `none`: a `sum`
  over a source is final only once the source has ended.
- **A transaction's decision.** `Txn` is a total order that no writer's domain supplies. The
  per-site oracle `begin_<site> : 𝐼 ⇒ Txn` places iteration `𝑖` of a site in it
  ([mutability.md](../src/ccl/design/mutability.md#the-model-histories-and-causal-recursion)), and
  each transaction reads the commit history strictly before its place
  ([Semantics](../src/ccl/design/mutability.md#semantics)). The engine realizes `Txn` as the commit
  clock of the store the transaction writes or reads.
  - **The clock.** A store's clock in generation `𝑔` is identified by the store's site and `𝑔`.
    It is stated as a source is: each position of the store's commit order in `𝑔`, a **tick**,
    holds a commit, or `none` where the engine states no commit will land. Tick `0` holds the
    generation's seed: the store's declared initializer in its first generation, and the reload's
    seed in a later one. One sequencer per store, as the engine has today, gives each commit the
    next tick and states no `none`. Stores that share no mutable variable share no clock. The
    decisions of every transaction on one store form one observation point, the store's **commit
    clock**, because two of its transactions must not commit at one tick. The `Transact` node
    carries the clock, and `CommitOperator` realizes it.
  - **The decision.** A transaction decides one of two values. `𝑔` is the generation of the clock
    the decision is taken on, and `𝑇` is a tick of it:
    - `` `commit(𝑔, 𝑇) ``: the attempt read the history through tick `𝑇−1` and committed at `𝑇`
      its **commit record**: one optional write per key of the store, and the rows its body
      feeds.
    - `` `retry ``: the attempt failed the engine's validation and took no tick, and the
      transaction runs its next attempt.

    The body computes the writes and the rows from what it read, and the engine's schedule chooses
    the tick. Every attempt that does not retry takes a tick, whatever it writes (#810): a grant, a
    grant whose writes are all `` `idle ``, a **deny**, whose guard takes no writing path, and an
    **abort**, whose body an exception escapes. A deny and an abort write no store key and feed no
    row.
  - **A read-only transaction.** A `with begin():` block that reads a store and writes nothing is a
    transaction on that store's clock and takes a tick (#811). It reads the history through
    `𝑇−1` and feeds its rows at `𝑇`. A read-only transaction reads one store, because reading two
    mutable variables together puts them in one store
    ([How many commit stores a program has](../src/ccl/design/mutability.md#how-many-commit-stores-a-program-has)).
- **A reload.** A reload replaces the operators of one version of a branch with those of the next
  while the terms hold tiles ([4. Reload](operational-semantics/semantics.md#4-reload)). Its entry
  holds:
  - **The new version.**
  - **The generations it starts.** The reload starts a generation for each term it rebuilds
    ([Terms](#terms)). For each old store a rebuilt store seeds from, the entry records that tick
    `0` of the new store's generation `𝑔_new` follows tick `𝑇_swap` of the old store's generation
    `𝑔_old`, where `𝑇_swap` is the old store's frontier at the swap. A store that merges several
    old stores records one such link for each, and each store a split produces records its own.
  - **The seeds.** A rebuilt store's seed is the value its predecessor held at the swap, matched by
    `VarPath`, or its declared initializer where it has no predecessor.
  - **The boundary guards.** Each term the reload pairs is split at a boundary guard, its
    evaluation boundary at the swap ([Terms](#terms)): what the earlier version had decided there.

  How far each term had got at the swap depends on the schedule
  ([What the properties do not settle](operational-semantics/semantics.md#what-the-properties-do-not-settle)),
  so the guards and the seeds are an observation, taken at the swap.

Operator terms compute every other tile from observations and literals. In the effects work, the
capability `ObserveWorld` marks every reading and every source the program opens, so the compiler
can list the program's world-chosen observation points. The engine-chosen points are the commit
clocks. The runtime takes a reload's entry when it swaps versions.

### The observation map

The **observation map** `𝑂` is a program state limited to the observation points: it assigns each
observation point `𝑡` a tile `𝑂(𝑡)` of `𝑡`'s tiling. Maps are ordered point by point by the
progress order, as program states are ordered term by term
([The program state an observation map determines](#the-program-state-an-observation-map-determines)).

| Observation point                      | Its tiling                                                                                                                                                                                                                         |
| -------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| A source whose elements have type `𝐸` | partial functions `ℕ ⇀ Option(𝐸)`: `some(𝑒)` where `𝑒` took the position, `none` where the source states no element will                                                                                                        |
| A reading                              | partial functions from position to value                                                                                                                                                                                           |
| A store's commit clock                 | partial functions from site and position to `` {`commit{(Gen, ℕ)} \| `retry} ``, beside the ticks stated `none`, that commit no tick of a generation twice and commit no tick stated `none` |                                       
| A branch's reloads                     | partial functions from a reload's index among the branch's versions to its version, the generations it starts with their links and seeds, and its boundary guards                                                                  |

`Gen` is the type of generation IDs ([Terms](#terms)). A source's tiling is the sparse function
tiling of
[The Direction: Tilings for Sparse Functions](operational-semantics/deprecation.md#the-direction-tilings-for-sparse-functions),
whose `nones` predicate holds the `none` entries. A commit clock's tiling is the partial function
tiling with `⊕` defined on fewer pairs: `𝑥 ⊕ 𝑦` is their union when their domains are disjoint, no
tick is committed in both, and no tick committed in one is stated `none` in the other. The sub-tiles
of a tile `𝑧` are still the restrictions of `𝑧` to subsets of its domain, so the tiling keeps
cancellativity and the sub-tile meet
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
  iteration position in that loop's domain, and the condition of each branch and filter around `𝑡`
  holds there in `𝜎`. A key in `𝑡`'s domain is **reached**.

A source is under no loop or branch, so every key is reached and `𝜎(𝑡)` is `𝑂(𝑡)`. A reading under a
filter or an `if` is reached only at the positions where the condition holds, so an entry of `𝑂` at
a position the program never evaluates is not part of `𝜎`. A function called from a site under
`if r.ok:` and from a site under no condition holds two readings, one per call site, and each is
reached under its own call's conditions. A transaction runs its body in a loop over attempts, the
innermost loop around its readings and its decision. The attempt loop's domain at a position holds
attempt `0`, and attempt `𝑗+1` where `𝜎` holds `` `retry `` at attempt `𝑗`. A commit clock's key is
reached through its transaction's loop, the conditions around its `with begin():`, and the attempt
loop. In the semantics' terms, `𝜎(𝑡)` is the part of `𝑂(𝑡)` inside the guard that selects the
reached keys ([The `split` Operation](operational-semantics/semantics.md#the-split-operation)).

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

A store's commit clock supplies the oracles `begin_<site>` of the transactions on the store. A
transaction's body at a decided position reads the store through its decision's snapshot in the
decision's generation `𝑔`: tick `𝑇−1` for `` `commit(𝑔, 𝑇) ``. The store holds the writes of
`` `commit(𝑔, 𝑇) `` at tick `𝑇` of `𝑔`, and its value at `𝑇` is decided once every tick of `𝑔` from
`1` through `𝑇` holds a commit or `none`. An operator that read a missing tick as one with no commit
would decide a value at a later tick that the missing commit then changes, and would not be
monotone. `CommitEngine::read_as_of` answers nothing past its watermark.

Two properties follow:

- **`𝐹` is monotone for a fixed reload history.** For maps `𝑂 ≤ 𝑂′` that hold the same reload
  entries, `𝐹(𝑂) ≤ 𝐹(𝑂′)` term by term: iterating the equations for `𝑂` from the least program
  state stays below `𝐹(𝑂′)`. A reload entry that `𝑂′` adds can change `𝐹` at a term, but only
  outside the term's evaluation boundary at the swap ([Across reloads](#across-reloads)).
- **The schedule decides progress, not the answer.** The schedule is the order and timing in which
  the runtime runs operators. Under any schedule, every program state the run reaches while holding
  observations `𝑂` is below `𝐹(𝑂)` term by term. At any moment, an operator's output (its tile in
  `𝐹(𝑂)`) is below the operator applied to its input's tile in `𝐹(𝑂)`. The schedule decides only
  how much of `𝐹(𝑂)` the run has computed. It reaches the answer only through the observations
  it chooses, a reading, a decision's tick or a reload's boundary, and those are in `𝑂`.

`Out(𝑂)` is `𝐹(𝑂)` at the sink terms: the outputs `𝑂` determines. The durability condition is stated
on `Out`, because sinks outlive versions and internal terms do not.

#### Across reloads

`𝐹(𝑂)` composes over the reload entries in `𝑂`. Before a branch's first reload, its terms satisfy
the first version's equations. A term a reload pairs then holds
`𝑦₁ ⊕ split(inject(𝑓₂), 𝑔₁).outside`, where `𝑦₁ = split(𝐹_𝑣₁(𝑂)(𝑡), 𝑔₁).inside`
([What a reload computes](operational-semantics/semantics.md#what-a-reload-computes)):

- `𝑣₁` and `𝑣₂` are the versions before and after the reload. `𝐹_𝑣` is `𝐹` computed with the
  equations of version `𝑣` alone, composed over the reloads before `𝑣`, and `𝑡` is the term in
  `𝑣₁`.
- `𝑔₁` is the reload's boundary guard for the term, from its entry in `𝑂`: the term's evaluation
  boundary at the swap, what the earlier version had decided there ([Terms](#terms)).
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
from `500` on. A store the reload rebuilds starts a new generation from the entry's seed at tick
`0`, so the new version's equations read only ticks of the new clock. Each later reload composes the
same way.

**The answer for a fixed reload history and what the run has decided are different things.** In
the example, suppose `orders` holds `1` at position `0` and `2` at position `1`, and the earlier
version has computed only position `0`. Before the reload `𝐹(𝑂)` holds `{0 ↦ 2, 1 ↦ 4}`, the answer
for that reload history. After a reload with `𝑔₁` holding position `0` it holds `{0 ↦ 2, 1 ↦ 6}`.
Position `1` was outside the evaluation boundary, so what changed is the answer for a reload
history, and nothing the run had decided. Inside the evaluation boundary, each reload keeps what
the earlier version decided, and the boundary only grows, so what the run has decided at a term only
grows across reloads. [The durability condition](#the-durability-condition) relies on that, and
[recovery catch-up](#recovery-catch-up) keeps it true across a crash.

### Well-formed maps

`𝑂` is **well-formed** when each of its entries is reached and valid in `𝐹(𝑂)`
([The program state an observation map determines](#the-program-state-an-observation-map-determines)):

- **Reached.** `𝐹(𝑂)` holds the entry at its observation point: its key is in the point's domain in
  `𝐹(𝑂)`.
- **Valid.** A source's `some` or `none`, a reading and a `` `retry `` are valid wherever they are
  reached. A `` `commit(𝑔, 𝑇) `` is valid when tick `𝑇−1` of `𝑔` is decided in `𝐹(𝑂)`, and its
  record is what the transaction's body computes reading the store at that snapshot. A reload's
  entry is valid when `𝐹_𝑣₁` decides, at each term the reload pairs, the tile inside the entry's
  boundary guard.
- **Ordered.** A site decides the positions of its domain in order
  ([8.5 Ordering and concurrency](chl-spec.md#85-ordering-and-concurrency)). A `` `commit `` at
  position `𝑝` is valid only when the site's decision at every earlier position is in `𝑂` and placed
  earlier on the clock. A commit at `(𝑔, 𝑇)` is placed at tick `𝑇` of `𝑔`. Across a reload, the
  entry's link places tick `𝑇_swap` of the old generation just before tick `0` of the new one.

`𝐹(𝑂)` is the least solution, so no entry is reached only through itself.

The run's map is well-formed at every moment:

- an arrival is taken before any observation keyed through its source position;
- a writer decides one position before it drives the next;
- the engine takes each clock's ticks in order, a read-only transaction's included;
- a reload's entry is taken at the swap, and its boundary guard at each term is the term's
  evaluation boundary there, from what the earlier version had computed.

Well-formed sub-maps of one map are closed under union. For a fixed reload history, reach is
monotone in `𝑂`. A reload keeps reached every entry taken before it, because each such entry is
inside the evaluation boundary at its observation point and so inside the boundary guard. A decided
snapshot keeps its value as `𝑂` grows, and a tag is a terminal scalar. So an entry valid in a
smaller map is valid in a larger one. The durable observations at a crash therefore have a largest
well-formed sub-map, and recovery recovers it
([The durability condition](#the-durability-condition)).

Consequences of the definition:

- **A key through a source position needs the element there.** Without `some` at position `7`, a
  loop over the source does not reach `7`, so a reading at position `7` is not reached. A reading
  kept without its element would answer whichever element takes position `7` after recovery.
- **A clock's commits are contiguous in each generation.** `` `commit(𝑔, 𝑇) `` reads through
  `𝑇−1`, which is decided only once every tick of `𝑔` below `𝑇` holds a commit or `none`. A
  well-formed map therefore commits each generation's ticks through some `𝑘`, and for well-formed
  `𝑂 ≤ 𝑂′` the commits of `𝑂` in a generation are those of `𝑂′` through `𝑘`.
- **A reading under a condition needs the condition.** A reading inside `if r.ok:` is reached at
  position `7` only where `r.ok` holds there in `𝐹(𝑂)`. That needs the element at `7` and everything
  `r.ok` reads.
- **A decision needs what its body reads.** A body that reads `time::now()` computes its record only
  where the reading at its key is in `𝑂`. Without that reading, `` `commit(𝑔, 5) `` at position `7`
  is not valid.
- **A key through a derived domain needs what formed it.** In `for g in group_by(orders, sku):`, a
  reading at iteration position `A` is reached only where `𝐹(𝑂)` holds group `A`. After the orders
  that formed `A` are lost, the reading is not reached.
- **A site's decisions are kept in order.** Suppose a withdrawal at position `𝑝` is denied at tick
  `5` of `𝑔` and a deposit at `𝑝+1` commits at tick `6`. If the deny is lost because the reading its
  body took was not durable, tick `5` is undecided, and `` `commit(𝑔, 6) `` is not valid either,
  because a clock's commits are contiguous. The ordering condition covers a deposit committed while
  `𝑝` has no decision: recovery would then decide `𝑝` after the deposit and grant the withdrawal, an
  order no crash-free run produces. So a commit at `𝑝+1` is not valid without the decision at `𝑝`.
- **Well-formed maps are not downward-closed.** Removing `` `commit(𝑔, 1) `` from a well-formed map
  leaves `` `commit(𝑔, 2) `` reading through an undecided tick, so no guard denotes the well-formed
  maps. Well-formedness says which maps the run can hold; the order between maps is the progress
  order.

### Immutable history

**An observation the run keeps has one value for the life of the run.** The run is the sequence of
versions a program passes through, with every crash and every reload between them. An observation a
crash loses was never part of the run ([Escape](#escape) says which ones may be lost).

- **A crash.** The run after recovery holds the same observation at every key it kept.
- **A reload [Decided].** A reading keeps its value at every key the reload keeps. A reload keeps a
  key when it keeps the key's site and the domain of every component of its position
  ([Terms](#terms)). A site the new version moves or adds is a new key, and so is a position under a
  loop whose iterated term the reload rebuilt: both read anew. A reload keeps every site that does
  not move, and a site moves only when one of its places moves
  ([Stability](../src/ccl/design/sites.md#stability)). A call continues the earlier version's call
  at the same site. The version that takes a reading does not own it; the run does.
- **Changing a loop's collection.** A reload that changes `for o in orders:` to `for o in refunds:`
  keeps the reading's site and changes the loop's domain, so position `7` of `refunds` is a new key,
  and the reading taken at position `7` of `orders` is not reused. A reload that rebuilds `range(3)`
  as `range(4)` starts a new generation of it, so the loop reaches iteration positions `0` through
  `3` of the new generation and none of the keys whose entries the release model may have dropped.

A program needs no mutable variable to keep a reading. In `started = time::now()`, `started` is one
instant for the run, and a reload that keeps the binding keeps the instant, as
[7.5 Time](chl-spec.md#75-time-decided) already states for a top-level binding.

A reading the new version takes can be earlier than one the run kept from an earlier version. In
`deployed = time::now()`, a binding the reload adds, `deployed` reads the clock when the new version
starts, and a kept `started` can be later than it. The readings of a weak clock carry no order
([7.5 Time](chl-spec.md#75-time-decided)).

### Escape

An output **escapes** when it leaves the run and reaches the world, where the run cannot take it
back: a row a sink takes, an HTTP response, or the request of a call made outside the program. A
source's release to the system it reads is a release, not an escape: it withdraws a copy that no
consumer will ask for again, under the rule every release follows
([Checkpoints](#checkpoints)).

A **support** for a set of outputs `𝐸` is a well-formed map `𝑂ₛ`, below the run's map, with
`𝐸 ≤ Out(𝑂ₛ)` ([Well-formed maps](#well-formed-maps)): observations that determine every output in
`𝐸`. An output can have several supports, and no observation need be in all of them. In
`sum(a ++ b) >= 100`, over two sources `a` and `b` of non-negative numbers, early termination
decides the comparison `true` once the elements seen sum to `100`. With `a₀ = 60`, `b₀ = 50` and
`b₁ = 70`, `true` holds under `{a₀, b₀}`, `{b₀, b₁}` and `{a₀, b₁}`, and no element is in all three.
The supports within one map are closed under union ([Well-formed maps](#well-formed-maps)), so the
runtime can keep any of them.

The alarm feed of `time::alarms()` is not an escape. Its path from feed to source runs through the
runtime, and its held rows are a producer state ([`time::alarms()`](#timealarms)).

**[Decided]** — an observation in `𝑂ᵣ` keeps its value for the rest of the run; one outside it was
never observed ([The durability condition](#the-durability-condition)). Recovery asks an observation
point again for a key outside `𝑂ᵣ`. The clock answers with a new reading. A source that holds its
elements answers with the same element, because it has not released it. No output can tell the
second answer from the first, because `𝑂ᵣ` holds a support for every output that escaped.

### The durability condition

Let `𝑂₁` be the observation map at a crash and `𝐸` the outputs that escaped before it. Recovery
continues the run from an observation map `𝑂ᵣ` and from recovered producer states that satisfy three
conditions:

1. **`𝑂ᵣ` is part of what was observed.** `𝑂ᵣ` is well-formed and `𝑂ᵣ ≤ 𝑂₁`
   ([Well-formed maps](#well-formed-maps)): each entry of `𝑂ᵣ` is an entry of `𝑂₁`, and in each
   generation the commits of `𝑂ᵣ` are those of `𝑂₁` through its greatest tick. The runtime invents
   no observation.
2. **`𝑂ᵣ` accounts for every escape.** `𝐸 ≤ Out(𝑂ᵣ)`: `𝑂ᵣ` holds a support for `𝐸`
   ([Escape](#escape)).
3. **The recovered producers stand for `𝑂ᵣ`.** For each producer `𝑢` and each consumer `𝑡` of it:
   - `𝑡`'s recovered state stands for a tile below `𝐹(𝑂ᵣ)` at `𝑡`.
   - What `𝑡` has released to `𝑢` is covered by `𝑡`'s recovered state.
   - `𝑢` has compacted only regions that the recovered guard of every consumer covers. It holds
     everything else, or computes it again from input it has not released.
   - `𝑡`'s recovered state and the guard it released come from one write.

The run then grows `𝑂ᵣ` to some final `𝑂` with `𝑂ᵣ ≤ 𝑂`. Condition 3 makes the recovered run behave
as a run that held `𝑂ᵣ` from the start: no recovered producer holds more than `𝐹(𝑂ᵣ)`, and every
region a recovered consumer asks for is held by its producer or computed again from that producer's
input. The run stays below `𝐹(𝑂)` and can reach it. Every output after the crash is below
`Out(𝑂)`. Every output before it is in `𝐸`, and `𝐸 ≤ Out(𝑂ᵣ)` by condition 2. `Out(𝑂ᵣ) ≤ Out(𝑂)`
holds in two cases:

- **No reload after the crash.** `𝑂` holds the reload entries of `𝑂ᵣ` and no others, and `𝐹` is
  monotone for a fixed reload history
  ([The program state an observation map determines](#the-program-state-an-observation-map-determines)).
- **A reload after the crash.** A reload keeps the earlier version's values inside its boundary
  guard, which is the evaluation boundary at the swap ([Across reloads](#across-reloads)). A crash
  can leave part of `Out(𝑂ᵣ)` outside the evaluation boundary at a sink, because recovered producers
  and the sinks' recovered releases lag what the run had computed. A reload at that moment would
  compute that part again with the new version's equations. Recovery catch-up holds every reload
  until each sink's release covers its recovery set, `Out(𝑂ᵣ)` at that sink
  ([Runtime obligations](#runtime-obligations)). From then on `Out(𝑂ᵣ)` lies inside every later
  reload's boundary guard at the sink's input, and each reload keeps it. A reload set to replace
  the recovering version does not wait, and the outputs it computes again are the one exception
  ([Recovery catch-up](#recovery-catch-up)).

So, apart from that exception, all of the outputs are parts of the one answer `Out(𝑂)`. An
observation in `𝑂₁` and not in `𝑂ᵣ` is an input the run lost, and since `𝑂ᵣ` accounts for every
escaped output without it, losing it is indistinguishable from never having received it.

Conditions 1 and 2 alone do not give this. A `sum` over standard input that has released positions
`0` through `900` to its source and is recovered at `⊥` meets both: `𝑂ᵣ` holds the lines, and every
escaped output is below `Out(𝑂ᵣ)`. The source has dropped the lines the `sum` released, so the
recovered `sum` totals only the lines from `901` on, which no `Out(𝑂)` holds. The second clause of
condition 3 rules this recovery out.

### An effect and its record are not atomic

Durability has a physical limit. The runtime cannot take an observation or emit an output in the
same instant that it persists a record of it, and a crash between the two loses the record. An
input's record is its entry in the observation log, and an output's is the sink's persisted release
of it:

- **An input is lost.** An arrival from a source that releases on arrival is gone if the run
  crashes before persisting it. Recovery cannot ask the source for it again.
- **An output is repeated.** An output sent before the sink persists a release covering it is sent
  again after recovery.

**[Decided]** — of the two orders for sending an output and persisting the release that covers it,
the sink sends first, so a crash repeats an output and never drops one. Losing an input stays the
one unavoidable loss, for a source whose system keeps no copy.

The gap lasts as long as one write to stable storage, and the runtime does not narrow it further.
Closing it needs a record on the other side: a source that holds its elements until released turns a
loss into a redelivery, and a sink that drops keys it has delivered turns a repeat into a recognized
duplicate ([Outputs are keyed](#outputs-are-keyed)).

### Transactions are keyed by their site and position

A transaction's identity is its site and the position of the iteration that runs it, `(𝑠, 𝑝)`. Each
attempt's decision is the observation at `(𝑠, 𝑝)` extended by the attempt index
([Observations](#observations)), and at most one attempt decides something other than `` `retry ``.
The commit record, one optional write per key and the rows the body feeds, is a function of the
commit history through the decision's snapshot, which is immutable.

So a transaction commits at most once at each key, in every program and not only in a workflow. A
second commit at key `(𝑠, 𝑝)` would be a second value of its decision, which immutable history
forbids. Recomputing a kept transaction's body is permitted: it reads the history through its
snapshot and the readings at its own keys, all kept, and yields the record it yielded before. No
keyed-transaction construct is needed, because the key is the position every transaction already
has. A reload that rebuilds the term a transaction's loop iterates starts a new domain, so a
transaction the rebuilt loop reaches at the same site has a new key and is a new transaction
([Immutable history](#immutable-history)).

A transaction that writes nothing is kept as one that writes. `await_final` reads a mutable
variable once every writer of it has drained ([8.6 `await_final`](chl-spec.md#86-await_final)), so
its value depends on each writer's denies and aborts. A deny decided again at a later tick can
grant, and the run would then contradict an `await_final` that escaped. A read-only transaction is
no writer, and `await_final` does not wait for it.

**The engine's retry is the loop over attempts inside the transaction**
([The program state an observation map determines](#the-program-state-an-observation-map-determines)).
The attempt index is the innermost component of the transaction's position, and the attempt loop's
domain grows by one attempt at each `` `retry ``, so the reach rule orders the attempts. Each
attempt takes its own readings, because its readings' keys hold the attempt. A reading taken before
`with begin():` is keyed by the loop's iteration alone and is the same in every attempt. A failed
attempt's writes and the rows its body fed are discarded, and nothing computed from its readings
leaves the run. A failed
attempt's readings and its `` `retry `` entry are compacted with the transaction's other entries,
once every consumer has released the transaction: the committing attempt is reached only through the
`` `retry `` entries before it. Recovery applies the committed attempt's record and does not
evaluate its body again ([The observation log](#the-observation-log)).

**A transaction refuses `AffectWorld`.** An operation that changes state outside the run causes
`AffectWorld`, whatever it returns, and the check follows the capability through calls as the
nested-transaction check does. Readings, which cause `ObserveWorld` alone, are allowed and retry
with their transaction. Work that has to happen after a commit goes through a feed
([Work after a commit](#work-after-a-commit)).

Every proposal reaches the engine's validation, which checks its read set against the commits after
its snapshot. A deny's proposal and a read-only transaction's are validated as a grant's is (#810,
#811): a withdrawal decided against a snapshot from before an earlier deposit's commit would
otherwise be denied for want of money that arrived first
([Well-formed maps](#well-formed-maps)). A stale proposal takes no tick, and the attempt decides
`` `retry ``. A site's commits follow its domain's order: the engine commits a site's proposal at
position `𝑝+1` only once the site's decision at `𝑝` is placed, so a pipelined `𝑝+1` cannot commit
first and leave `𝑝` to retry against its writes. A site with at most one position in flight meets
this, as `TransactWriterProducer` does today: it drives a position only after the one before it is
acknowledged.

### Outputs are keyed

A feed is a function over its domain
([8.4 Feeds are the second form of mutability](chl-spec.md#84-feeds-are-the-second-form-of-mutability)),
so every row appended to a feed has a key, its **feed key**: the site of the `<<` and the position
at which it ran, `(𝑠, 𝑝)`. The position is the full position, because a feed declared inside a loop
is a new feed at each iteration. A row fed inside a transaction's body leaves with the attempt that
commits and with no other, so its position is the transaction's, without the attempt index (#809).
A deny and an abort feed no row. An output at a key has one value, determined by `𝑂ᵣ`. An output
re-emitted after a crash is the same key with the same value, so a sink, or a remote that accepts an
idempotency key, recognizes it.

A sink receives the key with the value, so a re-emitted output can be recognized. A sink releases an
output only after sending it, so a crash may at worst repeat an output but never loses one. The key
lets the recipient recognize the repeat
([An effect and its record are not atomic](#an-effect-and-its-record-are-not-atomic)).

The model states which outputs exist. Delivery is the sink's contract. A sink that delivers at
least once and drops a key it has delivered delivers each output once. A remote that acts on a
request it has acted on before is outside what any layer of the run controls.

A call made outside the program is an output and a reading at one key: the request escapes at the
call's site and position, and the reply is a reading at the same key. A recomputed call finds its
reply in `𝑂ᵣ` and sends nothing. A call whose reply is not in `𝑂ᵣ` has not released its request,
and sends it again with the same key
([A call made outside the program](#a-call-made-outside-the-program)). A call made outside the
program happens only outside a transaction.

---

## Runtime obligations

A runtime satisfies [the durability condition](#the-durability-condition) when it meets seven
obligations. Each is a requirement on any implementation.

1. **Observation points are enumerable.** Every term whose tile depends on more than its inputs'
   tiles is an observation point, and each of its observations has a key. An operator that reads
   the wall clock, a socket, a random source or the scheduler makes its term an observation point
   the runtime does not know of, which breaks every other obligation silently.

2. **Recovery recovers the largest well-formed sub-map of the durable observations, and observation
   points answer its keys from it.** After recovery, and after a reload that keeps a key, a reading
   at a kept key returns the kept value, a source delivers the kept element or `none` at the kept
   source position, and the commit engine reuses a kept decision
   ([Well-formed maps](#well-formed-maps)).

3. **Before an output escapes, the durable observations hold a support for every output escaped so
   far, it included.** An observation is durable when the run has persisted it, or when a source
   that has not released it holds it ([Escape](#escape)).

4. **A kept key is never given to another element, and a redelivered element takes its kept key.** A
   replay or a redelivery returns an element at the source position it took ([Sources](#sources)). A
   message identity, which can be a feed key, maps to the source position the element took on its
   first arrival. A source that numbers arrivals from `0` in each process breaks this obligation:
   after a restart, a new request takes the position of a request that committed before the crash.

5. **Recovered producer states meet the third condition of
   [the durability condition](#the-durability-condition).** A consumer releases a region of its
   input only once what its future outputs need of the region is durable: persisted in one write
   with the guard it releases, `compact(𝑜)` in
   [Compaction](operational-semantics/semantics.md#compaction), or held in durable observations. It
   persists that only once the observations it was computed from are durable. A summary recovered
   without its guard counts the region a second time when the consumer pulls it again. A guard
   recovered without its summary omits the region from every future output, because the consumer
   does not pull it again.

   A source is a consumer of the system it reads. It releases a position once its persisted producer
   state holds the element itself, or once every consumer of the source has released the position. A
   source that releases on arrival is the one release the run cannot hold back
   ([An effect and its record are not atomic](#an-effect-and-its-record-are-not-atomic)).

6. **A reload's entry is durable before any output of the new version escapes.** The entry holds the
   new version, the generations it starts, its seeds and its boundary guards, and recovery needs
   them to compute what the earlier version decided ([Across reloads](#across-reloads)).

7. **After recovery, a reload waits until each sink's release covers its recovery set.** A sink's
   recovery set is `Out(𝑂ᵣ)` at that sink. A reload keeps the earlier version's values only inside
   the evaluation boundary, and after a crash an output that escaped can lie outside it until the
   recovered run computes it again and the sink releases it
   ([The durability condition](#the-durability-condition)). Intake and outputs continue while the
   reload waits. Waiting is the default. A reload set to replace the recovering version does not
   wait, and gives up this obligation for the outputs it computes again
   ([Recovery catch-up](#recovery-catch-up)).

Recomputation needs no obligation of its own. The operator contract makes an operator term's tile a
function of its inputs, and enumerable observation points answering kept keys make the inputs the
same.

---

## Implementation

The obligations leave the runtime free in what it persists and when. This section gives one design
for a single process that meets them without tracking which outputs depend on which observations.

Every term runs as a producer. An observation point's producer is a producer whose output is not a
function of its inputs: the source buffer, a reading's producer, and `CommitOperator` for a commit
clock ([Observations](#observations)). Its observations are its producer state, and no input gives
them back, so it persists them. Whatever persists them meets two requirements:

- **An output waits for its observations.** An output leaves the run only once the durable
  observations hold a support for it and for every output before it
  ([Runtime obligations](#runtime-obligations), the durable observations hold a support for every
  escaped output).
- **Recovery finds a well-formed map.** The persisted observations hold a well-formed map below
  `𝑂₁` ([The durability condition](#the-durability-condition)).

This design persists every observation point's observations in one observation log. The open
question on several processes describes persisting each observation point separately
([Open questions](#open-questions)).

The design is fuzzy checkpointing with a write-ahead log. The observation log is the write-ahead
log of the observation points ([Terms](#terms)). Every other producer checkpoints its state on its
own schedule, with no coordination among producers, and only once the log is durable through the
entries that state was computed from. Recovery only redoes: each observation point replays its
entries, and every other producer starts from its latest checkpoint and recomputes forward from
input its producers still hold unreleased. Nothing is undone, because no checkpoint holds state
computed from an observation the log lost.

In the terms of
[A Survey of Rollback-Recovery Protocols in Message-Passing Systems](https://www.cs.utexas.edu/~lorenzo/papers/SurveyFinal.pdf),
the design is uncoordinated checkpointing with log-based rollback recovery. Holding an output until
the log is durable is that survey's output commit. Uncoordinated checkpointing alone is subject to
the domino effect, in which recovering one producer from an older checkpoint forces its inputs back
to older checkpoints in turn. Log-based recovery avoids it where a recovered producer can answer a
pull for every region its consumers have not released ([Checkpoints](#checkpoints)).

One process writes a run's stable storage at a time. A process takes an exclusive lock on the
storage before recovery and holds it while it runs, so a process started while another is running
cannot persist state or release a source alongside it.

### The observation log

The **observation log** holds every observation the run takes, as a sequence of entries in the
order the run takes them, persisted in that order. It is the write-ahead log of the observation
points ([Terms](#terms)), and distinct from a commit store's per-key changelogs. Each entry is a key
and what its observation point needs to recover the observation at that key, which is the
observation point's choice ([Checkpoints](#checkpoints)).

A commit clock's entry holds the decision and its commit record
([Observations](#observations)). The record is computed, not observed, and the entry holds it so
that a store recovers each tick past its checkpoint by applying the tick's record, without
evaluating a body again. A transaction writes one store, because every mutable variable a
`with begin():` block relates is in one store
([How many commit stores a program has](../src/ccl/design/mutability.md#how-many-commit-stores-a-program-has)),
so one record covers the transaction.

An entry's **log sequence number** (LSN) is its number in the observation log: each entry's is one
more than the entry's before it. An LSN is not a source position. The entry for position 7 of
`orders` can be at LSN 1043, after the readings, decisions and other sources' arrivals taken before
it. A persisted entry keeps its LSN through recovery and after the entries around it are dropped,
and no other entry takes it. Recovery numbers from the end of the durable prefix, so an entry lost
in a crash leaves its LSN to the next observation taken, as a lost arrival leaves its source
position. Write `𝑂[<𝐿]` for the map held by the entries before LSN `𝐿`.

**An observation is appended when it is taken, and it is taken when its observation point answers.**
A source's arrival is taken when the source assigns its source position, a reading when its site is
evaluated at a position, a decision when the commit engine places a proposal at a tick or finds it
stale, and a reload when the runtime swaps versions. Taking and appending are one step, and no term
computes from an observation before it. So everything the run holds at a moment, outputs and
producer states alike, is computed from observations the observation log has already been given.

Every prefix of the observation log holds a well-formed map, because the run's map is well-formed
at every moment ([Well-formed maps](#well-formed-maps)). The observation log is a chain of
well-formed maps, each one entry larger than the one before, and the last holds `𝑂`.

The observation log is **durable through** `𝐿` when every entry before `𝐿` is persisted. Each write
to stable storage appends entries in LSN order and records the LSN through which the observation log
is durable, so recovery finds one durable prefix.

**An output escapes once the observation log is durable through every entry appended before the
output was produced.** The observations taken before an output was computed hold a support for it,
so the durable prefix holds a support for it and for every output computed before it. The obligation
that the durable observations hold a support for every escaped output is met with no record of
dependencies. The prefix over-approximates what each output needs, and the cost is latency: an
output waits until observations it does not depend on are persisted too. Group commit amortizes one
write to stable storage over every output waiting on it, but not over a large entry, such as a
request body from a source that releases on arrival: the write that releases the outputs after it
has to contain the body.

This escape rule is the first implementation and is temporary. Its successor has each output wait
for its own count per observation point, which applies to one process as well as to several
([Open questions](#open-questions), one count per observation point).

The rule also yields `𝑂ᵣ` directly. Every prefix of the observation log is well-formed and the
entries after the durable prefix are lost, so the durable prefix is the largest well-formed sub-map
of the durable observations, and it is below `𝑂₁`.

A finer rule is possible and not required. The compiler knows which observation points reach which
sinks, so an observation log partitioned by sink lets an output wait only for its own partition.
That rule tracks dependencies statically, per sink, rather than per output.

An observation point compacts its entries as any producer compacts its tile
([Compaction](operational-semantics/semantics.md#compaction)). Once every consumer has released a
key, the observation point drops the key's entry and folds it into a summary. Dropping an entry
changes no other entry's LSN and removes nothing from `𝑂ᵣ`: the observation was taken and
persisted, and no consumer asks for it again. A reading at a key a reload keeps is answered from
the observation log, so its consumers include those of every version that keeps the key
([The release model](../src/ccl/design/program-evolution.md#the-release-model)).

No key is reached again once its entry is dropped. A kept domain does not revisit a released
iteration position
([Positions are absolute](../src/ccl/design/program-evolution.md#positions-are-absolute)), and a
rebuilt term mints keys in a new generation. A key of a generation that a reload ended is reached
only inside the reload's boundary guards, whose values the reload's write holds
([Checkpoints](#checkpoints)). That write is therefore the old
generation's release: once it is durable, nothing reads the old generation's entries or the old
clock, and both are dropped.

Recovery recovers each observation point from its entries and its summary, and its consumers pull
from it as during the run:

- **The entries not released** are pulled again. Consumers are recovered from writes made at
  different times, so they pull again from different source positions. Where a source's consumer `A`
  has a checkpoint covering positions `0` through `9` and consumer `B` positions `0`
  through `4`, `B` pulls the recovered source's positions from `5` on and `A` from `10` on.
- **The summary** is what the observation point continues from: a source's next source position and
  a commit clock's latest committed tick. A reading's summary is empty.

A reading is recovered the same way. When a loop reaches a position again, the reading answers from
its recovered entry at that key. At a key it holds no entry for, it asks the world: no observation
was kept there, because an entry is dropped only once no consumer reaches its key again. An
observation point answering a kept key from the observation map
([Runtime obligations](#runtime-obligations)) is this recovery.

### Checkpoints

A producer's **checkpoint** is one write of its producer state and the guard it has released to each
of its inputs. A join holds one guard per input. A producer does not checkpoint the guard its
consumers have released to it: that guard is recovered from the consumers' own checkpoints. Each
producer checkpoints on its own schedule while the run continues, and no two producers' checkpoints
need to describe one moment of the run.

**A producer releases a region of its input only once what its future outputs need of the region is
durable**, in a checkpoint written with the guard it releases, or, for an observation point, in its
entries in the observation log. A source releases a position to the system it reads once its entry
holds the element, and the commit operator acknowledges a commit once the decision's entry, which
holds the commit record, is durable.

A checkpoint holds the producer's tile in the shape
[Compaction](operational-semantics/semantics.md#compaction) gives it: `compact(𝑜)` for the region
`𝑜` every consumer has released, beside the tile `𝑟` no consumer has released yet. The checkpoint
can leave out `𝑟`, or part of it, only where the producer can compute it again from input it has not
released.

**A recovered producer can answer a pull for every region its consumers have not released.** A
summary covers only regions every consumer has released, and a consumer releases a region only once
its own persisted state covers it. So every region a recovered consumer asks for again is in its
recovered producer's `𝑟`, or the producer computes it again from its input. A running sum whose
consumer has released positions `0` through `900` does not persist its sum through position `1000`
and release its input through `1000`. After a crash the consumer would ask for position `901` again,
and the recovered sum would hold only the total through `1000`. A runtime that recovered the sum
from an older checkpoint instead would have to recover the sum's input from an older checkpoint too,
and so on
up the chain: the domino effect. The rule's cost is lag: a release reaches a source one checkpoint
per producer after the sink's release, so the lag of a source's release to the system it reads grows
with the number of producers between the source and the sinks.

A checkpoint holds enough to recover its producer's state after a crash, given what its inputs still
hold unreleased. What it holds is the producer's own choice. An observation point's recovered state
holds each kept observation with its kept value.

A producer checkpoints its state only once the observation log is durable through every entry
appended before the state was computed, as an output escapes
([The observation log](#the-observation-log)). This is the write-ahead rule. The observations the
state was computed from are then in `𝑂ᵣ`, and because `𝐹` is monotone for a fixed reload history
the recovered state stands for a tile below `𝐹(𝑂ᵣ)` at its term.

These rules establish the third condition of [the durability condition](#the-durability-condition).
A recovered state stands for a tile below `𝐹(𝑂ᵣ)`, covers what its producer released, and comes from
one checkpoint with its guard, and a summary covers only regions every consumer has released.

What a checkpoint holds depends on the producer:

- **An observation point** writes its entries to the observation log. A source over a topic
  partition writes only that a position is taken, because the position is the offset and the
  partition holds the record. A standard-input source writes the line itself, because nothing
  upstream holds it ([Sources](#sources)). A random reading can write one random seed and derive
  each reading from it and its key. A commit clock writes each decision with its commit record. A
  source releases a position to the system it reads once its entry holds the element itself, or
  once every consumer of the source has released the position.
- **A producer that compacts** checkpoints its summary of the regions every consumer has
  released: an aggregate's value, a store's seed, changelog and frontier. A running average over
  released points holds their count and their sum, because the count alone does not give the next
  average. A `Memo` holds its cache, because it releases everything it merges
  ([A `Memo` releases everything it takes](../src/interpreter/design-operators.md#a-memo-releases-everything-it-takes)).
- **A producer that holds rows it has not released**, such as a join's open rows or the alarm pair's
  held rows, checkpoints them and then releases what they cover. Until it does, its inputs keep what
  the rows were computed from. A producer releases a region of its input only once it has produced
  every output that the region and the producer's internal state determine, so a row it holds
  determines no output it has not produced: a join holds an order until its customer arrives, and
  holds each customer for every later order that names it. A join that holds customer `1` produces
  `(o1, 1)` before it releases an order `o1` that names customer `1`. Without the checkpoint, its
  input would never release those rows, the observation log would keep their entries, and recovery
  would replay them. Holding rows without persisting them is an open question
  ([Open questions](#open-questions)).
- **A producer whose released region is obsolete** holds `⊥` for it and checkpoints only the
  guard. A sink is this case ([Sinks persist their release](#sinks-persist-their-release)).
- **A producer with no state**, such as a `map`, a `filter` or a `FanOut`, has no checkpoint. Its
  release is the one its consumers' releases permit, and a `FanOut`'s is the intersection of its
  slots' releases
  ([The release contract](../src/interpreter/design-operators.md#the-release-contract)).

The list is what `TileProducer::state_info` counts
([What a producer holds](../src/interpreter/design-operators.md#what-a-producer-holds)). The count
is an inventory of what to persist. The in-process reload already hands a successor its
predecessor's producer states through `OperatorMap::handover`, but the handover holds live
producers. Persisting needs each producer state as data that can be written to stable storage and
read back, which no producer defines today.

A producer chooses when to checkpoint. Checkpointing once the input it has taken since its last
checkpoint passes a bound keeps what recovery recomputes for that producer below the bound, which
checkpointing on a timer alone does not. Until a producer checkpoints, its inputs keep every region
it has not released, and the observation log keeps the entries those regions were computed from, so
how often a producer checkpoints also bounds what the run retains.

A store, its writers and its driver form a cycle, and two of the releases around it are
acknowledgements: the commit operator's release to a writer acknowledges its commit
([The runtime engines](../src/ccl/design/mutability.md#the-runtime-engines)), and a writer's release
to its driver finishes a position (`TransactWriterProducer` in
`src/interpreter/commit_operator.rs`). The commit operator acknowledges a commit once the
decision's entry is durable, because the entry holds the commit record, which is what the store's
checkpoint would otherwise hold for that tick. The store checkpoints on its own schedule, as any
producer does, and after a crash it applies the records of the ticks past its checkpoint. A driver
recovered past the store's checkpoint does not drive those positions again, and a driver recovered
before it drives positions the commit engine answers with their kept decisions
([Runtime obligations](#runtime-obligations), the commit engine reuses a kept decision). A
transaction reads only earlier ticks, so recovering the cycle's producers in tick order has no
domino effect. The induction loop, `InductionDriver` and `InductionStore` through a cyclic
`FanOut`, has no observation point to hold its steps, and checkpoints before each release inside
the loop ([Open questions](#open-questions)).

At a reload, the runtime appends the reload's entry to the observation log, and each term the reload
pairs persists its state at its boundary guard, in the same write as the entry or before it. The
boundary guard covers what the term holds and what its consumers have released to it, so the write
holds the term's unreleased values inside the guard, and a rebuilt store's seed. An output of the
new version waits for that write as for any entry ([The observation log](#the-observation-log)).
Recovery installs the version the latest reload entry of each branch names, and recovers each
producer from a state persisted under that version, so it never runs a retired version's
operators. Without that write, a producer whose latest persisted state predates the boundary would
need the retired version's operators to compute again what that version decided after the state was
written.

Recovery starts each producer from its latest checkpoint, or from `⊥` where it has none, and each
observation point from the observation log. Each recovered consumer issues its
persisted guard to its input as a release, and a producer with no state forwards it as during the
run. Consumers then pull as during the run. A producer recovered from an older write than its
latest in-memory state pulls again the regions it had not released, and its input still holds them
because the release never went out. A recovered producer pulls only outside the guards its
checkpoint holds, so recovery never merges into a producer a region its checkpoint already
covers.

### Sinks persist their release

A sink checkpoints the guard it releases upon each release, after sending the outputs in the
region and before the release reaches the sink's input. A "client-like" sink making a call outside
the program is a sink for its requests and an observation point for its replies, so it does not
release a request until the reply's entry is durable
([A call made outside the program](#a-call-made-outside-the-program)).

Recovery starts each sink from its latest persisted release, which is what
[recovery catch-up](#recovery-catch-up) compares against the sink's recovery set. Under the release
model, a term upstream computes a released position only where another consumer still asks for it
([The release model](../src/ccl/design/program-evolution.md#the-release-model)). An output already
sent is neither recomputed nor sent again. An output sent and not yet inside the sink's persisted
release is sent again
([An effect and its record are not atomic](#an-effect-and-its-record-are-not-atomic)).

The observations a sent output depends on were persisted in the observation log before it escaped,
and their entries are dropped only once every consumer of their observation point has released
them ([The observation log](#the-observation-log)). A request whose reply was sent is still
recomputed when its transaction feeds a counter that later requests read, and only its reply is
skipped.

### Recovery catch-up

A reload after recovery waits until each sink's release covers its recovery set
([Runtime obligations](#runtime-obligations)). The recovery set is what `𝐹(𝑂ᵣ)` decides at the
sink, and no producer holds it as a value, so the runtime checks it edge by edge from the
observation points down. Recovery has **caught up** at a term once it has caught up on each of its
inputs:

- **An observation point** has caught up when recovery starts. What it has produced is its entries
  in `𝑂ᵣ`.
- **A consumer has caught up on an input** once the input has caught up and the consumer's release
  covers everything the input had produced at that moment.

A caught-up sink's release covers its recovery set. A consumer releases a region only once what its
future outputs need of it is durable, in its checkpoint or in the observation log, and a producer
releases a region of its input only once it has produced every output that the region and the
producer's internal state determine ([Checkpoints](#checkpoints)). So a term that has caught up has
produced `𝐹(𝑂ᵣ)` at its term, either released by its consumers or held unreleased, and the rows it
holds determine no output in `𝐹(𝑂ᵣ)` that it has not produced.

For example, take a join of `orders` with `customers` on customer id, where `𝑂ᵣ` holds orders `o1`
to `o4` and customers `1` to `4`, and `o4` names customer `5`. The join has caught up once it has
released `o1` to `o4` and customers `1` to `4`. It releases `o4` once it has persisted `o4` as a
held row, because `o4` and the join's internal state determine no output. It releases `o1` once it
has produced `(o1, 1)`. A sink after it has caught up once its release covers `(o1, 1)` to
`(o3, 3)`, the outputs the join had produced when it caught up. A `Memo` whose persisted cache holds
outputs its sink had not released before the crash has caught up when recovery starts, and its sink
has caught up once it releases them.

A cycle, such as a store with its writers and its driver, catches up as one term, on the edges that
enter it. A store has produced every tick `𝑂ᵣ` decides once it has applied the records of the ticks
past its checkpoint ([The observation log](#the-observation-log)), so once the cycle has caught up
on its inputs it has produced every tick `𝑂ᵣ` decides.

Each term records in memory the guard of what it had produced when it caught up on its inputs.
Intake and outputs continue during the check, and only a reload waits for it.

**A reload can replace the version catch-up runs under.** A version that crashes deterministically
during catch-up crashes again after each recovery, so a reload that waits for catch-up never
installs a fix. A reload therefore has a setting that replaces the recovering version; without it,
the reload waits. A reload with the setting takes as its boundary guard at each term the evaluation
boundary recovery restored, and the new version computes everything outside it from `𝑂ᵣ`. Every
observation in `𝑂ᵣ` keeps its key and its value, so immutable history holds. A store the reload
rebuilds seeds at the last tick `𝑂ᵣ` decides on its clock, which the store reaches by applying the
kept ticks' records.

The cost falls on [Escape](#escape). A sink's outputs between its last persisted release and what it
had sent before the crash are computed again by the new version wherever they pass through a term
the reload rebuilds. Such an output keeps its key where the reload keeps its site and the domains of
the loops around it, and takes a new key where the reload rebuilds one of those domains. A sink that
drops a key it has delivered keeps the earlier value, and any other recipient receives both. An
output whose computation crashed was never sent, so the value the new version computes for it
contradicts nothing.

### Sources

A source meets three runtime obligations through how it numbers its elements and how it keeps them
available to recovery: observation points answer kept keys, a kept key is never given to another
element, and recovered producer states meet the third condition
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
checkpoint depends on it, and the runtime obligations make the element durable before
either. What the source persists for it depends on what the system it reads gives back:

| What the system it reads gives back                              | Example                                     | The source position an element takes                   | What the source persists   | A crash before the element's entry is persisted                              |
| ---------------------------------------------------------------- | ------------------------------------------- | ------------------------------------------------------ | -------------------------- | ---------------------------------------------------------------------------- |
| The element at a permanent address, until the source releases it | a topic partition                           | its address, the offset                                | that the position is taken | the source reads the address again, and the element takes the same position  |
| The element again, until the source acknowledges it              | a message queue; `time::alarms()`           | the position the run recorded for its message identity | the message identity       | the queue delivers it again, and another element may take its position first |
| Nothing                                                          | standard input, a UDP feed, an HTTP request | its arrival order                                      | the element                | the element is lost                                                          |

Two rules apply to every kind:

- **A system that holds an element only up to a limit.** A topic's retention by time or by size, and
  a queue's limit on deliveries, discard an element whether or not the source has released it. The
  source persists the element itself before such a limit can pass while the element is unreleased,
  and recovery then finds the element in its entry.
- **A missing element fails recovery.** A source that finds an element it took and has not released
  missing from the system it reads stops recovery. It does not state `none` at that position,
  because an escaped output or a checkpoint may depend on the element.

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

`time::alarms()` returns a pair: a `set_expiry` feed and an `expiries` source
([`time::alarms()`](chl-spec.md#timealarms)). The program feeds alarm rows to `set_expiry`, and each
row comes out of `expiries` once the clock reads at or after the row's `at` field. A row fed to the
pair does not escape the run. The rows the pair holds, its pending alarms, are its producer state
and are checkpointed as [Checkpoints](#checkpoints) describes. An alarm row
is persisted in one of two places:

1. **In the pair's checkpoint**, from the checkpoint after the row is fed to `set_expiry`
   until the row comes out of `expiries`.
2. **In the observation log**, from when `expiries` takes the row.

The pair is a message queue in the table above: it hands a row back until its entry is persisted,
and the row's message identity is its feed key ([Outputs are keyed](#outputs-are-keyed)). A row
appended with `<<` has a feed key no other row shares. The rows one `<<=` defines share a site and
a position, so their feed keys also need each row's key in the defined collection
([Consequences for other documents](#consequences-for-other-documents), 4.4). The entry that
`expiries` appends for a row records the row's feed key. The entry is persisted before the pair
persists its state without the row, so no alarm is lost between the two writes. A crash between
them leaves the row in both, and recovery removes from the recovered held rows every row whose feed
key already has an entry. A crash before the entry is persisted leaves the row only in the held
rows, and `expiries` takes it again at the next source position. No output depended on the lost
entry, because outputs wait for their entries
([The observation log](#the-observation-log)).

Numbering alarms by the order the pair releases them does not work: recovery would bring back the
held row beside its durable entry at source position `𝑝`, and `expiries` would take it again at a
later position, a second arrival that commits a second time any transaction it drives. Equal row
values cannot tell the two apart either, because two identical alarms can both be legitimate. The
feed key identifies the row, so its second appearance is the same message.

#### Work after a commit

A transaction refuses `AffectWorld`
([Transactions are keyed](#transactions-are-keyed-by-their-site-and-position)). Work that has to
happen after a commit is appended to a feed inside the transaction, which holds the row until the
transaction commits and drops it if it does not
([8.4 Feeds are the second form of mutability](chl-spec.md#84-feeds-are-the-second-form-of-mutability)).
A loop outside any transaction consumes the feed and makes the call, passing the row's feed key as
the call's idempotency key:

```python
balance := 1000
charges: Feed({order: Int, amount: Int})
for o in orders:
    with begin():
        balance := balance - o.amount
        charges << (order=o.id, amount=o.amount)      # appended only if the transaction commits
for c in charges:                                     # outside any transaction
    payments.charge(c.amount, idempotency_key=c.key)  # c.key: the row's feed key
```

CHL has no syntax for a row's feed key yet; `c.key` stands for it
([Consequences for other documents](#consequences-for-other-documents)).

A row of a feed appended inside a transaction is identified by its feed key wherever it goes. A loop
over the feed holds no rows: its positions are the feed's keys, and recovery recomputes each row at
the key it had. `payments.charge` is a call made outside the program, so it releases a row only once
its reply's entry is durable, and a crash before then sends the request again with the same
idempotency key ([A call made outside the program](#a-call-made-outside-the-program)).

#### A call made outside the program

A call made outside the program is a sink for its requests and an observation point for its
replies: the request and the reply share the call's key ([Outputs are keyed](#outputs-are-keyed)).
Until the reply is kept, the call may have to send the request again, so it releases a request only
once the reply's entry is durable ([Checkpoints](#checkpoints)). A crash
before the reply's entry is durable leaves the request unreleased: recovery computes it again, and
the call sends it again with the same key. A crash after it finds the reply in `𝑂ᵣ`, and the call
sends nothing.

Releasing a request once it is sent loses the reply: after a crash the request is released, so
nothing computes it again, and the reply's connection died with the process. A client's
specification states the rest: whether the remote recognizes the key, which a resent request needs
to act once ([An effect and its record are not atomic](#an-effect-and-its-record-are-not-atomic)),
and what the call does when the remote never answers.

#### HTTP requests

`http::serve`'s requests release on arrival. Each connection is a new source position, and nothing
holds the request. A crash closes the connection, and a response computed for it has no recipient
and is dropped. The request's effects stay kept once persisted, because another output may depend on
them. The client's resend is a new arrival at a new position, so a transaction the first request
committed commits a second time.

#### The life of one arrival

An element arrives on partition 0 of the topic `orders` at offset 120, so it takes source position
120 of the source that reads that partition. Its entry in the observation log is at LSN 1043 and
records that position 120 is taken; the partition holds the element.

| Step                       | What happens                                                                                                                                                                           | Copies of the element                                                                             |
| -------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------- |
| 1. Arrival                 | The source receives the element at position 120. Its entry is appended to the observation log at LSN 1043, in process memory.                                                          | the partition; process memory                                                                     |
| 2. Persist the entry       | The observation log is persisted through LSN 1043. Position 120 is kept.                                                                                                               | the partition; process memory                                                                     |
| 3. Escape                  | Outputs computed from position 120 leave the run.                                                                                                                                      | unchanged                                                                                         |
| 4. Checkpoint              | Each consumer of the source checkpoints its state covering position 120, then releases position 120.                                                                                   | the partition; process memory; what position 120 fed, in each consumer's checkpoint               |
| 5. The source's release    | Every consumer has released position 120. The source drops its buffered copy, commits its progress through offset 120 to the partition, and drops the entry at LSN 1043, in any order. | what position 120 fed; the partition, until its retention passes                                  |

Three rules order the steps:

- **Persisting the entry comes before escaping.** An output computed from position 120 leaves the
  run only once its entry is persisted (step 2 before step 3).
- **Persisting the entry comes before checkpointing.** A checkpoint computed from position 120
  stands for observations recovery keeps only once its entry is persisted (step 2 before step 4).
- **A consumer persists before it releases.** Until every consumer has released position 120,
  recovery may recover one that pulls position 120 again, and the entry holds no element, so the
  partition still has to hold it (step 4 before step 5).

Steps 3 and 4 can occur in either order.

A source that releases on arrival releases to the system it reads at step 1. Its entry holds the
element, and between steps 1 and 2 process memory holds the only copy
([An effect and its record are not atomic](#an-effect-and-its-record-are-not-atomic)).

### Requirement and implementation side by side

| The model requires                                                  | This design provides                                                                                                        |
| ------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------- |
| A kept observation has one value for the run                        | Observation points answer kept keys from the observation log                                                                |
| A support for every escaped output is kept                          | Outputs wait for the observation log's durable prefix                                                                       |
| An output is sent once, up to the limit                             | Each sink persists its release when it releases                                                                             |
| `𝑂ᵣ` is well-formed and `𝑂ᵣ ≤ 𝑂₁`                                | `𝑂ᵣ` is the durable prefix                                                                                                 |
| Recovered producer states stand for tiles below `𝐹(𝑂ᵣ)`           | A producer checkpoints only once the observation log is durable through the entries its state was computed from             |
| A released region is not needed again                               | A consumer releases only once its checkpoint, or the observation log, holds what it needs of the region                     |
| A reload's boundary is kept                                         | The reload's entry, and each paired term's state at its boundary, are persisted before an output of the new version escapes |
| Determined values only are recomputed                               | Recovered producers pull from inputs recovered from checkpoints and the observation log                                     |
| Outputs are recognizable when re-emitted                            | Sinks receive each output's key                                                                                             |
| A kept key keeps its meaning across reloads                         | A rebuilt term mints its keys in a new generation, and a rebuilt store's clock is a new clock                               |
| Every escaped output lies inside each later reload's boundary guard | After recovery, a reload waits for recovery catch-up unless set to replace the recovering version                            
| A row handed from a feed to a source arrives once                   | The source records the row's feed key, and recovery drops held rows whose feed key has an entry                             |
| A call's reply is kept or its request is sent again                 | A call releases a request only once the reply's entry is durable                                                            |

---

## Consequences for other documents

These statements conflict with the model or depend on it. Of them, only
[7.5 Time](chl-spec.md#75-time-decided) is edited here.

The model's consequences:

- **[Instances](operational-semantics/semantics.md#instances)** lists partial functions but not
  the commit clock's tiling, a partial function tiling with `⊕` defined on fewer pairs, that
  [The observation map](#the-observation-map) uses.

- **[The Operator Contract](operational-semantics/semantics.md#the-operator-contract)** makes an
  operator's output a function of its input tiles. `CommitOperator` realizes an observation point
  and breaks it, deciding ticks by the schedule, and the semantics has no term kind for it
  ([Observations](#observations)). `AsOfProducer` breaks it today by latching by the schedule, and
  #811 removes it.

- **[What a reload computes](operational-semantics/semantics.md#what-a-reload-computes)** takes
  `y₁` to be what the term held at the swap. Under the model the boundary guard is the term's
  evaluation boundary, which also covers what the term's consumers have released, and a reload
  entry is valid only with a guard that covers it ([Across reloads](#across-reloads)).

- **[What a producer holds](../src/interpreter/design-operators.md#what-a-producer-holds)** counts
  the values a producer retains, and `OperatorMap::handover` passes live producers. No producer
  defines its producer state as data that can be persisted and read back with the guard it has
  released. Checkpointing needs that for every stateful producer
  ([Checkpoints](#checkpoints)), and recovery catch-up needs each
  producer to give the guard of what it has produced ([Recovery catch-up](#recovery-catch-up)).

- **[How a reload works](../src/ccl/design/program-evolution.md#how-a-reload-works)** swaps versions
  without recording where each term's boundary was taken. Under the model a reload is an observation
  ([Observations](#observations)). The swap appends the reload's entry, with the generations it
  starts, its seeds and its boundary guards, before the new version computes anything, and recovery
  recovers [the branch table](../src/ccl/design/program-evolution.md#the-branch-table), which holds
  each branch's version in process memory, from those entries. A reload after recovery waits for
  recovery catch-up.

- **[Vocabulary](../src/ccl/design/program-evolution.md#vocabulary)** defines a commit tick as a
  store's private counter that a rebuilt store restarts at `0`. Under the model the rebuilt store's
  clock is a new generation, and the reload's entry links its tick `0` to the old clock's frontier.
  The counter stays private and restartable.

- **[A `Memo` releases everything it takes](../src/interpreter/design-operators.md#a-memo-releases-everything-it-takes)**
  releases each region as it merges it. Under [Checkpoints](#checkpoints) a consumer releases only
  once its checkpoint holds what it needs, so a `Memo`'s release, and every compacting producer's,
  waits for a checkpoint. Compaction in memory does not wait: a crash before the checkpoint leaves
  the region unreleased, and the recovered producer pulls it again.

- **Observations are taken in separate producers.** The source buffer assigns positions
  (`src/interpreter/stream_buffer.rs`), `CommitEngine::attempt` decides proposals, and
  `AsOfProducer` latches values. None appends to a shared sequence, and the observation log needs
  each to append at the moment it answers ([The observation log](#the-observation-log)).
  `CommitEngine::attempt` sees a step local to the writer, not the transaction's site and position,
  and a retry is not a decision it records. On main two decisions also bypass the commit engine: a
  deny or a grant that writes nothing is decided in `TransactWriterProducer`, which #810 changes,
  and a read-only transaction compiles to `AsOf`, which #811 changes.

- **[`mutability-walkthrough.md`](mutability-walkthrough.md)** calls a commit store's per-key
  changelogs "the commit log". The observation log is a different thing, and the two names differ
  only in their first word.

- **[mutability.md](../src/ccl/design/mutability.md)** does not say whether a transaction may make a
  call outside the program. Under the model a transaction refuses `AffectWorld`, and the check
  follows the capability through calls
  ([Transactions are keyed](#transactions-are-keyed-by-their-site-and-position)).

- **[8.3 Reads](chl-spec.md#83-reads)** describes an as-of read at an arbitrary commit position,
  and [The runtime engines](../src/ccl/design/mutability.md#the-runtime-engines) has `AsOf` latch a
  store's value when a trigger position is first observed. Under the model a read-only transaction
  takes a tick on its store's clock ([Observations](#observations)), as #811 makes it.

- **[4.4 Define statement `<<=`](chl-spec.md#44-define-statement-)** gives a feed every row of a
  collection from one evaluation of one statement. The rows share one site and one position, and
  so one feed key ([Outputs are keyed](#outputs-are-keyed)). The proposal is that a row defined by
  `<<=` takes one more component in its feed key: the defined collection's operator in its
  generation, and the row's key in it, as a loop over a collection contributes ([Terms](#terms)).
  Without it, two alarms defined by one `<<=` share a message identity, and recovery drops the
  second ([`time::alarms()`](#timealarms)). Whether `<<=` survives at all is **[Open]** in 4.4.

- **[8.4 Feeds are the second form of mutability](chl-spec.md#84-feeds-are-the-second-form-of-mutability)**
  indexes a reply inside a transaction by commit tick, and mutability.md's `by_commit_time` keys a
  reply by `Txn`. Under the model a reply's key is its feed key, the transaction's position without
  the attempt index ([Outputs are keyed](#outputs-are-keyed)), as #809 keys it. CHL also has no
  syntax for a row's feed key, which a consumer needs as an idempotency key
  ([Work after a commit](#work-after-a-commit)).

- **[7.5 Time](chl-spec.md#75-time-decided)** is edited here: "A reading orders nothing" and
  "Commit order never consults a reading" describe the current `time::now()`, a weak clock. A
  transactional clock, whose readings the commit engine places in commit order, would order its
  readings. A follow-up renames the current call `time::weak_now()` and keeps `time::now()` for the
  transactional clock. #585's
  section 7.5 still carries a clock floor and needs to drop it.

- **[`time::alarms()`](chl-spec.md#timealarms)** says a process exit discards held rows. Held rows
  are a producer state and are recovered, and each row's message identity is its feed key
  ([`time::alarms()`](#timealarms)).

- **The effects work's readings** state that a reading belongs to its version of the program, that
  a reload may take it again, and that a reading survives a crash only as the producer state
  holding it does. The model replaces all three with [Immutable history](#immutable-history). Main's
  [7.5 Time](chl-spec.md#75-time-decided) agrees with the model for a top-level binding. The spec's
  "Inputs from outside the program" (#656) and #585 record a reading on first evaluation so that a
  retried transaction reads the same value. Under the model each attempt takes its own readings
  ([Transactions are keyed](#transactions-are-keyed-by-their-site-and-position)).

- **The effects work's keys** leave gaps the model needs closed:
  - **A transaction has no site.** `WriterSite` holds no `Site`, and no place kind covers a
    `with begin():` block, so neither the decision key `(𝑠, 𝑝)` nor `begin_<site>` has a site yet.
    The store's site cannot stand in, because one store has many writers.
  - **A reload pairs readings by node correspondence, not by site.** `content_hash` hashes only a
    reading's kind, and the effects work's reload tests for readings pin two failing cases. Keeping
    a reading at a kept key needs pairing by site ([Immutable history](#immutable-history)).
  - **A position names no domain.** The spec's position counts loop iterations. Under the model each
    component also names the loop's domain, the operator the loop iterates, in its generation
    ([Terms](#terms)).
  - **"Position" has two scopes.** The runtime `Position` (`src/interpreter/types/value.rs`) and
    the spec's `OrderableFor(P, E)` mean one loop's component, which this document calls an
    iteration position; the spec's position of an evaluation covers every loop.
  - **A component of a position has three names.** The spec's position is "extended by one
    iteration for each loop", `ReadingSource` keys a reading by "the key path of the loops around
    the reading", and [Vocabulary](../src/ccl/design/program-evolution.md#vocabulary) calls one an
    iteration position. This document uses iteration position, because it uses key for an
    observation's key `(𝑠, 𝑝)`.
  - **"Call path" has three definitions.** The spec's is the call sites alone, the IR design's is
    the whole site, and `design-operators.md`'s `Readings` entry uses it for the key of a
    `ReadingSource`, which the code keys by `Site`. This document uses the site and drops the term.
  - **Which binders a position covers is unsettled.** The spec counts loops. The IR design binds a
    reading's position over the loops and lambdas around it, then calls a reading under a lambda
    constant.
  - **The run is in two places.** The spec's position starts at the run's start, and `Site` holds
    the run's path. [Terms](#terms) assumes the run is in the site, so a top-level position is
    empty.
  - **The site definitions are stale.** `chl-spec.md` defines a site as a `<<` with the calls that
    reached it, without the run or the other place kinds, and
    [Stability](../src/ccl/design/sites.md#stability) does not cover the effects work's new place
    kinds.
  - **Links depend on the effects work.** This document cites #656 and #691 in prose and links
    neither, because their documents are not on main.

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

- **Client and sink configuration** has no document yet. A call does not release a request, and
  its inputs keep what the request was computed from, until the reply is kept
  ([A call made outside the program](#a-call-made-outside-the-program)). Where a release guard
  cannot skip an unanswered request, one slow reply holds back the release of every later request.
  Such a document states a call's release granularity, its idempotency key, and what it does when
  the remote never answers.

---

## Open questions

- **[Open] Each output waits for its own count per observation point.** This is the successor to
  the escape rule of [The observation log](#the-observation-log), for one process as well as for
  several. When an output is computed, the runtime records how many entries each observation point
  that reaches the output's sink has taken, and the output leaves once each point's storage has
  confirmed that many. A point's count is its own append count. It follows a source's source
  positions and a commit clock's ticks, and it is not a reading's position, because a reading is
  taken in schedule order. An output then waits only for the observation points it can depend on,
  so a large entry holds back only the outputs of its own point.
- **[Open] Several processes.** The observation log's escape rule needs one take order, which
  processes that keep separate logs do not share. An observation log kept in a replicated store is
  still one observation log with one take order. The alternative is for each observation point to
  persist its own observations, and one log per process is the case where a process's observation
  points share one stream:
  - **An output waits for one count per observation point**, as the open question above describes.
  - **Recovery drops orphaned entries.** Each point's persisted entries can hold an entry that is
    not reached or not valid without an entry another point lost: a reading at position 7 without
    the source's element at source position 7, or a commit whose writer's decision at an earlier
    position was lost. Recovery drops it and every entry that needs it, such as each later decision
    of its writer and each later commit on its clock, which leaves the largest well-formed sub-map
    ([Well-formed maps](#well-formed-maps)). No escaped output or checkpoint depends on a dropped
    entry, because each waited for the entries it needs as well.
  - **Each point uses its own storage.** A topic source can keep its entries in the topic's
    committed offsets, and a commit clock in its store's changelog. Each point drops its released
    entries from its own stream, where one log holds entries of mixed lifetimes.
  - **An output can wait for several writes.** An output depending on three points waits for three
    confirmations, where one write to the observation log releases every output waiting on it.
  - **A reload is a cut.** A reload's entry has to be ordered against every observation point, so
    with separate logs a reload is a cut across them.

  Checkpoints need no coordination across processes, because each producer checkpoints its own
  state.
- **[Open] Holding rows without persisting them.** A producer that holds rows persists them
  ([Checkpoints](#checkpoints)). Keeping them only in memory and computing
  them again at recovery would save a write per bound. A streaming join is the first producer
  where the saving matters, because it holds every row of one input for as long as the other stays
  open ([Streaming Joins](../src/interpreter/design-operators.md#streaming-joins)). Its input then
  keeps every row that has determined no output yet, so the observation log keeps those entries and
  recovery replays them. Such a producer never releases a held row, so
  [Recovery catch-up](#recovery-catch-up) does not finish until each row it holds determines an
  output and the producer releases it.
- **[Open] Persisting an observation only in its consumers' checkpoints.** The observation log holds
  in full every input that no outside system keeps a copy of, such as an HTTP request body, a line
  of standard input or the reply to a call made outside the program, and the input's consumers
  checkpoint what they derive from it again. An entry is needed only until every consumer of its
  observation point has released its key ([The observation log](#the-observation-log)). Suppose the
  first consumers that hold state checkpoint it, and release the key, in the same write as the
  entry. The entry can then leave out the observation's value, and those checkpoints are its only
  record. For an HTTP request that commits a transaction, the decision's entry with its commit
  record is then the only write. The compiler knows the dataflow graph, so for each observation
  point it can choose consumers after the filters, projections and aggregates that shrink the data.
  The model has to count such an observation as kept, because no write holds its value. The
  implementation has to write an entry and several producers' checkpoints as one write, where
  [Checkpoints](#checkpoints) writes each producer's checkpoint on its own schedule. Each
  observation point already chooses what its entry holds, so neither changes an obligation.
- **[Open] Outputs to sinks with no recipient after a crash.** An `http::serve` response has no
  recipient after a crash ([HTTP requests](#http-requests)). An output that reaches only such sinks
  then needs no support in `𝑂ᵣ`, and a read-only HTTP request would persist neither its body nor
  the clock readings outside its transaction. This relaxes [obligation 3](#runtime-obligations),
  that the durable observations hold a support for every escaped output, so it needs its own
  decision before anything relies on it. The compiler can check which observation points reach
  which sinks. A read-only transaction still takes a tick on
  its store's clock, and a later commit on that clock is valid only once that tick is decided
  ([Well-formed maps](#well-formed-maps)). Its decision, and every reading its body took, are kept
  whenever a later commit on the clock is kept, unless the model lets a read-only transaction's tick
  be dropped.
- **[Open] Deleting a branch.** Recovery recovers
  [the branch table](../src/ccl/design/program-evolution.md#the-branch-table) from reload entries.
  Creating a branch is a reload
  ([A branch is created by branch-and-reload](../src/ccl/design/program-evolution.md#a-branch-is-created-by-branch-and-reload)),
  so it appends an entry, and
  [deleting a branch](../src/ccl/design/program-evolution.md#deleting-a-branch) appends none, so
  recovery brings a deleted branch back. A deletion needs an entry in the observation log. It frees
  the operators no other branch holds, which ends their generations, so the entry is also their
  release.
- **[Open] Checkpointing an induction loop as one unit.** An induction loop has no observation point
  whose entries hold its steps, as a commit clock's records hold a store's ticks, so under
  [Checkpoints](#checkpoints) its store checkpoints before each release to its driver, which puts
  one write in every iteration. Checkpointing the loop as one unit at the positions of the loop
  around it keeps the releases inside it in memory, as Falkirk Wheel persists a loop at its outer
  timestamps ([Falkirk Wheel](https://icgog.github.io/data/papers/2021-socc-falkirk.pdf)). That
  needs a cut that says what happens to the iterations in flight. Without one, a driver recovered as
  having finished positions through `9` beside a store recovered at position `5` never drives
  positions `6` through `9` again, and the store cannot pass position `5`.
- **[Open] When a cycle reaches `𝐹(𝑂)`.** `𝐹(𝑂)` is the least program state that satisfies the
  equations of
  [The program state an observation map determines](#the-program-state-an-observation-map-determines).
  An iteration reaches it only if the iteration stops, and the semantics defines a stopped program
  as one with no tile left to extend
  ([Termination and Extraction](operational-semantics/semantics.md#termination-and-extraction)). A
  cycle of operators, such as a store and its writers, has no rule in the semantics for when it
  stops. A source that never ends needs no such rule:
  [The durability condition](#the-durability-condition) needs only `𝐹(𝑂ᵣ) ≤ 𝐹(𝑂ₖ)` for each finite
  map `𝑂ₖ` the run reaches later, which monotonicity for a fixed reload history and recovery
  catch-up give.
