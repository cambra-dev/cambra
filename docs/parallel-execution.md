# Parallel execution of the operator graph: pipeline breakers and their state

Research notes toward task- and data-parallel execution of a compiled program's operator graph,
on one machine. Every claim about the runtime names the code it rests on; the parts drawn from
the database literature are marked as such. The thread-safe handles are implemented
(`src/interpreter/design-parallel.md`, "Thread-safe handles"); nothing else is.

## Summary

1. **Eight operator kinds hold state across pulls; every other operator is a homomorphism over
   its input and can run on any slice of it.** The state holders are `Memo`, `Aggregate`,
   `MapAggregate`, `Converse`, `ExtractFinal`, the store engines (`InductionStore`,
   `CommitProducer`) with their drivers and writers, `AsOf`, and `IterateExtent` (the source
   cursor). `FanOut` holds shared release state but no data. These are the pipeline breakers,
   with the distinction below between a breaker that blocks (`ExtractFinal`, `ExtractAggregate`
   with `only_terminal`, the split form of `CheckedLookup`) and one that materializes while
   streaming through (`Memo`, `MapAggregate`, `Converse`).
2. **The semantics already licenses morsel-driven execution.** An operator that is a homomorphism
   maps `a ⊕ b` to `op(a) ⊕ op(b)` (`docs/operational-semantics/semantics.md`, "Streaming via
   Homomorphisms"). A morsel is a tile over a disjoint sub-domain, and the stateless chain between
   two breakers is a composition of homomorphisms, so running it per morsel and merging the outputs
   with `Tile::merge` is the semantics' own rule, not a new one. The breakers are where a merge law
   beyond `⊕` is needed, and that law is the content of the per-operator state model below.
3. **The projection guard is the morsel.** `TileProducer::get` already takes a projection guard
   (`design-operators.md`, "The producer protocol"), and every tile operator restates a `Domain`
   interval guard for its inputs (`design-operators.md`, "Projection guards"), across levels the
   way `through_shared_levels` restates releases. A worker then pulls one row range of a source
   through a chain without touching the other workers' ranges, and no second protocol is needed.
4. **Partitioning stays out of the guard algebra.** Range partitions are spellable as
   `Predicate::Intervals`; hash partitions are not, and `design-operators.md`, "Guard operations
   are exact" forbids an approximate spelling. Hash partitioning is needed only inside a breaker,
   between its build and its probe, where it is private state and names no tile region. The
   exchange between partitions is internal to the breaker.
5. **The pull-per-lap model is the first obstacle, before threads.** A stateless producer re-renders
   everything its input has not released on every pull (`MapResultProducer::get_impl`,
   `ProductProducer::get_impl`, `ConverseProducer::get_impl`). Only a `Memo`, an `Aggregate` or a
   `MapAggregate` releases what it takes and so turns its input into a delta stream. A morsel
   pipeline is a push of one delta through a chain, so the chain's head must be a delta source
   (a source range, a `Memo` increment, a store render) and its tail a breaker that consumes and
   releases.
6. **Every shared handle is thread-safe and the operator traits carry the thread bounds.**
   `TileOperator` is `Send + Sync`; `TileProducer`, `Consumer` and `DataSourceDomainExtentImpl`
   are `Send`; the handles are `Arc<Mutex<_>>`, `Arc<RwLock<_>>` and atomics
   (`src/interpreter/design-parallel.md`, "Thread-safe handles"). A CCL `Type` is not `Send`, so
   nothing a thread holds stores one.
7. **A head hands out morsels, and the execution threads claim them through a dispatcher.** A
   work package is a pipeline and a morsel guard, never a tile. A worker asks for a morsel when it
   needs one and the pipeline's morsel source answers it, so no queue holds morsels. A finite
   source answers by advancing a cursor, a live source's answer is the arrivals not yet claimed,
   and a materialized output's head answers its rows; the released predicate governs reclaim, not
   claiming. A worker stays on one pipeline while it has work. A partitioned breaker's output is
   claimable only when a round's merge has run. A ring of immutable segments at each head, with
   reference-counted tiles and per-segment reclaim, is an optional refinement ([Optional: a ring of
   segments at each head](#optional-a-ring-of-segments-at-each-head)).
8. **Recommended shape: thread-confined producer chains per worker, shared state only at the
   breakers.** The chain between two breakers is instantiated once per worker (the protocol already
   permits several subscriptions to one operator through `FanOut` slots), and the breaker is the
   one object several workers write. The alternative, one producer per operator with `get`
   re-entrant across threads, puts a lock on every pull and is incompatible with `FanOut`'s
   re-entrancy cache.

## The runtime as it bears on parallelism

### Execution is one thread pulling whole tiles

`src/main.rs`'s loop polls every source, delivers notifications, pulls every `main` and every
queued sink once, and sleeps 10 ms when nothing was delivered. A pull is a recursive `get` down
the producer tree; a notification is a recursive `notify` up the consumer tree, gated so each
operator is woken at most once per pull (`scheduler.rs`, `GatedConsumer`). Threads exist only at
the I/O boundary: the HTTP dispatcher (`http_server.rs`), stdio (`stdio.rs`), the control port and
the inspector's websocket. Every handle is thread-safe and every operator `Send + Sync`
(`src/interpreter/design-parallel.md`, "Thread-safe handles"), and nothing uses it yet.

A recurrence advances one position per pull: the cyclic `FanOut` serves a snapshot taken before
the traversal began (`design-operators.md`, "One position per pull"). This bounds the
parallelism available along a loop's positions to one, by construction. Across independent
recurrences, and across the enclosing rows of a nested one, it bounds nothing.

### Tiles are columnar and already blocked

`ColumnValue` is struct-of-arrays (`Ints(Vec<i64>)`, `UInts`, `Strings(Vec<SmolStr>)`, `Bools`,
`Records(HashMap<SmolStr, ColumnValue>)`, `Union(TagMap<UnionArm>)`). A collection level is a CSR
layout: `row_starts` into one `domain` column with one `codomain` tile over the keys. Element-wise
chains compile to a `ScalarProgram` that runs in blocks of 1024 rows (`BLOCK_ROWS`,
`scalar_expr.rs`), with one slot column per instruction reused across blocks. That is a morsel
loop in miniature, inside one operator: peak memory is the input, the output and one block of
slots.

Two things work against cache efficiency and matter for the breaker designs:

- A grouped accumulator is `HashMap<Vec<Value>, Tile>` (`MapAggregateProducer::accumulators`),
  one heap-allocated `Tile` per group keyed by a `Vec<Value>` path. The per-pull output rebuilds
  the whole level from these entries, sorted by path. `Converse` holds `Vec<(Value, Value)>` and
  sorts it on every pull (`converse_collection`).
- `Zip` and `Product` build a `HashMap<Vec<Value>, usize>` over every path on every pull
  (`Tile::rows_by_path`), re-joining the arms by key rather than by position.

### Guards spell ranges, not hashes

`Predicate` admits `Intervals(IntervalSet<Value>)` over a scalar key and componentwise `Record`
predicates over a record key, plus `Qualified` paths and `Or` (`design-operators.md`,
"Predicate"). A row range of a source is a `UIntRange` interval; a key range is an interval. A
residue class of a hash has no spelling and must not get an approximate one.

`IterateExtentProducer` subtracts a released predicate from its extent and asks the source for the
elements not yet released, per producer name (`get_elements(producer)`,
`TestDataSource::get_elements`). The released predicate is an interval set, so releases need not
arrive as a prefix: morsels completed out of order release as disjoint intervals and the set
coalesces them.

### What the semantics promises and what it does not

`docs/design.md`, "The execution model": unordered-bag semantics plus data-dependency-only
ordering is parallelism; the scheduler may run any non-dependent work concurrently. The
homomorphism rule gives the merge law for stateless chains. For a breaker the semantics gives
monotonicity and compaction (`semantics.md`, "Compaction": a per-operator `compact` into a summary
tiling that is a homomorphism and preserves terminality), which is exactly the shape a per-thread
partial state needs: each worker's partial is a tile of the summary tiling, and the breaker's state
is their `⊕`.

## Operator classification

A **streaming operator** holds nothing between pulls beyond its `ProducerBase` (its accumulated
`obsolete_guard`, the gate, and in debug builds the last output). Its output over a sub-domain of
its input is the output restricted to that sub-domain. A **pipeline breaker** holds state that
later pulls read, so its output over a morsel depends on the morsels before it.

| Operator | State between pulls | Breaker? | Merge law of the state | Partition axis |
|---|---|---|---|---|
| `MapResult`, `MapResultToConst`, `RecordWrap`, `SelectField`, `MakeRecord`, `MapDomain`, `Uncurry`, `PermuteRecordDomain`, `FlattenTupleDomain`, `VariantWrap`, `VariantProject`, `VariantIs`, `Filter`, `Restrict`, `UnionOperator` | none | no | `⊕` of outputs | any row range of the data input; the function operand of `MapResult` is read whole |
| `Zip` | none; rebuilds `rows_by_path` per pull | no | `⊕` | a row range shared by every arm, which holds only when the arms are aligned by position, so an arm that arrives out of order needs a per-key buffer and becomes a breaker (a symmetric join) |
| `Product` | none; re-renders the whole product per pull | no | `⊕` | outer rows; the inner side is read whole per outer row |
| `MapResultWithSource` | `last_nested_input` cache | no | `⊕` | key range; reads the source handle under its lock |
| `CheckedLookup` (paired form) | none | no | `⊕` | row range of the pairs |
| `CheckedLookup` (split form) | none, but emits nothing until the collection is terminal | blocking | n/a | the keys; the collection is the build side |
| `Memo` | `cached_tile`, `upstream_drained` | materializing, non-blocking | `⊕` (it merges deltas today) | the cached tile is immutable once emitted, so readers take snapshots |
| `Aggregate` + `ExtractAggregate` | one accumulator; terminal flag | blocking at the extract (`only_terminal: true`) | `Sum`: `+`; `Max`/`Min`: lattice join; `Drain`: unit; `Sole`: at most one, asserted. All commutative, so partials combine in any order | any row range; partials per worker |
| `MapAggregate` + `MapExtractAggregate` | `accumulators: HashMap<Vec<Value>, Tile>`, `emptied_keys` | materializing; a group is emitted terminal as soon as its key path is complete | per key, the kind's law; keys union | by key hash internally; by enclosing row path across a nest |
| `Converse` | `held: Vec<(Value, Value)>` | materializing where its groups are consumed as groups: the hash join's probe, or a result that is the groups. Where a fold follows it, the fold is the breaker and `Converse` is the gather that fold's phase one performs anyway; see the fusion note below | key union; a group's members union | by key hash internally. This is the hash join's build side (`planning/join.rs`: `converse(build ≫ key)`, probed through `MapResult`) and the group-by's bucketize step (`planning/groupby.rs`: `converse(c ≫ key) ≫ map(c)`) |
| `ExtractFinal` | `final_tile` once terminal | blocking | one value | none; it reports terminality of a stream |
| `IterateExtent` | `released: Predicate` | source cursor | interval-set union | row ranges handed out to workers |
| `FanOut` (`FanOutShared`) | per-slot release guards, their intersection, the cyclic snapshot | shared bookkeeping, no data | intersection of guards | n/a; one object per fan |
| `InductionStore` (`Engines` of `CommitEngine`) | seed, per-key `BTreeMap<Position, Value>` changelog, frontier, decided positions | sequential recurrence | none along positions; across `Engines` leaves the stores are independent | enclosing row path of a nested `Transact` |
| `InductionDriver`, `TransactDriver` | `DecodedSource`, `DriverWindow`, cursors | sequential | none | with their store |
| `CommitProducer` (`CommitEngine`) | as above, plus per-writer consumed counts | serialization point | `attempt` is OCC: validate the read set, allocate the next tick, write | writers are parallel up to `attempt` |
| `TransactWriter` | `emitted: Vec<InFlightProposal>`, cursors | per-site sequential | none | one writer per site; sites are independent until the engine |
| `AsOf` | `latched`, `seen` | materializing | union over trigger positions | trigger row range |
| `StoreDenseRead`, `StoreValueStream`, `StoreFinalRead` | a release cursor | no (reads a store render) | n/a | with their store |
| `SinkConsumer` | `data: HashMap<Value, Value>` | terminal | union | by key |

Three observations on the table:

- **Every aggregate kind is a commutative monoid or a join-semilattice** (`src/ccl/aggregate.rs`),
  so an `Aggregate` and a `MapAggregate` admit per-worker partials with a final combine, and the
  terminal flag of the combined accumulator is the conjunction of the inputs' completion. `Sole`
  asserts at most one element per key and the assertion holds across a combine as it does within
  one.
- **The hash join and the group-by share one build operator.** `Converse` is both the join's
  build side and the group-by's bucketize step. A partitioned `Converse` serves both, and the
  probe is an ordinary `MapResult` reading the conversed table as its function operand, re-read
  whole on every pull. A partitioned probe therefore needs `MapResult` to route each probe row to
  the partition its key hashes to, which is a change to the operator reading the table, not to
  the table's tile.
- **A fold after `Converse` makes `Converse` redundant.** A breaker is where the morsel's key
  changes, and `MapAggregate` changes it too: its local table is keyed by group, and folding
  `pos ↦ (key, value)` into it is the same gather `Converse` performs, with the members consumed
  instead of stored. The chain planning emits for a group-by with a fold,
  `converse(c ≫ key) ≫ map(c ≫ v) ≫ map_aggregate(kind)`, therefore exchanges twice and
  materializes the members in between; fused into one grouped fold over `pos ↦ (key, v)` it
  exchanges once, releases its input by position as it folds, reads `c` through one fan slot
  instead of two, and holds one accumulator per key and no member. The group-by recognizer
  (`planning/groupby.rs`) builds the first half of that chain, so the match is against a shape
  planning itself emits. `Converse` stays a breaker where the groups are the result or the hash
  join probes them.
- **The breakers that block are few.** `ExtractFinal`, `ExtractAggregate` (its
  `only_terminal: false` path is `todo!()`), and the split `CheckedLookup` wait for terminality.
  Everything else streams partial results, which is what the early-termination example in
  `semantics.md` relies on. A task scheduler can therefore start a downstream pipeline as soon as
  its breaker has emitted anything, rather than when the breaker closes.

## Where the pipelines fall out

A pipeline is a maximal chain of streaming operators from a delta source to the next breaker. The
delta sources are a source row range (`IterateExtent` over a `DataSourceDomain` or a
`UIntRange`), a `Memo` increment, a store render, and the output of a materializing breaker. The
operator graph (`operator_graph.rs`, the `post-conversion` pane) is the pipeline graph once the
breaker nodes are marked.

Three programs from `tests/programs`, read off the plans in `planning/join.rs` and
`planning/groupby.rs`:

- `groupby_rollup`: `sales ▷ iterate` → `Converse` (break) → `MapResult(c)` per group →
  `MapAggregate` (break) → `MapExtractAggregate` → sink. Two pipelines; the first ends in the
  bucketize build, the second runs per group and ends in the grouped sum.
- `join_then_groupby`'s join: `users ▷ iterate ≫ .id` → `Converse` (break, the build side);
  `orders ▷ iterate ≫ .user_id` → `MapResult(_, converse)` → `uncurry` →
  `flatten_domain` → `map_domain` → `Aggregate` (break) → `ExtractAggregate`. The probe
  pipeline runs per orders morsel once the build has emitted; the build pipeline runs per users
  morsel.
- A `mut` loop (`for i in xs: acc += f(i)`): `IterateExtent` → `InductionDriver` → body chain
  → `InductionStore` (break) → `StoreFinalRead`. One pipeline with a sequential breaker; the
  body chain between driver and store is the only parallelizable part, and only across the enclosing
  rows of a nested loop.

Task parallelism is then: run every pipeline whose delta source has something new, each on its
own worker, with the breakers as the synchronization points. The notification graph already says
which pipelines have work: a gate set on a breaker's consumer is a pipeline below it whose head has
a morsel to claim.

## Designs

### The pipeline plan

A pass over `OperatorGraph` after conversion cuts the graph into pipelines, and that plan is what
the scheduler runs. The pass classifies each node as a breaker or a streaming operator by its
kind, using the table under [Operator classification](#operator-classification), and emits one
pipeline per maximal streaming chain: its head (a source, a memo or a breaker's output), the
chain, and the breaker it ends in or the sink. A fan is not a node of the plan; each of its slots
is the head of the pipeline that reads it. The plan records, per pipeline, how its head offers
work (rows as they arrive, or a round at a time) and whether it is sequential (a recurrence:
driver, body chain and store), so the scheduler never inspects an operator.

The pass runs where `OperatorGraph` is built today, between conversion and the subscribe loop,
which is the one window where the walk is total (`design-operators.md`, "Operator identity and
the graph the inspector reads").

### The morsel

A morsel is a contiguous row range of the pipeline head, claimed from the head's morsel source as a
work package and named to the chain by a `Domain` interval guard over the range's key bounds at the
level the head cuts. A finite source cuts its range by advancing a cursor; a live source's claim
answers the rows past what it has already handed out, each arrival once; a materialized output's
head answers its rows. The released predicate governs what the source reclaims, not what the head
answers. The guard is read off the keys at the range's ends, which
needs the head's domain column sorted at that level. For a flat source it is a range of `UIntRange`
positions or of source keys. For a pipeline under a standing level (a per-group body, a nested
loop's rows) the range holds whole enclosing rows and its guard is a qualified predicate, because
`group_at`, `regroup_beneath` and `per_group` already cut tiles at row boundaries.

Size follows the literature (Leis et al., "Morsel-Driven Parallelism", SIGMOD 2014): a few
thousand to a hundred thousand rows, so one morsel's columns through a chain stay in L2, and small
enough that work stealing balances a skewed chain. `BLOCK_ROWS` is the inner blocking and stays as
it is; the morsel is the outer one.

Two ways to drive a pipeline on a morsel:

- **Pull with a projection guard.** The worker's chain tail calls `get(morsel_guard)`; each
  streaming producer restates the guard for its input (`through_shared_levels`, as release does)
  and pulls that. `IterateExtentProducer::get_impl` renders the extent minus the released
  predicate, intersected with the guard. This keeps the protocol as it is and needs every
  streaming `get_impl` to stop binding `_projection_guard`. A `Memo` in the chain answers a gated
  pull from its whole cache today (`MemoProducer::get_impl` asserts a universal guard on that
  path), so it would need to project its cache.
- **Push.** The source cuts morsels and calls the chain forward. Nothing in the producer trait
  supports it, and the release and completeness contracts are written for pull. Not recommended
  as the first step.

The pull form is the one the protocol already has a slot for, and it keeps the debug checks
(`completeness_violation`, the released-data check) per producer.

### Thread-confined chains, shared breakers

Each worker owns one subscription of the chain between two breakers: its own `Box<dyn
TileProducer>` instances, its own `ProducerBase` with its own `obsolete_guard`. The producers stay
`!Sync`; what crosses threads is tiles into and out of the breaker. The breaker is one object
behind a lock or a partitioned structure, and its `get` is called by the downstream pipeline's
worker, not by the upstream ones. The upstream workers deliver through a breaker-specific
`absorb(tile)` entry rather than through the downstream `get`.

**A chain per worker needs operators that several consumers can subscribe.** Op-conversion
moves each `Box<dyn TileOperator>` into its single consumer, and `TileOperator::subscribe` takes
`&mut self` and is called once by that consumer; only `FanOut` is built for several subscribers.
Instantiating a chain `N` times therefore needs one of two changes: the plan holds the streaming
operators of a pipeline as shared nodes and subscribes each once per worker, or the first
subscription's producer chain is cloned per worker. A streaming producer is cheap to clone, a
`ProducerBase` and boxed inputs, so the clone is the smaller change; a stateful producer is never
cloned, since it is the breaker. Either way the inspector's graph walk is unchanged, because it
reads operators, not producers.

This needs the operator-to-producer boundary to be crossable from several threads for
`subscribe` only, once at start, which is where `Rc<RefCell<dyn DataSourceDomainExtentImpl>>` in
`Extent` has to go. The handle is read by `MapResultWithSource` (`source.get(keys)`) and
`IterateExtent` (`get_elements`, `release`) and polled by the scheduler. `Arc<Mutex<dyn
DataSourceDomainExtentImpl + Send>>` suffices; the critical sections are a buffer read and a
predicate union.

### The scheduler

The scheduler is a data structure, not a thread: the dispatcher. `N` execution threads, one per
core, take work from it; nothing dispatches to them. Its content is, per pipeline, the pipeline's
morsel source, whether that source is exhausted, and how many claimed morsels are not acknowledged;
a worker asking for the next package is answered from the pipeline it is on while that pipeline's
source has one. A source answers `None` once it has no more rows. A pipeline is done when its source
is exhausted, no claimed morsel is outstanding, and every worker that claimed from it has left it,
handing in the state it holds for it. The worker that completes the pipeline runs the breaker's
combine and starts the pipelines waiting on it; a pipeline's source is built then, since a pipeline
behind a breaker reads what the breaker produced. A worker with nothing claimable parks until a
pipeline finishes. A pipeline with its dependencies is the event, and a partitioned merge is a pipeline over the
partitions. A package carries a guard and never a tile,
because the tile is what a worker produces by pulling its own chain, and data crosses between
operators only through `get`.

**A worker's loop.** Claim the next package, pull the package's pipeline at its guard, hand the
result to the breaker, release, acknowledge, repeat. A worker leaves its pipeline only when the
pipeline's source has no morsel to claim. The affinity is what keeps the chain's producers, the rows
it reads and the breaker partial it writes in one cache; moving between pipelines per morsel would
evict all three. When it moves, it prefers a pipeline whose breaker partial it already holds, then
one whose head's rows sit on its socket.

**Partial and whole offering.** A head offers work in one of two ways, by what it is:

- A source or a `Memo` offers rows as they arrive. The arrival's notification publishes its region
  to the source and the source's claim answers it; a memo's claim answers as its own input
  lands. Work is available before the head is done, which is what lets a pipeline run while its
  source is live. Such a claim has a state between exhausted and nothing yet (`Idle`), which
  `Exhausted`, final, does not name.
- A breaker that builds partitioned state, `Converse` and `MapAggregate`, offers nothing until a
  round completes. A round closes when the upstream pipeline's source has no morsel left for the
  round, every claimed morsel has been acknowledged, and every worker holding a partial of the round
  has handed it in: an acknowledgement says the rows are in a worker's partial, not in the shared
  list. The breaker then runs its merge as tasks on the same workers, appends the merged output to
  its output, and the downstream head's claim answers it. Until then the downstream head answers
  nothing, since a partition cannot be read while its finalize writes it.
- A blocking breaker (`ExtractFinal`, `ExtractAggregate`) offers its one value at terminal and
  nothing before.

A round is the unit at which a partitioned breaker's output advances. A later round over newly
arrived input merges into the existing tables with `⊕` and appends the increments to the output,
so the downstream pipeline sees a live source as a sequence of rounds and never a
rebuild. The natural round trigger is the scheduler lap that polls the sources, which is already
where delivery happens today; a shorter round trades finalize cost for freshness. Under a live
source a round reads the head's row count once when it starts and covers the rows up to it; a
row that arrives after that belongs to the next round, so a round closes even while the source
keeps delivering.

**Backpressure.** A morsel exists only when a worker claims it, so a source's rows stay in its own
buffer until a worker asks and no queue grows. A breaker's round produces its output without being
asked, so a round that outruns its readers waits to append to an output holding more than a few
morsels per worker.

**Notification.** A notification carries the region that changed ([the notification
contract](../src/interpreter/design-operators.md#the-notification-contract)). A pipeline's head
consumer is a `PipelineConsumer`, which hands the region to the pipeline's source
(`MorselSource::publish`) and moves the dispatcher's epoch. A source keeps a pending region, the
keys published and not yet claimed, and a yield predicate, the keys whose rows are ready to read,
which is not a tile's `domain_predicate`: keys arrive in any order, `Everything` published to a live
source means everything that has arrived, and a key that has not arrived is not claimable. A claim
cuts at most one morsel of `CAMBRA_MORSEL_ROWS` keys from it, lowest keys first, and removes them. A
region already claimed is dropped when it is published again, so an `Everything` that covers rows
already published, or a region that reaches the head along two paths of a diamond, publishes once.
The claim answers a morsel, `Idle` (nothing pending, the source open) or `Exhausted` (the source
closed, nothing pending). `Idle` leaves the pipeline unfinished and the worker parks; a publish or a
close wakes it, which takes the `WakeupQueue`'s place for a pooled pipeline. A sink is pulled by
whichever worker takes a package of a pipeline that ends in it, once per lap, as today.

The delivering thread, the thread that reads the source's input, runs the notification cascade,
and nothing in it pulls: the cascade ends in a union and an epoch move. A worker reads the epoch
before it looks for a morsel and parks only while the epoch is unchanged. The delivering thread
writes the rows, then publishes the region under the source's lock, then moves the epoch, so a
worker that misses the region in its claim read the epoch before the move, and its park returns at
once. The delivering thread holds no lock the cascade takes: the dispatcher's lock on what reached
a pipeline before it started, the source's state lock, the lock its ready-positions function reads,
and the lock that parks idle workers.

Only the first worker's chain carries the `PipelineConsumer`; every other chain's head consumer
ignores the region. The chain's notification path from the source to that consumer satisfies one
invariant: every consumer on it reports `region_driven`, and the path is acyclic. A closure or a
sink's consumer on the path ignores the region, and a fan-out's input consumer drops a second
notification, so the plan refuses a chain with a shared operator or a recurrence. A consumer that
only sends `Everything` loses nothing: a live source resolves it to every ready position less what
was claimed.

**Shared writes per morsel.** A claim on a finite source is one atomic update of its cursor, and the
dispatcher counts a morsel outstanding before the claim and back at the acknowledgement, two atomic
updates. No lock is taken on a finite source's morsel path. A live source's claim takes the lock of
its pending region, a predicate cut and difference. Idle workers park on a `Condvar` taken only when
nothing is claimable. A per-worker deque with stealing (`crossbeam-deque`) is the
extension for socket affinity, a conjecture until measured. A breaker's thread-local partial is
written by one worker; a merged table is written by the one worker or task that owns it; a head's
rows are written by its producer before they are claimable and never after. The other locks are at
the places the per-breaker models name: the release-guard union on a `Memo` or `FanOut`, and
`CommitEngine::attempt`.

### Per-breaker state models

**`Aggregate`.** Per-worker accumulator tile; combine on demand with `AggregateKind::accumulate`
over the partials, which is what `Tile::merge_part` already does for two `Aggregation` tiles
(`whole = true` folds the other's accumulator in). Terminal when every worker has released its
range and the source is complete. No lock on the hot path: a worker touches only its own partial,
and the partials are combined by the one worker that pulls the extract.

**`MapAggregate`.** Two-phase grouped aggregation (HyPer's and Umbra's design: Leis et al. 2014,
section 4, and Müller et al., "Cache-Efficient Aggregation: Hashing Is Sorting", SIGMOD 2015, for
the pre-aggregation argument):

1. *Thread-local pre-aggregation.* Each worker folds its morsel into a hash table of its own,
   keyed by the group path, with the 64-bit hash stored beside the key. A heavy hitter collapses
   into one entry per worker, so skew in the key distribution costs nothing in phase one.
2. *Merge of the local tables.* At the end of a round the worker tables are merged into one. The
   merge is a scan of every local table and a probe of the target per entry, combining states on
   a hit with the kind's merge law and inserting on a miss, so a group's cost is the number of
   workers that saw it. The first form is the sequential one: one worker merges the others' tables
   into its own. It is the right form while the local tables are small, which is the case
   pre-aggregation produces, and it needs no partitioning and no extra buffers. Two escalations
   when the merge becomes the bottleneck, neither of which changes phase one:
   - *Merge by hash range.* `P` merge tasks, each owning a range of the stored hash and each
     scanning every local table for the entries in its range. No buffers are written; the local
     tables are read `P` times. This parallelizes the merge for a few hundred thousand groups at
     the cost of repeated scans.
   - *Radix partitioning*, the form in Leis et al. 2014: a local table that outgrows cache is
     flushed into per-worker partition buffers by hash radix and started afresh, so a group gains
     one partial row per flush; the merge then builds one table per partition from every worker's
     buffer for it, each partition owned by one task. This is the form for high cardinality, where
     the local tables stop fitting cache, and the one that bounds a partition's size by splitting
     it on a further radix.
3. *Emit.* A group's accumulator is emitted terminal when the input's completion predicate names
   its path (`complete.contains_path`), as today. The output level is the `⊕` of the merged
   table's groups; nothing requires it sorted (`validate_tile` asks for key uniqueness within a
   group, not order), so the per-pull sort by path in `MapAggregateProducer::get_impl` goes. The
   output is kept sorted by key at the level the next pipeline cuts, so a key range spells a
   guard ([The morsel](#the-morsel)).

Each form merges the same local tables with the same merge law; they differ in who scans what.
The sequential merge is where to start, and the choice between the escalations is made from the
measured size of the local tables at the end of phase one, not fixed ahead.

The representation should change with the algorithm: typed key columns and accumulators as columns
indexed by a dense group id, instead of `HashMap<Vec<Value>, Tile>` with one `Tile` per group.
`AggregateKind::accumulate` already takes a column and a row range, so the kernel is there.

**`Converse` (the build).** The same two phases with a multimap in place of the accumulator:
each worker inverts its morsel into a thread-local map from key to its member positions, and the
round merges the local maps by concatenating member lists under one key, which is the output
tiling's `⊕`. The merge takes the same three forms as `MapAggregate`'s, sequential first, by hash
range or by radix partition when measured size calls for it. The output tile is the `⊕` of the
merged groups. The probe (`MapResult` with the table as its function operand) looks each probe
row up in the merged table, or under radix partitioning in the partition its hash names. Skew on
the build key, the hash join's classic failure, is handled by over-partitioning plus splitting
oversized partitions; the heavier remedy, replicating heavy-hitter build keys to every partition
so their probe rows need no routing (Rödiger et al., "Flow-Join", ICDE 2016, for the distributed
case), is worth keeping in view and not building first. Today's `Converse` re-emits its whole
table on every pull and the probe re-reads it whole; merged per round, each probe pipeline reads
a snapshot of the merged table.

A grouped `Converse` under a standing level (`Converse::new_at`) partitions by enclosing row
instead: each row's inversion is independent.

Phase one of both `MapAggregate` and `Converse` is a thread-local multimap or hash table that no
other thread reads, and phase two is one merging worker, or one owner per hash range or
partition, so neither needs a lock or a lock-free structure beyond the dispatcher. The one
shared object is the list of partials a round combines, appended once per worker per round.
`Converse` offers its output to the scheduler only when a round's finalize has run
([The scheduler](#the-scheduler)): a group whose members sit in several unmerged partials is not
readable, and merging on read would repeat the finalize per reader.

**`Memo`.** The cache becomes a versioned immutable snapshot: the breaker merges deltas into a
new version and swaps an `Arc<Tile>` (RCU). Readers clone the `Arc`; a reader holding an old
version sees what the monotonicity invariant says is still correct (`src/interpreter/CLAUDE.md`,
"Core invariant: known data inside a Tile is immutable"). Release is the intersection of the
readers' guards, taken under a short lock when a reader releases. `remove_guarded` then runs on
the next version, not on the one readers hold.

**`FanOut`.** The shared release-guard vector and the cyclic snapshot move behind the same kind
of lock-and-swap. The `forwarded` gate becomes an atomic. The re-entrancy flag
(`subscribing_inner`, `producer.take()` during a cyclic pull) is a single-thread protocol; under
the thread-confined-chain design the cyclic fan's input is pulled by exactly one worker, the one
driving the recurrence, so it stays single-threaded by construction.

**`CommitEngine`.** The engine is the serialization point and should stay one object. The hot
path is `attempt`: a read-set validation against each key's latest write and a tick allocation,
both short. Two shapes:

- A mutex around `attempt`, writers call it directly. Simple; contention is proportional to
  commit rate, not to body evaluation, because the body runs in the writer's pipeline before the
  proposal is formed.
- A committer task with an MPSC queue of proposals, acknowledging commits back to writers (group
  commit). Removes the lock from the writers' path at the cost of one hop of latency per commit.

OCC is unchanged by either: a proposal's `snapshot` is a decided position and `Stale` sends the
writer back around, as today. What changes is that several `TransactWriter` sites evaluate their
bodies concurrently. The induction store has one writer per store and is sequential along
positions; its parallelism is across the leaves of `Engines`, one task per enclosing row of a
nested `Transact`, which is embarrassingly parallel because no row reads another's store.

**`IterateExtent` and the source buffer.** The source's claim answers morsels as row ranges; a
worker's `IterateExtent` instance renders the range of the package it claimed. Release per worker is
the range's interval, unioned into the source's per-producer released predicate
(`ProducerReleases`), which `Predicate::Intervals` keeps exact for ranges released out of order.
`UIntStreamBuffer` keeps a `Vec<SmolStr>` with a `start_idx`; compaction after release stays a
prefix trim, so the buffer trims to the lowest unreleased position across workers, and a slow morsel
holds the prefix. That is the same retention rule the fan's intersection imposes today. The optional
ring makes the trim per segment ([Optional: a ring of segments at each
head](#optional-a-ring-of-segments-at-each-head)).

**Sinks.** One lock per sink around `data`; or, since a sink is pulled once per pass by one
worker, keep it thread-confined and leave it.

### Recurrences under the scheduler

A recurrence is sequential along its positions by definition: `acc_i = body(acc_{i-1}, item_i)`
reads the previous position's result, and the driver supplies it
(`design-operators.md`, "The driver"). The plan marks the pipeline from driver through body chain
to store as sequential, and the scheduler runs it on one worker. Its parallelism comes from four
places, in decreasing order of payoff:

1. **Compile the loop away when the body is a fold.** `acc += f(i)` and `acc = max(acc, f(i))`
   are a commutative monoid or a semilattice applied to a function of the item alone: an
   `Aggregate` over `map(f)`, fully parallel, with no driver. `mut_elim` emits a writer body for
   every loop today; recognizing an associative accumulator at the `Transact` is a planning
   rewrite that removes the sequential operator instead of parallelizing it. Where the program
   reads the accumulator at every position (a `StoreDenseRead`, a feed inside the loop), the same
   associativity gives a parallel prefix: partials per range, a scan over the partials for each
   range's starting value, and a second parallel pass for the per-position values.
2. **The leaves of `Engines`.** A nested `Transact` runs one recurrence per enclosing row, no
   row's store reads another's, and the nested drive already reseeds at every row boundary. Rows
   are tasks: cut the enclosing level by qualified predicate and run each row's positions
   sequentially on whichever worker takes it. This needs the driver's single `emitted_through`
   cursor to become one cursor per row it drives, as the `Engines` tree already has one engine
   per leaf.
3. **Hoist the item-only part of the body.** A body `h(acc, g(i))` has a part `g` that reads only
   the item; it is a map over the source and runs ahead of the driver in parallel, leaving `h` on
   the recurrence. This is a planner split of the writer body into `map(g)` composed before the
   `Transact`, with the driver feeding `(prev, g(i))`.
4. **Run the sequential remainder as one task.** The cost of a loop today is one position per
   scheduler lap, because the cyclic fan serves a snapshot taken before the traversal began
   (`design-operators.md`, "One position per pull"). A task that owns driver, body and store and
   iterates to quiescence, publishing the store's new render to its own fan's memo between
   positions, runs `n` positions in one task instead of `n` laps. That publish inverts `get`'s
   direction, which the operator doc notes as not done.

`TransactWriter` sites are independent until `CommitEngine::attempt`, so several writers run their
bodies concurrently and serialize only at the commit; the induction driver has one writer by
construction and no equivalent.

### Function operands

`MapResult` reads its function operand whole on every pull and releases it only on a universal
release of its data input (`MapResultProducer::release_impl`), because any key might be looked up
again. Two consequences for a chain that reads a memo this way, as the group-by's `map(c)` and the
hash join's probe both do:

- **The read becomes random access into the memo's cache.** A function operand's domain column
  kept sorted answers a key by binary search, and a position-keyed operand whose rows are
  contiguous answers it by offset, so a worker touches only the rows its lookups name rather than
  reading the operand whole. An operand keyed by arbitrary values with many lookups per pull
  needs an index from key to row, built as the cache grows.
- **The release can be finer when each key is looked up once.** Where the data input's keys at
  the applied level are unique, as they are when the data is `Converse`'s output and the
  operand's keys are its member positions, a row released on the data side names a function key
  that will never be looked up again, and `MapResult` can release that key of its operand. The
  tilings say whether the uniqueness holds; where they do not, the universal-only rule stays.
  Without this, a memo read as a function operand by one slot and streamed by another retains
  everything until the whole output is released, because the fan passes the memo the intersection
  of its slots' releases.

The grouped fold fusion under [Operator classification](#operator-classification) removes the
second reader for a group-by with a fold, which is the case the finer release matters most for;
the hash join's probe keeps it.

### Cache efficiency

- Morsels keep a chain's working set in L2; `BLOCK_ROWS` keeps a `ScalarProgram`'s slots in L1.
- The breakers should hold columns, not `Tile`s per group or `Vec<(Value, Value)>` pairs. The
  group-by state is the first place to do this, because its per-pull rebuild and sort is the
  obvious serial cost before threads.
- `Zip` and `Product` rebuild a path hash per pull. Under aligned morsels (both arms cut at the
  same row ranges, which the projection guard guarantees when both arms descend from one source
  range) the join is positional and the hash goes away. A `Zip` whose arms come from different
  sources is a join and belongs with `Converse`.
- Hash tables: open addressing with linear probing over a `u64` hash column, keys compared by
  typed column, not by `Value`. The literature's result (Balkesen et al., "Main-memory hash joins
  on multi-core CPUs", ICDE 2013; Schuh et al., "An experimental comparison of thirteen relational
  equi-joins", SIGMOD 2016) is that a well-built non-partitioned table is competitive with radix
  partitioning on one socket and loses across sockets, which is where the NUMA section lands.

### NUMA awareness

The design is the standard one (Leis et al. 2014; Li et al., "NUMA-Aware Algorithms: The Case of
Data Shuffling", CIDR 2013; Psaroudakis et al., "Scaling Up Concurrent Main-Memory Column-Store
Scans", VLDB 2015):

- Morsels carry the socket their buffer lives on. A source's buffer is filled by the thread that
  receives the data (the HTTP dispatcher, the stdio reader), so the buffer is local to that
  thread's socket by first touch; a NUMA-aware source allocates per-socket buffers and round-robins
  the fill, or pins a reader per socket.
- Each worker is pinned to a core and prefers morsels on its socket; it steals from other sockets
  only when its own queue is empty. Per-worker partials and partition buffers are allocated and
  first-written by their owner, so they are local by construction.
- Breaker partitions are assigned to sockets; phase two of a grouped aggregation and the probe of
  a hash join run partition tasks on the socket that owns the partition's buffers.
- Rust has no NUMA API in `std`. Pinning is `libc::sched_setaffinity` or the `core_affinity`
  crate; topology comes from `hwloc` or `/sys/devices/system/node`. macOS, the development
  platform here, exposes no NUMA topology, so the socket-awareness is measurable only under Linux
  on a multi-socket machine, and the design should degrade to a single socket without a branch.

### Skew

Four skews, each with its own remedy, so that none is answered by a global one:

1. **Key skew in a group-by.** Thread-local pre-aggregation absorbs it: a hot key is one entry per
   worker, combined once. This is the reason phase one exists.
2. **Key skew in a join's build side.** Over-partition (`P` several times the worker count) and
   split any partition over a size bound by a second radix before building. Heavy-hitter
   replication is the next step if measurement shows a single key dominating.
3. **Row skew across enclosing rows** (a nested loop whose rows differ in length, a group-by whose
   groups differ in size). Rows are tasks; small rows batch into one morsel, a large row is
   itself cut into morsels where its operator admits it (a grouped sum does; a sequential inner
   loop does not). Work stealing over the task queue balances the rest.
4. **Partition skew in a hash-partitioned exchange.** Partition count above worker count plus
   stealing of partition tasks. The Umbra follow-up on self-tuning scheduling (Wagner et al.,
   "Self-Tuning Query Scheduling for Analytical Workloads", SIGMOD 2021) is the reference for
   adapting morsel size to observed task durations rather than fixing it.

The retention cost of skew is separate from the throughput cost: a slow morsel holds the source
prefix below it (the interval-set release lets later morsels release around it, but a prefix-trim
buffer cannot reclaim past it). A deque of morsels handed out in order keeps the held prefix
short; stealing from the front of another worker's queue rather than the back keeps it shorter.

### Optional: a ring of segments at each head

Everything above runs with the heads as they are: a source buffer that trims a released prefix,
a memo cache and a breaker output held as owned tiles, and a head per pipeline answering row
ranges. The ring below is a refinement of the heads, not a precondition. It buys two things: a
tile handed to a worker that references rows instead of copying them, and reclamation at a fixed
granularity with no guard arithmetic on shared state. It changes `Tile`'s ownership of its
columns, which is why it is separate.

Under it every pipeline head holds its rows in a ring of segments: a source's buffer, a `Memo`'s
cache, a breaker's output. A segment is an immutable block of a fixed number of rows of one tile
level, columnar inside, appended at the ring's tail as the head materializes rows and freed from
the ring's oldest end as readers release. Within a segment the keys of the level the head cuts are
sorted, so a segment's key bounds spell its guard. `UIntStreamBuffer` is this structure for one
case: a `Vec` with a `start_idx` prefix trim; the ring generalizes it to every head.

**Data are pointers.** A tile handed to a worker references segments rather than copying rows:
a segment reference per level plus the guard that names the region, and a per-segment mask for
rows the reader has released or the level has deleted. The monotonicity invariant
(`src/interpreter/CLAUDE.md`, "Core invariant: known data inside a Tile is immutable") is what
makes the sharing sound: a segment once appended never changes, so any number of readers on any
thread hold it without coordination. `Tile` today owns its columns; a ring-backed tile holds
reference-counted segment handles and column views into them, which `ColumnView` already is for
a region of a column.

**Release is exact; reclamation is per segment.** A reader's release is recorded as a guard, as
the release contract requires, and the union over readers is what the head has been promised.
Reclamation runs at segment granularity: a segment is freed when every reader's released guard
covers it whole. Compaction walks from the oldest segment forward and stops at the first segment
not wholly released, which is the prefix trim `UIntStreamBuffer` performs today. A segment released
in part stays whole, and a segment released out of order stays until the prefix reaches it. The
retention this costs is bounded by one segment per slow reader, and the contract permits it: a
producer may retain released data, and may not return it, which the per-segment mask on the
handed-out view enforces without a copy. A finer reclaim, freeing rows inside a segment, would
need a mutable segment and would cost the sharing above; it is not done.

**A segment is a work package.** The head answers one package per segment, and the guard that
flows down the chain is read off the segment's key bounds, with no guard algebra at the claim.

**What the ring shares.** No predicate arithmetic runs on shared state. A projection pull reads the
ring's tail index (an acquire load; the list is append-only with one producer), the taken segment's
key bounds (written once when the segment is appended), the segment's rows (immutable) and, for a
head whose keys can stay open after the segment is appended, a per-segment completeness word the
producer advances and a worker reads with one atomic load. The subtraction of released data uses the
worker's own `obsolete_guard` in its thread-confined `ProducerBase`. Release crosses threads as a
per-reader "released through segment `k`" counter, one atomic store per morsel; the compaction walk
takes the minimum over readers, and a partial release inside a segment does not advance it. Where a
consumer needs the head's whole completeness statement as a `Predicate`, the producer builds it and
swaps an `Arc` (read-copy-update); readers load it without waiting. The locks that remain are the
release-guard union on a `Memo` or `FanOut` across its readers, taken once per morsel at release,
and `CommitEngine::attempt`.

### The contracts under threads

- **Monotonicity and `⊕`.** A worker's output over its morsel is a tile over a sub-domain
  disjoint from every other worker's; the breaker merges them with `Tile::merge`, whose
  `validate_tile` check rejects a repeated key. The debug assertion stays and becomes the check
  that morsels did not overlap.
- **Completeness.** A morsel pipeline's output states completeness for its own range only, as a
  qualified or interval predicate; the breaker unions them. The rule that a complete path never
  changes (`design-operators.md`, "The completeness contract") is per path, so it is unaffected by
  which worker produced the path.
- **Release.** A worker releases its range; the breaker forwards the union. A `FanOut`'s
  intersection runs across slots as now, each slot's guard now written by one worker.
- **Notification.** A breaker notifies its consumer when any partition changes. `Notified`
  becomes an atomic flag with the same mark/take protocol; the deferred `WakeupQueue` becomes the
  task queue, and "a consumer woken by an operator pulls it" becomes "a woken pipeline is
  scheduled". The gate's reason for existing, one wake per pull, carries over unchanged.
- **The debug checks.** `last_output` and `completeness_violation` are per producer and per
  worker. The quiescence check in `pull_laps` walks the producer tree from the root; under
  thread-confined chains it walks each worker's chain and the breakers once.

### Failures, probes and output order

- **A panic in a worker fails the run.** Today a panic unwinds the one thread and the process ends.
  A worker's panic is caught at the task boundary, recorded on the scheduler, and every other worker
  stops when it next asks the dispatcher for a package; the run then fails with that panic's
  message. The debug checks (`completeness_violation`, the released-data check, `validate_tile` on
  merge) run inside workers and fail the run the same way, so a morsel overlap or a withdrawn
  completion is reported rather than merged.
- **Probes.** `ProducerBase::probes` writes an observation on every `get` while the inspector is
  attached. Under workers each producer writes from its own thread, so the probe table is either
  one per worker, merged when a frame is published, or behind a lock taken only while a client is
  watching. The frame's shape is unchanged.
- **Output order.** The semantics is unordered bags, and `validate_tile` constrains key uniqueness
  within a group and not order, so a sink receives groups in whatever order the merge produced
  them, which differs between runs. The program test harness renders a finished tile in a
  canonical order (`tests/programs/common/mod.rs`), which is the comparison every test must go
  through; a test that compares a tile's physical order compares an accident.

## Durability

The durable state of a running program is the state of its pipeline breakers, each in the form
of a tile and a guard. No operator kind other than a breaker holds anything, so the checkpoint
points of a durable run are the same cut as the task boundaries of a parallel one.

### Release owns persistence

An operator that releases a region of its input upstream holds the only copy of what that region
contributed, and so owns its durable form. An operator that forwards releases one to one holds
nothing and persists nothing. This is the compaction requirement of
[semantics.md](operational-semantics/semantics.md#compaction) read as an obligation: an
operator's future output is a function of `compact(obsolete)` and its remaining input alone, so
`compact(obsolete)` is what has to survive a restart. The reload takeover
([program-evolution.md](../src/ccl/design/program-evolution.md#state-takeover)) already applies
the same criterion across a version swap, and the operators it carries over are the operators to
persist:

| Operator | Releases upstream | Durable form |
|---|---|---|
| streaming operators | the consumer's guard, restated | nothing |
| `Memo` | what it merges, as it merges it | `cached_tile` and `upstream_drained` |
| `Aggregate` | each delivery, as it folds it | the accumulator and its terminal flag |
| `MapAggregate` | each delivery | the accumulators by key path and `emptied_keys` |
| `Converse` | rows whose output paths are released | nothing beyond its input's; it re-renders from the input it still holds |
| `ExtractFinal` | everything, on its first terminal pull | `final_tile` |
| `InductionStore`, `CommitProducer` | the body's decisions and seeds it has stepped | the `CommitEngine`: seed, changelog, frontier, decided positions |
| `InductionDriver`, `TransactDriver` | the source prefix emitted or acked, and filtered rows read past | `emitted_through` or the current position, `source_released_through`, the completion statements accumulated from the source |
| `TransactWriter` | the driver rows it has decided | `emitted`, `committed_base`, `last_decided_pos` |
| `AsOf` | the store below its latest decided tick; trigger rows latched | `latched` and `seen` |
| `IterateExtent` | nothing of its own; it records what consumers released | `released`, which is the source's resume point |
| `SinkConsumer` | what it has delivered | `data` |

A memo-only design fails this table at every folding row. `Aggregate` and the drivers release
what no memo holds, so a memo in front of each of them that never releases is the only way to
make a memo the durable form, and that is unbounded retention.

### The durable form is a tile and a guard

Every summary above is a tile of a summary tiling: a `DataFunction` cache, a `Tile::Aggregation`,
a `Tile::Store`, and for a cursor a `Predicate`. Each summary tiling has `⊕`, so an incremental
checkpoint is the `⊕`-delta since the previous one: the changelog entries and frontier advance
for a store, the merged-and-not-released delta for a memo, the accumulator value for a fold. The
guard is the operator's accumulated `obsolete_guard` toward its input, which is where its input
resumes. `IterateExtent`'s released predicate is that guard for a source, and the source replays
from its complement. The inspector already serializes tiles for the wire
(`src/inspector_model/design.md`, "A node on the wire"), so an encoding exists.

The store is a write-ahead log already: `CommitEngine::attempt` and `step` append a position's
writes per key and advance the frontier, and `gc_released_prefix` is log compaction. Persisting
it is appending the same records, and recovering it is replaying them into an empty engine.

### A release must mean durably consumed

One rule in today's runtime conflicts with durability. The induction driver releases an emitted
position back to the source before the store decides it (`design-operators.md`, "The driver"),
and the transact driver's ack is the intersection of the body's and the writer's releases
(`design-operators.md`, "The commit operator (`interpreter/commit_operator.rs`)"). A source that
has reclaimed a position on that release cannot replay it after a crash between the release and
the decision's checkpoint. Under durability a release of a source position follows the checkpoint
of the decision that consumed it, as an offset commit follows processing. The change is confined
to the two drivers' release paths; the body chain's eager release (`design-operators.md`, "The
commit operator (`interpreter/commit_operator.rs`)") is between the memo and the driver and does
not reach the source.

### Checkpoint consistency

Single-threaded, a checkpoint between two `Scheduler::deliver` calls is consistent by
construction: tiles only grow, release is the only shrink, and between laps every breaker's state
is a function of the released frontiers below it. Under morsel execution the checkpoint is a
barrier at morsel boundaries, aligned at each breaker: a breaker checkpoints once every upstream
worker has delivered the morsels before the barrier and none after it, which is the aligned
checkpoint of Carbone et al., "Lightweight Asynchronous Snapshots for Distributed Dataflows",
2015, with the pipeline cut supplying the alignment points. The breakers are the only operators
with state, so nothing between two barriers needs to be captured.

Recovery rebuilds the operator graph, seeds each breaker from its durable form through the same
path a reload uses to hand an operator its predecessor's state, and resumes every source from the
complement of its released predicate. A request on an HTTP source that was taken in and not
decided is lost, which the client's retry covers; a committed effect is not repeated, because the
store's frontier is durable before the sink's release is.

## An incremental path

Ordered so that each step is measurable on its own and none is undone by the next.

1. **Make tiles cross threads.** Landed: every shared handle is `Arc<Mutex<_>>`,
   `Arc<RwLock<_>>` or an atomic, and the operator traits carry `Send` and `Sync`
   (`src/interpreter/design-parallel.md`, "Thread-safe handles"). No behavior change.
2. **Honor the projection guard in streaming producers.** Every `_projection_guard` becomes a
   restated pull of the input. Test: pulling a chain at two disjoint guards and merging equals
   pulling it at the universal guard. This is the morsel mechanism, exercised single-threaded.
   Landed for every tile operator (`src/interpreter/design-operators.md`, "Projection guards"),
   and the morsel pipeline cuts a finite `IterateExtent` range and a collection `Constant`
   (`src/interpreter/design-parallel.md`, "Projection guards"). The `UIntStreamBuffer` is not
   yet cut by interval.
3. **The pipeline plan and a chain per worker.** The pass over `OperatorGraph` that classifies
   breakers and emits pipelines, and the cloning of a streaming producer chain per worker,
   exercised single-threaded with two chains over disjoint guards into one breaker.
4. **Fix the group-by state representation** (columns and dense group ids in `MapAggregate`,
   no per-pull sort). Measurable on `groupby_rollup` scaled up, with the flamegraph tooling in
   `~/.claude/projects/-Users-leon-dev-cambra/viz/`. This is the serial cost that would otherwise
   be parallelized as-is.
5. **A worker pool and the first breaker.** The pool, the dispatcher over a range source's cursor,
   and the sink as the breaker landed for `[x + 1 for x in xs]` over a literal list, and `Aggregate`
   over it as the first folding breaker, with a partial per worker combined at the end
   (`src/interpreter/design-parallel.md`, "A fold as the breaker"). Next: the same over a source,
   which is where the chain's scaling with no exchange is measured.
6. **The grouped fold.** The planning rewrite that fuses `converse(c ≫ key) ≫ map(c ≫ v) ≫
   map_aggregate(kind)` into one fold over `pos ↦ (key, v)`, with thread-local tables and the
   sequential merge. This is the group-by's parallel form and removes the second memo reader.
7. **`Converse` for the hash join**, with the same local maps and merge, the probe reading the
   merged table as a function operand with the finer release, and the hash-range and radix merges
   added to both breakers when measurement calls for them.
8. **Task parallelism across pipelines.** Independent sinks and `Let` bindings, then the leaves of
   `Engines` for nested loops, then `TransactWriter` sites with the engine behind a mutex, then the
   fold recognition that removes the induction driver where the body allows it.
9. **NUMA placement**, once there is a Linux multi-socket box to measure on.
10. **The ring of segments**, optional and last, when measurement shows tile copies at the heads or
    guard arithmetic on release as a cost worth the change to `Tile`'s ownership.

## Open questions

- Whether a round that keeps per-worker partials across rounds can use the pipeline's leave as its
  hand-in, which finishes a pipeline once every worker has left it, or needs a hand-in per round
  while the pipeline stays open.
- Whether to keep `get` as the only data path once a breaker has an `absorb` entry for upstream
  workers, or to admit a push edge into the protocol. The CLAUDE.md invariant is that data crosses
  only as tiles through `get`; a breaker's absorb takes a tile and returns nothing, which keeps
  the first half and not the second.
- How a reload (`semantics.md`, "4. Reload") takes over a breaker's partitioned state: the takeover
  rules are stated over one tile per term, and a partitioned breaker's tile is the `⊕` of its
  partitions, which is a tile. The partial states of in-flight workers at the swap are the part
  with no rule yet.
- Whether `Zip` over arms from one source range can be made positional in the type, so the
  per-pull path hash is gone for every zip and not only under aligned morsels.
