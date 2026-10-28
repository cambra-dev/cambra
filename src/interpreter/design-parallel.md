# Parallel execution: what is implemented

This document records the parallel execution the interpreter has, one section per piece as it
lands. The target design is [docs/parallel-execution.md](../../docs/parallel-execution.md); where
the two differ, this document states what the code does and the target states where it is going.

## Thread-safe handles

Every handle the interpreter shares between operators, consumers and the scheduler is
thread-safe, and the four traits a worker thread would hold objects of carry the bounds a thread
needs: `TileOperator` is `Send + Sync`, since one operator is subscribed by every chain that reads
it; `TileProducer`, `Consumer` and `DataSourceDomainExtentImpl` are `Send`, since a producer and
its consumers belong to one thread at a time. Nothing runs on a second thread yet; the bounds are
what lets a later change move a producer chain to one.

The handle types are defined once, in [`sync.rs`](sync.rs):

| Handle | Was | Is |
|---|---|---|
| a shared cell (`FanOutShared`, a consumer, a source, a probe table, a sink consumer) | `Rc<RefCell<T>>` | `Arc<Mutex<T>>` |
| an operator held by a fan or a `CycleSlot` | `Rc<RefCell<Box<dyn TileOperator>>>` | `Arc<RwLock<_>>` |
| a weak registration (a source's consumers) | `Weak<RefCell<T>>` | `std::sync::Weak<Mutex<T>>` |
| a flag (`Notified`) or a counter (a fan slot's index) | `Rc<Cell<_>>` | `Arc<AtomicBool>`, `Arc<AtomicUsize>` |
| a counter a test double shares | `Rc<Cell<_>>` | `Arc<SyncCell<_>>`, a test-only type |
| a shared operator (`FanOut`) or name (a probe's producer) | `Rc<T>` | `Arc<T>` |

A lock is taken with `LockNow::lock_now`, which is `Mutex::try_lock` with a panic on contention.
In a single-threaded run that is the `RefCell` contract: a borrow that overlaps another panics
instead of deadlocking, so a re-entrant lock is reported the way a re-entrant borrow was. A site
that two threads will contend on takes a blocking lock when that site exists, not before.
`forwarding_consumer`'s re-entry test keeps its shape: `try_lock_now` answers `None` where
`try_borrow_mut` answered an error.

A `Mutex` has no shared borrow, so two shared borrows of one cell that overlapped under `RefCell`
are a re-entrant lock here. Two walks nest reads around a recurrence's cycle:

- The operator graph walk reads a fan's input operator and recurses into it, and the cycle
  brings it back to the same fan while the first read is held. The operator cells a fan and a
  `CycleSlot` hold are therefore an `RwLock`, whose `read_now` nests and whose `write_now`,
  taken by `subscribe` and by the one-time wiring, panics on any held guard. An `RwLock` needs
  `Sync` contents, which an operator is.
- The producer walk (`TileProducer::visit_input_producers`) enters a fan's producer from one
  slot and, around the cycle, reaches a recurrence slot of the same fan. `FanOutShared` holds a
  producer, which is `Send` and not `Sync`, so it stays a `Mutex`, and the recurrence slot's
  `try_lock_now` answers `None` where `try_borrow` nested: that slot reports no input. The
  producer it would report is the one the walk is already inside, reached from the reader slot,
  so `each_producer` visits every producer as before; `ignored_inputs` examines that producer's
  gate from the reader slot and not from the recurrence slot. `commit_operator.rs`'s
  `a_recurrence_slot_reached_around_its_cycle_reports_no_input` pins the rule.

A nested lock on any other cell is reported by `lock_now`'s panic, which names the cell's type.

A test source's element type is a CCL `Type`, which holds inference state behind `Rc` and so is
not `Send`. `TestDataSource` holds a `TestSourceType` instead, built from the `Type` a test passes
(a base type, a tuple or a record of them) and rebuilt into one when inference registers the
source.

## The morsel prototype

`src/interpreter/parallel.rs` runs a program's `main` output on a pool of worker threads when
`CAMBRA_NUM_LOCAL_THREADS` is above one. The binary reads the configuration after it has compiled
the program, runs the pool if the plan admits the program, and prints the result as a pull of `main`
prints it; a program the plan refuses, or a run with `--inspect` or `--control`, says so on stderr
and runs on the scheduler loop as before. `CAMBRA_MORSEL_ROWS` sets the rows per morsel, 4096 unless
set.

### The plan

`plan_main` cuts the operator graph the way [docs/parallel-execution.md, "The pipeline
plan"](../../docs/parallel-execution.md#the-pipeline-plan) describes, for one chain shape: an
`IterateExtent`, then any number of `MapResult`s whose function operand is a `Constant`, into the
breaker, which is the `main` sink or an `ExtractAggregate` over an `Aggregate` into it ([A fold as
the breaker](#a-fold-as-the-breaker)). Every operator in the chain is streaming, so a worker's chain
holds no state between morsels. A graph with any other node on the path or a sink besides `main` is
refused with the reason, which the binary prints. `plan_main` checks the shape of the chain only.
Which rows the source enumerates is the source's to say ([The dispatcher](#the-dispatcher)), so
`run_main` refuses a source over anything but a finite range `[0, n)` when it asks the source for
morsels. The programs this admits are `[x + 1 for x in xs]` over a literal list and a `sum`, `max`
or `min` of it; a source over a data-source domain is the next shape.

### The pool

`run_main` subscribes the chain under the breaker once per worker, so each worker owns one producer
chain, as [docs/parallel-execution.md, "Thread-confined chains, shared
breakers"](../../docs/parallel-execution.md#thread-confined-chains-shared-breakers) asks. An
operator is subscribed as many times as there are workers; nothing is cloned, because the chain is a
tree of boxed operators each subscription walks afresh. A worker holds its chains in a vector
indexed by `PipelineId`, which holds one entry, since the plan holds one pipeline. The threads are
`std::thread::scope` threads over `run_worker`, and the calling thread waits for the scope. For a
collection the breaker's state is the collector, the sink: a `Mutex<Tile>` the workers merge into
with `Tile::merge`, which calls the collection complete once every worker has returned, every
package acknowledged after its rows were merged. For a fold it is the partials of [A fold as the
breaker](#a-fold-as-the-breaker).

The chains are lent to the workers and dropped after the scope, one at a time on the thread that
subscribed them: a producer's drop detaches its probe with a lock that must not find the probe table
held by another worker's `get`.

A worker releases a morsel on its chain only after the breaker holds the morsel's rows: the
collector's tile, or the worker's own partial for a fold. That release is the breaker's
acknowledgement ([docs/parallel-execution.md, "A release must mean durably
consumed"](../../docs/parallel-execution.md#a-release-must-mean-durably-consumed)), and it is also
what keeps the chain's producers consistent with the completeness contract: a producer's next pull
states a different interval complete, which it may do only where the previous one was released.

The cells workers contend on take a blocking lock, `LockNow::lock_wait`: the probe table's
`observe_named`, which every `get` calls, the collector, and the fold's partials. Every other cell
keeps the panic-on-contention lock, because a worker's chain is its own and never shares a cell with
another worker's; the probe table's readers are on the thread that runs the inspector, which a
parallel run refuses.

### The dispatcher

The dispatcher is the scheduler of [docs/parallel-execution.md, "The
scheduler"](../../docs/parallel-execution.md#the-scheduler) for the pipelines of a plan. A plan
gives it one `PipelineSpec` per pipeline: the pipelines it follows, a function that builds its
`MorselSource`, and an optional `finalize`. A `WorkPackage` is a `PipelineId` and the guard naming
one morsel. The morsel path takes no lock. The only lock parks idle workers. The calls:

- `next(prefer)` claims a morsel of `CAMBRA_MORSEL_ROWS` rows from a started pipeline, trying
  `prefer` first, and answers `Next::Package`. It answers `Next::Wait` when no started pipeline has
  a morsel and some pipeline has not finished, and `Next::Done` once every pipeline has finished or
  the dispatcher failed.
- `ack` counts a claimed morsel back, once the breaker holds its rows and the morsel is released.
- `serve(worker)` is one worker's loop over those calls ([A worker's turn](#a-workers-turn)).
- `fail` makes every `next` answer `Done` from then on.

A worker pulls its morsel from the source; no structure holds morsels between the two. This is the
dispatch of Leis et al. 2014, where the dispatcher carves the next range off a pipeline's input when
a worker asks.

**The source cuts its own rows.** `TileOperator::morsel_source` answers an `Arc<dyn MorselSource>`
for an operator that is a source and `None` for every other. `MorselSource::claim(rows)` answers a
`Claim`: `Morsel` with the guard of the next morsel of at most `rows` rows, `Idle` (nothing is
claimable now and a row may still arrive) or `Exhausted`, which is final. `IterateExtent` over a
finite range `[0, n)` answers a `RangeSource`: one `AtomicU64` cursor that `fetch_update` advances,
so each position is in exactly one claimed morsel whichever threads claim, and the cursor never
passes `n`. The update is acquire-release, because a claim that answers `Exhausted` must happen
after every claim that answered a morsel (the finish rule below relies on it). A finite source holds
every row from the start, so its `publish` and `close` do nothing and it never answers `Idle`. The
data a worker reads under a guard comes from its own chain. `IterateExtent`'s producer knows nothing
of the dispatcher. `run_main` finds the source by walking the chain's inputs to the first operator
that answers one, and refuses a chain with none or with several.

**A pipeline finishes when three counts agree.** Its source has answered `Exhausted`, no claimed
morsel is outstanding, and no worker is still attached. A claim counts itself outstanding before it
asks the source and takes the count back when the source answers `Idle` or `Exhausted`. A worker
attaches when it receives its first package of the pipeline and leaves once the source is exhausted,
handing in what it holds for the pipeline through `PoolWorker::leave`. The worker that completes the
pipeline, by its last `ack`, its `Exhausted` claim or its leaving, runs `finalize` and finishes it.
Nothing is outstanding and no worker is attached only after every claim that answered a morsel was
acknowledged: a claim attaches before it acknowledges.

**A pipeline starts when the pipelines it follows have finished.** Finishing a pipeline decrements
the wait count of each pipeline behind it, and the one that reaches zero builds its source. The
source is built then because a pipeline behind a breaker reads what the breaker produced. A plan
lists a pipeline after every pipeline it follows, so the dependencies form no cycle, and the
dispatcher refuses a plan that does not.

**Idle workers park.** A worker that finds nothing claimable reads the dispatcher's epoch before it
looks, and parks until the epoch moves. The epoch moves when a pipeline's source is exhausted, when
a pipeline finishes and when the dispatcher fails. The thread that moves it takes the idle lock
before it notifies, so a worker between its check and its wait is not missed. Exhaustion moves it
because a worker parked while attached has to wake and leave before the pipeline can finish.

**A live source's arrivals are published to it.** `LiveSource` is the source of keys that receive
rows, in any order, and any totally ordered values: positions, integers, strings. It holds the keys
published and not claimed (`pending`) and the keys claimed, as predicates under one lock, and reads
the source's yield predicate, `ready`, the region of keys whose rows are ready to read. For a
data-source domain the yield predicate is also what `IterateExtent` states complete, so a key
outside it may arrive later and none arrives inside it. `publish` names a region of `ready`, and
`Everything` names `ready` itself, not every key of the source's extent. A `Keys` region lies within
`ready`, since the rows and their keys in the yield predicate are visible before the region is
published, and `publish` asserts it in release builds as well. The source unites the region, less
what was claimed, into `pending`, so a region published twice is claimed once and a key that is not
ready is never claimed. Nothing is published after `close`. `claim(rows)` asks the source for the
first `rows` keys of `pending` in key order, and claims the keys from the first to the last that
`pending` names, so a morsel holds exactly those keys when they are sparse. A `pending` region that
names no key the source holds is dropped from `pending`, since a yield predicate may cover keys that
never arrive. The claim answers `Idle` while the source is open and nothing is pending, and
`Exhausted` once `close` was called and `pending` is empty. One lock orders every claim, so an
`Exhausted` follows every morsel.

**The source cuts its keys.** `DataSourceDomainExtentImpl::cuts_morsels` says a source lists its
keys and its extent's keys are totally ordered, and `first_keys_in(region, rows)` answers the first
`rows` keys of a region in key order. The source answers it because it holds its keys and the pool
does not. Both default to a source that does not cut (`false`, and unreachable):
`IterateExtent::morsel_source` answers `None` for it, `source_of` finds no source, and the program
stays on the compiling thread. `TestDataSource` cuts when its key extent is `Int`, `UInt` or
`String`. `LiveSource::claim` calls `first_keys_in` with the `LiveSource` state lock held and takes
the data source's `Mutex` inside it, which is the lock order. Each claim does work in proportion to
the keys the source holds under both locks (`TestDataSource::first_keys_in` sorts every key it
holds), and `claimed` grows with the keys claimed: known costs, not addressed.
`elements_in(producer, region)` is `get_elements` cut to a region, and an `IterateExtent` over a
data-source domain asks for it at a morsel, so the source renders only the morsel's keys.

`Dispatcher::publish(pipeline, region)` and `close(pipeline)` reach a pipeline's source and move the
epoch. A pipeline that has not started has no source yet, so they keep the region and the close in
the pipeline's `Early` state, which `start` hands to the source it builds. The delivering thread
holds no lock these calls take: `Early`'s, the `LiveSource` state lock, the one `ready` reads, and
`idle`.
`start` holds that state's lock until the source is set, so a publish either lands in it first or
finds the source set.

A `PipelineHandle` is a dispatcher and a pipeline, and `PipelineConsumer` is a `region_driven`
consumer over it: the consumer subscribed at the head of the first worker's chain. A notification
that reaches it publishes its region. Every other worker's chain subscribes a closure, and the
source registers every chain's consumer, so one arrival notifies all of them. Only the first chain
publishes, and the source takes a region it has already claimed once: the duplicates that remain are
an `Everything` that covers published rows and a region that reaches the head along two paths of a
diamond. The path from the source to the `PipelineConsumer` is region-driven and acyclic
([Region-carrying notifications](#region-carrying-notifications)), which `plan_main` guarantees by
admitting only `MapResult`s over a `Constant` function operand and refusing a shared node
(`FanOutSlot`) or a deferred edge. `run_pipeline` is the body of `run_main` for a plan with one
pipeline. Once the chains are subscribed it publishes `Everything` to the source, so the rows the
source holds when the pool starts are claimable, as no notification names them. Without a delivery
it then closes the source, since no row arrives later. it takes the breaker and the source, and with
a `DeliveringThread` runs that closure on the calling thread while the workers run. The closure
receives the handle and the scheduler the chains were subscribed with, writes rows to the source and
calls `Scheduler::check_for_notifications`, which polls the source (`check_for_new_data`) and
notifies the consumers registered for it with `Everything`. The head's `PipelineConsumer` publishes
that, and the live source resolves it to the keys that are ready. A region would add precision and
not correctness, and the scheduler's serial path is the same call. `run_pipeline` closes the source
when the closure returns, which can publish nothing more.

**Rows are written before their region is published, and the region before the epoch moves.** The
delivering thread writes the rows under their store's lock, publishes the region under the source's
lock, then moves the epoch. A worker that claims a morsel locks the source after the publish, and
the lock it takes on the store when it pulls follows the delivering thread's, so the rows are
visible to it. A worker reads the epoch before it claims. One that found `Idle` read the epoch
before the publish moved it, so its park returns at once, and one that read it after found the
region.

**A worker stays on its pipeline.** `next` tries the pipeline the worker last claimed from first,
which keeps its chain, the rows it reads and its partial in one cache. A worker moves when that
pipeline has no morsel.

A worker that panics fails the dispatcher on its way out (`FailOnUnwind`): `next` answers `Done`
from then on, parked workers wake, the other workers stop claiming, and the scope re-raises the
panic.

#### A worker's turn

`Dispatcher::serve` runs one worker until every pipeline has finished. Each pass leaves the
pipelines whose source is exhausted, asks `next`, and runs the package through `PoolWorker::work`,
which pulls the chain, hands the tile to the breaker and releases the morsel, before `ack`. The
plan's one pipeline is served by `MainWorker`; a test double records what it ran and left.

### Region-carrying notifications

`Consumer::notify(arrived: &Projection)` names the region of the notifying producer's outermost
keys that changed ([the notification contract](design-operators.md#the-notification-contract)). The
region is the work a pipeline's dispatcher hands out, so it must reach the pipeline's head intact
or widened, never narrowed or lost.

- **Default.** An operator keeps an input's keys, forwarding its region unchanged, when its row of
  the projection table pulls that input at the projection, and widens every other input, which
  forwards `Everything`. [The notification-contract
  table](design-operators.md#the-notification-contract) says which, per operator and input. There
  are four ways to keep keys: `consumer_keeping_keys_if` (or the bare consumer, for an operator
  with one input), `subscribe_forwarding_keeping_keys` and `subscribe_forwarding_keeping_keys_if`
  (an operator with several inputs behind one gate), and `forwarding_consumer_keeping_keys`
  (`Memo`). A region reaches a consumer unwidened only through operators that keep keys.
- **No gate for a region-driven consumer.** `Consumer::region_driven` says a consumer acts on the
  region and never pulls. `shared_consumer` gives such a consumer a gate of `Notified::Always`, so
  no region waits behind one: no pull is owed to its notifications, and a closed gate would pass one
  and hold the rest. A consumer that pulls keeps no region, since its pull reads whatever arrived.
  The wrappers (`widening`, `Gated`, `FlaggingConsumer`, `Forwarding`) report the flag of the
  consumer they wrap, and `Gated` asserts that a region-driven consumer's gate is `Always`.
  `forwarding_consumer` waits for the cell of a region-driven consumer with `lock_wait`, where the
  drop or the deferral that serves a consumer that pulls would lose the region.
- **The invariant.** Every consumer between the notifying producer and a region-driven consumer
  reports `region_driven`, and the notification graph between them is acyclic. A closure and a
  sink's consumer ignore the region, and a fan-out's input consumer drops a second notification, so
  a chain with one between its source and the pool's head loses regions. The pool's plan refuses
  such a chain. Acyclicity makes the wait of `forwarding_consumer` safe: a cascade does not reach
  one cell twice, and a cell downstream of a region-driven consumer is itself region-driven. It
  orders the cells' locks only. The thread that notifies holds no lock the cascade takes (the
  dispatcher's lock on what reached a pipeline before it started, the `LiveSource` state lock, the
  lock its yield-predicate function reads, and the lock that parks idle workers).
- **Closures.** A closure consumer ignores the region, and the scheduler's drains send `Everything`.

### A pool owns its pipeline's release record

A data source keeps one release record per producer reading it and reclaims only what every record
releases. A pool breaks both halves of that: the `main` producer `compile_program` subscribes
registers a record that releases nothing, and each worker's chain registers a record that releases
only the morsels that worker ran. Either holds the agreement at nothing.

The pool takes the pipeline's records as its own in two steps. The program's `main` producer goes
once the plan and the source are accepted, which retires its record. It sits in the program's
output, or with a `LiveProgram` that moved it out to drive it, which `LiveProgram::run_main_on_pool`
hands to `run_main_holding`; the pool asserts in debug builds that it dropped one. A program the
pool refuses keeps the producer and stays on the compiling thread. `run_pipeline` then subscribes
every worker's chain inside `Scheduler::with_pooled_release_records`, and a source producer
subscribed there (`IterateExtent`'s, and `MapResultWithSource`'s, which releases into the source as
well) holds its record under `pool#n/<operator id>`, with `n` counting runs. The workers' producers
of one operator share a record, which accumulates the union of what they released. The records of
different operators are intersected by the source, so a key is reclaimed once every operator that
reads the source has released it, as it is in a serial run.

The pool retires its records itself. A producer whose record is under a pool's name does not retire
it when it drops, so the first chain to drop does not take the others' record with it.
`with_pooled_release_records` returns the records with the chains, and they retire when they drop,
after the chains do and on a panic in `subscribe` or in a worker.

A source's lock is taken with `lock_wait` where a worker and the delivering thread can both reach
it: `get_yield_predicate`, `get_elements`, `get`, `get_fields`, `release`, `check_for_new_data`,
`element_extent` (including the checks of an extent's type and of a predicate over it) and `get_id`
(extent equality and display). `retire_producer` keeps `try_lock_now`, because a chain is dropped on
the calling thread after its workers returned, and a drop that finds the source locked is a bug.
Subscription keeps `lock_now`, because it runs before a worker exists. Locks nest in one order: the
`LiveSource` state lock, then the data source's `Mutex`. The delivering thread holds neither when
it notifies.

A `MapResultWithSource` producer retires its own release record when it drops, as an `IterateExtent`
producer does: a record that outlives its producer holds the source's reclaim at wherever the
producer stopped.

### Projection guards

A worker names its morsel with `Domain(Intervals([first, last]))` at the chain's tail. Every tile
operator restates the guard for its inputs, and the per-operator rules are the "Projection"
tables of [design-operators.md](design-operators.md#projection-guards). The morsel pipeline relies
on three of them:

- `IterateExtentProducer` over a `UIntRange` renders the intersection of its remaining range with
  the admitted interval, so a morsel costs the morsel's size. Every other extent renders whole and
  is cut after; a data-source domain is the next to cut.
- `ConstantProducer` holding a collection hands out the admitted keys.
- `MapResultProducer` passes a `Domain` guard to its function operand too, and forwards a
  `Domain` release to it, when the data is one level whose values are its keys and the operand is a
  collection applied at each value: the keys a morsel looks the operand up at are the morsel's own
  keys, and they are looked up no more once the morsel is released. The operand's keys outside the
  morsel are not cloned away: `Constant` removes and compacts them per pull, which is linear in the
  table; a slice by interval over a sorted domain is the next step. This is the finer
  function-operand release [docs/parallel-execution.md, "Function
  operands"](../../docs/parallel-execution.md#function-operands) names, for the one case the
  correlation makes checkable.

### A fold as the breaker

A `main` output that is an `ExtractAggregate` over an `Aggregate` is a fold, and the plan reads the
fold off those two nodes: `Breaker::Fold` carries the `AggregateKind` and the accumulator's tiling
from the `Aggregate`'s own. The chain the workers subscribe is the fold's input, reached through
`TileOperator::pool_input`, which `ExtractAggregate` answers with its fold and `Aggregate` with its
input; every other operator answers `None`, which `run_main` never consults, since `plan_main`
admits only those two above the chain.

The fold is the per-worker state the target design gives `Aggregate` ([docs/parallel-execution.md,
"Per-breaker state models"](../../docs/parallel-execution.md#per-breaker-state-models)): each worker
seeds a partial with `AggregateKind::initial_accumulator`, folds every morsel's values into it with
`accumulate`, the call `AggregateProducer` makes, and hands the partial in once, after its last
morsel, so nothing is shared on the morsel path. Once every worker has returned, the partials are
combined into the seed with the same `accumulate`, which is the combine `Tile::merge` performs on
two aggregation tiles, and `extract` turns the total into the scalar `ExtractAggregate` emits. The
partials are bare accumulators: the terminal flag `AggregateProducer` sets on its aggregation tile
is never built on the pool, and the scalar `extract` answers is terminal by holding a value, which
it does once every worker has returned. Every `AggregateKind` combines in any order, and its seed is
a unit of the combine, so a worker that takes no package hands in a partial that changes nothing,
and the partials are pushed in whichever order the workers finish.

### Tests

`tests/it/parallel.rs`: two chains pulled at disjoint guards and merged equal the whole pull, and
each chain's next pull past its released interval answers the rest; four workers over a thousand
rows with a morsel size that does not divide them equal the whole pull and are terminal, for the
collection and for `sum`, `max` and `min` over it, and the folds again over three rows, where a
worker takes no package; one worker equals the whole pull; the plan reads a fold off the extract; a
group-by is refused. The three producers each have a unit test of the interval they hand out and the
release that follows (`map.rs`, `scalar.rs`, `iterate.rs`). `iterate.rs` also tests `RangeSource`:
its morsels are disjoint and end in `Exhausted`, a morsel holds at least one row, and a finite range
from zero is the one extent that answers a source. The dispatcher's unit tests in `parallel.rs`:
morsels are disjoint and cover the range; an empty range finishes its pipeline when first asked; a
claimed morsel keeps its pipeline open until it is acknowledged; a failed dispatcher hands out
nothing; a panicking worker stops the others claiming; a pipeline waits for the one it follows, an
empty pipeline starts the ones behind it, and a pipeline behind two starts after both; a dependency
on a later pipeline is refused; a worker stays on its pipeline; eight workers over a chain of two
pipelines claim every position of each once, start each pipeline once and leave each pipeline they
claimed from; an idle worker parks while another holds a morsel and wakes when the pipeline
finishes; a failure wakes a parked worker. `source_of` finds the one source, and refuses a chain
with none and a chain with two.

`LiveSource` has unit tests in `iterate.rs`: it claims only what was published, a region published
twice is claimed once, `Everything` is cut to the positions that are ready, a region that becomes
ready ahead of an earlier one is claimed first, the earlier one is not claimable until it is ready,
and an `Everything` sent while it is missing claims nothing from it, a region outside `ready` is
refused, a region with open bounds names the positions it contains, and a closed source is exhausted
after its published rows. The dispatcher has five more: a live pipeline waits for an arrival and
finishes once closed and drained, a parked worker wakes on a publish and on a close, regions
published before the pipeline starts are united and kept for its source, and an `Everything`
published before it starts is resolved when the source is built.

**A live source through the pool, end to end** (`parallel_live_tests.rs`). `LiveRows` is a test
operator over a store of rows with a `LiveSource`. The delivering thread writes a chunk of rows,
adds its positions to the source's yield predicate and notifies every chain's consumer with the
chunk's positions (`Everything` for an empty chunk). It returns when the chunks are delivered, and
`run_pipeline` closes the source. Workers claim the arrivals and run `LiveRows → MapResult(negate)`
into the collecting breaker through `run_pipeline`. Each run checks that the breaker holds every row
once with its mapped value, as the serial answer computes it; that the source's producer saw every
position pulled once and released once, a release only after the claim and the pull, and reclaimed
every row; and that only the first chain's consumer is region-driven. The chunks arrive in bursts,
one row at a time, empty, and in lockstep, where every worker is parked (`Dispatcher::parked`)
before each arrival and the next waits until the workers have pulled the rows so far, so that a
parked worker has to be woken by the publish and not by the close. They also arrive out of order,
last to first and shuffled with fixed seeds. Before the delivering thread delivers the chunk at
position 0 after another, it waits for the workers to pull every row that arrived, and fails with
that cause after thirty seconds, so the workers must consume rows of a later chunk while an earlier
one is missing. Each pattern runs on one, two, four and eight workers, and the in-order and out-of-
order patterns each repeat two hundred times in one test. A test in which the first worker never
serves checks that its chain's notifications still reach the pipeline. A run that does not finish
within a minute fails as a lost wake-up, and a panic in a worker fails as that panic. Removing the
epoch move from `Dispatcher::publish`, the `Notified::Always` gate of a region-driven consumer, the
subtraction of claimed positions in `LiveSource::publish`, or the cut to the yield predicate (a row
count instead) each fail a test.

## Not yet implemented

A breaker other than the sink and a fold into `main`, a source over a data-source domain, a pipeline
plan over more than one pipeline (the dispatcher runs dependent pipelines, and `plan_main` cuts
one), the operator that serves a breaker's output to the pipeline behind it, a way to hand a morsel
back, and the sink pulls the scheduler loop queues. A live source exists as `LiveSource`, and
nothing outside tests publishes to it: `IterateExtent` over a data-source domain answers no
`morsel_source`. Before a source over a data-source domain lands, the `main` producer
`compile_program` subscribes has to be owned by the pool: it registers a release record of `False`
with the source, and a source agrees to reclaim only what every record releases, so an idle producer
pins the source. Every program the plan refuses runs on the thread that compiled it, through
`Scheduler::check_for_notifications` and the sink pulls it queues.
