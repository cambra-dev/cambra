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

`plan` cuts the operator graph the way [docs/parallel-execution.md, "The pipeline
plan"](../../docs/parallel-execution.md#the-pipeline-plan) describes, into pipelines listed upstream
first. A pipeline's chain is any number of `MapResult`s and `MapResultToConst`s whose operand is a
`Constant`, `MapResultWithSource`s over an `IterateExtent`, and `Restrict`s, `VariantWrap`s and
`VariantProject`s, from its head to its breaker ([Widening the plan](#widening-the-plan)). A head is an
`IterateExtent` over a source (`Head::Source`) or a `FanOutSlot` over a `Memo` (`Head::Breaker`).
The plan cuts at the slot: the pipeline that feeds the `Memo` ends in `Breaker::Materialize`, is
planned once per `Memo`, and the pipeline behind it streams from it. The last pipeline ends in the
breaker of the `main` sink, which is the sink or an `ExtractAggregate` over an `Aggregate` into it
([A fold as the breaker](#a-fold-as-the-breaker)). `classify` is the one table of what the plan does
with an operator kind (streaming, source, cut, or refuse with the kind named), and its last arm
refuses, so an operator the plan has not considered is refused. A test classifies every kind the
corpus of compiled programs holds. Every operator in a chain is streaming, so a worker's chain holds
no state between morsels. A graph with any other node on the path, a build side, or a sink besides
`main` is refused with the reason, which the binary prints. Which rows a source enumerates is the
source's to say ([The dispatcher](#the-dispatcher)), so `run_main` refuses a source over anything
but a finite range `[0, n)` when it asks the source for morsels. The programs this admits are `[x +
1 for x in xs]` over a literal list and a `sum`, `max` or `min` of it, and the same behind a value
that the program names and reads (`xs = [...]; [a * 2 for a in xs]`); a source over a data-source
domain is the next shape.

`run_main_delivering` reads everything it can refuse before it takes the program: the plan, each
pipeline's source with the graph cut at the slots (`check_pipelines`), and that a delivery reaches
one source. It then drops the `main` producer, cuts the graph, and runs. `cut` takes the chain that
feeds each `Memo` out of the graph, leaving a `Detached`, and replaces every slot with a
`BreakerOutput` over the output that chain will fill. The graph is the pool's from there: the cut
leaves it unusable to the scheduler loop, which is why nothing the pool can refuse follows it.
The fan-out keeps the serial chain the program subscribed when it compiled: `FanOutShared::producer`
is the serial `Memo`'s producer, and the operator map holds the fan-out for as long as the program,
so dropping the `main` producer and the slots does not end that subscription, and its release
records would pin the sources beneath it. `cut` calls `TileOperator::drop_serial_subscription` at
the slot it takes the chain behind, which drops the producer. `LiveProgram` clears the branch's
operator map once the pool has taken the program, so a reload compiles afresh and cannot offer the
fan-out, whose `Memo` now holds a `Detached`, to the next version; a pool takes a program for good.
A test runs a shared value over a source, with delivery that waits for each chunk to be released and
with delivery that does not, and asserts that no record and no key is left with the source.

The plan reads the graph through `TileOperator::visit_inputs` and cuts it through
`TileOperator::visit_inputs_mut`, which states an operator's owned inputs as boxes the visitor may
replace. It visits what `visit_inputs` states as a value edge, in the same order, and the shared
input of a `FanOutSlot` under the fan-out's write lock, so a visitor at a slot reaches the `Memo`
and below it the chain of the pipeline before the breaker. An edge wired after the operator was
built, which a store's writers are, is not reached: a plan that cuts a graph refuses a program with
such an edge. The method is required, as `visit_inputs` is: an operator states its inputs, and a
leaf states that it holds none. A test compiles a corpus of programs, each of which has to compile,
and checks at every operator the mutable visitor reaches that the two visitors state the same
inputs. It lists the kinds that state an input and that the corpus reaches through any edge,
deferred ones included, and the kinds it does not reach, which the commit stores, their drivers and
writers, `AsOf` and a few others are, and it fails when a kind moves between the lists. A visitor
that replaces the input of a slot changes what the slot states.

### The pool

`run_main` subscribes the chain under the breaker once per worker, so each worker owns one producer
chain, as [docs/parallel-execution.md, "Thread-confined chains, shared
breakers"](../../docs/parallel-execution.md#thread-confined-chains-shared-breakers) asks. An
operator is subscribed as many times as there are workers; nothing is cloned, because the chain is a
tree of boxed operators each subscription walks afresh. A worker holds its chains in a vector
indexed by `PipelineId`, with one entry per pipeline of the run (`run_pipelines`; `run_pipeline` is
the run of one). The threads are `std::thread::scope` threads over `run_worker`, and the calling
thread waits for the scope. For a
collection the breaker's state is the collector, the sink: a `Mutex<Tile>` the workers merge into
with `Tile::merge`, which calls the collection complete once every worker has returned, every
package acknowledged after its rows were merged. For a fold it is the partials of [A fold as the
breaker](#a-fold-as-the-breaker). For a breaker that materializes (`PoolBreaker::Materialize`) it is
a `Materialized` ([A breaker's output](#a-breakers-output)): a worker merges the morsel into it with
`absorb`, publishes the morsel's guard as the region, and then releases the morsel on its chain, so
the release is at the merge. The pipeline's `finalize` completes the output, before the pipelines
that stream from it are closed.

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
- `step(worker, state)` is one pass of a worker's turn, `serve(worker)` repeats it and parks, and
  `serve_until_wait(worker, state)` repeats it and returns where `serve` would park ([A worker's
  turn](#a-workers-turn)).
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
pipeline, by its last `ack`, its `Exhausted` claim, its `Idle` claim that ends after another
claim found the source exhausted, or its leaving, runs `finalize` and finishes it. Each of those
events is followed by a finish attempt, because the last of them is the one that makes the counts
agree, and a claim that ends `Idle` is the last when another worker's `Exhausted` claim saw it
outstanding. Nothing is outstanding and no worker is attached only after every claim that answered
a morsel was acknowledged: a claim attaches before it acknowledges.

**A pipeline starts when the pipelines it follows have finished.** Finishing a pipeline decrements
the wait count of each pipeline behind it, and the one that reaches zero builds its source. The
source is built then because a pipeline behind a breaker reads what the breaker produced. A plan
lists a pipeline after every pipeline it follows, so the dependencies form no cycle, and the
dispatcher refuses a plan that does not.

**A pipeline can read a pipeline's output as it is produced.** `PipelineSpec::streams_from` lists
the pipelines whose output a pipeline reads, which is the pipeline behind a breaker that
materializes. The pipeline has one more wait than it has `after` entries, and a worker's publish to
it releases that wait once (`Job::stream_released`): the pipeline starts at the first region
published to it, before the pipeline it streams from has finished, when nothing else is awaited. A
pipeline in `streams_from` that finishes decrements `streams_open` of each pipeline in its
`stream_readers`, and the last of them closes the pipeline and releases the wait if no publish did,
after its `finalize`. The pipeline behind a breaker that published nothing therefore starts at the
upstream's finish with its source closed, and finishes without a morsel. The closing goes before the
release, which builds that pipeline closed; the order is not otherwise observable at the source. A
region published while the pipeline waits on a build side or on a pipeline in `after` is kept in
`Early` and handed to the source when it is built, so the dependencies compose: the pipeline starts
when both are satisfied, and no published region is lost. A pipeline lists each earlier pipeline
once, in `after` or in `streams_from`, which the dispatcher checks.

The publish that releases a pipeline's last wait builds its source on the publishing thread, which
is an upstream worker inside `work` or `leave` or a consumer's `notify`. The source builder runs
inside that publish: it takes no lock the publisher may hold and does not re-enter the breaker's
notification.

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
([Region-carrying notifications](#region-carrying-notifications)), which `plan` guarantees by
admitting only `MapResult`s over a `Constant` function operand, cutting a pipeline at a `FanOutSlot`
and refusing a deferred edge. `run_pipeline` is the body of `run_main` for a plan with one
pipeline, and `run_pipelines` runs several. Once the chains are subscribed it publishes `Everything`
to the source, so the rows the source holds when the pool starts are claimable, as no notification
names them. Without a delivery it then closes the source, since no row arrives later. A
`DeliveringThread` is a closure that runs on the calling thread while the workers run. The closure
receives the handle and the scheduler the chains were subscribed with, writes rows to the source and
calls `Scheduler::check_for_notifications`, which polls the source (`check_for_new_data`) and
notifies the consumers registered for it with `Everything`. The head's `PipelineConsumer` publishes
that, and the live source resolves it to the keys that are ready. A region would add precision and
not correctness, and the scheduler's serial path is the same call. `run_pipeline` closes the source
when the closure returns, which can publish nothing more.

A `PipelineRun` names its head: a data source (`Head::Source`) or a breaker's output
(`Head::Breaker`). `run_pipelines` seeds and closes every pipeline with a data-source head when the
run starts, whatever the pipeline waits on, since the dispatcher keeps the region in `Early` until
the pipeline starts; the first of them is closed after its delivery instead when there is one.
Every chain is subscribed the same way, once per worker, and the first worker's chain of a pipeline
carries the consumer that reaches the dispatcher: the `PipelineConsumer` of a delivery or of a
breaker's output. `BreakerOutput` registers one consumer per reading operator, its first
subscription's, so the breaker's `publish` notifies a `PipelineConsumer` from the thread that
absorbed a morsel and the other workers' consumers are never notified. Debug builds assert that a
chain reaches no operator of another pipeline, that a data-source pipeline streams from none, and
that a breaker-headed pipeline reads the output of a pipeline it streams from. When the chains are
dropped, the breakers' readers retire.

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

`Dispatcher::step` is one pass of a worker's turn. It leaves the pipelines whose source is
exhausted, asks `next`, and runs the package through `PoolWorker::work`, which pulls the chain,
hands the tile to the breaker and releases the morsel, before `ack`. It answers `Step::Ran` after a
morsel, `Step::Wait` when `next` did, and `Step::Done` when `next` did, and it answers `Done` before
it leaves anything once the dispatcher has failed. What a worker holds between passes is a
`ServeState`: the pipelines it is attached to and the pipeline it ran last.
`Dispatcher::serve_state` mints one, naming its dispatcher by a per-dispatcher id, and a debug build
asserts on every step that the state is this dispatcher's and that one thread uses it.

`Dispatcher::serve` runs one worker until every pipeline has finished: it reads the epoch, takes a
step, and parks on the epoch it read when the step answers `Wait`. `serve_until_wait` takes steps
until one answers `Done`, or `Wait` with the epoch where it was before the step, and returns
`Settled::Wait` or `Settled::Done`. It parks nowhere: the caller delivers the arrivals that end the
wait and calls again with the same state. A step that answers `Wait` after the epoch moved is not a
wait. The claim that finds a source exhausted moves the epoch, and the worker's next step leaves the
pipeline and finishes it. Both entry points run `step`, so they give one worker the same packages
and `leave` calls.

The `Wait` of `serve_until_wait` is a wait only when every `publish`, `close`, `ack` and finish of
the dispatcher's pipelines happens on the thread that calls it, because the caller has no epoch to
park on. The inline driver is that caller; the threaded path, where other threads publish, is
`serve`. `FailOnUnwind` lives in `run_worker`, so the inline driver handles a panic in a worker
itself. The plan's pipelines are served by `MainWorker`; a test double records what it ran and left.

A parked worker leaves when the epoch has moved or the dispatcher has failed. `fail` moves the
epoch through `wake_idle`, and the `failed` check matters only when that move is lost. In the lib's
unit tests and in the `it` tests, which build the lib with `test-helpers`, a park gives up after
thirty seconds and panics with the epoch it waited on, so a lost wake-up fails a test with that
message and does not hang the suite.

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
  absorption into the notification in progress that serves a consumer that pulls would lose the region.
- **The invariant.** Every consumer between the notifying producer and a region-driven consumer
  reports `region_driven`, and the notification graph between them is acyclic. A closure and a
  sink's consumer ignore the region, and a fan-out's input consumer drops a second notification, so
  a chain with one between its source and the pool's head loses regions. The pool's plan refuses
  such a chain. Acyclicity makes the wait of `forwarding_consumer` safe: a cascade does not reach
  one cell twice, and a cell downstream of a region-driven consumer is itself region-driven. It
  orders the cells' locks only. The thread that notifies holds no lock the cascade takes (the
  dispatcher's lock on what reached a pipeline before it started, the `LiveSource` state lock, the
  lock its yield-predicate function reads, and the lock that parks idle workers).
- **Pipeline boundary.** The invariant holds per pipeline: a pipeline behind a breaker has its own
  leaf consumer ([Pipeline boundaries](../../docs/parallel-execution.md#pipeline-boundaries)).
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
input; every other operator answers `None`, which `run_main` never consults, since `plan`
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

### A breaker's output

A breaker that materializes keeps its rows in a `Materialized` (`breaker.rs`), one shared value per
breaker. The workers of the pipeline before it `absorb` a morsel's rows and `publish` the morsel's
region; the pipelines behind it read through `BreakerOutput` (`tile_operators/breaker_output.rs`),
an operator with no inputs whose producers answer from `Materialized::snapshot` and whose
`morsel_source` is a `LiveSource` over it. The consumer graph of the pipeline behind therefore ends
at `BreakerOutput`: no operator of the pipeline before the breaker is its input, and the only
notification that crosses is the region `publish` raises. Both types are crate-private.

**What is kept.** The state is the merged morsels (`tile`), the keys that are ready (`ready`), the
keys every reader released and that were removed (`reclaimed`), whether the breaker completed, and
the readers' records, in one `RwLock`, so a key is ready only once its rows are in the tile, and a
release reads and writes the records and the rows together. `absorb` merges and extends `ready`
under one write lock; the rows and their keys become visible together. A morsel states its whole
region complete, which `absorb` asserts, so a key the region names and the morsel lacks is decided
absent. A key the pipeline before the breaker filtered out is therefore in the region and has no
row, `first_keys` answers the keys that have rows, and `LiveSource` marks a region that names none
as claimed. `snapshot` answers the rows of a guard and states complete the keys that are ready, or
every key once the breaker completed: the statement is the output's own, because a morsel's
statement says nothing of keys of other morsels.

**Order.** A worker `absorb`s, then `publish`es with no lock held, and the dispatcher moves its
epoch inside the publish after the source took the region (`Dispatcher::publish`). The rows are
visible before the region is published, and the region before the epoch moves, so a worker that
finds no morsel in its claim has read the epoch before the move and its park returns at once. A
region published before its rows fails the assertion in `Materialized::publish` and in
`LiveSource::publish`. The locks, outermost first, are the consumer list (`downstream`), the gated
cell of a consumer's chain, a pipeline's early state, a `LiveSource`'s state and the output's
`state`. `publish` and `add_downstream` hold the consumer list while they notify, so a consumer's
`notify` takes no lock that precedes the consumer list in that order and does not register a
consumer; it reaches the locks that follow it, the pipeline's early state and the source's state,
which is why they come after it. A source builder that runs inside a notification takes none of the
locks above it: it only builds the source. `claim` reads `state` through `first_keys` while it holds
its source's state, and `release` takes `state` alone. A consumer registered after rows were
absorbed hears of them at once: `add_downstream` holds the consumer list from reading `ready` to
pushing the consumer, so a publish before the push is inside what it read and a publish after it
reaches the consumer.

**Readers.** A reading operator is one reader across the workers of a pool, and its record is the
union of the morsels they released: the workers subscribe one `BreakerOutput` once each, and
`Scheduler::pooled_release_record_for` gives their subscriptions one name, which `register_reader`
maps to one record. The rows leave when every reader has released them: the intersection of the
records, restricted to the keys that are ready and less what already left. A reader releases only
rows that are ready, except a release of everything, which says the reader is done with the output
and does not reclaim keys absorbed afterwards: those are held until a later release names them.
Every reader registers before a row leaves, which `register_reader` asserts, because a reader that
registered after a release would find reclaimed keys stated complete and absent. The output holds
one consumer per reading operator, the first subscription's, so a publish notifies operators and not
workers. A build side (`whole`) is read whole by every worker, so each worker is a reader of its own
and the rows leave once every worker has released them all; its producers ignore a release that
names part of it. A producer subscribed outside a pool is a reader of its own. A producer that is
dropped without releasing does not pin rows past the end of the run: the run calls `retire_readers`
once its chains are gone, which drops the records and the rows.

**Known costs.** A `snapshot` clones the held tile before it cuts it, `first_keys` reads every held
key, and a release compacts the held tile, so each costs in proportion to the rows the output holds
and not to the rows it answers or releases. Dense columns, which a collection of positions would
hold as a range, are the step that removes this; it is not designed here.

### The inline driver

`PooledRun` serves a program's pipelines from the thread that drives the scheduler loop: one worker,
no threads. `PooledRun::start` plans the program, reads everything it can refuse, drops the `main`
producer, cuts the graph and subscribes the pipelines once; it seeds the pipelines over a data
source. A range ends by exhaustion. A source whose rows arrive from outside stays open, and a lap
closes it once its yield predicate covers every key (`MorselSource::is_complete`), publishing what
it holds first: its `main` is not terminal until then, and a fold over it answers only then. `lap` runs
`Dispatcher::serve_until_wait` with the worker's state: every morsel the arrivals made claimable,
and nothing parks, because the loop delivers the arrivals. A lap answers `Ran` when a morsel ran,
`Idle` when nothing was claimable, and `Done` when every pipeline has finished. The lap arms
`FailOnUnwind`, which `run_worker` does for a pool's threads, so a panic in a chain fails the
dispatcher and is raised in the loop.
A lap of a dispatcher that failed elsewhere answers `Failed`. The worker's fold partials belong to the
run, so a panic in a chain leaves them as they were.

The pipeline that ends in `main` ends in `Materialize` as the others do, and `main` is read through
a `BreakerOutput` subscribed on the driver thread, with the branch's consumer, so the breaker's
`publish` wakes the loop as a serial `main` would. The reader registers before the first lap, so no
row leaves before it has read. A fold ends in the partials of the one worker, and the pipeline's
`finalize` combines them into a `FoldedResult` that a small producer answers `main` from until it is
released. The loop is deliver, lap, `Scheduler::pull_sinks`, pull the mains: `pull_sinks` is the
last block of `deliver`, split out because a sink behind a breaker is woken by the lap and not by
the delivery. `CAMBRA_DISPATCH=inline` turns the driver on in `src/main.rs` for a run without
`--inspect` or `--control`; a refused program stays on the plain loop, and
`LiveProgram::start_inline` swaps the branch's `main` producer for the pool's.

Every sink of the program is an output of the inline driver ([Sinks and the HTTP
path](#sinks-and-the-http-path)); the threaded `run_main` runs `main` only and refuses a program
that writes a sink.

`PooledRun::serve_pass` is the loop's part of a pass: without a run it does nothing, so a program
the pool refused passes as the plain loop passes it, sink pulls queued for the next delivery.

### The differential suite

`CAMBRA_DISPATCH_CHECK=1` makes `run_program_with_ctx`, which every `compilation_pipeline` test runs
a program through, run the program again through `PooledRun` on a fresh context and compare the
answer with the serial one (`sort_tile_collections`, after `compact`), after which the run must
answer `Lap::Done`. A panic in the dispatched run is re-raised naming the program's hash. A program
that does not compile on a bare context, because it reads a source or sink its test registered, is
counted as skipped and is not checked: the dispatched context does not rebuild a test's sources, so
a program over a source has no differential check yet. A program the plan refuses is counted with
its reason; a program it admits is checked.

The admitted programs are pinned in `tests/it/compilation_pipeline/dispatch_admitted.txt`, a hash
of the program's files and the name of the test that ran it on each line, separated by a tab. An
admitted program that is not listed fails, and so does a listed one that is refused, so a plan
change that admits more or less is a diff in that file. `CAMBRA_DISPATCH_BLESS=1` rewrites the file
from the programs a run admits, sorted, and so is run over the whole corpus.
`CAMBRA_DISPATCH_REPORT=<file>` appends one line per program, written at once so that tests on
several threads do not interleave: outcome, reason and hash. `./ci.sh dispatch` runs the suite
with a report and compares the admitted hashes with the pin, which fails for a pinned program that
no test runs any more, and runs in CI's test job. The suite is off by default and is not in
`./ci.sh fast`: it runs the corpus twice more.

Each admitted program runs through the inline driver at one morsel size per row and at three rows
(`CAMBRA_MORSEL_ROWS` sets a single size), so a program over a few rows runs as many morsels, and
through the threaded pool on four workers with two-row morsels when the threaded plan admits it.
The threaded answers are compared with the rows in key order, since the workers merge morsels as
they finish.

A completed collection is complete at every level. A morsel states an inner level correctly, and
`Tile::merge` drops the statement as covered by the outer level when the breaker absorbs the morsel
(`drop_covered_completion`). The dispatched tile then means the same as the serial one under the
closure rule and differs in representation, and `Tile ==` compares representations; the first run
of the suite found it in a list of records holding collections, and `[[1, 2], [3, 4]]`, a list of
pairs holding lists and a value read back through a second pipeline show it too.
`Materialized::snapshot` therefore states every level beneath the outermost complete once the
breaker has completed, after the merges and the cut to the projection, keeping what the outermost
states for a read of part of the keys. The threaded collector states every level complete when its
workers have returned (`Tile::complete_every_level`, `Tile::complete_inner_levels`). A breaker that
has not completed states none of them. A collection a variant holds is a value of the variant's
column and has no level of its own, so it is not affected.

### Sinks and the HTTP path

`plan_inline` plans every `Sink` node of the graph as an output: `main`, and each sink such as the
reply channel of `http_serve`, ends a pipeline of its own. `plan` keeps `main` as the one output for
the threaded pool. A sink's pipeline ends in a collection breaker (`Breaker::Collect`); only `main`
may end in a fold, since a sink dispatches a collection. A `Memo` is still read by one slot, so two
sinks over one memo are refused.

`PooledRun::start` takes each sink's serial producer out of its `SinkConsumer`, which drops the
subscription that registered a release record with the sources, cuts the sink's chain at its memos
as `main`'s, and installs in the consumer a `BreakerOutput` producer over the sink pipeline's output
(`SinkConsumer::install_producer`). The `BreakerOutput` is subscribed on the driver thread with the
sink consumer, so the breaker's `publish` requests a pull on the scheduler's sink queue as a serial
change would, and `PooledRun::serve_pass` drains it after the lap. The pull is the consumer's own:
it reads the rows that arrived, hands them to the `DataSink`, and releases them, so a row reaches
the sink once. A program with no `main` has no `main` producer (`PooledRun::take_main` answers
`None`).

The HTTP source is cut by `UIntStreamBuffer::first_keys_in` (see `design-http-server.md`, "Cutting
morsels"). `check_for_new_data` runs on the driver thread, in the delivery, and its notification
reaches the dispatcher as a region that resolves to the keys ready and not yet claimed. The reply
sink (`HttpServerSharedState::process`) stays on the driver thread behind its `BreakerOutput`: it
removes each answered request from its `pending` map and needs a reply per request exactly once, in
any order, with the request index as the key. Decision: the order of replies is the order the sink's
pulls see rows, which is the arrival order within a lap and the lap order across laps; no client
observes more, because each reply goes to its own connection. Decision: a sink reads its breaker
while the breaker is incomplete, since an HTTP route never completes; a pull hands over the rows
published so far and the terminal tile arrives when the source ends.

Compiling a program pulls each sink once, which hands it the rows its sources held and releases them
under the serial producer's record. `PooledRun::start` reads, before it drops the serial producers,
what each output's producers released of each source (`DataSourceDomainExtentImpl::released_by`,
over the names the output's subscription registered, `CompiledOutput::source_producers`), and starts
the pool's record of each source operator in that output's pipelines there. Each output inherits
from its own chain, not from the intersection across outputs, and the pipelines behind a `Memo`
inherit from the output that reads it. Without this the pool's records start at nothing, and a
source whose agreement another reader holds back offers the rows again
(`rows_held_at_compile_reach_the_sink_once`). The precondition is that the pool's operators are the
operators whose serial producers registered the names, which holds because the pool cuts the same
graph the program compiled.

The differential suite compiles each program in a context with no sources or sinks registered, so
the programs that read one are skipped, and the HTTP programs are compared by the scenarios above.

### Widening the plan

The plan admits an operator by kind (`classify`), on one rule: a pull of the operator at a guard
is answered from its input's answer at the same guard, and the keys it answers are among its
input's. An operator joins in a change of its own with a `classify` arm, a plan test over a program
that reaches it, a mutation check that removes the arm, and the differential suite's zero
differences with the pin updated.

`VariantWrap`, `VariantProject` and `Restrict` share `Streaming::Unary`. `VariantWrap` answers its
input's keys, `VariantProject` answers only the keys whose rows carry its tag, and `Restrict`
answers the keys whose predicate holds. Three candidates are not admitted.

- `Constant` as a source. A list literal compiles to an `IterateExtent` and a `Constant` operand
  that a `MapResult` applies, so a collection-valued `Constant` is never a chain's data input in
  the corpus, and a `morsel_source` for it admits no program. The `Constant` refusals are scalars,
  which have no rows to cut, and the plan refuses a `Constant` at the head of a chain as "no source
  of rows".
- `SelectField`. `selects_a_tile` builds it only over a bare product or a record holding a level.
  Over a stream, that needs a `MakeRecord` or a source of records holding collections, and the
  corpus has no program that reaches it with an admitted head. It stays refused until a group with
  `MakeRecord` gives a program to test.
- `RecordWrap`. No program of the corpus reaches it (`NOT_REACHED` in `visit_inputs_tests.rs`), so
  admitting it adds a path nothing runs. It keeps its input's keys and has a projection-guard test,
  so it joins `Streaming::Unary` with the first program that reaches it.

`Restrict` is `Streaming::Unary`: it keeps a row and marks it deleted where its predicate fails
(`RestrictProducer::get_impl`, `mark_deleted`), so a key it drops is in the morsel's region and has
no live row, as for a `MapResult` that filters. `MainWorker::work` compacts a morsel before it
absorbs or folds it. The threaded collector merges morsels without compacting, so its answer carries
the deleted marks, and the pipeline tests compare after `compact`, as every pipeline test does; the
differential suite's threaded pass covers the filtered programs. `MapResultToConst` joins
`MapResult` as `Streaming::Applies`, a data input and an operand named by the edge (`fn`,
`constant`); the operand must be a `Constant`, which every morsel reads whole, and any other operand
is a build side, which stays refused (`a_map_result_to_const_applies_a_constant_and_nothing_else`).

Admission also needs the operator to answer a collection over the keys its input's collection has
(`Planner::keeps_outer_domain`): at the outermost level `MapResultToConst` reads its input whole and
`VariantWrap` wraps it whole, and a morsel's guard would cut something they do not name. The plan
compares the operator's tiling with its input's and refuses a mismatch
(`a_streaming_operator_at_the_outermost_level_is_refused`).

The operators that stay refused need machinery of their own: `MakeRecord` and `Zip` join several
inputs, `UnionOperator` concatenates keys, `Converse` and `MapExtractAggregate` read inner levels, a
`MapResult` that applies a `FanOutSlot` has a build side, and `StoreFinalRead` and `ExtractFinal`
read a recurrence's result.

A list of variants a hundred elements long overflows the stack when the program compiles, on the
serial path as well; the plan test uses twenty.

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
finishes; a failure wakes a parked worker; a claim that ends `Idle` after another found the source
exhausted finishes the pipeline. A worker's turn is the same through `serve` and through
repeated `serve_until_wait` calls with one `ServeState`: the same packages and the same `leave`
calls, with a wait at each unpublished arrival over a live source. A pipeline that streams from
another starts at the first publish to it while the other has a morsel running, starts at the
other's finish with its source closed when nothing was published, stays blocked on a build side
although published and starts when the build side finishes with the region it was published, is
closed only when the last of two upstreams finishes, with a region published after the first
finished still claimed, builds its source on the publishing thread, and starts a parked worker; a
stream from a later pipeline and a pipeline listed twice, in `after` or in `streams_from`, or in
both, are refused. Eight workers over 200 rounds, with the upstream's workers publishing per morsel
or all at once when they leave, claim every downstream position once, and the downstream finishes
after the upstream. A panicking upstream worker fails the dispatcher and no worker stays parked.
`source_of` finds the one source, and refuses a chain
with none and a chain with two.

`LiveSource` has unit tests in `iterate.rs`: it claims only what was published, a region published
twice is claimed once, `Everything` is cut to the keys that are ready, a region that becomes
ready ahead of an earlier one is claimed first, the earlier one is not claimable until it is ready,
and an `Everything` sent while it is missing claims nothing from it, a region outside `ready` is
refused, a region with open bounds names the keys it contains, and a closed source is exhausted
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

**A real data source through the pool, end to end** (`parallel_source_tests.rs`). `[x + 1 for x in
source1()]` is compiled over a `TestDataSource` and run with `run_main_delivering`. Its keys are
sparse integers (10, 20, 35, 41, 90, 120, 7000) or strings, and they arrive in chunks, in order,
last to first and shuffled with fixed seeds. The calling thread delivers a chunk in two steps, as a
real source's rows precede its yield predicate: it writes the rows and calls
`check_for_notifications`, and then adds the chunk's keys to the yield predicate and calls it again.
The yield predicate is the keys that arrived, or, for chunks that arrive in order, the interval from
the smallest key to the largest. Each run checks that the sink holds every row once with its mapped
value, as the serial answer computes it, and that the source reclaimed every key: the pool's release
records are the only ones left, so a key is reclaimed only once a worker claimed, pulled, merged and
released it. In lockstep, every worker is parked before a delivery and the rows written before their
keys are ready must stay unclaimed. Before the chunk of the smallest key is delivered after another,
the delivering thread waits for the source to hold nothing, which a worker can only bring about by
claiming a later chunk while the earlier one is missing, and fails with that cause after thirty
seconds, or at once when the pool failed. Each pattern runs on one, two, four and eight workers, and
one test repeats a run two hundred times. A source that says it cannot cut morsels is refused and
the program then answers through the scheduler loop. A worker that fails reading the source stops
the pool, `run_pipeline` raises that worker's own panic, and the pool's release records are gone.
`run_main` over a source that already holds rows, with no delivery, returns them and finishes
(`tests/it/parallel.rs`). Removing the subtraction of claimed keys, the cut to the yield predicate
or the epoch move each fail a test.

## Not yet implemented

The inline driver's run is held by the loop in `src/main.rs`, which refuses `--control` for a pooled
run because a reload would compile a program beside a pool that still pins the old one's release
records. Storing the run on the `Branch`, dropping it in `tear_down`, and having `pull_mains` drive
the lap lifts that refusal; the lap sits between the delivery and the sink pulls, and `pull_mains`
runs after both, so the loop's order changes with it.

A breaker other than a sink or a `Memo`'s input, a fold into a sink, a build side, a way to hand a
morsel back, and a `Memo` read by more than one slot. A source over a data-source domain runs on the
pool when it cuts morsels (`cuts_morsels`): `TestDataSource` and `HttpServerDataSource` do, and the
stdio source keeps the default, so a program over it stays on the compiling thread. Their arrivals
reach the pipeline through the scheduler's polling, which a live pool drives from the calling
thread: `run_main_delivering` for the threaded pool, which nothing outside tests starts over a live
source (`run_main` has no delivery, so it runs the rows a source holds when it starts and closes the
source), and the loop of the inline driver. The scheduler's `check_for_notifications` notifies with
`Everything`, because `check_for_new_data` says that a source has data and not which keys. A thread
that knows the keys it wrote names them with `Scheduler::notify_source_consumers`, which wakes a
consumer whose outermost keys are the source's with the region and any other with `Everything`. The
end-to-end test names each chunk's keys that way, but the poll before it publishes `Everything` too,
so it does not show the region reaching the head;
`a_chain_over_a_source_forwards_the_region_an_arrival_names` does. The sources' own arrival regions
are not reported. Every program the plan refuses runs on the thread that compiled it, through
`Scheduler::check_for_notifications` and the sink pulls it queues.
