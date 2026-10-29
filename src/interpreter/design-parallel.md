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

`src/interpreter/parallel.rs` runs a program's pipelines through the dispatcher on the scheduler
loop's own thread. Execution is single-threaded: no worker thread exists, and `PooledRun::lap`
serves what the dispatcher has claimable between the scheduler's delivery and the pulls ([The inline
driver](#the-inline-driver)). A program the plan refuses runs on the scheduler loop as before.
`CAMBRA_MORSEL_ROWS` sets the rows per morsel, 4096 unless set.

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
corpus of compiled programs holds. Every operator in a chain is streaming, so the chain holds
no state between morsels. A graph with any other node on the path, a build side, or a sink besides
`main` is refused with the reason, which the binary prints. Which rows a source enumerates is the
source's to say ([The dispatcher](#the-dispatcher)), so `PooledRun::start` refuses a source over anything
but a finite range `[0, n)` when it asks the source for morsels. The programs this admits are `[x +
1 for x in xs]` over a literal list and a `sum`, `max` or `min` of it, and the same behind a value
that the program names and reads (`xs = [...]; [a * 2 for a in xs]`); a source over a data-source
domain is the next shape.

`PooledRun::start` reads everything it can refuse before it takes the program: the plan and each
pipeline's source (`check_pipelines`). It then drops the `main` producer and subscribes the
pipelines. A `Memo` stays in the graph: its own producer, switched to sink mode, is the breaker of the
pipeline that fills it ([Pipeline breakers: sink, finalize and get](#pipeline-breakers-sink-finalize-and-get)),
and the program's slots read it. `LiveProgram` clears the branch's operator map once the pool has
taken the program, so a reload compiles afresh and cannot offer the fan-out to the next version; a
pool takes a program for good. The memo's producer keeps its release record with each source beneath
it until the context's fan-outs drop it, and has released everything it merged by then.
A test runs a shared value over a source and asserts that no key is retained at the source once
the run is released, and no record once the context drops
(`a_memo_over_a_source_leaves_no_record_and_no_key`).

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

`PooledRun::start` subscribes the chain of each pipeline once, so the run owns one producer chain
per pipeline, indexed by `PipelineId`. For a collection the breaker's state is the collector: a
`Mutex<Tile>` the driver merges into with `Tile::merge`, which calls the collection complete once
every package is acknowledged after its rows were merged. For a fold it is the partial of [A fold
as the breaker](#a-fold-as-the-breaker). For a breaker that materializes
(`PoolBreaker::Materialize`) it is a `Materialized` ([A breaker's output](#a-breakers-output)): the
driver merges the morsel into it with `absorb`, publishes the morsel's guard as the region, and then
releases the morsel on its chain, so the release is at the merge. The pipeline's `finalize`
completes the output, before the pipelines that stream from it are closed.

The driver releases a morsel on its chain only after the breaker holds the morsel's rows. That
release is the breaker's acknowledgement ([docs/parallel-execution.md, "A release must mean durably
consumed"](../../docs/parallel-execution.md#a-release-must-mean-durably-consumed)), and it is also
what keeps the chain's producers consistent with the completeness contract: a producer's next pull
states a different interval complete, which it may do only where the previous one was released.

### The dispatcher

The dispatcher is the scheduler of [docs/parallel-execution.md, "The
scheduler"](../../docs/parallel-execution.md#the-scheduler) for the pipelines of a plan. A plan
gives it one `PipelineSpec` per pipeline: the pipelines it follows, a function that builds its
`MorselSource`, and an optional `finalize`. A `WorkPackage` is a `PipelineId` and the guard naming
one morsel. The morsel path of a finite source takes no lock. The calls:

- `next(prefer)` claims a morsel of `CAMBRA_MORSEL_ROWS` rows from a started pipeline, trying
  `prefer` first, and answers `Next::Package`. It answers `Next::Wait` when no started pipeline has
  a morsel and some pipeline has not finished, and `Next::Done` once every pipeline has finished or
  the dispatcher failed.
- `ack` counts a claimed morsel back, once the breaker holds its rows and the morsel is released.
- `step(worker, state)` is one pass of the driver's turn, and `serve_until_wait(worker, state)`
  repeats it until nothing is claimable ([The driver's turn](#the-drivers-turn)).
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
of the dispatcher. `PooledRun::start` finds the source by walking the chain's inputs to the first operator
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

**The epoch counts what can end a wait.** It moves when a pipeline's source is exhausted, when a pipeline finishes, on a publish, on a close and when the dispatcher fails. `serve_until_wait` returns `Settled::Wait` when a step answers `Wait` and the epoch has not moved since the step began.

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
cutting a pipeline at every `FanOutSlot`, so that a slot is the leaf of a `BreakerOutput` and not an
edge into a shared node, and by refusing a deferred edge. A chain that reads a `Memo` at keys has a
head reached along several paths of a diamond: the iterated source's path and one path per slot.
Each path is acyclic, since the slots are leaves, and the keyed head's consumer publishes
`Projection::Everything` for any of them ([Keyed reads](#keyed-reads)), which the live source
resolves to the keys that are ready and not yet claimed, so a duplicate publish adds no key.
`PooledRun::start` subscribes the chains and publishes `Everything` to each data source, so the rows
the source holds when the run starts are claimable, as no notification names them. A source whose
rows arrive stays open until a lap sees its yield predicate cover every key. The driver's loop writes
rows to the source and calls `Scheduler::check_for_notifications`, which polls the source
(`check_for_new_data`) and notifies the consumers registered for it with `Everything`. The head's
`PipelineConsumer` publishes that, and the live source resolves it to the keys that are ready. A
region would add precision and not correctness, and the scheduler's serial path is the same call.

A `PipelineRun` names its head: a data source (`Head::Source`) or a breaker's output
(`Head::Breaker`). `PooledRun::start` seeds every pipeline with a data-source head when the run
starts, whatever the pipeline waits on, since the dispatcher keeps the region in `Early` until the
pipeline starts. The chain of a pipeline carries the consumer that reaches the dispatcher: the
`PipelineConsumer` of a source or of a breaker's output. `BreakerOutput` registers one consumer per
reading operator, so the breaker's `publish` notifies a `PipelineConsumer` from the morsel that
absorbed. Debug builds assert that a chain reaches no operator of another pipeline, that a
data-source pipeline streams from none, and that a breaker-headed pipeline reads the output of a
pipeline it streams from.

**Rows are written before their region is published, and the region before the epoch moves.** The
driver's loop writes the rows under their store's lock, publishes the region under the source's
lock, then moves the epoch, so a claim that follows the publish finds the region and its rows.

**The driver stays on its pipeline.** `next` tries the pipeline the driver last claimed from first,
which keeps its chain and the rows it reads in one cache. The driver moves when that pipeline has no
morsel.

A panic in a chain fails the dispatcher (`FailOnUnwind` in `PooledRun::lap`): `next` answers `Done`
from then on and the panic is re-raised.

#### The driver's turn

`Dispatcher::step` is one pass of the driver's turn. It leaves the pipelines whose source is
exhausted, asks `next`, and runs the package: through the breaker's `pull_sink` for a pipeline with
a breaker, otherwise through `PoolWorker::work`, which pulls the chain, hands the tile to the breaker
and releases the morsel, before `ack`. It answers `Step::Ran` after a morsel, `Step::Wait` when
`next` did, and `Step::Done` when `next` did, and it answers `Done` before it leaves anything once
the dispatcher has failed. What the driver holds between passes is a `ServeState`: the pipelines it
is attached to and the pipeline it ran last. `Dispatcher::serve_state` mints one, naming its
dispatcher by a per-dispatcher id, and a debug build asserts on every step that the state is this
dispatcher's and that one thread uses it.

`serve_until_wait` takes steps until one answers `Done`, or `Wait` with the epoch where it was
before the step, and returns `Settled::Wait` or `Settled::Done`. It parks nowhere: the caller
delivers the arrivals that end the wait and calls again with the same state. A step that answers
`Wait` after the epoch moved is not a wait. The claim that finds a source exhausted moves the epoch,
and the next step leaves the pipeline and finishes it. Every `publish`, `close`, `ack` and finish
of the dispatcher's pipelines happens on the thread that calls it. The plan's pipelines are served
by `MainWorker`; a test double records what it ran and left. `FailOnUnwind` in `PooledRun::lap`
fails the dispatcher when a chain panics.

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
  lock its yield-predicate function reads).
- **Pipeline boundary.** The invariant holds per pipeline: a pipeline behind a breaker has its own
  leaf consumer ([Pipeline boundaries](../../docs/parallel-execution.md#pipeline-boundaries)).
- **Closures.** A closure consumer ignores the region, and the scheduler's drains send `Everything`.

### A pool owns its pipeline's release record


The pool's reader records and `inherits` are superseded by [Pipeline breakers: sink, finalize and get](#pipeline-breakers-sink-finalize-and-get): the producer that was
subscribed keeps its release record across the switch to sink mode.
A data source keeps one release record per producer reading it and reclaims only what every record
releases. A pool breaks both halves of that: the `main` producer `compile_program` subscribes
registers a record that releases nothing, and each worker's chain registers a record that releases
only the morsels that worker ran. Either holds the agreement at nothing.

The pool takes the pipeline's records as its own in two steps. The program's `main` producer goes
once the plan and the source are accepted, which retires its record. It sits in the program's
output, or with a `LiveProgram` that moved it out to drive it, which `LiveProgram::start_inline`
hands to `PooledRun::start`; the pool asserts in debug builds that it dropped one. A program the
pool refuses keeps the producer and stays on the plain loop. `PooledRun::start` then subscribes
every chain inside `Scheduler::with_pooled_release_records`, and a source producer subscribed there
(`IterateExtent`'s, and `MapResultWithSource`'s, which releases into the source as well) holds its
record under `pool#n/<operator id>`, with `n` counting runs. The records of different operators are
intersected by the source, so a key is reclaimed once every operator that reads the source has
released it, as it is in a serial run.

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
from the `Aggregate`'s own. The chain the driver subscribes is the fold's input, reached through
`TileOperator::pool_input`, which `ExtractAggregate` answers with its fold and `Aggregate` with its
input; every other operator answers `None`, which the driver never consults, since the plan
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


The `Materialized` output, `BreakerOutput` and the reader records described here are superseded by
[Pipeline breakers: sink, finalize and get](#pipeline-breakers-sink-finalize-and-get): the breaker holds its state locally and serves `get_impl` from it.
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

**Order.** The driver `absorb`s, then `publish`es with no lock held, and the dispatcher moves its
epoch inside the publish after the source took the region (`Dispatcher::publish`). The rows are
visible before the region is published, and the region before the epoch moves, so a claim that
finds no morsel has read the epoch after the move. A
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
path](#sinks-and-the-http-path)).

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
(`CAMBRA_MORSEL_ROWS` sets a single size), so a program over a few rows runs as many morsels.
A program admitted at the first size and refused at another fails the run.

A completed collection is complete at every level. A morsel states an inner level correctly, and
`Tile::merge` drops the statement as covered by the outer level when the breaker absorbs the morsel
(`drop_covered_completion`). The dispatched tile then means the same as the serial one under the
closure rule and differs in representation, and `Tile ==` compares representations; the first run
of the suite found it in a list of records holding collections, and `[[1, 2], [3, 4]]`, a list of
pairs holding lists and a value read back through a second pipeline show it too.
`Materialized::snapshot` therefore states every level beneath the outermost complete once the
breaker has completed, after the merges and the cut to the projection, keeping what the outermost
states for a read of part of the keys. A breaker that
has not completed states none of them. A collection a variant holds is a value of the variant's
column and has no level of its own, so it is not affected.

### Sinks and the HTTP path

`plan_inline` plans every `Sink` node of the graph as an output: `main`, and each sink such as the
reply channel of `http_serve`, ends a pipeline of its own. A sink's pipeline ends in a collection breaker (`Breaker::Collect`); only `main`
may end in a fold, since a sink dispatches a collection. A `Memo` that a slot starts a chain from is
read by that one slot, so two sinks that each start a chain from one memo are refused, and two
outputs that read one memo at keys are admitted ([Keyed reads](#keyed-reads)).

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

A request the route table does not match is answered by the dispatcher thread, and a malformed one
by the HTTP parser, before either reaches the program. `tests/it/http_server.rs` runs scenarios
through the serial loop and the inline dispatcher and compares the replies:
`source_map_sink_replies_to_each_request_once` (eight requests in two waves, so more than one lap),
`a_memo_between_two_maps_replies_to_each_request_once`,
`a_request_that_arrives_after_idle_laps_is_replied_in_a_later_lap` and
`an_unmatched_or_malformed_request_is_handled_as_in_the_serial_loop`. A map with a filter, and a
reply fed under an `if`, read their request at its own key and run as keyed reads ([Keyed
reads](#keyed-reads)). Each scenario also asserts that the reply sink was handed no index that no
request waits on (a reply written twice) and that the inline run holds no row once every reply is
out (a row never released).

The differential suite compiles each program in a context with no sources or sinks registered, so
the programs that read one are skipped, and the HTTP programs are compared by the scenarios above.

### Keyed reads


The keyed pipeline's `BreakerOutput` source and reader per slot are superseded by [Pipeline breakers: sink, finalize and get](#pipeline-breakers-sink-finalize-and-get):
a parent pipeline's morsels are the keys pushed to it. The admission rules below stay.
Decision: a `MapResult` whose function is a slot of a `Memo` and whose input iterates the memo's own
source extent is a keyed read, and the plan runs it as a pipeline over the memo's output. A
comprehension that reads its source twice, as a filter does, compiles to it: `MapResult(function =
FanOutSlot of the memo, input = IterateExtent)`, and an HTTP program's request stream is such a memo
(`reqs`). The slot is not a build side, which every row reads whole and which blocks its pipeline
until it is complete, a state a live route never reaches. A keyed read asks for the one key of the
row it applies to, and the memo holds that key once the pipeline that fills it has merged the morsel
that contains it.

The plan admits the read under these rules, and each refusal states its reason; the plan tests
`a_keyed_read_is_admitted_over_a_memo_that_keeps_every_key` and the hand-built graphs in
`parallel.rs` (`keyed_graphs`) pin them.

- The values of the input are its keys. `MapResult` reads the memo at `function(input(k))`, so an
  input that answers anything but the keys, a `MapResultWithSource`, a `MapResult` of a `Constant`,
  another keyed read, would read the memo at a key no claim ordered. Only an `IterateExtent` or a
  `Restrict`, which answers the keys that pass, stands directly beneath a keyed read, and the planner
  enforces it.
- The extent of the `IterateExtent` is the memo's own, by `Extent` equality: the key the row names
  is a key of the memo.
- A chain reads at most one memo. The chain's morsels are the keys that memo has merged, and a key
  of a second memo may not be merged yet.
- A memo is read at keys or by a slot that starts a chain, not both. The slot that starts a chain
  takes the memo's pipeline as the chain's own upstream, and a keyed read gives the memo's output
  several readers. Any number of chains, and any number of outputs, may read one memo at keys: each
  slot is a reader of its own, and the shared pipeline inherits what every output that reads it had
  released.
- A keyed read does not sit in a chain that starts at a breaker's output, which has no source whose
  keys it iterates.
- The memo's own input is a `Memo`'s input edge, and not a deferred or shared one.
- The memo's pipeline holds no `Restrict` and no `VariantProject`. This refusal is conservative. A
  keyed morsel may name a key between its first and last for which the memo holds no row, and the
  slot is believed to answer such a key complete and absent, as the serial memo does:
  `test_refiltered_let_bound_comprehension` and `a_filter_over_a_box_that_already_carries_one` agree
  with the serial answer at one and three rows per morsel and on four threads with the refusal
  removed. Admitting it needs the missing-key rule written down. `drops_keys` counts the operators
  that drop keys, `Restrict` and `VariantProject`; the function operands the plan admits are total,
  so a `MapResult` does not.

A keyed pipeline is a `Head::Breaker` pipeline over the memo's output with `keyed` set and the
memo's pipeline in `streams_from`. Its dispatcher source is the source of a slot's `BreakerOutput`,
which claims the published keys and no others, so a morsel never names a key the memo does not hold.
The chain still reads the data source whose keys it iterates, which supplies the rows the morsel
names, and the pool's record for that operator holds the source's rows until the morsel releases
them. The arrivals of that source also notify the chain's head with the keys that arrived, and a
keyed pipeline's consumer publishes `Projection::Everything` for every notification
(`PipelineConsumer`), since a region of arrivals is not a region the memo has merged.

The ordering is the one of every breaker: the upstream worker absorbs the morsel's rows into the
memo's output, which makes the rows and their keys visible together, then publishes the morsel's
region to the readers, then the publish moves the dispatcher's epoch. A claim of the keyed pipeline
reads the published keys, so by the time it can name key `k` the row at `k` is in the output. Each
slot of the chain is a reader of the output that is not `whole`: it reads the rows that were merged
and not yet released by it, and releases the morsel's keys when the morsel is done, so the output
reclaims a row once every slot released it (`a_keyed_read_runs_behind_the_keys_its_memo_has_merged`
asserts that no row is held at the end). The answer is complete once the memo's pipeline has
finished and the keyed pipeline has run its last morsel. The cut gives every slot of a memo a
`BreakerOutput` over one output, and only the first takes the chain that fills it. The inline driver runs keyed reads
(`a_keyed_read_runs_behind_the_keys_its_memo_has_merged`).

The HTTP programs a filter or an `if` reply compiles to run through the inline dispatcher and answer
as the serial loop does (`a_filtered_map_replies_to_the_admitted_requests_only`,
`a_reply_fed_under_an_if_replies_to_the_admitted_requests_only`). A filter over a bare `source1()`,
which reads the source's value at the keys of a restricted `IterateExtent`, stays refused:
`MapResultWithSource` is admitted over an `IterateExtent` only.

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
absorbs or folds it. The pipeline tests compare after `compact`, as every pipeline test does. `MapResultToConst` joins
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
`MapResult` that applies a `FanOutSlot` of a `Memo` that drops keys has a build side, and
`StoreFinalRead` and `ExtractFinal` read a recurrence's result.

A list of variants a hundred elements long overflows the stack when the program compiles, on the
serial path as well; the plan test uses twenty.

### Pipeline breakers: sink, finalize and get

Decision: each pipeline breaker implements a different interface from a streaming operator. The
interface has three entry points, and a breaker is the sink of its pipeline.

- `pull_sink(guard)` is called by the dispatcher. It runs everything from the source to persisting
  the breaker's own state inside the operator itself.
- `finalize()` is called by the dispatcher once the pipeline has drained. It finalizes any state
  requirements and notifies the pipelines that read the breaker, by pushing work packages for them
  onto the dispatcher.
- `get_impl` is called as it is today, and serves projections out of the state `pull_sink` built and
  the breaker holds locally, where an aggregation builds its state inside `get_impl` today.

The terms of this section: a **parent pipeline** of a breaker is a pipeline whose head reads that
breaker's output. A **round** is the dispatcher's drain of the regions pending for one pipeline.
**Local state** is what the breaker's producer holds between calls.

The decisions taken with the interface:

1. Execution is single-threaded. Every call below runs on the dispatcher's thread.
2. `finalize` runs per round, and a round is one drain of the regions pending for the pipeline: a
   round per lap bounds the pushes of a lap to one per pipeline. `finalize` pushes the keys that are
   final to the parent pipelines. A terminal finish is a flag on the last round, so a pipeline over
   a source that never ends, an HTTP route, feeds its parents each round with the keys that are
   final by then.
3. The breaker owns its input chain. `pull_sink(guard)` pulls the input producer the breaker owns at
   the morsel guard, merges the answer into local state, and releases the input at the guard after
   the merge, as a `Memo` releases its input today. The dispatcher neither clones nor reaches into a
   chain. It reaches a breaker through the handle its pipeline's spec holds.
4. `get_impl` answers only from local state. It states completeness from what `finalize` has said,
   and it never pulls the input once the breaker is a sink.
5. A keyed read needs no structure of its own. A morsel of a parent pipeline exists only for keys a
   push named, and the breaker holds those keys.
6. `finalize` pushes through a `Pushes` handle, and does not return a region. The handle pushes to
   every parent of the breaker, which is a fixed set: a pipeline that reads a breaker's pushes
   streams from that one breaker pipeline.
7. A `Memo` switched to sink mode adopts the cache it holds and pushes its keys first, since the
   serial pull already released them and no sink pull reads them again. Only a collection switches:
   a parent's morsels are keys.
8. Several consumers of one breaker keep the per-slot release records of the serial `Memo`, and the
   breaker reclaims a key when every slot has released it.
9. A pipeline's breaker pushes keys with rows only, and the refusal of a keyed read of a memo that
   drops keys is lifted in a later commit, once the missing-key rule is written down.
10. The scheduler's registry, keyed by `NodeId` and filled at `subscribe`, finds a breaker, because
    consumers own the producers and a walk would open every consumer. The producer owns the breaker
    and the registry holds it weakly, so dropping the producer drops the input and retires the
    release records it registered.
11. A program with one breaker the plan refuses is refused as a whole, as the plan refuses a program
    now.
12. The pinned programs are checked with every memo in sink mode from step 4, the step that
    removes the other inline path.

#### The interface

```rust
trait Breaker: Send + Sync {
    /// Switch to sink mode. Called once, before the first `pull_sink`.
    fn begin_sinking(&self);

    /// Pull the owned input at `guard`, merge the answer into local state, release the input at
    /// `guard`. Called by the dispatcher for each morsel of the breaker's pipeline.
    fn pull_sink(&self, guard: TileGuard);

    /// The first `rows` keys of `region` that local state holds, in key order: how a parent
    /// pipeline's morsel is cut.
    fn first_keys(&self, region: &Predicate, rows: u64) -> Vec<Value>;

    /// End of a round. Finalize what the round merged and push the keys that are final, which the
    /// parents may now claim. `round.terminal` is set on the last round of the pipeline.
    fn finalize(&self, round: Round, parents: &mut Pushes);

    /// How many keys local state holds, which a release of the output reclaims.
    fn held_keys(&self) -> usize;
}

type BreakerHandle = Arc<dyn Breaker>;

struct Round {
    terminal: bool,
}

/// What `finalize` may do to the dispatcher: push final keys to the parent pipelines.
struct Pushes<'d> { /* the dispatcher and the breaker's parents */ }

impl Pushes<'_> {
    fn push(&mut self, region: &Predicate);
}
```

A breaker is the sink of its pipeline: the pipeline's morsels end in it. The dispatcher driving it
per morsel is the same act as the scheduler pulling a program sink, since a program's own sink is
the consumer of the last pipeline's breaker. This is why the entry point is `pull_sink`, in the
codebase's word for driving a sink (`SinkConsumer::pull_now`, `Scheduler::pull_sinks`). The trait is
`Breaker`.

The producer that owns a breaker holds its `BreakerHandle`, and the local state lives behind it: the
operator is a description that outlives one subscription. The methods take `&self` and the
implementor locks its own state, since the handle is shared by the producer and the pipeline's spec.
A pipeline's chain holds only streaming producers between its source and its breaker.

`push` names a region of the breaker's output keys that are final. The dispatcher records it as
claimable by each parent pipeline and cuts morsels from it with `first_keys`, and it claims each
pushed key once. A parent's source is cut by one breaker's `first_keys`, so a pipeline streams from
exactly one breaker pipeline when it reads pushes: the dispatcher asserts it when it is built, since
a second breaker's keys would be claimed as pending of the first and lost. `finalize` pushes keys
with rows: a key the pipeline dropped, as a `Restrict` does, is not named.

`get_impl` is unchanged in signature. In sink mode it reads local state restricted to the projection
guard, and the guard checks of the `get` wrapper apply as they do to every producer.

#### The dispatcher

A pipeline is the pair of a breaker and the chain the breaker owns. The plan names the breaker
operator of each pipeline. A breaker's producer registers its breaker with the scheduler when it is
subscribed, keyed by its operator's `NodeId`, because consumers own the producers; `PipelineSpec`
carries the handle of its pipeline's breaker, and the dispatcher calls it directly. One thread
drives a dispatcher that has a breaker pipeline, through `serve_until_wait`.

The step of `serve_until_wait` for pipeline `P` changes in three places.

1. The source of `P`'s morsels is `P`'s own: the data source's `MorselSource`, or for a parent
   pipeline the queue of regions pushed to it, cut by the breaker's `first_keys`.
2. A claimed morsel runs `breaker.pull_sink(guard)`. The dispatcher no longer pulls a chain and
   hands the tile to a breaker's `absorb`.
3. When `P` has no morsel left to claim and either ran one since its last round or has run no
   round yet, the dispatcher calls `breaker.finalize(Round { terminal }, pushes)`. `terminal` is set when the source of `P` is
   exhausted and every pipeline `P` streams from has finished; the dispatcher marks `P` finished,
   runs the terminal round, closes the pipelines that stream from `P` and starts the pipelines
   waiting on it.

`streams_from` is kept. It lists the pipelines whose pushes a pipeline consumes, and it orders start
and finish: a pipeline finishes after the pipelines it streams from. The push direction is its
inverse, and the dispatcher computes it once when it builds the specs, so `Pushes` for a breaker
addresses exactly the pipelines that list it in `streams_from`. Replacing `streams_from` by a
`feeds` list would state one relation twice, since a finish is ordered by the same edges the pushes
travel.

`after` keeps its meaning, a pipeline that starts only when another has finished, which a build side
needs. The region publish that a breaker's `Materialized` performs today is `Pushes::push`.

A pipeline whose chain reads a memo at keys is a parent pipeline of that memo. Its morsel source is
the push queue regardless of the data source its chain iterates, which supplies the rows the morsel
names. The rule that the values of the input are keys ([Keyed reads](#keyed-reads)) stays a plan
rule, since the morsel names keys and the chain must read at them.

The interface lives in `src/interpreter/tile_operators/mod.rs` (`Breaker`, `Round`, `BreakerHandle`),
and the dispatcher's side in `src/interpreter/parallel.rs` (`Pushes`, `PipelineSpec::breaker`,
`Dispatcher::drain`, `Dispatcher::round` and `Dispatcher::sink_morsel`, `pushed_source`). The
registry is `Scheduler::register_breaker` and `Scheduler::breaker`, and holds each breaker by `Weak`;
a second registration for an operator replaces the first, because a reload subscribes an operator it
carried forward while the old producer is alive:
the producer that owns a breaker holds its `BreakerHandle`, an `Arc<dyn Breaker>`, and a pipeline's
spec holds a clone. The methods of `Breaker` take `&self` and the implementor locks its own state,
because the handle is shared; the lock is never contended. The enum `parallel::BreakerKind` names
what a planned pipeline ends in. `Memo` implements the interface in
`src/interpreter/tile_operators/fanout.rs`: `MemoState` holds the cache, `dirty` and the input, and
the producer owns it and the `MemoBreaker` that reaches it, so the registry's weak entry lives as
long as the producer.

#### Completeness and release

While rounds continue, `get_impl` states complete the region of keys merged and final, and states
every other region incomplete. A collection breaker (`Memo`) states a merged key complete because
the morsel that supplied it did, and its merged keys are final. A folding breaker states its value
incomplete until the terminal round, and the terminal round states it complete. A group of a
grouping breaker is terminal when `finalize` says so, which is the terminal round: a grouping
breaker pushes a key only when it is final.

A memo in sink mode swallows what its input notifies: those regions are changes the sink has not
merged. `finalize` notifies the memo's consumer of the keys it pushed, and with `Everything` on the
terminal round, so a consumer is never woken before the rows it was woken for are merged.

An update of a key a parent pipeline has already claimed is not served, as today: a parent claims
each pushed key once, so a key pushed with a running value would reach its consumers once and
incomplete, and would never be updated. A downstream of a grouping breaker over a source that never
ends therefore waits for the terminal round, which is the semantics until updates can be re-served.

Release has two directions.

- The downstream release is a release at the breaker's `get`. A `Memo` reclaims a cached key when
  every consumer released it, as today. A folding breaker has one value, and a release of it at the
  terminal round frees the state.
- The sink's own release is the release of its input. `pull_sink` asserts the answer states the
  whole guard complete, merges it, and releases the input at the guard, so the input holds nothing
  for a merged morsel, and a source reclaims what the breaker's producer released. The producer is
  the one the serial run subscribed, so its release record with a source is the same record before
  and after the switch to sink mode.

#### The serial path

A serial run pulls through `get_impl` as today, and every program the plan refuses runs that way. A
breaker therefore has both behaviours, and one producer serves both.

The producer starts in pull mode, which is the behaviour it has now: `get_impl` pulls the owned
input at the projection, merges, and answers. `PooledRun::start` plans the program, and for each
pipeline it plans, it calls `begin_sinking` on the breaker's producer. A producer that has been
switched is in sink mode until it drops, and no program switches back. A program the plan refuses
switches nothing and keeps the pull mode of every breaker.

The switch adopts the state the producer holds. A `Memo` keeps its cache, and the keys the cache
holds are the first it pushes; the region pending for its pipeline is the dispatcher's source, and
the memo's `dirty` is pull-mode state that sink mode does not read. A fold keeps its accumulator. A
breaker that is not a collection does not switch: a parent's morsels are keys, and the plan switches
only the memos it plans as pipelines. A producer switched before it was ever pulled holds an empty
state, which is the usual case, since `PooledRun::start` runs before the loop's first pull of
`main`; a sink that `compile_program` pulled at once is the exception, and it is why adoption is
part of the interface.

The risk is two code paths in each breaker. Each breaker's tests run in both modes and compare the
answers, and the differential suite compares a whole program's answer through the pull mode and
through the sink mode at every step of the migration.

#### The per-breaker mapping

`Memo`: the state is the cache. `pull_sink(guard)` pulls the input at the guard, merges the tile
into the cache, and releases the input at the guard. `finalize` pushes the keys merged since the
last round, which are final. `get_impl` answers a projection from the cache and states the merged
region complete. `first_keys` lists and sorts the keys the cache holds on each call, a cost per
claim that a sorted index would remove.

`Aggregate` and `ExtractAggregate`: the state is the accumulator. `pull_sink` accumulates the
morsel's values into it (`AggregateKind::accumulate`), which is the work `get_impl` does today.
`finalize` pushes nothing until the terminal round and then pushes the one key of the result.
`get_impl` serves the accumulator, incomplete until the terminal round. The `ExtractAggregate` reads
the fold's value through `get_impl`, so a fold into `main` stays a pipeline whose breaker is the
aggregate.

`MapAggregate` and `MapExtractAggregate`: the state is the group table. `pull_sink` accumulates the
morsel into the groups its keys fall in. `finalize` pushes nothing until a group is final, which is
the terminal round, and then pushes the group keys. A group is terminal when `finalize` says so.

`Converse`: the state is the hash table that regroups the input by value. `pull_sink` extends the
table with the morsel's rows. A new row can add a key to any group, so no group is final before the
terminal round, and `finalize` pushes the group keys on that round. A probe pipeline reads the table
as a function operand through `get_impl`, which is the hash join's build side, once it is final.

`ExtractFinal`: the state is the one value of a store's final read. `pull_sink` merges nothing until
the input's terminal round, and `finalize` on that round pushes the value's key.

The stores and recurrence operators (`InductionStore`, `TransactWriter`, `CommitOperator`,
`StoreFinalRead`, and the drivers) stay as they are. They are not breakers of this interface, and
the plan refuses them as it does today.

#### What the design replaces and keeps

What stays:

- `serve_until_wait`, the dispatcher's epoch protocol, and the inline driver `PooledRun`.
- The differential suite and its pin of 160 programs.
- The HTTP source's morsels and the reply sink. A program's sink pulls the last breaker's producer
  through `get_impl`, where it pulls a `BreakerOutput` today.
- The admission arms of `classify`, the plan tests and `keeps_outer_domain`.
- The release record of a pipeline's source operators, owned by the producer that was subscribed for
  the serial run.

What goes:

- `Materialized`, `BreakerOutput` and `PoolBreaker::Materialize`: local state and `get_impl` replace
  them.
- The cut and `TileOperator::visit_inputs_mut`: the breaker keeps its chain, so no chain is taken
  out of the graph.
- The pool's reader records and `inherits`: the producer's own record continues across the switch.

What is rebuilt:

- Keyed reads: the pipeline's morsel source is the push queue, and the plan keeps the
  values-are-keys rule.
- The plan's identification of a pipeline: the plan names the breaker operator in place of the cut
  chain.
- The refusal that drops-keys memos are not read at keys: `finalize` pushes keys with rows, so the
  refusal can be lifted once the missing-key rule is written down.

#### Migration

Each step is a commit with its unit tests and a full differential run, and the pinned programs do
not regress. Step 3 checks every pinned program in pull mode and in sink mode; from step 4 the
inline driver has sink mode only.

1. The interface: `Breaker`, `Round`, `Pushes`, the scheduler's registry, the dispatcher's round and
   push queues, tested with a breaker double. Tests: rounds run when a pipeline drains, a terminal
   flag is set once, a push reaches exactly the parents, a parent's morsels are cut from pushed keys
   only.
2. `Memo` implements the interface in both modes. Tests: sink and pull answer the same, the switch
   adopts a cache and its keys reach the parent, completeness follows rounds, release at merge, the
   consumer is notified from `finalize` only, the sink never pulls its input from `get_impl`. The
   whole-corpus differential in sink mode starts at step 3, since no pooled run uses a memo's
   breaker before it.
3. `PooledRun::start` switches the memos it plans, and the dispatcher runs them as pipelines. The
   cut still takes the other chains.

   In step 3 `MemoMode` selected the mode: `PooledRun::start_in` took it, and `PooledRun::start` read
   `CAMBRA_DISPATCH_MEMOS`. `sunk_memos` finds each planned memo's breaker in the scheduler's
   registry, and `start_planned` calls `begin_sinking` on it and gives the memo's pipeline a `Sunk`
   placeholder (`tile_operators/sunk.rs`) where the chain would be, so no chain is cut for a memo.
   A memo whose tiling is not a data function, or that the registry does not hold, is refused. A
   pipeline that streams from a memo takes its morsels from `pushed_source` of the memo's handle:
   the chain's notifications do not reach it. `PipelineRun::sink` is the handle of the memo whose
   pipeline it is.

   A pipeline that reads pushes ignores the notifications of its chain's source. Its morsels are
   the keys pushed to it, a pushed key is a key the memo merged from that source, and the chain
   reads the source at that key through its own release record, so a row that arrives after its key
   was pushed concerns a later push. `a_keyed_read_runs_behind_the_keys_its_memo_has_merged` runs
   rows in waves. The plan ends a chain at one head, so a pipeline streams from
   at most one breaker pipeline; `Dispatcher::new` asserts it for any other spec.

   `PooledRun::held_keys` adds the keys the sink memos hold (`Breaker::held_keys`), which a
   release of the output reclaims.

   A memo swallows its input's notifications in sink mode, so a memo pipeline that reads a live
   source learns of arrivals from the lap: `OpenSource::poll` has the lap publish `Everything` to
   it, and a finished pipeline is skipped. A lap that sank a morsel counts as work.

   The differential checks every admitted program in both modes at morsel sizes 1 and 3. Tests: a
   memo in sink mode answers as the materializing pool does; a memo over a live source delivers each
   row once, alone and in a chain; a keyed read behind its memo's merges in both modes; the corpus at
   the pinned count in both modes; the HTTP scenarios through the plain loop, the inline driver and
   the inline driver in sink mode.
4. Sink mode is the only inline memo mode. The inline driver no longer cuts the graph: `MemoMode`,
   `PooledRun::start_in`, `CAMBRA_DISPATCH_MEMOS`, the cut and `Taken`, `Detached`,
   `TileOperator::drop_serial_subscription`, `Materialized::feeds`, the keyed `PipelineConsumer` and
   the keyed pipeline source are deleted, and a keyed read's morsels are the keys its memo pushed.
   Tests: the keyed read tests as they stand, run over the push queue; the HTTP scenarios; the
   corpus at the pinned count. The threaded passes had been removed by the commit before it, so
   no differential runs a memo through the pool's materializing path. `Materialized`,
   `BreakerOutput` and `PoolBreaker::Materialize` stay for the outputs' own breakers until step 9.
5. `Aggregate` and `ExtractAggregate`, with the unit tests per kind and the differential run of the
   folds.
6. `MapAggregate` and `MapExtractAggregate`, with a test that a group is terminal only at the
   terminal round.
7. `Converse`, with a test of a probe that reads the table of one round and then of the next.
8. `ExtractFinal`.
9. The program sink pulls the last breaker's producer; delete `BreakerOutput` and `Materialized`.
10. Delete the cut, `visit_inputs_mut`, the reader records and `inherits`, and the sections of this
    document they leave stale.

#### Invariants

Asserted where the invariant lives, in debug builds:

- A breaker in sink mode pulls its input only inside `pull_sink`.
- A key is pushed only when it is final.
- `finalize` is called with `terminal` set at most once, and `pull_sink` is not called after it.
- A parent's morsel is a subset of the keys pushed to it and not yet claimed.
- `get_impl` states complete only keys a morsel merged, and every level complete only after the
  terminal round. A finite extent whose every key was merged is complete at that round.
- A morsel's answer states its guard complete, and the input is released at the guard.
- `begin_sinking` is called once, before the first `pull_sink`, and a breaker is never switched
  back; a breaker that sinks is a collection.
- A pipeline that reads pushes streams from one breaker pipeline.
- Every call of the interface happens on one thread, through `serve_until_wait`.

Checked in every build, because a violation loses rows silently:

- Each round's pushed keys are disjoint from the keys of every earlier round: `Pushes::push` panics
  on a repeated key, and a parent would never serve the second push of it.

#### Open questions

None.



### Tests

The dispatcher's unit tests run against hand-built `PipelineSpec`s and a recording worker
(`parallel.rs`, `mod tests`; `parallel_breaker_tests.rs`): morsels are disjoint and cover the range;
a pipeline starts after the pipelines it follows and at the first publish of a pipeline it streams
from, and a region published before it starts is kept; an empty pipeline starts the ones behind it;
a dependency on a later pipeline, a repeated dependency and a pipeline that both follows and streams
from one are refused; a pipeline finishes only when its claimed morsels are acknowledged and every
attached claim has left; `finalize` runs before the pipelines behind it start; a failed dispatcher
hands out nothing; `serve_until_wait` waits on a live source and resumes from its state.

The inline driver's tests (`parallel_inline_tests.rs`, `tests/it/parallel.rs`) run programs through
`PooledRun` and compare with the serial answer: collections and folds over literal lists at morsel
sizes that do and do not divide the rows, a shared value as two pipelines, variants, `Restrict`
and `MapResultToConst`, rows delivered in waves to a live source, a source that cannot cut morsels,
a source that holds rows when the run starts, and no release record or retained key left at the
source once the run is released. The differential suite covers the rest of the corpus.

## Not yet implemented

The inline driver's run is held by the loop in `src/main.rs`, which refuses `--control` for a pooled
run because a reload would compile a program beside a pool that still pins the old one's release
records. Storing the run on the `Branch`, dropping it in `tear_down`, and having `pull_mains` drive
the lap lifts that refusal; the lap sits between the delivery and the sink pulls, and `pull_mains`
runs after both, so the loop's order changes with it.

A breaker other than a sink or a `Memo`'s input, a fold into a sink, a build side, a way to hand a
morsel back, and a `Memo` read by more than one slot that starts a chain. A source over a data-source domain runs on the
pool when it cuts morsels (`cuts_morsels`): `TestDataSource` and `HttpServerDataSource` do, and the
stdio source keeps the default, so a program over it stays on the compiling thread. Their arrivals
reach the pipeline through the scheduler's polling, which the loop of the inline driver drives from
the calling thread. The scheduler's `check_for_notifications` notifies with
`Everything`, because `check_for_new_data` says that a source has data and not which keys. A thread
that knows the keys it wrote names them with `Scheduler::notify_source_consumers`, which wakes a
consumer whose outermost keys are the source's with the region and any other with `Everything`. The
end-to-end test names each chunk's keys that way, but the poll before it publishes `Everything` too,
so it does not show the region reaching the head;
`a_chain_over_a_source_forwards_the_region_an_arrival_names` does. The sources' own arrival regions
are not reported. Every program the plan refuses runs on the thread that compiled it, through
`Scheduler::check_for_notifications` and the sink pulls it queues.
