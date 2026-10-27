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
scheduler"](../../docs/parallel-execution.md#the-scheduler) for the pipelines of a plan. It holds
one job per pipeline, a `MorselSource` with two atomics, and one `failed` flag. No lock guards it
and no worker waits in it. A `WorkPackage` is a `PipelineId` and the guard naming one morsel. The
calls:

- `next` claims a morsel of `CAMBRA_MORSEL_ROWS` rows from the first pipeline whose source has one
  and answers it as a package. It answers `None` once every source is exhausted or the dispatcher
  failed.
- `ack` counts a claimed morsel back, once the breaker holds its rows and the morsel is released.
- `is_done` says whether a pipeline's source has answered `None` and every morsel it answered is
  acknowledged.
- `fail` makes every `next` answer `None` from then on.

A worker pulls its morsel from the source; no structure holds morsels between the two. This is the
dispatch of Leis et al. 2014, where the dispatcher carves the next range off a pipeline's input when
a worker asks.

**The source cuts its own rows.** `TileOperator::morsel_source` answers an `Arc<dyn MorselSource>`
for an operator that is a source and `None` for every other. `MorselSource::claim(rows)` answers the
guard of the next morsel of at most `rows` rows, or `None`, which is final. `IterateExtent` over a
finite range `[0, n)` answers a `RangeSource`: one `AtomicU64` cursor that `fetch_update` advances,
so each position is in exactly one claimed morsel whichever threads claim, and the cursor never
passes `n`. The claim orders nothing else: the cursor partitions positions, and the data a worker
reads under a guard comes from its own chain. `IterateExtent`'s producer knows nothing of the
dispatcher. `run_main` finds the source by walking the chain's inputs to the first operator that
answers one, and refuses a chain with none or with several.

**Done is a count.** A claim counts itself outstanding before it asks the source and takes the count
back when the source answers `None`, so an exhausted source with nothing outstanding has no claim in
flight. `ack` is the only other decrement.

**`None` is final only while every pipeline's source exists.** A pipeline that exists only after
another finishes, behind a breaker, or a source that receives rows over time, makes `None` mean
"nothing now". The dispatcher is where a worker then waits, which needs a wake-up that a claim does
not provide.

A worker that panics fails the dispatcher on its way out (`FailOnUnwind`): `next` answers `None`
from then on, the other workers stop claiming, and the scope re-raises the panic.

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
its morsels are disjoint and end in `None`, a morsel holds at least one row, and a finite range from
zero is the one extent that answers a source. The dispatcher's unit tests in `parallel.rs`: morsels
are disjoint and cover the range; an empty range hands out nothing; a claimed morsel keeps its
pipeline from being done until it is acknowledged; a failed dispatcher hands out nothing; a
panicking worker stops the others claiming; eight workers claim every position of a range once.
`source_of` finds the one source, and refuses a chain with none and a chain with two.

## Not yet implemented

A breaker other than the sink and a fold into `main`, a source over a data-source domain, a pipeline
plan over more than one pipeline, a source that receives rows over time (its claim needs a state
between exhausted and nothing yet, and workers need a wake-up), and the sink pulls the scheduler
loop queues. Before a source over a data-source domain lands, the `main` producer `compile_program`
subscribes has to be owned by the pool: it registers a release record of `False` with the source,
and a source agrees to reclaim only what every record releases, so an idle producer pins the source.
Every program the plan refuses runs on the thread that compiled it, through
`Scheduler::check_for_notifications` and the sink pulls it queues.