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
plan"](../../docs/parallel-execution.md#the-pipeline-plan) describes, for one pipeline shape:
`IterateExtent` over a finite range `[0, rows)`, any number of `MapResult`s whose function operand
is a `Constant`, and the `main` sink. Every operator in the chain is streaming, so a worker's chain
holds no state between morsels, and the sink is the one breaker. A graph with any other node on the
path, a source over anything but `[0, rows)`, or a sink besides `main` is refused with the reason,
which the binary prints. The program this admits is `[x + 1 for x in xs]` over a literal list; a
source over a data-source domain is the next shape.

### The pool

`run_main` subscribes the `main` operator once per worker, so each worker owns one producer chain,
as [docs/parallel-execution.md, "Thread-confined chains, shared
breakers"](../../docs/parallel-execution.md#thread-confined-chains-shared-breakers) asks. An
operator is subscribed as many times as there are workers; nothing is cloned, because the chain is a
tree of boxed operators each subscription walks afresh. A worker holds its chains in a vector
indexed by `PipelineId`, which holds one entry, since the plan holds one pipeline. The threads are
`std::thread::scope` threads over `run_worker`; the head runs on the calling thread inside the same
scope, so the workers drain the dispatcher while the head fills it. The collector is the sink: a
`Mutex<Tile>` the workers merge into with `Tile::merge`, which calls the collection complete once
every worker has returned, every package acknowledged after its rows were merged.

The chains are lent to the workers and dropped after the scope, one at a time on the thread that
subscribed them: a producer's drop detaches its probe with a lock that must not find the probe table
held by another worker's `get`.

A worker releases a morsel on its chain only after the collector holds the morsel's tile. That
release is the sink's acknowledgement ([docs/parallel-execution.md, "A release must mean durably
consumed"](../../docs/parallel-execution.md#a-release-must-mean-durably-consumed)), and it is also
what keeps the chain's producers consistent with the completeness contract: a producer's next pull
states a different interval complete, which it may do only where the previous one was released.

The cells workers contend on take a blocking lock, `LockNow::lock_wait`: the probe table's
`observe_named`, which every `get` calls, the collector, and the dispatcher's state. Every other
cell keeps the panic-on-contention lock, because a worker's chain is its own and never shares a cell
with another worker's; the probe table's readers are on the thread that runs the inspector, which a
parallel run refuses.

### The dispatcher

The dispatcher is the scheduler of [docs/parallel-execution.md, "The
scheduler"](../../docs/parallel-execution.md#the-scheduler) for one pipeline: a
`Mutex<DispatchState>` with a `Condvar`. The state is a `VecDeque` of `WorkPackage`s, each a
`PipelineId` and the guard naming one morsel, and per pipeline whether it is closed and how many of
its packages are taken and not acknowledged. One queue serves every pipeline because the plan holds
one; the target gives each pipeline its own queue, so a worker can stay on its pipeline. It has six
calls:

- `publish` queues a package behind every package already published.
- `close` records that the pipeline's head publishes no more.
- `next` answers the oldest queued package and counts it taken; with the queue empty it waits on
  the `Condvar` while a pipeline is open, and answers `None` once every pipeline is closed.
- `ack` counts a taken package back, once its morsel is merged and released.
- `is_done` says whether a pipeline is closed with none of its packages queued or taken.
- `fail` makes every `next` answer `None` from then on.

The pipeline's head is a `RangeHead` over `[0, rows)`: it cuts the range into morsels of
`CAMBRA_MORSEL_ROWS` rows, publishes one package per morsel in order, and closes the pipeline.
`IterateExtent`'s producer knows nothing of the dispatcher: each worker holds its own, and the head
is the one object per pipeline that cuts the source.

A worker that panics fails the dispatcher on its way out (`FailOnUnwind`), and so does the head:
`next` answers `None` from then on, the other workers return, and the scope re-raises the panic
instead of waiting for a package nobody will publish.

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

### Tests

`tests/it/parallel.rs`: two chains pulled at disjoint guards and merged equal the whole pull, and
each chain's next pull past its released interval answers the rest; four workers over a thousand
rows with a morsel size that does not divide them equal the whole pull and are terminal; one worker
equals the whole pull; a program with an aggregate is refused. The three producers each have a unit
test of the interval they hand out and the release that follows (`map.rs`, `scalar.rs`,
`iterate.rs`). The dispatcher's unit tests in `parallel.rs`: a range head publishes disjoint morsels
covering its range and closes; an empty range publishes nothing and is done; a taken package keeps
its pipeline from being done until it is acknowledged; a waiting worker wakes on a publish and on a
close; a panicking worker releases the waiting ones.

## Not yet implemented

A breaker other than the sink, a source over a data-source domain, a pipeline plan over more than
one pipeline, a dispatcher over more than one pipeline with heads that publish as rows arrive, and
the sink pulls the scheduler loop queues. Before a data-source head lands, the `main` producer
`compile_program` subscribes has to be owned by the pool: it registers a release record of `False`
with the source, and a source agrees to reclaim only what every record releases, so an idle producer
pins the source. Every program the plan refuses runs on the thread that compiled it, through
`Scheduler::check_for_notifications` and the sink pulls it queues.
