# Concurrent execution with shared pipeline breakers

Status: initial implementation. [Unified native execution](#unified-native-execution) specifies the
implemented runtime and eligibility rules. The preceding sections describe the target model and
its remaining scope. The planner, ownership extraction and dispatcher are specified in
[Pipeline dispatch](design-dispatcher.md#the-dispatcher).

Workers execute shared immutable pipeline plans using explicit worker-local execution state. They
read upstream breakers or sources, evaluate inline operators, and apply contributions to shared
destination breakers. Mergeable aggregates may buffer contributions in reusable worker-local maps.
The coordinator schedules claims and handles publication and control; it does not prepare input
tiles or combine worker results. Incremental publication is required from the first admitted
pipeline: completed output regions can enable downstream work before the producer pipeline closes.

This design preserves the [producer protocol](design-operators.md#the-producer-protocol).
Operators exchange tiles through subscribed inputs. Shared breaker readers implement that protocol;
they do not expose accumulator maps or other operator state to downstream operators.

## Decisions and scope

- Pipeline parallelism runs ready work from different pipelines concurrently. Dependencies become
  runnable through the existing breaker publication rules.
- Data parallelism runs independent claims of one shared pipeline plan with private execution
  state in each worker context. Operator configuration is immutable and shared.
- One shared state instance represents each breaker, including breakers with several inputs.
  Workers apply contributions directly under one state mutex per breaker initially.
- Mutable inline operator state has one worker owner. Mergeable aggregates support reusable local
  accumulators with explicit flush obligations. Finer breaker locking is a later optimization.
- Breakers and sources own shared retention accounting per logical reader. Private worker release
  guards do not independently authorize reclaiming shared input.
- Output publication follows region and group completeness, independently of whole-pipeline finish.
  Buffered contributions count as outstanding work until applied to shared state.
- Graph construction, source polling, notification routing, publication, finish and loop control
  initially remain on the coordinator. Worker reads and releases do not call back to it for data.
- Ordered pipelines retain one claim in flight. Other pipelines permit concurrent claims only when
  their operator instances and breaker updates satisfy the contracts below.

The first admitted pipelines include incremental publication and logical retention. Eligibility
requires a correct region-readiness and contribution protocol; a whole-input barrier is not the
default parallel execution contract. Unsupported chains remain serial under the same dispatcher.
They may overlap workers only when every shared boundary they touch is synchronized.

## Ownership and execution

A pipeline plan contains immutable operator configuration and input/output identities. Each worker
has an execution context with private cursor progress for the pipelines it executes. An execution
instance below means one such private state entry, including caches, cursors, subscriptions and
optional aggregate buffers. It does not own another copy of the immutable operator plan. A job
carries a claim and pipeline identity. State is initialized and reused on its owning worker.

| Object | Owns | Access |
| --- | --- | --- |
| Shared pipeline plan | Operator configuration, structural shapes, input/output identities | Immutable, `Send + Sync` |
| Worker context | Private release bookkeeping, caches, cursors, scratch and local aggregate buffers | Its worker only; no thread-local lookup |
| Shared breaker | Held output, shared accumulators, output releases, contribution progress and completion | Synchronized readers and writers |
| Logical input subscription | Reader identity, established releases, pending demand and active reads across workers | Synchronized metadata |
| Coordinator | Admission, publication deduplication, notification routes, source pollers and lifecycle | One control thread |

`Breaker::consume_impl(&mut self, input, guard)` currently reads upstream, changes retained state
and releases upstream under one mutable borrow. The target separates input execution state from
shared destination state. A mutex around the complete existing producer would serialize upstream
reads and inline computation.

For example, `Memo → MapResult(price × quantity) → MapAggregate(by customer)` shares the immutable
map and aggregation definitions. Each worker reads the memo through its logical subscription and
computes products. It folds those products into a reusable local map keyed by the complete customer
path. A flush transfers accumulator contributions to the shared `MapAggregate`. Downstream readers
observe published tiles according to the aggregation's completeness rules.

### Several instances of one pipeline

Different workers may execute the same immutable plan concurrently. Each private state entry is
initialized from that plan and explicit logical input subscriptions. Initialization does not
register another unrestricted upstream reader. Private release guards record established local
releases; assigning work does not mark it obsolete. Producer and probe instance IDs remain distinct
from logical reader identities.

Configuration such as `MapResult.level`, `Filter.level`, `MapResultToConst.mode`, record field names
and aggregate kind belongs to the shared plan. Release guards, cached tiles, seen/held paths and
local aggregate maps belong to worker state. Existing native producers mix these categories;
their compatibility adapters do not complete this separation.

Persistent state in `Converse`, `Zip`, Cartesian `IterateExtent`, store cursors and transaction
attempts requires an operator-specific partition rule. Until then, the affected pipeline has one
private state entry and one active claim. It can still overlap independent pipelines. State shared
by concurrent pipelines belongs behind a synchronized boundary. Shared inline memos requiring
partial reads retain the eligibility rules under [Inline caches](#inline-caches-cycles-and-transactions).

Pause retains or restores every private state entry and logical subscription, including buffered
contributions. Dropping all but one entry would lose state. The initial model keeps entries on their
owning workers; migration requires an explicit ownership transfer and any necessary `Send` bounds.


## Claim lifecycle

The coordinator owns each dispatcher claim until acknowledgment. A worker receives the claim and
executes its shared plan with private state. It does not acknowledge the claim itself.

1. The coordinator reserves an eligible claim and an idle worker. Admission records the claim's
   retention obligations before the worker can read any input.
2. The worker enters the dispatched-run context and incorporates pending notifications for its
   private state. It executes the pipeline with normal `get` calls on upstream reader adapters.
   Breaker and source reads return owned snapshots and release their locks before evaluation
   continues through other operators.
3. The worker computes without holding the destination state mutex. It either applies a contribution
   and its progress together under that mutex, or records a local buffered contribution under the
   [flush protocol](#worker-local-aggregation-and-flushing).
4. The worker calls `release` through its own input producer wrapper. Normal operator forwarding
   translates the output guard into input releases. Shared subscription accounting forwards only
   releases permitted by all outstanding obligations. It records the resulting logical release
   state used by finish and reconstruction. Claim-local release is settled when logical accounting
   accepts it and required forwarding is registered. It does not wait for another logical reader
   to release, or for global data reclamation.
5. The worker reports applied, buffered or failed progress and becomes available for another job.
   An applied outcome means releases are recorded and deferred forwarding is registered as control
   work. A buffered outcome leaves contribution obligations outstanding. Messages carry metadata;
   the coordinator does not merge result tiles or aggregate maps.
6. The coordinator publishes newly available regions, delivers notifications and acknowledges
   claims whose contribution and release obligations are settled. Worker availability and claim
   acknowledgment are separate: buffering must not prevent that worker accepting more morsels.

Filtered and empty results still record decided progress, translate releases through their actual
producer wrappers, and report completion. Bypassing those wrappers would leave `input_released`
and retained inline release state inconsistent. All downstream calls occur after the destination
state lock has been released.

An update can become visible before its worker reports completion. Publication may include several
already applied contributions. It must never declare a region complete while an unapplied
contribution can change it. Each claim remains outstanding until its releases and required
publication are done, even if another completion caused its values to be published.

For example, two claims contribute `A -> [2, 5]` and `A -> [3, 9]` to one sum. Their workers update
the same accumulator, which holds `19` after both writes. The first completion cannot make the
group final while the other contribution remains unapplied. A claim filtering out both rows still
records that its region is decided.

### Worker-local aggregation and flushing

A worker may reuse one local hash map for an aggregate across many morsels. Keys include the full
path, so equal inner keys under different enclosing rows name different accumulators. Local state
also records empty groups, completeness statements and the input contributions represented by each
buffered batch. Only aggregates with a valid partial-combination contract use this mode. Arithmetic,
overflow, duplicate checking and ordering semantics still apply.

A flush transfers contributions exactly once into shared aggregate state and resets or drains the
local deltas while retaining reusable allocation. Resending cumulative snapshots would double-count.
For example, flushing `A → 7` and later adding `3` flushes `A → 3`, not `A → 10`. The shared result
then contains `10`. A supported aggregate combines these deltas with its aggregate operation;
ordinary disjoint-tile merge is not sufficient for repeated contributions to the same key.

A buffered batch remains an outstanding contribution even after its worker accepts another morsel.
Its input may be released once the aggregate contract establishes that the owned local state fully
represents the required information. Claim acknowledgment waits for shared application and the
required release/publication obligations. Acknowledgment records applied contribution progress;
it does not wait for the final value of an entire group. Batch metadata identifies the claims or
regions settled by a flush; source closure alone cannot settle them.

Contribution coverage is separate from input-release accounting. Releasing an input region after
capturing its delta does not make that unapplied contribution complete or obsolete. Obsolete
coverage means the corresponding output is no longer demanded and that contribution was explicitly
discharged under the output-release contract. Only that decision can cancel a buffered contribution;
an upstream release guard cannot substitute for shared application.

Flush triggers include a bounded batch or memory threshold, a group-completion boundary, explicit
publication/control requests and pipeline drain. Control work is serviced within a bounded number of
scheduling opportunities; unrelated ready work cannot starve it. A small buffer cannot wait
indefinitely to reach its batch threshold. Ordered pipelines flush pending contributions before
waiting for acknowledgment to admit their next claim. With no runnable data work, the coordinator
issues flush work to owners of pending buffers before waiting or attempting finish. This rule
prevents a cycle where claims await flush and flush awaits claim acknowledgment. Flush jobs run on
the owning worker and do not make it wait for another worker's computation.

Publishing only at pipeline finish is insufficient for incremental execution. A continuously open
pipeline must have opportunities to flush and publish while it remains open. Terminal finish drains
all remaining buffers; it is the last flush. Partial accumulators may be visible through the native
aggregation-tile contract, but a final scalar for a group is published only after the group closes
and exact coverage proves every required input region applied or obsolete. This includes queued,
not-yet-admitted, active and buffered work. If group membership is unknown until input is read,
the enclosing input scope retains a conservative obligation; an empty active set cannot prove
that group complete.

## Breaker operations and locking

The runtime interface separates input execution, shared-state update, held-state read, output
release and an owned publication view. The reader adapter retains the checks in `TileProducer`'s
`get` and `release` wrappers. A scheduled upstream breaker read observes held state; it does not
recursively execute that breaker's input pipeline.

Initially one mutex protects each breaker's values and their associated progress, releases and
completion metadata. For `MapAggregate`, this includes accumulators, empty enclosing groups and
completeness statements. A read copies the requested held data, or the snapshot needed to construct
its tile, under that mutex. The returned tile owns its data and remains valid after unlocking.

An update respects accepted output releases and cannot recreate a released region. Discarding an
unwanted output still completes its input contribution and retention obligations. Reclamation and
release accumulation form one state operation so a snapshot cannot expose removed data as held.

No operation calls another operator, source, sink or notification consumer while holding a breaker
state mutex. No worker holds two shared data-state locks simultaneously, including source and
retention locks. Each operation computes an owned action under its lock, unlocks, and then forwards
that action through its owner. Release bookkeeping commits the irreversible decision before
forwarding it; later claims cannot acquire an obligation on a region already released.
Readiness, pinning and admission must agree before an upstream release can be forwarded.

`obsolete_guard()` and `completed_keys()` currently return references into a producer. Shared
adapters replace these with owned snapshots or references bounded by a guard. Identity and shape
remain separate from mutable held state. Debug checks may inspect only a consistent state snapshot;
they cannot borrow the live graph while another worker mutates it.

### Releases into another pipeline's input chain

An output release may require forwarding through the released breaker's own inputs. For example,
`Memo::release_impl` and `MapAggregate::release_impl` currently call their input producer's
`release`. That input chain may belong to a different active worker. Unlocking the breaker does
not grant the caller ownership of that chain.

The shared breaker records output obsolescence and pending upstream-release obligations in one state
transition. It coalesces pending guards per logical input using the exact guard algebra. The chain's
exclusive owner takes pending actions between executing data jobs, drops the shared lock, forwards
them through its producer wrappers, and records completion. This boundary means no executing job or
active read on that state entry; buffered claims may remain outstanding. New releases arriving
during forwarding remain pending. Several instances route obligations according to their partition
contract; broadcasting a release must not duplicate or bypass logical reader accounting.

A release never calls directly into another active instance. Initially, the coordinator stops new
admission for the affected pipeline, waits for executing data jobs and reads to leave their private
state, and issues release control work to the owning workers. It does not wait for all buffered
claims to be acknowledged before scheduling flush or release controls. Those workers forward pending
output-driven releases through their private state. Other pipelines continue. This protects
in-flight input reads and ensures release processing can run even when no new data claim is ready.
Before resuming admission, the planner's guard translation must establish which pending work is
still needed and discharge work rendered obsolete without reading released inputs. An unsupported
translation keeps that chain ineligible for worker execution. Ordinary per-claim input releases
still run on workers through logical subscription accounting.

Pending and in-progress forwarding count as control work. They prevent finish completion,
retirement, pause completion and ownership restoration until they settle. A worker reports
completion once the shared boundary has accepted its release; its private state stays on that
worker. It never waits for another executor to forward that release. Output obsolescence takes
effect immediately, so deferred forwarding delays reclamation without allowing further reads of
that output. Processing these actions may create more
releases; draining continues until all such obligations settle. This applies to ordinary breakers
and cyclic stores.

Finishing input execution does not retire the release endpoint. The breaker retains its input
instances or equivalent release state while downstream readers can still release held output.
Late releases after finish still schedule forwarding, without reopening data consumption.

## Retention and logical readers

Release accounting for shared breakers and sources is shared across logical input subscriptions.
Each logical reader records the releases established by its worker contexts. Reclamation intersects
established releases across distinct logical readers and excludes any active or future input demand.
A worker's terminal release retires its private state; it does not make the whole logical reader
obsolete while other or future claims can still read.

Retention belongs to the logical input subscription, not to an OS worker. Its synchronized record
tracks assigned claims, active read obligations and accumulated completed releases. Reader adapters
consult it when worker-local operators release. The destination's `input_released` view derives
from that logical record, not from whichever instance happened to finish most recently.

An active-read count alone is insufficient: pending and future claims can need the same input.
Disjoint output guards can read a common lookup table or function operand. Initially such side
inputs stay retained until the logical reader finishes. Exclusive positional inputs can be released
when their claims complete, provided the operator's dependency mapping proves that remaining work
cannot read them. Pinning on entry to `get` cannot restore data an earlier claim already released.

Instances issue releases through one logical reader with this accounting. They do not independently
release through a shared identity, and they do not each hold a permanent unrestricted subscription.
The former permits premature reclamation; the latter makes instances retain one another's work.
Source producer registrations and `ReadingSource` reader identities follow the same rule.

Logical input completion also finalizes retained operands in every instance. `MapResult` currently
releases its whole function operand only when its local upstream release becomes universal. If two
instances process disjoint halves, neither local wrapper reaches that condition by processing its
own half. Once the logical input is complete, every claim has drained, and finish-time input reads
are complete, the coordinator issues the terminal release through each retained input wrapper,
including idle instances with held operands. Forwarding uses the logical subscription accounting
and settles before final publication, feed closure or instance retirement. The completed scope
supplies the terminal guard; a still-open enclosing scope is not released. A pause with unfinished
logical input preserves its remaining side-input retention. Taking the union of replica guards
alone does not perform this final forwarding.

`FanOut` still intersects releases between distinct logical subscribers. Its subscriber table,
release intersection and compaction are synchronized. Current-value store readers retain the latest
observable value while releasing older history. Registration, slot renumbering and retirement occur
at a drained boundary; ordinary reads, releases and compaction can occur concurrently under the
shared state protocol. Shared sources account for readers in every branch, including paused ones.

## Completeness, publication and finish

Source closure establishes that no new input will arrive. Queued input may still be unclaimed, and
computed input may still be buffered. Completion requires exact applied-or-obsolete coverage of
every required input region. An input-wide final value waits for that coverage across the scope; a
breaker's per-region completion follows its operator's dependency mapping. A breaker with several
inputs records each input's completion separately and performs its final action once all required
inputs finish.

The coordinator requests one owned publication view containing compatible held and decided
regions, completed keys, output releases and output-morsel information. It applies dispatcher
publication deduplication and delivers notifications after dropping the state lock. It does not
assemble that view by separately reading properties while workers can change them. Publication
requests are serialized on the coordinator, preventing out-of-order worker snapshots.

Incremental publication is part of admission. After applying contributions, a breaker can publish
newly available values and completed regions without waiting for its whole input to close. A
notification records its region before dependent work is made runnable. Guard translation and
input-specific readiness determine which downstream claims can run; a sibling field or unrelated
group remaining open must not impose a whole-row or whole-pipeline barrier. Idle worker caches must
observe relevant arrivals before their next read.

`Memo` publishes independently available fragments and their completion information. `MapAggregate`
can flush partial accumulator contributions, but a group's final value requires proof that its input
scope is complete and every input region that could contribute to that group is applied or obsolete.
Queued, not-yet-admitted, active and buffered work all count. Unknown group membership retains the
enclosing scope obligation until resolved. Other groups may remain open when dependency coverage
establishes their independence. If the source cannot establish per-group closure, a final aggregate
for that group necessarily waits for the enclosing scope to close. Synchronizing a hash map does not
prove closure. Partial accumulator tiles and finalized scalar values retain distinct native
contracts.

For example, a map pipeline can publish transformed positions 0–255 while later source positions
remain open. A grouped aggregate can publish a completed outer row while another row remains open.
An unwindowed sum over an open source cannot publish its final scalar; incremental scheduling does
not manufacture that missing completion information.

The coordinator starts finish after input closure, buffer drain and claim acknowledgment. Control
jobs on owning workers perform any operator-specific final reads and state updates through the
normal shared interfaces. `SinkBreaker::finish`, for example, can still require loop output not
consumed by an earlier claim. Closing the queue does not authorize releasing that input before its
final read. Final reads that create contributions settle those contributions before finish proceeds.

After those reads and updates, finish control on each owner performs terminal release forwarding
and reports its settled actions. The coordinator waits for every required owner and deferred
control obligation, checks logical input release conditions, then publishes final output and closes
dependent feeds once. Waiting for another logical reader's eventual global release is not part of
that pipeline's finish condition. These phases require splitting the current finish
operation where its final read and release are intertwined. Input reads and state updates hold no
nested shared locks. Worker completion order does not establish output order.

## Thread-safety changes required

The current value types `Tile`, `TileGuard`, `Predicate`, `Value`, `ColumnValue`, `ScalarProgram`,
`Dispatcher` and `ProbeSlot` already satisfy `Send + Sync`. `Extent`, `Tiling`, `Arrivals`,
`SharedConsumer` and producer trait objects do not. An outer mutex does not make a non-`Send`
producer transferable.

### Runtime ownership and trait bounds

Shared operator plans and runtime reader/writer handles require `Send + Sync`, with `Send` state
inside shared mutexes. Jobs and completion metadata require `Send`. Private state initialized,
used and destroyed on one worker needs no blanket `Send` or `Sync` bound. Moving initialized state
between workers requires an explicit transfer with `Send` bounds on the full reachable state.
An outer mutex cannot substitute for those bounds.

[breaker_reader.rs](tile_operators/breaker_reader.rs) currently shares a complete
`BreakingProducer` through an `Rc<RefCell<_>>` handle. It must separate worker-owned input state
from synchronized held state. Its reader accesses held state without borrowing the upstream
executor. Producer-slot restoration and the sink's `ProducerSlot` must respect the execution state's
owner. Shared plans cannot capture an `Rc<RefCell<Option<Box<dyn TileProducer>>>>` from the compiled
graph.

`ProducerBase` combines private release/debug state with tilings, probes and control handles
([tile_operators/mod.rs](tile_operators/mod.rs)). Keep release checks and last-output observations
private to the instance. Replace runtime shape/source handles with shareable representations.
Replace coordinator-owned routing references with immutable IDs or notification endpoints. Shared
output release and completion state belongs to the breaker, not to one reader's `ProducerBase`.

### Shape, sources and external readings

| Current state | Required runtime representation and coordination |
| --- | --- |
| `Extent::DataSourceDomain` and its `Rc<RefCell<dyn DataSourceDomainExtentImpl>>` | An `Arc` runtime source handle with immutable identity and synchronized access to retained data, domain progress and releases. Workers call its read API directly. |
| `Tiling` and nested `Extent` values | Transferable structural shape, recursively containing only transferable handles. Identity comparison must not lock two source states. |
| `Extent::Restricted` | Shared immutable restriction identity. `Restriction` is currently an empty marker, so it needs no mutable-state mutex. |
| Source buffers, yielded/closed predicates and `ProducerReleases` | A consistent read/release/poll state transition. Register readers before admission; serialize reclamation with reads and release intersection. Return owned columns/tiles. |
| `ReadingSource` | Shared synchronized values and logical-reader retention. Sampling and inserting a value for a site/position are one operation, so two pipelines cannot observe different samples there. |

These handles occur in [extent.rs](types/extent.rs), [tiling_kind.rs](tiling/tiling_kind.rs),
[producer_releases.rs](producer_releases.rs) and [reading.rs](tile_operators/reading.rs).
All concrete source adapters must implement the runtime contract, including HTTP, stdin and test
sources. Source registration in the compilation context and `SourceRegistry` must refer to the same
logical source identities as worker handles.

Polling and I/O ownership can stay on the coordinator. A poller integrates new data into the
synchronized source state, unlocks, then routes notifications. Blocking I/O must occur outside the
state lock. An adapter whose poller cannot move between threads must separate that poller from its
shared retained-data view. A worker source read accesses the shared view directly; it does not
request that the coordinator materialize a tile. Calls involving source shapes or external callbacks
must not introduce nested locks or expose borrowed source data after unlocking.

### Notifications and construction handles

Notification routing remains on the coordinator. Workers never invoke mutable consumer graphs
through copied `Rc` handles. Shared breakers send completion/control metadata; the coordinator
reads their publication state and traverses the normal routes.

| Current state | Required separation |
| --- | --- |
| `SharedConsumer`, forwarding consumers and captured restating closures | Keep mutable routing graphs coordinator-owned. Runtime producers hold route IDs or synchronized notification endpoints instead of pointers into that graph. Closures that move into a runtime instance require `Send`; immutable closures shared by workers also require `Sync`. |
| `Arrivals` shared between `RecordingConsumer` and a producer | A synchronized mailbox that atomically accumulates and takes regions. Each execution instance observes every notification relevant to its private cache; instances cannot compete to drain one mailbox and lose one another's invalidations. |
| `Placement`, `DecidedTarget`, `Entry` | Freeze route targets and tilings for the run before starting workers. Runtime copies contain immutable run-specific metadata. Replanning replaces them only after drain. |
| `FanOut`, `FanHold`, `CycleSlot`, subscription builders and `SubscribeContext` | Mutable compiled wiring stays on the coordinator. A worker may initialize private subscription aliases from its shared plan. Cross-pipeline readers use shared breaker handles and stable logical reader IDs, with no backpointer to the compiled graph's mutable construction cells. |
| `StoreCell` and cyclic fan-out state | Separate the serialized store transition from the shared published snapshot and synchronized deferred releases. Recurrence readers use the explicit snapshot route described below. |

The definitions are in [notifications.rs](notifications.rs), [dispatcher.rs](dispatcher.rs),
[fanout.rs](tile_operators/fanout.rs) and [subscribe_context.rs](subscribe_context.rs). Mutable
construction objects can remain thread-confined if no worker-reachable field retains them.
Runtime recurrence backedges preserve their non-owning lifetime through thread-safe weak handles;
replacing construction references with owning runtime handles must not introduce reference cycles.

A notification records its arrival before making the corresponding claim runnable. The worker
incorporates that instance's pending arrivals before reading its chain. An arrival during `get`
remains pending for the next read; finishing a fill cannot erase it. A take-and-reset mailbox plus
worker-owned cache state provides this ordering only if the fill never clears newer arrivals.
An idle or newly constructed instance must see the relevant notification state before its first
read. No coordinator callback directly mutates a worker-owned cache.

### Inspection, sinks and execution context

`ProbeSlot` in [value_probe.rs](value_probe.rs) already synchronizes observation storage. Instances
need distinct observation identities or a defined aggregation of observations. Dropping an instance
must not detach another instance's probes. Live inspection uses snapshots; mutable graph walks
wait for a drained boundary. Runtime producer and probe IDs distinguish instances; compiler operator
IDs retain their provenance, and logical reader IDs retain their subscription identity.

`DataSink` already requires `Send + Sync`; this alone does not provide delivery ordering or
exactly-once semantics. `SinkBreaker` synchronizes its accumulated answer, terminal flag and
delivery obligations. External sink calls occur after unlocking. Ordered sink pipelines retain
one claim in flight; preserving that contract takes precedence over parallel sink execution.

The debug pull stack and dispatched-run context stay thread-local. Every worker enters them while
executing a chain and unwinds them on failure. Job-local paths and stack addresses must not survive
the job that created them. The coordinator remains the owner of loop/control traversal;
workers receive immutable scope/request identities and synchronized breaker handles.

## Completion delivery and worker capacity

The execution loop drains completions and deferred releases, services control and source polling,
then admits ready work and processes dispatcher actions. While a job, release or completion
obligation remains, `Next::Wait` does not establish a drained boundary. With no other action ready,
the coordinator receives from the completion channel with a timeout for its source/control polling
deadline. That receive observes
completion arriving between an empty-channel check and parking. The coordinator must not wait
solely on `Dispatcher::wait` while acknowledgment depends on processing worker completions.

Each data job reports exactly one applied, buffered or failed outcome. Control jobs report their
completion and the claim obligations they settle. The worker boundary catches a panic and
reports failure; a disconnected completion channel with outstanding jobs fails the run. Workers
send only after dropping all shared locks. Each worker admits one job at a time, and another claim
waits until the coordinator processes the prior completion. Completion capacity is bounded by this
limit. Claims with no available execution instance do not occupy workers waiting for one.

A worker's `get` reads held input for ready work. It does not wait for another pipeline to run or
recursively consume that pipeline under a shared lock. A path requiring such a wait needs a
scheduler-visible suspension before it can run in the pool. Otherwise all workers could wait for
work that only those workers can execute. Unsupported paths retain serial scheduling.

Morsel count does not bound nested tile sizes, persistent inline state or scratch allocation. This
admission limit provides no hard byte bound. Byte admission is a later optimization.

## Inline caches, cycles and transactions

A private inline memo is filled only by its owning execution instance. Its pending arrivals use
the mailbox contract above. A scheduled shared memo has separate input execution and held-state
reads; downstream readers do not fill it while holding its lock. Instance replication must not
duplicate logically shared memo fills or their input contributions.

`Memo::inline` also shares partial input between readers without making its whole output a scheduled
dependency. For example, two readers of `{ready: 7, rows: live_collection}` can read `ready` before
`rows` closes. Converting that memo to a scheduled boundary under current publication rules can
block those reads behind the open sibling collection. Such connected chains remain serial with
their existing inline-fill behavior. Their shared inline state cannot overlap worker reads or
writes. Enabling concurrency requires scheduling that preserves field/projection readiness, or a
separately specified synchronized inline-fill protocol. This proposal does not substitute a
whole-row barrier. That partial-record behavior remains a required regression test during
conversion.

Cyclic store reads use a published snapshot of a completed store transition through the existing
Tile protocol. A failed lock attempt cannot identify recurrence: another worker may hold the lock.
The runtime reader carries explicit recurrence identity and reads the published snapshot without
re-entering the mutation executor. Deferred releases accumulate in synchronized bookkeeping and
settle after the transition; releasing cannot call back into a locked store. These changes are
required before worker pipelines may read a concurrently executing cyclic store.

Transaction writer chains have exclusive attempt state and read shared store snapshots through
producer adapters. Validation, tick allocation, multi-key writes, retry decisions and publication
of the corresponding snapshot remain one serialized store transition. A concurrent map per store
key would not preserve atomic multi-key commits. Worker execution requires a shared attempt plan,
private attempt state and notification/retry routing; replication requires a separate
attempt-partition contract. Unsupported writers remain serialized with their store control.

## Loops, pause and failure

Loop control remains on the coordinator. Before advancing a round, it stops new claims for that
round, waits for its workers, processes completions, publishes body output and drains any work that
publication enables. It advances only when this reaches a fixed point for the round. Independent
pipelines can continue. The parent request remains in flight throughout, so a global outstanding
count is not the round's completion condition. Shared induction state and runtime scope handles
must be synchronized before body workers can read them.

Pause and reload stop admission, finish active operations, flush pending contributions, process
completions and drain notifications. Retained state includes private persistent state, logical
release records and shared breaker values. Worker-private state must remain on its owner or be
exported through an explicit restoration operation before that owner exits. Joining workers and
dropping all their contexts cannot implement a retained pause. An initialized state transfer needs
the full `Send` contract; private reconstruction needs an operator-defined restoration contract.
Only temporary scratch can be discarded. Retained pause/reload remains ineligible until these
operations exist for every affected state entry. Claim IDs and completion messages cannot survive
into a later run.

A worker panic or failed state update stops admission and wakes waiters. Every worker is joined
before teardown. Applied updates are not automatically retried: merging and aggregation can
otherwise double-count after a partial update. A failed run's mutated retained state, including
state shared with other branches, cannot resume through normal pause/reload. Recovery requires a
separate contract. Language exceptions represented as values retain their language semantics.

## Eligibility and rollout

Eligibility is checked for the whole reachable runtime chain: its inputs, source and breaker
handles, notification endpoints, retained state and destination update. Transferable shared plans
and synchronized boundaries permit worker-owned execution state; they do not by themselves permit
reordered contributions. Data parallelism additionally requires exact guard coverage, state
partitioning, logical retention and restoration, and an update whose value and completion semantics
permit reordering.

`Sole` checks local duplicates during accumulation and cross-batch duplicates under the shared lock.
Empty groups whose element type has no `Min` or `Max` identity remain invalid once complete.
Integer `Sum` uses overflow-checking arithmetic in debug builds. Reordering or reassociating
contributions can change intermediate overflow. Ordered admission alone does not make a buffered partial sum safe. Its original fold and
batch boundaries must be preserved, or local pre-aggregation remains refused until a valid
combination contract exists. The current compiled prototype refuses `Sum`.


Implementation proceeds in independently testable steps:

1. Establish shared immutable plans, explicit worker contexts, synchronized breaker/source state
   and logical retention. Admit a finite pointwise pipeline with region publication, allowing its
   dependent pipeline to execute before the producer closes. Publication follows each integrated
   contribution whose output region is complete.
2. Add mergeable aggregate buffers, reusable local maps, flush control and outstanding-contribution
   accounting. Verify per-group finalization and incremental publication while other groups remain
   open. Preserve aggregate arithmetic and duplicate semantics.
3. Run independent claims and pipelines concurrently through the same contracts. Verify shared
   logical subscriptions, pending-demand retention and independent worker cache notifications.
4. Expand stateful chains, transaction writers, loop bodies and retained pause/reload as their
   partition and restoration contracts are implemented. Keep store transitions and recurrence
   rounds serialized.

Workers read their own inputs through the producer protocol. There is no coordinator-materialized
input stage. Each admitted pipeline preserves its incremental contract from its first parallel run.

## Validation

Tests use barriers to force overlap in real `get`, computation, update and release operations. The
serial dispatcher is the comparison for deterministic values, output regions, exact releases and
finish counts. Transaction outcomes follow their permitted ordering contract.

Required cases include:

- A downstream pipeline executes a published region before its upstream pipeline closes, with
  upstream `get` observed on workers and no source lock held across operator execution.
- A worker consumes several morsels into the same local aggregate map, flushes deltas more than
  once without double-counting, and retains reusable allocation.
- All data work buffered with no runnable jobs, proving explicit flush control unblocks drain.
- A group closes while another worker still holds its buffered contribution: no premature final
  value, followed by publication when that contribution is applied.
- A buffered contribution releases its upstream input before flushing, then another contribution
  closes the group: input-release coverage cannot stand in for the missing shared update.
- A closing contribution runs before an unclaimed queued morsel for the same group: completion
  waits for that morsel's applied-or-obsolete coverage, including unknown membership scopes.
- A release control runs while claims are buffered and unacknowledged. It is not blocked waiting
  for those acknowledgments or for a different logical reader's eventual release.
- Ordered checked Sum with shared value `-i64::MAX` and successive morsels `[i64::MAX]`, `[1]`:
  preserving serial fold boundaries succeeds, while reassociating the buffered delta would overflow.
- One logical reader releases while another retains; another worker has pending future side-input
  demand. Shared breaker/source data remains readable until all obligations permit reclamation.
- Two claims of one pipeline using distinct mutable instances, with real overlapping input reads
  and computation and direct writes into the same breaker.
- Same-key and disjoint-key aggregation, nested paths sharing an inner key, empty groups, filtered
  claims and duplicate `Sole` values.
- A delayed earlier contribution with a later closing contribution, proving publication and finish
  cannot pass unapplied work.
- Read/update/release races at shared breakers and live sources, with valid owned snapshots and no
  resurrected released regions. Polling must not hold a source lock while delivering notifications.
- Common side inputs and future claims, with completion and release in different orders. Idle
  instances must neither pin unrelated history nor permit premature reclamation.
- Disjoint `MapResult` instances whose individual releases never become universal, verifying that
  logical completion releases their shared function operand after every claim drains.
- A loop-backed main sink whose final read contributes rows beyond its ordinary claims, verifying
  terminal release cleanup happens after that read and before final publication and closure.
- Wrapper release forwarding through filters and changing key shapes, including logical
  `input_released`, final finish and reconstruction without duplicate work.
- A downstream release while another worker owns the upstream breaker's input chain, and another
  release arriving during deferred forwarding. Idle chains must drain releases without a new data
  claim; finish and pause must wait for every forwarding obligation.
- Concurrent reads of one `ReadingSource` position returning the same sample, with reclamation
  respecting every logical reader.
- Arrivals before admission, during a cache fill and while another instance is idle, with no lost
  notification or direct mutation of a running instance's cache.
- Two readers of a ready record field beside an open live collection, preserving partial reads
  through a shared inline memo without introducing a whole-row publication dependency.
- Multiple inputs finishing once, cyclic snapshots during store mutation, and nested loop rounds
  where publication enables further work.
- Pause/reload after different instances have processed disjoint claims, preserving every retained
  cache, cursor, release and subscription. Probe teardown must not detach peer observations.
- Failure before mutation, during mutation, and after mutation before completion, with no replay
  of partially applied work or normal resumption of damaged state.
- Completion arriving between the empty-channel check and receive, disconnected/failed workers,
  and backpressure with no shared lock held. A full pool must not block on unscheduled dependencies.

Compile-time checks require shared plans and runtime handles to be `Send + Sync`, and jobs and
completion messages to be `Send`. Worker-private state does not cross threads. Coordinator-owned
mutable construction objects stay unreachable from workers. No unsafe thread-safety assertion may
bypass the existing `Rc<RefCell<_>>` dependencies.

## Operator state audit

The following inventory describes the current implementation and the state each conversion must
account for. It is not a claim that every operator is eligible for concurrent execution.

### Pipeline breakers

The implementations are in [aggregate.rs](tile_operators/aggregate.rs),
[fanout.rs](tile_operators/fanout.rs), [extract_final.rs](tile_operators/extract_final.rs),
[rekey_sorted.rs](tile_operators/rekey_sorted.rs), [commit_operator.rs](commit_operator.rs) and
[sink_breaker.rs](tile_operators/sink_breaker.rs).

| Breaker | Shared state | Required coordination |
| --- | --- | --- |
| `MemoProducer` | `cached_tile`, `DirtyRegion`, output releases | Merge each input contribution once. Reads, release compaction and publication use a consistent cache view. A private inline memo has one executor. Shared inline memos requiring partial reads keep their connected chains serial until a concurrency protocol preserves that behavior. |
| `AggregateProducer` | accumulator, released flag, input completion | Update the accumulator atomically with progress. Final extraction waits until every input contribution is integrated. |
| `MapAggregateProducer` | accumulators by full path, empty enclosing keys, `Stated`, releases | Update values and completeness together. Snapshot construction and removal of released groups cannot race insertion or folding. |
| `ExtractAggregateProducer` | extracted value and releases | Extract and insert the terminal value once, with deduplicated publication. Repeated reads return the retained value until release, including reads by different fan-out subscribers. |
| `ExtractFinalProducer` | merged candidates, final value, released flag | Select the greatest source key, independent of worker completion order. Resolve the default only after source completion and all contributions are integrated. |
| `RekeySortedProducer` | output, held key-position pairs, consumed predicate, completed prefix | Advance the output frontier only through the consumed input prefix. A later completed package cannot close an earlier gap. |
| `CommitProducer` | proposal queues, retry sets, writer progress, engine, closed keys, snapshot | Validation, tick allocation, multi-key writes and the resulting snapshot form one commit operation. Concurrent proposal arrival does not permit independent writes to the store's key maps. |
| `InductionStoreProducer` | row engines, seed/row completion, stepped position, snapshot, loop run | Preserve sequential rounds for each recurrence. Body work may run concurrently within a round; advancing the store waits for that round's writes and publications. |
| `InductionDriverProducer` | decoded source, window, emitted/released paths, reseeds, rendered tile | Coordinate source progress with the scope's current request. Multiple workers cannot advance the same recurrence cursor independently. |
| `SinkBreaker` | collected main answer, terminal-delivery flag, output ordering | Emit each package once and finish once. Main output retains its ordered publication contract even if input computation overlaps. |

`MapAggregate` keys its accumulators by full paths. Identical inner keys under different outer
rows name different accumulators. Its empty-group set and completion statements must agree with
those accumulators when a snapshot is built or a release removes a group.

### Other producers and shared boundaries

| Operators or boundary | State and concurrency requirement |
| --- | --- |
| `Constant`, `VariantWrap`, `VariantProject`, `VariantIs`, `RecordWrap`, `SelectField`, `MakeRecord`, `MapResult`, `MapResultToConst`, `MapDomain`, `Uncurry`, `Filter`, `Restrict`, `Product`, `CheckedLookup`, `Lookup`, `PermuteRecordDomain`, `FlattenTupleDomain`, `MapExtractAggregate`, `Union` | Immutable configuration belongs to the shared plan; release/debug state is private to worker execution. Whole-input operands still require shared retention. This ownership classification does not establish that arbitrary guards are independent. |
| `Converse` | Held input/output path mappings and `read`/`seen` predicates persist across reads. Replication must preserve group completeness and forwarding of late releases across package boundaries. |
| `Zip` | Per-arm held paths and emitted pairs persist across reads. Partitioning must preserve matching rows and field-specific releases. |
| `MapResultWithSource` | Its retained nested-input paths remain private to an instance. Worker source lookups and logical source release accounting require synchronized runtime handles. |
| `IterateExtent` | Direct iteration tracks released regions. Cartesian iteration retains each side's keys and release state. Pair enumeration, source arrivals and side reclamation need a consistent view and exact pair coverage. |
| `Readings` | Its `ReadingSource` shares one sampled value per site and position, plus reader retention. Sampling and insertion must be one operation so concurrent readers observe the same sample. |
| `StoreValueStream`, `StoreDenseRead`, `StoreFinalRead` | Reader cursors and released flags remain private to an instance; replicating a cursor requires a partition contract. Store snapshots, key completion and history reclamation are shared. Current-value retention must still protect the value each reader can observe. |
| `TransactDriver`, `TransactWriter` | Windows, taken items, emitted proposals, acknowledgments and retry decisions span calls. Keep each writer's attempt state exclusive until proposal computation is separated from its driver and commit arbitration. |
| `FanOut` | Subscriber identities, release guards, their intersection, current-value retention and the published cyclic snapshot are shared. Slot compaction and subscription changes occur only after active reads and writes drain. |
| Sources | Buffers, logical positions, yielded/closed progress and `ProducerReleases` are shared by reads, polling and reclamation. Polling can retain one owner while synchronized access protects the buffer and its retention. |

## Unified native execution

The production [planner](dispatcher/plan.rs) builds the only execution graph. Its
[worker pool](dispatcher/workers.rs) executes admitted pipelines at every local degree of
parallelism, including one. `CAMBRA_PARALLEL_WORKERS` selects a positive worker count, defaulting to
one; `CAMBRA_MORSEL_ROWS` selects the input claim size. Inspector and control modes use this same
path. Pipeline execution uses the native operator definitions and tile shapes.

`TileOperator: Send + Sync` is the shared immutable definition. Ordinary subscriptions take
`Arc<Self>` and construct the canonical producers once. Every pipeline retains its existing input
chain in a shared cell. Worker initialization creates a cursor over that cell and execution-local
release and validation bookkeeping; it constructs no native producer or input graph.

Stateless producers execute `get_impl(&self, context, guard)` on their existing instances and read
operands through the execution context. Temporary tiles remain on the stack. Stateful converse
retention and zip presence bookkeeping use mutexes on the existing producer; fan-out aliases keep
their existing shared input and release intersection. Exclusive operands use their canonical cell
on coordinator execution and make a chain ineligible for worker execution. Shared breaker boundaries
remain readable through their existing native readers. Source progress and reloads are reflected by
the same graph, without restoring release guards into replicated chains.

The planner checks partition coordinates through the native definitions between breaker
boundaries. Pointwise finite maps, filters, record operations and supported aggregate input chains
can execute concurrently. A converse can partition original input positions beneath its groups.
Operators without a partition contract, source polling, transaction control and loop scopes retain
exclusive coordinator execution inside the same graph. Checked `Sum` and its producing dependency
paths retain their original order, because changing either contribution order or reassociation can
change overflow behavior. Scope dependency paths remain coordinator-owned initially. Transaction
stores and their producing and consuming dependency paths also retain coordinator ownership:
their canonical subscriptions carry execution history that a release frontier alone cannot restore.

Workers call `consume_impl(&self, state, input, guard)` on the existing canonical breaker instance.
`ConsumeState` borrows their input cursor and persistent native aggregation buffers. Workers hold a shared
runtime guard during a batch, allowing concurrent claims while canonical mutations wait. No breaker
instance is constructed per worker. Native coordinator consumption supplies canonical input state to
the same method; coordinator-only control breakers retain exclusive consumption.

Memo caches, scalar accumulators and sink delivery state synchronize their own updates; input
computation runs outside those output locks. A bounded batch contains at most four claims. Grouped
aggregation reuses a worker-local map keyed by full paths, then drains its new contributions into
the shared map while preserving local allocation. The coordinator publishes completed native regions
and acknowledges claims after integration. A completion carries claims, cumulative input releases and intermediate node releases, not a result
tile or map. Dependent pipelines can run while upstream queues remain open.
Input-position guards never stand in for output-group completion.

The canonical input subscription of each shared output breaker owns its logical reader releases.
Worker readers do not forward releases into shared inputs. After native consumption and flushing,
the worker reports its cumulative input release guard and node releases recorded during reads. The coordinator advances the canonical input
at that guard before publication and acknowledgement, combining applied claims from all workers.
Existing fan-out intersections protect other logical readers, and native release transformations retain whole operands until the pipeline no
longer needs them. Both memo and grouped output integration remove already obsolete payload from
late writes under the output lock, preventing released values from reappearing.
Output-driven forwarding into a pipeline's input is deferred while that pipeline is pinned for
active or future queued claims. Local obsolete payload is removed immediately. Ordinary progress
releases after shared application continue, so the pin protects reusable operands without retaining
all consumed input. Finalization releases the pin; pause and failure teardown join workers before
forwarding any deferred releases.


Queue closure and acknowledgement of every claim precede worker-input finalization. That step
releases the canonical input whole and records final aggregate/group completeness before the
native breaker finishes. Finite main outputs merge contributions and restore positional order
within each enclosing row, preserving deletion masks. Live outputs retain their existing ordered
package delivery. A drained live boundary waits for active worker contributions before polling,
pausing or reloading. Worker failures stop admission, join the pool and propagate the failure;
applied contributions are not retried.

Worker readings use their canonical subscription's probe identity. They survive worker teardown,
remain bounded across resumed runs, and retire when that canonical subscription is replaced.
Worker execution IDs remain distinct for execution and debugging. A reading's obsolete guard
belongs to the worker making that observation; global completion and release frontiers come from
the shared native breaker state.

Runtime handles use `Arc`, standard-library `RwLock` and `Mutex`, and synchronized state.
Poisoned guards are recovered to preserve the runtime's existing unwind behavior. Store and sink
guards retain the whole locked slot; typed induction views borrow through the store guard.
Compiler-only source types stay in
`SourceDefinition`; runtime source handles contain no inference graph. Source release records have
an independent synchronized ledger. Reader teardown captures its retirement handle during
subscription, so destruction does not need the source data lock. Notifications and recursive
construction share a standard mutex with per-thread nesting and active-consumer identities. The
thread retains the mutex guard until its last control guard drops, including when guards drop out
of nesting order. Tile computation holds no such gate.

Each reported pipeline records `worker_claims`, `worker_instances`, `workers_used`, `delta_flushes`
and `incremental_claims`. These distinguish configured state, executed work, actual worker use and
claims admitted before an upstream finish.

For example:

```cambra
xs = [1, 2, 3, 4, 5, 6]
[x * 3 + 1 for x in xs if x > 2]
```

Run it with `CAMBRA_PARALLEL_WORKERS=4 CAMBRA_MORSEL_ROWS=1 cambra example.cambra`.
