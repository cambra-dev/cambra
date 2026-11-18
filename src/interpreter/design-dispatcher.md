# Pipeline dispatch

The dispatcher schedules regions of pipeline inputs. Producers and breakers own values and release
state; the dispatcher owns work queues and progress for one run. The operator protocol is specified
in [CCL Operator Specifications](design-operators.md#the-producer-protocol).

## The dispatcher

A pipeline consumes one input of a breaker. A breaker with several inputs has several pipelines;
those pipelines share the breaker's output progress. A work package names a region of that input,
not the region of the upstream operator that originally announced it.

A source pipeline receives packages from the run's source driver. A dependent pipeline receives
regions restated through its input chain. A pipeline can receive both kinds of work. Several readers
of one producer require a fan-out so one reader's release cannot reclaim another reader's input.
The pipeline dependency graph is acyclic; loop requests represent recurrences within that graph.

A package consumes the requested region and releases the input the breaker has taken. A breaker
that publishes while consuming then announces its held output and completeness before the package
is acknowledged. The driver lands those pushes after releasing its borrow of the breaker.
No tile passes through a dispatcher queue.

A breaker that does not publish while consuming acknowledges individual packages before a later
held-output publication pass. A loop waits for that pass before releasing step dependencies: package
acknowledgement alone does not settle the round.

The morsel size controls cuts where a region has an enumerable ordered set of held keys or finite
runs of source positions. Regions that cannot be cut this way remain whole. It is not a hard limit
on all package sizes, bytes, or nested values. Cuts partition a region exactly; keys known absent
remain covered, and keys released whole are excluded. A reader reached along several paths queues
each region once, except the explicit repeated reads of loop closing rounds.

An ordered pipeline consumes one package at a time in queue order. A source's optional outstanding
package limit delays admission while the limit is reached. One admitted notification can contain
several morsels, so the limit bounds admission rather than the size of that notification.

## Running a compiled program

The planner walks the subscribed producer graph from its sinks and main outputs. Each consuming
breaker ends a pipeline. The nearest upstream breakers supply its dependencies; a shared breaker
has one identity across all paths that reach it. A transaction store has a pipeline for each input,
and an induction store has request, body and step pipelines.

The plan holds each ordinary breaker through its subscription's shared cell. The producer chain
holds a forwarding reader of that cell; package consumption and publication borrow the cell
without walking from a sink or store root. Shared paths identify a subscription by its cell.
Cyclic stores retain their existing store cells, including deferred releases at mutable borrow
boundaries, and sink breakers remain owned by the run's target list. A loop's body members hold
the same breaker cells as their readers. Run teardown drops these handles while retained producer
chains preserve subscriptions across reload.

Consumer routes describe how input regions reach a pipeline. A route can preserve or restate keys,
or widen a change to the whole input. A widened change supplies no claim that output is complete.
The planner records both the dependencies and the part of the input each dependency can decide.
Operators without their own pipeline read their inputs inside a scheduled pipeline's chain.

A route is what `Consumer::notify` does to a push. The planner walks each read's pushing consumer
with a routing landing (`Landing::route`) over the regions `pushes_of` builds from the pusher's
output: at each collection level the path of one key per level, and beneath the outermost level one
key under every key above it. It walks them as changes, adding a change of every key, and twice as
complete regions, of a source not yet wholly complete and of one that is, adding `Everything` of the
latter (`walk_routes`). The
landing records each entry a walk reaches, whether a consumer on the way widened the push, and the
two marks a consumer sets inside `notify`: a complete region naming only part of what a row depends
on (`Landing::completing_part`), and a key read only once final (`Landing::requiring_final_key`).
The dispatcher keeps the routes per read (`Dispatcher::plan_routes`). A nested loop's drive records
its source's complete regions at the loop's pipeline; the walks of the body around the loop pass it
while they run (`build_scope`).

Each package the dispatcher queues must match a change route with the same marks, widened exactly
as the package's push is, and each complete region a read records must match a complete route with
the same marks (`Landing::queue`). A push that queues nothing is not checked, and nor is a store's
complete region that reaches its own pipelines around its recurrence. A consumer that delivers a
push along a path its walk did not take fails the run where the push is queued
(`a_push_along_a_route_its_planner_did_not_walk_fails_the_run`).

Compilation builds the subscribed graph without executing its outputs. A planning refusal occurs
before execution consumes anything. Refusals include an unsupported store shape,
a shared producer without the required fan-out, and a live source whose arrivals cannot reach its
pipeline as supported regions. The store restrictions are specified in
[A store as a breaker](design-operators.md#a-store-as-a-breaker).

A static source starts with its unreleased input, cut over the positions left, so a source released
whole closes with nothing queued (`Dispatcher::start_source`). A live source announces its complete
extent, including previously yielded regions when a run starts. The pipeline queues only what its
breaker's input has not released. Subsequent polls announce additional progress. Several appearances
of one source do not turn one delivered position into several loop requests.

A route that preserves source positions can admit them as they arrive. A route that widens them
reads its whole input again after each delivery and once more after the source closes ([Reading a
widened input again](#reading-a-widened-input-again)). A loop or transaction whose source is
supplied through another pipeline also waits for that pipeline to decide each admitted region.
Compound source regions are retained as regions; they are not converted into an invented ordering of
rows.

The run alternates source polling and consuming claimable work. When claims drain, it publishes held
breaker output and continues if that makes more work available. A live source can remain open while
the run is quiescent. Quiescence permits an idle callback or pause; it does not imply completion.
The run completes only after every pipeline finishes.

A sink receives each consumed answer. A finite main output collects its packages and emits its final
answer at completion. A live main output emits package answers as they arrive and emits completion
when its sources close. Main-output packages are ordered. Returning several tiles does not change
the collection's value or imply an order among its elements.

The binary runs every program through the dispatcher, including under `--inspect` and `--control`.
`CAMBRA_MORSEL_ROWS` selects a positive morsel size, defaulting to 1024. Compilation builds the graph
without executing sinks. A planning refusal reports an error before execution.

Transaction and induction drivers sample the store's committed snapshot. The planner waits for
seed opening before admitting their source items. Transaction replies commit as taps and are
rekeyed from commit ticks to their original source positions.

A transaction store is notified of a delivery's keys as its writer's items, read off the extents of
its input and its live ranges (`store_items`), since a writer may read its source through requests
no push climbs. Where the input's domain is the live source's own, a delivery's keys are the items.
Over a concatenation a live range's positions stand under every arm whose extent is the range's
(`Notifies::Items`), and an arm whose extent reads no live source, as a list arm, is queued whole
with the first notification, so its items commit before the source delivers anything, unless the
store waits for its seed or for a pipeline it reads. A tagged guard is not cut into morsels, so a
delivery is one package of the store at any morsel size. A store with an arm of any other extent, as
a union nested under a tag, takes its input whole once its sources close. A store that reads its
items through another pipeline takes them as that pipeline's positions where its route to the store
is an identity. Rebuilding a feed reader across reload can replay values emitted before the cut. A
live collection inside a record or a nested row reaches its reader before the source closes through
a read of a widened input ([Reading a widened input again](#reading-a-widened-input-again)).

### Pause and reload

A control request is serviced at a drained boundary. The dispatcher and its run-local scheduling
metadata are then discarded. Retained breakers keep their accumulated values, snapshots and input
releases. Store finish counts restart for each run. A flat induction store publishes a ready seed at
a drained boundary even before its first source position, so an idle version can hand its carried
value to a later version. A new plan starts with fresh queue and publication records.

A drained boundary has no claim in flight (`RunObserver::drained`): no package is claimed and
unacknowledged, and no pipeline's finish is claimed and incomplete. A claimed package's consume or a
claimed finish has begun on breaker state, and the reconstruction below does not repeat it. A loop
scope's open request is its store pipeline's claimed package and its pending finish is that
pipeline's claimed finish, so the condition covers every scope, nested ones included. A package
queued or waiting for its inputs that no claim took is rebuilt by the reconstruction. `drive_live`
reaches the boundary once nothing is claimable and `Execution::resume` makes no progress. A root,
body or step claim completes within the claim. An open request completes only through further
rounds, steps or settlements, so one still open at the boundary is a loop that cannot progress. A
debug build asserts the condition at every drained boundary, whether the run pauses there or
continues (`Execution::assert_nothing_in_flight`). Each loop's opening step
(`InductionRun::opened`) is run-local, so the next run repeats it; a loop paused between batches
answers each position once (`a_run_paused_at_every_boundary_answers_each_arrival_once`).

To reconstruct runnable work, retained breakers publish what they still hold and sources announce
what they have yielded. Each breaker filters input announcements by its own releases. Dispatcher
queue history is not transferred between versions. Compilation and state inheritance decide which
producers survive a reload; source retention alone does not guarantee that a rebuilt reader can
reconstruct an already reclaimed prefix. Those rules belong to
[program evolution](../ccl/design/program-evolution.md).

The inspector publishes observations without pulling producers. Its version boundary is specified
in [A reload of main is followed](../inspector_model/design.md#a-reload-of-main-is-followed).

#### What a pause and a reload keep

A pause keeps the operator graph and drops the plan. Each breaker keeps its accumulated value,
snapshot and input releases, and each fan-out keeps the release guard of every slot.

A reload also keeps what the previous version's operators hold at the nodes the new version
corresponds to. What it rebuilds starts from handovers:

- A kept fan-out drops the slots of the readers the reload retired, and a new reader's slot starts
  at what the fan-out has released (`FanOutShared::released`).
- A source starts a new producer where the replaced version's producers stopped
  (`ProducerReleases::carry_to_new_producers`).
- A rebuilt store is seeded from the value its variable held (`Offer::mutable_state`).

A `PipelineId` names a position in one plan, and every plan numbers its pipelines afresh. Each
pipeline's queue, `pushed` region and completeness are discarded with the plan, including for a
pipeline whose operators a reload keeps, and run cleanup clears the placements the plan set.

Control waits for one pass. `drive_live` polls each live source once, then claims until a
`Next::Wait` at which `Execution::resume` and publishing held output make no progress. During a
dispatched run the binary reads the control port only in its observer's `drained`
(`Driver::drained` in `src/main.rs`). Everything the poll admitted, what it causes downstream, and
every round of a loop request it opened run before a control request is seen. `CAMBRA_MORSEL_ROWS`
bounds a package, not a pass, and no live run sets a source's limit on outstanding packages
(`Dispatcher::limit`).

Between two claims the serial driver may retain a loop or transaction scope's open request.
A loop request's state is `InductionRun::request`, which lives on the store producer and which run
cleanup drops (`InductionStoreProducer::clear_run`). A pause between claims would have to keep it on
the store and re-key its package, which names a queue index in the old plan, to a region of the
store's input. This is a conjecture; nothing implements a pause between claims.

### A run that unwinds

A run that unwinds restores the graph's ownership and nothing more. `ClearsPlacements` clears the
placements a loop's planning pass sets for its probes, `Planner`'s `Drop` clears the entries the
planner placed, `SinksUnplacedOnUnwind` unplaces the sink consumers, `ScopeRuns` drops each
loop's and each transaction writer's run, `run_program_into` puts the `main` output's producer
back (`MainGivenBackOnUnwind`), and `LiveProgram::run` puts each branch's back (`TakenMains`).
The state an operator advanced before the unwind, a cache, a consuming breaker's accumulation, a
store, or the region each queue consumed, stays as it was, so the graph can be planned again, but a
run of it answers from that state: a graph whose run unwound after its first package is compiled
again rather than run again. A run that finishes keeps the placements outside its scopes' bodies,
as `run_targets` leaves them, and a scope's body is unplaced once it finishes (`Scope::resume`). A
paused run unplaces them ([Pause and reload](#pause-and-reload)).

## Waiting for input completion

An admitted region waits until every dependency has completed the part of that region it supplies.
For example, a loop seeded by `sum(source1())` cannot start from a partial sum. Its source positions
remain waiting for inputs until the seed is complete.

Work awaiting input completion contains guards, not copies of rows. The producers retain those rows until consumption
releases them. A region contributed by a push may be split as its dependencies decide parts of it.
A source morsel or a loop's closing row waits whole: its completion is part of the work requested.

A source that never closes can keep a whole-input dependency unresolved indefinitely. This is a
consequence of the computation's dependency, not evidence that the region awaiting input completion has been consumed.

## Completeness in pushes

Publication communicates two facts: which output regions can supply work, and which regions are
complete. A complete key has an immutable value or is known absent. A breaker may have completed more
than it still holds because readers have released some of its output.

| Input relationship | Work region | Complete region |
| --- | --- | --- |
| Preserves keys | Same keys | Same keys |
| Restates keys | Restated keys | Restated keys |
| Depends on the whole input | Whole output | Nothing until the input is wholly complete |
| Depends on several inputs | Regions contributed by each input | Their required contributions must all be complete |

The dispatcher records completeness per dependency and intersects it with that dependency's reach.
A region outside a dependency's reach need not wait for it. A dependency read only by pull must be
whole before it can establish completeness for its reader.

Where one dependency reaches a reader through several paths and a path decides only part of each
row's prerequisites, one union of path regions cannot establish readiness. That dependency must be
whole unless the paths' requirements can be tracked separately. A lookup table also used as input
rows is such a case.

An operator replacing a value preserves notifications above that value's level. A change beneath
it names the enclosing rows. A complete region beneath it passes only where it decides the whole
value. A nested store publishes completed enclosing rows; a final read retains those row keys and
participates in the body's pipeline dependencies, so the outer step waits for the read's value.

Static ranges are complete at the start. Live ranges publish their complete extent as it grows.
Breakers that publish while consuming announce their complete regions after each consume; breakers
that hold output announce them in a later publication pass. Completion publishes final progress.
Notifications queue dispatcher work; no deferred wakeup schedules work.

## Reading a widened input again

A pipeline that a live source reaches widened reads all of its input again after each change,
where its breaker reads an open input (`Breaker::reads_open_input`). A sink does, a memo does, and
so does a `main` output that hands each package's answer. Such a breaker releases what each answer
makes releasable (`Tile::to_guard`), and the next read answers the rest; a memo also caches the
open keys it read and merges what they gained.

A read again is a package of the universal guard that records no region
(`Queue::append_read_again_locked`). It discharges what its breaker releases, not its guard, so
neither deduplication nor the finish check counts it, and the next read takes what it left open.
It asks for the universal guard rather than for what is unreleased, because the unreleased region
can name keys beneath the outermost level or within a record, where a widened operator cannot be
pulled.

Three events queue a read again:

| Event | Pipeline | Entry point |
| --- | --- | --- |
| A delivery | A source pipeline notified of its whole input | `Dispatcher::notify_again` |
| A push that reaches it widened | A reader that waits for its inputs and takes no arrivals | `Dispatcher::read_again_on_widened_push` |
| A change | Either, where the consume of a read again in a pipeline it reads pushed one | `Dispatcher::land_change` |

The consume of a read again pushes a change through its breaker's consumer, because what the
breaker answers may have grown where it completed nothing, or in a region no projection spells,
such as a record whose collection field grows. The change queues a read again for each reader that
reads its input again and does not follow the pipeline that pushed, and nothing else; it records
nothing as pushed. The operators on its way learn of it as of a delivery and mark inline caches
dirty.

No read again is queued while one of the same pipeline waits unclaimed, since that one reads
whatever arrived before its claim. A live run consumes on one thread (`drive_live`), so no two reads
of one open row run at once.

Every widened pipeline also reads its input once every source yields everything, held until the
inputs it waits for have completed it. That read carries the obligation the finish checks: it takes
what no read again took, such as rows an input that reaches it widened completes after the last
delivery.

A push names a projection of the breaker's keys. Where the region a breaker completed holds cells
beneath a row besides whole keys, the push names the keys (`spelled_part`). A region no projection
spells is pushed once one does, at the latest once it is whole (`Pushes::push_final`), and a finish
that leaves one fails the run. Before then only a reader that reads its input again learns of it,
through the change.

A sink's release follows the release contract: a plain value held under a key is complete once
there, so a read can release a row whole. A field selector states complete each row it holds where
the field it selects is plain (`Tile::state_held_values_complete`). Its input states a row complete
only once all its fields are, so without it `[p.0 for p in xs]` over rows whose collection field
grows would answer no row complete. A sink's or a `main` output's producer that its reader released
whole has handed all it holds, so where its pull at the run's finish does not state it complete, the
finish states it complete (`pull_at_finish`, for `SinkConsumer::complete` and
`SinkBreaker::finish`).

A breaker that folds or extracts what it is handed, or steps until its guard is released, reads
its input once, after every source yields everything. An aggregate, an extract and a store are
such breakers, so a final sum still waits for the input it needs.

## Reading each row once

A dependent pipeline admits only regions whose required contributions are complete. It records the
regions already admitted so repeated pushes along different paths do not duplicate consumption.
Its readiness rule is the same whether a region arrives already complete or becomes ready after
waiting for inputs.

A pipeline reading both a live source and another pipeline can receive source arrivals and distinct
rows contributed by that pipeline. A widened push does not supply another copy of source rows.
Releases of the breaker's input record which consumed regions remain unnecessary across runs.

Closing rounds are explicit repeated reads. The last value of a nested row does not establish the
row's end, and an empty row still has completeness to deliver.

A read of a widened input again is a repeated read too, and admits no region
([Reading a widened input again](#reading-a-widened-input-again)): the regions recorded as admitted
stay those of the packages whose guard is their obligation.

A breaker's `complete()` is authoritative. It preserves completion after payload reclamation.
`final_guard()` derives the region available for publication, accounting for release and resumed
store positions. The dispatcher's per-dependency completion is a cache of this statement after
notification routes translate it into the reader's input coordinates.

Publication and admission retain separate histories. `pushed` names output already published and
can be shared by several writer pipelines. Queue `region` names input already scheduled, including
acknowledged packages. Admission subtracts that history and the region awaiting input completions under the same
queue lock. A cached union of guards currently awaiting input completion avoids scanning the backlog on each
arrival; making waiting work ready rebuilds that union from the remaining packages. Moving a region from waiting for inputs into the queue holds the lock throughout, so another
arrival cannot admit it during the transfer. Repeated loop rounds bypass ordinary deduplication
and remain distinct packages.

Ordered pipelines claim only while the queue's in-flight map is empty. Acknowledgement records
consumption and updates its counter before removing the entry and unlocking the next claim.
Graph composition requires every reserved package to remain ready, so neither an in-flight nor
an acknowledged package can enter a newly composed graph.

## Transaction requests and attempts

A writer's request retains the delivered source region while an attempt runs. As for a loop
scope, request and step handlers bound the recurrence: both kinds of scope sit behind
`Handler::Request` and `Handler::Step` as a `Scope`. Both keep their inner pipelines in a `Body`
(`loop_scope.rs`): the planned graph, its members and entries, the driver, and where execution
appends the graph to the run's shared dispatcher (`Execution::attach_body`). The driver, body
breakers and writer are ordinary pipelines planned by the same dependency and notification rules as
other pipelines. The main claim loop consumes them; transaction control queues work and never
claims or consumes a body pipeline itself.

The driver samples the committed store and publishes attempt rows. Each row carries its source
item's position and the sampled frontier. Body pipelines publish the decision, and the writer
publishes a proposal against that same frontier. The step follows the body's pipelines and waits
for their output to settle before collecting proposals and validating them. A stale proposal
records a retry in the store tile and queues another attempt against the new snapshot. A parent
request is acknowledged only after its source region is released and its decisions are settled.

Completing a writer includes the finish's attempt, so its body observes source completion. Source
pipelines then close; normal finishes drain the body graph before the request pipeline finishes. A
writer's attempts are for no request, one request, or the finish (`Attempt` in
`transaction_scope.rs`). The body holds the scope's finish until its pipelines and step have
finished (`Body::take_finish`), for a loop as for a writer.
Run cleanup removes the transaction metadata and its placements, as it does for loop scopes.
Transaction control retains no dispatcher handle and constructs no additional producer instances.

## A loop in rounds

An induction store owns its accumulator, published snapshot and optional run-local controller.
The request, body and store-step pipelines share the program's dispatcher. The controller maps
those pipelines to the store for one run; it does not retain a handle back to its own store cell.

A request remains unacknowledged until all its positions and any closing round have stepped. Each
position first runs the body, publishes held output, and then steps the store. The next position
cannot pass that step. A nested request remains outstanding until its row finishes, so the outer
step cannot pass an unfinished inner row. Other independent work remains claimable.

Quiescence alone does not permit a step: a body breaker can hold complete output it has not yet
published. The controller publishes held output until no further work appears, then releases the
step's dependencies. The production driver coordinates one claim at a time. The shared dispatcher
does not provide a concurrent loop-settlement protocol.

The first request initializes the store after its drive has read the source. A position package
emits only the next covered position. A nested row also has a closing round, including when it has
no positions. A flat delivery that only establishes absence or source completion can require a
closing round without emitting a position.

Finishing a request closes its body sources and waits for the body and step pipelines to finish.
The store's final publication precedes completion of the request pipeline. Run cleanup clears
controller metadata and entry placements on completion, pause, refusal or unwinding; it preserves
the store's values and releases.

Nested rounds use projections naming full paths. The planner verifies that every operator pulled
inside the round restates the level it is pulled at, which its consumer's `input_level` declares;
consuming breakers check their own input chains.
See [Projections that name a path](design-path-projections.md).

## One finish per pipeline

A pipeline accepts work until all its input feeds close. A source has one arrival feed; a dependent
pipeline waits for its dependencies, and a pipeline receiving both also waits for its arrivals to
close. Closure prevents further reservations.

A finish can be claimed once the queue is closed and every reserved package is acknowledged. Exactly
one claimant moves the pipeline to finishing. The breaker must have released every consumed input
region before its finish. Final output is published before dependent feeds close. The run is done
once every pipeline has finished.

## Claiming from several threads

The dispatcher can be shared between workers. A per-pipeline mutex protects ready packages and
in-flight claims. A claim moves the oldest ready package to the in-flight map; acknowledgement
removes its entry, even when an earlier package is still running. Package indices increase for the
run and are never reused. An acknowledgement must match an in-flight index and guard. Ordered
pipelines permit at most one package in flight. No queue lock is held while an operator executes.

Queue entries retain only ready and in-flight guards. Collection capacity can retain its peak
allocation; it does not grow with the number of acknowledged packages. The accumulated region
remains available for deduplication and finish after package entries are removed. Its size depends
on the shape of that region. Atomic reservation and acknowledgement counts determine outstanding
work and finish readiness; closing freezes the reservation count. An append reserves its indices
only after every step that can panic, so the reservation count never exceeds the packages queued.

A waiter observes a generation before scanning for work. Every transition that can make work
claimable or end the run advances that generation and wakes sleepers. A change between scanning and
waiting therefore cannot be lost. A worker failure wakes waiters and stops further claims, and so
does a panic in a thread that publishes (`notify`, `start_source`, `close`, `land`, `finish`,
queueing a reader), worker or not.

These guarantees concern scheduling. Breakers use `Rc<RefCell<_>>`, and the production driver runs
them serially. Several pipelines can share one breaker, whose consumes, offers and finishes would
need additional coordination before parallel execution. Atomic-ordering proofs and queue storage
mechanics are documented beside their implementation in `dispatcher.rs`.
