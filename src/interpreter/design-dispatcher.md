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

A route is what `Consumer::notify` does to a push. The planner walks a pushing consumer with a
routing landing (`Landing::route`) over the regions `pushes_of` builds from the pusher's output: at
each collection level the path of one key per level, and beneath the outermost level one key under
every key above it (`routes_to`). The walk records each entry a push reaches. The planner reads the
routes for two decisions. A pipeline that no route reaches takes no push of that read, so it is
queued its whole input once every source yields everything. A loop's scope whose reads' pushes reach
its drive as the drive's own positions takes its positions from those pushes
(`keys_arrive_as_themselves`). A probe landing (`Landing::probe`) records where a region lands
without queuing it; a loop's round uses one to name the row each inner pipeline takes (`row_for`).

The dispatcher records, per reader, whether the walk of each pipeline it reads reached it
(`Dispatcher::plan_route`). A push from a pipeline whose walk did not reach the reader fails the run
where it is queued (`a_push_along_a_route_its_planner_did_not_walk_fails_the_run`): the planner
reads that pipeline by pull, and a reader that takes no arrivals is queued its whole input at the
start, so the push would deliver its rows twice. The ids are a graph's own, and appending a graph
offsets them with its other pipeline ids. A walk that reaches a reader that no push then reaches is
not checked.

A breaker publishes only rows whose whole value it has decided, at any level of keys: a package
names keys, never part of a value (`spelled_part`). A record decides its
fields together, so a record row whose collection field is still growing is published once the
record is whole. A reader takes each row once. A store steps only the positions its input has
decided and leaves the rest of a package unreleased.

A pipeline consumes one breaker input, and an entry lands regions of its own input's tiling. A
breaker with several inputs, as a loop's scope with its seed, has entries of an input its pipeline
does not consume. Such a region names every row of the consumed input (`rows_named_in`). The planner
records each pipeline's consumed input (`Dispatcher::consumes_input`) and reads arrivals by the same
rule.

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

A record of values is read field by field, so a pipeline whose input is one is queued, at the
start, each field that no push, arrival or range names (`unnamed_fields`): such a field holds values
its own chain computes, as a constant does, and nothing else reads it.

A route that preserves source positions can admit them as they arrive. A route that widens them
names every row of the input ([A widened push](#a-widened-push)). A loop or transaction whose source is
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
`CAMBRA_MORSEL_ROWS` selects a positive morsel size, defaulting to 65,536. Compilation builds the
graph without executing sinks. A planning refusal reports an error before execution.

Transaction and induction drivers sample the store's committed snapshot. The planner waits for
seed opening before admitting their source items. Transaction replies commit as taps and are
rekeyed from commit ticks to their original source positions.

A transaction store is notified of a delivery's keys as its writer's items, read off the extents of
its input and its live ranges (`store_items`), since a writer may read its source through requests
no push climbs. Where the input's domain is the live source's own, a delivery's keys are the items.
Over a concatenation, a live range's positions stand under every arm whose extent is the range's
(`Notifies::Items`). An arm whose extent reads no source, as a list arm, is queued whole with the
first notification. Its items then commit before the source delivers anything, unless the store
waits for its seed or for a pipeline it reads. A tagged guard is not cut into morsels
(`cut_positions`), so a delivery is one package of the store at any morsel size. A store with an arm
of any other extent, as a union nested under a tag, takes the arrivals its sources' ranges bring, as
any pipeline does. A store that reads its items through another pipeline takes them as that
pipeline's positions where its route to the store is an identity.

A live collection inside a record or a nested row reaches its reader once that row is whole
([A widened push](#a-widened-push)).

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

- A rebuilt reader of a kept fan-out starts at its predecessor's exact release, holes included,
  read off the predecessor's slot. A reader whose predecessor held no slot of the fan-out starts at
  the intersection over the slots (`FanOutShared::released`), which decides only what the input
  reclaims. The slots of retired readers hold that intersection back until the handover settles,
  since a replacement may still start at one
  ([program-evolution.md](../ccl/design/program-evolution.md#where-a-rebuilt-reader-picks-up)).
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
sets the size a package is cut to where its region can be cut, and a region that cannot be cut stays
one package ([The dispatcher](#the-dispatcher)). It bounds no pass, and no live run sets a source's
limit on outstanding packages (`Dispatcher::limit`).

Between two claims the serial driver may retain a loop or transaction scope's open request.
A loop request's state is `InductionRun::request`, which lives on the store producer and which run
cleanup drops (`InductionStoreProducer::clear_run`). A pause between claims would have to keep it on
the store and re-key its package, which names a queue index in the old plan, to a region of the
store's input. This is a conjecture; nothing implements a pause between claims. A run recovered
from breaker copies taken between claims rebuilds the open request instead of keeping it: the
store's pipeline queues what the store has not released, and the loop's next round first runs the
position its drive emitted past the store's decided path (`TileProducer::emitted_undecided`).

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

A scope holds the positions a round or attempt could not decide as waiting for inputs
(`Offered::waiting`). A loop's round decides nothing at a position whose body read an input that is
not final yet, as a sum over a live source. A writer's attempt is held the same way once every
writer has attempted without changing the store, an input's release or the decisions to retry. The
request then ends with those positions unreleased, so a drained boundary holds no claim of it.
A flat loop's request that ends before its drive's source delivers the positions it covers leaves
its undecided positions waiting until the store is terminal
(`InductionStoreProducer::keep_undecided`). The drive reads its source by pull, so the entry in
front of the source queues nothing, and the push that delivers a position wakes the scope instead.

A scope's body entries are placed, and marked the scope's, when the scope is attached for a run
(`Execution::attach_body`), so a push that arrives before the scope's first request, as a live
source's first poll of the run does, reaches them.

A push that reaches one of the scope's entries and that no pipeline there takes wakes the scope
(`Entry::wake`): an unplaced entry, or a placed one whose ingress refuses the sender. The wake offers
the scope its waiting positions, and a placed entry records what reached it (`Offered::grown`). The
next request runs the waiting positions, and its first round or attempt queues what grew on the
pipelines it reached, so they read it. A closing round queues what grew too: it runs its rows'
readers, a nested loop's among them, and a nested loop is offered only the positions its readers
have read. A loop first steps its store over the waiting positions, so its drive emits past the ones
now decided, and runs again the round it left undecided. A push can wake the scope while no
position waits (`Offered::woken`). Positions that begin to wait after such a push are offered once
(`Body::set_waiting`), since the push may have grown an input after the request that left them
undecided read it. The scope's pipeline stays open while positions wait (`Body::queue_offered`).

A release can also end a wait. In a durable run a gate holds a breaker's release until a checkpoint
covering it is durable, then passes it on in a later step, outside any consume
(`src/interpreter/durability/mod.rs`). Such a release can let a producer emit what a scope waits
for, as a transaction drive emits its next item once its last row is reclaimed, but it reaches no
entry, so it wakes no scope. When the run is quiescent, the driver asks its observer to pass on held
releases (`RunObserver::pass_held_releases`). Where the observer answers that it passed one on, the
driver offers each scope its waiting positions again (`Execution::offer_waiting`) and claims again.

A nested loop holds each row the round around it gives it until its drive's source delivers the row
(`Body::ready_rows`). A held row the source has not delivered does not hold back the round around
it, which steps and leaves its own position waiting.

Waiting positions are scope state, which a pause or reload does not keep.

## Morsels of a live source

A pusher cuts what it pushes into morsels of at most the run's morsel size, by its own keys: a
breaker's final push (`Pushes::push_final`, through `BreakingProducer::morsels`) and a live
source's arrivals alike. Each morsel is a package of its own, so the pipeline that reads it takes
them in parallel, or one at a time in key order where it is ordered.

A live pipeline's poll cuts the keys each of its own ranges newly yielded at the keys the range's
source holds (`DataSourceDomainExtentImpl::morsels`, `LivePipeline::poll`), pushes each piece
through the range's consumer, and queues each landing as one package. Only the test source
(`TestDataSource`) cuts; the HTTP and stdin sources queue each arrival as one package. A range
beneath the pipeline's outermost keys, as a nest's inner range is, is cut too: its pieces land as
packages beneath the outermost keys ([Who claims what](#who-claims-what)). The poll pushes a range
whole where its pieces land on overlapping regions of the pipeline's input, as a range re-keyed onto
values its pieces share does (`lands_as_morsels`). Two ranges of one pipeline, as a join's two sides
are, can deliver the same rows, so each morsel is queued less what the poll queued before it.

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

A dependency read only by pull must be whole before it can establish completeness for its reader.

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

## A widened push

A push widened on its way to an entry names every row of the reader's input, and the entry queues
it as it queues any push, named as the rows of that input (`Landing::queue`,
`Dispatcher::rows_named`). No pipeline reads its input again. A reader takes each row once and
final, so a live collection inside a record or a nested row reaches its reader once that row is
whole.

A push names a projection of the breaker's keys. Where the region a breaker completed holds cells
beneath a row besides whole keys, the push names the keys (`spelled_part`). A region no projection
spells is pushed once one does, at the latest once it is whole (`Pushes::push_final`), and a finish
that leaves one fails the run.

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

A breaker publishes each region of its output once, and only once the region is final. A push names
the breaker's final guard less the region its pipeline has pushed before (`Pushes::push_final`).
Pipelines that share one publication, such as a transaction store's writer pipelines, record one
pushed region (`PipelineInfo::pushes_with`). A reader is therefore queued each row once, and the
row's value does not change after the push.

Four records are authoritative:

- **Completion.** A breaker's `complete()` states what it has decided, including keys whose
  payloads readers have released. `final_guard()` derives the region to publish from it, after
  releases and resumed store positions.
- **Publication history.** `PipelineState::pushed` names the output a pipeline has pushed. A push
  subtracts it and grows it under one lock, so two pushes from two threads push disjoint regions.
- **Queue history.** A queue holds its ready packages and those in flight, and counts the packages
  reserved and acknowledged. It keeps no region history and refuses no package as a repeat. In a
  debug build it also records the union of the acknowledged guards for the finish check.
- **Release.** `Breaker::input_released` names what the breaker has released of its input. A
  breaker releases what its input stated complete. In a debug build, a pipeline's finish fails
  unless that release covers every guard the pipeline acknowledged (`finish_pipeline`): a region
  acknowledged and not released holds cells that never arrived.

The dispatcher keeps no completion per dependency and no region of work waiting for inputs. A
position that cannot be decided yet waits in its scope ([Waiting for input
completion](#waiting-for-input-completion)), and the scope queues it again once a push wakes it. A
loop's rounds queue their rows again as packages of their own.

A pipeline reading both a live source and another pipeline can receive source arrivals and distinct
rows contributed by that pipeline. A widened push does not supply another copy of source rows.

Closing rounds are explicit repeated reads. The last value of a nested row does not establish the
row's end, and an empty row still has completeness to deliver.

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
for their output to settle before collecting proposals and validating them
(`CommitProducer::complete_attempt`). The store releases a proposal to its writer only once it
commits, and only then does the drive release the item from its source. A parent request is
acknowledged once its source region is released, which means every decision for it committed, or
once its attempts stall, with the positions it has not decided waiting for inputs.

A stale proposal releases nothing, so its item stays in the drive's window and in its source, and
the request queues another attempt. That attempt publishes the store before its pipelines run, so
the drive reads a frontier past the commit that made the proposal stale and emits the item again.

The store keeps every tile it publishes to its cycle as its snapshot
(`CommitProducer::publish_commits`), and a direct pull answers the snapshot. The store cell is free
while an attempt's pipelines run, so a reader slot can pull the store directly after an earlier
pull read the published tile from the fan-out's cache. Both pulls answer the same tile. An older
snapshot would still hold commit ticks that a release has since reclaimed.

An attempt progresses if it commits a decision, changes an input's release, finds a decision stale,
or finds a writer's proposal stream terminal for the first time. A terminal stream can close a key
and make the store terminal (`CommitProducer::render_store`). A reclaim alone is not progress: it
changes the store without changing what a later attempt reads, because
`CommitEngine::gc_released_prefix` keeps the versions every live position reads and the frontier
stays. A stale outcome counts although it changes neither the store nor a release, because the
drive's retry at the moved frontier reads differently. `Stalls` (`transaction_scope.rs`) counts
consecutive attempts without progress across the store's writers, and the request ends once the
count exceeds the number of writers. An attempt counts only if it was queued since the last attempt
that progressed. The writers' attempts overlap, so an attempt queued before another writer's
progress may have read the store and its inputs before that progress. Its outcome does not show that
an attempt queued now would change nothing.

The rule admits no unbounded run of attempts without a commit. A writer's retry reads a frontier
at or past the commit that made its previous proposal stale, so that commit cannot make the retry
stale. Each of a writer's stale outcomes is therefore caused by a distinct commit, and a writer has
no more stale outcomes than the store has commits. A writer's input release grows only when the
drive releases an item whose decision committed, the positions it decides absent on reading source
news, or the whole source once it is exhausted (`TransactDriverProducer::advance`). A request's
guard holds finitely many items and positions, and the whole-source release happens once. A writer's
proposal stream turns terminal at most once. Past these, each other writer has at most one attempt
queued before the last progress, which does not count. Every later attempt increments the stall
count, so the request ends within twice the number of writers further attempts.

A writer's finish attempt follows the same rule. While the store reports the writer's last decision
stale (`CommitProducer::holds_stale_decision`) and the attempts have not stalled, the finish queues
another attempt. An attempt of a writer that holds a stale decision always progresses: it reads a
frontier past the commit that made the decision stale, so the drive emits the item again and the
attempt decides it. The stall count after that attempt is zero, so the finish closes a writer only
once its decision has committed, which `finish_request` asserts in a debug build. A writer whose
store finish still finds a stale decision in flight fails the run (`CommitProducer::finish`), since
a terminal store would drop the item.

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

A scope queues an offered request only once every pipeline its pipeline reads is quiescent
(`Body::queue_offered`). The push that offers positions also queues packages on the pipelines the
drive pulls its source through, which a worker may still consume. A request begun before they have
would find no position and run a closing round over positions the drive emits later.

Finishing a request closes its body sources and waits for the body and step pipelines to finish.
A loop's step takes arrivals, and its scope closes them once the body is finishing, no step is
pending, and every body pipeline has finished (`Body::close_step_when_settled`). The step reads the
body, and closing on the body's finish alone would let it finish before the scope queues the last
round's step. While the body finishes, the resume pass publishes its inner pipelines' held output
and releases their followers, as while a request is open.
The store's final publication precedes completion of the request pipeline. Run cleanup clears
controller metadata and entry placements on completion, pause, refusal or unwinding; it preserves
the store's values and releases.

Nested rounds use projections naming full paths. An operator pulled inside a round at a level it
does not restate is pulled at the nearest level above that it restates, and its answer is cut to
the round's paths (`TileProducer::get`). See
[Projections that name a path](design-path-projections.md).

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
removes its entry, even when an earlier package is still running. A package whose region meets the
region of a package in flight is not claimed, and the packages behind it wait with it, until that
package is acknowledged (`Queue::claim`). A pipeline can be notified of a region again before its
package for the region is acknowledged, as a reader keyed by one row is at each push of what it
reads, and two packages naming one region would read it at once. Package indices increase for the
run and are never reused. An acknowledgement must match an in-flight index and guard. Ordered
pipelines permit at most one package in flight. No queue lock is held while an operator executes.
A delivery takes no lock beyond what each consumer's own state needs
([The notification contract](design-operators.md#the-notification-contract)).

Queue entries retain only ready and in-flight guards. Collection capacity can retain its peak
allocation; it does not grow with the number of acknowledged packages. The accumulated region
remains available for deduplication and finish after package entries are removed. Its size depends
on the shape of that region. Atomic reservation and acknowledgement counts determine outstanding
work and finish readiness; closing freezes the reservation count. An append reserves its indices
only after every step that can panic, so the reservation count never exceeds the packages queued.

A waiter observes a generation before scanning for work. Every transition that can make work
claimable or end the run advances that generation and wakes sleepers. A change between scanning and
waiting therefore cannot be lost. An acknowledgement advances the generation where it frees an
ordered pipeline's next package or a package held back behind the acknowledged one's region,
returns a limited source's credit, or completes a queue (`Dispatcher::acknowledge`). A pool's
claimant also wakes the others once its claim ends (`Dispatcher::wake_claimants`), so a claimant
that waits on the pool's busy count sees the claim end. A worker failure wakes waiters and stops
further claims, and so
does a panic in a thread that publishes (`notify`, `start_source`, `close`, `land`, `finish`,
queueing a reader), worker or not.

These guarantees concern scheduling. Which thread claims which package, and how a breaker shared by
several threads is consumed and published, is under
[Shared native pipeline execution](#shared-native-pipeline-execution). Atomic-ordering proofs and
queue storage mechanics are documented beside their implementation in `dispatcher.rs`.

## Shared native pipeline execution

A run that names no number of workers takes `CAMBRA_LOCAL_DOP`, or one where it is unset
(`default_workers`). `run_program_with_workers` names the number for one run, as a parameter.
All runs use the same planner, dispatcher queues and native breakers. The coordinator is one of the
run's workers, so a run of `n` workers starts `n - 1` threads. With one worker the run starts no
thread and the coordinator claims every package and every finish itself.

A pipeline owns its subscribed non-breaker producer chain. Its upstream breaker readers share
canonical breaker handles. Workers retain those handles and call the existing breaker's immutable
`consume_impl`; they construct no operator chains, input readers, or secondary topology.
`get` and `get_impl` read the existing operands directly.

A breaker consumes packages at once where it answers `Breaker::consumes_concurrently`: a memo
whose rows hold no nested collection, an aggregate and a map-aggregate whose accumulator holds no
collection level, and a final-value extraction. Each requires keyed input whose keys have an order
(`consumes_at_once`), since a push is cut into morsels in key order, and a function value has none.
A memo whose rows hold a nested collection consumes one package at a time: a merge of its packages'
answers loses the completion each states of its rows' inner collections. A final-value extraction
keeps the row at the greatest key whatever order its packages merge in. A sum folds its packages in
any order by wrapping addition, which a release build's `+` already does, so a sum is the same in
every build and every order. A breaker that requires ordered input (`requires_ordered_input`), as a
store does, and its producing dependencies preserve input order: the planner orders every pipeline
such a breaker reads (`order_inputs_of_ordered_breakers`). So do a loop's store pipeline and every
pipeline it reads, transitively: a loop runs its positions in order and takes a request none of
whose positions is next as one that only closes absent positions, so its input is published in
position order, one package in flight per pipeline. The store's step reads the body and seeds no
ordering, so the body is not ordered by this. Control scopes, sinks, and shapes without independent
position projections keep their coordinator handlers.

A sink's packages are not ordered, so with more than one worker its answers arrive out of key order.
`TestSink` merges them in arrival order and reads the merged value in key order
(`Value::in_key_order`), since a collection's binding order states nothing. A `main` output's
pipeline is ordered and needs no sort.

A worker reads and computes its claimed region before taking the output-state lock. Memo merges
under its cache lock. Aggregates fold received values under the shared accumulator lock.
Map-aggregate folds into its shared group map under one lock. There are no worker-local aggregate
maps or delta-flush buffers.

The native `consume_impl(&self)` integrates output, drops its output-state lock, and releases
consumed input through the existing producer chain.

### Who claims what

A pipeline is **admitted** when all of these hold:

- It is a pipeline of the program over a chain or a pipeline of a loop's or transaction writer's
  body.
- Its packages run at once, or no scope's pipeline reads it.

A pipeline's packages run beside each other where its breaker consumes concurrently and its input is
keyed by ordered keys (`consumes_at_once`). A breaker consumes concurrently unless it opts out
(`Breaker::consumes_concurrently`), as a store, a commit, a loop's or a transaction's driver, a
transaction writer, a commit store's reply tap, a memo whose rows hold a nested collection and an
aggregate whose accumulator holds a collection level do. A package may name keys at any level of
the input. Every producer answers a projection at every level: a pull at keys of a level the
producer does not restate (`TileProducer::restates`) pulls the keys above them at the nearest level
it restates, and the answer is cut to the keys asked for (`TileProducer::get`). A package is always
a projection, which a debug build asserts. A package runs beside the pipeline's others except where
its guard overlaps a package in flight.

A pipeline admitted for the second reason alone is **serial**: the planner orders it, so one package
of it is in flight at a time, on any thread. A worker runs the finish of every admitted pipeline no
scope's pipeline reads. A push into a scope's pipeline offers the scope requests, which the
coordinator queues after the consume or finish that pushed them, so a pipeline a scope's pipeline
reads stays the coordinator's. A loop's drive source offers through its entry instead
(`CompletionTarget`); the coordinator's resume pass queues what it offered.

With more than one worker, two kinds of claimant share the dispatcher:

- A worker thread claims packages and finishes of admitted pipelines only
  (`Dispatcher::claim_where`). It sleeps in `Dispatcher::wait` while none is claimable.
- The coordinator claims any package and any finish (`Dispatcher::try_claim_where`). A claim of an
  admitted pipeline runs as a worker's would (`WorkerPool::consume_on_coordinator`,
  `WorkerPool::finish_on_coordinator`). It also runs the loop and transaction scopes, the resume
  pass ([A loop in rounds](#a-loop-in-rounds)) and the polling of live sources.

### A worker's claim

A worker consumes, publishes and acknowledges its own claim, in that order:

1. It calls `consume_impl` under the breaker's handle held shared. Several workers consume one
   pipeline at once; an ordered pipeline has at most one package in flight.
2. Where the breaker answers `pushes_while_consuming`, as on the coordinator (`consume_with`), it
   computes the pipeline's pushes under the handle held exclusively (`Pushes::push_final`), so the
   push reads the breaker with no consume between the merge of a consume's rows and the release of
   its input. A breaker that publishes only at its finish or in the resume pass pushes nothing here.
3. It lands the pushes with no handle held, then acknowledges the package.

A finish is claimable only once every package is acknowledged, so no claimant holds the pipeline.
The claimant releases a concurrently consumed input whole (`Breaker::finish_parallel_input`) and
runs the finish.

### Bodies on workers

A scope queues a round's packages, and a writer an attempt's, after it releases its store. The scope
computes the round under the store and answers it as a `RoundWork`, which the handler queues once
the store guard has dropped (`Scope::begin`, `Scope::step`). A reader that finds the store held is
answered from the snapshot the store published after its last step (`consume_store`), which is the
store's state until its next step. A reader of the round's first packages therefore finds the store
free and pulls the round's state, not the snapshot from before the round.

A round's step passes only output the resume pass has published. Each scope body has one follower
hold over its inner pipelines and its step (`Dispatcher::add_hold_group`). The coordinator re-holds
a scope's body after each of its own claims (`Execution::consume`). A worker re-holds the body it
consumed in before it acknowledges the package (`WorkerPool::consume`). The resume pass reads the
body's hold before it publishes and releases it only where the hold is unchanged
(`Dispatcher::release_followers_if`). A hold counts each time it is taken, so a release decided
before a worker's consume published fails, and the step waits for the next pass.

### Waiting and stalls

Both drivers claim through one routine (`Execution::claim_until_quiescent`), which ends once every
pipeline has finished, the run has failed, or the run is quiescent. A coordinator claim that answers
`Next::Wait` goes on in this order:

1. While a worker holds a claim, or a package or finish of an admitted pipeline is in flight,
   claimable or finishing (`WorkerPool::may_progress`), the coordinator sleeps in
   `Dispatcher::wait`. A worker counts itself busy once its claim returns; until then the package
   in flight or the pipeline finishing shows the claim.
2. Otherwise it runs the resume pass, and claims again where the pass changed anything.
3. Otherwise, where the generation has not moved since the claim, no claimant can progress, and
   the routine answers that the run is quiescent. A run with no live source panics. A live run
   pushes what its breakers hold and claims again where that changed anything. Otherwise it asks
   its observer to pass on held releases, and where the observer passed one on, it offers each
   scope its waiting positions and claims again ([Waiting for input
   completion](#waiting-for-input-completion)). Otherwise it has reached a drained boundary, where
   its driver polls the sources and tells its observer.

A worker's publication can advance the generation during the resume pass, which then counts as
progress. The coordinator claims again and reaches the same fixed point.

### Lock order

No two threads wait on each other through these rules:

- A thread holding a breaker handle takes only the handles of pipelines that breaker's chain
  reads, shared, and takes a store only with `try_write`.
- No thread waits for a store's blocking `write` or in `Dispatcher::wait` while it holds a breaker
  handle. Pushes land after the handle is released, in `consume_with` and `push_held` alike.
- A landing reaches every consumer through `notifications::notify_shared`, which takes no lock. A
  consumer takes only the lock on its own state and releases it before it notifies another, so a
  landing holds at most one consumer's lock at a time. No consumer takes a breaker handle or a store
  while it is notified.
- Only the coordinator takes a store's blocking `write`, in the scope handlers. While it holds one
  it takes the scope's member handles, where `row_for` probes where a round's push lands; a worker
  never waits on a store, since it reaches one only through `try_write`, so the coordinator's
  store-first order meets no worker waiting the other way. The round's packages are queued after the
  store is released ([Bodies on workers](#bodies-on-workers)).

A wait for a handle is therefore a wait on a thread that holds a handle further upstream and waits
for nothing but handles further upstream still. The pipelines form a DAG, since a loop's cycle runs
through its store, so these waits end.

### Failure and pause

A worker holds a `Dispatcher::worker` guard while it claims. A worker that panics fails the run, so
every claimant answers `Next::Failed`. The coordinator stops claiming, joins the workers and resumes
the worker's panic on its own thread (`a_worker_panic_ends_the_run_with_that_panic`). The
coordinator holds the same guard, so a panic on it wakes and stops the workers. Its panic is caught
until the workers have joined: a worker's panic, which failed the run first, is resumed in its
place, and the coordinator's is resumed only where no worker panicked. A run that returns has not
failed.

A worker thread the system refuses to start leaves the run with the workers already started; with
none, the coordinator claims every package. The coordinator's guard exists only once the workers
are started, so a refusal must not panic: the workers already started would never be stopped.

A run that ends at a drained boundary, to pause or reload, has no claim in flight and none claimable
by a worker. The coordinator ends the claims (`Dispatcher::stop_claims`), every worker's claim
answers `Next::Done`, and the coordinator joins them before the run returns its operators.

Reads and releases lock the retained state they access, without an operator-wide operation
lock. A cache read copies an owned tile under its state lock; computation continues on that
snapshot. Release accumulates obsolete guards under their own lock, then reclaims retained
state through the native callback. Memo cache locks are dropped before forwarding releases upstream.
A memo's release of its input waits for the memo's consumes in flight: a reader of the memo's cache
can release it while the memo's own pipeline still consumes, and a consume either finishes before
the release or finds its region released and reads nothing.
Canonical breaker handles allow shared access to both reads and releases. Stateful control
operators protect their retained state with a mutex because consumption and reclamation mutate
it. There are no worker input-retention pins or deferred worker releases. Workers join before
the run returns its operators on pause, cancellation, or unwinding.
