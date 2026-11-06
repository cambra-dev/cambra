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

Consumer routes describe how input regions reach a pipeline. A route can preserve or restate keys,
or widen a change to the whole input. A widened change supplies no claim that output is complete.
The planner records both the dependencies and the part of the input each dependency can decide.
Operators left in pull mode remain inside a pipeline's chain.

Compilation defers sink pulls until planning succeeds. A planning refusal therefore occurs before
execution consumes anything. Refusals include an already-pulled sink, an unsupported store shape,
a shared producer without the required fan-out, and a live source whose arrivals cannot reach its
pipeline as supported regions. The store restrictions are specified in
[A store as a breaker](design-operators.md#a-store-as-a-breaker).

A static source starts with its unreleased input. A live source announces its decided extent,
including previously yielded regions when a run starts. The pipeline queues only what its breaker's
input has not released. Subsequent polls announce additional progress. Several appearances of one
source do not turn one delivered position into several loop requests.

A route that preserves source positions can admit them as they arrive. A route that requires the
whole source waits until that source closes. A loop or transaction whose source is supplied through
another pipeline also waits for that pipeline to decide each admitted region. Compound source
regions are retained as regions; they are not converted into an invented ordering of rows.

The run alternates source polling and consuming claimable work. When claims drain, it publishes held
breaker output and continues if that makes more work available. A live source can remain open while
the run is quiescent. Quiescence permits an idle callback or pause; it does not imply completion.
The run completes only after every pipeline finishes.

A sink receives each consumed answer. A finite main output collects its packages and emits its final
answer at completion. A live main output emits package answers as they arrive and emits completion
when its sources close. Main-output packages are ordered. Returning several tiles does not change
the collection's value or imply an order among its elements.

`CAMBRA_DISPATCH` enables dispatch, including under `--inspect` and `--control`.
`CAMBRA_MORSEL_ROWS` selects a positive morsel size, defaulting to 1024. An initial planning refusal
can fall back to pull execution in the same compilation context. A refusal after dispatched
execution has consumed state is an error; it cannot restart that state in pull mode.

### Pause and reload

A control request is serviced at a drained boundary. The dispatcher and its run-local scheduling
metadata are then discarded. Retained breakers keep their accumulated values, snapshots and input
releases. A new plan starts with fresh queue and publication records.

To reconstruct runnable work, retained breakers publish what they still hold and sources announce
what they have yielded. Each breaker filters input announcements by its own releases. Dispatcher
queue history is not transferred between versions. Compilation and state inheritance decide which
producers survive a reload; source retention alone does not guarantee that a rebuilt reader can
reconstruct an already reclaimed prefix. Those rules belong to
[program evolution](../ccl/design/program-evolution.md).

The inspector publishes observations without pulling producers. Its version boundary is specified
in [A reload of main is followed](../inspector_model/design.md#a-reload-of-main-is-followed).

## Parking arrivals until a read is decided

An admitted region waits until every dependency has decided the part of that region it supplies.
For example, a loop seeded by `sum(source1())` cannot start from a partial sum. Its source positions
remain parked until the seed is complete.

Parked work contains guards, not copies of rows. The producers retain those rows until consumption
releases them. A region contributed by a push may be split as its dependencies decide parts of it.
A source morsel or a loop's closing row waits whole: its completion is part of the work requested.

A source that never closes can keep a whole-input dependency unresolved indefinitely. This is a
consequence of the computation's dependency, not evidence that the parked region has been consumed.

## Completeness in pushes

Publication communicates two facts: which output regions can supply work, and which regions are
decided. A decided key has a complete value or is known absent. A breaker may have decided more
than it still holds because readers have released some of its output.

| Input relationship | Work region | Decided region |
| --- | --- | --- |
| Preserves keys | Same keys | Same keys |
| Restates keys | Restated keys | Restated keys |
| Depends on the whole input | Whole output | Nothing until the input is wholly decided |
| Depends on several inputs | Regions contributed by each input | Their required contributions must all be decided |

The dispatcher records completeness per dependency and intersects it with that dependency's reach.
A region outside a dependency's reach need not wait for it. A dependency read only by pull must be
whole before it can establish completeness for its reader.

Where one dependency reaches a reader through several paths and a path decides only part of each
row's prerequisites, one union of path regions cannot establish readiness. That dependency must be
whole unless the paths' requirements can be tracked separately. A lookup table also used as input
rows is such a case.

Static ranges are decided at the start. Live ranges publish their decided extent as it grows.
Breakers that publish while consuming announce their decided regions after each consume; breakers
that hold output announce them in a later publication pass. Completion publishes final progress. Ordinary pull-mode
notifications and deferred wakeups do not schedule dispatched execution.

## Reading each row once

A dependent pipeline admits only regions whose required contributions are decided. It records the
regions already admitted so repeated pushes along different paths do not duplicate consumption.
Its readiness rule is the same whether a region arrives already decided or becomes ready after
parking.

A pipeline reading both a live source and another pipeline can receive source arrivals and distinct
rows contributed by that pipeline. A widened push does not supply another copy of source rows.
Releases of the breaker's input record which consumed regions remain unnecessary across runs.

Closing rounds are explicit repeated reads. The last value of a nested row does not establish the
row's end, and an empty row still has completeness to deliver.

## A loop in rounds

An induction store owns its accumulator, published snapshot and optional run-local controller.
The request, body and store-step pipelines share the program's dispatcher. The controller maps
those pipelines to the store for one run; it does not retain a handle back to its own store cell.

A request remains unacknowledged until all its positions and any closing round have stepped. Each
position first runs the body, publishes held output, and then steps the store. The next position
cannot pass that step. A nested request remains outstanding until its row finishes, so the outer
step cannot pass an unfinished inner row. Other independent work remains claimable.

Quiescence alone does not permit a step: a body breaker can hold decided output it has not yet
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
inside the round supports the requested level; consuming breakers check their own input chains.
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

The dispatcher can be shared between workers. Package claims use atomic reservation and claim
counts; no two claims receive one package. Ordered pipelines permit at most one package in flight.
Claiming a finish also reads the consumed region under its lock. Append, readiness publication and
sleeping have their own synchronization; the dispatcher is not wholly lock-free.

A waiter observes a generation before scanning for work. Every transition that can make work
claimable or end the run advances that generation and wakes sleepers. A change between scanning and
waiting therefore cannot be lost. A worker failure wakes waiters and stops further claims.

These guarantees concern scheduling. Breakers use `Rc<RefCell<_>>`, and the production driver runs
them serially. Several pipelines can share one breaker, whose consumes, offers and finishes would
need additional coordination before parallel execution. Atomic-ordering proofs and queue storage
mechanics are documented beside their implementation in `dispatcher.rs`.
