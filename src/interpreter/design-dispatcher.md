# Pipeline dispatch

## The dispatcher

`Dispatcher` (`src/interpreter/dispatcher.rs`) holds the graph of pipelines, which pipelines each
one reads and so which one reads it, a queue of work packages per pipeline, and the morsel size
`morsel_rows`. A work package is a pipeline, a guard for its breaker to consume, one morsel of at
most `morsel_rows` held rows, and the package's index in the pipeline's queue. The dispatcher holds
no breaker: the driver, `run`, reaches each breaker, with the input of it the pipeline consumes,
through a handle its caller passes, indexed by pipeline, and borrows it for one call at a time.

`Dispatcher::new` refuses a zero morsel size, a graph with a cycle, and a pipeline that reads one
pipeline twice. A pipeline may read several pipelines, and its queue closes at the finish of the
last of them. A work package is a guard of the breaker's own input, whichever
pipeline's push queued it. Several pipelines may read one. The release of one reader would remove
rows from the breaker's state that another has still to read, so readers of one pipeline need a
`FanOut` between them, which the dispatcher does not check.

A source pipeline, one that reads no pipeline, is queued the regions of its breaker's input that
have arrived. `Dispatcher::notify` queues one such region, cut every `morsel_rows` positions where
it names finite runs of positions (`Value::UInt` keys) and whole otherwise.
`Dispatcher::close` says no more of the source's input arrives. A pipeline that reads pipelines can
also take arrivals (`Dispatcher::take_arrivals`): it is notified and closed as a source is, and its
queue closes once both its close and the finishes of the pipelines it reads have happened
([Reading each row once](#reading-each-row-once)).
`Dispatcher::start_source` queues the input whole and closes the source: where the input's tiling
states a finite range of positions for its outermost keys (a `UIntRange`), the dispatcher cuts it
every `morsel_rows` positions, the last morsel open above. Any other input starts as one package at
its universal guard: a sparse source's keys are not known before it is pulled. `Dispatcher::limit`
caps a source's packages queued and not acknowledged: `notify` waits while the
source has that many outstanding, and `try_notify` answers that it did not queue. A notify admitted
below the limit queues every morsel it cuts, so the packages outstanding pass the limit by at most
one notify's morsels less one, for one thread that notifies. A notify returns once the run fails,
having queued nothing.

`run` starts every source whole. It consumes the package at the front of the lowest pipeline's
queue that has one. When no pipeline has one, it finishes the lowest pipeline that may finish, and
it stops once every pipeline has finished.

`Pushes::push_final` pushes what a breaker has decided and its pipeline has not pushed before, its
final guard less the region pushed, one package per morsel the breaker cuts it into
(`BreakingProducer::morsels`); a breaker no pipeline reads cuts nothing. The dispatcher keeps each
breaker's pushed region, which the pipelines of one breaker share (`Dispatcher::share_pushes`). A
push computes the difference and grows the region in one step under that region's lock, so two
threads pushing for one pipeline push disjoint regions, and a push, after a consume or at the
finish, pushes only what no earlier push did. The driver lands a push
made after a consume at once (`Dispatcher::land`), before it acknowledges the package, so a reader
may claim it while the pipeline runs; the finish lands its own push and closes the queue of each
pipeline that reads it, where every other pipeline that one reads has finished. A breaker whose
output is one value, `Aggregate`, `ExtractAggregate` and `ExtractFinal`, pushes one morsel. `Memo`
and `MapAggregate` cut at the outermost keys they hold, in key order (`cut_at_keys`): a cut falls
before every `morsel_rows`-th held key the guard names, the first morsel reaches down from the
guard's lower end and the last is open above. The morsels partition the guard exactly. A key the
breaker states absent rides in the morsel that covers it, so the releases of a reader's input at its
morsels add up to the whole guard, and a reader that is final once its input is released whole, such
as `Aggregate`, becomes final. A released key is in no morsel, because the final guard already
excludes it. A guard naming no more than `morsel_rows` held keys is one morsel. A package is a guard
of the reader's input tiling, as the reader's chain restates the morsel, and `run` asserts in a
debug build that a package fits its breaker's input.

A push lands by climbing the breaker's consumer (`ProducerBase::downstream`) one morsel at a time,
as a projection of the breaker's keys at any level (`Consumer::push`). Each consumer between two
breakers restates the region in its operator's keys, as it restates a notification ([The
notification contract](design-operators.md#the-notification-contract)), and passes it on: a fan-out to every live slot,
a tagged union under the arm's tag. No gate holds a push back, since every pushed region is a work
package, and a consumer that pulls ignores it, so a push wakes no one. The `dispatcher::Entry` at
the input of each breaker the push reaches queues the region, as a guard of that breaker's input
tiling, for the breaker's pipeline, less what is queued for that pipeline already. The difference
and the queue's growth are one step under the queue's lock, so a push that reaches a breaker along
two paths, as a filter reads one memo for its values and its predicate, is queued once. A push an
operator widens to `Everything` on its way fails the run at a reader that reads that pipeline's
pushes (`Landing::widened` marks the path, `Landing::queue` refuses it), since the reader could not
tell which of its keys it names: a reader reached that way reads the pushing pipeline once it has
finished, instead of its pushes. A reader that parks takes no row from such a push, and reads each
row once its reads have decided it ([Reading each row once](#reading-each-row-once)). A push that
re-enters a consumer it is passing through has met a cycle, and fails the run too. A compiled
program's dispatched run notifies no consumer: a producer that caches what it reads reads it again
where a store steps or a live source yields more (`TileProducer::read_again`), and a debug build
checks that no consumer is notified inside the run (`dispatcher::debug_assert_outside_a_run`).
`notify`, its gates and `WakeupQueue` serve pull mode.

`dispatcher::finish_pipeline` finishes a pipeline. It asserts five invariants before it calls the
breaker: the pipeline has not begun to finish, its queue is closed and empty, no package claimed for
it is in flight, every pipeline it reads has finished, and its breaker's input has released every
guard the pipeline consumed. A pipeline consumes only rows its reads have decided
([Reading each row once](#reading-each-row-once)), so its input releases them. The release check is
closed
over the input's tiling (`TileGuard::closed_over`): an input that released a row through the last
position of its finite range of positions has released the row, though the difference of the two
guards names the row's paths past that position. A source's input releases the regions queued for
it; a reading pipeline's input releases only what the guards pushed or queued at the start for it
name, and nothing at all when nothing was; a pipeline that reads its input whole releases all of it.
A debug build also asserts that the morsels of a pushed guard partition it (`partition_gap`), and
that a pipeline consumes each region once: a guard pushed to a pipeline meets none pushed to it
before, except a loop's round, which reads its row again ([A loop in rounds](#a-loop-in-rounds)).

The dispatcher reads a breaker's input `input` through `input_tiling` and `input_released`, the
tiling a package's guard is a guard of and the guard the breaker has released of that input, so a
breaker whose input sits inside a shared cell can answer both.

A compiled program's dispatched run queues no wake-up: `WakeupQueue::request` drops one inside the
run (`dispatcher::in_a_run`). A breaker's reader learns of what it holds through the push.

### Running a compiled program

`dispatcher::run_program` (`dispatcher/plan.rs`) runs a compiled program's pipelines on the calling
thread. It walks the producer chains under the program's sinks and `main` outputs with
`TileProducer::visit_input_producers_mut`, the mutable twin of `visit_input_producers`, and takes
each producer whose `as_breaking_mut` answers one as a pipeline breaker. A breaker's pipeline reads
the pipelines of the nearest breakers beneath it, which are numbered before it, and the walk places
the `Entry` at the breaker's input in the pipeline. A breaker's operator installs that entry when it
subscribes its input (`BreakerInput`), and keeps the consumer it was subscribed with as the one it
pushes to; a store and the induction drive build their entries themselves, since each shares its
consumer with other inputs, a store's with its seeds and the drive's with the store, and a range
(`IterateExtent`) keeps its consumer too. A producer is identified by its address, since
`producer_id` counts per producer type. A breaker a second reader reaches keeps its pipeline, and a
reader that reaches one along two paths, as a filter reads its input for the values and the
predicate, reads it once. A pipeline that reads directly a pipeline another breaker's pipeline reads
is refused, since only a fan-out slot keeps one reader's release from removing what another still
reads. The pipelines of one store's inputs count as one reader: the store reads and releases a seed
once, when it opens. A store is the breaker of a pipeline per input, and a loop's scope of a
pipeline of its own ([A store as a breaker](design-operators.md#a-store-as-a-breaker),
[A loop in rounds](#a-loop-in-rounds)), which the walk plans where it reaches a reader slot of the
store's fan-out (`TileProducer::store_read`). Each package reaches its breaker by walking the chains
again, and the pushes a call makes land once the walk has returned, since a breaker reached through
a fan-out slot is called while the walk holds the fan-out its push climbs.

Before the run, the planner reads each edge from a pipeline to the pipeline that reads it off the
consumers between them (`Consumer::route`). Each consumer declares how it passes a push on without
any region being pushed: a consumer that keeps its operator's input's keys passes the route on, a
tagged union's arm passes it on under the arm's tag, a widening consumer marks it widened
(`Routes::widened`), and the `Entry` of a placed breaker records its pipeline. Where every path to
the reader's entry keeps the keys, or the pushing breaker holds one value, whose push is
`Everything`, a push names the rows of its own keys. Where a path widens them, as a lookup's table
reaches its reader, a push names every row of the reader's input. Either way the reader parks the
rows a push brings until the pipelines it reads have decided them, and reads each once
([Reading each row once](#reading-each-row-once)). A reader reads its input whole
(`Dispatcher::read_whole`) where a pipeline it reads pushes along no route to it, or where no push
and no region queued at the start names a row of its input. Which region of the reader's input a
push names comes from a probe: the read pipeline's breaker pushes `Everything` through its consumer
into a landing that records what reaches each entry instead of queueing it (`Landing::probe`). So
is each range under a reader of pushes probed, such as the positions of a literal arm of a
concatenation. A constant keeps no consumer.
A constant whose keys a reader consumes is one of four kinds, and none brings a key the ranges and
the pushes do not name:

- a list literal's table, the function operand of a `MapResult` over the literal's positions
  (`IterateExtent`), so the positions bring every key the table would;
- bound by a `let`, beneath the binding's `Memo`, whose pipeline is a source and reads its input
  whole;
- empty, which brings no key;
- a scalar, which has one position, so any push to its reader names all of it.

`run_program` refuses, in a debug build, a constant collection beneath a reader of pushes that is
not a function operand. What the ranges bring, less everything the pushes can name, is queued for
the reader at the start of the run as one region (`Dispatcher::queue_for`).

Each sink is the breaker of a pipeline of its own (`SinkBreaker`), planned after the pipelines its
producer's chain reads and read by no pipeline. The walk places the sink's `SinkConsumer` in that
pipeline, so a push that climbs to the sink queues there a guard of the sink's producer's tiling,
as an `Entry` queues one of its breaker's input. A `SinkBreaker` consumes a package by pulling the
sink's producer at the package's guard, handing the answer to the `DataSink`, and releasing the
producer at what the answer states. Pull mode makes the same pull, hand-off and release at the
universal guard. The sink's pipeline is not ordered: a tile carries its keys, and a `DataSink` takes
each answer by key, as `TestSink` merges it and the HTTP sink answers each request by its index. A
package's answer states only its own region complete, so it is terminal only where the package is
the producer's whole input. A sink is done once its producer is released whole, however many
packages that took. The run ends with one pull of each sink, as pull mode's last: the producer
answers from what its breakers consumed and is released whole, so the pull hands the sink nothing
new and finds it done (`DoneNotifier::signal`), which fires `CompiledProgram::done` once every sink
has. The pull closes its answer's outermost statement over the producer's tiling
(`Tile::closed_over`): an answer assembled arm by arm of a tagged union, as a sink fed from two
sites is, states each arm complete on its own, and only the closed statement reads as terminal.

A `main` output's producer is the driver's to pull. The run takes it into a slot and makes it the
root of a sink's pipeline, and hands the producer back after; a program has at most one. The compile
subscribes the producer to the driver's consumer behind an unplaced `Entry`
(`CompiledOutput::main_entry`), which the walk places in that pipeline as it places a sink's
`SinkConsumer`. A push that climbs to the `main` output therefore queues a guard of the producer's
tiling there, and the pipeline plans its edges and its live sources as a sink's does: a map over a
live source at the `main` output is notified of each delivery's keys. The pipeline's `SinkBreaker`
(`SinkBreaker::main`) hands the `DataSink` the caller passes `run_program_into` the output's
answers. With no live source it hands one answer, at the pipeline's finish: the answers of its
packages merged with a pull of the producer at the universal guard, the answer pull mode's one pull
makes. That pull states what the producer states complete and adds no key, since the packages
consumed all the producer holds. Where the output reads a loop's scope, the pull also answers the
rows the loop's rounds have written, each final as it is written (`SinkBreaker::reads_a_loop`). Over
a live source the run finishes the output only once every source yields everything, so the breaker
hands each package's answer as it consumes it (`SinkBreaker::hand_each_package`), and at the finish
the pull's answer, which states the output complete, unless an answer before was terminal. The
pipeline is ordered (`Dispatcher::order`), so it consumes its packages in queue order. The answers
add up to a terminal tile, as pull mode's last pull is. `run_program` passes a `DataSink` that
merges the answers (`Collected`) and answers the merged tile (`Run::main`). The driver holds the
producer, released whole, once the run returns.

The run pulls only the breakers' inputs. The program is compiled with
`GlobalContext::defer_sink_pulls`, which leaves out the pull each sink takes once subscribed, and
`CompiledProgram::sink_pulls_deferred` records it. The planner refuses, before anything runs, with
a `Refused` error that names the shape, and pull mode runs every refused program:

- a program compiled with its sinks pulled;
- a live source whose arrivals reach no pipeline's entry or reach one as a region that is no
  projection of its keys (below);
- a pipeline notified of a live source's arrivals beside a range no live source yields, or beside a
  pipeline it reads whose pushes arrive as its own keys, since no arrival names those rows;
- a pipeline read directly by a pipeline another pipeline reads;
- the stores [A store as a breaker](design-operators.md#a-store-as-a-breaker) lists.

A range over a live source's domain (`TileProducer::data_sources`, an `IterateExtent` over a
`DataSourceDomain`) is no range the run queues whole at its start. The pipeline that stands for it
in the run's dispatcher is live (`Planned::live`), and the run notifies it of what the source yields
in one of four ways (`LivePipeline::poll`):

- Every route from the range's consumer to the pipeline's entry keeps the range's keys
  (`Consumer::route`), and a push of one key reaches the entry as a projection of the input's keys
  at any level, as a `Converse` restates its input's keys one level in: the pipeline is notified of
  the keys each delivery adds, as the region a push of them brings its entry.
- A route widens the keys, as a feed `out << 𝑒` widens its source's keys, which sit beneath the
  sink's one row: the pipeline reads its input whole once every live source under it yields
  everything (`Planned::whole`). The widened pushes of several ranges, as of a sink fed from
  two sites, name their parts of the input together.
- The range is read inside a loop's scope, whose pipeline stands for every pipeline inside it
  (`Planner::members`). Where the range's routes reach the scope's own drive keeping its keys, and
  a push of one key reaches the drive as that key, the scope is notified of each delivery's keys as
  positions of its rounds. Where it reaches no drive of the scope, the source is
  read inside a loop nested in it, whose rows end only once the source yields everything, so the
  scope reads its input whole then, as pull mode waits for each row.
- The range is read under a writer of a transaction store, whose source is the input of the
  writer's pipeline, read behind an entry no planner places: that pipeline is notified of each
  delivery's keys as its items.

A scope or a store that also reads pipelines takes each delivery once those pipelines have decided
it (`Dispatcher::take_arrivals`,
[Parking arrivals until a read is decided](#parking-arrivals-until-a-read-is-decided)).

A drive and a transaction store decide positions in order, and a debug build checks that a delivery
adds positions after every one before it. A dispatched run delivers no notification: a loop's scope
has its drive read its source once the drive has emitted every position it read, and a delivery to a
transaction store has its writer's drive read its source again (`Breaker::read_source_again`). A
package of positions the drive emits none of, such as the delivery that completes a source or one of
keys a filter on its source drops, runs no round of a position; the scope runs a closing round at
the package, queued to every inner pipeline but the sources in the store's chain, which has them
read what the drive read past, and the store's step releases the package. A pipeline other than a
store or a loop's scope whose chain reads a live source and a pipeline takes the source's arrivals
beside the pushes of the pipelines it reads, and parks them
([Reading each row once](#reading-each-row-once)).

The run starts the other sources whole and then polls: each pass asks every live source for new data
(`DataSourceDomainExtentImpl::check_for_new_data`), notifies each live pipeline of the keys its
sources yield beyond what it was notified of (`get_yield_predicate`), and runs what is claimable. A
live pipeline closes once its sources yield everything, and the run ends once every pipeline has
finished. Once a pass's claims run out, every breaker pushes what it holds and no push named, and
the pass runs on while that brings anything: `MapAggregate` pushes only so, and finishes only once
every source yields everything. A run starts with every breaker pushing what it holds
(`dispatcher::push_held`), as a run after a pause or a reload starts over breakers an earlier run
consumed into. A pass that finds nothing new calls the caller's `on_idle` after running what is
claimable (`run_program_polling`): `run_program` sleeps for a millisecond, and a test feeds the
source there. A range reads one source, keyed by positions: the planner refuses a cross product of
sources, a source beside a static extent, and a source with other keys, whose arrivals no region of
one source's positions spells.

The binary runs a program dispatched where `CAMBRA_DISPATCH` is set to anything but `0` or the empty
string, and neither `--inspect` nor `--control` is given, at morsels of `CAMBRA_MORSEL_ROWS` rows
(1024 unset; a value that is no positive count panics). It prints each answer of the `main` output
where the answer holds a key or a value or is terminal, as pull mode prints each pull's answer: a
collection cut into several morsels prints once, and a map over stdin prints each line's answer as
the line arrives. A refused program runs in pull mode after a note on stderr, in the
context the dispatched run compiled it in: the compile has opened its sources and sinks, a port
bound or stdin taken, which a second compile could not open again.

Every program of the differential suite (`tests/it/differential_interp.rs`) runs dispatched too, at
morsels of one row and of every row, and answers what pull mode answers, or the planner refuses it.

### Parking arrivals until a read is decided

A loop's scope or a transaction store steps on the pipelines it reads by pull, and a step that pulls
a pipeline not yet final reads a partial answer: a seed `sum(source1())` before `source1` yields
everything opens the store at a wrong value. A scope or store over a live source that reads
pipelines parks its arrivals (`Dispatcher::park`). A notify of a region that some pipeline it reads
has not decided keeps its morsels out of the queue. Each pipeline's decided pushes record what it
has decided of the reader's input ([Completeness in pushes](#completeness-in-pushes)). The decided
push that covers a parked morsel appends it to the scope's or store's queue, before the pushing
pipeline counts its finish toward the reader's close. From then on each delivery the reads have
decided is queued as it arrives.

The parked morsels are guards of the scope's or store's input, not rows: the rows stay in the live
source, which releases none of them until the scope or store consumes them. Over a seed whose
sources never yield everything, the scope or store never steps, and its source keeps every row it
delivered.

A pipeline that reads its input whole (`Dispatcher::read_whole`) parks that input from the start. A
decided push releases the part of a parked region that every pipeline the reader reads has decided,
and the rest stays parked (`Dispatcher::decided_part`). A transaction store over a let-bound list,
whose list's pipeline is decided before any delivery, reads its input then. A morsel a source's
notify cut counts as one of that source's packages, so it is released whole.

A loop's drive reads its source by pull, behind an entry no planner places in the run's dispatcher,
so a push of the source stops there. The positions the drive emits are its source's keys, so the
entry records a decided push of the source at the loop's scope, as the same keys of the store's
input (`DecidedTarget`, set by `InductionStoreProducer::decide_through_drive`). A loop over a
let-bound list of a live source then steps at each position the list has decided, before the source
yields everything.

### Completeness in pushes

A key of a pipeline's output is decided where its value can no longer change and its presence or
absence is settled: a key present in the output, whose value is complete once it is there, or a key
the domain predicate rules out ([The completeness contract](design-operators.md#the-completeness-contract)). That is
the region `Tile::to_guard` names and `BreakingProducer::decided` states. The decided region enters
the dispatcher as a guard, pushed up the consumer chain beside the region that changed, and the
dispatcher decides that a read is final by guard containment.

Both ends of a pipeline push a decided region:

- A range pushes its decided region each time it grows (`Dispatcher::land_range_decided`). A range
  over a static extent pushes the universal guard when the run starts. A range over a live source
  pushes the keys it has delivered for good.
- A breaker pushes its decided region beside its final guard (`Pushes::push_final`).

A push carries two guards: the region that changed, which a reader reads again, and the region
decided. An operator restates each in its own keys by its own rule:

| Operator | Changed region | Decided region |
| --- | --- | --- |
| keeps its input's keys | unchanged | unchanged |
| keeps them under another spelling (`Uncurry` beneath a standing level) | restated (`scheduler::restating`) | restated |
| looks a collection operand up at each row's own key (`MapResult` over values that equal their keys, as a group-by's) | the rows whose last key it names, under every path (`keys_looked_up`) | the rows whose last key it names, under every path, as a part of what those rows depend on |
| widens its input's keys | the universal guard (`Landing::widened`) | the empty guard, and the universal guard once the input's decided region is universal; an outermost `Uncurry` restates it as the pairs its outer keys head (`scheduler::widening_restating_decided`) |
| reads several inputs (`Zip`, `Filter`, `Product`) | each input's region, as it arrives | the intersection of the inputs' decided regions |

A widened change rounds up and a widened decided region rounds down: every output key of a widening
operator depends on every input key, so none is decided until all of the input is. Each restatement
is exact, as every guard operation must be ([Guard operations are
exact](design-operators.md#guard-operations-are-exact)). The dispatcher intersects the decided regions of inputs that
come from different pipelines, since a step needs each pipeline it reads to cover it. An operator
intersects those of inputs within one chain, as a static arm beside a live arm.

A pipeline that reaches a reader along a path whose decided region names only part of what a row
depends on (`Routes::deciding_part`), and along another path, decides the reader's input only once
it is whole (`Dispatcher::decides_whole_only`). The dispatcher records one region per pipeline, so
it cannot intersect the paths. A widening passes a region that is not whole as nothing, and a
lookup's operand names the rows reading a decided key whatever their input holds. A group-by's memo
is the case: it reads a list both as its rows and as the table of a lookup.

The dispatcher keeps, per pipeline, the union of the decided regions each pipeline it reads has
pushed. A unit of work is claimable once that union covers the region the work pulls, checked with
`guard_minus`:

- a whole read (`Dispatcher::read_whole`);
- a step of a store or a loop's scope over a live source;
- a parked delivery of a store or a loop's scope (`Dispatcher::park`);
- a row a push, an arrival or a loop's round brings
  ([Reading each row once](#reading-each-row-once)).

Loop body pipelines use the same rule in the shared dispatcher, with keys carrying the loop's
position. A nested request takes a round's row once the pipelines its rounds pull are quiescent
(`Dispatcher::follow`), since it reads them by pull and no decided push of theirs reaches it.

In the program below, store `a` reads a static list, and the loop reads a live source that never
yields everything:

```
a: Mut(Int, Txn) := 100
for r in [10, 20]:
    with begin():
        a := a - r
last := await_final(a)
for x in source1():
    last := last + x
out << last
```

The range over `[10, 20]` pushes the universal guard at the start, and `a` pushes its decided region
once it has consumed it, so `a` is final then and the loop steps per delivery of `source1`, with no record of
which pipelines have closed.

A breaker states its decided region in `BreakingProducer::decided`, which is its held region but
for the induction store: the transaction store its positions through its watermark, a memo, a map
aggregate and an induction drive their tiles' `to_guard`, and an aggregate or an extraction
everything once it is final. An induction store holds nothing until it is terminal
(`BreakerState::held`), since a reader pulls its tile whole, but decides its positions one at a
time: its decided region is its tile's statement, the positions it has stepped, row by row under
rows, so a reader of one row of a store per row waits for that row alone.

### Reading each row once

A pipeline's chain can answer nothing for a row whose input is not yet decided. An operator that
reads a sibling input does not answer a row from that input before it is final: `MapResultToConst`
answers no row while its scalar constant is not terminal (`empty_beneath_live_rows`), a binop
combines only the positions both operands hold, `CheckedLookup` answers a missing key only once its
table is terminal, a `VariantWrap` emits a collection payload only once it is whole, and
`ExtractFinal` answers once its source is terminal. The planner keeps a pipeline from consuming such
a row early: the pipeline parks each row a push or an arrival brings until every pipeline it reads
has decided it ([Parking arrivals until a read is
decided](#parking-arrivals-until-a-read-is-decided)), so it reads each row once, final, and its
breaker's input releases what it consumed.

A row waits only for the pipelines that reach it. The planner records, per pipeline a reader reads,
the region of the reader's input that pipeline can decide: what a push of its every key, wholly
decided, lands as at the reader's entry (`Dispatcher::reaches`). A row outside that region does not
depend on the pipeline. A pipeline read by pull, whose push reaches no entry of the reader, reaches
all of its input, and the reader records it whole once it is wholly decided.

Every pipeline that reads another parks the rows its pushes, its arrivals and its start bring, in
the run's dispatcher and in a loop's scope's (`plan_edges`). A push brings the rows it names at the
reader's entry, a widened one every row, less what a push brought before. A pipeline read along no
route is read by pull, so its reader reads its input whole (`Dispatcher::read_whole`), released as
the pipelines it reads decide it.

A pipeline whose chain reads a live source and other pipelines takes the source's arrivals
(`Dispatcher::take_arrivals`), and its queue counts its close as one more event. It is
queued no start region and reads nothing whole.

A pipeline that takes arrivals brings rows only from its arrivals: a push brings it none, since its
arrivals name its rows. A push of one value that names only rows the arrivals bring reaches rows
that wait parked for its decided push.

A loop body reader parks arrivals until its dependencies decide their rows. Its keys carry the
loop's position, so a decided region names the rows of one position. A round queues its row to each
inner reader as a push of the row from the drive lands at the reader's entry, restated by every
operator on the way (`InductionStoreProducer::row_for`), and queues none to a reader whose input has
released the row whole. A row a round queues waits whole until the pipelines the reader reads have
decided all of it, the row's end included, which a closing round's reads state
(`Dispatcher::queue_round`). Every round queues its row whole, whatever it queued before, since a
closing round reads its row again (`Queue::append_again`). A nested loop's scope takes a round's row
only once the pipelines its rounds pull are quiescent (`Dispatcher::follow`), and so does a reader
of a nested loop's scope.

A pull beneath a path over a live source's domain states the source's positions complete only
through those it delivered, not past its last once it is complete, so a reader of a push beneath its
outermost keys does not release those positions.

`[x for x in source1() if sum([1, 2, 3]) > 5]` at `main` takes each delivery's rows once the sum is
decided, before the first delivery. With `sum(source1())` in its place, the rows of every delivery
stay parked until the source yields everything, where the sum is decided.

### A loop in rounds

An induction loop runs one round per source position. Its request, body and ordered store-step
pipelines share the run's dispatcher. The request and store-step pipelines target the same
`InductionStoreProducer`. Its optional `InductionRun` retains the pending request package, current
round and global pipeline IDs. The producer retains the accumulator and its published snapshot;
scheduling metadata contains no handle back to its own store cell. `Dispatcher` queues guards and
tracks claims, acknowledgements and finishes; it holds no loop or operator state. The
`run_program` planner and execution handler live in `dispatcher/plan.rs`.

`Execution` uses one handler table indexed by global pipeline ID. A body handler records its owning
store and breaker address; a request or step handler names the induction store. Lookup reaches the
recorded owner directly.

The planner configures each body graph locally, removes whole-input breakers that must remain in
pull mode, and appends the configured graphs to the run. Composition remaps dependency and follower
indices. The `Planned.rounds` report remains a tree with indices local to each sibling list; those
indices describe planning and are not runtime pipeline IDs.

Each plan installs fresh run metadata through a plan-scoped `InductionRuns` owner. The owner covers
graph construction and execution, and clears run metadata when the plan exits or unwinds. Cleanup
clears body entry placements and keeps engines, snapshots and input releases unchanged.

A scope's request pipeline is ordered. Claiming a request opens its store if necessary and queues
one round. The execution handler retains the request's acknowledgement until every position and
closing round in that request has stepped. Other pipelines remain claimable during that interval.
A nested scope's request names one row of its store and remains in flight until that row finishes,
so the outer store-step cannot pass a pending nested row.

A round proceeds as follows:

1. The store has its cycle's pull-mode operators read again (`TileProducer::read_cycle_again`). The
   previous step pulled them before the body pipelines consumed this position.
2. Explicitly queued source pipelines receive the position. Nested requests and closing-row readers
   receive the region restated at their own input entries. The store-step pipeline receives one
   package for the same round, after those body packages have been queued.
3. The body pipelines consume through the shared dispatcher. Their held and decided output pushes
   land before their packages are acknowledged.
4. Once claims drain, the execution handler has the active scope's body pipelines push held state.
   Followers remain held until that scope's publication pass changes nothing. `MapAggregate` can be
   quiescent while it still holds unpublished groups, so quiescence alone does not release a step.
5. The serial execution driver releases followers for one claim, then holds them again before
   another publication pass. The ordered step follows every direct body pipeline and becomes
   claimable only after they are quiescent. Its handler steps the store and queues the next position
   or closing row.

The execution driver coordinates one claim at a time because breakers use `Rc<RefCell<_>>`. A scope
compares the dispatcher generation only around its own publication pass; no other claim runs during
that pass, so another scope's work cannot be mistaken for one of these pushes.

Body pipelines are held from claims and finishes until their first request activates them. Their
non-source entries then stay placed at global IDs until the scope finishes. Each body entry accepts
pushes only from the configured body graph (`Dispatcher::restrict_ingress`); a push from outside
that graph stops there. Cross-scope dependencies are represented by request pipelines instead of
entering a body outside its current round. A breaker inside the cycle is reached by walking the
store's chain while its cell is borrowed, so recurrence reads use the published snapshot.

The drive (`InductionDriverProducer`) is an explicitly queued source pipeline. Its source entry
stays unplaced; the controller alone queues positions for the drive. The drive consumes at an empty
guard to read its source without emitting a position. A position package emits only the next
position it covers; a consuming pull returns that rendering and advances nothing. A position the
source filters out runs no position round.

The first request has the drive read its source before the store's opening step publishes its seed.
A flat request reads the source again after its buffered positions run out, at most once per
request.
A nested row reads at its start and end. Its closing round queues the whole row to every body
pipeline except the sources in the store's chain, including a row containing no positions. The last
position alone does not state the row's end, so this closing round has every reader observe that
completeness and lets the store release the row whole. A row is restated at each reader's input by
`InductionStoreProducer::row_for`; a reader whose input has released the whole row is not queued it.

A flat package can name positions the source filtered out, or a delivery that only closes the
source.
If it emitted no position and its input remains unreleased, it runs a closing round at that package.
The body pipelines read what the drive read past, and the store step releases those absent
positions.

Finishing a request pipeline closes its body sources. The execution handler retains the finish
until all body and step pipelines have finished in the same dispatcher. The store is terminal then;
its final push lands before the request pipeline's finish releases its readers. A nested store
releases its body a position at a time and each row it decides whole. Its readers release their
rows as they finish with them, and the store's offer cuts rows released since its last step from
the snapshot. A flat store holds nothing short of terminal.

A scope whose store has 𝑑 row levels above its positions runs rounds at paths of 𝑑 + 1 keys
(`Projection::of_path`). The planner asserts that operators its rounds pull restate a projection
at that level (`Planner::unrestated_in_rounds`). This check covers nested loops and stores per
comprehension row. The walk stops at consuming breakers: their consumes pull their own inputs, and
their scopes check those pulls. A breaker left in pull mode passes the pull on. A level violation
panics before execution.

### One finish per pipeline

A run has no batches. A pipeline's queue is open while appends land in it: a source's notifies, and
the pushes of the pipelines it reads, which land as those pipelines consume and at their finishes.
The queue closes at the source's close, for a source, and at the finish of the last of the
pipelines it reads, for a reader, which a count of the pipelines it reads that have not finished
tells. A pipeline that takes arrivals beside the pipelines it reads counts its close as one more
event ([Reading each row once](#reading-each-row-once)). Nothing is queued for a pipeline once its
queue is closed, so it finishes once: a claim hands out its finish (`Next::Finish`) once the queue
is closed and every package in it acknowledged, and a compare and exchange of the pipeline's phase
picks one claim. The finish is the breaker's last call (`Breaker::finish`). It pushes what the
breaker decided and no consume pushed into the queues of the pipelines that read it, and closes the
queue of each whose last pipeline read to finish it is this one. The finish of the last pipeline to
finish ends the run.

A reader learns what a breaker decides from its pushes after each consume, not from a finish: every
breaker pushes while consuming, but `MapAggregate`, whose groups beneath its outermost keys a
reader's chain cannot restate (`BreakingProducer::pushes_while_consuming`). A run after a pause or a
reload starts over breakers that hold what an earlier run consumed, so it starts with every breaker
pushing what it holds and no push named (`dispatcher::push_held`), before any arrival.

In a loop's scope a reader takes a package only once every pipeline it follows
(`Dispatcher::follow`) is quiescent: it has consumed every package queued for it, and so has every
pipeline it reads (`Dispatcher::quiescent`). It takes no push of theirs
([A loop in rounds](#a-loop-in-rounds)). A claim of such a reader reads the package's index first,
then checks the pipelines it follows, then takes that index alone, so the check sees the work that
the package was queued after. A round holds its followers while its pushes settle
(`Dispatcher::hold_followers`). An ordered pipeline has at most one package in flight and
takes its packages in queue order.

### Claiming from several threads

`Dispatcher` is `Sync`, and a claim takes no lock. A pipeline's queue is appended to while it is
open, and a closed queue takes nothing more. A source's queue grows at each `notify` and closes at
the source's close. A reader's queue is filled by the pushes the pipelines it reads land as they
consume, and closed at the last of their `finish`es, since each finishes once.

A queue's slots sit in buckets that double in size, each allocated by the first append that reaches
it, so a slot never moves. An append reserves its indices together, by compare and exchange on
`reserved`, and then writes each slot, once. The top bit of `reserved` says the queue is closed, so
an append reserves only while the queue is open, and one read gives both the count and the close. A
claim reads a slot only once it is written. The queue keeps the region its packages partition under
a lock that appends and the move of the pipeline to finishing take, and a claim of a package never
does. Two counters per pipeline only grow: `claimed`, the index of the next package to claim, and
`acknowledged`, how many packages have been acknowledged. Each pipeline's phase (running,
finishing, finished), a failure flag and the generation, the count of changes a waiting worker
waits on, are atomics too. A worker takes a lock only to sleep while there is nothing
to claim, and a change that can end a sleep takes it to wake the sleepers, only while there are
some. A pipeline that parks takes the lock on its parked rows at a push or an arrival to it and at a
decided push that releases them. The graph, the morsel size, the limits and the ordered pipelines
are fixed before the dispatcher is shared, since the methods that set them
take `&mut self`; every other method takes `&self`. The breakers are `Rc<RefCell<…>>`, which is not
`Send`. `run` claims on the calling thread, and no driver claims from several threads.

A worker asks `Dispatcher::try_claim` what to do next, and the answer (`Next`) is one of five:

| Answer | The worker |
|---|---|
| `Package(package)` | hands the package to its pipeline's breaker, then calls `acknowledge` |
| `Finish { pipeline, consumed }` | finishes the pipeline, pushing through `pushes(pipeline)` and the breaker's `finish`, then calls `Dispatcher::finish` with the pushes |
| `Wait(generation)` | calls `wait(generation)` and asks again |
| `Done` | stops: every pipeline has finished |
| `Failed` | stops: the run failed, whatever has not finished |

`claim` is `try_claim` and `wait` in a loop, and never answers `Wait`. A claim takes the package at
the front of the queue of the pipeline the worker prefers, where it may, and otherwise that of the
lowest pipeline whose queue it may take from. With no package to take, it finishes the lowest
pipeline that may finish. Single-threaded, with no
preferred pipeline, this is the order `run` follows, and a `Wait` there panics, because an acyclic
graph with every source closed and nothing queued has a pipeline that may finish.

A source pipeline may finish only once its queue is closed, so workers may start claiming before the
sources start: they wait until then, and no source finishes before its input has stopped arriving. A
closed source refuses a `notify`, a second `close` and a second `start_source`.

A claim reads `claimed`, and takes that index's package where its slot is written, by moving
`claimed` on with a compare and exchange. A claim that loses the exchange reads `claimed` again, so
no two claims take one package and none skips a package an append writes later: `claimed` never
passes `reserved`. A claimed package is in flight until the worker acknowledges it. `acknowledge`
refuses a package whose index no claim has handed out, whose guard is not the queued one, or that
was acknowledged before, the last through a flag per package that the first acknowledgement sets. A
pipeline may finish when it is running, its queue is closed and every package in it acknowledged. A
claim reads the count and the close in one read, and nothing is reserved after the close, so the
count of a closed queue is its last. The counters only grow, so a pipeline that may finish stays so
until it does. Its packages partition the region its queue was filled with, and the finish gets
that region as `consumed`: the regions notified to a source, its input whole for a pipeline that
reads its input whole, or the union of the guards pushed to the pipeline.

The claim that finds a pipeline that may finish moves its phase from running to finishing with a
compare and exchange, so exactly one claim finishes each pipeline. `Dispatcher::begin_finish` makes
the same move for a pipeline the caller names and asserts each condition;
`dispatcher::finish_pipeline` calls it. A finish's pushes collect in its `Pushes`. `finish` moves
the pipeline from finishing to finished with a compare and exchange, so a second finish is refused,
and then lands the pushes and closes the queue of each pipeline that reads it and reads no pipeline
still to finish. A push after a consume collects in a `Pushes` of its own, which `Dispatcher::land`
lands at once. A reader claims the packages landed there while the pipelines it reads run, and
finishes only from a closed queue. Its chain may therefore read the breaker of a pipeline it reads
while that pipeline consumes, which a driver on several threads would have to order; the breakers
are not `Send`, and `run` drives them on one thread. `finish` asserts that the reader has not begun
to finish, and dropping a `Pushes` whose morsels never landed panics.

An ordered pipeline has at most one package in flight. A flag per pipeline, taken by compare and
exchange before a claim of it looks and kept for the package it takes, admits one claim at a time,
and its acknowledgement drops the flag. Its morsels are therefore consumed one at a time, in the
order they were queued.

The pipelines of a transaction store share its breaker, and each is ordered on its own, so two of
them may each have a package in flight. A consume of one takes from its writer and commits from
every writer's queue ([Ready transaction decisions](design-operators.md#ready-transaction-decisions)), so a driver on several threads
has to serialize the consumes and finishes of one breaker's pipelines; `run` drives them on one
thread.

A claim reads the generation before it scans the pipelines, and one that finds nothing to do while a
pipeline has not finished answers `Wait` with that generation. The generation advances after each
change that can let a claim succeed: an append (`notify`, `start_source`, `finish`), a close, an
acknowledgement of an ordered pipeline's package, of a limited source's package or of the last
package reserved in a queue, a finish, and a failure. A change the scan missed therefore advanced
the generation past the one the claim answers, and `wait` returns at once instead of missing it.
`wait` sleeps on a `Condvar` under a `Mutex` that guards no data, counting itself as a sleeper under
that lock before it reads the generation. An advance writes the generation before it reads the count
of sleepers, and takes the lock to wake every sleeper only when the count is not zero; all four
accesses are sequentially consistent, so either the sleeper reads the new generation or the advance
wakes it. Waking every sleeper at each advance costs spurious wake-ups and needs no choice of which
one to wake. A `notify` waiting at its limit waits the same way.

`Dispatcher::fail` sets the failure flag and advances the generation: every claim from then answers
`Failed`, and every waiter wakes. A worker thread holds the handle `Dispatcher::worker` returns for
as long as it claims, and dropping that handle while the thread panics calls `fail`, so no worker
waits for a package the panicking one claimed and never acknowledged. A dispatcher method refuses a
caller that breaks the protocol through one check, which calls `fail` before it panics, so the run
fails with or without a worker handle. That includes a pipeline the dispatcher does not have. The
debug-build assertions on a breaker's morsels and on a `Pushes` finishing through its own dispatcher
panic without failing the run. After a failure, `acknowledge` and `finish` record nothing, and
`notify` returns at once.

Every claim reads the generation and writes the `claimed` counter of the pipeline it takes from, and
an acknowledgement writes `acknowledged`, so those cache lines move between the cores that claim
from one pipeline.

A claim hands out a finish only when no package anywhere is claimable, so a pipeline ready to finish
waits behind the packages of every other pipeline, which delays its reader when the reader
is on the run's longest path. A reader starts on the first push of a pipeline it reads, which lands
after that pipeline's first consume, unless that pipeline pushes only at its finish
(`pushes_while_consuming`).

