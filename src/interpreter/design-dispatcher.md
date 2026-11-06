# Pipeline dispatch

## The dispatcher

`Dispatcher` (`src/interpreter/dispatcher.rs`) holds the graph of pipelines, which pipelines each
one reads and so which one reads it, a queue of work packages per pipeline, and the morsel size
`morsel_rows`. A work package is a pipeline, a guard for its
breaker to consume, one morsel of at most `morsel_rows` held rows, and the package's index in the pipeline's queue. The dispatcher holds no breaker: the driver,
`run`, reaches each breaker through a handle its caller passes, indexed by pipeline, and borrows it
for one call at a time.

`Dispatcher::new` refuses a zero morsel size, a graph with a cycle, and a pipeline that reads one
pipeline twice. A pipeline may read several pipelines, and its queue  closes at the
finish of the last of them. A work package is a guard of the breaker's own input, whichever
pipeline's push queued it. Several pipelines may read one. The release of one reader would remove
rows from the breaker's state that another has still to read, so readers of one pipeline need a
`FanOut` between them, which the dispatcher does not check.

A source pipeline, one that reads no pipeline, is queued the regions of its breaker's input that
have arrived. `Dispatcher::notify` queues one such region, cut every
`morsel_rows` positions where it names finite runs of positions (`Value::UInt` keys) and whole
otherwise. `Dispatcher::close` says no more of the source's input arrives.
`Dispatcher::start_source` queues the input whole and closes the source: where the input's tiling
states a finite range of positions for its outermost keys (a `UIntRange`), the dispatcher cuts it
every `morsel_rows` positions, the last morsel open above. Any other input starts as one package at
its universal guard: a sparse source's keys are not known before it is pulled. `Dispatcher::limit`
caps a source's packages queued and not acknowledged,: `notify` waits while the
source has that many outstanding, and `try_notify` answers that it did not queue. A notify admitted
below the limit queues every morsel it cuts, so the packages outstanding pass the limit by at most
one notify's morsels less one, for one thread that notifies. A notify returns once the run fails,
having queued nothing.

`run` starts every source whole. It consumes the package at the front of the lowest pipeline's
queue that has one. With no package to claim, it finishes the lowest pipeline that may finish,
and stops once every pipeline has finished.

`Pushes::push_final` pushes what a breaker has decided and its pipeline has not pushed before, its
final guard less the region pushed, one package per morsel the breaker cuts it into
(`BreakingProducer::morsels`); a breaker no pipeline reads cuts nothing. The dispatcher keeps each
pipeline's pushed region. A push computes the difference and grows the region in one
step under that region's lock, so two threads pushing for one pipeline push disjoint regions, and a
push, after a consume or at its finish, pushes only what no earlier push did. The driver
lands a push made after a consume at once (`Dispatcher::land`), before it acknowledges the package,
so a reader may claim it while the pipeline runs; the finish lands its own push and closes the queue
of each pipeline that reads it, where every other pipeline that one reads has finished. A breaker
whose output is one value, `Aggregate`, `ExtractAggregate` and `ExtractFinal`, pushes one morsel.
`Memo` and `MapAggregate` cut at the outermost keys they hold, in key order (`cut_at_keys`): a cut
falls before every `morsel_rows`-th held key the guard names, the first morsel reaches down from the
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
tiling, for the breaker's pipeline, less what is queued for that pipeline there
already. The difference and the queue's growth are one step under the queue's lock, so a push that
reaches a breaker along two paths, as a filter reads one memo for its values and its predicate, is
queued once. A push an operator widens to `Everything` on its way fails the run at the reader it
reaches (`Landing::widened` marks the path, `Landing::queue` refuses it), since the reader could not
tell which of its keys it names: a reader reached that way reads the pushing pipeline once it has
finished, instead of its pushes. A push that re-enters a consumer it is passing through has met a
cycle, and fails the run too. The push path sits beside `notify` while runs still pull. Once every
run goes through the dispatcher, `notify`, its gates and `WakeupQueue` go, and `push` takes their
place.

`dispatcher::finish_pipeline` finishes a pipeline once. It checks that the pipeline has not
begun to finish, its queue is closed and every package acknowledged, each pipeline it reads has
finished, and its breaker's input has released every guard the pipeline consumed. The release
check is closed over the input's tiling (`TileGuard::closed_over`): a row released through the last
position of its finite range is released whole. A debug build also asserts that the morsels of a
pushed guard partition it (`partition_gap`) and that every region is consumed once.

The dispatcher reads a breaker's input `input` through `input_tiling` and `input_released`, the
tiling a package's guard is a guard of and the guard the breaker has released of that input, so a
breaker whose input sits inside a shared cell can answer both.

A dispatcher run delivers no wake-up queued on the scheduler. A breaker's reader learns of what it
holds through the push, and a producer's notifications queue on the scheduler as in pull mode
(`WakeupQueue`), to be delivered by a scheduler that pulls the program afterwards.

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
predicate, reads it once. A pipeline that reads directly a pipeline another pipeline reads is
refused, since only a fan-out slot keeps one reader's release from removing what another still
reads. A store, or a loop's scope, is the breaker of a pipeline of its own
([A store as a breaker](design-operators.md#a-store-as-a-breaker), [A loop in rounds](#a-loop-in-rounds)), which the
walk plans where it reaches a reader slot of the store's fan-out (`TileProducer::store_read`).
Each package reaches its breaker by walking the chains again, and the pushes a call makes land
once the walk has returned, since a breaker reached through a fan-out slot is called while the walk
holds the fan-out its push climbs.

Before the run, each edge from a pipeline to the pipeline that reads it is probed: the read
pipeline's breaker pushes `Everything` through its consumer into a landing that records what reaches
each entry instead of queueing it (`Landing::probe`). What reaches the reader's entry is the region
of its input that pipeline's pushes reach (`Dispatcher::reaches`). A reader that a pipeline it reads
reaches at no entry reads that pipeline by pull, as a lookup reads its table, and reads its input
whole once every pipeline it reads has finished (`Dispatcher::read_whole`). Every other reader parks
the rows its pushes bring until the pipelines it reads have decided them
([Parking arrivals until a read is decided](#parking-arrivals-until-a-read-is-decided)). Each range
under a reader of pushes is probed too, such as the positions of a literal arm of a concatenation.
A constant keeps no consumer. A constant whose keys a reader consumes is one of four kinds, and none
brings a key the ranges and the pushes do not name:

- a list literal's table, the function operand of a `MapResult` over the literal's positions
  (`IterateExtent`), so the positions bring every key the table would;
- bound by a `let`, beneath the binding's `Memo`, whose pipeline is a source and reads its input
  whole;
- empty, which brings no key;
- a scalar, which has one position, so any push to its reader names all of it.

`run_program` refuses, in a debug build, a constant collection beneath a reader of pushes that is
not a function operand. What the ranges bring, less everything the pushes can name, is queued for
the reader at the start of the run as one region (`Dispatcher::queue_for`), parked as a push's rows
are. A reader that neither a push nor a range brings a row reads its input whole.

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
root of a sink's pipeline whose `DataSink` merges what it is handed (`Collected`); no push reaches
the driver's consumer, so that pipeline reads its input whole. The run answers the `main`
output's merged tile (`Run::main`) and hands the producer back; a program has at most one.

The run pulls only the breakers' inputs. The program is compiled with
`GlobalContext::defer_sink_pulls`, which leaves out the pull each sink takes once subscribed, and
`CompiledProgram::sink_pulls_deferred` records it. The planner refuses, before anything runs, with
a `Refused` error that names the shape, and pull mode runs every refused program:

- a program compiled with its sinks pulled;
- a program that reads a live source (`CompiledProgram::source_producers`), whose arrivals no run
  notifies;
- a pipeline read directly by a pipeline another pipeline reads;
- a breaker with no consuming mode (`Breaker::no_consuming_mode`): a transaction store of several
  writers;
- the stores [A store as a breaker](design-operators.md#a-store-as-a-breaker) lists.

The binary runs a program dispatched where `CAMBRA_DISPATCH` is set to anything but `0` or the empty
string, and neither `--inspect` nor `--control` is given, at morsels of `CAMBRA_MORSEL_ROWS` rows
(1024 unset; a value that is no positive count panics). It prints the `main` output's value once. A
refused program runs in pull mode after a note on stderr, in the context the dispatched run compiled
it in: the compile has opened its sources and sinks, a port bound or stdin taken, which a second
compile could not open again.

Every program of the differential suite (`tests/it/differential_interp.rs`) runs dispatched too, at
morsels of one row and of every row, and answers what pull mode answers, or the planner refuses it.

### Completeness in pushes

A key of a pipeline's output is decided where its value can no longer change and its presence or
absence is settled: the region `BreakingProducer::decided` states, which defaults to what the
breaker holds. A breaker's finish pushes its decided region up the consumer chain beside its final
guard (`Pushes::push_final`), and each operator restates it in its own keys. An operator that keeps
its input's keys passes it unchanged. One that widens them passes nothing until the region is every
key, since each of its keys depends on every key of its input (`Landing::is_wholly_decided`). The
reader records, per pipeline it reads, the union of the regions that reached its entry
(`Dispatcher::record_decided`).

### Parking arrivals until a read is decided

A reader that parks (`Dispatcher::park`) reads each row of its input once, when every pipeline it
reads has decided it. A push brings the rows it names less what pushes brought before
(`Dispatcher::queue_or_park`). The part that each pipeline it reads has decided, or does not reach,
is queued in its queue, and the rest is parked (`Dispatcher::decided_part`). A decided push
appends what it leaves decided of the parked rows to the reader's queue , before the
pushing pipeline counts its finish toward the reader's close (`Dispatcher::release_parked`). Two
pipelines whose pushes name one key, as the output's memo reads two aggregates of one binding, are
read once: the key waits until both have decided it. At the finish every pipeline has
decided all it pushes, so nothing stays parked.

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

Finishing a request pipeline closes its body sources. The execution handler retains the finish
until all body and step pipelines have finished in the same dispatcher. The store is terminal then;
its final push lands before the request pipeline's finish releases its readers. A nested store
releases its body a position at a time and each row it decides whole. Its readers release their
rows as they finish with them, and the store's offer cuts rows released since its last step from
the snapshot. A flat store holds nothing short of terminal.

A scope inside 𝑑 others runs rounds at paths of 𝑑 + 1 keys (`Projection::of_path`). The planner
refuses a nested loop where a pulled operator restates no projection at that level
(`Planner::refusal_of_nested`). The walk stops at consuming breakers: their consumes pull their own
inputs, and their scopes check those pulls. A breaker left in pull mode passes the pull on. The
planner panics on such a loop, as it does on the stores
[A store as a breaker](design-operators.md#a-store-as-a-breaker) lists.

### Claiming from several threads

`Dispatcher` is `Sync`. Each pipeline has one queue, its claimed and acknowledged counts, and a
phase: running, finishing, or finished. A source's queue closes at `close`; a reader's closes after
every pipeline it reads has finished and landed its pushes. Every pipeline finishes once.

Queue slots sit in buckets that double in size, allocated by the first append that reaches them.
An append reserves indices through an atomic counter, then writes each slot once. The counter's
top bit closes the queue, so no reservation succeeds after the close. A claim takes an index only
once its slot is written. The region the queue's packages partition is protected by a mutex that
appends and finishes take; a package claim takes no lock.

| Answer | The worker |
|---|---|
| `Package(package)` | Hands the package to its breaker, then calls `acknowledge`. |
| `Finish { pipeline, consumed }` | Finishes the breaker through `pushes(pipeline)`, then calls `Dispatcher::finish`. |
| `Wait(generation)` | Calls `wait(generation)` and asks again. |
| `Done` | Stops: every pipeline has finished. |
| `Failed` | Stops: the run failed. |

`try_claim` takes a package from the preferred pipeline where possible, then scans in pipeline
order. With no package to claim, it moves the lowest ready pipeline from running to finishing by
compare and exchange. Readiness requires a closed queue with every package acknowledged. The
finish receives the union of the package guards as `consumed`. `begin_finish` checks the same
conditions for a named pipeline. A finish moves its phase to finished by compare and exchange,
lands its pushes, closes its readers' queues, and ends the run at the last pipeline's finish.
`claim` repeats `try_claim` and `wait` until the answer is no longer `Wait`.

An acknowledgement checks that the package's index was claimed, its guard matches the queued guard,
and its acknowledgement flag was unset. An ordered pipeline has at most one package in flight:
a claim holds its atomic flag until acknowledgement. Its morsels run in queue order.

A claim reads the generation before scanning. Each change that can enable work advances it: an
append, close, finish, failure, or an acknowledgement that frees ordered work, returns source
credit, or completes a queue. `wait` counts a sleeper under a mutex before reading the generation;
an advance writes the generation before counting sleepers, using sequentially consistent atomics.
It wakes every sleeper under that mutex when any exist. A limited source's `notify` waits by the
same protocol. A claim that releases an ordered pipeline's flag after finding nothing checks
again for a package and advances the generation if one appeared meanwhile.

`fail` sets the failure flag and wakes waiters. Every claim then answers `Failed`. A worker holds
`Dispatcher::worker` while claiming; its destructor fails the run when its thread panics.
Protocol refusals fail the run before panicking, including those made without a worker handle.
After failure, acknowledgements and finishes record nothing, and notifications return at once.

The breakers are `Rc<RefCell<…>>` and are not `Send`. `run` drives them on one thread. A future
driver that consumes and reads a breaker on different threads must order those accesses. Dropping
pushes whose morsels never landed panics.

