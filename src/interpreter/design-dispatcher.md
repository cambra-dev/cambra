# Pipeline dispatch

## The dispatcher

`Dispatcher` (`src/interpreter/dispatcher.rs`) holds the graph of pipelines, which pipelines each
one reads and so which one reads it, a queue of work packages per pipeline, and the morsel size
`morsel_rows`. A work package is a pipeline, a guard for its
breaker to consume, one morsel of at most `morsel_rows` held rows, and the package's index in the pipeline's queue. The dispatcher holds no breaker: the driver,
`run`, reaches each breaker through a handle its caller passes, indexed by pipeline, and borrows it
for one call at a time.

`Dispatcher::new` refuses a zero morsel size, a graph with a cycle, and a pipeline that reads more
than one pipeline: a breaker has one input, and a work package does not say which input its guard
is for. Several pipelines may read one. The release of one reader would remove rows from the
breaker's state that another has still to read, so readers of one pipeline need a `FanOut` between
them, which the dispatcher does not check.

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
so a reader may claim it while the pipeline runs; the finish lands its own push and closes the
queues of the pipelines that read it. A breaker whose output is one value, `Aggregate`,
`ExtractAggregate` and `ExtractFinal`, pushes one morsel. `Memo` and `MapAggregate` cut at the
outermost keys they hold, in key order (`cut_at_keys`): a cut falls before every `morsel_rows`-th
held key the guard names, the first morsel reaches down from the guard's lower end and the last is
open above. The morsels partition the guard exactly. A key the breaker states absent rides in the
morsel that covers it, so the releases of a reader's input at its morsels add up to the whole guard,
and a reader that is final once its input is released whole, such as `Aggregate`, becomes final. A
released key is in no morsel, because the final guard already excludes it. A guard naming no more
than `morsel_rows` held keys is one morsel. A package is a guard of the reader's input tiling, as
the reader's chain restates the morsel, and `run` asserts in a debug build that a package fits its
breaker's input.

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

Nothing calls the dispatcher or the breakers' methods outside unit tests: no scheduler runs
pipelines, and how a driver reaches a breaker from a program's roots is not decided.

### Completeness in pushes

A key of a pipeline's output is decided where its value can no longer change and its presence or
absence is settled: the region `BreakingProducer::decided` states, which defaults to what the
breaker holds. A breaker's finish pushes its decided region up the consumer chain beside its final
guard (`Pushes::push_final`), and each operator restates it in its own keys. An operator that keeps
its input's keys passes it unchanged. One that widens them passes nothing until the region is every
key, since each of its keys depends on every key of its input (`Landing::is_wholly_decided`). The
reader records, per pipeline it reads, the union of the regions that reached its entry
(`Dispatcher::record_decided`).

### Claiming from several threads

`Dispatcher` is `Sync`. Each pipeline has one queue, its claimed and acknowledged counts, and a
phase: running, finishing, or finished. A source's queue closes at `close`; a reader's closes after
the pipeline it reads has finished and landed its pushes. Every pipeline finishes once.

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

