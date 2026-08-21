# Live update: replacing a running program

A running Cambra program can be replaced by a new version of its source without
restarting. The new version inherits the running one's external endpoints and
whichever of its operators compute the same thing; everything else is rebuilt.

Two questions decide the design, and they have separate answers:

- **What may change.** The logic between the existing sources and sinks. The
  endpoint set is a precondition the compiler checks, not a convention.
- **What survives.** Every `Let` binding and every `Transact` store whose
  computation is unchanged, together with what that computation has
  accumulated.

The entry point is `LiveProgram::update` in `src/live_program.rs`. Diffing the
two versions is [diffing.md](diffing.md); this doc covers what an update does
with the answer.

## Endpoints outlive a version

An `EndpointRegistry` (`ccl/context.rs`) holds a program's open data sources, the
reply sink of each open `http_serve` route, and the listener behind each bound
port. A listener's socket, its routing-table entry, and the requests buffered
behind it are program state rather than compilation state: they outlive the
version of the program that opened them.

Compiling a replacement seeds a fresh `LoweringContext` from that registry with
`endpoints_frozen` set. An `http_serve` call then binds a route the registry
already holds, and naming one it does not hold is a lowering error. Freezing is
what makes "only the logic between sources and sinks may change" checkable. It is
also what lets a *diff* be answered about a running program at all: compiling the
new version in a fresh `GlobalContext` would try to bind a port the running
program holds and fail.

Routes are keyed by their source name rather than by the response binding's name,
which a new version may spell differently.

## Operator identity is the term it computes

Operator conversion consults the previous version at every `Let` binding
(`OpConversionContext::bind_let`). A binding is reused when the previous version
bound the same computation, and the fan-out behind it is branched instead of
rebuilt.

A `Let` is the reuse boundary because it is already the sharing boundary. Every
binding compiles to `Rc<FanOut>::new(Memo::new(op))` so that several uses can
draw on one operator, and a new version's use is one more use. A late branch does
not re-subscribe upstream: it pulls the same `MemoProducer`, whose cache is
cumulative. That is what hands a reused operator's accumulation to the version
that inherits it.

Identity is the `resolved_hash` of the bound term (`ccl/content_hash.rs`), taken
against the class tokens of the bindings in scope. It is α-invariant, so two
independent compilations of one source agree, and type-aware, so a refinement
change is a change.

### Reuse is hereditary

An operator is adopted only when every binding its term reads was adopted too, so
a carried-forward operator is never left reading a subgraph the update rebuilt.
`OpConversionContext::rebuilt` records the bindings this compilation built, and
`reads_only_adopted` declines any term with a free name among them
(`ccl_utils::free_names`, which counts occurrences inside refinement predicates
as well as in the term). Bindings are bound in dependency order, so the check is
transitive: a binding that reads a rebuilt one is itself recorded as rebuilt.

Naming which bindings were rebuilt, rather than folding that into the class, is
what keeps the class stable. A class is the identity hash of the term the binding
computes, in every compilation and whether or not the operator behind it was
adopted. Two compilations of one source therefore agree on it, and an unchanged
part of a program is recognized on the first update.

Encoding "was it rebuilt" in the class instead makes reuse depend on how many
updates have happened: the classes a first compilation hands out are then all
values no later compilation reproduces, so every binding that reads another is
rebuilt on the first update and reuse only settles from the second.
`reuse_does_not_depend_on_how_many_updates_came_before` pins that.

### Stores are bindings too

A program's mutable variables live in a `Transact` store bound to `__reg`, and
every read of one is a projection `__reg.k` off that binding. The store is bound
by `OpConversionContext::bind_store` on the same terms as any other binding: it
carries a class, it is keyed by the identity of its `Transact` term, and a
matching one is adopted whole. Adopting a store is what carries an accumulator
across an update, because the store is where the accumulation lives.

Registering the store outside the conversion scope is what the class exists to
prevent. `__reg` would then be free in every term reading a mutable variable, and
`hash_free_var` identifies an unresolved free variable by its bare spelling — so
every such term would hash the same however the recurrence was edited, and its
operator would be reused against a store that no longer computed what it had.
`an_edit_to_the_accumulating_loop_takes_effect` pins that.

One store covers one causal group, so an edit anywhere in a group rebuilds that
group's store; two independent mutable variables get two stores and are
independently reusable.

### What is never reused

A binding compiled under an iteration (`BindingKind::Aligned`) is rebuilt. Its
operator is parameterized by an iteration input threaded into it at conversion
time; the input is not part of the term, so the term does not identify the
operator.

## A subscription lasts as long as its producer

Replacing a graph while sharing operators with it requires knowing which
subscriptions are still real. Three registrations answer that the same way: the
subscriber owns its side, and the registry holds a weak reference.

- **Fan-out branches.** `FanOutShared::subscribers` holds a `Weak<()>` per slot
  whose strong side lives in the `FanOutProducer` that slot handed out. A slot
  whose producer is gone is skipped when notifying and when intersecting release
  guards. Skipping matters: the guards are intersected before anything is
  released upstream, so a subscriber that will never release again would
  otherwise pin the intersection where it stopped and the input would retain
  everything from there on. Slots are never renumbered, because a producer
  addresses its guard by index.
- **Scheduler wake-ups.** `Scheduler::add_source_handle` records a
  `Weak<RefCell<dyn Consumer>>`, and the `IterateExtentProducer` that registered
  it owns the strong side. A source handle outlives a version; the subscriptions
  against it do not. A strong registration would keep every operator any version
  ever subscribed alive and being notified.
- **Sink dispatch.** `SinkConsumer::detach` clears the producer slot at teardown.
  Dropping the compiled outputs does not end a replaced version's dispatch on its
  own: an operator the next version carries forward still holds the notification
  closure that reaches the old sink consumers, so they would keep being woken and
  keep writing to sinks the new version now owns. Clearing the slot also drops
  the operators behind it, which is what lets the fan-outs they subscribed to see
  those subscriptions end.

## Order of an update

1. Compile the new version to `CompileStage::Planned` against the endpoint
   registry. This opens nothing and builds no operators, so a version that fails
   here leaves the running program serving.
2. Tear down the running graph: detach its sinks, drop its outputs.
3. `GlobalContext::retire_version` moves the retiring conversion context's
   operators into the next compilation's inheritance.
4. Compile and subscribe the new version with `Endpoints::Inherited`.

Steps 2 and 3 come after step 1 so that a rejection is never destructive, and
before step 4 so that what the new version inherits is held by the inheritance
and not also by a graph still running.

## What an update does not do

- **Define what a rebuilt store starts from.** See "Rebuilding a store replays
  its inputs" below. This is the open question in the design, not a detail.
- **Reuse across a change of shape.** Adoption is all-or-nothing per binding and
  keyed by exact term identity, so a term that changed at all is rebuilt whole.
  Nothing recognizes that an edited term still computes most of what it did.
- **Run both versions.** The replaced version is dropped. Running two versions
  concurrently over shared state is a separate model.
- **Reuse below a `Let`.** Reuse is offered at binding boundaries only. Offering
  it at an arbitrary node would mean wrapping every node in `Memo`/`FanOut`,
  changing execution characteristics program-wide.

## Rebuilding a store resumes it

A rebuilt store does not restart its variables from the inits the source
declares. Each one resumes from the value the retired version left it holding, so
editing a loop changes what it does next without discarding what it had
accumulated. Editing how a guestbook formats an entry leaves the entries it
already recorded as they were and formats the next one the new way.

Three pieces carry that:

- **The value.** `InductionStore` publishes its carried keys' current values into
  a shared cell (`StoreState`) as it runs, and `OpConversionContext` hands them
  to the next compilation. A cell rather than a read of the producer, because the
  producer is owned inside the graph the replacement is about to drop and its
  type is not recoverable from the `dyn TileProducer` holding it.
- **The name.** State is keyed by `(store_scope, runtime key)`, where the scope
  is the data source the loop iterates. A variable's own key does not identify it
  across versions: planning labels an accumulator by its position within its
  store, so two loops each carrying one variable both call it `acc0`. The source
  a loop reads is the part an edit to its body leaves alone.
- **The position.** A replacement's new producers enrol with each source at its
  current frontier rather than at the oldest value it retains
  (`advance_registration_frontier`), so a rebuilt store continues the stream. The
  drive's cursor starts at the base of the first window it sees rather than at
  `0`, and the engine seeds at the tick that position reads
  (`CommitEngine::seeded_at`) rather than at tick 0.

A commit (`Txn`) store publishes no state, so a transactional variable does not
resume yet.

### Unresolved: a rebuilt store stalls once its source has trimmed

A rebuilt store produces nothing when its source has advanced past a handful of
positions. Measured on `guestbook` with the `/sign` loop edited: correct at two
prior requests (`e1`, `e2`, then `- AF`), no output at five or more. The update
itself is accepted, the graph stays live, and the program's other endpoints keep
serving; only the rebuilt store is silent.

The integration tests do not cover this. They drive two or three requests before
updating, which is the regime that works, so the suite is green while the case
above is broken. Treat a green run as saying nothing about this until a test
drives enough positions to reach it.
