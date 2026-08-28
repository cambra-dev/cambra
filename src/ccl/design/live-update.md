# Live update: replacing a running program

A running Cambra program can be replaced by a new version of its source without
restarting. The new version inherits the running one's external endpoints and
whichever of its operators compute the same thing; everything else is rebuilt.

Two questions decide the design, and they have separate answers:

- **What may change.** Its logic freely, and its endpoints by addition.
- **What may not.** State: a variable the running program holds a value for must
  be one the new version declares, at the same type.
- **What survives.** Every `Let` binding and every `Transact` store whose
  computation is unchanged, and every variable's value whether or not its store
  was rebuilt.

The entry point is `LiveProgram::update` in `src/live_program.rs`. Diffing the
two versions is [diffing.md](diffing.md); this doc covers what an update does
with the answer.

## The model: every carrier has its own cut

An update cuts the running program and hands whatever must survive across the cut. No cut is
program-wide. There is no instant the whole graph stops at, and two carriers' cuts need not fall at
the same input.

A cut is a position in a coordinate both versions share. A source's domain positions are such a
coordinate: the source outlives the version and hands the same positions to whoever reads it next. A
commit clock is not shared but is private and restartable — nothing outside the store holds a tick,
so a rebuilt store starts its clock at `0` and loses nothing. A count of the columns a tile
currently offers is neither: it names a position in a view whose contents depend on what has been
released, so it means nothing to anyone who did not emit it.

Carriers are of two kinds, and each takes its cut from a different place.

**A carrier that holds nothing takes its cut from its source.** An element-wise map, a feed, a loop
over a literal list: the replacement recomputes from wherever its input still has work, and the
release state the retired producers agreed on is what says where that is
(`UIntStreamBuffer::carry_release_to_new_producers`). This asks one thing of every producer — that
it release what it has finished, and only that.

**A carrier that holds a value takes its cut from itself.** An induction store's value at position
𝑝 already summarizes every position below 𝑝, so the store's own frontier says where the replacement
starts. Its source's release state does not and cannot. The value and the position travel together
in one `CarriedState`, because either alone decides a position twice or skips it.

The two are not interchangeable in either direction. A carrier of the second kind reading its cut
off its source re-decides positions its recurrence already decided: a drive holds the input it reads
one position back through, so a source legitimately still owes elements the store has consumed. A
carrier of the first kind reading its cut off the end of the buffer drops everything that arrived
and went unhandled — over HTTP, a request accepted and then never answered.

A carrier that holds progress and releases nothing has neither cut and replays its whole input.
`TransactDriver` therefore names the item it is attempting by absolute source position and releases
each item as it finishes, which makes it a carrier of the first kind: it holds no progress its
source does not, so an update has nothing to hand over.
`a_transaction_writer_does_not_replay_what_it_committed` pins that, and the same release bounds a
transactional source's buffer while the program runs.

Every carrier in the program, and where its cut comes from:

| Carrier | Cut | Mechanism |
| --- | --- | --- |
| A `Let` binding or store the new version also computes | None — nothing is replaced | `resolved_hash` match, one more `FanOut` branch |
| An element-wise map, a feed, a loop over a list | Its source's agreed release | `carry_release_to_new_producers` |
| An induction store | Its own frontier | `CarriedState`, each variable's value and position together |
| A transaction writer's item cursor | Its source's agreed release | Absolute item positions, released on the commit-ack |
| A commit clock | None — private and restartable | A rebuilt store seeds at `0` |
| A route, its listener, and the requests behind it | None while any version still binds a route on the port | `SourceSinkRegistry` |

## Sources and sinks outlive a version

A `SourceSinkRegistry` (`ccl/context.rs`) holds a program's open data sources, the
reply sink of each open `http_serve` route, and the listener behind each bound
port. A listener's socket, its routing-table entry, and the requests buffered
behind it are program state rather than compilation state: they outlive the
version of the program that opened them.

Compiling any version seeds a fresh `LoweringContext` from that registry. An
`http_serve` call naming a route the registry holds binds it — keeping the
listener and everything buffered behind it — and one naming a route it does not
hold opens it, in a replacement exactly as in a first version. Routes are keyed
by their source name rather than by the response binding's name, which a new
version may spell differently.

Seeding the registry is also what lets a *diff* be answered about a running
program at all: compiling the new version in a fresh `GlobalContext` would try to
bind a port the running program holds and fail.

## The one guard: a version must be able to take over the state

`LiveProgram::update` compares the variables the running program holds against
those the new version declares, read off its planned tree
(`OpConversionContext::state_conflicts`). Two things are refused:

- **A variable the new version no longer declares.** Its value has nowhere to be
  seeded and would be discarded. Reported apart from the case where a variable of
  that name turns up under a *different* store — a loop's accumulator moved to
  another loop, or to or from a transaction — since an accumulator's history came
  from the inputs its own loop read and is not a seed for one over another
  source.
- **A variable it declares at a different type.** Its value cannot seed a store
  built for another shape. Allowed through, the store is constructed around a
  constant of the wrong extent and the *process* dies on the next pull
  (`Scalar(Strings([…])) vs Scalar(Int)`), taking every endpoint with it — which
  is why this is checked rather than left to fail later.

The check runs before anything is torn down, so a refused update leaves the
program whole.

Nothing else is refused. An earlier version of this pass froze the source and
sink set and rejected any new `http_serve`; adding one turns out to work — the
added route serves as soon as the swap completes, and what was already there
keeps its state — so the restriction bought nothing and the guard now matches
what the mechanism does.

Losing a value is refused because it is the one failure an author cannot
observe: the program carries on answering, and only the accumulated history is
gone. Every other change either works or fails visibly.

### A route a version stops serving is retired

Removing an `http_serve` is accepted, and the route goes with it. A listener and
its routing-table entry are registry state, so they outlive the version that
opened them: left registered, the address would keep matching requests and
buffering them for a reader that no longer exists, and the client would wait on a
reply nobody computes. `SourceSinkRegistry::retire_routes_absent_from` compares
the routes the pass bound against those the registry holds and unregisters the
difference, so the address answers 404 — which is what "this program no longer
serves that" should look like from outside.

Retiring belongs to installing a version, not to compiling one, and it runs in
`compile_program` rather than in `run_frontend` for that reason. A diff compiles
the new version against the running registry, so the listeners it sees are the
running program's; a compile that answered a question by unregistering a route
would make `/diff` change what the program serves.
`diffing_against_a_version_that_drops_a_route_does_not_retire_it` pins it.

The port goes when its last route does. While a sibling route survives there the
listener stays, which is what makes the retired address answer 404 rather than
refuse a connection; once nothing is registered there is nothing left to answer
for, so `release_unrouted_ports` drops the listener and the socket closes. That
bounds what a long-lived program holds: a version that moves its endpoints to
another port releases the one it left, instead of the process keeping every port
it ever served. Dropping the handle is what closes it — `SharedHttpServer` holds
the listener alongside the dispatcher thread and unblocks the thread on drop, so
the thread's own shutdown path runs and its `Server` goes with it.
`a_port_whose_last_route_goes_is_released` covers both halves.

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
against the correspondents of the bindings in scope. It is α-invariant, so two
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

Naming which bindings were rebuilt, rather than folding that into the
correspondent, is what keeps the correspondent stable. A binding's correspondent
is the identity hash of the term it computes, in every compilation and whether or
not the operator behind it was adopted. Two compilations of one source therefore
agree on it, and an unchanged part of a program is recognized on the first update.

Encoding "was it rebuilt" in the correspondent instead makes reuse depend on how
many updates have happened: the correspondents a first compilation hands out are
then all values no later compilation reproduces, so every binding that reads
another is
rebuilt on the first update and reuse only settles from the second.
`reuse_does_not_depend_on_how_many_updates_came_before` pins that.

### Stores are bindings too

A program's mutable variables live in a `Transact` store bound to `__hist`, and
every read of one is a projection `__hist.k` off that binding, where `k` is the
variable's own spelling. The store is bound
by `OpConversionContext::bind_store` on the same terms as any other binding: it
carries a correspondent, it is keyed by the identity of its `Transact` term, and a
matching one is adopted whole. Adopting a store is what carries an accumulator
across an update, because the store is where the accumulation lives.

Registering the store outside the conversion scope is what the correspondent
exists to
prevent. `__hist` would then be free in every term reading a mutable variable, and
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
  everything from there on. A producer addresses its guard by slot number, so the
  number lives in a `Cell` the producer and the registry share: `FanOut::reopen`
  drops the dead slots and writes each survivor its new number. Without that
  renumbering the slot list would grow by one dead entry per replaced subscriber
  on every update and never shrink, and both the notify walk and the release
  intersection scan it —
  `reopening_a_fan_out_drops_dead_slots_and_renumbers_the_rest` pins that the
  survivor keeps the guard it released.
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

1. Render the difference between the running source and the new one, which
   compiles both to `Phase::AsOfRead`.
2. Compile the new version to `Phase::Planning` against the endpoint registry and
   run the state guard on the planned tree. Steps 1 and 2 open nothing and build
   no operators, so a version that fails either leaves the running program
   serving.
3. Tear down the running graph: detach its sinks, drop its outputs.
4. `GlobalContext::retire_version` moves the retiring conversion context's
   operators into the next compilation's inheritance.
5. Compile and subscribe the new version against the same registry, which now
   binds every endpoint the retired version left open.

Steps 3 and 4 come after step 2 so that a rejection is never destructive, and
before step 5 so that what the new version inherits is held by the inheritance
and not also by a graph still running.

An accepted update therefore compiles four times: twice for the diff, once to
`Planning` for the guard, and once for real. `run_frontend` goes from source to a
stop phase and there is no way to continue a stopped tree into operator
conversion, so the guard's tree cannot be the one that gets built — which is why
`LiveProgram::update` documents a panic for the two compiles disagreeing.
Compilation is cheap next to the state the swap preserves, and the ordering is
what makes a rejection non-destructive, so the cost buys the guarantee.

## What an update does not do

- **Start a rebuilt store empty.** It resumes instead — see
  [Rebuilding a store resumes it](#rebuilding-a-store-resumes-it).
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

- **The value.** A store's value rides its own cyclic `FanOut` as a
  `Tile::Store`, so `live_state` reads each carried key off
  `FanOut::cached_tile` with `store_frontier` / `store_value_at`. Reading the
  fan's own memo rather than keeping a copy beside the operator is what keeps
  this off the shared-state ledger `./ci.sh shared_state` maintains: no value
  crosses between operators outside a tile.
- **The name.** State is keyed by a `VarPath`: the variable's own spelling plus
  its index among the variables of that spelling, in tree order. The spelling
  carries the meaning — a writer's write set is keyed by the variable written, so
  the name survives from the source text to the store — and the index only
  disambiguates. Counted among the variables sharing the spelling rather than
  among all of them, so a stateful loop added anywhere shifts nothing unless it
  declares that same name.

  **A spelling is not unique, and nothing computed can stand in for one.** A
  declaration can be shadowed, and a function holding a whole stateful loop
  declares one variable per call site once inlining has cloned its body. Two such
  instantiations can differ *only* in their writer bodies once arguments are
  substituted, so a content-derived identity either fails to tell them apart or
  changes under exactly the edit state has to survive. The index is what is left,
  and it is why identity is assigned by one walk
  (`OpConversionContext::set_var_paths`) whose answers both the guard and
  conversion read, rather than derived twice.
- **The position.** A rebuilt store resumes at the retired store's frontier, and
  each variable's seed is that store's value at the same position
  (`CarriedState`). The value and the position travel together because either one
  alone decides a position twice or skips it, and they hang off the *variable*
  because a variable is what has an identity: a store has none, so two commit
  stores at different frontiers would otherwise race to set one position. A
  rebuilt store reads the position back off any variable it declares. Both the
  store's seed tick (`CommitEngine::seeded_at`) and the drive's window base come
  from `resume_at`, and they must agree — `InductionDriver` asserts that a
  decision cannot precede the input it decides.

  A position only means something in the domain it was counted in, and that is
  the `Transact`'s own sequencing domain — the index of every key's history. A
  data source and a transaction's commit clock outlive the version reading them,
  so a position counted in one still means something to the next version. A
  concrete iteration extent does not: it is part of the program, so a variable
  sequenced by one carries nothing at all and its replacement recomputes the fold
  from the collection its own version declares.
- **What the source still owes.** A source hands a producer registering after the
  swap the release state its retired producers agreed on, which runs *below* a
  store's resume position rather than deciding it: a drive holds the input it
  reads one position back through, so the source owes the replacement elements
  the recurrence has already decided, and the drive holds those without
  re-deciding them. See
  [The model: every carrier has its own cut](#the-model-every-carrier-has-its-own-cut).

### Positions are absolute, in the store and in the window alike

`DriverWindow` addresses rows absolutely: `rows[i]` is position `base + i`, and
released rows compact off the front without renumbering, because the body looks a
decision up by domain value. A drive that starts with its source leaves `base` at
`0`, where row index and position coincide; a resuming drive sets it to the
position it starts from.

Getting that wrong stalls the drive rather than misreading it — the decision
lookup finds no row at the absolute position and the drive stops without
advancing, so the resumed loop answers nothing while the rest of the program
keeps serving. `a_store_resumes_however_far_its_source_has_advanced` pins it,
driving six positions before the update; at one or two the two indexings overlap
enough to mask it.

## What the guard lets through

Everything that leaves the state takeable. Measured across the shapes an edit can
have:

| Change | Outcome |
| --- | --- |
| Logic of a loop or a transaction writer | Accepted; the variable resumes |
| A loop gains an accumulator | Accepted; the others resume, the new one starts at its init |
| A variable's declared init changes, type unchanged | Accepted; the carried value wins, the init is only for a fresh start |
| A whole stateful loop is added | Accepted; existing state untouched |
| A route is added | Accepted; it serves as soon as the swap completes |
| A route is removed | Accepted; the route is retired and answers 404 |
| A loop loses an accumulator | Refused, naming it |
| A variable's type changes, records included | Refused, naming both types |
| A variable moves to another loop, or to or from a transaction | Refused, naming where it went |

An update is atomic with respect to requests: under concurrent load every request
is answered by exactly one version, and the versions do not interleave.

A program whose output is its `main` value rather than a sink updates the same
way. Such a program is not short-lived — `stdin` is unbounded, so the binary's
own driver loop keeps running and services the control port between pulls. Its
loops are identified by their source like any other, so the guard names one
plainly: `` `n`, of the loop over `stdin` ``.

Its state is as live as a sink program's, and reads the same way:

- A pure element-wise transformation splits exactly at the swap. Eight lines with
  the swap after the fourth emit four under the old rule and four under the new,
  each once: the stream is neither replayed through the new version nor dropped
  at the handover.
- An accumulator carries across. Counting `+1` per line, switched to `+2` after
  half the stream, the value at EOF is `1.5` times the line count — each half
  counted by the rule that was in force when it arrived.
- Feeding the accumulator out (`out << n`) reports it per line rather than only
  at EOF, so the swap is observable mid-stream: `1, 2, 4, 6` resumes from `2`
  rather than restarting.

What a value like a bare trailing `n` reports is decided by *when* it is read,
and reading it at the tail of the program means EOF — which is a property of that
program, not a limit on what an update can carry.
