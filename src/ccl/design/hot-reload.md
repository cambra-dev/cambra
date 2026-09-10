# Hot reload: replacing a running program

`--control` (default 8081) serves two endpoints against a running program. `/diff` reports how a new
version of the source differs from the running one, at a pipeline phase the caller names, and
changes nothing. `/reload` replaces the program with that version: the endpoints stay bound, every
operator whose computation is unchanged is kept along with what it has accumulated, and every
mutable variable the new version still declares is seeded with the value it was holding.

What a reload means, and the three properties that make one well defined, are
[Reload](/docs/operational-semantics/semantics.md#4-reload) in the operational semantics. This doc
is the mechanism that realizes them.

Three questions decide the design:

- **What may change.** Logic, freely. Endpoints, by addition and by removal. State, by addition — a
  version may declare a variable the running program does not have, and it starts at its init.
- **What may not.** The continuity of a value that already exists. A variable the running program
  holds a value for must be one the new version still declares, at the same type, and one the source
  tells apart from its siblings; otherwise the reload is refused and the running program is left
  serving. See [The one guard](#the-one-guard-a-version-must-be-able-to-take-over-the-state).
- **What survives.** Every `Let` binding, `Transact` store and iteration input whose computation is
  unchanged, and every variable's value whether or not its store was rebuilt.

The entry point is `LiveProgram::reload` in `src/live_program.rs`. Computing the difference between
two programs is [diffing.md](diffing.md); this doc covers what a reload does with it.

## How a reload works

A reload drops the running version's subscriptions and then builds the replacement's, so one
version's graph is subscribed at a time and nothing observes a half-swapped one. The swap sits
between two pulls: the driver services the control port between them, and `LiveProgram::reload`
takes `&mut self`. What crosses the swap is what the teardown does not reach — the process and its
listeners, the requests buffered behind a route, every mutable variable's value, and the operators
the handover holds.

Building the replacement is three steps. [Order of a reload](#order-of-a-reload) is the full
sequence, including the guard and the endpoint bookkeeping either side of these.

### 1. Say which nodes of the two programs correspond

The compile that installs the version diffs its own tree against the running version's
(`compile_replacement`, `CompiledProgram::ast`), at `Phase::Planning`, using the structural diff in
`ccl/diff.rs`. `Correspondence` records the `Content::Same` matches and nothing else: a node
corresponds exactly where the two versions' subtrees are isomorphic modulo α. A `Same` node's whole
subtree is `Same`, which is what lets a kept region's contents be found by walking the tree rather
than listed.

The diff's matcher reads through a renamed binder and a moved subtree, so a reordered or relocated
binding still corresponds. It does not read through an edit: a term that changed at all is a node
with no correspondent, and so is every node above it.

A node's identity is its address (`NodeId`). The tree conversion walks must therefore be the tree
the program keeps, which is why `CompiledProgram::ast` is boxed — a bare field is moved into place
after conversion, which relocates the root and leaves the root's recorded operator unreachable.

### 2. Keep the operator at a corresponding node

Conversion consults the correspondence at three places: every `Let` binding
(`OpConversionContext::bind_let`), every store (`OpConversionContext::bind_store`) and every
writer's iteration input (`OpConversionContext::iteration_input`). Each records what it built under
the node it built it from, so the replacement finds the previous version's operator at its own
node's correspondent and branches the fan-out behind it instead of building one.

A fan-out is what carries a producer across a version, and it is the only thing that can. It owns
the producer it subscribed and re-points the notification to the new version's branch, whereas a
producer's consumer is fixed at `TileOperator::subscribe` — one lifted out of a retired graph would
go on waking a consumer that no longer exists. So an operator is reusable only where a fan-out
already sits, which is what decides the three places above: [What a reload does not
do](#what-a-reload-does-not-do) says why they are not everywhere.

Keeping an operator keeps the whole subgraph under it, including its stores and their accumulated
values. Two conditions bound that: every binding the term reads must have been kept too ([Reuse is
hereditary](#reuse-is-hereditary)), and a site that needs the operator to still *supply* something
must find it not released in full by its subscribers, since it can then only answer empty
([A binding whose operator is spent is rebuilt, not
changed](#a-binding-whose-operator-is-spent-is-rebuilt-not-changed)).

The second condition bounds the two sites that reuse an operator for what it supplies. A binding is
what a name reads and a store seeds its accumulators from, so a spent one hands on nothing
(`a_reload_does_not_seed_an_accumulator_from_a_released_in_full_binding`). An iteration input is
reused for something else — the position it reached, which `FanOut::released_position` reports as
well from a spent operator as from a live one — so it looks the correspondence up through
`OpConversionContext::correspondent` and takes a released-in-full operator. Keeping it is what says
the fold is finished and leaves the replacement asking for nothing; building a fresh one offers
every position of the collection again and folds the whole list onto the carried value
(`a_fold_over_a_fixed_collection_resumes_where_it_stopped`). One released-in-full collection can be
reached from both sites in one reload, which is why the condition belongs to the lookup each site
does rather than to the operator.

### 3. Build the rest and wire it to its input

An operator with no correspondent is built and subscribed like any other. Subscribing is also how it
learns where it is: a new subscriber's guard starts at what its input has already released, so it
claims neither data that is gone nor data nobody has finished with. A `FanOut` seeds that guard from
what it has released upstream, and a source seeds a newly-registered producer the same way
(`ProducerReleases`, `carry_release_to_new_producers`). This asks one thing of every producer — that
it release what it has finished, and only that.

Nothing establishes a frontier across the graph. Each rebuilt operator resumes wherever its own
input still has work, and two of them can resume at unrelated positions in unrelated inputs.

Two things a subscription cannot supply have to be computed and handed to the operator being built:

- **The value each mutable variable was holding.** No input holds it, because a store's value at
  position 𝑝 summarizes every position below 𝑝. `live_state` reads it off each store's own cyclic
  fan-out at handover, `Inheritance::mutable_state` carries it, and a rebuilt store seeds from it
  under the variable's `VarPath`.
- **The position a rebuilt recurrence starts at.** This is derived from the input rather than
  carried, but a store and a drive are told it at construction rather than discovering it: one past
  `FanOut::released_position` for an iteration the reload kept, `first_position_for_a_new_producer`
  for one built fresh over a source, and `0` for one over a collection.

[Rebuilding a store resumes it](#rebuilding-a-store-resumes-it) is both of those in full.

Where each part of a program stands after a swap:

| Part of the program | Where it starts | Mechanism |
| --- | --- | --- |
| An operator the new version also has | Where it already was — nothing is replaced | Node correspondence, one more `FanOut` branch |
| A rebuilt map or feed over a kept operator | What that operator has released | A new subscriber's guard starts there |
| A rebuilt map or feed over a source | What the source's retired producers released | `carry_release_to_new_producers` |
| A rebuilt recurrence over a kept iteration | One past what that iteration's readers released | `FanOut::released_position` |
| A rebuilt recurrence over a rebuilt iteration | Where that iteration begins — a source's carried release, or `0` for a collection | `first_position_for_a_new_producer` |
| A transaction writer's drive | Its writer's iteration input where the reload kept it, and `0` over a rebuilt one | Absolute item positions, released on the commit-ack |
| A rebuilt store's commit clock | `0`, seeded from the carried value | Private and restartable |
| A route, its listener, and the requests behind it | Where they were, while any version still binds a route on the port | `SourceSinkRegistry` |

## Reuse is hereditary

An operator is kept only when every binding its term reads was kept too, so a carried-forward
operator is never left reading a subgraph the reload rebuilt. The correspondence cannot answer this
on its own — `content_hash` matches a term's free variables by spelling, so an unchanged term can
read a binding that changed. `OpConversionContext::rebuilt` records the bindings this compilation
built, and `reads_only_kept` declines any term with a free name among them (`ccl_utils::free_names`,
which counts occurrences inside refinement predicates as well as in the term). Bindings are bound in
dependency order, so the check is transitive: a binding that reads a rebuilt one is itself recorded
as rebuilt.

How much a reload reuses does not depend on how many reloads preceded it. The correspondence
relates this version's tree to the running version's tree, and neither is derived from how those
trees were built, so an unchanged part of a program is recognized on the first reload.
`reuse_does_not_depend_on_how_many_reloads_came_before` pins that, comparing one edit applied
directly against the same edit applied after a no-op reload.

That test is also what catches a kept region losing what it holds. Keeping a region does not walk
into it, so nothing inside reaches `bind_let`, `bind_store` or `iteration_input` to be recorded, and
the next version would find nothing at those nodes. `OpConversionContext::keep_region` records it
instead, by walking the kept subtree: the region corresponds `Content::Same` throughout, so what it
holds is whatever the previous version recorded at a corresponding node.

## Stores are bindings too

A program's mutable variables live in a `Transact` store bound to `__hist`, and every read of one is
a projection `__hist.k` off that binding, where `k` is the variable's own spelling. The store is
bound by `OpConversionContext::bind_store` on the same terms as any other binding: it is keyed by
the node of its `Transact` term, and a corresponding one is kept whole. Keeping a store is what
carries an accumulator across a reload, because the store is where the accumulation lives.

One store covers one causal group, so an edit anywhere in a group rebuilds that group's store; two
independent mutable variables get two stores and are independently reusable.
`an_edit_to_the_accumulating_loop_takes_effect` pins the first half: the edit is inside the
`Transact` node, so the two versions' nodes do not correspond there and the operator is rebuilt.

A store below a kept binding is handed on rather than bound again, by that same walk. Without it a
store declared inside a function body — where the `Transact` sits under the `Let` binding the call's
result, rather than at the top of the binding chain — leaves the handover on the first reload that
keeps its binding, and the next reload reseeds its variable from the declared init while the guard,
reading the same map, no longer refuses dropping it.
`a_variable_survives_a_reload_that_kept_its_binding` and
`the_state_guard_survives_a_reload_that_kept_the_binding` pin the two halves.

## A binding whose operator is spent is rebuilt, not changed

An operator whose subscribers released it in full can only answer empty: it has told its input that
nothing will be read again, and a `Memo` input drops what it holds in response
(`FanOut::released_in_full`). A binding standing behind one hands its readers nothing, so the reload
rebuilds it — where the term is recomputable, which is what makes the rebuilt operator hold what the
spent one held.

Rebuilding for that reason is not a change to what the binding computes, and `bind_let` does not
record it as one. The distinction is load-bearing: `reads_only_kept` declines to keep an operator
that reads a binding this version **rebuilt**, on the grounds that progress through something the
reload replaced means nothing. A binding rebuilt only because its operator was spent computes what
the retired one computed, so a recurrence over it may still take the retired iteration and continue.
Recorded as a change, the recurrence loses its iteration, restarts at `0`, and folds its whole input
on top of the value it is carrying — the doubling
`a_loop_added_over_a_folded_collection_reads_it_whole` pins.

## What is never reused

A binding compiled under an iteration (`BindingKind::Aligned`) is rebuilt. Its operator is
parameterized by an iteration input threaded into it at conversion time; the input is not part of
the term, so the term does not identify the operator.

## Sources and sinks outlive a version

A `SourceSinkRegistry` (`ccl/context.rs`) holds a program's open data sources, the reply sink of
each open `http_serve` route, and the listener behind each bound port. A listener's socket, its
routing-table entry, and the requests buffered behind it are program state rather than compilation
state: they outlive the version of the program that opened them.

Compiling any version seeds a fresh `LoweringContext` from that registry. An `http_serve` call
naming a route the registry holds binds it — keeping the listener and everything buffered behind it
— and one naming a route it does not hold opens it, in a replacement exactly as in a first version.
Routes are keyed by their source name rather than by the response binding's name, which a new
version may spell differently.

Seeding the registry is also what lets `/diff` be answered about a running program at all: compiling
the new version in a fresh `GlobalContext` would try to bind a port the running program holds and
fail.

## The one guard: a version must be able to take over the state

`LiveProgram::reload` compares the variables the running program holds against those the new version
declares, read off its planned tree (`OpConversionContext::state_conflicts`). Three things are
refused:

- **A variable the new version no longer declares.** Its value has nowhere to be seeded and would be
  discarded.
- **A variable it declares at a different type.** Its value cannot seed a store built for another
  shape. Allowed through, the store is constructed around a constant of the wrong extent and the
  process dies on the next pull (`Scalar(Strings([…])) vs Scalar(Int)`), taking every endpoint with
  it, which is why this is checked rather than left to fail later.
- **A value that would move between two declarations the source does not distinguish.** Two
  anonymous call sites of one stateful function are told apart by position alone, so reordering
  them, or inserting a third ahead, hands each variable its neighbour's value. The site's own
  content is what catches it: a site whose body the reload edited is gone from the new version,
  while one still present under a different variable has moved (`site_moved`). Refused rather than
  followed, because nothing in the source says which declaration the value belongs to — the refusal
  names both and says that binding each call site to a name is what makes the edit carry.

The check runs before anything is torn down, so a refused reload leaves the program whole.

Nothing else is refused. Adding an `http_serve` works: the added route serves as soon as the swap
completes, and what was already there keeps its state.

Losing a value is refused because the program carries on answering afterwards and only the
accumulated history is gone, so an author has nothing to notice. One other outcome is silent in the
same way and is **reported** rather than refused, off the same tree at the same moment: a loop that
begins above the beginning of what it reads
([A variable that begins above its loop's input](#a-variable-that-begins-above-its-loops-input)). Everything else either
works or fails visibly.

### A route a version stops serving is retired

Removing an `http_serve` is accepted, and the route goes with it. A listener and its routing-table
entry are registry state, so they outlive the version that opened them: left registered, the address
would keep matching requests and buffering them for a reader that no longer exists, and the client
would wait on a reply nobody computes. `SourceSinkRegistry::retire_routes_absent_from` compares the
routes the pass bound against those the registry holds and unregisters the difference, so the
address answers 404.

A request that arrived before the unregister has no version left to answer it, and retirement
answers it with the same 404. The source holding such a request outlives the route: a retired
version's operators sit in the next compilation's inheritance and reach the source through it, so
nothing else ends the client's wait. `DataSourceDomainExtentImpl::answer_in_flight` drains both
stages a request waits at — the dispatcher's channel, before the source has accepted it, and the
shared pending map, after — so the stage a request happened to reach does not decide what its client
sees. `a_request_that_arrived_before_its_route_was_retired_is_answered` pins it.

Retiring belongs to installing a version, not to compiling one, and it runs in `compile_program`
rather than in `run_frontend` for that reason. A diff compiles the new version against the running
registry, so the listeners it sees are the running program's; a compile that answered a question by
unregistering a route would make `/diff` change what the program serves.
`diffing_against_a_version_that_drops_a_route_does_not_retire_it` pins it.

The port goes when its last route does. While a sibling route survives there the listener stays,
which is what makes the retired address answer 404 rather than refuse a connection; once nothing is
registered there is nothing left to answer for, so `release_unrouted_ports` drops the listener and
the socket closes. That bounds what a long-lived program holds: a version that moves its endpoints
to another port releases the one it left, instead of the process keeping every port it ever served.
Dropping the handle is what closes it — `SharedHttpServer` holds the listener alongside the
dispatcher thread and unblocks the thread on drop, so the thread's own shutdown path runs and its
`Server` goes with it. `a_port_whose_last_route_goes_is_released` covers both halves.

## A subscription lasts as long as its producer

Replacing a graph while sharing operators with it requires knowing which subscriptions are still
real. Three registrations answer that the same way: the subscriber owns its side, and the registry
holds a weak reference.

- **Fan-out branches.** `FanOutShared::subscribers` holds a weak reference per slot whose strong
  side lives in the `FanOutProducer` that slot handed out. A slot whose producer is gone is skipped
  when notifying and when intersecting release guards. Skipping matters: the guards are intersected
  before anything is released upstream, so a subscriber that will never release again would
  otherwise pin the intersection where it stopped and the input would retain everything from there
  on. A producer addresses its guard by slot number, so the number lives in a `Cell` the producer
  and the registry share: `FanOut::reopen` drops the dead slots and writes each survivor its new
  number. Without that renumbering the slot list would grow by one dead entry per replaced
  subscriber on every reload and never shrink, and both the notify walk and the release intersection
  scan it — `reopening_a_fan_out_drops_dead_slots_and_renumbers_the_rest` pins that the survivor
  keeps the guard it released.
- **Scheduler wake-ups.** `Scheduler::add_source_handle` records a `Weak<RefCell<dyn Consumer>>`,
  and the `IterateExtentProducer` that registered it owns the strong side. A source handle outlives
  a version; the subscriptions against it do not. A strong registration would keep every operator
  any version ever subscribed alive and being notified.
- **Sink dispatch.** `SinkConsumer::detach` clears the producer slot at teardown. Dropping the
  compiled outputs does not end a replaced version's dispatch on its own: an operator the next
  version carries forward still holds the notification closure that reaches the old sink consumers,
  so they would keep being woken and keep writing to sinks the new version now owns. Clearing the
  slot also drops the operators behind it, which is what lets the fan-outs they subscribed to see
  those subscriptions end.

## Nothing inside a fan-out owns it

A fan-out owns its input chain through `FanOutShared::producer`, so a handle on the fan-out held
from inside that chain closes a cycle and nothing in the subgraph is ever freed. `FanHold` names the
distinction that avoids it: a downstream reader owns the fan-out, and a reader sitting inside its
input chain does not. Two readers sit inside.

- **The notification closure.** `FanOutBranch::subscribe` hands the input a closure that wakes the
  fan-out's consumers, and the producer that subscribe returns is what the fan-out then owns. The
  closure holds a weak reference and does nothing when it cannot upgrade, which is the case where
  the fan-out is gone and has no consumers left to wake.
- **A store's recurrence.** A store's driver reads the store to recover each position's prior value,
  and a transaction's writer reads it to decide a commit. Both are placed inside the store, so both
  hold it by `FanOut::recurrence_branch`. Either read happens only while the fan-out is pulling the
  chain the reader sits in, so the fan-out is alive for the whole of it.

This is what frees a retired version's operators, and the release bookkeeping depends on their being
freed: a source hands back a producer's release record from that producer's `Drop`, so one that
outlives its version goes on constraining the agreement from where it stopped, and the next version
is offered what the retired one already committed —
`a_second_reload_does_not_replay_what_the_first_committed` pins it.

## Order of a reload

1. Render the difference between the running source and the new one, which compiles both to
   `Phase::AsOfRead`.
2. Compile the new version to `Phase::Planning` against the endpoint registry, opening the endpoints
   it adds and keeping them, and run the state guard on the planned tree. Neither step builds an
   operator, so a version that fails either leaves the running program serving; a refusal here hands
   the ports back (`release_unrouted_ports`).
3. Tear down the running graph: detach its sinks, drop its outputs.
4. `GlobalContext::retire_version` moves the retiring conversion context's operators and stores into
   the next compilation's inheritance.
5. Compile and subscribe the new version against the same registry, which now binds every endpoint
   the retired version left open, and opens the ones it adds. This compile diffs its own tree
   against the running version's (`compile_replacement`, `CompiledProgram::ast`) to get the
   correspondence reuse is keyed on.
6. Notify each sink, so whatever is already available is pulled.

Step 6 is not redundant with the notifications `subscribe` raises. An operator notifies from inside
`subscribe` — an induction store does, to start its loop — and a sink consumer's producer does not
exist until `subscribe` returns, so those notifications reach a consumer with nothing to pull and
are dropped. A first compile does not notice: a source holding data reports it as new on the next
poll, which drives everything. A replacement is not covered by that, because the version it replaces
already took the report. Without step 6 a reload installed while work is outstanding — a fold
caught partway, a request accepted and not yet answered — sits until the next arrival
(`a_version_installed_mid_fold_is_pulled_without_a_new_arrival`).

Step 1 opens nothing, and step 2 opens only ports. Rendering a difference runs with
`Endpoints::Inherited`, so a route the registry does not hold is named rather than opened: the
context is thrown away but a socket is not, and opening one would make asking a question change what
the program serves.

Step 2 is the exception, because binding is the one thing it and step 5 would otherwise not share. A
port already in use — a typo in the source, the program's own control port, a port another process
holds — would then fail for the first time at step 5, after step 3 had torn the running graph down,
where there is nothing left to reject to and the failure is the panic step 5 documents. Taking the
port at step 2 makes it an ordinary compile error raised while the program is whole, and taking
rather than probing it means nothing can claim the port in between. A port the guard then refuses is
released, and one whose routes never materialize is dropped by `release_unrouted_ports`.
`a_version_naming_an_unbindable_port_is_refused` pins it.

Steps 3 and 4 come after step 2 so that a rejection is never destructive, and before step 5 so that
what the new version inherits is held by the inheritance and not also by a graph still running.

An accepted reload therefore compiles four times: twice for the diff, once to `Planning` for the
guard, and once for real. `run_frontend` goes from source to a stop phase and there is no way to
continue a stopped tree into operator conversion, so the guard's tree cannot be the one that gets
built — which is why `LiveProgram::reload` documents a panic for the two compiles disagreeing.

Reuse is keyed on step 5's own tree, not on step 1's or step 2's. Step 1 renders a difference for a
reader and step 2's tree is thrown away, while a node's identity is its address, so a correspondence
taken against either would name nodes the built graph was not built from.

## Rebuilding a store resumes it

A rebuilt store does not restart its variables from the inits the source declares. Each one resumes
from the value the retired version left it holding, so editing a loop changes what it does next
without discarding what it had accumulated. Editing how a guestbook formats an entry leaves the
entries it already recorded as they were and formats the next one the new way.

Three things decide where a rebuilt store picks up, and only two of them are handed over:

- **The value.** A store's value rides its own cyclic `FanOut` as a `Tile::Store`, so `live_state`
  reads each carried key off `FanOut::cached_tile` with `store_frontier` / `store_value_at`. Reading
  the fan's own memo rather than keeping a copy beside the operator is what keeps this off the
  shared-state ledger `./ci.sh shared_state` maintains: no value crosses between operators outside a
  tile.
- **The name.** State is keyed by a `VarPath`: the author-written bindings whose definitions enclose
  the declaration, outermost first, then the variable's own spelling, then its index among the
  variables sharing both. The spelling carries the meaning — a writer's write set is keyed by the
  variable written, so the name survives from the source text to the store — and the chain is what
  tells two declarations of one spelling apart. So a stateful loop added anywhere shifts nothing:
  `a`.`n` is `a`.`n` however many other `n`s the version declares
  (`a_loop_added_ahead_of_a_same_spelled_one_starts_at_its_init`,
  `reordering_two_same_spelled_variables_keeps_their_state_apart`).

  The index is left for the one shape the source names nothing in: two anonymous call sites of one
  stateful function in one expression. An edit to either body leaves it alone, and a reload that
  would move a value between them is refused (`swapping_two_anonymous_call_sites_is_refused`). What
  is left unaddressed is narrower: a reorder that edits both bodies at once leaves neither site
  present to recognise, so the position decides and the values cross.

  **A spelling is not unique, and nothing computed can stand in for one.** A declaration can be
  shadowed, and a function holding a whole stateful loop declares one variable per call site once
  inlining has cloned its body. Two such instantiations can differ solely in their writer bodies
  once arguments are substituted, so a content-derived identity either fails to tell them apart or
  changes under exactly the edit state has to survive. The enclosing bindings are what is left, and
  they are why identity is assigned by one walk (`OpConversionContext::set_var_paths`) whose answers
  both the guard and conversion read, rather than derived twice.
- **The position.** A rebuilt store resumes one position past what the iteration operator it was
  handed has released (`FanOut::released_position`), which is where the retired recurrence had
  reached: a drive holds the input it reads one position back through, so the release runs exactly
  one position behind the decision. Both the store's seed tick (`CommitEngine::seeded_at`) and the
  drive's cursors come from that one number, and they must agree — `InductionDriver` asserts that a
  decision cannot precede the input it decides.

  The position is not carried. It is a fact about one operator, and that operator is what the reload
  hands over, so there is no second answer to reconcile and no sequence for two versions to compare.
  A variable whose new version reads a different iteration seeds its value and takes that
  iteration's position instead. That is a variable moving between loops, or a program moving to
  another port: the positions it is about to decide belong to something its predecessor never read,
  so none is decided twice and none is skipped, while the value — which is the variable's, not the
  input's — goes on.

  A universal release is where the number would otherwise be lost. A consumer that finishes an
  iteration releases the whole domain, and a universal guard names no position, so `FanOut` keeps
  the highest position its releases have named alongside the guard
  (`FanOutShared::released_position`) and that watermark only rises. Without it a fold that ran to
  the end of its list would read as a fold that had released nothing, and its replacement would
  decide every position again (`a_fold_over_a_fixed_collection_resumes_where_it_stopped`).

  **Starting again is not starting at `0`.** A loop's iteration built fresh over a source starts at
  `first_position_for_a_new_producer` — `0` for a source nothing has read, and the released frontier
  otherwise, because a source the loop moved to may have been read all along by some other loop that
  released what it consumed. Basing a drive below that makes it wait for an element that is not
  coming, which is a silent stall rather than a wrong answer. The same holds for a store the version
  adds rather than replaces: a loop that gains an accumulator over a source the program was already
  reading has nothing carried and still cannot start at `0`
  (`a_stateless_loop_may_gain_an_accumulator_over_an_advanced_source`).

  A collection needs none of that, and a fold that carries a value gets its continuity from the kept
  iteration instead. Such a fold resumes at the position it had reached, so an edit inside the loop
  governs the elements that are left rather than replaying the ones already folded, and a fold over
  another collection is a different node, which rebuilds the iteration and starts that collection
  from its first element. A fold carrying nothing takes the other answer — see "A recurrence reads
  its input from the position it starts at".
  The positions the predecessor decided are not re-decided and are not re-read: the resumed store
  seeds tick `0` with the value handed over, so a reader enumerating the whole collection reads that
  value for them. A fold caught partway is where this is visible — the elements below the swap keep
  what the retired version decided and the rest are the new one's
  (`a_fold_interrupted_partway_resumes_at_the_position_it_reached`).

  A transaction's drive counts in its writer's iteration input and takes a kept one's position from
  there (`a_transaction_over_a_fixed_collection_does_not_replay`). Over a rebuilt iteration it
  starts at `0` whatever the source has done, because it finds its next item by scanning up from its
  cursor rather than being based at a position: an advanced source costs it a comparison where an
  induction drive's window would stall
  (`a_stateless_route_may_gain_a_transactional_writer_over_an_advanced_source`). A store with more
  than one writer needs nothing extra: each site's iteration is its own node, so each drive reads
  its own input's position rather than sharing one cursor.

A rebuilt drive is therefore handed elements its predecessor already decided. The release state a
source hands a newly-registered producer runs below the store's resume position rather than deciding
it, because a drive holds the input it reads one position back through, so the drive holds those
elements without re-deciding them. See [3. Build the rest and wire it to its
input](#3-build-the-rest-and-wire-it-to-its-input).

### Positions are absolute, in the store and in the drive alike

Every `DriverRow` carries its own absolute position, and released rows compact off the front without
renumbering, because the body looks a decision up by domain value. A row index is therefore not a
position, and a filtered source makes that plain: the positions it delivers are not contiguous.
Where a resuming drive starts is said by its two cursors instead — `emitted_through`, which the next
position to iterate is taken from, and `source_released_through`, which keeps it from re-releasing a
prefix its predecessor released.

Getting that wrong stalls the drive rather than misreading it — the decision lookup finds no row at
the absolute position and the drive stops without advancing, so the resumed loop answers nothing
while the rest of the program keeps serving. `a_store_resumes_however_far_its_source_has_advanced`
pins it, driving six positions before the reload; at one or two the two indexings overlap enough to
mask it.

## A variable that begins above its loop's input

A recurrence starts at a position and folds upward from it, so which position it starts at and what
its input can offer are one question. The answer is per variable rather than per store: one loop
drives one position sequence, and a store's variables share it.

A variable **carrying a value** has had every position that value summarizes folded into it. Its
loop takes the iteration the retired version was running and starts one above what that iteration
released (`FanOut::released_position`), so no element is folded twice — which is compatibility,
[semantics.md](/docs/operational-semantics/semantics.md#4-reload), property 1.

A variable **carrying nothing** starts at the value it declares, which summarizes no position, so it
wants its loop's input from the beginning. It gets that only where the loop's input is rebuilt,
which happens where nothing in the store carries and the input's term can be built again: a fresh
iteration over a collection of literals starts at `0` and folds it whole. Otherwise the loop is the
retired one continued, and the variable begins wherever that loop resumes — including a variable
added to a loop whose other variables carry, which is the ordinary case and just as silent.

**A source and a collection are not two cases.** A source offers a new producer what its retired
producers had not released — `StreamBuffer::first_index_for_a_new_producer` is a released prefix
plus one — and a kept operator holds what its retired consumers had not released. One condition,
read off two mechanisms. What separates a term that can be built again from one that cannot is
whether it reads a source at all, which is what `unrecomputable_nodes` answers.

`unreadable_inputs` reports every variable that begins above its loop's input, in the reload's
report and in `/diff` before that. Reported rather than refused, because there is nothing better
available: the elements are gone, so folding from here is all that is left. What the source does not
say is which was meant — an accumulator added to a live endpoint intends a running total from here,
and a view over a retained feed intends the whole, and the two are the same term. Refusing would
refuse the first along with the second. The declaration is where that belongs, and until it can say
so the report is what makes the choice visible.

The cases, in the order they get harder to see: `a_loop_may_gain_an_accumulator` (the added variable
begins where its loop is, though the loop's other variables carry),
`a_stateless_route_may_gain_a_transactional_writer_over_an_advanced_source` (a commit drive is based
at `0` and scans up, so where it begins is its source's answer rather than its own),
`a_loop_that_cannot_read_its_collection_from_the_start_is_reported` (nothing in the store carries and
the input reads a source), and
`a_loop_added_over_a_buildable_collection_reports_nothing` with
`a_loop_added_over_a_folded_collection_reads_it_whole` for the case that is rebuilt instead.

## What a reload does not do

- **Start a rebuilt store empty.** It resumes instead — see [Rebuilding a store resumes
  it](#rebuilding-a-store-resumes-it).
- **Reuse across a change of shape.** Reuse is all-or-nothing per node: the correspondence records
  `Content::Same` matches, so a term that changed at all is rebuilt whole. Nothing recognizes that
  an edited term still computes most of what it did.
- **Run both versions.** The replaced version is dropped. Running two versions concurrently over
  shared state is a separate model.
- **Reuse at every node.** Reuse needs a fan-out at the node to be reused, because a fan-out is the
  only thing that carries a producer across a version, and one is placed where a `Let` already needs
  it for sharing and where a rebuild would otherwise lose progress a recompute cannot recover (a
  writer's iteration input). Offering it everywhere would mean a fan-out per node, which changes
  execution characteristics program-wide.

## What the guard lets through

Everything that leaves the state takeable. Measured across the shapes an edit can have:

| Change | Outcome |
| --- | --- |
| Logic of a loop or a transaction writer | Accepted; the variable resumes |
| A loop gains an accumulator under a new name | Accepted and reported; the others resume, and the new one starts at its init and folds from where the loop has got to, since one loop drives one position sequence |
| A variable's declared init changes, type unchanged | Accepted; the carried value wins, the init is only for a fresh start |
| A whole stateful loop is added under new names | Accepted; existing state untouched. It folds its input whole where this version can build that input again, and from where that input starts where it cannot — reported in the second case |
| A route serving statelessly gains a transactional writer | Accepted and reported; the writer commits from the next request, replaying none the route already answered |
| A route is added | Accepted; it serves as soon as the swap completes |
| A route is removed | Accepted; the route is retired and answers 404 |
| A loop loses an accumulator | Refused, naming it |
| A variable's type changes, records included | Refused, naming both types |
| A variable is added whose name another already has | Accepted; the bindings enclosing each declaration tell them apart, so the existing one resumes and the added one starts at its init |
| Two anonymous call sites of one stateful function are reordered, or a third is inserted ahead | Refused, naming both declarations and saying to bind each call site to a name. Their state is told apart by position alone, and the source does not say which declaration a value belongs to |
| The same, with both bodies edited in the one reload | Their state crosses. Neither site is left for `site_moved` to recognise, so the position decides — the one shape the identity does not address |
| A variable moves to another loop | Accepted; it seeds with the value it held and decides the positions its new loop's iteration still has |
| A variable moves to or from a transaction | Accepted, both directions; the value carries and the position comes from whatever the variable now iterates. A commit clock hands on no position, and over an unchanged collection both sides read the same kept iteration, so a fold caught partway resumes where it stopped rather than committing an element twice |
| A loop reads another source, a port change say | Accepted; same as above, and the port it left is released |
| Two loops, or two transaction writers, swap which source they read | Accepted; each keeps its value and continues on the source it moved to, taking over that source's iteration |
| A variable moves to a loop over a fixed collection | Accepted; same as above — the value seeds and the collection folds on top of it |
| The body of a loop over a fixed collection is edited | Accepted; the fold resumes at the position it had reached, so the new rule governs the elements left |
| The collection itself is edited | Accepted; the edited collection is a different computation, so its iteration is rebuilt and the collection folded whole |

A request a surviving route delivers is therefore answered by exactly one version, and a request
buffered before the swap is answered after it: the buffer belongs to the source rather than to
either graph (`a_request_that_arrived_before_the_swap_is_answered_after_it`). A route the reload
retires is the case where that runs out — the source behind it is unreachable from the new graph, so
retirement answers those requests itself ([A route a version stops serving is
retired](#a-route-a-version-stops-serving-is-retired)). Behaviour under concurrent load is not
measured.

A program whose output is its `main` value rather than a sink reloads the same way. Such a program
is not short-lived — `stdin` is unbounded, so the binary's own driver loop keeps running and
services the control port between pulls. Its loops are identified by their source like any other, so
the guard names one by the address the source gives it — a bare `` `n` `` where the program declares
one, and `` `a`.`n` `` where the declaration sits inside a binding (`VarPath`'s `Display`).

Its state is as live as a sink program's, and reads the same way:

- A pure element-wise transformation splits exactly at the swap. Eight lines with the swap after the
  fourth emit four under the old rule and four under the new, each once: the stream is neither
  replayed through the new version nor dropped at the handover.
- An accumulator carries across. Counting `+1` per line, switched to `+2` after half the stream, the
  value at EOF is `1.5` times the line count — each half counted by the rule that was in force when
  it arrived.
- Feeding the accumulator out (`out << n`) reports it per line rather than only at EOF, so the swap
  is observable mid-stream: `1, 2, 4, 6` resumes from `2` rather than restarting.

What a value like a bare trailing `n` reports is decided by the position it is read at, and reading
it at the tail of the program means EOF. That is a property of that program rather than a limit on
what a reload can carry.
