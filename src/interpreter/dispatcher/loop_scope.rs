//! A loop run in rounds: the pipeline of a loop's scope, whose breaker runs a nested dispatcher
//! over the pipelines inside the loop's cycle, one round per position, and steps the loop's store
//! after each. See `src/interpreter/design-operators.md`, "A loop in rounds".

use super::plan::{Consumes, Members, Planned, plan_edges, probe, reach_in_chain, routes_to};
use super::*;
use crate::interpreter::tile_operators::StoreCell;

/// Where a loop scope finds the breaker of one of its inner pipelines.
pub(super) enum Member {
    /// In the store's chain, by its address (`plan::address`).
    Chain(usize),
    /// The scope of a loop nested in this one, which runs the rounds of one row of its store per
    /// round, the row of the round's position.
    Scope(Box<RefCell<LoopScope>>),
}

/// The breaker of a loop's scope in the enclosing dispatcher. Its input is the store's, and a
/// consume runs one round per position it names: each inner pipeline the round starts is queued
/// the position, the inner pipelines run until a pass changes nothing (`run_round`), and the
/// store steps. It is no producer, and pushes the store at the finish where the store is
/// terminal.
pub(super) struct LoopScope {
    store: StoreCell,
    inner: Dispatcher,
    members: Vec<Member>,
    /// The placements of the inner pipelines' entries, which hold the inner pipelines only while
    /// the scope runs ([`Placed`]).
    placements: Vec<Vec<Placement>>,
    /// The inner pipelines a round queues its position for: the sources, and the nested loops,
    /// which take it once the pipelines they read have finished the round.
    starts: Vec<PipelineId>,
    /// What the inner dispatcher planned for each inner pipeline, in pipeline order.
    pub(super) planned: Vec<Planned>,
    opened: bool,
    request: Option<Request>,
    /// The drive, which the plan fixes: found on the first call of [`drive`](Self::drive).
    drive: std::cell::OnceCell<PipelineId>,
}

struct Request {
    guard: TileGuard,
    rows: bool,
    read: bool,
    rounds: usize,
    closing: bool,
    round: Option<TileGuard>,
}

impl LoopScope {
    /// The scope of the store `store`, whose inner pipelines' breakers are `members`, as
    /// `pipelines` plans them. A breaker whose pipeline would read its input whole, which happens
    /// only once the run's sources are whole, is in no pipeline and stays in pull mode: the store
    /// has it read again before each round and each step, and its readers read the pipelines it
    /// reads. The scope places the entries to probe the inner edges, and unplaces them until it
    /// runs.
    ///
    /// # Panics
    ///
    /// Where no inner pipeline is a source: the drive, a breaker that reads the store through
    /// its recurrence, is one.
    pub(super) fn new(
        store: StoreCell,
        members: Vec<Member>,
        pipelines: Members<'_>,
        morsel_rows: usize,
    ) -> Self {
        let mut kept: Vec<usize> = (0..members.len()).collect();
        let (inner, planned, reads) = loop {
            let reads = reads_of_kept(&pipelines.reads, &kept);
            // A breaker in no pipeline keeps no entry: an id the planner gave it may be a kept
            // pipeline's here, and a probe would take it for an arrival there.
            for placement in pipelines.placements.iter().flatten() {
                placement.set(None);
            }
            for (at, &pipeline) in kept.iter().enumerate() {
                for placement in &pipelines.placements[pipeline] {
                    placement.set(Some(PipelineId(at)));
                }
            }
            let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
                reach_member(&store, &members[kept[pipeline.0]], pipeline, call)
            };
            let names: Vec<String> = kept.iter().map(|&at| pipelines.names[at].clone()).collect();
            let leaves: Vec<_> = kept
                .iter()
                .map(|&at| pipelines.leaves[at].clone())
                .collect();
            let kinds: Vec<Consumes> = kept.iter().map(|&at| pipelines.kinds[at]).collect();
            // A live source read inside a scope is read by the scope's pipeline in the run's
            // dispatcher, so no inner pipeline is live.
            // A store inside a scope is a nested loop's, whose scope is one pipeline, so no two
            // inner pipelines share a breaker's pushes.
            let (inner, planned) = plan_edges(
                &reads,
                &names,
                &leaves,
                &vec![false; names.len()],
                false,
                &kinds,
                &(0..names.len()).collect::<Vec<_>>(),
                morsel_rows,
                &mut reach,
                &mut |pipeline| match &members[kept[pipeline.0]] {
                    Member::Scope(scope) => Some(scope.borrow().pushing_end()),
                    Member::Chain(_) => None,
                },
            );
            for placement in pipelines.placements.iter().flatten() {
                placement.set(None);
            }
            let whole: Vec<usize> = planned
                .iter()
                .enumerate()
                .filter(|(at, plan)| plan.whole && pipelines.kinds[kept[*at]] == Consumes::Pushes)
                .map(|(at, _)| kept[at])
                .collect();
            if whole.is_empty() {
                break (inner, planned, reads);
            }
            kept.retain(|pipeline| !whole.contains(pipeline));
        };
        assert!(
            reads.iter().any(Vec::is_empty),
            "{} has a pipeline inside its cycle that reads none, the drive's",
            store.borrow().name()
        );
        let mut members: Vec<Option<Member>> = members.into_iter().map(Some).collect();
        let members: Vec<Member> = kept
            .iter()
            .map(|&at| members[at].take().expect("a pipeline is kept once"))
            .collect();
        // A nested scope's own pipelines are planned in its own dispatcher.
        let mut planned = planned;
        for (plan, member) in planned.iter_mut().zip(&members) {
            if let Member::Scope(scope) = member {
                plan.rounds = std::mem::take(&mut scope.borrow_mut().planned);
            }
        }
        let starts = (0..members.len())
            .filter(|&at| reads[at].is_empty() || !matches!(members[at], Member::Chain(_)))
            .map(PipelineId)
            .collect();
        let placements = kept
            .iter()
            .map(|&at| pipelines.placements[at].clone())
            .collect();
        Self {
            store,
            inner,
            members,
            placements,
            starts,
            planned,
            opened: false,
            request: None,
            drive: std::cell::OnceCell::new(),
        }
    }

    pub(super) fn with_store<R>(&self, f: impl FnOnce(&mut dyn BreakingProducer) -> R) -> R {
        let mut store = self.store.borrow_mut();
        f(store
            .as_breaking_mut()
            .expect("a loop's store is a pipeline breaker"))
    }

    /// Place the inner pipelines' entries for as long as `run` takes.
    fn placed<R>(&self, run: impl FnOnce(&Self) -> R) -> R {
        let _placed = Placed::new(&self.placements);
        run(self)
    }

    fn terminal(&self) -> bool {
        self.with_store(|store| store.held().is_universal())
    }

    /// The path of the position the drive emits next, which the next round runs: the next its
    /// source delivers. `None` once the source delivers no more.
    ///
    /// # Panics
    ///
    /// Where no source in the store's chain among the scope's pipelines, or more than one, is a
    /// drive.
    fn next_position(&self) -> Option<Vec<Value>> {
        let drive = self.drive();
        let mut next = None;
        reach_member(
            &self.store,
            &self.members[drive.0],
            drive,
            &mut |breaker, _| {
                next = breaker
                    .as_producer()
                    .and_then(|producer| producer.next_position())
                    .flatten();
            },
        );
        next
    }

    /// The drive: the one source pipeline in the store's chain whose breaker answers
    /// `TileProducer::next_position`.
    ///
    /// # Panics
    ///
    /// Where no source in the store's chain among the scope's pipelines, or more than one, is a
    /// drive.
    fn drive(&self) -> PipelineId {
        *self.drive.get_or_init(|| self.find_drive())
    }

    /// Have the entry in front of the drive's source record a decided push of the source's keys
    /// at `pipeline`, this scope's pipeline in the dispatcher around it, as decided positions of
    /// the store's input: the drive reads its source by pull, so no push of the source reaches the
    /// scope's entry otherwise, and the scope would park each round until the source is whole.
    pub(super) fn decide_through_drive(&self, pipeline: PipelineId) {
        let input = self.with_store(|store| store.input_tiling(InputId::ONLY));
        let mut target = None;
        reach_member(
            &self.store,
            &self.members[self.drive().0],
            self.drive(),
            &mut |breaker, _| {
                target = breaker
                    .as_producer()
                    .and_then(|producer| producer.decides_through());
            },
        );
        let target = target.expect("a loop's drive records its source's decided pushes");
        *target.borrow_mut() = Some((pipeline, input));
    }

    fn find_drive(&self) -> PipelineId {
        let drives: Vec<PipelineId> = self
            .starts
            .iter()
            .copied()
            .filter(|&start| {
                self.inner.is_source(start) && matches!(self.members[start.0], Member::Chain(_))
            })
            .filter(|&start| {
                let mut drive = false;
                reach_member(
                    &self.store,
                    &self.members[start.0],
                    start,
                    &mut |breaker, _| {
                        drive = breaker
                            .as_producer()
                            .is_some_and(|producer| producer.next_position().is_some());
                    },
                );
                drive
            })
            .collect();
        let [drive] = drives.as_slice() else {
            panic!(
                "a loop's scope has one drive among its sources, not {}",
                drives.len()
            )
        };
        *drive
    }

    /// The paths a push from the range in front of `consumer` takes to the drive's entry, as the
    /// consumers on the way declare them (`Consumer::route`).
    pub(super) fn routes(&self, consumer: &SharedConsumer) -> Vec<Route> {
        let drive = self.drive();
        self.placed(|_| routes_to(consumer, drive.0))
    }

    /// Where a push of `region` from the range in front of `consumer` lands at the drive's entry,
    /// as guards of the drive's input, the drive's source: a planner probes how a live source's
    /// arrivals reach the scope's rounds.
    pub(super) fn arrivals(&self, consumer: &SharedConsumer, region: &Projection) -> Vec<Arrival> {
        let drive = self.drive();
        self.placed(|_| probe(consumer, drive, region, drive.0))
    }

    /// Have the drive read what its source holds, emitting nothing: a consume at no position. A
    /// loop nested in another learns the positions of a row once the round of the loop around it
    /// has run, so the scope reads them before it runs the row's rounds.
    fn read_source(&self) {
        let drive = self.drive();
        reach_member(
            &self.store,
            &self.members[drive.0],
            drive,
            &mut |breaker, input| {
                let none = breaker.input_tiling(input).empty_guard();
                breaker.consume_impl(input, none);
            },
        );
    }

    /// Run the inner dispatcher until nothing is claimable, and answer whether it is done. On one
    /// thread nothing else advances it, so every inner pipeline is then quiescent.
    fn run_inner(&self) -> bool {
        let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
            reach_member(&self.store, &self.members[pipeline.0], pipeline, call)
        };
        loop {
            match self.inner.try_claim(None) {
                Next::Package(package) => consume_with(&self.inner, &mut reach, package),
                Next::Finish { pipeline, consumed } => {
                    finish_with(&self.inner, &mut reach, pipeline, consumed)
                }
                Next::Wait(_) => return false,
                Next::Done => return true,
                Next::Failed => {
                    panic!("a loop's rounds run on one thread, which fails by panicking")
                }
            }
        }
    }

    /// Run the round queued. No finish ends a round, so each inner pipeline pushes what it has
    /// decided and no push named, and the inner dispatcher runs until nothing is claimable, again
    /// until a pass changes nothing: a pipeline the round queues nothing, as the drive in a closing
    /// round, states there what it read past, and a breaker that pushes only at a finish, as
    /// `MapAggregate`, hands its readers the round's groups.
    ///
    /// The pipelines that follow others are held while those passes run, and released for one
    /// claim at a time, after which the passes settle again: a follower reads by pull what it
    /// follows, which is quiescent before its pushes settle, and a follower's consume can feed
    /// another breaker that pushes only at `push_held`.
    fn run_round(&self) {
        let mut reach = |pipeline: PipelineId, call: &mut Call<'_>| {
            reach_member(&self.store, &self.members[pipeline.0], pipeline, call)
        };
        loop {
            self.inner
                .hold_followers((0..self.members.len()).map(PipelineId), true);
            loop {
                let before = self.inner.changes();
                push_held(&self.inner, &mut reach);
                self.run_inner();
                if self.inner.changes() == before {
                    break;
                }
            }
            self.inner
                .hold_followers((0..self.members.len()).map(PipelineId), false);
            match self.inner.try_claim(None) {
                Next::Package(package) => consume_with(&self.inner, &mut reach, package),
                Next::Finish { pipeline, consumed } => {
                    finish_with(&self.inner, &mut reach, pipeline, consumed)
                }
                Next::Wait(_) | Next::Done => return,
                Next::Failed => {
                    panic!("a loop's rounds run on one thread, which fails by panicking")
                }
            }
        }
    }

    fn closing_readers(&self) -> Vec<PipelineId> {
        (0..self.members.len())
            .map(PipelineId)
            .filter(|&pipeline| {
                !(self.inner.is_source(pipeline)
                    && matches!(self.members[pipeline.0], Member::Chain(_)))
            })
            .collect()
    }

    /// The row `guard`, a guard of the store's input, as each inner pipeline in `readers` takes
    /// it: where a push of the row from the drive reaches the pipeline's entry, what it lands as
    /// there, restated by every operator on the way, as `Uncurry` restates the row as the pairs it
    /// heads; elsewhere the row itself, for a pipeline whose input the store's positions key.
    fn row_for(&self, guard: &TileGuard, readers: &[PipelineId]) -> Vec<(PipelineId, TileGuard)> {
        let drive = self.drive();
        let mut consumer = None;
        reach_member(
            &self.store,
            &self.members[drive.0],
            drive,
            &mut |breaker, _| {
                consumer = breaker
                    .as_producer()
                    .and_then(|producer| producer.base().downstream.clone());
            },
        );
        let consumer = consumer.expect("a loop's drive pushes to the pipelines that read it");
        let region = Projection::of(guard)
            .unwrap_or_else(|why| panic!("a loop's round names a row of its store: {why}"));
        let mut landing = Landing::probe(drive);
        consumer.borrow_mut().push(&region, &mut landing);
        let arrivals = landing.arrivals();
        readers
            .iter()
            .flat_map(|&reader| {
                let landed: Vec<(PipelineId, TileGuard)> = arrivals
                    .iter()
                    .filter(|arrival| arrival.pipeline.0 == reader.0)
                    .map(|arrival| (reader, arrival.guard.clone()))
                    .collect();
                if !landed.is_empty() {
                    return landed;
                }
                let mut fits = false;
                reach_member(
                    &self.store,
                    &self.members[reader.0],
                    reader,
                    &mut |breaker, input| fits = guard.check_from(&breaker.input_tiling(input)),
                );
                match fits {
                    true => vec![(reader, guard.clone())],
                    false => Vec::new(),
                }
            })
            .collect()
    }

    fn begin_request(&mut self, guard: TileGuard) {
        assert!(
            self.request.is_none(),
            "a loop completes one request before starting another"
        );
        if !self.opened {
            // The drive reads before the opening step, so the step emits no position outside
            // a round. Each emitted position must run the body before the next store step.
            self.read_source();
            self.with_store(|store| {
                let none = store.input_tiling(InputId::ONLY).empty_guard();
                store.consume_impl(InputId::ONLY, none);
            });
            self.opened = true;
        }
        let rows = self.with_store(|store| !matches!(store.tiling(), Tiling::Store { .. }));
        if rows {
            self.placed(|scope| scope.read_source());
        }
        self.request = Some(Request {
            guard,
            rows,
            read: rows,
            rounds: 0,
            closing: false,
            round: None,
        });
    }

    /// Queue one round. The request remains pending until a later call finds no more rounds.
    fn queue_next_round(&mut self) -> bool {
        let mut request = self.request.take().expect("a loop has a pending request");
        assert!(
            request.round.is_none(),
            "the body and store step complete before the next round"
        );
        if request.closing {
            return false;
        }
        loop {
            if !self.terminal()
                && let Some(position) = self.next_position()
                && request.guard.covers_path(&position)
            {
                let guard = self.with_store(|store| {
                    Projection::of_path(&position).guard(&store.input_tiling(InputId::ONLY))
                });
                self.placed(|scope| scope.queue_round(&guard, &scope.starts));
                request.rounds += 1;
                request.round = Some(guard);
                self.request = Some(request);
                return true;
            }
            // A flat scope reads newly delivered source positions at most once per request,
            // after exhausting the positions the drive buffered before this request.
            if request.read || self.terminal() || self.next_position().is_some() {
                break;
            }
            self.placed(|scope| scope.read_source());
            request.read = true;
        }
        let closing = request.rows
            || (request.rounds == 0
                && !self.terminal()
                && !guard_minus(
                    &request.guard,
                    &self.with_store(|store| store.input_released(InputId::ONLY)),
                )
                .is_empty());
        if !closing {
            return false;
        }
        self.placed(|scope| {
            // A row's last position does not state the row's end. Render the drive once more
            // at no position so the closing round can release the row whole, including an
            // empty row. A flat request closes only positions the source emitted none of.
            if request.rows {
                scope.read_source();
            }
            scope.queue_round(&request.guard, &scope.closing_readers());
        });
        request.closing = true;
        request.round = Some(request.guard.clone());
        self.request = Some(request);
        true
    }

    /// Step the queued round after its body and held pushes settle.
    fn complete_round(&mut self) {
        let guard = self
            .request
            .as_mut()
            .and_then(|request| request.round.take())
            .expect("a loop steps one queued round");
        self.placed(|scope| scope.step(&guard));
    }

    /// Queue the body's work for one position or closing row, before the store steps it.
    fn queue_round(&self, guard: &TileGuard, starts: &[PipelineId]) {
        self.with_store(|store| store.read_cycle_again());
        let (sources, readers): (Vec<PipelineId>, Vec<PipelineId>) = starts
            .iter()
            .partition(|&&start| self.inner.is_source(start));
        for source in sources {
            self.inner.notify(source, guard);
        }
        for (reader, row) in self.row_for(guard, &readers) {
            // A reader whose input has released the whole row consumed it final, its end
            // included, and reads it no more: it is no longer there to read. A row released in
            // part is read again whole, for its end.
            let mut released = false;
            reach_member(
                &self.store,
                &self.members[reader.0],
                reader,
                &mut |breaker, input| {
                    released = guard_minus(&row, &breaker.input_released(input)).is_empty()
                },
            );
            if !released {
                self.inner.queue_round(reader, &row);
            }
        }
    }

    /// Step the store after the round's body and held pushes have settled.
    fn step(&self, guard: &TileGuard) {
        self.with_store(|store| {
            store.consume_impl(InputId::ONLY, guard.clone());
            // The round's pipelines ran before the step, so the store's input releases the
            // round's position.
            assert!(
                store.held().is_universal()
                    || guard_minus(guard, &store.input_released(InputId::ONLY)).is_empty(),
                "{}'s step in the round of {guard:?} decides it",
                store.name()
            );
        });
    }
}

/// The reads of the pipelines `kept` holds, numbered by their place in it: a read of a pipeline
/// that is not kept is a read of the pipelines it reads.
fn reads_of_kept(reads: &[Vec<usize>], kept: &[usize]) -> Vec<Vec<usize>> {
    fn expand(reads: &[Vec<usize>], kept: &[usize], read: usize, into: &mut Vec<usize>) {
        match kept.iter().position(|&pipeline| pipeline == read) {
            Some(at) if !into.contains(&at) => into.push(at),
            Some(_) => {}
            None => {
                for &beneath in &reads[read] {
                    expand(reads, kept, beneath, into);
                }
            }
        }
    }
    kept.iter()
        .map(|&pipeline| {
            let mut into = Vec::new();
            for &read in &reads[pipeline] {
                expand(reads, kept, read, &mut into);
            }
            into
        })
        .collect()
}

/// Call `call` with `member`'s breaker, the inner pipeline `pipeline`'s: in `store`'s chain, or
/// a nested loop's scope.
fn reach_member(store: &StoreCell, member: &Member, pipeline: PipelineId, call: &mut Call<'_>) {
    match member {
        Member::Scope(scope) => call(&mut *scope.borrow_mut(), InputId::ONLY),
        Member::Chain(id) => {
            let mut store = store.borrow_mut();
            let mut call = Some(call);
            let mut found = false;
            store.visit_input_producers_mut(&mut |_, input| {
                found = found || reach_in_chain(input, *id, &mut call);
            });
            assert!(
                found,
                "inner pipeline {} has its breaker in the store's chain",
                pipeline.0
            );
        }
    }
}

impl Breaker for LoopScope {
    /// Puts the store and every breaker of the scope's dispatcher in consuming mode, a nested
    /// loop's scope among them. `members` holds only the pipelines `LoopScope::new` kept, so a
    /// breaker it dropped to pull mode, which the rounds read again, stays in pull mode.
    fn enter_consuming_mode(&mut self) {
        self.with_store(|store| store.enter_consuming_mode());
        for (at, member) in self.members.iter().enumerate() {
            reach_member(&self.store, member, PipelineId(at), &mut |breaker, _| {
                breaker.enter_consuming_mode()
            });
        }
    }

    /// Runs a round per position `guard` names that the drive emits, in order, until the store is
    /// terminal: a position the loop's source filters out runs no round. The first consume steps
    /// the store once before, which opens it at its seed and publishes it: the drive reads the
    /// open store, and its source, before it emits a position. A loop nested in another is
    /// queued one row of its store per round of the loop around it, and steps its store until
    /// the body has released the row whole, which a row of no position needs too.
    fn consume_impl(&mut self, _: InputId, guard: TileGuard) {
        self.begin_request(guard);
        while self.queue_next_round() {
            self.placed(|scope| scope.run_round());
            self.complete_round();
        }
    }

    fn input_tiling(&self, _: InputId) -> Tiling {
        self.with_store(|store| store.input_tiling(InputId::ONLY))
    }

    fn input_released(&self, _: InputId) -> TileGuard {
        self.with_store(|store| store.input_released(InputId::ONLY))
    }

    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        None
    }

    fn pushing(&self, push: &mut dyn FnMut(&dyn BreakingProducer)) {
        self.with_store(|store| push(&*store));
    }

    /// Ends the rounds, then pushes the store, which is terminal.
    ///
    /// # Panics
    ///
    /// Where the store is not terminal.
    fn finish(&mut self, pushes: &mut Pushes<'_>) {
        self.placed(|scope| {
            for &start in &scope.starts {
                if scope.inner.is_source(start) {
                    scope.inner.close(start);
                }
            }
            assert!(
                scope.run_inner(),
                "a loop's scope is done once its sources close"
            );
        });
        self.with_store(|store| {
            assert!(
                store.held().is_universal(),
                "{} finishes the run terminal",
                store.name()
            );
            pushes.push_final(&*store);
        });
    }
}

impl LoopScope {
    /// The addresses of the breakers of the inner pipelines in the store's chain
    /// ([`address`]), the ones a round queues or pushes packages to.
    pub(super) fn chain_breakers(&self) -> Vec<usize> {
        self.members
            .iter()
            .filter_map(|member| match member {
                Member::Chain(id) => Some(*id),
                Member::Scope(_) => None,
            })
            .collect()
    }

    /// The consumer the scope's pipeline pushes to, the store's, and whether the store pushes a
    /// region of its keys: a nested store pushes rows, and a flat store the positions its rounds
    /// decide where it pushes any before it is terminal (`pushes_decided_positions`). Any other
    /// pushes everything, once it is terminal.
    pub(super) fn pushing_end(&self) -> (SharedConsumer, bool) {
        self.with_store(|store| {
            let keyed = matches!(store.tiling(), Tiling::DataFunction { .. })
                || crate::interpreter::commit_operator::pushes_decided_positions(store.tiling());
            let downstream =
                store.base().downstream.clone().unwrap_or_else(|| {
                    panic!("{} is read, so it pushes to a consumer", store.name())
                });
            (downstream, keyed)
        })
    }
}

/// The inner pipelines' entries placed in their pipelines, from construction until the drop. A
/// push that reaches an inner entry comes from inside the cycle or from a pipeline beneath it;
/// one beneath it has finished before the scope consumes, since the scope's pipeline reads it
/// whole or waits for its finish, and its push stops at the unplaced entry, as a push of the
/// enclosing dispatcher must: the entry's pipeline is the inner dispatcher's.
struct Placed<'p> {
    placements: &'p [Vec<Placement>],
}

impl<'p> Placed<'p> {
    fn new(placements: &'p [Vec<Placement>]) -> Self {
        for (pipeline, placements) in placements.iter().enumerate() {
            for placement in placements {
                debug_assert!(
                    placement.get().is_none(),
                    "a loop scope's inner entries are unplaced while the scope does not run"
                );
                placement.set(Some(PipelineId(pipeline)));
            }
        }
        Self { placements }
    }
}

impl Drop for Placed<'_> {
    fn drop(&mut self) {
        for placement in self.placements.iter().flatten() {
            placement.set(None);
        }
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    use super::super::plan::Planner;
    use super::*;
    use crate::ccl::context::{GlobalContext, compile_program};
    use crate::ccl::load::LoadedProgram;
    use crate::interpreter::commit_operator::store_frontier;
    use crate::interpreter::operator_conversion::OperatorMap;
    use crate::interpreter::tile_operators::TileProducer;
    use crate::interpreter::tile_operators::test_helpers::keys_between;
    use crate::interpreter::{Position, Tile};

    /// `total` summed over `[1, 2, 3]` and written to `out`: 6.
    const SUM: &str = indoc! {"
        out = test_sink()
        total := 0
        for x in [1, 2, 3]:
            total += x
        out << total
    "};

    /// [`SUM`] with the write guarded by `x > 1`: 5. The guard puts `Memo`s inside the cycle,
    /// between the drive's and the store's body.
    const GUARDED_SUM: &str = indoc! {"
        out = test_sink()
        total := 0
        for x in [1, 2, 3]:
            if x > 1:
                total += x
        out << total
    "};

    /// A program compiled with its sinks unpulled and no notification delivered, and the scope of
    /// its one store.
    struct Compiled {
        _ctx: GlobalContext,
        operators: OperatorMap,
        scope: LoopScope,
    }

    impl Compiled {
        fn of(source: &str) -> Self {
            let mut ctx = GlobalContext::default();
            ctx.defer_sink_pulls();
            let _sink = ctx.register_test_sink("out");
            let loaded = LoadedProgram::test(source);
            compile_program(&mut ctx, &loaded, Box::new(|| {}))
                .unwrap_or_else(|errors| panic!("{source} compiles: {errors:?}"));
            let operators = ctx.take_operator_map();
            let stores: Vec<_> = operators
                .operators()
                .into_iter()
                .filter(|fan| fan.cached_tile().is_some())
                .collect();
            assert_eq!(stores.len(), 1, "one store");
            let mut planner = Planner::default();
            planner.store_pipeline(crate::interpreter::tile_operators::StoreRead {
                fan: stores[0].id(),
                store: stores[0].store().expect("the program subscribed its store"),
            });
            assert_eq!(planner.scopes.len(), 1, "an induction store runs in rounds");
            let mut scope = planner.build_scope(0, usize::MAX, &mut Vec::new());
            scope.enter_consuming_mode();
            Self {
                _ctx: ctx,
                operators,
                scope,
            }
        }

        /// The store as a consuming breaker answers it.
        fn snapshot(&self) -> Tile {
            self.scope.with_store(|store| {
                let guard = store.tiling().universal_guard();
                store.offer_impl(guard)
            })
        }

        /// The value the store holds for its one variable.
        fn value(&self) -> Value {
            let state = self.operators.live_state();
            assert_eq!(state.len(), 1, "one variable: {state:?}");
            state.into_values().next().expect("one variable")
        }
    }

    /// A morsel of one position is one round, which decides the position; the round of the last
    /// position leaves the store terminal, holding what pull mode writes, and its body released.
    #[test]
    fn a_round_decides_its_position() {
        let mut compiled = Compiled::of(SUM);
        for position in [0, 1] {
            compiled
                .scope
                .consume_impl(InputId::ONLY, keys_between(position, position));
            let snapshot = compiled.snapshot();
            assert_eq!(
                store_frontier(&snapshot),
                Some(Position::new(Value::UInt(position))),
                "the round of position {position} decides it"
            );
            assert!(!snapshot.is_terminal());
        }
        compiled
            .scope
            .consume_impl(InputId::ONLY, keys_between(2, 2));
        assert!(compiled.snapshot().is_terminal());
        assert!(
            compiled.scope.input_released(InputId::ONLY).is_universal(),
            "a terminal body whose every decision is stepped is released whole"
        );
        assert_eq!(compiled.value(), Value::Int(6));
    }

    #[test]
    fn requests_resume_between_rounds_independently() {
        let mut sum = Compiled::of(SUM);
        let mut guarded = Compiled::of(GUARDED_SUM);
        for compiled in [&mut sum, &mut guarded] {
            let whole = compiled.scope.input_tiling(InputId::ONLY).universal_guard();
            compiled.scope.begin_request(whole);
            assert!(compiled.scope.queue_next_round());
        }
        for position in 0..3 {
            for compiled in [&mut sum, &mut guarded] {
                assert!(compiled.scope.request.is_some());
                compiled.scope.placed(|scope| scope.run_round());
                compiled.scope.complete_round();
                assert_eq!(
                    store_frontier(&compiled.snapshot()),
                    Some(Position::new(Value::UInt(position))),
                );
                if position < 2 {
                    assert!(compiled.scope.queue_next_round());
                } else {
                    assert!(!compiled.scope.queue_next_round());
                    assert!(compiled.scope.request.is_none());
                }
            }
            if position < 2 {
                assert!(!sum.snapshot().is_terminal());
                assert!(!guarded.snapshot().is_terminal());
            }
        }
        assert!(sum.snapshot().is_terminal());
        assert!(guarded.snapshot().is_terminal());
        assert_eq!(sum.value(), Value::Int(6));
        assert_eq!(guarded.value(), Value::Int(5));
    }

    #[test]
    #[should_panic(expected = "the body and store step complete before the next round")]
    fn a_request_cannot_queue_the_next_round_before_stepping() {
        let mut compiled = Compiled::of(SUM);
        let whole = compiled.scope.input_tiling(InputId::ONLY).universal_guard();
        compiled.scope.begin_request(whole);
        assert!(compiled.scope.queue_next_round());
        compiled.scope.queue_next_round();
    }

    /// A guarded loop's `Memo`s are inner pipelines, which each round queues the position for and
    /// runs before the store steps.
    #[test]
    fn a_guarded_loop_runs_its_memos_each_round() {
        let mut compiled = Compiled::of(GUARDED_SUM);
        let kinds = |kind: &str| {
            compiled
                .scope
                .planned
                .iter()
                .filter(|plan| plan.name.starts_with(kind))
                .count()
        };
        assert!(
            kinds("InductionDriver") == 1 && kinds("Memo") >= 1,
            "the drive and the guard's `Memo`s: {:?}",
            compiled.scope.planned
        );
        let whole = compiled.scope.input_tiling(InputId::ONLY).universal_guard();
        compiled.scope.consume_impl(InputId::ONLY, whole);
        assert!(compiled.snapshot().is_terminal());
        assert_eq!(compiled.value(), Value::Int(5));
    }

    /// The store holds the positions its rounds decided before it is terminal, and everything
    /// after.
    #[test]
    fn the_store_holds_its_decided_positions_then_everything_once_terminal() {
        let mut compiled = Compiled::of(SUM);
        compiled
            .scope
            .consume_impl(InputId::ONLY, keys_between(0, 0));
        let (held, decided) = compiled
            .scope
            .with_store(|store| (store.final_guard(), store.decided()));
        assert!(
            !held.is_empty() && !held.is_universal() && held == decided,
            "{held:?}, deciding {decided:?}"
        );
        compiled
            .scope
            .consume_impl(InputId::ONLY, keys_between(1, 2));
        assert!(
            compiled
                .scope
                .with_store(|store| store.final_guard().is_universal())
        );
    }

    /// A call on the drive [`with_drive`] finds.
    type OnDrive<'f> = dyn FnMut(&mut dyn TileProducer) + 'f;

    /// Call `f` with the drive in `scope`'s store's chain: the producer that answers a next
    /// position.
    fn with_drive(scope: &LoopScope, f: impl FnOnce(&mut dyn TileProducer)) {
        fn find(producer: &mut dyn TileProducer, f: &mut Option<&mut OnDrive<'_>>) {
            if producer.next_position().is_some() {
                (f.take().expect("one drive in the store's chain"))(producer);
                return;
            }
            producer.visit_input_producers_mut(&mut |_, input| find(input, f));
        }
        let mut f = Some(f);
        let mut call = |drive: &mut dyn TileProducer| (f.take().expect("called once"))(drive);
        let mut call: Option<&mut OnDrive<'_>> = Some(&mut call);
        scope.with_store(|store| {
            store.visit_input_producers_mut(&mut |_, input| find(input, &mut call));
        });
        assert!(call.is_none(), "the store's chain holds a drive");
    }

    /// How many pulls `drive`'s source has taken.
    fn source_pulls(drive: &dyn TileProducer) -> u64 {
        let mut pulls = 0;
        drive.visit_input_producers(&mut |role, input| {
            if role == "source" {
                pulls = input.base().pulls;
            }
        });
        pulls
    }

    /// A consume of the drive emits a position only where its package names it: not a position
    /// past the next, not for an empty package, and the next where the package names it. A
    /// consuming drive answers a pull from that consume and reads its source no more.
    #[test]
    fn a_drive_emits_only_the_position_its_package_names() {
        let compiled = Compiled::of(SUM);
        // As the scope's first consume does: the drive reads its source, then the store opens.
        compiled.scope.read_source();
        compiled.scope.with_store(|store| {
            let none = store.input_tiling(InputId::ONLY).empty_guard();
            store.consume_impl(InputId::ONLY, none);
        });
        let held = |drive: &mut dyn TileProducer| {
            drive
                .as_breaking_mut()
                .expect("the drive is a pipeline breaker")
                .held()
        };
        with_drive(&compiled.scope, |drive| {
            assert_eq!(drive.next_position(), Some(Some(vec![Value::UInt(0)])));
            let breaker = drive
                .as_breaking_mut()
                .expect("the drive is a pipeline breaker");
            breaker.consume_impl(InputId::ONLY, keys_between(1, 1));
            breaker.consume_impl(
                InputId::ONLY,
                breaker.input_tiling(InputId::ONLY).empty_guard(),
            );
            assert!(
                !held(drive).covers_path(&[Value::UInt(0)]),
                "nothing emitted"
            );
            let breaker = drive
                .as_breaking_mut()
                .expect("the drive is a pipeline breaker");
            breaker.consume_impl(InputId::ONLY, keys_between(0, 0));
            assert!(
                held(drive).covers_path(&[Value::UInt(0)]),
                "position 0 emitted"
            );
            assert_eq!(drive.next_position(), Some(Some(vec![Value::UInt(1)])));
            let before = source_pulls(drive);
            let whole = drive.tiling().universal_guard();
            let pulled = drive.get(whole);
            assert!(pulled.to_guard().covers_path(&[Value::UInt(0)]));
            assert_eq!(
                drive.next_position(),
                Some(Some(vec![Value::UInt(1)])),
                "a pull emits nothing"
            );
            assert_eq!(source_pulls(drive), before, "a pull reads no source");
        });
    }

    /// A scope whose store is not terminal at its finish panics.
    #[test]
    #[should_panic(expected = "finishes the run terminal")]
    fn a_scope_short_of_terminal_at_its_finish_panics() {
        let mut compiled = Compiled::of(SUM);
        compiled
            .scope
            .consume_impl(InputId::ONLY, keys_between(0, 0));
        let dispatcher = Dispatcher::new(vec![vec![]], usize::MAX);
        dispatcher.finish_by_hand(PipelineId(0), |pushes| compiled.scope.finish(pushes));
    }
}
