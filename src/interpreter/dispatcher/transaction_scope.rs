//! Transaction requests and attempts on the run's shared dispatcher.
//!
//! As for loop rounds, request and step handlers control the recurrence boundary. The
//! driver, body breakers and proposal writer are ordinary pipelines between those handlers.

use super::loop_scope::{Body, RoundWork};
use super::*;
use crate::interpreter::commit_operator::CommitProducer;
use crate::interpreter::tile_operators::{StoreBorrow, StoreCell};

/// A seed claim owns the store through its breaker call. The borrow ends before the
/// resulting pushes land, since a reader can reach the same store.
pub(super) struct ReservedSeed<'a> {
    pub(super) store: StoreBorrow<'a>,
    pub(super) input: InputId,
}

impl ReservedSeed<'_> {
    pub(super) fn reach(mut self, call: &mut Call<'_>) {
        call(
            self.store
                .as_breaking_mut()
                .expect("a transaction seed breaker"),
            self.input,
        );
    }
}

#[cfg(test)]
thread_local! {
    /// The requests on this thread that ended with positions waiting for inputs
    /// ([`CommitProducer::finish_request`]'s stall), for a test that has to see that path taken.
    /// A run's worker threads add their counts to the thread that runs it once they join
    /// (`WorkerPool::hand_over_counters`).
    pub(crate) static STALLS: Cell<usize> = const { Cell::new(0) };
}

pub(crate) struct TransactionRun {
    pub(super) writers: Vec<WriterRun>,
    /// Incremented whenever an attempt can change what another writer reads.
    pub(super) progress: u64,
}

impl TransactionRun {
    /// The planned driver is stable for the run even while another worker is pulling its fan-out.
    pub(crate) fn writer_driver(&self, writer: usize) -> &BreakerHandle {
        let body = &self.writers[writer].body;
        let loop_scope::Member::Chain(driver) = &body.members[body.driver.0] else {
            unreachable!("a transaction driver is a chain")
        };
        driver
    }

    /// Wake parked peers on progress. An incomplete request may park once it has tried the
    /// current epoch. Overlapping attempts that read an older epoch get another turn.
    pub(super) fn settle(&mut self, writer: usize, queued_at: u64, progressed: bool) -> bool {
        if progressed {
            self.progress += 1;
            for (index, peer) in self.writers.iter().enumerate() {
                if index != writer {
                    peer.body.offer_waiting();
                }
            }
        }
        // An overlapping attempt may have read the old snapshot. Retry it once at the new epoch.
        queued_at == self.progress
    }
}

pub(super) struct WriterRun {
    pub(super) body: Body,
}

/// A writer's attempt state, which its request and step handlers advance one at a time under the
/// scope's own cell (`Scope::Writer` in `scope.rs`).
#[derive(Default)]
pub(super) enum WriterPhase {
    #[default]
    Idle,
    Attempt {
        /// The outstanding request, or `None` for the final attempt.
        request: Option<WorkPackage>,
        guard: TileGuard,
        queued_at: u64,
    },
    /// The final attempt has settled and the inner sources and step have closed.
    Draining,
    Finished,
}

impl WriterPhase {
    /// Open the request `package`, a claim of the writer's own pipeline.
    pub(super) fn begin(
        &mut self,
        store: &StoreCell,
        writer: usize,
        dispatcher: &Dispatcher,
        package: WorkPackage,
    ) {
        let work = transaction(store).begin_request(self, dispatcher, writer, package);
        work.queue(dispatcher);
    }

    /// End the attempt whose step claimed `package`: queue a retry, or complete the request.
    pub(super) fn step(
        &mut self,
        store: &StoreCell,
        writer: usize,
        dispatcher: &Dispatcher,
        package: WorkPackage,
    ) {
        #[cfg(test)]
        let pipeline = package.pipeline;
        dispatcher.acknowledge(package);
        let (done, work) = {
            let mut store = transaction(store);
            #[cfg(test)]
            if let Some(probe) = &dispatcher.scope_step_probe {
                probe(pipeline);
            }
            store.finish_request(self, dispatcher, writer)
        };
        work.queue(dispatcher);
        if self.open() {
            transaction(store)
                .writer_run(writer)
                .body
                .hold_followers(dispatcher);
        }
        scope::complete_request(dispatcher, done, |pushes| {
            transaction(store).push_store(pushes)
        });
    }

    /// The guard of the open attempt's step package.
    pub(super) fn step_guard(&self) -> Option<&TileGuard> {
        match self {
            Self::Attempt { guard, .. } => Some(guard),
            _ => None,
        }
    }

    pub(super) fn has_request(&self) -> bool {
        matches!(
            self,
            WriterPhase::Attempt {
                request: Some(_),
                ..
            }
        )
    }

    /// Whether the writer's followers wait on it: a request or a finish is open.
    pub(super) fn open(&self) -> bool {
        matches!(self, WriterPhase::Attempt { .. } | WriterPhase::Draining)
    }
}

impl WriterRun {
    pub(super) fn new(body: Body) -> Self {
        Self { body }
    }

    /// Activate the body for an attempt queued at the store's progress epoch `queued_at`, and
    /// answer the attempt's work, which is queued once the store is released.
    fn queue(
        &mut self,
        phase: &mut WriterPhase,
        dispatcher: &Dispatcher,
        request: Option<WorkPackage>,
        guard: TileGuard,
        queued_at: u64,
    ) -> RoundWork {
        let mut work = RoundWork::default();
        self.body.activate(dispatcher);
        self.body.hold_followers(dispatcher);
        // The request establishes readiness of the external source. Materialize any
        // source pipelines inside this writer before advancing its driver; the
        // driver may read a breaker carrying another transaction's reply.
        for local in 0..self.body.members.len() {
            let pipeline = self.body.global(PipelineId(local));
            if local != self.body.driver.0 && dispatcher.is_source(pipeline) {
                self.body.reach(PipelineId(local), &mut |breaker, input| {
                    work.queue_round(pipeline, &breaker.input_tiling(input).universal_guard());
                });
            }
        }
        self.body.queue_grown(&mut work);
        work.queue_round(self.body.global(self.body.driver), &guard);
        *phase = WriterPhase::Attempt {
            request,
            guard,
            queued_at,
        };
        work
    }

    pub(super) fn drain(&mut self, phase: &mut WriterPhase, dispatcher: &Dispatcher) {
        *phase = WriterPhase::Draining;
        self.body.close_sources(dispatcher);
        dispatcher.close(self.body.attached().step);
    }

    pub(super) fn take_finish(
        &mut self,
        phase: &mut WriterPhase,
        dispatcher: &Dispatcher,
    ) -> Option<PipelineId> {
        if !matches!(phase, WriterPhase::Draining) {
            return None;
        }
        let pipeline = self.body.finished_pipeline(dispatcher)?;
        *phase = WriterPhase::Finished;
        Some(pipeline)
    }
}

pub(super) struct TransactionBorrow<'a>(StoreBorrow<'a>);
impl std::ops::Deref for TransactionBorrow<'_> {
    type Target = CommitProducer;
    fn deref(&self) -> &Self::Target {
        self.0.as_transaction_store().expect("a transaction store")
    }
}
impl std::ops::DerefMut for TransactionBorrow<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
            .as_transaction_store_mut()
            .expect("a transaction store")
    }
}
pub(super) fn transaction(store: &StoreCell) -> TransactionBorrow<'_> {
    TransactionBorrow(store.write())
}

impl CommitProducer {
    pub(super) fn writer_run(&self, writer: usize) -> &WriterRun {
        &self
            .run
            .as_ref()
            .expect("a transaction run is planned")
            .writers[writer]
    }
    pub(super) fn writer_run_mut(&mut self, writer: usize) -> &mut WriterRun {
        &mut self
            .run
            .as_mut()
            .expect("a transaction run is planned")
            .writers[writer]
    }
    fn progress_epoch(&self) -> u64 {
        self.run
            .as_ref()
            .expect("a transaction run is planned")
            .progress
    }
    /// Queue the requests offered to writer `writer` on its pipeline, and close the pipeline once
    /// asked, where the store is open: an attempt reads the store, which exists once every seed
    /// key's value is final ([`Body::queue_offered`]). Whether it queued or closed anything.
    pub(super) fn queue_requests(&mut self, dispatcher: &Dispatcher, writer: usize) -> bool {
        if !self.writer_run(writer).body.has_offers(dispatcher) {
            return false;
        }
        let open = self.open_if_ready();
        self.writer_run_mut(writer)
            .body
            .queue_offered(dispatcher, open)
    }

    pub(super) fn begin_request(
        &mut self,
        phase: &mut WriterPhase,
        dispatcher: &Dispatcher,
        writer: usize,
        package: WorkPackage,
    ) -> RoundWork {
        let input = self.writer_input(writer);
        assert!(
            matches!(phase, WriterPhase::Idle),
            "a writer completes its request before another starts"
        );
        self.begin_delivery(input);
        self.begin_attempt();
        let mark = self.progress_epoch();
        let run = self.writer_run_mut(writer);
        let guard = match run.body.take_waited() {
            Some(waiting) => package.guard.union(&waiting),
            None => package.guard.clone(),
        };
        run.queue(phase, dispatcher, Some(package), guard, mark)
    }
    pub(super) fn finish_request(
        &mut self,
        phase: &mut WriterPhase,
        dispatcher: &Dispatcher,
        writer: usize,
    ) -> (Option<WorkPackage>, RoundWork) {
        let progressed = self.complete_attempt(writer);
        let transaction = self.run.as_mut().expect("a transaction run is planned");
        let WriterPhase::Attempt {
            request,
            guard,
            queued_at,
        } = std::mem::take(phase)
        else {
            unreachable!("a writer's step completes an attempt it queued")
        };
        let caught_up = transaction.settle(writer, queued_at, progressed);
        let Some(package) = request else {
            // A stale decision keeps its item in flight. Retry it before closing the sources.
            if self.holds_stale_item(writer) {
                assert!(
                    !caught_up,
                    "writer {writer}'s final retry made no progress on its stale item"
                );
                self.begin_attempt();
                let mark = self.progress_epoch();
                return (
                    None,
                    self.writer_run_mut(writer)
                        .queue(phase, dispatcher, None, guard, mark),
                );
            }
            self.writer_run_mut(writer).drain(phase, dispatcher);
            return (None, RoundWork::default());
        };
        if self.request_complete(self.writer_input(writer), &guard) {
            debug_assert!(
                !self.holds_stale_item(writer),
                "writer {writer}'s request completes with no stale decision in flight: the drive \
                 releases an item from its source only once its decision commits"
            );
            let run = self.writer_run_mut(writer);
            run.body.set_waiting(None, None);
            return (Some(package), RoundWork::default());
        }
        // The writer tried the current store and its body settled. The next relevant push,
        // or progress by a peer, reoffers its undecided positions.
        if caught_up {
            #[cfg(test)]
            STALLS.with(|stalls| stalls.set(stalls.get() + 1));
            let input = self.writer_input(writer);
            let waiting = guard_minus(&guard, &self.input_released(input));
            // A stale decision's item stays among the positions waiting for inputs. The store
            // releases an item of the drive's source only at its decision's commit
            // (`commit_ready`), and the request's guard holds every item its attempts decided. A
            // push that wakes those positions queues the item's retry, whichever input it reads.
            debug_assert!(
                self.stale_item(writer)
                    .is_none_or(|item| waiting.covers_path(std::slice::from_ref(item.value()))),
                "writer {writer}'s request waits for the item whose decision went stale: \
                 {:?} lies outside the positions waiting, {waiting:?}",
                self.stale_item(writer)
            );
            let entry = self.writer_placements[writer].clone();
            let run = self.writer_run_mut(writer);
            run.body.set_waiting(Some(waiting), Some(&entry));
            return (Some(package), RoundWork::default());
        }
        self.begin_attempt();
        let mark = self.progress_epoch();
        (
            None,
            self.writer_run_mut(writer)
                .queue(phase, dispatcher, Some(package), guard, mark),
        )
    }
    pub(super) fn begin_transaction_finish(
        &mut self,
        phase: &mut WriterPhase,
        dispatcher: &Dispatcher,
        writer: usize,
    ) -> RoundWork {
        assert!(
            matches!(phase, WriterPhase::Idle),
            "a writer finishes after its requests settle"
        );
        let whole = self
            .input_tiling(self.writer_input(writer))
            .universal_guard();
        self.begin_attempt();
        let mark = self.progress_epoch();
        let run = self.writer_run_mut(writer);
        run.queue(phase, dispatcher, None, whole, mark)
    }
}
