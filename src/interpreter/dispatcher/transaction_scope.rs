//! Transaction requests and attempts on the run's shared dispatcher.
//!
//! As for loop rounds, request and step handlers control the recurrence boundary. The
//! driver, body breakers and proposal writer are ordinary pipelines between those handlers.

use super::loop_scope::Body;
use super::*;
use crate::interpreter::commit_operator::CommitProducer;
use crate::interpreter::tile_operators::StoreCell;

#[cfg(test)]
thread_local! {
    /// The requests on this thread that ended with positions waiting for inputs
    /// ([`CommitProducer::finish_request`]'s stall), for a test that has to see that path taken.
    /// A run's scopes step on the thread that runs it.
    pub(crate) static STALLS: Cell<usize> = const { Cell::new(0) };
}

pub(crate) struct TransactionRun {
    pub(super) writers: Vec<WriterRun>,
    /// Incremented whenever an attempt can change what another writer reads.
    pub(super) progress: u64,
}

impl TransactionRun {
    /// Wake parked peers on progress. An incomplete request may park once it has tried the
    /// current epoch. Overlapping attempts that read an older epoch get another turn.
    pub(super) fn settle(&mut self, writer: usize, progressed: bool) -> bool {
        if progressed {
            self.progress += 1;
            for (index, peer) in self.writers.iter().enumerate() {
                if index != writer {
                    peer.body.offer_waiting();
                }
            }
        }
        // An overlapping attempt may have read the old snapshot. Retry it once at the new epoch.
        self.writers[writer].queued_at == self.progress
    }
}

pub(super) struct WriterRun {
    pub(super) body: Body,
    attempt: Attempt,
    /// The store's progress when the active attempt was queued.
    queued_at: u64,
}

/// What a writer's attempts are for.
enum Attempt {
    /// No request is open and no finish has begun.
    Idle,
    /// Attempts toward this request run until it completes, over the request's positions and
    /// those an earlier request left waiting for inputs.
    Request(WorkPackage, TileGuard),
    /// The finish's attempt runs. Once it has, the sources close and the body finishes
    /// ([`Body::take_finish`]).
    Finishing,
}

impl WriterRun {
    pub(super) fn new(body: Body) -> Self {
        Self {
            body,
            attempt: Attempt::Idle,
            queued_at: 0,
        }
    }

    pub(super) fn has_request(&self) -> bool {
        matches!(self.attempt, Attempt::Request(..))
    }

    /// Whether the writer's followers wait on it: a request or a finish is open.
    fn open(&self) -> bool {
        !matches!(self.attempt, Attempt::Idle) || self.body.is_finishing()
    }

    pub(super) fn hold_followers(&mut self, dispatcher: &Dispatcher) {
        if self.open() {
            self.body.hold_followers(dispatcher);
        }
    }

    pub(super) fn release_followers(&mut self, dispatcher: &Dispatcher) -> bool {
        self.open() && self.body.release_followers(dispatcher)
    }

    /// Queue an attempt over `guard`, at the store's progress epoch `mark`.
    fn queue(&mut self, dispatcher: &Dispatcher, guard: &TileGuard, mark: u64) {
        self.queued_at = mark;
        self.body.activate(dispatcher);
        self.hold_followers(dispatcher);
        for local in 0..self.body.members.len() {
            let pipeline = self.body.global(PipelineId(local));
            if local != self.body.driver.0 && dispatcher.is_source(pipeline) {
                self.body.reach(PipelineId(local), &mut |breaker, input| {
                    dispatcher.queue_for(pipeline, &breaker.input_tiling(input).universal_guard());
                });
            }
        }
        self.body.queue_grown(dispatcher);
        dispatcher.queue_for(self.body.global(self.body.driver), guard);
        self.body.end_round_with(guard);
    }

    fn close(&self, dispatcher: &Dispatcher) {
        self.body.close_sources(dispatcher);
        dispatcher.close(self.body.attached().step);
    }
}

pub(super) fn transaction(
    store: &StoreCell,
) -> crate::interpreter::tile_operators::StoreBorrow<'_, CommitProducer> {
    store.borrow_mut().map(|producer| {
        producer
            .as_transaction_store_mut()
            .expect("a transaction store")
    })
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
        if !self.writer_run(writer).body.has_offers() {
            return false;
        }
        let open = self.open_store();
        self.writer_run_mut(writer)
            .body
            .queue_offered(dispatcher, open)
    }

    pub(super) fn begin_request(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
        package: WorkPackage,
    ) {
        let input = self.writer_input(writer);
        assert!(
            matches!(self.writer_run(writer).attempt, Attempt::Idle),
            "a writer completes its request before another starts"
        );
        self.begin_delivery(input);
        self.publish_commits();
        let mark = self.progress_epoch();
        let run = self.writer_run_mut(writer);
        let guard = match run.body.take_waited() {
            Some(waiting) => package.guard.union(&waiting),
            None => package.guard.clone(),
        };
        run.attempt = Attempt::Request(package, guard.clone());
        run.queue(dispatcher, &guard, mark);
    }
    pub(super) fn finish_request(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
    ) -> Option<WorkPackage> {
        let progressed = self.complete_attempt(writer);
        let transaction = self.run.as_mut().expect("a transaction run is planned");
        let caught_up = transaction.settle(writer, progressed);
        let holds_stale = self.holds_stale_decision(writer);
        let run = self.writer_run_mut(writer);
        let guard = match std::mem::replace(&mut run.attempt, Attempt::Idle) {
            // A stale decision leaves its item in flight, so the finish attempts again while one
            // does. Such an attempt always progresses, so the finish closes no writer holding one
            // (`src/interpreter/design-dispatcher.md`, "Transaction requests and attempts").
            Attempt::Finishing if holds_stale => {
                assert!(
                    !caught_up,
                    "writer {writer}'s final retry made no progress on its stale item"
                );
                let whole = self
                    .input_tiling(self.writer_input(writer))
                    .universal_guard();
                self.publish_commits();
                let mark = self.progress_epoch();
                let run = self.writer_run_mut(writer);
                run.attempt = Attempt::Finishing;
                run.queue(dispatcher, &whole, mark);
                return None;
            }
            Attempt::Finishing => {
                run.close(dispatcher);
                return None;
            }
            Attempt::Request(package, guard) => {
                run.attempt = Attempt::Request(package, guard.clone());
                guard
            }
            Attempt::Idle => unreachable!("a writer's step completes an attempt it queued"),
        };
        if self.request_complete(self.writer_input(writer), &guard) {
            debug_assert!(
                !self.holds_stale_decision(writer),
                "writer {writer}'s request completes with no stale decision in flight: the drive \
                 releases an item from its source only once its decision commits"
            );
            let run = self.writer_run_mut(writer);
            run.body.set_waiting(None, None);
            let Attempt::Request(package, _) = std::mem::replace(&mut run.attempt, Attempt::Idle)
            else {
                unreachable!("matched a request above")
            };
            return Some(package);
        }
        // The writer tried the current store and its body settled. The next relevant push,
        // or progress by a peer, reoffers its undecided positions.
        if caught_up {
            #[cfg(test)]
            STALLS.with(|stalls| stalls.set(stalls.get() + 1));
            let input = self.writer_input(writer);
            let waiting = guard_minus(&guard, &self.input_released(input));
            // A stale decision's item stays unreleased in the drive's source until a retry
            // commits, so the wait holds it, and the request that the wait's wake queues retries it.
            debug_assert!(
                !self.holds_stale_decision(writer) || !waiting.is_empty(),
                "writer {writer}'s request waits for the item whose decision went stale"
            );
            let entry = self.writer_placements[writer].clone();
            let run = self.writer_run_mut(writer);
            run.body.set_waiting(Some(waiting), Some(&entry));
            let Attempt::Request(package, _) = std::mem::replace(&mut run.attempt, Attempt::Idle)
            else {
                unreachable!("matched a request above")
            };
            return Some(package);
        }
        self.publish_commits();
        let mark = self.progress_epoch();
        self.writer_run_mut(writer).queue(dispatcher, &guard, mark);
        None
    }
    pub(super) fn begin_transaction_finish(&mut self, dispatcher: &Dispatcher, writer: usize) {
        assert!(
            matches!(self.writer_run(writer).attempt, Attempt::Idle),
            "a writer finishes after its requests settle"
        );
        let whole = self
            .input_tiling(self.writer_input(writer))
            .universal_guard();
        self.publish_commits();
        let mark = self.progress_epoch();
        let run = self.writer_run_mut(writer);
        run.attempt = Attempt::Finishing;
        run.body.begin_finish();
        run.queue(dispatcher, &whole, mark);
    }
}
