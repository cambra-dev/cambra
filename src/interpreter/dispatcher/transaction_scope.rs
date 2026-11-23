//! Transaction requests and attempts on the run's shared dispatcher.
//!
//! As for loop rounds, request and step handlers control the recurrence boundary. The
//! driver, body breakers and proposal writer are ordinary pipelines between those handlers.

use super::loop_scope::{Body, RoundWork};
use super::*;
use crate::interpreter::commit_operator::CommitProducer;
use crate::interpreter::tile_operators::StoreCell;

pub(crate) struct TransactionRun {
    pub(super) writers: Vec<WriterRun>,
    /// How many attempts in a row changed nothing a later attempt reads
    /// ([`CommitProducer::complete_attempt`]).
    pub(super) stalled: usize,
}

pub(super) struct WriterRun {
    pub(super) body: Body,
    attempt: Attempt,
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

    pub(super) fn release_followers(
        &mut self,
        dispatcher: &Dispatcher,
        read: FollowersHold,
    ) -> bool {
        self.open() && self.body.release_followers(dispatcher, read)
    }

    /// The step's follower hold, read before a publication pass, or `None` before the writer is
    /// attached.
    pub(super) fn followers_hold(&self, dispatcher: &Dispatcher) -> Option<FollowersHold> {
        self.body.followers_hold(dispatcher)
    }

    /// Activate the body, and answer the attempt's work, which is queued once the store is
    /// released.
    fn queue(&mut self, dispatcher: &Dispatcher, guard: &TileGuard) -> RoundWork {
        let mut work = RoundWork::default();
        self.body.activate(dispatcher);
        self.hold_followers(dispatcher);
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
        work.queue_round(self.body.global(self.body.driver), guard);
        self.body.end_round_with(guard);
        work
    }

    fn close(&self, dispatcher: &Dispatcher) {
        self.body.close_sources(dispatcher);
        dispatcher.close(self.body.attached().step);
    }
}

pub(super) struct TransactionBorrow<'a>(crate::interpreter::tile_operators::StoreBorrow<'a>);
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
    /// Queue the requests offered to writer `writer` on its pipeline, and close the pipeline once
    /// asked, where the store is open: an attempt reads the store, which exists once every seed
    /// key's value is final ([`Body::queue_offered`]). Whether it queued or closed anything.
    pub(super) fn queue_requests(&mut self, dispatcher: &Dispatcher, writer: usize) -> bool {
        if !self.writer_run(writer).body.has_offers() {
            return false;
        }
        let open = self.open_if_ready();
        self.writer_run_mut(writer)
            .body
            .queue_offered(dispatcher, open)
    }

    pub(super) fn begin_request(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
        package: WorkPackage,
    ) -> RoundWork {
        let input = self.writer_input(writer);
        assert!(
            matches!(self.writer_run(writer).attempt, Attempt::Idle),
            "a writer completes its request before another starts"
        );
        self.begin_delivery(input);
        self.begin_attempt();
        let run = self.writer_run_mut(writer);
        let guard = match run.body.waiting() {
            Some(waiting) => package.guard.union(&waiting),
            None => package.guard.clone(),
        };
        run.attempt = Attempt::Request(package, guard.clone());
        run.queue(dispatcher, &guard)
    }
    pub(super) fn finish_request(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
    ) -> (Option<WorkPackage>, RoundWork) {
        let progressed = self.complete_attempt(writer);
        let transaction = self.run.as_mut().expect("a transaction run is planned");
        transaction.stalled = match progressed {
            true => 0,
            false => transaction.stalled + 1,
        };
        let (stalled, writers) = (transaction.stalled, transaction.writers.len());
        let run = self.writer_run_mut(writer);
        let guard = match std::mem::replace(&mut run.attempt, Attempt::Idle) {
            Attempt::Finishing => {
                run.close(dispatcher);
                return (None, RoundWork::default());
            }
            Attempt::Request(package, guard) => {
                run.attempt = Attempt::Request(package, guard.clone());
                guard
            }
            Attempt::Idle => unreachable!("a writer's step completes an attempt it queued"),
        };
        if self.request_complete(self.writer_input(writer), &guard) {
            let run = self.writer_run_mut(writer);
            run.body.set_waiting(None, None);
            let Attempt::Request(package, _) = std::mem::replace(&mut run.attempt, Attempt::Idle)
            else {
                unreachable!("matched a request above")
            };
            return (Some(package), RoundWork::default());
        }
        // An attempt reads the store, its inputs and the decisions to attempt again. Once every
        // writer has attempted with none of those changed, no further attempt differs: the
        // request ends with what it has not decided waiting for inputs, and what the writer
        // pushes once an input grows is offered to its scope, which queues the next request.
        if stalled > writers {
            let input = self.writer_input(writer);
            let waiting = guard_minus(&guard, &self.input_released(input));
            let entry = self.writer_placements[writer].clone();
            let run = self.writer_run_mut(writer);
            run.body.set_waiting(Some(waiting), Some(&entry));
            let Attempt::Request(package, _) = std::mem::replace(&mut run.attempt, Attempt::Idle)
            else {
                unreachable!("matched a request above")
            };
            self.run
                .as_mut()
                .expect("a transaction run is planned")
                .stalled = 0;
            return (Some(package), RoundWork::default());
        }
        self.begin_attempt();
        (None, self.writer_run_mut(writer).queue(dispatcher, &guard))
    }
    pub(super) fn begin_transaction_finish(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
    ) -> RoundWork {
        assert!(
            matches!(self.writer_run(writer).attempt, Attempt::Idle),
            "a writer finishes after its requests settle"
        );
        let whole = self
            .input_tiling(self.writer_input(writer))
            .universal_guard();
        self.begin_attempt();
        let run = self.writer_run_mut(writer);
        run.attempt = Attempt::Finishing;
        run.body.begin_finish();
        run.queue(dispatcher, &whole)
    }
}
