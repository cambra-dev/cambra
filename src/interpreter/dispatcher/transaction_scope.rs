//! Transaction requests and attempts on the run's shared dispatcher.
//!
//! As for loop rounds, request and step handlers control the recurrence boundary. The
//! driver, body breakers and proposal writer are ordinary pipelines between those handlers.

use super::loop_scope::{Body, RoundWork};
use super::*;
use crate::interpreter::commit_operator::CommitProducer;
use crate::interpreter::tile_operators::StoreCell;

#[cfg(test)]
thread_local! {
    /// The requests on this thread that ended with positions waiting for inputs
    /// ([`CommitProducer::finish_request`]'s stall), for a test that has to see that path taken.
    /// A run's worker threads add their counts to the thread that runs it once they join
    /// (`WorkerPool::hand_over_counters`).
    pub(crate) static STALLS: Cell<usize> = const { Cell::new(0) };
}

impl TransactionRun {
    /// Whether a writer has a request open or a finish begun.
    #[cfg(test)]
    pub(crate) fn has_open_request(&self) -> bool {
        self.writers
            .iter()
            .any(|writer| !matches!(writer.attempt, Attempt::Idle))
    }
}

pub(crate) struct TransactionRun {
    pub(super) writers: Vec<WriterRun>,
    pub(super) stalls: Stalls,
}

/// The attempts without progress across a store's writers, which end a request once they
/// outnumber the writers ([`CommitProducer::finish_request`]). An attempt progresses as
/// [`CommitProducer::complete_attempt`] answers.
///
/// An attempt counts toward a stall only if it was queued since the last attempt that progressed.
/// Each writer has one attempt at a time, and the writers' attempts overlap. An attempt queued
/// before another writer's progress may have run its pipelines before that progress, so it does
/// not show that an attempt queued now would change nothing.
#[derive(Default)]
pub(super) struct Stalls {
    /// How many attempts of this run have progressed.
    progressed: u64,
    /// How many attempts in a row changed nothing, each queued since the last progress.
    stalled: usize,
}

impl Stalls {
    /// The mark that an attempt queued now passes to [`complete`](Self::complete).
    fn mark(&self) -> u64 {
        self.progressed
    }

    /// Count an attempt queued at `mark`, and answer how many attempts in a row have stalled.
    fn complete(&mut self, mark: u64, progressed: bool) -> usize {
        debug_assert!(
            mark <= self.progressed,
            "an attempt's mark is a progress count already reached"
        );
        if progressed {
            self.progressed += 1;
            self.stalled = 0;
        } else if mark == self.progressed {
            self.stalled += 1;
        }
        self.stalled
    }

    /// Start counting again, once a stall has ended a request.
    fn reset(&mut self) {
        self.stalled = 0;
    }
}

pub(super) struct WriterRun {
    pub(super) body: Body,
    attempt: Attempt,
    /// The [`Stalls::mark`] taken when the open attempt was queued.
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

    pub(super) fn release_followers(
        &mut self,
        dispatcher: &Dispatcher,
        read: FollowersHold,
    ) -> bool {
        self.open() && self.body.release_followers(dispatcher, read)
    }

    /// The body's follower hold, read before a publication pass, or `None` before the writer is
    /// attached.
    pub(super) fn followers_hold(&self, dispatcher: &Dispatcher) -> Option<FollowersHold> {
        self.body.followers_hold(dispatcher)
    }

    /// Activate the body for an attempt queued at the stall count's `mark` ([`Stalls::mark`]), and
    /// answer the attempt's work, which is queued once the store is released.
    fn queue(&mut self, dispatcher: &Dispatcher, guard: &TileGuard, mark: u64) -> RoundWork {
        self.queued_at = mark;
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
    fn stall_mark(&self) -> u64 {
        self.run
            .as_ref()
            .expect("a transaction run is planned")
            .stalls
            .mark()
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
        let mark = self.stall_mark();
        let run = self.writer_run_mut(writer);
        let guard = match run.body.waiting() {
            Some(waiting) => package.guard.union(&waiting),
            None => package.guard.clone(),
        };
        run.attempt = Attempt::Request(package, guard.clone());
        run.queue(dispatcher, &guard, mark)
    }
    pub(super) fn finish_request(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
    ) -> (Option<WorkPackage>, RoundWork) {
        let progressed = self.complete_attempt(writer);
        let transaction = self.run.as_mut().expect("a transaction run is planned");
        let queued_at = transaction.writers[writer].queued_at;
        let stalled = transaction.stalls.complete(queued_at, progressed);
        let writers = transaction.writers.len();
        let holds_stale = self.holds_stale_decision(writer);
        let retry_finish = stalled <= writers && holds_stale;
        let run = self.writer_run_mut(writer);
        let guard = match std::mem::replace(&mut run.attempt, Attempt::Idle) {
            // A stale decision leaves its item in flight, so the finish attempts again while one
            // does. Such an attempt always progresses, so the finish closes no writer holding one
            // (`src/interpreter/design-dispatcher.md`, "Transaction requests and attempts").
            Attempt::Finishing if retry_finish => {
                let whole = self
                    .input_tiling(self.writer_input(writer))
                    .universal_guard();
                self.begin_attempt();
                let mark = self.stall_mark();
                let run = self.writer_run_mut(writer);
                run.attempt = Attempt::Finishing;
                return (None, run.queue(dispatcher, &whole, mark));
            }
            Attempt::Finishing => {
                debug_assert!(
                    !holds_stale,
                    "writer {writer}'s finish closes it with no stale decision in flight: an \
                     attempt that holds one decides its item again at a later frontier, which \
                     progresses"
                );
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
            return (Some(package), RoundWork::default());
        }
        // An attempt reads the store and its inputs, and a writer's drive emits its item again
        // after a stale decision. Once more consecutive attempts than the store has writers do not
        // progress (`CommitProducer::complete_attempt`), counted across the writers and each
        // queued since the last progress ([`Stalls`]), no further attempt differs. The request
        // then ends with what it has not decided waiting for inputs, and what the writer pushes
        // once an input grows is offered to its scope, which queues the next request.
        if stalled > writers {
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
            self.run
                .as_mut()
                .expect("a transaction run is planned")
                .stalls
                .reset();
            return (Some(package), RoundWork::default());
        }
        self.begin_attempt();
        let mark = self.stall_mark();
        (
            None,
            self.writer_run_mut(writer).queue(dispatcher, &guard, mark),
        )
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
        let mark = self.stall_mark();
        let run = self.writer_run_mut(writer);
        run.attempt = Attempt::Finishing;
        run.body.begin_finish();
        run.queue(dispatcher, &whole, mark)
    }
}

#[cfg(test)]
mod tests {
    use super::Stalls;

    /// Two writers, as `keyed_writes_from_two_sites_at_distinct_keys_both_land` runs them at one
    /// worker. Writer 1's first attempt is queued with writer 0's, and its drive reads the store
    /// before it opens, so it proposes nothing. Its step runs only after writer 0 has committed
    /// every item and run two attempts without progress. That attempt is not evidence of a stall:
    /// its retry reads the commits and decides.
    #[test]
    fn an_attempt_queued_before_another_writers_progress_does_not_stall() {
        let writers = 2;
        let mut stalls = Stalls::default();
        let writer_1 = stalls.mark();
        // Writer 0 opens the store and commits its five items.
        for _ in 0..6 {
            let mark = stalls.mark();
            assert_eq!(stalls.complete(mark, true), 0);
        }
        // Its last request attempt and its finish's attempt change nothing.
        for expected in 1..=2 {
            let mark = stalls.mark();
            assert_eq!(stalls.complete(mark, false), expected);
        }
        assert!(
            stalls.complete(writer_1, false) <= writers,
            "writer 1's first attempt ended its request as stalled"
        );
        // Its retry is queued since the last progress, and counts.
        let mark = stalls.mark();
        assert_eq!(stalls.complete(mark, false), 3);
    }

    /// Attempts queued since the last progress count across writers, and progress starts the
    /// count again.
    #[test]
    fn attempts_queued_since_the_last_progress_count_until_one_progresses() {
        let mut stalls = Stalls::default();
        let mark = stalls.mark();
        assert_eq!(stalls.complete(mark, false), 1);
        assert_eq!(stalls.complete(mark, false), 2);
        assert_eq!(stalls.complete(mark, true), 0);
        let mark = stalls.mark();
        assert_eq!(stalls.complete(mark, false), 1);
        stalls.reset();
        assert_eq!(stalls.complete(mark, false), 1);
    }
}
