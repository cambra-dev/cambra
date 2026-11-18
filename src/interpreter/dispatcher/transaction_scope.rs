//! Transaction requests and attempts on the run's shared dispatcher.
//!
//! As for loop rounds, request and step handlers control the recurrence boundary. The
//! driver, body breakers and proposal writer are ordinary pipelines between those handlers.

use super::loop_scope::{Member, SharedScope, reach_member};
use super::plan::Planned;
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
    /// The body graph, until it is appended to the run's shared dispatcher.
    pub(super) graph: Option<Dispatcher>,
    /// Where the body is appended, and the store's input the writer reads, once it is.
    attachment: Option<(SharedScope, InputId)>,
    pub(super) members: Vec<Member>,
    pub(super) placements: Vec<Vec<Placement>>,
    pub(super) driver: PipelineId,
    pub(super) planned: Vec<Planned>,
    attempt: Attempt,
}

/// What a writer's attempts are for.
enum Attempt {
    /// No request is open and no finish has begun.
    Idle,
    /// Attempts toward this request run until it completes.
    Request(WorkPackage),
    /// The finish's attempt runs; the region is what the writer's pipeline consumed.
    Finishing(Option<TileGuard>),
    /// The finish's attempt has run and the sources are closed; the inner pipelines and the
    /// step are finishing.
    Closing(Option<TileGuard>),
}

impl WriterRun {
    pub(super) fn new(
        graph: Dispatcher,
        members: Vec<Member>,
        placements: Vec<Vec<Placement>>,
        driver: PipelineId,
        planned: Vec<Planned>,
    ) -> Self {
        Self {
            graph: Some(graph),
            attachment: None,
            members,
            placements,
            driver,
            planned,
            attempt: Attempt::Idle,
        }
    }

    pub(super) fn attach(&mut self, shared: SharedScope, input: InputId) {
        debug_assert!(
            self.graph.is_none() && self.attachment.is_none(),
            "a writer's body graph is taken, then attached, once"
        );
        self.attachment = Some((shared, input));
    }

    /// Where the body is attached and the input it reads.
    ///
    /// # Panics
    ///
    /// Before [`attach`](Self::attach): a writer is reached only through the handlers attaching
    /// it installs.
    pub(super) fn attached(&self) -> (&SharedScope, InputId) {
        let (shared, input) = self
            .attachment
            .as_ref()
            .expect("a writer is reached once it is attached");
        (shared, *input)
    }

    pub(super) fn has_request(&self) -> bool {
        matches!(self.attempt, Attempt::Request(_))
    }

    pub(super) fn pipelines(&self) -> Vec<PipelineId> {
        self.attachment
            .iter()
            .flat_map(|(shared, _)| shared.pipelines(self.members.len()))
            .collect()
    }

    /// Whether the writer's followers wait on it: a request or a finish is open on an active
    /// body.
    fn holds_followers(&mut self) -> Option<&mut SharedScope> {
        let open = !matches!(self.attempt, Attempt::Idle);
        self.attachment
            .as_mut()
            .map(|(shared, _)| shared)
            .filter(|shared| shared.is_active() && open)
    }

    pub(super) fn hold_followers(&mut self, dispatcher: &Dispatcher) {
        let members = self.members.len();
        if let Some(shared) = self.holds_followers() {
            shared.hold_followers(dispatcher, members);
        }
    }

    pub(super) fn release_followers(&mut self, dispatcher: &Dispatcher) -> bool {
        let members = self.members.len();
        self.holds_followers()
            .is_some_and(|shared| shared.release_followers(dispatcher, members))
    }

    fn queue(&mut self, dispatcher: &Dispatcher, guard: &TileGuard) {
        let (shared, _) = self
            .attachment
            .as_mut()
            .expect("a writer is queued once it is attached");
        shared.activate(&self.placements, dispatcher);
        self.hold_followers(dispatcher);
        let (shared, _) = self.attached();
        dispatcher.queue_round(shared.global(self.driver), guard);
        dispatcher.queue_round(shared.step, guard);
    }

    fn close(&self, dispatcher: &Dispatcher) {
        for pipeline in self.pipelines() {
            if dispatcher.is_source(pipeline) {
                dispatcher.close(pipeline);
            }
        }
        dispatcher.close(self.attached().0.step);
    }
}

impl Drop for TransactionRun {
    fn drop(&mut self) {
        for writer in &self.writers {
            for placements in &writer.placements {
                for placement in placements {
                    placement.set(None);
                }
            }
            reach_member(&writer.members[writer.driver.0], &mut |breaker, _| {
                if let Some(target) = breaker
                    .as_producer()
                    .and_then(|producer| producer.completes_through())
                {
                    *target.borrow_mut() = None;
                }
            });
        }
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
    pub(super) fn begin_request(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
        package: WorkPackage,
    ) {
        let (_, input) = self.writer_run(writer).attached();
        assert!(
            matches!(self.writer_run(writer).attempt, Attempt::Idle),
            "a writer completes its request before another starts"
        );
        self.begin_delivery(input);
        self.begin_attempt();
        let guard = package.guard.clone();
        let run = self.writer_run_mut(writer);
        run.attempt = Attempt::Request(package);
        run.queue(dispatcher, &guard);
    }
    pub(super) fn finish_request(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
    ) -> Option<WorkPackage> {
        let progressed = self.complete_attempt(writer);
        let transaction = self.run.as_mut().expect("a transaction run is planned");
        transaction.stalled = match progressed {
            true => 0,
            false => transaction.stalled + 1,
        };
        let (stalled, writers) = (transaction.stalled, transaction.writers.len());
        let run = self.writer_run_mut(writer);
        let guard = match std::mem::replace(&mut run.attempt, Attempt::Idle) {
            Attempt::Finishing(consumed) => {
                run.attempt = Attempt::Closing(consumed);
                run.close(dispatcher);
                return None;
            }
            Attempt::Request(package) => {
                let guard = package.guard.clone();
                run.attempt = Attempt::Request(package);
                guard
            }
            Attempt::Idle | Attempt::Closing(_) => {
                unreachable!("a writer's step completes an attempt it queued")
            }
        };
        let (_, input) = run.attached();
        if self.request_complete(input, &guard) {
            let run = self.writer_run_mut(writer);
            let Attempt::Request(package) = std::mem::replace(&mut run.attempt, Attempt::Idle)
            else {
                unreachable!("matched a request above")
            };
            return Some(package);
        }
        // An attempt reads the store, its inputs and the decisions to attempt again. Once every
        // writer has attempted with none of those changed, no further attempt differs.
        assert!(
            stalled <= writers,
            "a transaction request is attempted again only while an attempt changes the store, \
             an input's release or the decisions to retry: writer {writer} is queued {guard:?} \
             after {stalled} attempts that changed none of them"
        );
        self.begin_attempt();
        self.writer_run_mut(writer).queue(dispatcher, &guard);
        None
    }
    pub(super) fn begin_transaction_finish(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
        consumed: Option<TileGuard>,
    ) {
        assert!(
            matches!(self.writer_run(writer).attempt, Attempt::Idle),
            "a writer finishes after its requests settle"
        );
        let (_, input) = self.writer_run(writer).attached();
        let whole = self.input_tiling(input).universal_guard();
        self.begin_attempt();
        let run = self.writer_run_mut(writer);
        run.attempt = Attempt::Finishing(consumed);
        run.queue(dispatcher, &whole);
    }
    pub(super) fn take_transaction_finish(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
    ) -> Option<(PipelineId, Option<TileGuard>)> {
        let run = self.writer_run_mut(writer);
        let (shared, _) = run.attachment.as_ref()?;
        if !matches!(run.attempt, Attempt::Closing(_))
            || !shared.finished(dispatcher, run.members.len())
        {
            return None;
        }
        let request = shared.pipeline;
        let Attempt::Closing(consumed) = std::mem::replace(&mut run.attempt, Attempt::Idle) else {
            unreachable!("matched a closing attempt above")
        };
        Some((request, consumed))
    }
}
