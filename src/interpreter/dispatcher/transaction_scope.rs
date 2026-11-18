//! Transaction requests and attempts on the run's shared dispatcher.
//!
//! As for loop rounds, request and step handlers control the recurrence boundary. The
//! driver, body breakers and proposal writer are ordinary pipelines between those handlers.

use std::sync::PoisonError;

use super::loop_scope::{Member, reach_member};
use super::plan::Planned;
use super::*;
use crate::interpreter::commit_operator::CommitProducer;
use crate::interpreter::tile_operators::StoreCell;

pub(crate) struct TransactionRun {
    pub(super) writers: Vec<WriterRun>,
}

pub(super) struct WriterRun {
    pub(super) graph: Option<Dispatcher>,
    pub(super) members: Vec<Member>,
    pub(super) placements: Vec<Vec<Placement>>,
    pub(super) driver: PipelineId,
    pub(super) planned: Vec<Planned>,
    pub(super) shared: Option<SharedTransaction>,
    request: Option<WorkPackage>,
    finishing: Option<Option<TileGuard>>,
    closing: bool,
}

pub(super) struct SharedTransaction {
    pub(super) request: PipelineId,
    pub(super) input: InputId,
    pub(super) base: usize,
    pub(super) step: PipelineId,
    active: bool,
    followers_released: bool,
}

impl SharedTransaction {
    pub(super) fn new(request: PipelineId, input: InputId, base: usize, step: PipelineId) -> Self {
        Self {
            request,
            input,
            base,
            step,
            active: false,
            followers_released: false,
        }
    }
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
            members,
            placements,
            driver,
            planned,
            shared: None,
            request: None,
            finishing: None,
            closing: false,
        }
    }
    fn pipeline(&self, local: PipelineId) -> PipelineId {
        PipelineId(
            self.shared
                .as_ref()
                .expect("a transaction body is attached")
                .base
                + local.0,
        )
    }
    pub(super) fn has_request(&self) -> bool {
        self.request.is_some()
    }
    pub(super) fn pipelines(&self) -> Vec<PipelineId> {
        let Some(shared) = &self.shared else {
            return Vec::new();
        };
        (0..self.members.len())
            .map(|local| PipelineId(shared.base + local))
            .collect()
    }
    fn hold_followers(&mut self, dispatcher: &Dispatcher) {
        if let Some(shared) = &mut self.shared {
            if !shared.active || (self.request.is_none() && self.finishing.is_none()) {
                return;
            }
            dispatcher.hold_followers(
                (shared.base..shared.base + self.members.len())
                    .map(PipelineId)
                    .chain(std::iter::once(shared.step)),
                true,
            );
            shared.followers_released = false;
        }
    }
    pub(super) fn release_followers(&mut self, dispatcher: &Dispatcher) -> bool {
        let Some(shared) = &mut self.shared else {
            return false;
        };
        if !shared.active
            || shared.followers_released
            || (self.request.is_none() && self.finishing.is_none())
        {
            return false;
        }
        dispatcher.hold_followers(
            (shared.base..shared.base + self.members.len())
                .map(PipelineId)
                .chain(std::iter::once(shared.step)),
            false,
        );
        shared.followers_released = true;
        true
    }
    fn activate(&mut self, dispatcher: &Dispatcher) {
        let shared = self
            .shared
            .as_mut()
            .expect("a transaction body is attached");
        if shared.active {
            return;
        }
        shared.active = true;
        for (local, placements) in self.placements.iter().enumerate() {
            let pipeline = PipelineId(shared.base + local);
            for placement in placements {
                placement.set((!dispatcher.is_source(pipeline)).then_some(pipeline));
            }
            dispatcher.hold_pipeline(pipeline, false);
        }
        dispatcher.hold_pipeline(shared.step, false);
    }
    fn queue(&mut self, dispatcher: &Dispatcher, guard: &TileGuard) {
        self.activate(dispatcher);
        self.hold_followers(dispatcher);
        dispatcher.queue_round(self.pipeline(self.driver), guard);
        dispatcher.queue_round(
            self.shared.as_ref().expect("an attached writer").step,
            guard,
        );
    }
    fn close(&mut self, dispatcher: &Dispatcher) {
        self.closing = true;
        for pipeline in self.pipelines() {
            if dispatcher.is_source(pipeline) {
                dispatcher.close(pipeline);
            }
        }
        dispatcher.close(self.shared.as_ref().expect("an attached writer").step);
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
                    *target.write().unwrap_or_else(PoisonError::into_inner) = None;
                }
            });
        }
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
    pub(super) fn begin_request(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
        package: WorkPackage,
    ) {
        let input = self
            .writer_run(writer)
            .shared
            .as_ref()
            .expect("an attached writer")
            .input;
        assert!(
            self.writer_run(writer).request.is_none(),
            "a writer completes its request before another starts"
        );
        self.begin_delivery(input);
        self.begin_attempt();
        let guard = package.guard.clone();
        self.writer_run_mut(writer).request = Some(package);
        self.writer_run_mut(writer).queue(dispatcher, &guard);
    }
    pub(super) fn finish_request(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
    ) -> Option<WorkPackage> {
        self.complete_attempt(writer);
        let run = self.writer_run_mut(writer);
        if run.finishing.is_some() {
            run.close(dispatcher);
            return None;
        }
        let shared = run.shared.as_ref().expect("an attached writer");
        let input = shared.input;
        let package = run
            .request
            .as_ref()
            .expect("a transaction attempt has a request");
        let guard = package.guard.clone();
        if self.request_complete(input, &guard) {
            return self.writer_run_mut(writer).request.take();
        }
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
            !self.writer_run(writer).has_request(),
            "a writer finishes after its requests settle"
        );
        let input = self
            .writer_run(writer)
            .shared
            .as_ref()
            .expect("an attached writer")
            .input;
        let whole = self.input_tiling(input).universal_guard();
        self.begin_attempt();
        self.writer_run_mut(writer).finishing = Some(consumed);
        self.writer_run_mut(writer).queue(dispatcher, &whole);
    }
    pub(super) fn take_transaction_finish(
        &mut self,
        dispatcher: &Dispatcher,
        writer: usize,
    ) -> Option<(PipelineId, Option<TileGuard>)> {
        let run = self.writer_run_mut(writer);
        let shared = run.shared.as_ref()?;
        if !run.closing
            || !run
                .pipelines()
                .into_iter()
                .chain(std::iter::once(shared.step))
                .all(|pipeline| dispatcher.states[pipeline.0].phase.load() == Phase::Finished)
        {
            return None;
        }
        let consumed = run.finishing.take()?;
        Some((shared.request, consumed))
    }
    pub(super) fn hold_transaction_followers(&mut self, dispatcher: &Dispatcher) {
        if let Some(run) = &mut self.run {
            for writer in &mut run.writers {
                writer.hold_followers(dispatcher);
            }
        }
    }
}
