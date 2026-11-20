//! The execution of a partitioned pipeline's claims: several threads consume one pipeline's
//! packages at once through its shared breaker handle. See `src/interpreter/design-dispatcher.md`,
//! "A partitioned claim".
use super::*;
use crate::interpreter::CurryLevel;
#[cfg(test)]
use std::sync::atomic::{AtomicU64, AtomicUsize};

/// A partitioned pipeline's breaker and the level its claims partition.
struct Spec {
    target: BreakerHandle,
    level: CurryLevel,
    /// For a pipeline of a loop's or transaction writer's body, the body's pipelines and step,
    /// whose followers a claim holds again before it is acknowledged.
    body: Option<Vec<PipelineId>>,
}

/// What each pipeline's claims did on the pool, for the tests ([`Partitioned::report`]).
#[cfg(test)]
#[derive(Default)]
struct Stats {
    claims: AtomicUsize,
    /// One bit per worker that consumed a claim of the pipeline.
    used: AtomicU64,
    incremental: AtomicUsize,
}

/// Per pipeline, its breaker and level where several claims consume it at once.
pub(super) struct Partitioned {
    specs: Vec<Option<Spec>>,
    #[cfg(test)]
    stats: Vec<Stats>,
}

impl Partitioned {
    /// The partitioned pipelines among `targets`: those whose breaker answers a parallel level.
    /// `bodies` names, per pipeline of a scope's body, the body's pipelines and step.
    pub(super) fn new(
        targets: Vec<Option<BreakerHandle>>,
        bodies: Vec<Option<Vec<PipelineId>>>,
    ) -> Self {
        debug_assert_eq!(
            targets.len(),
            bodies.len(),
            "the targets and the bodies name the same pipelines"
        );
        let specs: Vec<_> = targets
            .into_iter()
            .zip(bodies)
            .map(|(target, body)| {
                let target = target?;
                let level = target
                    .read()
                    .unwrap_or_else(PoisonError::into_inner)
                    .parallel_level()?;
                Some(Spec {
                    target,
                    level,
                    body,
                })
            })
            .collect();
        Self {
            #[cfg(test)]
            stats: (0..specs.len()).map(|_| Stats::default()).collect(),
            specs,
        }
    }

    /// Whether several claims of `pipeline` may consume it at once.
    pub(super) fn has(&self, pipeline: PipelineId) -> bool {
        self.specs.get(pipeline.0).is_some_and(Option::is_some)
    }

    /// Consume `package` under the breaker's handle held shared, publish the pipeline under it
    /// held exclusively, land the pushes with no handle held, and acknowledge the package.
    pub(super) fn consume(
        &self,
        dispatcher: &Dispatcher,
        package: WorkPackage,
        #[cfg_attr(not(test), allow(unused_variables))] worker: usize,
    ) {
        #[cfg(test)]
        self.count_claim(dispatcher, &package, worker);
        let pipeline = package.pipeline;
        let spec = self.specs[pipeline.0]
            .as_ref()
            .expect("a package that holds no exclusion domain is of a partitioned pipeline");
        let target = &spec.target;
        {
            let breaker = target.read().unwrap_or_else(PoisonError::into_inner);
            debug_assert!(
                package
                    .guard
                    .check_from(&breaker.input_tiling(InputId::ONLY)),
                "pipeline {} consumes a guard of the tiling its breaker's input answers: {:?}",
                pipeline.0,
                package.guard
            );
            breaker.consume_impl(InputId::ONLY, package.guard.clone());
        }
        // Exclusive, so the push sees no consume between the merge of its rows and the release of
        // its input, which the readers it wakes rely on. A breaker that publishes only at its
        // finish or in the resume pass pushes nothing here, as in serial work
        // (`consume_with`).
        let pushes = {
            let breaker = target.write().unwrap_or_else(PoisonError::into_inner);
            breaker
                .as_producer()
                .filter(|producer| producer.pushes_while_consuming())
                .map(|producer| {
                    let mut pushes = dispatcher.pushes(pipeline);
                    pushes.push_final(producer);
                    pushes
                })
        };
        if let Some(pushes) = pushes {
            dispatcher.land(pushes);
        }
        // Before the acknowledgement that can leave the body quiescent: the round's step waits
        // for the coordinator to publish what this consume left held, as it does after a claim
        // of its own (`Execution::consume`).
        if let Some(body) = &spec.body {
            dispatcher.hold_followers(body.iter().copied(), true);
        }
        dispatcher.acknowledge(package);
        // An acknowledgement advances the generation only where it frees or completes a queue; a
        // coordinator asleep because this package was in flight wakes to see it acknowledged.
        dispatcher.wake_claimants();
    }

    pub(super) fn start_source(
        &self,
        dispatcher: &Dispatcher,
        p: PipelineId,
        input: &Tiling,
        released: &TileGuard,
    ) {
        if self
            .specs
            .get(p.0)
            .and_then(Option::as_ref)
            .is_some_and(|s| s.level == CurryLevel::new(1))
        {
            let Tiling::DataFunction { codomain, .. } = input else {
                unreachable!("a source admitted at level 1 reads a collection")
            };
            let guards = seed(codomain, dispatcher.morsel_rows)
                .into_iter()
                .map(|g| {
                    let TileGuard::Function(FunctionGuard::Domain(keys)) = g else {
                        unreachable!("a seed of a collection's keys is a domain guard")
                    };
                    guard_minus(
                        &Projection::keys_at(CurryLevel::new(1), keys).guard(input),
                        released,
                    )
                })
                .filter(|g| !g.is_empty())
                .collect::<Vec<_>>();
            dispatcher.append_to_source(p, &guards);
            dispatcher.close(p);
        } else {
            dispatcher.start_source(p, input, released);
        }
    }

    /// Before a partitioned pipeline finishes, release its input whole.
    pub(super) fn finishing(&self, p: PipelineId, reach: &mut Reach<'_>) {
        if self.specs.get(p.0).is_some_and(Option::is_some) {
            reach(p, &mut |breaker, _| breaker.finish_parallel_input());
        }
    }

    #[cfg(test)]
    fn count_claim(&self, dispatcher: &Dispatcher, package: &WorkPackage, worker: usize) {
        let stats = &self.stats[package.pipeline.0];
        stats.claims.fetch_add(1, Ordering::Relaxed);
        stats.used.fetch_or(1 << (worker % 64), Ordering::Relaxed);
        if dispatcher.infos[package.pipeline.0]
            .reads
            .iter()
            .any(|p| dispatcher.states[*p].phase.load() != Phase::Finished)
        {
            stats.incremental.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// Report each pipeline's claims in `planned`, a pipeline of a scope's body under the
    /// program's pipeline `owners` names for it.
    #[cfg(test)]
    pub(super) fn report(&self, planned: &mut [Planned], owners: &[usize]) {
        let mut used = vec![0u64; planned.len()];
        for (p, stats) in self.stats.iter().enumerate() {
            let planned = &mut planned[owners[p]];
            planned.worker_claims += stats.claims.load(Ordering::Relaxed);
            planned.incremental_claims += stats.incremental.load(Ordering::Relaxed);
            used[owners[p]] |= stats.used.load(Ordering::Relaxed);
        }
        for (planned, used) in planned.iter_mut().zip(used) {
            planned.workers_used = used.count_ones() as usize;
        }
    }
}
