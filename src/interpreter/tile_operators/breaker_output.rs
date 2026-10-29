//! The operator that serves a breaker's output to the pipeline behind it.

use super::*;
use crate::interpreter::Materialized;

/// A breaker's [`Materialized`] output as an operator with no inputs: the leaf of the pipeline
/// behind the breaker. Its producers read the rows the breaker's workers absorbed, and its source
/// hands the keys that were published to the workers of the pipeline behind as morsels.
///
/// The consumer graph of the pipeline behind ends here: the operators of the pipeline before the
/// breaker are not inputs of this one, so no notification of theirs crosses it. The breaker
/// raises its own region through [`Materialized::publish`] once it holds a morsel's rows.
/// See `src/interpreter/design-parallel.md`, "A breaker's output".
///
/// One operator reads the output as one reader: the workers of a pool subscribe it once each, and
/// the rows leave the output once every reading operator has released them.
pub(crate) struct BreakerOutput {
    base: OperatorBase,
    materialized: Arc<Materialized>,
    /// Whether the reader reads every row whole: the build side of a join. Its producers answer
    /// the universal read and ignore a release that names part of it. No plan builds one yet: a
    /// build side is admitted by a later change, and the support is here for it.
    whole: bool,
    correlation: Option<Vec<TilePathStep>>,
    source: Arc<LiveSource>,
    /// Whether a subscription has registered this operator's consumer with the output.
    registered: bool,
}

impl BreakerOutput {
    /// The output `materialized` holds, shaped `tiling`, read as a stream, or as a build side
    /// when `whole`. `correlation` is the breaker's own `result_correlation`.
    pub(crate) fn new(
        materialized: Arc<Materialized>,
        tiling: Tiling,
        whole: bool,
        correlation: Option<Vec<TilePathStep>>,
    ) -> Self {
        let source = materialized.source();
        Self {
            base: OperatorBase::new(tiling),
            materialized,
            whole,
            correlation,
            source,
            registered: false,
        }
    }
}

impl TileOperator for BreakerOutput {
    impl_operator_base!();

    fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
    fn visit_inputs_mut(&mut self, _visit: &mut dyn FnMut(&mut Box<dyn TileOperator>)) {}

    fn morsel_source(&self) -> Option<Arc<dyn MorselSource>> {
        Some(self.source.clone())
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // The workers of one operator share a record, so the rows leave once every operator has
        // released them and not once the first worker has. Their releases are disjoint morsels.
        // A build side is read whole by every worker, so each worker is a reader of its own and
        // the rows leave once every worker has released them all.
        let reader = self.materialized.register_reader(match self.whole {
            true => None,
            false => scheduler.pooled_release_record_for(self.operator_id()),
        });
        // One consumer per operator reaches the output, the first subscription's: a pool passes
        // the pipeline's consumer to its first worker, and the output notifies it once, from
        // the thread that absorbed the morsel, whichever thread that is.
        if !self.registered {
            self.registered = true;
            self.materialized.add_downstream(consumer);
        }
        Box::new(BreakerOutputProducer {
            base: ProducerBase::new(
                BreakerOutputProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            materialized: self.materialized.clone(),
            reader,
            whole: self.whole,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        self.correlation.clone()
    }
}

/// What a pool leaves where it took a chain out of the graph: an operator with the chain's tiling
/// and no inputs, which nothing subscribes.
pub(crate) struct Detached {
    tiling: Tiling,
}

impl Detached {
    pub(crate) fn new(tiling: Tiling) -> Self {
        Self { tiling }
    }
}

impl TileOperator for Detached {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}

    fn visit_inputs_mut(&mut self, _visit: &mut dyn FnMut(&mut Box<dyn TileOperator>)) {}

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        _consumer: Box<dyn Consumer>,
        _scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        panic!("a chain a pool took out of the graph is not subscribed")
    }
}

/// Producer for [`BreakerOutput`]: answers a read from the rows the breaker holds.
struct BreakerOutputProducer {
    base: ProducerBase,
    materialized: Arc<Materialized>,
    /// This producer's operator's record in the breaker's [`Materialized`].
    reader: usize,
    whole: bool,
}

impl TileProducer for BreakerOutputProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node
    }

    /// The rows of the projection that are in the output and were not released to this
    /// producer. A build side answers the universal read whatever it is asked.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let guard = match self.whole {
            true => self.tiling().universal_guard(),
            false => projection_guard,
        };
        let mut tile = self.materialized.snapshot(&guard);
        tile.remove_guarded(self.obsolete_guard().clone());
        tile.compact();
        tile
    }

    /// Hand the release to the breaker's record for this producer's operator. A build side is
    /// released whole or not at all: its rows are read by every row of the pipeline behind.
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if self.whole && !obsolete_guard.is_universal() {
            return;
        }
        self.materialized.release(self.reader, &obsolete_guard);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{RegionLog, int_entries, keys_between};
    use crate::interpreter::{BaseType, ColumnValue, Extent, Predicate, Value};
    use bit_set::BitSet;

    fn ints() -> Tiling {
        Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        )
    }

    /// The keys `first..=last` as a predicate.
    fn region(first: u64, last: u64) -> Predicate {
        match Projection::of(&keys_between(first, last)).expect("keys") {
            Projection::Keys(keys) => keys,
            other => panic!("a region of keys, got {other:?}"),
        }
    }

    /// The rows at `keys`, each holding ten times its key, stating `stated` complete, as a
    /// worker's chain answers a morsel.
    fn rows_at(keys: &[u64], stated: Predicate) -> Tile {
        Tile::data_function(
            ColumnValue::from_uints(keys.to_vec()),
            Box::new(Tile::Scalar(ColumnValue::Ints(
                keys.iter().map(|&k| 10 * k as i64).collect(),
            ))),
            stated,
            BitSet::new(),
        )
    }

    /// Absorb the rows at `keys` as the morsel `first..=last`, which states its region
    /// complete, and publish its region.
    fn absorb(materialized: &Materialized, first: u64, last: u64, keys: &[u64]) {
        materialized.absorb(
            rows_at(keys, region(first, last)),
            &keys_between(first, last),
        );
        materialized.publish(&Projection::of(&keys_between(first, last)).unwrap());
    }

    fn output(materialized: &Arc<Materialized>) -> BreakerOutput {
        BreakerOutput::new(materialized.clone(), ints(), false, None)
    }

    /// A producer of `output` subscribed outside a pool: its operator's record is its own.
    fn subscribe(output: &mut BreakerOutput) -> Box<dyn TileProducer> {
        output.subscribe(
            output.tiling().universal_guard(),
            Box::new(|| {}),
            &mut Scheduler::new(),
        )
    }

    /// `workers` producers of `output`, subscribed as a pool subscribes the workers' chains, so
    /// that they share their operator's record.
    fn subscribe_pooled(output: &mut BreakerOutput, workers: usize) -> Vec<Box<dyn TileProducer>> {
        let tiling = output.tiling().clone();
        let (producers, _records) =
            Scheduler::new().with_pooled_release_records("pool#test".to_string(), |scheduler| {
                (0..workers)
                    .map(|_| output.subscribe(tiling.universal_guard(), Box::new(|| {}), scheduler))
                    .collect()
            });
        producers
    }

    /// A read at a guard sees the rows of that guard only, and states complete the keys that
    /// are ready.
    #[test]
    fn a_read_sees_the_rows_of_its_guard() {
        let materialized = Materialized::new(ints());
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        absorb(&materialized, 4, 7, &[4, 5, 6, 7]);
        let mut producer = subscribe(&mut output(&materialized));

        let low = producer.get(keys_between(0, 3));
        assert_eq!(int_entries(&low), vec![(0, 0), (1, 10), (2, 20), (3, 30)]);
        let Tile::DataFunction {
            domain_predicate, ..
        } = &low
        else {
            panic!("a collection, got {low:?}");
        };
        assert!(domain_predicate.contains(&Value::UInt(3)));
        assert!(!domain_predicate.contains(&Value::UInt(4)));

        // Keys that have not arrived are not stated complete.
        let wide = producer.get(keys_between(0, 9));
        let Tile::DataFunction {
            domain_predicate, ..
        } = &wide
        else {
            panic!("a collection, got {wide:?}");
        };
        assert!(domain_predicate.contains(&Value::UInt(7)));
        assert!(
            !domain_predicate.contains(&Value::UInt(8)),
            "{domain_predicate:?}"
        );
    }

    /// Absorbing a morsel and publishing its region notifies each consumer behind the breaker of
    /// the region, and a consumer that registers later hears of what is there.
    #[test]
    fn a_published_region_reaches_every_consumer_behind() {
        let materialized = Materialized::new(ints());
        let (early, early_regions) = RegionLog::new(true);
        let (late, late_regions) = RegionLog::new(true);
        materialized.add_downstream(Box::new(early));
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        materialized.add_downstream(Box::new(late));
        absorb(&materialized, 4, 7, &[4, 5, 6, 7]);
        let named = |a, b| Projection::of(&keys_between(a, b)).unwrap();
        assert_eq!(*early_regions.lock_wait(), [named(0, 3), named(4, 7)]);
        assert_eq!(
            *late_regions.lock_wait(),
            [named(0, 3), named(4, 7)],
            "the first is the region ready when it registered"
        );
    }

    /// A region published while a consumer registers reaches it: the consumer list is held from
    /// reading `ready` to pushing the consumer, so a publish that ran before the push is inside
    /// the `ready` the registration read, and one that runs after reaches the consumer.
    ///
    /// The consumer's first notification, which the registration makes, lets another thread
    /// absorb and publish `4..=7` and waits for it to finish publishing, up to a tenth of a
    /// second: a publish that cannot take the list yet waits for the registration to finish.
    #[test]
    fn a_region_published_while_a_consumer_registers_reaches_it() {
        struct Races {
            materialized: Arc<Materialized>,
            raced: Option<std::thread::JoinHandle<()>>,
            heard: Arc<Mutex<Vec<Projection>>>,
        }
        impl Consumer for Races {
            fn notify(&mut self, arrived: &Projection) {
                self.heard.lock_wait().push(arrived.clone());
                if self.raced.is_some() {
                    return;
                }
                let materialized = self.materialized.clone();
                let published = Arc::new(AtomicBool::new(false));
                let done = published.clone();
                self.raced = Some(std::thread::spawn(move || {
                    absorb(&materialized, 4, 7, &[4, 5, 6, 7]);
                    done.store(true, Ordering::Release);
                }));
                let deadline = std::time::Instant::now() + std::time::Duration::from_millis(100);
                while !published.load(Ordering::Acquire) && std::time::Instant::now() < deadline {
                    std::thread::yield_now();
                }
            }
        }
        let materialized = Materialized::new(ints());
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        let heard = Arc::new(Mutex::new(Vec::new()));
        let consumer = Races {
            materialized: materialized.clone(),
            raced: None,
            heard: heard.clone(),
        };
        materialized.add_downstream(Box::new(consumer));
        // The thread has absorbed by now or waits on the list; either way it finishes.
        wait_for_ready(&materialized, 7);
        let heard_keys = |regions: &[Projection]| {
            let all = regions
                .iter()
                .fold(Projection::Nothing, |all, r| all.union(r));
            all.contained_in(&Projection::admitting(region(0, 7)))
                && Projection::admitting(region(0, 7)).contained_in(&all)
        };
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
        while !heard_keys(&heard.lock_wait()) {
            assert!(
                std::time::Instant::now() < deadline,
                "the consumer heard of 4..=7: {:?}",
                heard.lock_wait()
            );
            std::thread::yield_now();
        }
    }

    fn wait_for_ready(materialized: &Materialized, key: u64) {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
        while !materialized.ready().contains(&Value::UInt(key)) {
            assert!(
                std::time::Instant::now() < deadline,
                "the rows were absorbed"
            );
            std::thread::yield_now();
        }
    }

    /// A region is published after its rows are absorbed.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "a region is published after its rows were absorbed")]
    fn a_region_published_before_its_rows_is_rejected() {
        let materialized = Materialized::new(ints());
        materialized.publish(&Projection::of(&keys_between(0, 3)).unwrap());
    }

    /// Two operators read the output; the rows leave when both have released them, and the
    /// workers of one operator, which subscribe the same operator, share its record.
    #[test]
    fn rows_leave_once_every_reading_operator_released_them() {
        let materialized = Materialized::new(ints());
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        absorb(&materialized, 4, 7, &[4, 5, 6, 7]);
        let (mut a, mut b) = (output(&materialized), output(&materialized));
        let [mut a1, mut a2] = <[_; 2]>::try_from(subscribe_pooled(&mut a, 2))
            .ok()
            .unwrap();
        let [mut b1] = <[_; 1]>::try_from(subscribe_pooled(&mut b, 1))
            .ok()
            .unwrap();

        // Worker 1 of `a` and worker 2 of `a` release disjoint morsels into one record.
        a1.get(keys_between(0, 3));
        a1.release(keys_between(0, 3));
        a2.get(keys_between(4, 7));
        a2.release(keys_between(4, 7));
        let kept = b1.get(keys_between(0, 7));
        assert_eq!(int_entries(&kept).len(), 8, "`b` has not released anything");

        b1.release(keys_between(0, 3));
        let kept = materialized.snapshot(&keys_between(0, 7));
        assert_eq!(int_entries(&kept), vec![(4, 40), (5, 50), (6, 60), (7, 70)]);
        b1.release(keys_between(4, 7));
        assert!(int_entries(&materialized.snapshot(&keys_between(0, 7))).is_empty());
    }

    /// One operator with several workers is one reader: the first worker's release removes the
    /// rows, because no other operator reads them.
    #[test]
    fn the_workers_of_one_operator_are_one_reader() {
        let materialized = Materialized::new(ints());
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        let mut only = output(&materialized);
        let [mut first, _second] = <[_; 2]>::try_from(subscribe_pooled(&mut only, 2))
            .ok()
            .unwrap();
        first.get(keys_between(0, 3));
        first.release(keys_between(0, 3));
        assert!(int_entries(&materialized.snapshot(&keys_between(0, 3))).is_empty());
    }

    /// Only the first subscription of an operator registers its consumer with the output, so a
    /// publish notifies one consumer per reading operator and not one per worker.
    #[test]
    fn a_publish_notifies_one_consumer_per_reading_operator() {
        let materialized = Materialized::new(ints());
        let mut only = output(&materialized);
        let (log, regions) = RegionLog::new(true);
        let (quiet, quiet_regions) = RegionLog::new(true);
        let tiling = only.tiling().clone();
        let mut scheduler = Scheduler::new();
        let _first = only.subscribe(tiling.universal_guard(), Box::new(log), &mut scheduler);
        let _second = only.subscribe(tiling.universal_guard(), Box::new(quiet), &mut scheduler);
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        assert_eq!(regions.lock_wait().len(), 1);
        assert!(quiet_regions.lock_wait().is_empty());
    }

    /// A build side is read whole by every worker, so each worker is a reader of its own: the
    /// first worker's release of everything does not reclaim rows the second still probes.
    #[test]
    fn a_build_side_is_reclaimed_only_when_every_worker_released_it() {
        let materialized = Materialized::new(ints());
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        let mut build = BreakerOutput::new(materialized.clone(), ints(), true, None);
        let [mut first, mut second] = <[_; 2]>::try_from(subscribe_pooled(&mut build, 2))
            .ok()
            .unwrap();
        let universal = first.tiling().universal_guard();
        first.get(universal.clone());
        first.release(universal.clone());
        let seen = second.get(universal.clone());
        assert_eq!(
            int_entries(&seen).len(),
            4,
            "the second worker still reads it"
        );
        second.release(universal);
        assert!(int_entries(&materialized.snapshot(&keys_between(0, 3))).is_empty());
    }

    /// A reader releases only rows that are ready.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "a reader releases only rows that are ready")]
    fn a_release_of_rows_that_were_not_absorbed_is_rejected() {
        let materialized = Materialized::new(ints());
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        let mut producer = subscribe(&mut output(&materialized));
        producer.release(keys_between(4, 5));
    }

    /// A morsel's keys are disjoint from the keys ready.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "a morsel's keys are disjoint from the keys ready")]
    fn a_morsel_absorbed_twice_is_rejected() {
        let materialized = Materialized::new(ints());
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        materialized.absorb(rows_at(&[2], region(2, 3)), &keys_between(2, 3));
    }

    /// A morsel states its whole region complete: keys the region names that the morsel does not
    /// hold are decided absent, which only a statement over them says.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "a morsel states its whole region complete")]
    fn a_morsel_that_does_not_state_its_region_complete_is_rejected() {
        let materialized = Materialized::new(ints());
        materialized.absorb(rows_at(&[0, 1], region(0, 1)), &keys_between(0, 3));
    }

    /// A breaker completes once, and absorbs nothing after.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "no morsel is absorbed after the breaker completed")]
    fn a_morsel_absorbed_after_completion_is_rejected() {
        let materialized = Materialized::new(ints());
        materialized.complete();
        materialized.absorb(rows_at(&[0], region(0, 0)), &keys_between(0, 0));
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "a breaker completes once")]
    fn a_breaker_completed_twice_is_rejected() {
        let materialized = Materialized::new(ints());
        materialized.complete();
        materialized.complete();
    }

    /// Every reader registers before a row leaves: a reader registered after a release would
    /// find reclaimed keys stated complete and absent.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "every reader registers before a row leaves")]
    fn a_reader_registered_after_a_row_left_is_rejected() {
        let materialized = Materialized::new(ints());
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        let mut producer = subscribe(&mut output(&materialized));
        producer.release(keys_between(0, 3));
        subscribe(&mut output(&materialized));
    }

    /// Completion states every key complete, and notifies each consumer of everything.
    #[test]
    fn completion_states_the_collection_whole() {
        let materialized = Materialized::new(ints());
        let (log, regions) = RegionLog::new(true);
        materialized.add_downstream(Box::new(log));
        absorb(&materialized, 0, 1, &[0, 1]);
        assert!(!materialized.is_complete());
        materialized.complete();
        assert!(materialized.is_complete());
        let tile = materialized.snapshot(&keys_between(0, 9));
        let Tile::DataFunction {
            domain_predicate, ..
        } = &tile
        else {
            panic!("a collection, got {tile:?}");
        };
        assert!(
            domain_predicate.contains(&Value::UInt(9)),
            "{domain_predicate:?}"
        );
        assert_eq!(regions.lock_wait().last(), Some(&Projection::Everything));
        assert_eq!(materialized.tiling(), &ints());
    }

    /// A release of everything before the breaker completed does not reclaim the rows absorbed
    /// after it: they are held until another reader's release finds every reader done with them.
    #[test]
    fn rows_absorbed_after_a_release_of_everything_are_held_until_the_next_release() {
        let materialized = Materialized::new(ints());
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        let (mut a, mut b) = (output(&materialized), output(&materialized));
        let (mut done, mut reading) = (subscribe(&mut a), subscribe(&mut b));
        done.release(done.tiling().universal_guard());
        reading.release(keys_between(0, 3));
        assert!(int_entries(&materialized.snapshot(&keys_between(0, 3))).is_empty());

        absorb(&materialized, 4, 7, &[4, 5, 6, 7]);
        assert_eq!(
            int_entries(&materialized.snapshot(&keys_between(4, 7))).len(),
            4,
            "held: the reader that is still reading has not released them"
        );
        reading.release(keys_between(4, 7));
        assert!(int_entries(&materialized.snapshot(&keys_between(4, 7))).is_empty());
    }

    /// The record of a reader that released everything does not reclaim keys that were not
    /// ready: a later release names the rows absorbed since, and they leave then.
    #[test]
    fn a_release_of_everything_reclaims_only_the_keys_that_were_ready() {
        let materialized = Materialized::new(ints());
        let reader = materialized.register_reader(None);
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        materialized.release(reader, &ints().universal_guard());
        absorb(&materialized, 4, 7, &[4, 5, 6, 7]);
        assert_eq!(
            int_entries(&materialized.snapshot(&keys_between(4, 7))).len(),
            4
        );
        materialized.release(reader, &keys_between(4, 7));
        assert!(int_entries(&materialized.snapshot(&keys_between(4, 7))).is_empty());
    }

    /// A producer dropped without releasing does not pin the rows past the end of the run.
    #[test]
    fn retiring_the_readers_drops_the_rows_a_dropped_producer_never_released() {
        let materialized = Materialized::new(ints());
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        let mut quiet = output(&materialized);
        let mut busy = output(&materialized);
        let (mut released, forgotten) = (subscribe(&mut busy), subscribe(&mut quiet));
        released.release(keys_between(0, 3));
        drop(forgotten);
        assert_eq!(
            int_entries(&materialized.snapshot(&keys_between(0, 3))).len(),
            4
        );
        materialized.retire_readers();
        assert!(int_entries(&materialized.snapshot(&keys_between(0, 3))).is_empty());
    }

    /// The output knows the sources it handed out, and only those.
    #[test]
    fn an_output_feeds_the_sources_it_handed_out() {
        let materialized = Materialized::new(ints());
        let (mine, other) = (output(&materialized), output(&Materialized::new(ints())));
        assert!(materialized.feeds(&mine.morsel_source().unwrap()));
        assert!(!materialized.feeds(&other.morsel_source().unwrap()));
    }

    /// The source over the output claims published keys that have rows: a key the pipeline
    /// before the breaker filtered out is in the region and not in the rows, and no morsel
    /// names it.
    #[test]
    fn the_source_claims_published_keys_that_have_rows() {
        let materialized = Materialized::new(ints());
        let output = output(&materialized);
        let source = output.morsel_source().expect("an output is a source");
        absorb(&materialized, 0, 3, &[0, 2]);
        source.publish(&Projection::of(&keys_between(0, 3)).unwrap());
        let morsel = match source.claim(4) {
            Claim::Morsel(guard) => guard,
            _ => panic!("a published region with rows is claimable"),
        };
        let Some(Projection::Keys(keys)) = Projection::of(&morsel).ok() else {
            panic!("a morsel names keys");
        };
        assert!(keys.contains(&Value::UInt(0)) && keys.contains(&Value::UInt(2)));
        // Key 3 names no row: the region it is in is claimed and nothing is left.
        assert!(matches!(source.claim(4), Claim::Idle));
        source.close();
        assert!(matches!(source.claim(4), Claim::Exhausted));
    }

    /// A region published to the source before its rows are ready is refused: the rows are
    /// visible before the region, and the region before the epoch moves.
    #[test]
    #[should_panic(expected = "are ready before their region is published")]
    fn the_source_refuses_a_region_whose_rows_are_not_ready() {
        let materialized = Materialized::new(ints());
        let output = output(&materialized);
        let source = output.morsel_source().expect("an output is a source");
        source.publish(&Projection::of(&keys_between(0, 3)).unwrap());
    }

    /// A build side answers the universal read whatever it is pulled at, and a release of part
    /// of it removes nothing.
    #[test]
    fn a_build_side_is_read_and_released_whole() {
        let materialized = Materialized::new(ints());
        absorb(&materialized, 0, 3, &[0, 1, 2, 3]);
        let mut build = BreakerOutput::new(materialized.clone(), ints(), true, None);
        let mut producer = subscribe(&mut build);
        let all = producer.get(producer.tiling().universal_guard());
        assert_eq!(int_entries(&all).len(), 4);
        producer.release(keys_between(0, 1));
        assert_eq!(
            int_entries(&materialized.snapshot(&keys_between(0, 3))).len(),
            4,
            "a part of a build side is not released"
        );
        producer.release(producer.tiling().universal_guard());
        assert!(int_entries(&materialized.snapshot(&keys_between(0, 3))).is_empty());
    }

    /// The keys of a collection need only be ordered: strings and sparse integers go through the
    /// output, and the source claims them in key order, which `first_keys` sorts.
    #[test]
    fn keys_that_are_strings_or_sparse_integers_are_claimed_in_key_order() {
        let strings = Tiling::data_function(
            Extent::Base(BaseType::String),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let ints_keyed = Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let cases: Vec<(Tiling, ColumnValue, Value, Value, Vec<Value>)> = vec![
            (
                strings,
                ColumnValue::Strings(vec!["c".into(), "a".into(), "b".into()]),
                Value::String("a".into()),
                Value::String("c".into()),
                vec![
                    Value::String("a".into()),
                    Value::String("b".into()),
                    Value::String("c".into()),
                ],
            ),
            (
                ints_keyed,
                ColumnValue::Ints(vec![100, -5, 7]),
                Value::Int(-5),
                Value::Int(100),
                vec![Value::Int(-5), Value::Int(7), Value::Int(100)],
            ),
        ];
        for (tiling, keys, low, high, ordered) in cases {
            let materialized = Materialized::new(tiling.clone());
            let guard = TileGuard::Function(FunctionGuard::Domain(Predicate::intervals(
                intervalsets::IntervalSet::from(intervalsets::Interval::closed(low, high)),
            )));
            let region = Projection::of(&guard).unwrap();
            let stated = match &region {
                Projection::Keys(keys) => keys.clone(),
                other => panic!("keys, got {other:?}"),
            };
            let rows = keys.len();
            materialized.absorb(
                Tile::data_function(
                    keys,
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![0; rows]))),
                    stated.clone(),
                    BitSet::new(),
                ),
                &guard,
            );
            materialized.publish(&region);
            assert_eq!(materialized.first_keys_for_test(&stated, 10), ordered);
            let source = BreakerOutput::new(materialized.clone(), tiling, false, None)
                .morsel_source()
                .expect("a source");
            source.publish(&region);
            let Claim::Morsel(morsel) = source.claim(10) else {
                panic!("the published keys are claimable");
            };
            assert_eq!(Projection::of(&morsel).unwrap(), region);
        }
    }
}
