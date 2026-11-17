use super::*;
use crate::interpreter::operator_graph::value;
use crate::interpreter::{
    ColumnValue, Consumer, Extent, Projection, Scheduler, Value, tuple_field,
};

/// Re-keys a collection of pairs by each pair's first component, `𝐾 ⤇ (𝐽, 𝑉)` to `𝐽 ⤇ 𝑉`, where
/// those keys are distinct: the `map` constructor's re-keying (group by the new key, then take the
/// group's one element) for input whose every new key appears once.
///
/// Its one use is a commit store's reply tap (`src/ccl/design/mutability.md`, "Replies ride
/// their transaction"): the tap's `StoreValueStream`, `Txn ⤇ (𝐼, 𝑉)`, holds the item position the
/// writer committed each value with, and a site commits its items once each. No CCL term names
/// it: op-conversion builds it for the read.
///
/// Where the keys rise with the input's own key order ([`KeyOrder::Rising`]), as a site's do
/// when it commits its items in its source's order, the rising keys are what the operator is
/// for. Once the input is complete through a position, no later position carries a key at or
/// below the one there, so the output is complete through that key: an entry is final as soon
/// as the input is complete through it, where a group-by of the pairs could close no group before
/// the whole input completes. Where they need not ([`KeyOrder::Any`]), the output states complete
/// the keys of the rows the input states complete, and the rest once the input completes.
///
/// A scheduled consume retains the output and releases the continuous consumed input prefix.
/// Position-to-key mappings above an input gap remain until consumption closes that gap.
/// Downstream release removes retained output without delaying release of consumed input.
///
/// A reader that reads the input directly releases its positions when the corresponding output
/// keys are released. It forwards the longest input prefix whose rows all have released keys;
/// rows above a gap stay with the input and are removed from the reader's output.
pub struct RekeySorted {
    /// Output tiling: `DataFunction { domain: 𝐽, codomain: 𝑉 }`.
    base: OperatorBase,
    /// The pairs, `DataFunction { domain: 𝐾, codomain: (𝐽, 𝑉) }`.
    input: Box<dyn TileOperator>,
    /// Whether the keys rise with the input's positions.
    order: KeyOrder,
}

/// How the new keys of [`RekeySorted`]'s input are ordered against its positions.
#[derive(Clone, Copy)]
pub enum KeyOrder {
    /// Each position carries a key above every key at the positions before it.
    Rising,
    /// The keys come in any order.
    Any,
}

impl RekeySorted {
    pub fn new(input: Box<dyn TileOperator>, order: KeyOrder) -> Self {
        let tiling = rekeyed_tiling(input.tiling());
        Self {
            base: OperatorBase::new(tiling),
            input,
            order,
        }
    }
}

/// The output tiling for an input of pairs, keyed by the pairs' first component and valued
/// by their second.
fn rekeyed_tiling(input: &Tiling) -> Tiling {
    let Tiling::DataFunction { codomain, .. } = input else {
        panic!("RekeySorted expected a collection, got {input:?}")
    };
    let (key, value) = match codomain.as_ref() {
        // A pair of scalars is one scalar column of records.
        Tiling::Scalar(Extent::Record(fields)) => (
            fields.get(&tuple_field(0)).cloned(),
            fields.get(&tuple_field(1)).cloned().map(Tiling::Scalar),
        ),
        Tiling::Record(fields) => (
            match fields.get(&tuple_field(0)) {
                Some(Tiling::Scalar(key)) => Some(key.clone()),
                _ => None,
            },
            fields.get(&tuple_field(1)).cloned(),
        ),
        _ => (None, None),
    };
    let (Some(key), Some(value)) = (key, value) else {
        panic!("RekeySorted expected pairs of a scalar key and a value, got {input:?}")
    };
    Tiling::data_function(key, value)
}

impl TileOperator for RekeySorted {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let input = BreakerInput::new(consumer, self.input.tiling(), false, cx);
        share_breaker(RekeySortedProducer {
            base: ProducerBase::new(
                RekeySortedProducer::alloc_id(),
                self.tiling(),
                &self.base,
                cx,
            )
            .breaking(input.downstream, input.placement),
            input: self
                .input
                .subscribe(self.input.tiling().universal_guard(), input.consumer, cx),
            output: self.tiling().empty_tile(),
            held: Vec::new(),
            complete: Complete::new(self.order),
            released_through: None,
            consumed: Predicate::False,
            consuming: false,
        })
    }
}

/// Producer for [`RekeySorted`].
struct RekeySortedProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    output: Tile,
    /// Position-to-key mappings above the consumed input prefix, in position order. These
    /// survive output release until an earlier input gap closes and their keys can advance
    /// output completeness.
    held: Vec<(Value, Value)>,
    /// The keys the output has called complete. They only grow, and a release of their rows
    /// does not shrink them.
    complete: Complete,
    /// Under rising keys, the greatest key whose row a release on the read-whole path dropped
    /// from `held` without calling it complete. A row that arrives later carries a key above it.
    released_through: Option<Value>,
    consumed: Predicate,
    consuming: bool,
}

impl TileProducer for RekeySortedProducer {
    /// Output keys name different positions; the input is read whole.
    fn input_level(&self, _role: &str, _level: CurryLevel) -> Option<CurryLevel> {
        None
    }

    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::holding(self.output.cell_count() + self.held.len())
    }

    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("input", &mut *self.input);
    }

    fn as_breaking_mut(&mut self) -> Option<&mut dyn BreakingProducer> {
        Some(self)
    }

    fn answers_from_state(&self) -> bool {
        self.consuming
    }

    fn get_impl(&mut self, guard: TileGuard) -> Tile {
        let projection = guard.projection_for(self);
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        if !self.consuming {
            // A key's position is known only once its row arrives, so the input is read whole
            // and the answer cut to the pull's keys.
            let mut tile = self.read_input(self.input.tiling().universal_guard());
            tile.restrict_to(&projection, self.tiling());
            tile
        } else {
            self.offer_impl(guard)
        }
    }

    fn release_impl(&mut self, _obsolete_guard: TileGuard) {
        self.output.remove_guarded(self.obsolete_guard().clone());
        if self.consuming {
            return;
        }
        // The accumulated guard, not the increment: a release that closes a gap releases the
        // rows above it that an earlier release named.
        let released = self.obsolete_guard().clone();
        if released.is_universal() {
            return self.input.release(self.input.tiling().universal_guard());
        }
        let through = self
            .held
            .iter()
            .take_while(|(key, _)| released.covers_path(std::slice::from_ref(key)))
            .last()
            .cloned();
        let Some((key, through)) = through else {
            return;
        };
        if matches!(self.complete, Complete::Through(_)) {
            self.released_through = Some(key);
        }
        self.held.retain(|(_, at)| at > &through);
        self.input
            .release(TileGuard::Function(FunctionGuard::Domain(
                Predicate::at_or_below(through),
            )));
    }
}

impl RekeySortedProducer {
    /// Only the continuous consumed prefix can advance a prefix-releasing input.
    fn consumed_prefix(&self) -> Predicate {
        match &self.consumed {
            Predicate::True => Predicate::True,
            Predicate::False => Predicate::False,
            Predicate::Intervals(intervals) => {
                intervals
                    .intervals()
                    .first()
                    .map_or(Predicate::False, |first| {
                        let prefix =
                            Predicate::intervals(intervalsets::IntervalSet::from(first.clone()));
                        if prefix.as_at_or_below().is_some() {
                            prefix
                        } else {
                            Predicate::False
                        }
                    })
            }
            other => panic!("RekeySorted consumes a region of ordered input positions: {other:?}"),
        }
    }

    fn read_input(&mut self, input_guard: TileGuard) -> Tile {
        let input = self.input.get(input_guard);
        let Tile::DataFunction {
            row_starts,
            domain: positions,
            codomain,
            domain_predicate,
            deleted,
            ..
        } = input
        else {
            panic!("RekeySorted expected a collection, got {input:?}")
        };
        assert_eq!(row_starts, vec![0], "RekeySorted re-keys one collection");
        assert!(
            deleted.is_empty(),
            "RekeySorted re-keys every row of its input"
        );
        let (keys, values) = match *codomain {
            Tile::Scalar(ColumnValue::Records(mut columns)) => (
                columns.remove(&tuple_field(0)),
                columns.remove(&tuple_field(1)).map(Tile::Scalar),
            ),
            Tile::Record { mut fields, absent } => {
                assert!(absent.is_empty(), "RekeySorted reads whole pairs");
                (
                    match fields.remove(&tuple_field(0)) {
                        Some(Tile::Scalar(keys)) => Some(keys),
                        _ => None,
                    },
                    fields.remove(&tuple_field(1)),
                )
            }
            other => panic!("RekeySorted expected pairs, got {other:?}"),
        };
        let (Some(keys), Some(values)) = (keys, values) else {
            panic!("RekeySorted expected pairs of a scalar key and a value")
        };
        let rows: Vec<(Value, Value)> = (0..positions.len())
            .map(|row| (keys.index_at(row), positions.index_at(row)))
            .collect();
        // `held` is in position order, so a position is looked up by binary search.
        let arrived: Vec<(Value, Value)> = rows
            .iter()
            .filter(|(_, at)| {
                self.held
                    .binary_search_by(|(_, held)| {
                        held.partial_cmp(at).expect("ordered input positions")
                    })
                    .is_err()
            })
            .cloned()
            .collect();
        // A released key is complete, so its row had arrived when it was released: a row
        // seen for the first time cannot carry one.
        debug_assert!(
            arrived
                .iter()
                .all(|(key, _)| !self.obsolete_guard().covers_path(std::slice::from_ref(key))),
            "a row arrived under a key {} has already released",
            self.name()
        );
        // Rising keys are the precondition the completeness below rests on, so a violation
        // stops here rather than declaring a key complete that a later row carries. Every key
        // through `through` is complete, so a row not seen before carries a key above it. The
        // check reads `complete` rather than `held`, because rows of the consumed prefix have
        // left `held`.
        if let Complete::Through(Some(through)) = &self.complete
            && let Some((key, at)) = arrived.iter().find(|(key, _)| key <= through)
        {
            panic!(
                "RekeySorted's keys rise with its input's order: key {key:?} at position \
                 {at:?} arrived after keys through {through:?} were complete"
            );
        }
        // On the read-whole path a release drops rows from `held` without calling their keys
        // complete, so the greatest key it dropped bounds what arrives after it the same way.
        if let Some(through) = &self.released_through
            && let Some((key, at)) = arrived.iter().find(|(key, _)| key <= through)
        {
            panic!(
                "RekeySorted's keys rise with its input's order: key {key:?} at position \
                 {at:?} arrived after the row of key {through:?} was released"
            );
        }
        self.consumed = self.consumed.union(&domain_predicate);
        self.held.extend(arrived);
        self.held
            .sort_by(|a, b| a.1.partial_cmp(&b.1).expect("ordered input positions"));
        // `held` holds every arrived row above the consumed prefix in position order, so its
        // keys rise across morsels and within this one.
        assert!(
            !matches!(self.complete, Complete::Through(_))
                || self.held.windows(2).all(|w| w[0].0 < w[1].0),
            "RekeySorted's keys rise with its input's order"
        );
        let prefix = self.consumed_prefix();
        for (key, at) in &self.held {
            if prefix.contains(at) {
                self.complete.add(key);
            }
        }
        let complete = match prefix.is_true() {
            true => Predicate::True,
            false => {
                let Tiling::DataFunction { domain, .. } = self.tiling() else {
                    unreachable!("RekeySorted outputs a collection")
                };
                self.complete.predicate(domain)
            }
        };
        // A collection's keys ascend, which keys in any order are put in.
        let mut order: Vec<usize> = (0..rows.len()).collect();
        order.sort_by(|&a, &b| {
            rows[a]
                .0
                .partial_cmp(&rows[b].0)
                .expect("the keys of one domain compare")
        });
        assert!(
            order.windows(2).all(|w| rows[w[0]].0 != rows[w[1]].0),
            "RekeySorted's keys are distinct"
        );
        let (keys, values) = match order.iter().enumerate().all(|(at, &row)| at == row) {
            true => (keys, values),
            false => (
                keys.select_indices(order.iter().copied(), order.len()),
                values.select_rows(&order),
            ),
        };
        let mut out = Tile::data_function(keys, Box::new(values), complete, deleted);
        // The rows above a gap in the released keys, which the input still holds.
        let released = self.obsolete_guard().clone();
        if !released.is_empty() {
            out.remove_guarded(released);
        }
        out
    }
}

impl Breaker for RekeySortedProducer {
    fn enter_consuming_mode(&mut self) {
        self.consuming = true;
    }
    fn consume_impl(&mut self, _: InputId, guard: TileGuard) {
        let tile = self.read_input(guard.clone());
        self.output.merge(tile);
        let prefix = self.consumed_prefix();
        self.input
            .release(TileGuard::Function(FunctionGuard::Domain(prefix.clone())));
        self.held.retain(|(_, position)| !prefix.contains(position));
    }
    fn input_tiling(&self, _: InputId) -> Tiling {
        self.input.tiling().clone()
    }
    fn input_released(&self, _: InputId) -> TileGuard {
        self.input.obsolete_guard().clone()
    }
    fn as_producer(&self) -> Option<&dyn BreakingProducer> {
        Some(self)
    }
}

impl BreakingProducer for RekeySortedProducer {
    fn complete(&self) -> TileGuard {
        self.output.to_guard()
    }
    fn offer_impl(&mut self, guard: TileGuard) -> Tile {
        let mut tile = self.output.clone();
        tile.restrict_to(&guard.projection_for(self), self.tiling());
        tile
    }
    fn morsels(&self, guard: &TileGuard, rows: usize) -> Vec<TileGuard> {
        cut_at_keys(
            guard,
            self.output
                .live_keys()
                .into_iter()
                .flatten()
                .map(|(_, key)| key),
            rows,
            self.tiling(),
        )
    }
}

/// The keys a [`RekeySortedProducer`] has called complete.
enum Complete {
    /// Under [`KeyOrder::Rising`], every key through the highest complete one, `None` before
    /// any.
    Through(Option<Value>),
    /// Under [`KeyOrder::Any`], the complete keys themselves.
    Any(Predicate),
}

impl Complete {
    fn new(order: KeyOrder) -> Complete {
        match order {
            KeyOrder::Rising => Complete::Through(None),
            KeyOrder::Any => Complete::Any(Predicate::False),
        }
    }

    /// Call `key`'s row complete.
    fn add(&mut self, key: &Value) {
        match self {
            Complete::Through(through) => {
                if through.as_ref().is_none_or(|through| key > through) {
                    *through = Some(key.clone());
                }
            }
            Complete::Any(keys) if !keys.contains(key) => {
                *keys = keys.union(&Predicate::point(key.clone()));
            }
            Complete::Any(_) => {}
        }
    }

    /// The complete keys over the output's domain `key`.
    fn predicate(&self, key: &Extent) -> Predicate {
        match self {
            Complete::Through(None) => Predicate::False,
            Complete::Through(Some(through)) => Predicate::at_or_below_in(through.clone(), key),
            Complete::Any(keys) => keys.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::BaseType;
    use crate::interpreter::tile_operators::test_helpers::ReleaseSpy;
    use bit_set::BitSet;
    use std::collections::HashMap;

    /// Commits at `positions`, each carrying the pair `(key, value)`.
    fn pairs(positions: &[u64], keys: &[u64], values: &[i64], complete: Predicate) -> Tile {
        Tile::data_function(
            ColumnValue::from_uints(positions.to_vec()),
            Box::new(Tile::Scalar(ColumnValue::Records(HashMap::from([
                (tuple_field(0), ColumnValue::from_uints(keys.to_vec())),
                (tuple_field(1), ColumnValue::Ints(values.to_vec())),
            ])))),
            complete,
            BitSet::new(),
        )
    }

    fn pair_tiling() -> Tiling {
        Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Record(HashMap::from([
                (tuple_field(0), Extent::Base(BaseType::UInt)),
                (tuple_field(1), Extent::Base(BaseType::Int)),
            ]))),
        )
    }

    /// A producer over `input`, pulled once, with the guards it forwards upstream.
    fn pulled(input: Tile) -> (RekeySortedProducer, Tile, Rc<RefCell<Vec<TileGuard>>>) {
        pulled_in(input, KeyOrder::Rising)
    }

    /// [`pulled`] for keys ordered as `order` says.
    fn pulled_in(
        input: Tile,
        order: KeyOrder,
    ) -> (RekeySortedProducer, Tile, Rc<RefCell<Vec<TileGuard>>>) {
        let (spy, released) = ReleaseSpy::new(input, pair_tiling());
        let tiling = rekeyed_tiling(&pair_tiling());
        let mut producer = RekeySortedProducer {
            base: ProducerBase::unowned(RekeySortedProducer::alloc_id(), &tiling),
            input: Box::new(spy),
            output: tiling.empty_tile(),
            held: Vec::new(),
            complete: Complete::new(order),
            released_through: None,
            consumed: Predicate::False,
            consuming: false,
        };
        producer.enter_consuming_mode();
        producer.consume_impl(InputId::ONLY, pair_tiling().universal_guard());
        let out = producer.get(tiling.universal_guard());
        (producer, out, released)
    }

    /// A producer over rising keys that reads `input` whole, pulled once, and the guards it
    /// forwards upstream: the path a breaker takes outside consuming mode.
    fn read_whole(input: Tile) -> (RekeySortedProducer, Tile, Rc<RefCell<Vec<TileGuard>>>) {
        let (spy, released) = ReleaseSpy::new(input, pair_tiling());
        let tiling = rekeyed_tiling(&pair_tiling());
        let mut producer = RekeySortedProducer {
            base: ProducerBase::unowned(RekeySortedProducer::alloc_id(), &tiling),
            input: Box::new(spy),
            output: tiling.empty_tile(),
            held: Vec::new(),
            complete: Complete::new(KeyOrder::Rising),
            released_through: None,
            consumed: Predicate::False,
            consuming: false,
        };
        let out = producer.get(tiling.universal_guard());
        (producer, out, released)
    }

    fn keys(keys: Predicate) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(keys))
    }

    fn uint(n: u64) -> Value {
        Value::UInt(n)
    }

    /// A later morsel cannot release an unread earlier tick or rule its output key absent.
    #[test]
    fn reverse_morsels_release_only_the_consumed_prefix() {
        use crate::interpreter::tile_operators::test_helpers::ProjectionSpy;
        let input_tiling = pair_tiling();
        let (spy, _, releases) = ProjectionSpy::new(
            pairs(&[0, 1], &[0, 1], &[10, 20], Predicate::True),
            input_tiling,
        );
        let tiling = rekeyed_tiling(&pair_tiling());
        let mut producer = RekeySortedProducer {
            base: ProducerBase::unowned(RekeySortedProducer::alloc_id(), &tiling),
            input: Box::new(spy),
            output: tiling.empty_tile(),
            held: Vec::new(),
            complete: Complete::new(KeyOrder::Rising),
            released_through: None,
            consumed: Predicate::False,
            consuming: false,
        };
        producer.enter_consuming_mode();
        producer.consume_impl(InputId::ONLY, keys(Predicate::point(uint(1))));
        assert!(producer.input.obsolete_guard().is_empty());
        let Tile::DataFunction {
            domain_predicate, ..
        } = &producer.output
        else {
            unreachable!()
        };
        assert!(!domain_predicate.contains(&uint(0)));
        producer.release(keys(Predicate::point(uint(1))));
        producer.enter_consuming_mode();
        producer.consume_impl(InputId::ONLY, keys(Predicate::point(uint(0))));
        assert!(
            producer
                .complete
                .predicate(&producer.tiling().domain_extent().unwrap())
                .contains(&uint(1))
        );
        assert_eq!(
            producer.input.obsolete_guard(),
            &keys(Predicate::at_or_below(uint(1)))
        );
        assert!(
            releases
                .borrow()
                .iter()
                .all(|guard| guard.is_empty() || *guard == keys(Predicate::at_or_below(uint(1))))
        );
    }

    /// The output is complete through the key at the input's last complete position, before
    /// the input completes.
    #[test]
    fn completeness_passes_through_by_key() {
        let (_, out, _) = pulled(pairs(
            &[3, 7, 9],
            &[0, 1, 2],
            &[10, 20, 30],
            Predicate::at_or_below(uint(7)),
        ));
        let Tile::DataFunction {
            domain,
            codomain,
            domain_predicate,
            ..
        } = out
        else {
            panic!("expected a collection")
        };
        assert_eq!(domain, ColumnValue::from_uints(vec![0, 1, 2]));
        assert_eq!(*codomain, Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30])));
        assert_eq!(domain_predicate, Predicate::at_or_below(uint(1)));
    }

    /// On the read-whole path, a prefix of keys is released as the prefix of positions that
    /// carries them.
    #[test]
    fn a_key_prefix_releases_a_position_prefix() {
        let (mut producer, _, released) = read_whole(pairs(
            &[3, 7, 9],
            &[0, 1, 2],
            &[10, 20, 30],
            Predicate::True,
        ));
        producer.release(keys(Predicate::at_or_below(uint(1))));
        assert_eq!(
            *released.borrow(),
            vec![keys(Predicate::at_or_below(uint(7)))]
        );
    }

    /// On the read-whole path, a release with a gap below it forwards nothing until the gap is
    /// released, and the key above the gap leaves the output meanwhile.
    #[test]
    fn a_gap_holds_the_rows_above_it() {
        let (mut producer, _, released) = read_whole(pairs(
            &[3, 7, 9],
            &[0, 1, 2],
            &[10, 20, 30],
            Predicate::True,
        ));
        producer.release(keys(Predicate::point(uint(1))));
        assert!(released.borrow().is_empty(), "{:?}", released.borrow());
        let out = producer.get(producer.tiling().universal_guard());
        assert_eq!(
            out.live_keys()
                .map(|k| k.map(|(_, key)| key).collect::<Vec<_>>()),
            Some(vec![uint(0), uint(2)])
        );
        producer.release(keys(Predicate::point(uint(0))));
        assert_eq!(
            *released.borrow(),
            vec![keys(Predicate::at_or_below(uint(7)))]
        );
    }

    /// On the read-whole path, key 10 at position 0 is read while nothing is complete and then
    /// released, which drops its row. Key 5 then arrives at position 1, beneath it.
    #[test]
    #[should_panic(expected = "RekeySorted's keys rise with its input's order")]
    fn keys_falling_beneath_a_released_row_fail() {
        let (mut producer, _, _) = read_whole(pairs(&[0], &[10], &[1], Predicate::False));
        producer.release(keys(Predicate::point(uint(10))));
        // The input answers what arrived since, without the released position 0.
        let (grown, _) = ReleaseSpy::new(pairs(&[1], &[5], &[2], Predicate::False), pair_tiling());
        producer.input = Box::new(grown);
        producer.get(producer.tiling().universal_guard());
    }

    #[test]
    fn a_pull_at_some_keys_answers_those_keys() {
        let (mut producer, _, _) = pulled(pairs(
            &[3, 7, 9],
            &[0, 1, 2],
            &[10, 20, 30],
            Predicate::True,
        ));
        let out = producer.get(keys(Predicate::point(uint(1))));
        let Tile::DataFunction {
            domain, codomain, ..
        } = out
        else {
            panic!("expected a collection")
        };
        assert_eq!(domain, ColumnValue::from_uints(vec![1]));
        assert_eq!(*codomain, Tile::Scalar(ColumnValue::Ints(vec![20])));
    }

    /// A pull of nothing answers the empty tile without pulling the input, and keeps the rows
    /// the last pull held.
    #[test]
    fn a_pull_of_nothing_reads_no_input() {
        use crate::interpreter::tile_operators::test_helpers::ProjectionSpy;
        let (spy, pulled, _) = ProjectionSpy::new(
            pairs(&[3, 7, 9], &[0, 1, 2], &[10, 20, 30], Predicate::True),
            pair_tiling(),
        );
        let tiling = rekeyed_tiling(&pair_tiling());
        let mut producer = RekeySortedProducer {
            base: ProducerBase::unowned(RekeySortedProducer::alloc_id(), &tiling),
            input: Box::new(spy),
            output: tiling.empty_tile(),
            held: Vec::new(),
            complete: Complete::new(KeyOrder::Rising),
            released_through: None,
            consumed: Predicate::False,
            consuming: false,
        };
        assert_eq!(producer.get(tiling.empty_guard()), tiling.empty_tile());
        assert!(pulled.borrow().is_empty(), "{:?}", pulled.borrow());
        assert!(producer.held.is_empty());
        producer.get(keys(Predicate::point(uint(1))));
        let held = producer.held.clone();
        assert_eq!(held.len(), 3);
        assert_eq!(producer.get(tiling.empty_guard()), tiling.empty_tile());
        assert_eq!(pulled.borrow().len(), 1, "{:?}", pulled.borrow());
        assert_eq!(producer.held, held);
    }

    /// A breaker over rising keys, whose input holds `row_keys` at positions 0, 1, …, consuming
    /// `positions` one morsel at a time, in that order.
    fn consumed_one_at_a_time(row_keys: &[u64], positions: &[u64]) -> RekeySortedProducer {
        use crate::interpreter::tile_operators::test_helpers::ProjectionSpy;
        let all: Vec<u64> = (0..row_keys.len() as u64).collect();
        let values: Vec<i64> = (0..row_keys.len() as i64).collect();
        let (spy, _, _) = ProjectionSpy::new(
            pairs(&all, row_keys, &values, Predicate::True),
            pair_tiling(),
        );
        let tiling = rekeyed_tiling(&pair_tiling());
        let mut producer = RekeySortedProducer {
            base: ProducerBase::unowned(RekeySortedProducer::alloc_id(), &tiling),
            input: Box::new(spy),
            output: tiling.empty_tile(),
            held: Vec::new(),
            complete: Complete::new(KeyOrder::Rising),
            released_through: None,
            consumed: Predicate::False,
            consuming: false,
        };
        producer.enter_consuming_mode();
        for &at in positions {
            producer.consume_impl(InputId::ONLY, keys(Predicate::point(uint(at))));
        }
        producer
    }

    /// Key 5 at position 1 arrives after position 0's key 10 made every key through 10
    /// complete: the keys fall across the two morsels.
    #[test]
    #[should_panic(expected = "RekeySorted's keys rise with its input's order")]
    fn keys_falling_across_two_morsels_fail() {
        consumed_one_at_a_time(&[10, 5], &[0, 1]);
    }

    /// Key 10 at position 2 arrives above the gap at positions 0 and 1, so nothing is complete,
    /// and key 20 then arrives at position 1, beneath it: the retained rows' keys fall in
    /// position order.
    #[test]
    #[should_panic(expected = "RekeySorted's keys rise with its input's order")]
    fn keys_falling_beneath_a_row_held_above_a_gap_fail() {
        consumed_one_at_a_time(&[5, 20, 10], &[2, 1]);
    }

    /// Positions consumed in reverse with keys rising in position order are valid: nothing is
    /// complete until position 0 arrives, and then keys 10 and 20 are.
    #[test]
    fn rising_keys_consumed_in_reverse_are_complete_once_the_prefix_arrives() {
        let producer = consumed_one_at_a_time(&[10, 20], &[1, 0]);
        let Tile::DataFunction {
            domain,
            domain_predicate,
            ..
        } = &producer.output
        else {
            panic!("expected a collection")
        };
        let mut keys: Vec<Value> = (0..domain.len()).map(|row| domain.index_at(row)).collect();
        keys.sort_by(|a, b| a.partial_cmp(b).expect("keys compare"));
        assert_eq!(keys, [uint(10), uint(20)]);
        for key in [10, 20] {
            assert!(
                domain_predicate.contains(&uint(key)),
                "{domain_predicate:?}"
            );
        }
    }

    /// Keys in any order are answered in key order, and each is complete where its row is.
    #[test]
    fn keys_in_any_order_are_complete_where_their_rows_are() {
        let (_, out, _) = pulled_in(
            pairs(
                &[3, 7, 9],
                &[0, 2, 1],
                &[10, 20, 30],
                Predicate::at_or_below(uint(7)),
            ),
            KeyOrder::Any,
        );
        let Tile::DataFunction {
            domain,
            codomain,
            domain_predicate,
            ..
        } = out
        else {
            panic!("expected a collection")
        };
        assert_eq!(domain, ColumnValue::from_uints(vec![0, 1, 2]));
        assert_eq!(*codomain, Tile::Scalar(ColumnValue::Ints(vec![10, 30, 20])));
        assert_eq!(
            domain_predicate,
            Predicate::point(uint(0)).union(&Predicate::point(uint(2)))
        );
    }

    #[test]
    fn a_universal_release_releases_the_input() {
        let (mut producer, _, released) =
            pulled(pairs(&[3, 7], &[0, 1], &[10, 20], Predicate::True));
        producer.release(producer.tiling().universal_guard());
        assert!(
            released.borrow().iter().any(TileGuard::is_universal),
            "{:?}",
            released.borrow()
        );
    }
    /// The declared input level matches the whole read used to translate output keys.
    #[test]
    fn a_projected_rekey_declares_the_input_level_it_reads() {
        use crate::interpreter::tile_operators::test_helpers::ProjectionSpyOp;
        let (input, pulled, _) = ProjectionSpyOp::new(
            pairs(&[3, 7, 9], &[0, 1, 2], &[10, 20, 30], Predicate::True),
            pair_tiling(),
        );
        let mut operator = RekeySorted::new(Box::new(input), KeyOrder::Rising);
        let tiling = operator.tiling().clone();
        let mut cx = Default::default();
        let mut producer = operator.subscribe(tiling.universal_guard(), Box::new(|| {}), &mut cx);
        let guard = keys(Predicate::point(uint(1)));
        let level = Projection::of(&guard)
            .expect("a key projection")
            .level()
            .unwrap();
        fn leaf_level(
            producer: &dyn TileProducer,
            level: Option<CurryLevel>,
        ) -> Option<CurryLevel> {
            let mut leaf = level;
            producer.visit_input_producers(&mut |role, input| {
                leaf = leaf_level(
                    input,
                    level.and_then(|level| producer.input_level(role, level)),
                );
            });
            leaf
        }
        let declared = leaf_level(&*producer, Some(level));
        let _ = producer.get(guard);
        let pulled = pulled.borrow();
        assert_eq!(pulled.len(), 1);
        let actual = Projection::of(&pulled[0])
            .expect("an input projection")
            .level();
        assert_eq!(declared, actual);
    }
}
