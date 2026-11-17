use super::*;
use crate::interpreter::operator_graph::value;
use crate::interpreter::{BaseType, ColumnValue, Consumer, Extent, Value, tuple_field};

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
    input: Arc<dyn TileOperator>,
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

impl KeyOrder {
    /// The order a site commits its items in, from its source's positions. A stream's positions,
    /// `UInt`s or a range of them, are delivered in their own order, so its items commit rising.
    /// Any other source's need not be: a product's, a record of its dimensions' positions, and a
    /// concatenation's, a union of its parts', deliver their parts independently, and a keyed
    /// collection's keys, a group-by's say, arrive as their groups complete.
    pub fn of_items(positions: &Extent) -> KeyOrder {
        match positions {
            Extent::Base(BaseType::UInt) | Extent::UIntRange(_) => KeyOrder::Rising,
            _ => KeyOrder::Any,
        }
    }
}

impl RekeySorted {
    pub fn new(input: Arc<dyn TileOperator>, order: KeyOrder) -> Self {
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

    fn subscribe_impl(
        self: Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let input = BreakerInput::new(consumer, self.input.tiling(), false);
        share_breaker(RekeySortedProducer {
            base: ProducerBase::new(
                RekeySortedProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            )
            .breaking(input.downstream, input.placement),
            input: self.input.clone().subscribe(
                self.input.tiling().universal_guard(),
                input.consumer,
                cx,
            ),
            output: self.tiling().empty_tile(),
            held: Vec::new(),
            complete: Complete::new(self.order),
            consumed: Predicate::False,
        })
    }
}

/// Producer for [`RekeySorted`].
struct RekeySortedProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    output: Tile,
    /// Position-to-key mappings above the consumed input prefix. These survive output release
    /// until an earlier input gap closes and their keys can advance output completeness.
    held: Vec<(Value, Value)>,
    /// The keys the output has called complete. They only grow, and a release of their rows
    /// does not shrink them.
    complete: Complete,
    consumed: Predicate,
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

    fn get_impl(&mut self, guard: TileGuard) -> Tile {
        if self.base.reads_input() {
            let mut tile = self.read_input(self.input.tiling().universal_guard());
            tile.restrict_to(&guard.projection_for(self), self.tiling());
            tile
        } else {
            let mut tile = self.output.clone();
            tile.restrict_to(&guard.projection_for(self), self.tiling());
            tile
        }
    }

    fn release_impl(&mut self, _obsolete_guard: TileGuard) {
        self.output.remove_guarded(self.obsolete_guard().clone());
        if self
            .base
            .placement
            .as_ref()
            .is_some_and(|at| at.get().is_some())
        {
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
            .map(|(_, at)| at.clone());
        let Some(through) = through else {
            return;
        };
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
        // The precondition the completeness below rests on, so a violation stops here rather
        // than declaring a key complete that a later row carries.
        assert!(
            matches!(self.complete, Complete::Any(_)) || rows.windows(2).all(|w| w[0].0 < w[1].0),
            "RekeySorted's keys rise with its input's order"
        );
        // A released key is complete, so its row had arrived when it was released: a row
        // seen for the first time cannot carry one.
        debug_assert!(
            rows.iter()
                .filter(|(_, at)| !self.held.iter().any(|(_, held)| held == at))
                .all(|(key, _)| !self.obsolete_guard().covers_path(std::slice::from_ref(key))),
            "a row arrived under a key {} has already released",
            self.name()
        );
        self.consumed = self.consumed.union(&domain_predicate);
        for row in &rows {
            if !self.held.iter().any(|(_, at)| at == &row.1) {
                self.held.push(row.clone());
            }
        }
        self.held
            .sort_by(|a, b| a.1.partial_cmp(&b.1).expect("ordered input positions"));
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
        // The input is read whole, because a key's position is known only once its row
        // arrives; the answer is cut to the pull's keys.
        out
    }
}

impl Breaker for RekeySortedProducer {
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
    fn pulled(input: Tile) -> (RekeySortedProducer, Tile, Arc<RwLock<Vec<TileGuard>>>) {
        pulled_in(input, KeyOrder::Rising)
    }

    /// [`pulled`] for keys ordered as `order` says.
    fn pulled_in(
        input: Tile,
        order: KeyOrder,
    ) -> (RekeySortedProducer, Tile, Arc<RwLock<Vec<TileGuard>>>) {
        let (spy, released) = ReleaseSpy::new(input, pair_tiling());
        let tiling = rekeyed_tiling(&pair_tiling());
        let mut producer = RekeySortedProducer {
            base: ProducerBase::unowned(RekeySortedProducer::alloc_id(), &tiling),
            input: Box::new(spy),
            output: tiling.empty_tile(),
            held: Vec::new(),
            complete: Complete::new(order),
            consumed: Predicate::False,
        };
        producer.consume_in_pipeline(InputId::ONLY, pair_tiling().universal_guard());
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
            consumed: Predicate::False,
        };
        producer.consume_in_pipeline(InputId::ONLY, keys(Predicate::point(uint(1))));
        assert!(producer.input.obsolete_guard().is_empty());
        let Tile::DataFunction {
            domain_predicate, ..
        } = &producer.output
        else {
            unreachable!()
        };
        assert!(!domain_predicate.contains(&uint(0)));
        producer.release(keys(Predicate::point(uint(1))));
        producer.consume_in_pipeline(InputId::ONLY, keys(Predicate::point(uint(0))));
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
                .read()
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
            released.read().iter().any(TileGuard::is_universal),
            "{:?}",
            released.read()
        );
    }
    /// The declared input level matches the whole read used to translate output keys.
    #[test]
    fn a_projected_rekey_declares_the_input_level_it_reads() {
        use crate::interpreter::tile_operators::test_helpers::{
            ProjectionSpyOp, ReadInPipeline as _,
        };
        let (input, pulled, _) = ProjectionSpyOp::new(
            pairs(&[3, 7, 9], &[0, 1, 2], &[10, 20, 30], Predicate::True),
            pair_tiling(),
        );
        let operator = Arc::new(RekeySorted::new(Arc::new(input), KeyOrder::Rising));
        let tiling = operator.tiling().clone();
        let mut cx = Default::default();
        let mut producer =
            operator
                .clone()
                .subscribe(tiling.universal_guard(), Box::new(|| {}), &mut cx);
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
        let _ = producer.read_in_pipeline(guard);
        let pulled = pulled.read();
        assert_eq!(pulled.len(), 1);
        let actual = Projection::of(&pulled[0])
            .expect("an input projection")
            .level();
        assert_eq!(declared, actual);
    }
}
