use super::*;
use crate::interpreter::operator_graph::value;
use crate::interpreter::scheduler::restating;
use crate::interpreter::{BaseType, ColumnValue, Consumer, Extent, Scheduler, Value, tuple_field};

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
/// A release names output keys, and the input is released by its own positions. Under rising
/// keys a prefix of keys is a prefix of positions, so the operator forwards the longest prefix
/// of the input whose every row has its key released. A release that is not a prefix of keys
/// leaves a gap the input keeps until the keys below it are released too; the operator drops
/// those rows from its output itself. Its one input today, a reply tap's `StoreValueStream`,
/// honors only a prefix of commit ticks, so a prefix is also all it could be told.
///
/// A region an input pushes or notifies names input positions, and which output keys sit at
/// those positions is data the operator reads only at its next pull. The caller supplies the
/// restatement, `restate`, from what it knows of the input: a reply tap's store records the
/// item each commit answered ([`CommittedItems`]).
///
/// [`CommittedItems`]: crate::interpreter::commit_operator::CommittedItems
pub struct RekeySorted {
    /// Output tiling: `DataFunction { domain: 𝐽, codomain: 𝑉 }`.
    base: OperatorBase,
    /// The pairs, `DataFunction { domain: 𝐾, codomain: (𝐽, 𝑉) }`.
    input: Box<dyn TileOperator>,
    /// The output's domain, the pairs' first component, which a prefix of a union key needs
    /// for its tags.
    key: Extent,
    /// A region of input positions restated as the output keys at those positions.
    restate: Rc<dyn Fn(&Projection) -> Projection>,
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
    pub fn new(
        input: Box<dyn TileOperator>,
        restate: Rc<dyn Fn(&Projection) -> Projection>,
        order: KeyOrder,
    ) -> Self {
        let (tiling, key) = rekeyed_tiling(input.tiling());
        Self {
            base: OperatorBase::new(tiling),
            input,
            key,
            restate,
            order,
        }
    }
}

/// The output tiling for an input of pairs, keyed by the pairs' first component and valued
/// by their second, with that component's extent.
fn rekeyed_tiling(input: &Tiling) -> (Tiling, Extent) {
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
    (Tiling::data_function(key.clone(), value), key)
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
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(RekeySortedProducer {
            base: ProducerBase::new(
                RekeySortedProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            input: self.input.subscribe(
                self.tiling().universal_guard(),
                {
                    let restate = self.restate.clone();
                    restating(Box::new(move |region| restate(region)), consumer)
                },
                scheduler,
            ),
            held: Vec::new(),
            complete: Complete::new(self.order),
            key: self.key.clone(),
        })
    }
}

/// Producer for [`RekeySorted`].
struct RekeySortedProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    /// The rows the input returned on the last pull, as `(key, position)` in the input's
    /// order, which is also key order under [`KeyOrder::Rising`].
    held: Vec<(Value, Value)>,
    /// The keys the output has called complete. They only grow, and a release of their rows
    /// does not shrink them.
    complete: Complete,
    /// The output's domain ([`RekeySorted::key`]).
    key: Extent,
}

impl TileProducer for RekeySortedProducer {
    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::holding(self.held.len())
    }

    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("input", &mut *self.input);
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection_for(self);
        let input = self.input.get(self.input.tiling().universal_guard());
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
        for (key, at) in &rows {
            if domain_predicate.contains(at) {
                self.complete.add(key);
            }
        }
        let complete = match domain_predicate.is_true() {
            true => Predicate::True,
            false => self.complete.predicate(&self.key),
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
        self.held = rows;
        let mut out = Tile::data_function(keys, Box::new(values), complete, deleted);
        // The rows above a gap in the released keys, which the input still holds.
        let released = self.obsolete_guard().clone();
        if !released.is_empty() {
            out.remove_guarded(released);
        }
        // The input is read whole, because a key's position is known only once its row
        // arrives; the answer is cut to the pull's keys.
        out.restrict_to(&projection, self.tiling());
        out
    }

    fn release_impl(&mut self, _obsolete_guard: TileGuard) {
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
        let (tiling, key) = rekeyed_tiling(&pair_tiling());
        let mut producer = RekeySortedProducer {
            base: ProducerBase::unowned(RekeySortedProducer::alloc_id(), &tiling),
            input: Box::new(spy),
            held: Vec::new(),
            complete: Complete::new(order),
            key,
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

    /// A prefix of keys is released as the prefix of positions that carries them.
    #[test]
    fn a_key_prefix_releases_a_position_prefix() {
        let (mut producer, _, released) = pulled(pairs(
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

    /// A release with a gap below it forwards nothing until the gap is released, and the key
    /// above the gap leaves the output meanwhile.
    #[test]
    fn a_gap_holds_the_rows_above_it() {
        let (mut producer, _, released) = pulled(pairs(
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

    /// A pull at some keys reads the input whole and answers those keys alone.
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

    /// Under keys in any order, the input is released through the last position whose key, and
    /// every key at a position before it, is released.
    #[test]
    fn keys_in_any_order_release_a_position_prefix() {
        let (mut producer, _, released) = pulled_in(
            pairs(&[3, 7, 9], &[0, 2, 1], &[10, 20, 30], Predicate::True),
            KeyOrder::Any,
        );
        producer.release(keys(Predicate::point(uint(1))));
        assert!(released.borrow().is_empty(), "{:?}", released.borrow());
        producer.release(keys(Predicate::point(uint(0))));
        assert_eq!(
            *released.borrow(),
            vec![keys(Predicate::at_or_below(uint(3)))]
        );
        producer.release(keys(Predicate::point(uint(2))));
        assert_eq!(
            released.borrow().last(),
            Some(&keys(Predicate::at_or_below(uint(9))))
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
}
