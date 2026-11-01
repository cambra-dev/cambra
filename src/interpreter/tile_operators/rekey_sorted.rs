use super::*;
use crate::interpreter::operator_graph::value;
use crate::interpreter::{ColumnValue, Consumer, Extent, Scheduler, Value, tuple_field};

/// Re-keys a collection of pairs by each pair's first component, `𝐾 ⤇ (𝐽, 𝑉)` to `𝐽 ⤇ 𝑉`, where
/// those keys are distinct and rise with the input's own key order: the `map` constructor's
/// re-keying (group by the new key, then take the group's one element) for input that states
/// its new keys in sorted order.
///
/// Its one use is a reply tap read keyed by item (`src/ccl/design/mutability.md`, "A block in
/// value position"): the tap's `StoreValueStream`, `Txn ⤇ (𝐼, 𝑉)`, holds the item position the
/// writer committed each value with, and a site commits its items once each and in its source's
/// order. No CCL term names it: op-conversion builds it for the read.
///
/// The rising keys are what the operator is for. Once the input is complete through a
/// position, no later position carries a key at or below the one there, so the output is
/// complete through that key: an entry is final as soon as the input is complete through it,
/// where a group-by of the pairs could close no group before the whole input completes.
///
/// A release names output keys, and the input is released by its own positions. Under rising
/// keys a prefix of keys is a prefix of positions, so the operator forwards the longest prefix
/// of the input whose every row has its key released. A release that is not a prefix of keys
/// leaves a gap the input keeps until the keys below it are released too; the operator drops
/// those rows from its output itself. Its one input today, a reply tap's `StoreValueStream`,
/// honors only a prefix of commit ticks, so a prefix is also all it could be told.
pub struct RekeySorted {
    /// Output tiling: `DataFunction { domain: 𝐽, codomain: 𝑉 }`.
    base: OperatorBase,
    /// The pairs, `DataFunction { domain: 𝐾, codomain: (𝐽, 𝑉) }`.
    input: Box<dyn TileOperator>,
    /// The output's domain, the pairs' first component, which a prefix of a union key needs
    /// for its tags.
    key: Extent,
}

impl RekeySorted {
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let (tiling, key) = rekeyed_tiling(input.tiling());
        Self {
            base: OperatorBase::new(tiling),
            input,
            key,
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
            input: self
                .input
                .subscribe(self.tiling().universal_guard(), consumer, scheduler),
            held: Vec::new(),
            complete_through: None,
            key: self.key.clone(),
        })
    }
}

/// Producer for [`RekeySorted`].
struct RekeySortedProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    /// The rows the input returned on the last pull, as `(key, position)` in the input's
    /// order, which is also key order.
    held: Vec<(Value, Value)>,
    /// The highest key the output has called complete. It only rises, and a release of the
    /// rows below it does not lower it.
    complete_through: Option<Value>,
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

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input = self.input.get(self.input.tiling().universal_guard());
        let Tile::DataFunction {
            row_starts,
            domain: positions,
            codomain,
            domain_predicate,
            deleted,
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
            rows.windows(2).all(|w| w[0].0 < w[1].0),
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
            if domain_predicate.contains(at)
                && self.complete_through.as_ref().is_none_or(|c| key > c)
            {
                self.complete_through = Some(key.clone());
            }
        }
        self.held = rows;
        let complete = if domain_predicate.is_true() {
            Predicate::True
        } else {
            match &self.complete_through {
                Some(key) => Predicate::at_or_below_in(key.clone(), &self.key),
                None => Predicate::False,
            }
        };
        let mut out = Tile::data_function(keys, Box::new(values), complete, deleted);
        // The rows above a gap in the released keys, which the input still holds.
        let released = self.obsolete_guard().clone();
        if !released.is_empty() {
            out.remove_guarded(released);
        }
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
    fn pulled(
        input: Tile,
    ) -> (
        RekeySortedProducer,
        Tile,
        Rc<std::cell::RefCell<Vec<TileGuard>>>,
    ) {
        let (spy, released) = ReleaseSpy::new(input, pair_tiling());
        let (tiling, key) = rekeyed_tiling(&pair_tiling());
        let mut producer = RekeySortedProducer {
            base: ProducerBase::unowned(RekeySortedProducer::alloc_id(), &tiling),
            input: Box::new(spy),
            held: Vec::new(),
            complete_through: None,
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
