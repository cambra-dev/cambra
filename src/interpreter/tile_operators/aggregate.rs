use bit_set::BitSet;
use bit_vec::BitVec;
use log::trace;
use std::collections::HashMap;

use super::*;
use crate::{
    ccl::AggregateKind,
    interpreter::{ColumnValue, Consumer, Scheduler, Value},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// Reduces a `SealedFunction` input to a single scalar via an aggregation operation.
///
/// On each `get`, reads all codomain values from the input and folds them into a
/// running `Tile::Aggregation` accumulator. The result becomes terminal once the
/// input's `domain_predicate` is `True` (all elements seen).
pub struct Aggregate {
    /// The `SealedFunction`-typed input whose codomain elements are aggregated.
    input: Box<dyn TileOperator>,
    /// Identity and the output tiling — always
    /// `Tiling::Aggregation { accumulator: <output extent> }`.
    base: OperatorBase,
}

impl Aggregate {
    /// Construct an `Aggregate` operator.
    ///
    /// Panics if `input` does not have a `SealedFunction` tiling, or if `kind`
    /// does not support the codomain element type.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        let err = || panic!("Cannot apply {kind:?} to non-function {:?}", input.tiling());
        let codomain_extent = input
            .tiling()
            .codomain()
            .map(|t| t.extent())
            .unwrap_or_else(err);
        let tiling = Tiling::Aggregation {
            kind,
            accumulator: kind.output_extent(&codomain_extent).unwrap_or_else(err),
        };
        Self {
            input,
            base: OperatorBase::new(tiling),
        }
    }
}

impl TileOperator for Aggregate {
    impl_operator_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let input_producer =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(AggregateProducer::new(
            self.base.tiling.clone(),
            input_producer,
        ))
    }
}

struct AggregateProducer {
    base: ProducerBase,
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation.
    kind: AggregateKind,
    /// Running accumulation state; updated in place on each `get`.
    accumulator: Tile,
    /// Set once the consumer has released this output universally, after which
    /// the accumulator must never be handed back — it *is* the whole output, so
    /// re-emitting it returns released data.
    released: bool,
}

impl AggregateProducer {
    /// Construct an `AggregateProducer`, seeding the accumulator with the identity element.
    fn new(tiling: Tiling, input: Box<dyn TileProducer>) -> Self {
        let (kind, accumulator) = match &tiling {
            Tiling::Aggregation {
                kind,
                accumulator: acc_extent,
            } => (
                *kind,
                Tile::Aggregation {
                    kind: *kind,
                    accumulator: kind.initial_accumulator(acc_extent),
                    terminal: ColumnValue::Bools(BitVec::from_elem(1, false)),
                },
            ),
            other => panic!("AggregateProducer created with non-Aggregation tiling: {other:?}"),
        };
        Self {
            base: ProducerBase::new(Self::alloc_id(), &tiling),
            input,
            kind,
            accumulator,
            released: false,
        }
    }
}

impl TileProducer for AggregateProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        if self.released {
            return self.tiling().empty_tile();
        }
        let i_tiling = self.input.tiling().clone();
        let mut input_result = self.input.get(i_tiling.universal_guard());
        let upstream_guard = input_result.to_guard();
        input_result.compact();
        let Tile::SealedFunction { codomain, .. } = input_result else {
            panic!("Aggregate expected function tiling, got {input_result:?}");
        };
        self.input.release(upstream_guard);
        let values = scalar_tile_to_column_value(*codomain);

        let is_terminal = self.input.obsolete_guard().is_universal();
        trace!(
            "Aggregate input is_terminal: {is_terminal} from guard {:?}",
            self.input.obsolete_guard()
        );
        let Tile::Aggregation {
            kind: _,
            ref mut accumulator,
            terminal: ColumnValue::Bools(ref mut terminal),
        } = self.accumulator
        else {
            panic!("Accumulator must be Aggregation tile")
        };
        self.kind.accumulate(accumulator, &values, 0, values.len());
        terminal.set(0, is_terminal);
        self.accumulator.clone()
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // An `Aggregation` guard is all-or-nothing — the accumulator has no
        // sub-regions — so the only release that can arrive is the universal one.
        // Releasing the input in full is what `get_impl` cannot do: it releases
        // each delivery as it folds it in, so whatever the input never delivered
        // — this aggregate being done before its source ran dry — would stay
        // stranded upstream.
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.released = true;
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

pub struct ExtractAggregate {
    input: Box<dyn TileOperator>,
    /// Identity and the output tiling.
    base: OperatorBase,
    kind: AggregateKind,
    only_terminal: bool,
}

impl ExtractAggregate {
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind, only_terminal: bool) -> Self {
        let tiling = if only_terminal {
            Tiling::Scalar(input.extent())
        } else {
            todo!("functions on partial aggregates")
        };
        Self {
            input,
            base: OperatorBase::new(tiling),
            kind,
            only_terminal,
        }
    }
}

impl TileOperator for ExtractAggregate {
    impl_operator_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(ExtractAggregateProducer {
            base: ProducerBase::new(ExtractAggregateProducer::alloc_id(), self.tiling()),
            input: self
                .input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler),
            kind: self.kind,
            only_terminal: self.only_terminal,
        })
    }
}

struct ExtractAggregateProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    kind: AggregateKind,
    only_terminal: bool,
}

impl TileProducer for ExtractAggregateProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_result = self.input.get(self.input.tiling().universal_guard());
        let Tile::Aggregation {
            kind: _,
            accumulator,
            terminal,
        } = input_result
        else {
            panic!(
                "ExtractAggregate expected Aggregation tiling, got {:?}",
                self.input.tiling()
            );
        };
        // An empty accumulator is `⊥`, not a finished aggregation of nothing: the
        // input has either not produced yet, or has released what it produced and
        // gone quiet. Either way there is no terminal flag to read.
        if terminal.is_empty() {
            return self.tiling().empty_tile();
        }
        if self.only_terminal {
            if terminal.index_at(0).as_bool() {
                Tile::Scalar(self.kind.extract(accumulator))
            } else {
                self.tiling().empty_tile()
            }
        } else {
            todo!()
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

/// Extracts terminal per-key aggregation results from a
/// `SealedFunction(D, Aggregation)`, producing a `SealedFunction(D, Scalar)`.
///
/// For each domain element, the aggregation value is extracted and emitted only
/// when that element's terminal flag is `true`.  Non-terminal elements are
/// filtered out of the output domain.
pub struct MapExtractAggregate {
    /// The `SealedFunction(D, Aggregation)`-typed input.
    input: Box<dyn TileOperator>,
    /// The aggregation operation used to extract final values from accumulators.
    kind: AggregateKind,
    /// Identity and the output tiling:
    /// `SealedFunction { domain: input.domain, codomain: Scalar(output_extent) }`.
    base: OperatorBase,
}

impl MapExtractAggregate {
    /// Create a new `MapExtractAggregate` operator.
    ///
    /// `input` must have a `SealedFunction` tiling whose codomain is
    /// `Aggregation { accumulator: A }`.  The output tiling is
    /// `SealedFunction { domain: input.domain, codomain: Scalar(A) }`.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        let tiling = match input.tiling() {
            Tiling::SealedFunction { domain, codomain } => match codomain.as_ref() {
                Tiling::Aggregation { accumulator, .. } => Tiling::SealedFunction {
                    domain: domain.clone(),
                    codomain: Box::new(Tiling::Scalar(accumulator.clone())),
                },
                t => panic!(
                    "MapExtractAggregate expected SealedFunction(Aggregation) codomain, got {t:?}"
                ),
            },
            t => panic!("MapExtractAggregate expected SealedFunction input, got {t:?}"),
        };
        Self {
            input,
            kind,
            base: OperatorBase::new(tiling),
        }
    }
}

impl TileOperator for MapExtractAggregate {
    impl_operator_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let input_producer =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(MapExtractAggregateProducer {
            base: ProducerBase::new(MapExtractAggregateProducer::alloc_id(), &self.base.tiling),
            input: input_producer,
            kind: self.kind,
        })
    }
}

/// Producer for [`MapExtractAggregate`].
struct MapExtractAggregateProducer {
    base: ProducerBase,
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation used to extract final values.
    kind: AggregateKind,
}

impl TileProducer for MapExtractAggregateProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_result = self.input.get(self.input.tiling().universal_guard());
        let Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate,
            ..
        } = input_result
        else {
            panic!("MapExtractAggregate expected SealedFunction tile")
        };
        let Tile::Aggregation {
            accumulator,
            terminal,
            ..
        } = *codomain
        else {
            panic!("MapExtractAggregate expected SealedFunction(Aggregation) codomain")
        };
        // Emit only the domain elements whose per-key aggregation is terminal.
        let mask = terminal
            .as_bitvec()
            .unwrap_or_else(|| panic!("Expected bools"));
        let mut output = Tile::SealedFunction {
            domain,
            codomain: Box::new(Tile::Scalar(self.kind.extract(accumulator))),
            domain_predicate,
            deleted: BitSet::new(),
        };
        output.retain(mask);
        output
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        self.input.release(match obsolete_guard {
            g if g.is_universal() => self.input.tiling().universal_guard(),
            g if g.is_empty() => self.input.tiling().empty_guard(),
            TileGuard::Function(FunctionGuard::Domain(p)) => {
                TileGuard::Function(FunctionGuard::Domain(p))
            }
            g => todo!("MapExtractAggregate cannot honor the release guard {g:?}"),
        });
    }
}

/// Performs a per-key aggregation over a [`Tile::CurriedFunction`], producing a
/// `SealedFunction` that maps each domain key to an in-progress aggregation.
///
/// For a lookup `D → [C]` and an [`AggregateKind`], `MapAggregate` produces a
/// sealed function `D → Aggregation(C)`.  New data from partial lookups is
/// merged into per-key accumulators on each `get`; each key's aggregation
/// becomes terminal when the input lookup's `domain_predicate` is `True`.
pub struct MapAggregate {
    /// The lookup-function input to aggregate per key.
    input: Box<dyn TileOperator>,
    /// The aggregation operation (Sum, Max, …).
    kind: AggregateKind,
    /// Identity and the output tiling:
    /// `SealedFunction { domain: input.domain, codomain: Aggregation { accumulator: output_extent } }`.
    base: OperatorBase,
}

impl MapAggregate {
    /// Create a new `MapAggregate` operator.
    ///
    /// `input` must have a `CurriedFunction` tiling; `kind` must support the
    /// lookup's codomain element type.  The output tiling is
    /// `SealedFunction { domain: input.domain, codomain: Aggregation { accumulator: output_extent } }`.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        let (domain, input_codomain) = match input.tiling() {
            Tiling::CurriedFunction {
                domain1, codomain, ..
            } => (domain1.clone(), codomain.clone()),
            t => panic!("MapAggregate requires CurriedFunction input, got {t:?}"),
        };
        let output_extent = kind.output_extent(&input_codomain).unwrap_or_else(|| {
            panic!("Cannot apply {kind:?} to codomain extent {input_codomain:?}")
        });
        let tiling = Tiling::SealedFunction {
            domain,
            codomain: Box::new(Tiling::Aggregation {
                kind,
                accumulator: output_extent,
            }),
        };
        Self {
            input,
            kind,
            base: OperatorBase::new(tiling),
        }
    }
}

impl TileOperator for MapAggregate {
    impl_operator_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let input_producer =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(MapAggregateProducer {
            base: ProducerBase::new(MapAggregateProducer::alloc_id(), &self.base.tiling),
            input: input_producer,
            kind: self.kind,
            accumulators: HashMap::new(),
        })
    }
}

/// Producer for [`MapAggregate`].
struct MapAggregateProducer {
    base: ProducerBase,
    /// The subscribed lookup-function producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation.
    kind: AggregateKind,
    /// Running per-key accumulators, grown as new keys arrive across `get` calls.
    accumulators: HashMap<Value, ColumnValue>,
}

impl TileProducer for MapAggregateProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let mut input_tile = self.input.get(self.input.tiling().universal_guard());
        trace!("{} received {input_tile:?}", self.name());
        let upstream_guard = input_tile.to_guard();
        input_tile.compact();
        let Tile::CurriedFunction {
            domain1,
            offsets,
            domain2: _,
            codomain,
            domain_predicate,
            ..
        } = input_tile
        else {
            panic!("MapAggregate requires a CurriedFunction tile")
        };
        // output_extent is the accumulator extent from the Aggregation codomain tiling.
        let output_extent = self.tiling().codomain().unwrap().extent();
        let domain_extent = self.tiling().domain_extent().unwrap();
        // Merge newly arrived values into per-key accumulators.
        let kind = &self.kind;
        let accumulators = &mut self.accumulators;
        let n = domain1.len();
        for i in 0..n {
            let key = domain1.index_at(i);
            let start = offsets.index_at(i).as_uint();
            let end = if i + 1 < n {
                offsets.index_at(i + 1).as_uint()
            } else {
                codomain.len()
            };
            let acc = accumulators
                .entry(key)
                .or_insert_with(|| kind.initial_accumulator(&output_extent));
            kind.accumulate(acc, &codomain, start, end);
        }

        // Release received values
        self.input.release(upstream_guard);

        // Build the output tile from all known per-key accumulators.
        // TODO apply the domain predicate to each domain value.
        let is_terminal = domain_predicate.as_bool().unwrap_or(false);
        let n = self.accumulators.len();
        let (domain_values, accumulator_values): (Vec<Value>, Vec<Value>) = self
            .accumulators
            .iter()
            .map(|(key, acc)| (key.clone(), acc.as_single().unwrap()))
            .unzip();
        Tile::SealedFunction {
            domain: ColumnValue::from_values(domain_values, &domain_extent),
            codomain: Box::new(Tile::Aggregation {
                kind: self.kind,
                accumulator: ColumnValue::from_values(accumulator_values, &output_extent),
                terminal: ColumnValue::Bools(BitVec::from_elem(n, is_terminal)),
            }),
            domain_predicate,
            deleted: BitSet::new(),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // The output domain *is* this producer's accumulator key set, and the
        // input's `domain1` is that same key set, so a domain release names
        // exactly which accumulators to drop and forwards verbatim. Keeping a
        // released key would re-emit it on the next pull, since `get_impl` builds
        // its output from every accumulator it holds.
        match obsolete_guard {
            g if g.is_empty() => {}
            g if g.is_universal() => {
                self.accumulators.clear();
                self.input.release(self.input.tiling().universal_guard());
            }
            TileGuard::Function(FunctionGuard::Domain(pred)) => {
                self.accumulators.retain(|key, _| !pred.contains(key));
                self.input
                    .release(TileGuard::Function(FunctionGuard::Domain(pred)));
            }
            g => todo!("Unimplemented guard in MapAggregateProducer: {g:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{QuietSpy, ReleaseSpy};
    use crate::interpreter::{BaseType, Extent, Predicate, Tile};
    fn int_sealed(domain: Vec<usize>, values: Vec<i64>) -> Tile {
        Tile::SealedFunction {
            domain: ColumnValue::from_uints(domain),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(values))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        }
    }

    /// An `Aggregate`'s accumulator *is* its whole output, so once the consumer
    /// has released it there is nothing left to hand back. Re-emitting it would
    /// return released data, which a caching consumer merges into itself twice.
    #[test]
    fn aggregate_goes_quiet_after_a_universal_release() {
        let in_tiling = Tiling::SealedFunction {
            domain: Extent::uint_range(2),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let (spy, _released) = ReleaseSpy::new(int_sealed(vec![0, 1], vec![10, 20]), in_tiling);
        let tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Extent::Base(BaseType::Int),
        };
        let mut producer = AggregateProducer::new(tiling.clone(), Box::new(spy));

        let first = producer.get(tiling.universal_guard());
        let Tile::Aggregation { accumulator, .. } = &first else {
            panic!("expected an Aggregation tile, got {first:?}");
        };
        assert_eq!(accumulator.as_single().unwrap(), Value::Int(30));

        producer.release(tiling.universal_guard());
        assert_eq!(
            producer.get(tiling.universal_guard()),
            tiling.empty_tile(),
            "a released accumulator must not be handed back"
        );
    }

    /// The release also has to reach the input in full. `get_impl` only releases
    /// what was actually delivered, so an aggregate finishing before its source
    /// ran dry would otherwise strand the remainder upstream.
    #[test]
    fn aggregate_releases_its_input_universally() {
        let in_tiling = Tiling::SealedFunction {
            domain: Extent::uint_range(2),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let (spy, released) = ReleaseSpy::new(int_sealed(vec![0], vec![10]), in_tiling.clone());
        let tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Extent::Base(BaseType::Int),
        };
        let mut producer = AggregateProducer::new(tiling.clone(), Box::new(spy));

        producer.release(tiling.universal_guard());
        assert!(
            released.borrow().iter().any(TileGuard::is_universal),
            "expected a universal release to reach the input, got {:?}",
            released.borrow()
        );
        let _ = in_tiling;
    }

    /// A **per-key** release must drop exactly those accumulators and forward the
    /// same domain predicate upstream. `get_impl` rebuilds its output from every
    /// accumulator it holds, so a kept-but-released key is re-emitted; and the
    /// input's `domain1` is the same key set, so nothing else would reclaim it.
    #[test]
    fn map_aggregate_drops_and_forwards_a_per_key_release() {
        let key_extent = Extent::Base(BaseType::Int);
        let in_tiling = Tiling::CurriedFunction {
            domain1: key_extent.clone(),
            domain2: Extent::Base(BaseType::Int),
            codomain: Extent::Base(BaseType::Int),
        };
        // Keys 1 and 2, each with two values: 1 -> [10, 20], 2 -> [30, 40].
        let tile = Tile::curried_function(
            ColumnValue::Ints(vec![1, 2]),
            ColumnValue::from_uints(vec![0, 2]),
            ColumnValue::Ints(vec![0, 1, 0, 1]),
            ColumnValue::Ints(vec![10, 20, 30, 40]),
            Predicate::True,
            BitSet::new(),
        );
        let (spy, released) = QuietSpy::new(tile, in_tiling.clone());
        let out_tiling = Tiling::SealedFunction {
            domain: key_extent,
            codomain: Box::new(Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Extent::Base(BaseType::Int),
            }),
        };
        let mut producer = MapAggregateProducer {
            base: ProducerBase::new(MapAggregateProducer::alloc_id(), &out_tiling),
            input: Box::new(spy),
            kind: AggregateKind::Sum,
            accumulators: HashMap::new(),
        };

        let first = producer.get(out_tiling.universal_guard());
        let Tile::SealedFunction { domain, .. } = &first else {
            panic!("expected a SealedFunction, got {first:?}");
        };
        assert_eq!(domain.len(), 2, "both keys aggregate on the first pull");

        // Release key 1 only.
        let key_one = TileGuard::Function(FunctionGuard::Domain(Predicate::Intervals(
            intervalsets::IntervalSet::from(intervalsets::Interval::closed(
                Value::Int(1),
                Value::Int(1),
            )),
        )));
        producer.release(key_one.clone());

        assert!(
            released.borrow().contains(&key_one),
            "the per-key release must reach the input, got {:?}",
            released.borrow()
        );
        let second = producer.get(out_tiling.universal_guard());
        let Tile::SealedFunction { domain, .. } = &second else {
            panic!("expected a SealedFunction, got {second:?}");
        };
        assert_eq!(
            domain.index_at(0),
            Value::Int(2),
            "only the unreleased key may be emitted, got {second:?}"
        );
        assert_eq!(domain.len(), 1, "the released key must be gone: {second:?}");
    }
}
