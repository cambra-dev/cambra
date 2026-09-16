use bit_set::BitSet;
use bit_vec::BitVec;
use log::trace;
use std::cmp::Ordering;
use std::collections::HashMap;

use super::*;
use crate::interpreter::nest_levels;
use crate::interpreter::operator_graph::value;
use crate::{
    ccl::AggregateKind,
    interpreter::{ColumnValue, Consumer, Scheduler, Value},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// Reduces a `Function` input to a single scalar via an aggregation operation.
///
/// On each `get`, reads all codomain values from the input and folds them into a
/// running `Tile::Aggregation` accumulator. The result becomes terminal once the
/// input's `domain_predicate` is `True` (all elements seen).
pub struct Aggregate {
    /// The `Function`-typed input whose codomain elements are aggregated.
    input: Box<dyn TileOperator>,
    /// Output tiling — always `Tiling::Aggregation { accumulator: <output extent> }`.
    base: OperatorBase,
}

impl Aggregate {
    /// Construct an `Aggregate` operator.
    ///
    /// Panics if `input` does not have a `Function` tiling, or if `kind`
    /// does not support the codomain element type.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        let err = || panic!("Cannot apply {kind:?} to non-function {:?}", input.tiling());
        let values = input.tiling().codomain().unwrap_or_else(err);
        let tiling = Tiling::Aggregation {
            kind,
            accumulator: Box::new(kind.output_tiling(&values).unwrap_or_else(err)),
        };
        Self {
            base: OperatorBase::new(tiling),
            input,
        }
    }
}

impl TileOperator for Aggregate {
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
        let input_producer =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(AggregateProducer::new(
            self.tiling().clone(),
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
                accumulator: acc_tiling,
            } => (
                *kind,
                Tile::Aggregation {
                    kind: *kind,
                    accumulator: Box::new(kind.initial_accumulator(acc_tiling)),
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
        let Tile::Function {
            values: codomain, ..
        } = input_result
        else {
            panic!("Aggregate expected a collection, got {input_result:?}");
        };
        self.input.release(upstream_guard);
        let values = *codomain;

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
        self.kind.accumulate(accumulator, &values, 0, values.rows());
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
            base: OperatorBase::new(tiling),
            input,
            kind,
            only_terminal,
        }
    }
}

impl TileOperator for ExtractAggregate {
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
                self.kind.extract(*accumulator)
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

/// Extracts terminal aggregation results, turning an `Aggregation` codomain into a `Scalar`
/// one and leaving the domain structure alone.
///
/// Both function shapes reach this, because [`MapAggregate`] leaves whichever its input's
/// depth calls for: `Function(D, Aggregation)` becomes `Function(D, Scalar)`,
/// and `Function(D₀ … Dₙ₋₁, Aggregation)` becomes the same levels over a `Scalar`.
/// An element is emitted only where its terminal flag is set; the rest are filtered out,
/// which for a nested tile also drops every key left holding nothing.
pub struct MapExtractAggregate {
    /// The `Function(D, Aggregation)`-typed input.
    input: Box<dyn TileOperator>,
    /// The aggregation operation used to extract final values from accumulators.
    kind: AggregateKind,
    /// Output tiling: `Function { domain: input.domain, codomain: Scalar(output_extent) }`.
    base: OperatorBase,
}

impl MapExtractAggregate {
    /// Create a new `MapExtractAggregate` operator.
    ///
    /// `input` must have a `Function` tiling whose codomain is
    /// `Aggregation { accumulator: A }`.  The output tiling is
    /// `Function { domain: input.domain, codomain: Scalar(A) }`.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        let accumulator_of = |codomain: &Tiling| match codomain {
            Tiling::Aggregation { accumulator, .. } => (**accumulator).clone(),
            t => panic!("MapExtractAggregate expected an Aggregation codomain, got {t:?}"),
        };
        let tiling = match input.tiling() {
            Tiling::Function { keys, values } => Tiling::Function {
                keys: keys.clone(),
                values: Box::new(accumulator_of(values)),
            },
            t => panic!("MapExtractAggregate expected a collection input, got {t:?}"),
        };
        Self {
            base: OperatorBase::new(tiling),
            input,
            kind,
        }
    }
}

impl TileOperator for MapExtractAggregate {
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
        let input_producer =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(MapExtractAggregateProducer {
            base: ProducerBase::new(MapExtractAggregateProducer::alloc_id(), self.tiling()),
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
        // The shape passes through; only the codomain changes and the non-terminal
        // elements go. Rebuilding with the same levels is what keeps a deeper fold's
        // grouping intact for the fold above it.
        let (rebuild, codomain): (Box<dyn FnOnce(Tile) -> Tile>, Box<Tile>) = match input_result {
            Tile::Function {
                row_starts,
                keys,
                values: codomain,
                domain_predicate,
                ..
            } => (
                Box::new(move |extracted| {
                    Tile::grouped(
                        row_starts,
                        keys,
                        Box::new(extracted),
                        domain_predicate,
                        BitSet::new(),
                    )
                }),
                codomain,
            ),
            other => panic!("MapExtractAggregate expected a function tile, got {other:?}"),
        };
        let Tile::Aggregation {
            accumulator,
            terminal,
            ..
        } = *codomain
        else {
            panic!("MapExtractAggregate expected an Aggregation codomain")
        };
        // Emit only the elements whose aggregation is terminal.
        let mask = terminal
            .as_bitvec()
            .unwrap_or_else(|| panic!("Expected bools"));
        let mut output = rebuild(self.kind.extract(*accumulator));
        // One bool per accumulator, so the mask is over the collection's keys.
        output.retain_keys(mask);
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

/// Order two element paths lexicographically.
///
/// [`Value`] is `PartialOrd` and not `Ord`, so incomparable components compare equal here:
/// the order only has to group a parent's children together, which any total order does.
fn compare_paths(a: &[Value], b: &[Value]) -> Ordering {
    for (x, y) in a.iter().zip(b) {
        match x.partial_cmp(y) {
            Some(Ordering::Equal) | None => continue,
            Some(other) => return other,
        }
    }
    a.len().cmp(&b.len())
}

/// Rebuild a function of `extents.len()` domain levels from the sorted paths of its
/// innermost elements, with `codomain` already vectorized over those elements.
///
/// Each level nests inside the one above it, so a new key at a level starts its run of
/// children where the level below has reached. The paths must arrive sorted: a parent's
/// children are contiguous only then.
fn build_curried_from_paths(
    paths: &[&[Value]],
    extents: &[Extent],
    codomain: Tile,
    domain_predicate: Predicate,
) -> Tile {
    let depth = extents.len();
    let mut columns: Vec<Vec<Value>> = vec![Vec::new(); depth];
    let mut starts: Vec<Vec<usize>> = vec![Vec::new(); depth.saturating_sub(1)];
    let mut last: Vec<Option<Vec<Value>>> = vec![None; depth];
    for path in paths {
        for level in 0..depth {
            let prefix = &path[..=level];
            if last[level].as_deref() == Some(prefix) {
                continue;
            }
            if level + 1 < depth {
                starts[level].push(columns[level + 1].len());
            }
            columns[level].push(path[level].clone());
            last[level] = Some(prefix.to_vec());
            // A new element invalidates every prefix below it, so the next path opens fresh
            // elements there instead of extending the previous parent's last child.
            for deeper in last.iter_mut().skip(level + 1) {
                *deeper = None;
            }
        }
    }
    let mut domains: Vec<ColumnValue> = columns
        .into_iter()
        .zip(extents)
        .map(|(values, extent)| ColumnValue::from_values(values, extent))
        .collect();
    if depth == 1 {
        return Tile::function(
            domains.pop().unwrap_or_else(|| unreachable!()),
            Box::new(codomain),
            domain_predicate,
            BitSet::new(),
        );
    }
    nest_levels(
        domains,
        starts.into_iter().map(ColumnValue::UInts).collect(),
        Box::new(codomain),
        domain_predicate,
    )
}

/// Collapses the **innermost** collection of a nested tile into an aggregation, leaving the
/// levels above it intact.
///
/// For `K₀ ⤇ … ⤇ Kₙ₋₁ ⤇ C` and an [`AggregateKind`] it produces `K₀ ⤇ … ⤇ Kₙ₋₂ ⤇
/// Aggregation(C)`. Collapsing one level per operator is what lets nested aggregation nest:
/// each `sum` in `sum([sum([…]) for …])` is one of these.
///
/// Accumulators are keyed by the **path** of the element being folded into, not by its own
/// value: a key repeats across its siblings' groups, so below the outermost level a value
/// does not identify an element. New data merges on each `get`; an element's aggregation
/// becomes terminal where the input's `domain_predicate` names its outermost ancestor.
pub struct MapAggregate {
    /// The lookup-function input to aggregate per key.
    input: Box<dyn TileOperator>,
    /// The aggregation operation (Sum, Max, …).
    kind: AggregateKind,
    /// Output tiling: `Function { domain: input.domain, codomain: Aggregation { accumulator: output_extent } }`.
    base: OperatorBase,
}

impl MapAggregate {
    /// Create a new `MapAggregate` operator.
    ///
    /// `input` must have a `Function` tiling; `kind` must support the
    /// lookup's codomain element type.  The output tiling is
    /// `Function { domain: input.domain, codomain: Aggregation { accumulator: output_extent } }`.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        // A collection whose values are not themselves a collection has no level above the
        // one being folded, which is `Aggregate`'s shape rather than this one's.
        let Tiling::Function { values, .. } = input.tiling() else {
            panic!(
                "MapAggregate requires a collection input, got {}",
                input.tiling()
            )
        };
        assert!(
            matches!(values.as_ref(), Tiling::Function { .. }),
            "MapAggregate folds a collection of collections, got {}",
            input.tiling()
        );
        let tiling = fold_innermost(input.tiling(), kind);
        Self {
            base: OperatorBase::new(tiling),
            input,
            kind,
        }
    }
}

/// Replace `tiling`'s innermost collection with the aggregation that folds it.
fn fold_innermost(tiling: &Tiling, kind: AggregateKind) -> Tiling {
    let Tiling::Function { keys, values } = tiling else {
        panic!("fold_innermost walks a chain of collections, got {tiling}")
    };
    match values.as_ref() {
        Tiling::Function { .. } => Tiling::Function {
            keys: keys.clone(),
            values: Box::new(fold_innermost(values, kind)),
        },
        inner => {
            let accumulator = kind
                .output_tiling(inner)
                .unwrap_or_else(|| panic!("Cannot apply {kind:?} to values {inner}"));
            Tiling::Aggregation {
                kind,
                accumulator: Box::new(accumulator),
            }
        }
    }
}

/// A folded tiling's key extent per level, outermost first, and the accumulator extent the
/// chain ends in.
fn folded_shape(tiling: &Tiling) -> (Vec<Extent>, Tiling) {
    let mut extents = Vec::new();
    let mut node = tiling;
    loop {
        match node {
            Tiling::Function { keys, values } => {
                extents.push(keys.clone());
                node = values;
            }
            Tiling::Aggregation { accumulator, .. } => return (extents, (**accumulator).clone()),
            other => panic!("MapAggregate leaves collections around an aggregation, got {other}"),
        }
    }
}

impl TileOperator for MapAggregate {
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
        let input_producer =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(MapAggregateProducer {
            base: ProducerBase::new(MapAggregateProducer::alloc_id(), self.tiling()),
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
    accumulators: HashMap<Vec<Value>, Tile>,
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
        let Tile::Function {
            domain_predicate, ..
        } = &input_tile
        else {
            panic!("MapAggregate requires a collection tile, got {input_tile:?}")
        };
        let domain_predicate = domain_predicate.clone();

        // Descend to the collection being folded, extending the key path at every level.
        // Its rows are the elements the groups fold into, so `parent_paths` names them.
        let mut node = &input_tile;
        let mut parent_paths = vec![Vec::new()];
        let folded = loop {
            parent_paths = node.key_paths(&parent_paths);
            let Tile::Function { values, .. } = node else {
                unreachable!("the loop only descends into a collection")
            };
            match values.as_ref() {
                Tile::Function { values: inner, .. } if inner.is_function() => node = values,
                Tile::Function { .. } => break values.as_ref(),
                other => panic!("MapAggregate folds a collection of collections, got {other:?}"),
            }
        };
        let Tile::Function { values, .. } = folded else {
            unreachable!("the loop breaks on a collection")
        };
        let values = (**values).clone();
        let (extents, output_tiling) = folded_shape(self.tiling());

        // Fold each group into its row's accumulator. A group is a contiguous run of the
        // folded collection's values, so the fold stays vectorized.
        let kind = &self.kind;
        let accumulators = &mut self.accumulators;
        for (row, path) in parent_paths.iter().enumerate() {
            let (start, end) = folded.row_run(row);
            let acc = accumulators
                .entry(path.clone())
                .or_insert_with(|| kind.initial_accumulator(&output_tiling));
            kind.accumulate(acc, &values, start, end);
        }

        // Release received values
        self.input.release(upstream_guard);

        // Build the output from all known accumulators.
        //
        // **Terminal per element, which is what the predicate says.** A `domain_predicate`
        // names the region of the outermost domain that will see no new elements, each key
        // together with every level below it — so an element
        // whose outermost ancestor lies inside it has a complete group and its accumulator
        // is the answer, whatever the rest of the domain is still doing. Reading the
        // predicate as one bool answers "not yet" for every element whenever any part of the
        // domain is open, which is never right for a live source: a collection held per row
        // is complete as soon as its row arrives, and an aggregate over one would otherwise
        // never settle.
        let mut entries: Vec<(Vec<Value>, Tile)> = self
            .accumulators
            .iter()
            .map(|(path, acc)| (path.clone(), acc.clone()))
            .collect();
        // Sorted so the outermost column stays ordered and a parent's children sit
        // contiguously, which is what rebuilding the offsets assumes.
        entries.sort_by(|a, b| compare_paths(&a.0, &b.0));

        let terminal: BitVec = entries
            .iter()
            .map(|(path, _)| domain_predicate.contains(&path[0]))
            .collect();
        // One accumulator per key, run together in path order: a scalar fold's rows are a
        // column, and `Sole`'s are the elements' own levels.
        let mut accumulator = output_tiling.empty_at_no_rows();
        for (_, acc) in &entries {
            accumulator.merge_rows(acc.clone());
        }
        let aggregation = Tile::Aggregation {
            kind: self.kind,
            accumulator: Box::new(accumulator),
            terminal: ColumnValue::Bools(terminal),
        };
        let paths: Vec<&[Value]> = entries.iter().map(|(path, _)| path.as_slice()).collect();
        build_curried_from_paths(&paths, &extents, aggregation, domain_predicate)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // The output domain *is* this producer's accumulator key set, and the
        // input's own keys are that same key set, so a domain release names
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
                // The guard names the outermost domain, which is the head of every
                // accumulator's path.
                self.accumulators.retain(|path, _| !pred.contains(&path[0]));
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
        Tile::function(
            ColumnValue::from_uints(domain),
            Box::new(Tile::Scalar(ColumnValue::Ints(values))),
            Predicate::True,
            BitSet::new(),
        )
    }

    /// An `Aggregate`'s accumulator *is* its whole output, so once the consumer
    /// has released it there is nothing left to hand back. Re-emitting it would
    /// return released data, which a caching consumer merges into itself twice.
    #[test]
    fn aggregate_goes_quiet_after_a_universal_release() {
        let in_tiling = Tiling::function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (spy, _released) = ReleaseSpy::new(int_sealed(vec![0, 1], vec![10, 20]), in_tiling);
        let tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let mut producer = AggregateProducer::new(tiling.clone(), Box::new(spy));

        let first = producer.get(tiling.universal_guard());
        let Tile::Aggregation { accumulator, .. } = &first else {
            panic!("expected an Aggregation tile, got {first:?}");
        };
        assert_eq!(
            *accumulator,
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![30])))
        );

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
        let in_tiling = Tiling::function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (spy, released) = ReleaseSpy::new(int_sealed(vec![0], vec![10]), in_tiling.clone());
        let tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
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

    /// A **per-key** release drops exactly those accumulators. `get_impl` rebuilds its
    /// output from every accumulator it holds, so a kept-but-released key is re-emitted.
    ///
    /// The input here declares itself final, so the first pull already releases it whole
    /// ([`Tile::to_guard`]) and every later guard is covered by that one. Forwarding is
    /// therefore not observable on this fixture, and
    /// [`map_aggregate_forwards_a_per_key_release_to_an_open_input`] pins it on one where
    /// it is.
    #[test]
    fn map_aggregate_drops_a_per_key_release() {
        let key_extent = Extent::Base(BaseType::Int);
        let in_tiling = Tiling::function(
            key_extent.clone(),
            Tiling::function(
                Extent::Base(BaseType::Int),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        // Keys 1 and 2, each with two values: 1 -> [10, 20], 2 -> [30, 40].
        let tile = Tile::function(
            ColumnValue::Ints(vec![1, 2]),
            Box::new(Tile::grouped(
                ColumnValue::from_uints(vec![0, 2]),
                ColumnValue::Ints(vec![0, 1, 0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30, 40]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let (spy, released) = QuietSpy::new(tile, in_tiling.clone());
        let out_tiling = Tiling::function(
            key_extent,
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            },
        );
        let mut producer = MapAggregateProducer {
            base: ProducerBase::new(MapAggregateProducer::alloc_id(), &out_tiling),
            input: Box::new(spy),
            kind: AggregateKind::Sum,
            accumulators: HashMap::new(),
        };

        let first = producer.get(out_tiling.universal_guard());
        let Tile::Function { keys: domain, .. } = &first else {
            panic!("expected a collection, got {first:?}");
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

        // Key 1 is released at the input, by the universal release the first pull already
        // issued. Which guard covered it is the sibling test's subject, not this one's.
        assert!(
            released
                .borrow()
                .iter()
                .any(|g| g.is_universal() || *g == key_one),
            "the released key must be covered at the input, got {:?}",
            released.borrow()
        );
        let second = producer.get(out_tiling.universal_guard());
        let Tile::Function { keys: domain, .. } = &second else {
            panic!("expected a collection, got {second:?}");
        };
        assert_eq!(
            domain.index_at(0),
            Value::Int(2),
            "only the unreleased key may be emitted, got {second:?}"
        );
        assert_eq!(domain.len(), 1, "the released key must be gone: {second:?}");
    }

    /// A per-key release **reaches the input**, which the case above cannot show.
    ///
    /// The input's `domain_predicate` calls both groups whole without being `True`, so
    /// [`Tile::to_guard`] answers a bounded `Domain` rather than the universal guard that
    /// covers every later release. The only guard naming key 1 on its own is then the one
    /// `release_impl` forwards. The input's own keys are this producer's accumulator key
    /// set, so nothing else would reclaim the key.
    #[test]
    fn map_aggregate_forwards_a_per_key_release_to_an_open_input() {
        let key_extent = Extent::Base(BaseType::Int);
        let in_tiling = Tiling::function(
            key_extent.clone(),
            Tiling::function(
                Extent::Base(BaseType::Int),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        let tile = Tile::function(
            ColumnValue::Ints(vec![1, 2]),
            Box::new(Tile::grouped(
                ColumnValue::from_uints(vec![0, 2]),
                ColumnValue::Ints(vec![0, 1, 0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30, 40]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::LessThanEq(Value::Int(2)),
            BitSet::new(),
        );
        let (spy, released) = QuietSpy::new(tile, in_tiling.clone());
        let out_tiling = Tiling::function(
            key_extent,
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            },
        );
        let mut producer = MapAggregateProducer {
            base: ProducerBase::new(MapAggregateProducer::alloc_id(), &out_tiling),
            input: Box::new(spy),
            kind: AggregateKind::Sum,
            accumulators: HashMap::new(),
        };
        producer.get(out_tiling.universal_guard());
        assert!(
            !released.borrow().iter().any(TileGuard::is_universal),
            "a bounded predicate is not released whole, got {:?}",
            released.borrow()
        );

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
    }
}
