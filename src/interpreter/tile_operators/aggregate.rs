use bit_set::BitSet;
use log::trace;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use super::*;
use crate::interpreter::nest_levels;
use crate::interpreter::operator_graph::value;
use crate::{
    ccl::AggregateKind,
    interpreter::{ColumnValue, Consumer, Projection, Scheduler, Value},
};

/// Folds a collection's values into one [`Tile::Aggregation`].
///
/// Accumulation, completion, and release follow `src/interpreter/design-operators.md`,
/// "Aggregation and extraction". [`ExtractAggregate`] reads the terminal result.
pub struct Aggregate {
    /// The `DataFunction`-typed input whose codomain elements are aggregated.
    input: Box<dyn TileOperator>,
    base: OperatorBase,
}

impl Aggregate {
    /// Construct an `Aggregate` operator.
    ///
    /// Panics if `input` does not have a `DataFunction` tiling, or if `kind`
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
            ProducerBase::new(
                AggregateProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
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
    /// Suppresses subsequent emissions after universal release.
    released: bool,
}

impl AggregateProducer {
    /// Initialize through [`AggregateKind::initial_accumulator`]. An extremum without an identity
    /// starts without a value and waits for its first element.
    fn new(base: ProducerBase, input: Box<dyn TileProducer>) -> Self {
        let (kind, accumulator) = match &base.tiling {
            Tiling::Aggregation {
                kind,
                accumulator: acc_tiling,
            } => (
                *kind,
                Tile::Aggregation {
                    kind: *kind,
                    accumulator: Box::new(kind.initial_accumulator(acc_tiling)),
                    terminal: ColumnValue::Bools(vec![false; 1]),
                },
            ),
            other => panic!("AggregateProducer created with non-Aggregation tiling: {other:?}"),
        };
        Self {
            base,
            input,
            kind,
            accumulator,
            released: false,
        }
    }
}

impl TileProducer for AggregateProducer {
    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::holding(self.accumulator.cell_count())
    }

    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    /// An accumulator has no keys to project, so the projection is all of it or none. The
    /// input is read whole whatever the consumer asks.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        match projection_guard.projection(&self.name()) {
            Projection::Everything => {}
            Projection::Nothing => return self.tiling().empty_tile(),
            Projection::Keys { .. } => panic!(
                "{} is one accumulator, which has no keys to project: {projection_guard:?}",
                self.name()
            ),
        }
        if self.released {
            return self.tiling().empty_tile();
        }
        let i_tiling = self.input.tiling().clone();
        let mut input_result = self.input.get(i_tiling.universal_guard());
        let upstream_guard = input_result.to_guard();
        input_result.compact();
        let Tile::DataFunction { codomain, .. } = input_result else {
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
        terminal[0] = is_terminal;
        // No terminal flag can be emitted before the accumulator has a value.
        if self.kind.awaits_first_element(accumulator) {
            if is_terminal {
                self.kind.no_extreme_of_nothing();
            }
            return self.tiling().empty_tile();
        }
        self.accumulator.clone()
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Universal release also covers input not yet delivered. Per-delivery releases in
        // `get_impl` cover only the received tiles.
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.released = true;
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

/// Extracts a terminal result from an aggregation. Partial-result extraction is unsupported.
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
            base: ProducerBase::new(
                ExtractAggregateProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
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

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    /// One extracted value has no keys to project: the projection is all of it or none.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        match projection_guard.projection(&self.name()) {
            Projection::Everything => {}
            Projection::Nothing => return self.tiling().empty_tile(),
            Projection::Keys { .. } => panic!(
                "{} extracts one value, which has no keys to project: {projection_guard:?}",
                self.name()
            ),
        }
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
        // An empty tile has no terminal flag; it is not the completed fold of an empty input.
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

/// Extracts terminal results beneath a chain of collection levels.
///
/// Preserves the enclosing levels and removes innermost keys whose aggregation is not terminal.
/// See `src/interpreter/design-operators.md`, "Aggregation and extraction".
pub struct MapExtractAggregate {
    input: Box<dyn TileOperator>,
    /// The aggregation operation used to extract final values from accumulators.
    kind: AggregateKind,
    base: OperatorBase,
}

impl MapExtractAggregate {
    /// Create a new `MapExtractAggregate` operator.
    ///
    /// `input` must be a collection chain ending in `Aggregation { accumulator: A }`, at
    /// whatever depth. The output replaces that aggregation with what it extracts to.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        assert!(
            input.tiling().is_data_function(),
            "MapExtractAggregate expected a collection input, got {}",
            input.tiling()
        );
        let tiling = extract_innermost(input.tiling());
        Self {
            base: OperatorBase::new(tiling),
            input,
            kind,
        }
    }
}

/// Replace the aggregation a collection chain ends in with the value it extracts to.
fn extract_innermost(tiling: &Tiling) -> Tiling {
    match tiling {
        Tiling::DataFunction { domain, codomain } => Tiling::DataFunction {
            domain: domain.clone(),
            codomain: Box::new(extract_innermost(codomain)),
        },
        Tiling::Aggregation { accumulator, .. } => (**accumulator).clone(),
        t => panic!("MapExtractAggregate expected an aggregation under the keys, got {t}"),
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
            base: ProducerBase::new(
                MapExtractAggregateProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
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

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let mut output = self.input.get(self.input.tiling().universal_guard());
        // Every level passes through; only what sits under the innermost changes, and the
        // non-terminal keys of that level go. Keeping the levels is what leaves a deeper
        // fold's grouping intact for the fold above it.
        let slot = output.deepest_values_mut();
        let folded = std::mem::replace(slot, Tile::record(HashMap::new()));
        let Tile::Aggregation {
            accumulator,
            terminal,
            ..
        } = folded
        else {
            panic!("MapExtractAggregate expected an aggregation under the keys, got {folded:?}")
        };
        // Emit only the elements whose aggregation is terminal.
        let mask = terminal
            .as_bools()
            .unwrap_or_else(|| panic!("Expected bools"));
        *slot = self.kind.extract(*accumulator);
        // One bool per accumulator, so the mask is over the innermost collection's keys.
        output
            .innermost_level_mut()
            .unwrap_or_else(|| unreachable!("the input tiles as a collection"))
            .retain_keys(mask);
        output
    }

    /// Restates releases through the unchanged collection levels. Releasing part of an
    /// extracted value does not release its input aggregation.
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        self.input.release(match obsolete_guard {
            g if g.is_universal() => self.input.tiling().universal_guard(),
            g if g.is_empty() => self.input.tiling().empty_guard(),
            // What sits under the innermost level is the extract, not the input's
            // aggregation, so only a release of all of it reaches the input's values.
            g @ (TileGuard::Function(_) | TileGuard::Or(_)) => {
                let input = self.input.tiling();
                crate::interpreter::tiling::through_shared_levels(g, input.levels(), input)
            }
            g => unreachable!("MapExtractAggregate's tiling is a collection, released by {g:?}"),
        });
    }
}

/// Order two element paths lexicographically.
///
/// One level's keys share a type, so comparing two paths compares like with like at every
/// component and the order is total — which is what [`build_levels_from_paths`] needs, a
/// parent's children being contiguous only under one.
///
/// [`Value`] is `PartialOrd` and not `Ord`, so that precondition is checked rather than
/// assumed. Treating an incomparable pair as equal would not restore the order: the
/// comparison would fall through to the next component and sort a parent's children apart,
/// leaving the rebuild to emit one key twice. `MapResult` makes the same demand of a domain
/// it sorts (`Tile::DataFunction`'s keys, `map.rs`).
fn compare_paths(a: &[Value], b: &[Value]) -> Ordering {
    for (x, y) in a.iter().zip(b) {
        match x.partial_cmp(y) {
            Some(Ordering::Equal) => continue,
            Some(other) => return other,
            None => panic!(
                "a level holds keys of two types, so its elements have no order: \
                 {x:?} against {y:?}"
            ),
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
fn build_levels_from_paths(
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
        // A path may stop short of the innermost level: a key with nothing beneath.
        for level in 0..path.len() {
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
        return Tile::data_function(
            domains.pop().unwrap_or_else(|| unreachable!()),
            Box::new(codomain),
            domain_predicate,
            BitSet::new(),
        );
    }
    nest_levels(domains, starts, codomain, domain_predicate)
}

/// Collapses the innermost collection of a nested tile into an aggregation, leaving the
/// levels above it intact.
///
/// Accumulators use complete key paths to distinguish equal keys under different parents.
/// Completion and release follow `src/interpreter/design-operators.md`,
/// "Aggregation and extraction".
pub struct MapAggregate {
    /// The lookup-function input to aggregate per key.
    input: Box<dyn TileOperator>,
    /// The aggregation operation (Sum, Max, …).
    kind: AggregateKind,
    base: OperatorBase,
}

impl MapAggregate {
    /// Create a new `MapAggregate` operator.
    ///
    /// `input` must have a `DataFunction` tiling whose codomain is a collection; `kind` must
    /// support that collection's element type. The innermost level becomes an
    /// `Aggregation` and the levels above it are left as they are
    /// ([`fold_innermost`]), so a two-level input yields
    /// `DataFunction { domain, codomain: Aggregation { .. } }`.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        // A collection whose values are not themselves a collection has no level above the
        // one being folded, which is `Aggregate`'s shape rather than this one's.
        let Tiling::DataFunction { codomain, .. } = input.tiling() else {
            panic!(
                "MapAggregate requires a collection input, got {}",
                input.tiling()
            )
        };
        assert!(
            matches!(codomain.as_ref(), Tiling::DataFunction { .. }),
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
    let Tiling::DataFunction { domain, codomain } = tiling else {
        panic!("fold_innermost walks a chain of collections, got {tiling}")
    };
    match codomain.as_ref() {
        Tiling::DataFunction { .. } => Tiling::DataFunction {
            domain: domain.clone(),
            codomain: Box::new(fold_innermost(codomain, kind)),
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

/// A folded tiling's key extent per level, outermost first, and the accumulator tiling the
/// chain ends in.
fn folded_shape(tiling: &Tiling) -> (Vec<Extent>, Tiling) {
    let mut extents = Vec::new();
    let mut node = tiling;
    loop {
        match node {
            Tiling::DataFunction { domain, codomain } => {
                extents.push(domain.clone());
                node = codomain;
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
            base: ProducerBase::new(
                MapAggregateProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            input: input_producer,
            kind: self.kind,
            accumulators: HashMap::new(),
            emptied_keys: HashSet::new(),
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
    /// Running accumulators indexed by complete paths, outermost key first.
    accumulators: HashMap<Vec<Value>, Tile>,
    /// Keys above the accumulators whose every accumulator was released without the key
    /// itself: a key is there only through what it maps to, and a release naming part of
    /// what lies beneath leaves it in place, holding nothing unreleased
    /// (`src/interpreter/design-operators.md`, "The completeness contract").
    emptied_keys: HashSet<Vec<Value>>,
}

impl TileProducer for MapAggregateProducer {
    fn state_info(&self) -> ProducerStateInfo {
        let accumulators: usize = self
            .accumulators
            .iter()
            .map(|(path, acc)| path.len() + acc.cell_count())
            .sum();
        ProducerStateInfo::holding(accumulators + self.emptied_keys.len())
    }

    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    /// Every level of the output is a level of the input, and the aggregation folds only the
    /// innermost beneath them.
    fn restates(&self) -> Restates {
        Restates::Every
    }

    /// The keys at every level are the input's, with each group beneath one whole, so the input
    /// is pulled at the projection and the answer is cut to it: accumulators for keys pulled
    /// earlier stay held, and a pull names the keys it wants.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection_for(self);
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let mut input_tile = self.input.get(projection.guard(self.input.tiling()));
        trace!("{} received {input_tile:?}", self.name());
        let upstream_guard = input_tile.to_guard();
        input_tile.compact();
        let Tile::DataFunction {
            domain_predicate, ..
        } = &input_tile
        else {
            panic!("MapAggregate requires a collection tile, got {input_tile:?}")
        };
        let domain_predicate = domain_predicate.clone();

        // The collection being folded is the innermost one, and the rows it stands over
        // are the groups: `parent_paths` names them, one path per group.
        //
        // Every level above it states its own completion, which is collected here: a level
        // says which of *its* keys are closed, and no other level says it for it.
        let depth = input_tile.innermost_depth().unwrap_or_else(|| {
            panic!("MapAggregate folds a collection of collections, got {input_tile:?}")
        });
        assert!(
            depth >= 1,
            "MapAggregate folds a collection of collections, so the fold sits under a \
             level: {input_tile:?}"
        );
        let level_predicates: Vec<Predicate> = (0..depth)
            .map(|level| {
                let Tile::DataFunction {
                    domain_predicate, ..
                } = input_tile.values_at(CurryLevel::new(level))
                else {
                    unreachable!("every level above the innermost one is a collection")
                };
                domain_predicate.clone()
            })
            .collect();
        // Which groups are complete, over whole paths: those some level on the path calls
        // complete ([`Tile::completion_at`]).
        let complete = input_tile.completion_at(CurryLevel::new(depth - 1));
        let parent_paths = input_tile.row_paths_at(depth);
        let folded = input_tile.values_at(CurryLevel::new(depth));
        let Tile::DataFunction { codomain, .. } = folded else {
            unreachable!("the loop breaks on a collection")
        };
        let values = (**codomain).clone();
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

        // Completion is per path. An inner group can be complete while its enclosing
        // collections remain open; `complete` combines the statements at every level.
        let mut entries: Vec<(Vec<Value>, Tile)> = self
            .accumulators
            .iter()
            .map(|(path, acc)| (path.clone(), acc.clone()))
            .collect();
        // Sorted so the outermost column stays ordered and a parent's children sit
        // contiguously, which is what rebuilding the offsets assumes.
        entries.sort_by(|a, b| compare_paths(&a.0, &b.0));
        // Omit identity-free extrema until they have values; a completed empty group is invalid.
        entries.retain(|(path, acc)| {
            if !kind.awaits_first_element(acc) {
                return true;
            }
            if complete.contains_path(path) {
                kind.no_extreme_of_nothing();
            }
            false
        });

        let terminal: Vec<bool> = entries
            .iter()
            .map(|(path, _)| complete.contains_path(path))
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
        let mut paths: Vec<&[Value]> = entries.iter().map(|(path, _)| path.as_slice()).collect();
        paths.extend(
            self.emptied_keys
                .iter()
                .filter(|key| !entries.iter().any(|(path, _)| path.starts_with(key)))
                .map(Vec::as_slice),
        );
        paths.sort_by(|a, b| compare_paths(a, b));
        let mut out = build_levels_from_paths(&paths, &extents, aggregation, domain_predicate);
        // Each level beneath the outermost holds the input's keys at that level, so it
        // states what the input's does there: a group settles once some level on its path
        // is complete, and a level saying nothing would leave it looking open downstream.
        for (level, stated) in level_predicates.into_iter().enumerate().skip(1) {
            if let Tile::DataFunction {
                domain_predicate, ..
            } = out.values_at_mut(CurryLevel::new(level))
            {
                *domain_predicate = stated;
            }
        }
        out.restrict_to(&projection, self.tiling());
        out
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Remove covered accumulators before another pull rebuilds the output from this map.
        match obsolete_guard {
            g if g.is_empty() => {}
            g if g.is_universal() => {
                self.accumulators.clear();
                self.emptied_keys.clear();
                self.input.release(self.input.tiling().universal_guard());
            }
            // Preserve unreleased ancestor keys even when their last accumulator is removed.
            // The input has a collection where the output has an accumulator, so restate
            // the guard through their shared levels rather than forwarding it unchanged.
            g => {
                let released: Vec<Vec<Value>> = self
                    .accumulators
                    .keys()
                    .filter(|path| g.covers_path(path))
                    .cloned()
                    .collect();
                self.accumulators.retain(|path, _| !g.covers_path(path));
                for path in released {
                    for len in 1..path.len() {
                        let key = &path[..len];
                        if !g.covers_path(key) {
                            self.emptied_keys.insert(key.to_vec());
                        }
                    }
                }
                self.emptied_keys.retain(|key| !g.covers_path(key));
                let levels = self.tiling().levels();
                let input = self.input.tiling();
                self.input
                    .release(crate::interpreter::tiling::through_shared_levels(
                        g, levels, input,
                    ));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{QuietSpy, ReleaseSpy};
    use crate::interpreter::{BaseType, Extent, Predicate, Tile};
    fn int_function(domain: Vec<u64>, values: Vec<i64>) -> Tile {
        Tile::data_function(
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
        let in_tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (spy, _released) = ReleaseSpy::new(int_function(vec![0, 1], vec![10, 20]), in_tiling);
        let tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let mut producer = AggregateProducer::new(
            ProducerBase::unowned(AggregateProducer::alloc_id(), &tiling),
            Box::new(spy),
        );

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
        let in_tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (spy, released) = ReleaseSpy::new(int_function(vec![0], vec![10]), in_tiling.clone());
        let tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let mut producer = AggregateProducer::new(
            ProducerBase::unowned(AggregateProducer::alloc_id(), &tiling),
            Box::new(spy),
        );

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
        let in_tiling = Tiling::data_function(
            key_extent.clone(),
            Tiling::data_function(
                Extent::Base(BaseType::Int),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        // Keys 1 and 2, each with two values: 1 -> [10, 20], 2 -> [30, 40].
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![1, 2]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::Ints(vec![0, 1, 0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30, 40]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let (spy, released) = QuietSpy::new(tile, in_tiling.clone());
        let out_tiling = Tiling::data_function(
            key_extent,
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            },
        );
        let mut producer = MapAggregateProducer {
            base: ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
            input: Box::new(spy),
            kind: AggregateKind::Sum,
            accumulators: HashMap::new(),
            emptied_keys: HashSet::new(),
        };

        let first = producer.get(out_tiling.universal_guard());
        let Tile::DataFunction { domain, .. } = &first else {
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
        let Tile::DataFunction { domain, .. } = &second else {
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
    /// Key 2's group is still growing, so [`Tile::to_guard`] stops inside it and the first
    /// pull releases only the path as far as it got. Releasing key 2 whole reaches past
    /// that path, making it the one guard the producer has to forward for the key to be
    /// reclaimed — the input's own keys being this producer's accumulator key set. A key
    /// the first pull already covered would be dropped by the release accumulation in
    /// [`TileProducer::release`] instead, and show nothing about forwarding.
    #[test]
    fn map_aggregate_forwards_a_per_key_release_to_an_open_input() {
        let key_extent = Extent::Base(BaseType::Int);
        let in_tiling = Tiling::data_function(
            key_extent.clone(),
            Tiling::data_function(
                Extent::Base(BaseType::Int),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        // Key 1 holds its whole group; key 2 has delivered the first of its two.
        let tile = Tile::data_function(
            ColumnValue::Ints(vec![1, 2]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::Ints(vec![0, 1, 0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::at_or_below(Value::Int(1)),
            BitSet::new(),
        );
        let (spy, released) = QuietSpy::new(tile, in_tiling.clone());
        let out_tiling = Tiling::data_function(
            key_extent,
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
            },
        );
        let mut producer = MapAggregateProducer {
            base: ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
            input: Box::new(spy),
            kind: AggregateKind::Sum,
            accumulators: HashMap::new(),
            emptied_keys: HashSet::new(),
        };
        producer.get(out_tiling.universal_guard());
        assert!(
            !released.borrow().iter().any(TileGuard::is_universal),
            "a bounded predicate is not released whole, got {:?}",
            released.borrow()
        );

        let key_two = TileGuard::Function(FunctionGuard::Domain(Predicate::Intervals(
            intervalsets::IntervalSet::from(intervalsets::Interval::closed(
                Value::Int(2),
                Value::Int(2),
            )),
        )));
        producer.release(key_two.clone());
        assert!(
            released.borrow().contains(&key_two),
            "the per-key release must reach the input, got {:?}",
            released.borrow()
        );
    }

    /// An input holding the group `[0, 2, 1]` under an open outer key, the order `Tile::merge`
    /// gives two interleaving deliveries. The first pull sums 330 and releases what it read,
    /// so a second pull adds nothing.
    #[test]
    fn a_sum_over_a_group_held_out_of_order_counts_each_element_once() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let in_tiling =
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int())));
        let tile = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![0, 2, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![100, 120, 110]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let (spy, _) = QuietSpy::new(tile, in_tiling);
        let out_tiling = Tiling::data_function(
            uint(),
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(int())),
            },
        );
        let mut producer = MapAggregateProducer {
            base: ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
            input: Box::new(spy),
            kind: AggregateKind::Sum,
            accumulators: HashMap::new(),
            emptied_keys: HashSet::new(),
        };
        producer.get(out_tiling.universal_guard());
        let second = producer.get(out_tiling.universal_guard());
        let Tile::Aggregation { accumulator, .. } = second.values_at(CurryLevel::new(1)) else {
            panic!("the fold sits beneath one level, got {second:?}")
        };
        assert_eq!(
            **accumulator,
            Tile::Scalar(ColumnValue::Ints(vec![330])),
            "each element counted once"
        );
    }

    /// A group the input settles at an inner level is stated settled at the same level of
    /// the output, which holds the input's keys there.
    #[test]
    fn map_aggregate_states_a_settled_group_at_its_own_level() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let in_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int()))),
        );
        // Outer row 0 is open; the level beneath calls key 0 under row 0 complete, so the
        // group at (0, 0) is whole.
        let tile = Tile::data_function(
            ColumnValue::from_uints(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::from_uints(vec![0]),
                Box::new(Tile::grouped(
                    vec![0],
                    ColumnValue::from_uints(vec![0, 1]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
                    Predicate::False,
                    BitSet::new(),
                )),
                Predicate::qualified(Predicate::point(Value::UInt(0)), Predicate::True),
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let (spy, _released) = QuietSpy::new(tile, in_tiling);
        let out_tiling = Tiling::data_function(
            uint(),
            Tiling::data_function(
                uint(),
                Tiling::Aggregation {
                    kind: AggregateKind::Sum,
                    accumulator: Box::new(Tiling::Scalar(int())),
                },
            ),
        );
        let mut producer = MapAggregateProducer {
            base: ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
            input: Box::new(spy),
            kind: AggregateKind::Sum,
            accumulators: HashMap::new(),
            emptied_keys: HashSet::new(),
        };
        let out = producer.get(out_tiling.universal_guard());
        let Tile::Aggregation { terminal, .. } = out.values_at(CurryLevel::new(2)) else {
            panic!("the fold sits beneath two levels, got {out:?}")
        };
        assert_eq!(
            terminal,
            &ColumnValue::Bools(vec![true; 1]),
            "the any-level rule settles the group: {out:?}"
        );
        let Tile::DataFunction {
            domain_predicate, ..
        } = out.values_at(CurryLevel::new(1))
        else {
            panic!("the output's second level is a collection, got {out:?}")
        };
        assert!(
            domain_predicate.contains_path(&[Value::UInt(0), Value::UInt(0)]),
            "the input settles (0, 0) at this level, and the output says nothing: \
             {domain_predicate:?}"
        );
    }
}

#[cfg(test)]
mod aggregate_projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, ints_by_position, keys_between,
    };
    use crate::interpreter::{BaseType, Extent, Tile};

    /// `sum(xs)` over a finished stream `[1, 2, 3, 4]`, with the stream's pulls logged.
    fn sum_of_finished_stream() -> (AggregateProducer, GuardLog) {
        let in_tiling = Tiling::data_function(
            Extent::uint_range(4),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (stream, pulled, _) =
            ProjectionSpy::new(ints_by_position(&[1, 2, 3, 4], true), in_tiling);
        let tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        (
            AggregateProducer::new(
                ProducerBase::unowned(AggregateProducer::alloc_id(), &tiling),
                Box::new(stream),
            ),
            pulled,
        )
    }

    /// `sum(evens ++ odds)` while the odd arm delivers late. Each pull of the union returns
    /// what the arms hold and have not had released, and the aggregate releases what it folded,
    /// so a row is folded once however many times the union is pulled: the sum grows by the
    /// rows that arrive and by nothing else.
    #[test]
    fn a_sum_over_a_union_folds_each_row_once_across_pulls() {
        use crate::interpreter::tile_operators::UnionOperator;
        use crate::interpreter::tile_operators::test_helpers::{ScriptedOp, int_column};
        use crate::interpreter::{FunctionGuard, Predicate, Scheduler, Value};

        let stream = Tiling::data_function(
            Extent::uint_range(8),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let TileGuard::Function(FunctionGuard::Domain(through_3)) = keys_between(0, 3) else {
            unreachable!("keys_between names a key region")
        };
        let (even, _) = ScriptedOp::new(
            int_column(vec![0, 2, 4, 6], Predicate::True),
            stream.clone(),
        );
        let (odd, odd_cell) = ScriptedOp::new(int_column(vec![1, 3], through_3), stream);
        let union = UnionOperator::new_flat(
            vec![Box::new(even), Box::new(odd)],
            Extent::Base(BaseType::Int),
        );
        let mut sum = Aggregate::new(Box::new(union), AggregateKind::Sum);
        let mut scheduler = Scheduler::new();
        let mut producer = sum.subscribe(
            sum.tiling().universal_guard(),
            Box::new(|| {}),
            &mut scheduler,
        );
        let total = |tile: Tile| {
            let Tile::Aggregation {
                accumulator,
                terminal,
                ..
            } = tile
            else {
                panic!("an aggregation, got {tile:?}")
            };
            (*accumulator, terminal)
        };
        let open = || ColumnValue::Bools(vec![false]);

        // The odd arm has decided `0..=3` only, so the sum is a running one.
        let (first, terminal) = total(producer.get(sum.tiling().universal_guard()));
        assert_eq!(
            first,
            Tile::Scalar(ColumnValue::Ints(vec![1 + 2 + 3 + 4 + 6]))
        );
        assert_eq!(terminal, open());

        // Nothing has arrived since, so the same pull adds nothing and stays open.
        let (again, terminal) = total(producer.get(sum.tiling().universal_guard()));
        assert_eq!(again, first);
        assert_eq!(terminal, open());

        // The odd arm delivers row 5 without finishing: the sum takes it once and stays open.
        *odd_cell.borrow_mut() = int_column(vec![1, 3, 5], Predicate::exactly(&[Value::UInt(5)]));
        let (partial, terminal) = total(producer.get(sum.tiling().universal_guard()));
        assert_eq!(partial, Tile::Scalar(ColumnValue::Ints(vec![16 + 5])));
        assert_eq!(terminal, open());

        // Both arms have now decided every position, so the sum is final.
        *odd_cell.borrow_mut() = int_column(vec![1, 3, 5, 7], Predicate::True);
        let (last, terminal) = total(producer.get(sum.tiling().universal_guard()));
        assert_eq!(last, Tile::Scalar(ColumnValue::Ints(vec![(0..8).sum()])));
        assert_eq!(terminal, ColumnValue::Bools(vec![true]));
    }

    /// The fold reads the whole stream, and what it answers is one terminal accumulator.
    #[test]
    fn a_sum_reads_the_whole_stream() {
        let (mut sum, pulled) = sum_of_finished_stream();
        let tile = sum.get(sum.tiling().universal_guard());
        let Tile::Aggregation {
            accumulator,
            terminal,
            ..
        } = tile
        else {
            panic!("an aggregation")
        };
        assert_eq!(*accumulator, Tile::Scalar(ColumnValue::Ints(vec![10])));
        assert_eq!(terminal, ColumnValue::Bools(vec![true]));
        assert_eq!(pulled.borrow().len(), 1);
        assert!(pulled.borrow()[0].is_universal());
    }

    #[test]
    fn a_sum_asked_for_nothing_reads_nothing() {
        let (mut sum, pulled) = sum_of_finished_stream();
        let tile = sum.get(sum.tiling().empty_guard());
        assert_eq!(tile, sum.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }

    #[test]
    #[should_panic(expected = "one accumulator")]
    fn a_key_projection_of_a_sum_is_rejected() {
        let (mut sum, _) = sum_of_finished_stream();
        sum.get(keys_between(0, 1));
    }
}

#[cfg(test)]
mod extract_aggregate_projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{GuardLog, ProjectionSpy, keys_between};
    use crate::interpreter::{BaseType, Extent, Tile};

    /// `sum(xs)` extracted once the aggregation is terminal: an accumulator holding `10`.
    fn extract_of_finished_sum() -> (ExtractAggregateProducer, GuardLog) {
        let accumulator = Tiling::Scalar(Extent::Base(BaseType::Int));
        let in_tiling = Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(accumulator.clone()),
        };
        let finished = Tile::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10]))),
            terminal: ColumnValue::Bools(vec![true]),
        };
        let (input, pulled, _) = ProjectionSpy::new(finished, in_tiling);
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        (
            ExtractAggregateProducer {
                base: ProducerBase::unowned(ExtractAggregateProducer::alloc_id(), &tiling),
                input: Box::new(input),
                kind: AggregateKind::Sum,
                only_terminal: true,
            },
            pulled,
        )
    }

    #[test]
    fn a_finished_sum_extracts_whole() {
        let (mut extract, pulled) = extract_of_finished_sum();
        let tile = extract.get(extract.tiling().universal_guard());
        assert_eq!(tile, Tile::Scalar(ColumnValue::Ints(vec![10])));
        assert!(pulled.borrow()[0].is_universal());
    }

    #[test]
    fn an_extract_asked_for_nothing_reads_nothing() {
        let (mut extract, pulled) = extract_of_finished_sum();
        let tile = extract.get(extract.tiling().empty_guard());
        assert_eq!(tile, extract.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }

    #[test]
    #[should_panic(expected = "extracts one value")]
    fn a_key_projection_of_an_extracted_value_is_rejected() {
        let (mut extract, _) = extract_of_finished_sum();
        extract.get(keys_between(0, 1));
    }
}

#[cfg(test)]
mod map_aggregate_nested_projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        ProjectionSpyOp, assert_conforms_beneath,
    };
    use crate::interpreter::{BaseType, Extent, Tile};

    /// `k ⤇ j ⤇ z ⤇ Int`: the keys 0 and 1, each holding the positions 0 to 2, each holding the
    /// positions 0 and 1 valued `100k + 10j + z`, every level stated complete.
    fn three_levels_of_ints() -> Box<dyn TileOperator> {
        let tiling = Tiling::data_function(
            Extent::uint_range(2),
            Tiling::data_function(
                Extent::uint_range(3),
                Tiling::data_function(
                    Extent::uint_range(2),
                    Tiling::Scalar(Extent::Base(BaseType::Int)),
                ),
            ),
        );
        let values = (0..2)
            .flat_map(|k| (0..3).flat_map(move |j| (0..2).map(move |z| 100 * k + 10 * j + z)))
            .collect();
        let tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 3],
                ColumnValue::UInts(vec![0, 1, 2, 0, 1, 2]),
                Box::new(Tile::grouped(
                    vec![0, 2, 4, 6, 8, 10],
                    ColumnValue::UInts(vec![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                    Predicate::True,
                    BitSet::new(),
                )),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        Box::new(ProjectionSpyOp::new(tile, tiling).0)
    }

    /// The sum of each `(k, j)`'s positions, pulled at paths of `(k, j)`, answers what the whole
    /// answer cut to those paths answers: a loop's round pulls a sum at its position's path.
    #[test]
    fn a_sum_of_each_path_answers_a_projection_of_paths() {
        assert_conforms_beneath(|| {
            Box::new(MapAggregate::new(
                three_levels_of_ints(),
                AggregateKind::Sum,
            ))
        });
    }
}

#[cfg(test)]
mod map_aggregate_projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, keys_between,
    };
    use crate::interpreter::{BaseType, Extent, Tile};

    const GROUPS: u64 = 4;

    /// `{k: sum(group) for k, group in groups}` over the groups `0: [1, 2]`, `1: [3]`,
    /// `2: [4, 5]`, `3: [6]`, each stated whole, with the pulls of the groups logged.
    fn sums_of_groups() -> (MapAggregateProducer, GuardLog) {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let in_tiling = Tiling::data_function(
            Extent::uint_range(GROUPS),
            Tiling::data_function(uint(), Tiling::Scalar(int())),
        );
        let groups = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1, 2, 3]),
            Box::new(Tile::grouped(
                vec![0, 2, 3, 5],
                ColumnValue::from_uints(vec![0, 1, 0, 0, 1, 0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3, 4, 5, 6]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let (input, pulled, _) = ProjectionSpy::new(groups, in_tiling);
        let out_tiling = Tiling::data_function(
            Extent::uint_range(GROUPS),
            Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(Tiling::Scalar(int())),
            },
        );
        (
            MapAggregateProducer {
                base: ProducerBase::unowned(MapAggregateProducer::alloc_id(), &out_tiling),
                input: Box::new(input),
                kind: AggregateKind::Sum,
                accumulators: HashMap::new(),
                emptied_keys: HashSet::new(),
            },
            pulled,
        )
    }

    /// The group keys and sums an answer holds.
    fn sums(tile: &Tile) -> Vec<(Value, i64)> {
        let Tile::DataFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("a collection, got {tile:?}")
        };
        let Tile::Aggregation { accumulator, .. } = &**codomain else {
            panic!("an aggregation per key, got {codomain:?}")
        };
        let Tile::Scalar(ColumnValue::Ints(sums)) = &**accumulator else {
            panic!("integer sums, got {accumulator:?}")
        };
        (0..domain.len())
            .map(|i| (domain.index_at(i), sums[i]))
            .collect()
    }

    /// A morsel of groups pulls the input at the morsel and answers the morsel's sums, which is
    /// what a worker that owns those groups reads.
    #[test]
    fn a_morsel_of_groups_is_summed_from_a_morsel_of_the_input() {
        let (mut sums_of, pulled) = sums_of_groups();
        let morsel = sums_of.get(keys_between(1, 2));
        assert_eq!(
            sums(&morsel),
            vec![(Value::UInt(1), 3), (Value::UInt(2), 9)]
        );
        assert_eq!(*pulled.borrow(), vec![keys_between(1, 2)]);
    }

    /// The consumer releases a morsel before the next, which drops the first morsel's
    /// accumulators, so the second's answer holds its own groups.
    #[test]
    fn successive_morsels_answer_their_own_groups() {
        let (mut sums_of, _) = sums_of_groups();
        sums_of.get(keys_between(0, 1));
        sums_of.release(keys_between(0, 1));
        let next = sums_of.get(keys_between(2, 3));
        assert_eq!(sums(&next), vec![(Value::UInt(2), 9), (Value::UInt(3), 6)]);
    }

    #[test]
    fn sums_asked_for_nothing_read_nothing() {
        let (mut sums_of, pulled) = sums_of_groups();
        let tile = sums_of.get(sums_of.tiling().empty_guard());
        assert_eq!(tile, sums_of.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }

    #[test]
    fn the_morsels_together_are_the_whole_pull() {
        for guard in [keys_between(0, 3), keys_between(2, 5), keys_between(5, 5)] {
            assert_conforms(|| Box::new(sums_of_groups().0), guard);
        }
    }
}
