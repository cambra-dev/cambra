use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, PoisonError, RwLock};

use super::aggregate::{build_levels_from_paths, compare_paths};
use super::*;
use crate::interpreter::operator_graph::value;
use crate::{
    ccl::GroupedFold,
    interpreter::{
        BaseType, ColumnValue, Consumer, Projection, SubscribeContext, Value, tuple_field,
    },
};

/// Folds the rows of a collection into one accumulator per key: a group-by and the aggregation
/// over its groups, run as one breaker over the ungrouped rows
/// (`src/interpreter/design-operators.md`, "GroupAggregate").
///
/// The input is a chain of collections whose innermost level holds the rows, as records. Field
/// `_0` is the row's group key. Each aggregation then has a field holding the value it folds,
/// followed by its keep flags ([`GroupedFold`]). The levels above the rows are enclosing keys, and
/// each enclosing path groups its own rows. The output replaces the rows' level by
/// `key ⤇ result`, where the result is the one aggregation's, or a tuple of every aggregation's.
pub(crate) struct GroupAggregate {
    input: Arc<dyn TileOperator>,
    base: OperatorBase,
    folds: Vec<GroupedFold>,
}

/// The enclosing levels' key extents, outermost first, and the rows' record fields.
fn rows_of(tiling: &Tiling) -> (Vec<Extent>, &HashMap<SmolStr, Tiling>) {
    let mut enclosing = Vec::new();
    let mut at = tiling;
    loop {
        match at {
            Tiling::DataFunction { domain, codomain } => match &**codomain {
                Tiling::Record(fields) => return (enclosing, fields),
                inner => {
                    enclosing.push(domain.clone());
                    at = inner;
                }
            },
            other => panic!(
                "GroupAggregate expects a collection of (key, value, keep…) rows, got {other:?}"
            ),
        }
    }
}

impl GroupAggregate {
    /// # Panics
    ///
    /// When `input` is no collection of rows laid out as `folds` names, `folds` is empty, or a
    /// fold does not fold its value's tiling into a scalar. Planning fuses only such rows
    /// (`planning::group_fold`).
    pub(crate) fn new(input: Arc<dyn TileOperator>, folds: Vec<GroupedFold>) -> Self {
        let (enclosing, fields) = rows_of(input.tiling());
        assert_eq!(
            fields.len(),
            1 + folds.iter().map(|fold| 1 + fold.keeps).sum::<usize>(),
            "GroupAggregate expects a key, then a value and its keep flags per fold: {fields:?}"
        );
        assert!(
            matches!(fields[&tuple_field(0)], Tiling::Scalar(_)),
            "a group key is a scalar: {fields:?}"
        );
        for (value, keeps) in fold_columns(&folds) {
            assert!(fields.contains_key(&tuple_field(value)), "{fields:?}");
            for keep in keeps {
                assert!(
                    matches!(
                        &fields[&tuple_field(keep)],
                        Tiling::Scalar(Extent::Base(BaseType::Bool))
                    ),
                    "a keep flag is a Bool: {fields:?}"
                );
            }
        }
        let results = accumulator_tilings(&folds, fields);
        for result in &results {
            assert!(
                matches!(result, Tiling::Scalar(_)),
                "a fused group aggregate folds to a scalar: {result:?}"
            );
        }
        let result = match results.as_slice() {
            [one] => one.clone(),
            [] => panic!("GroupAggregate folds with at least one aggregation"),
            several => Tiling::Record(
                several
                    .iter()
                    .enumerate()
                    .map(|(i, result)| (tuple_field(i), result.clone()))
                    .collect(),
            ),
        };
        let tiling = enclosing.into_iter().rev().fold(
            Tiling::data_function(fields[&tuple_field(0)].extent(), result),
            |inner, domain| Tiling::data_function(domain, inner),
        );
        Self {
            base: OperatorBase::new(tiling),
            input,
            folds,
        }
    }
}

/// Each fold's value field and keep fields, by index into the row record.
fn fold_columns(folds: &[GroupedFold]) -> Vec<(usize, std::ops::Range<usize>)> {
    let mut at = 1;
    folds
        .iter()
        .map(|fold| {
            let value = at;
            at += 1 + fold.keeps;
            (value, value + 1..at)
        })
        .collect()
}

/// The tiling each fold folds its value field of `fields` into.
///
/// # Panics
///
/// When a fold does not fold its value.
fn accumulator_tilings(folds: &[GroupedFold], fields: &HashMap<SmolStr, Tiling>) -> Vec<Tiling> {
    folds
        .iter()
        .zip(fold_columns(folds))
        .map(|(fold, (value, _))| {
            let value = &fields[&tuple_field(value)];
            fold.kind
                .output_tiling(value)
                .unwrap_or_else(|| panic!("{:?} does not fold {value:?}", fold.kind))
        })
        .collect()
}

impl TileOperator for GroupAggregate {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
    }

    fn subscribe(
        self: Arc<Self>,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        cx: &mut SubscribeContext,
    ) -> Box<dyn TileProducer> {
        let (enclosing, fields) = rows_of(self.input.tiling());
        let depth = enclosing.len();
        let accumulators = accumulator_tilings(&self.folds, fields);
        // The enclosing levels are the input's; at depth 0 the outermost keys are the groups',
        // which no region of the rows names.
        let input = BreakerInput::new(consumer, self.input.tiling(), depth > 0);
        let input_producer =
            self.input
                .clone()
                .subscribe(self.input.tiling().universal_guard(), input.consumer, cx);
        share_breaker(GroupAggregateProducer::new(
            ProducerBase::new(
                GroupAggregateProducer::alloc_id(),
                self.tiling(),
                self.clone(),
                cx,
            )
            .breaking(input.downstream, input.placement),
            input_producer,
            self.folds.clone(),
            accumulators,
            depth,
        ))
    }
}

struct GroupAggregateProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    folds: Vec<GroupedFold>,
    /// The tiling of one group's accumulator, per aggregation.
    accumulators: Vec<Tiling>,
    /// How many enclosing levels stand above the rows.
    depth: usize,
    state: RwLock<GroupAggregateState>,
}

/// The accumulators and what the answers consumed state, behind the breaker's lock.
struct GroupAggregateState {
    /// Per enclosing path, one accumulator per aggregation per key read, its rows kept or not.
    /// An enclosing path the input holds with no row has an empty map.
    groups: HashMap<Vec<Value>, HashMap<Value, Vec<Tile>>>,
    /// Paths above the enclosing paths that hold nothing beneath them, which no group's path
    /// names.
    keys_with_nothing_beneath: HashSet<Vec<Value>>,
    /// What the answers consumed state of each enclosing level, together, outermost first.
    enclosing_stated: Vec<Predicate>,
    /// The rows the answers consumed state complete, over whole paths
    /// ([`Tile::completion_at`]), together.
    rows_complete: Predicate,
}

impl GroupAggregateProducer {
    fn new(
        base: ProducerBase,
        input: Box<dyn TileProducer>,
        folds: Vec<GroupedFold>,
        accumulators: Vec<Tiling>,
        depth: usize,
    ) -> Self {
        Self {
            base,
            input,
            folds,
            accumulators,
            depth,
            state: RwLock::new(GroupAggregateState {
                groups: HashMap::new(),
                keys_with_nothing_beneath: HashSet::new(),
                enclosing_stated: vec![Predicate::False; depth],
                rows_complete: Predicate::False,
            }),
        }
    }

    /// The final groups' results, cut to `projection`, read under the state's lock.
    fn answer(&self, projection: &Projection) -> Tile {
        let state = self.state.read().unwrap_or_else(PoisonError::into_inner);
        self.build(&state, projection)
    }

    /// Pull the input at `guard`, register every live row's key under its enclosing path and
    /// fold the kept rows, then release the input at what the answer stated, so no row is
    /// answered, or folded, twice.
    fn fold_input(&self, guard: TileGuard) {
        let obsolete = self.obsolete_guard();
        let mut rows = self.input.get(guard);
        let stated = rows.to_guard();
        rows.compact();
        {
            let mut state = self.state.write().unwrap_or_else(PoisonError::into_inner);
            self.fold_rows(&mut state, &rows, &obsolete);
        }
        // Released once the state's lock is dropped, as every breaker releases its input.
        self.input.release(stated);
    }

    /// Register every live row of `rows` under its enclosing path and fold the kept rows.
    fn fold_rows(&self, state: &mut GroupAggregateState, rows: &Tile, obsolete: &TileGuard) {
        let depth = self.depth;
        debug_assert_eq!(
            rows.innermost_depth(),
            Some(depth),
            "{} reads rows beneath its enclosing levels: {rows:?}",
            self.name()
        );
        for (level, stated) in state.enclosing_stated.iter_mut().enumerate() {
            let Tile::DataFunction {
                domain_predicate, ..
            } = rows.values_at(CurryLevel::new(level))
            else {
                unreachable!("every level above the rows is a collection")
            };
            *stated = stated.union(domain_predicate);
        }
        state.rows_complete = state
            .rows_complete
            .union(&rows.completion_at(CurryLevel::new(depth)));
        // A key above the enclosing paths with nothing beneath it is kept by path, since no
        // group names it.
        for level in 1..depth {
            let beneath = rows.values_at(CurryLevel::new(level));
            for (row, path) in rows.row_paths_at(level).into_iter().enumerate() {
                let (from, to) = beneath.row_run(row);
                if from == to && !obsolete.covers_path(&path) {
                    state.keys_with_nothing_beneath.insert(path);
                }
            }
        }
        if depth > 0 {
            for path in rows.row_paths_at(depth) {
                if !obsolete.covers_path(&path) {
                    state.groups.entry(path).or_default();
                }
            }
        }
        let paths = rows.row_paths_at(depth + 1);
        let Tile::DataFunction { codomain, .. } = rows.values_at(CurryLevel::new(depth)) else {
            unreachable!("the rows are a collection")
        };
        let Tile::Record { fields, .. } = &**codomain else {
            panic!(
                "{} expected (key, value, keep…) rows, got {codomain:?}",
                self.name()
            );
        };
        let Tile::Scalar(keys) = &fields[&tuple_field(0)] else {
            panic!("{} expects a scalar key", self.name());
        };
        debug_assert_eq!(paths.len(), keys.len(), "one path per row");
        let flags = |at: usize| match &fields[&tuple_field(at)] {
            Tile::Scalar(flags) => flags,
            other => panic!("a keep flag is a scalar, got {other:?}"),
        };
        // Per fold, the value field and the keep flags gating it.
        let columns: Vec<(&Tile, Vec<&ColumnValue>)> = fold_columns(&self.folds)
            .into_iter()
            .map(|(value, keeps)| (&fields[&tuple_field(value)], keeps.map(flags).collect()))
            .collect();
        for (row, path) in paths.iter().enumerate() {
            let enclosing = &path[..depth];
            let key = keys.index_at(row);
            let mut grouped = enclosing.to_vec();
            grouped.push(key.clone());
            if obsolete.covers_path(&grouped) {
                continue;
            }
            // Every row registers its key's group, kept or not: the group set is the keys the
            // rows carry, so a group whose rows a filter drops answers the fold of nothing.
            let accs = state
                .groups
                .entry(enclosing.to_vec())
                .or_default()
                .entry(key)
                .or_insert_with(|| {
                    self.folds
                        .iter()
                        .zip(&self.accumulators)
                        .map(|(fold, tiling)| fold.kind.initial_accumulator(tiling))
                        .collect()
                });
            for ((fold, acc), (values, keeps)) in self.folds.iter().zip(accs).zip(&columns) {
                if keeps.iter().all(|flags| flags.index_at(row).as_bool()) {
                    fold.kind.accumulate(acc, values, row, row + 1);
                }
            }
        }
    }

    /// Whether the groups under `enclosing` are final: every row beneath it is complete, so no
    /// row adds a group or folds into one.
    fn settled(&self, state: &GroupAggregateState, enclosing: &[Value]) -> bool {
        if self.input.obsolete_guard().is_universal() {
            return true;
        }
        match enclosing.is_empty() {
            true => state.rows_complete.is_true(),
            false => state.rows_complete.within(enclosing, 0).is_true(),
        }
    }

    /// The final groups' results, cut to `projection`. Only a settled enclosing path's groups are
    /// held, since a partial accumulator is no result, and each settled path is stated complete
    /// at the level of its last key, beneath which it holds every group.
    fn build(&self, state: &GroupAggregateState, projection: &Projection) -> Tile {
        let mut entries: Vec<(Vec<Value>, Vec<Value>)> = Vec::new();
        let mut settled: Vec<&Vec<Value>> = Vec::new();
        for (enclosing, groups) in &state.groups {
            if !self.settled(state, enclosing) {
                continue;
            }
            settled.push(enclosing);
            for (key, accs) in groups {
                let results = self
                    .folds
                    .iter()
                    .zip(accs)
                    .map(|(GroupedFold { kind, .. }, acc)| {
                        if kind.awaits_first_element(acc) {
                            kind.no_value_of_nothing();
                        }
                        let Tile::Scalar(result) = kind.extract(acc.clone()) else {
                            unreachable!("checked by `GroupAggregate::new`: each fold is a scalar")
                        };
                        result.index_at(0)
                    })
                    .collect();
                let mut path = enclosing.clone();
                path.push(key.clone());
                entries.push((path, results));
            }
        }
        entries.sort_by(|a, b| compare_paths(&a.0, &b.0));
        let mut paths: Vec<&[Value]> = entries.iter().map(|(path, _)| path.as_slice()).collect();
        // An enclosing path that holds no group, and a key above with nothing beneath it, stand
        // as keys with nothing beneath.
        paths.extend(
            settled
                .iter()
                .filter(|enclosing| !enclosing.is_empty() && state.groups[**enclosing].is_empty())
                .map(|enclosing| enclosing.as_slice()),
        );
        paths.extend(
            state
                .keys_with_nothing_beneath
                .iter()
                .filter(|key| !state.groups.keys().any(|path| path.starts_with(key)))
                .map(Vec::as_slice),
        );
        paths.sort_by(|a, b| compare_paths(a, b));
        let mut extents = Vec::new();
        let mut at = self.tiling();
        while let Tiling::DataFunction { domain, codomain } = at {
            extents.push(domain.clone());
            at = codomain;
        }
        let column = |i: usize, extent: &Extent| {
            Tile::Scalar(ColumnValue::from_values(
                entries
                    .iter()
                    .map(|(_, results)| results[i].clone())
                    .collect(),
                extent,
            ))
        };
        let results = match at {
            Tiling::Scalar(extent) => column(0, extent),
            Tiling::Record(fields) => Tile::record(
                (0..self.folds.len())
                    .map(|i| {
                        let Tiling::Scalar(extent) = &fields[&tuple_field(i)] else {
                            unreachable!("checked by `GroupAggregate::new`: each fold is a scalar")
                        };
                        (tuple_field(i), column(i, extent))
                    })
                    .collect(),
            ),
            other => unreachable!("built with scalar results in `GroupAggregate::new`: {other:?}"),
        };
        // Each enclosing level states what the input's does there, and the level of an
        // enclosing path's last key also states each settled path complete. At depth 0 the
        // outermost level is the groups', complete once the rows are.
        let mut statements = state.enclosing_stated.clone();
        match statements.last_mut() {
            Some(innermost) => {
                *innermost = innermost.union(&Predicate::union_all(
                    settled
                        .iter()
                        .map(|path| Predicate::exactly(path))
                        .collect(),
                ));
                statements.push(Predicate::False);
            }
            None => statements.push(match self.settled(state, &[]) {
                true => Predicate::True,
                false => Predicate::False,
            }),
        }
        let mut out = build_levels_from_paths(&paths, &extents, results, statements[0].clone());
        for (level, stated) in statements.iter().enumerate().skip(1) {
            if let Tile::DataFunction {
                domain_predicate, ..
            } = out.values_at_mut(CurryLevel::new(level))
            {
                *domain_predicate = stated.clone();
            }
        }
        debug_assert!(
            out.check_from(self.tiling()) && validate_tile(&out),
            "{} answers a tile of its tiling: {out:?}",
            self.name()
        );
        out.restrict_to(projection, self.tiling());
        out
    }
}

impl TileProducer for GroupAggregateProducer {
    fn state_info(&self) -> ProducerStateInfo {
        let state = self.state.read().unwrap_or_else(PoisonError::into_inner);
        let groups: usize = state.groups.values().map(HashMap::len).sum();
        ProducerStateInfo::holding(groups + state.keys_with_nothing_beneath.len())
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

    /// The answer is built from the accumulators and cut to the projection at any level.
    fn restates(&self) -> Restates {
        Restates::Every
    }

    fn answers_from_state(&self) -> bool {
        true
    }

    /// The answer is built from the accumulators, which only a consume folds into.
    fn get_impl(&self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection_for(self);
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        self.answer(&projection)
    }

    fn release_impl(&self, obsolete_guard: TileGuard) {
        if obsolete_guard.is_empty() {
            return;
        }
        if obsolete_guard.is_universal() {
            {
                let mut state = self.state.write().unwrap_or_else(PoisonError::into_inner);
                state.groups.clear();
                state.keys_with_nothing_beneath.clear();
            }
            return self.input.release(self.input.tiling().universal_guard());
        }
        let obsolete = self.obsolete_guard();
        {
            let mut state = self.state.write().unwrap_or_else(PoisonError::into_inner);
            state
                .groups
                .retain(|enclosing, _| enclosing.is_empty() || !obsolete.covers_path(enclosing));
            for (enclosing, groups) in &mut state.groups {
                groups.retain(|key, _| {
                    let mut path = enclosing.clone();
                    path.push(key.clone());
                    !obsolete.covers_path(&path)
                });
            }
            state
                .keys_with_nothing_beneath
                .retain(|key| !obsolete.covers_path(key));
        }
        // The enclosing levels are the input's, so a release of their keys releases the rows
        // beneath them. A release of groups beneath an enclosing path names no row, the rows
        // being keyed by position: each consume has released the rows it read already.
        if self.depth > 0 {
            self.input
                .release(crate::interpreter::tiling::through_shared_levels(
                    obsolete_guard,
                    self.depth,
                    self.input.tiling(),
                ));
        }
    }
}

impl Breaker for GroupAggregateProducer {
    /// Folds the rows the input answers at `guard`, a guard of the input's tiling, and releases
    /// the input at what the answer stated.
    fn consume_impl(&self, _: InputId, guard: TileGuard) {
        debug_assert!(
            guard.check_from(self.input.tiling()),
            "{} consumes a guard of its input's tiling: {guard:?}",
            self.name()
        );
        if guard.is_empty() || self.obsolete_guard().is_universal() {
            return;
        }
        self.fold_input(guard);
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

impl BreakingProducer for GroupAggregateProducer {
    /// Beneath enclosing keys it holds the groups of the settled paths, and a push of those is a
    /// region beneath the outermost keys, which a reader's chain may not restate
    /// (`TileProducer::restates`); it pushes at the pipeline's finish, as `MapAggregate` does.
    fn pushes_while_consuming(&self) -> bool {
        false
    }

    /// The final groups: those of every settled enclosing path, and the keys the input states
    /// complete above them.
    fn complete(&self) -> TileGuard {
        self.answer(&Projection::Everything).to_guard()
    }

    /// Cut at the outermost keys held.
    fn morsels(&self, guard: &TileGuard, rows: usize) -> Vec<TileGuard> {
        let output = self.answer(&Projection::Everything);
        let keys = output.live_keys().into_iter().flatten();
        cut_at_keys(guard, keys.map(|(_, key)| key), rows, self.tiling())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::AggregateKind;
    use crate::interpreter::tile_operators::test_helpers::ProjectionSpy;
    use bit_set::BitSet;

    fn ints() -> Extent {
        Extent::Base(BaseType::Int)
    }

    fn uints() -> Extent {
        Extent::Base(BaseType::UInt)
    }

    fn row_tiling() -> Tiling {
        Tiling::Record(HashMap::from([
            (tuple_field(0), Tiling::Scalar(ints())),
            (tuple_field(1), Tiling::Scalar(ints())),
            (tuple_field(2), Tiling::Scalar(Extent::Base(BaseType::Bool))),
        ]))
    }

    fn rows(keys: Vec<i64>, values: Vec<i64>, keep: Vec<bool>) -> Tile {
        Tile::record(HashMap::from([
            (tuple_field(0), Tile::Scalar(ColumnValue::Ints(keys))),
            (tuple_field(1), Tile::Scalar(ColumnValue::Ints(values))),
            (tuple_field(2), Tile::Scalar(ColumnValue::Bools(keep))),
        ]))
    }

    fn positions(at_most: u64) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(Value::UInt(
            at_most,
        ))))
    }

    fn after(at_most: u64) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(
            Predicate::True.minus(&Predicate::at_or_below(Value::UInt(at_most))),
        ))
    }

    /// Group 2's one row fails its keep flag, so it folds nothing and stays a group; no group is
    /// held before every row is read, since a later row can carry any key.
    #[test]
    fn groups_are_held_once_every_row_is_read_and_a_filtered_group_stays() {
        let input_tiling = Tiling::data_function(uints(), row_tiling());
        let input = Tile::data_function(
            ColumnValue::UInts(vec![0, 1, 2, 3]),
            Box::new(rows(
                vec![0, 1, 0, 2],
                vec![1, 2, 3, 4],
                vec![true, true, true, false],
            )),
            Predicate::True,
            BitSet::new(),
        );
        let (input, _, _) = ProjectionSpy::new(input, input_tiling.clone());
        let output = Tiling::data_function(ints(), Tiling::Scalar(ints()));
        let mut sums = GroupAggregateProducer::new(
            ProducerBase::unowned(GroupAggregateProducer::alloc_id(), &output),
            Box::new(input),
            vec![GroupedFold {
                kind: AggregateKind::Sum,
                keeps: 1,
            }],
            vec![Tiling::Scalar(ints())],
            0,
        );
        sums.begin_run();
        sums.consume_in_pipeline(InputId::ONLY, positions(1));
        assert!(sums.complete().is_empty(), "{:?}", sums.complete());
        sums.consume_in_pipeline(InputId::ONLY, after(1));
        assert!(sums.complete().is_universal(), "{:?}", sums.complete());
        assert_eq!(
            sums.answer(&Projection::Everything),
            Tile::data_function(
                ColumnValue::Ints(vec![0, 1, 2]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![4, 2, 0]))),
                Predicate::True,
                BitSet::new(),
            )
        );
    }

    /// Each enclosing row groups its own rows, and its groups are held once the rows beneath it
    /// are complete, whatever the other enclosing rows state.
    #[test]
    fn an_enclosing_row_settles_on_its_own() {
        let input_tiling =
            Tiling::data_function(uints(), Tiling::data_function(uints(), row_tiling()));
        let input = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::UInts(vec![0, 1, 0, 1]),
                Box::new(rows(
                    vec![5, 5, 6, 7],
                    vec![1, 2, 3, 4],
                    vec![true, true, true, true],
                )),
                Predicate::qualified(Predicate::point(Value::UInt(0)), Predicate::True),
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let (input, _, released) = ProjectionSpy::new(input, input_tiling.clone());
        let output = Tiling::data_function(
            uints(),
            Tiling::data_function(ints(), Tiling::Scalar(ints())),
        );
        let mut sums = GroupAggregateProducer::new(
            ProducerBase::unowned(GroupAggregateProducer::alloc_id(), &output),
            Box::new(input),
            vec![GroupedFold {
                kind: AggregateKind::Sum,
                keeps: 1,
            }],
            vec![Tiling::Scalar(ints())],
            1,
        );
        sums.begin_run();
        sums.consume_in_pipeline(InputId::ONLY, input_tiling.universal_guard());
        let held = sums.complete();
        assert!(
            held.covers_path(&[Value::UInt(0), Value::Int(5)]),
            "row 0's rows are complete: {held:?}"
        );
        assert!(
            !held.covers_path(&[Value::UInt(1), Value::Int(6)]),
            "row 1's rows are not: {held:?}"
        );
        // A release of an enclosing key drops its groups and reaches the input at that key,
        // whose rows stand beneath it there too.
        sums.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::point(Value::UInt(0)),
        )));
        assert!(
            !sums
                .answer(&Projection::Everything)
                .live_keys()
                .into_iter()
                .flatten()
                .any(|(_, key)| key == Value::UInt(0)),
            "row 0 is released"
        );
        assert!(
            released
                .read()
                .unwrap_or_else(PoisonError::into_inner)
                .iter()
                .any(|guard| guard.covers_path(&[Value::UInt(0)])),
            "the input is released at row 0: {:?}",
            released.read().unwrap_or_else(PoisonError::into_inner)
        );
    }
}
