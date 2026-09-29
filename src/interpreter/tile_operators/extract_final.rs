use std::cmp::Ordering;

use super::*;
use crate::interpreter::operator_graph::value;
use crate::{
    interpreter::{
        ColumnValue, Consumer, Path, Scheduler, Value, forwarding_consumer, shared_consumer,
    },
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

// ---------------------------------------------------------------------------
// ExtractFinal / ExtractFinalProducer
// ---------------------------------------------------------------------------

/// The **final** value of each collection `source` holds, or the default where one holds no
/// position.
///
/// `rows` is how many collection levels stand above the reductions, and it is the only
/// thing that varies with depth. **None** is one reduction over the whole source:
/// `final_or_default` over a stream. **One or more** is a reduction per row of the innermost
/// of them: a nested loop's trailing read, the inner accumulator's history per enclosing row,
/// falling back to the seed that row began with. A `mut` loop's own trailing read with no
/// rows above is a [`StoreFinalRead`](crate::interpreter::commit_operator::StoreFinalRead)
/// instead, which samples the settled store.
///
/// With rows above, **the rows are the default's**, not the source's: a row whose loop ran no
/// position has no group in the source, and its answer is exactly its default. A row is
/// answerable where the source has closed its group, and the output's own predicate is the
/// default's met with that, widened by the rows already answered.
///
/// A row's final is held from the pull its group closes until this operator's consumer
/// releases the row, which is also when this operator releases the row of its source. See
/// `src/interpreter/design-operators.md`, "`ExtractFinal` reduces at any depth".
pub struct ExtractFinal {
    /// The collections being reduced, and — with rows above them — sparse over those rows.
    source: Box<dyn TileOperator>,
    /// The value each reduction falls back to where it has no position, one per row.
    ///
    /// `None` when the source is known **total** — a tag partition over an exhaustive
    /// `match` always yields exactly one value, so there is no empty case to fall back
    /// from and no default value has to be invented. An empty source with no default is an
    /// invariant violation, not a fallback, and only a reduction with no rows above it can
    /// declare itself total: the rows of the others are the default's.
    default: Option<Box<dyn TileOperator>>,
    /// How many collection levels stand above the reductions.
    rows: usize,
    /// The extent one reduction answers at, from the source's values. An answer is built at
    /// it rather than from itself: a value carries only the tag it holds, so a column built
    /// from one would have just that arm — narrower than this operator's tiling wherever
    /// the alternatives it collapses carry more tags between them. Building at the declared
    /// extent keeps every arm present, with the ones that did not occur empty, which is
    /// what downstream merges and appends require.
    value_extent: Extent,
    base: OperatorBase,
}

impl ExtractFinal {
    /// One reduction over the whole `source`, falling back to `default`.
    ///
    /// `source` must have a collection tiling and `default` a tiling whose extent the
    /// source's codomain includes — neither identically tiled nor even the same extent. A
    /// record value is `Scalar(Record)` coming from a mutable variable's history but
    /// struct-of-arrays from a literal, and a tag `match` collapses its arms to their join
    /// while the arm supplying the default carries only its own tag.
    pub fn new(source: Box<dyn TileOperator>, default: Box<dyn TileOperator>) -> Self {
        let tiling = Self::source_codomain_tiling(source.as_ref());
        debug_assert!(
            tiling.extent().includes(&default.tiling().extent()),
            "ExtractFinal default must be representable in the source codomain: \
             default {} is not included in {tiling}",
            default.tiling(),
        );
        Self {
            value_extent: tiling.extent(),
            base: OperatorBase::new(tiling),
            source,
            default: Some(default),
            rows: 0,
        }
    }

    /// One reduction over a source known to be **total**, which needs no default.
    ///
    /// Used where the stream is a partition that always covers exactly one position — an
    /// exhaustive tag `match` — so the empty case cannot arise. If the source does turn out
    /// empty, the producer fails loudly rather than inventing a value.
    pub fn without_default(source: Box<dyn TileOperator>) -> Self {
        let tiling = Self::source_codomain_tiling(source.as_ref());
        Self {
            value_extent: tiling.extent(),
            base: OperatorBase::new(tiling),
            source,
            default: None,
            rows: 0,
        }
    }

    /// One reduction per row: `source : K₀ ⤇ … ⤇ Kₙ₋₁ ⤇ (Pos ⤇ V)` against
    /// `default : K₀ ⤇ … ⤇ Kₙ₋₁ ⤇ V`, output `K₀ ⤇ … ⤇ Kₙ₋₁ ⤇ V`, where `rows` is `n`.
    ///
    /// `rows` is the iteration the reduction sits in, which the caller states from where it
    /// is in the program. It is not read off the default: a value that is a collection
    /// carries levels of its own, which a count of the default's levels would take for rows.
    /// Every level above the rows is left standing.
    pub fn per_row_at(
        source: Box<dyn TileOperator>,
        default: Box<dyn TileOperator>,
        rows: CurryLevel,
    ) -> Self {
        assert!(
            rows.index() > 0,
            "a reduction per row takes one default per row of a collection; a default of \
             {} is one reduction over the whole source, which is `ExtractFinal::new`",
            default.tiling()
        );
        let Tiling::DataFunction {
            codomain: values, ..
        } = source.tiling().values_at(rows)
        else {
            panic!(
                "a per-row reduction's source holds each row's positions beneath its {rows} \
                 rows: source {}, default {}",
                source.tiling(),
                default.tiling()
            )
        };
        let values = (**values).clone();
        let value_extent = values.extent();
        let default_values = default.tiling().values_at(rows);
        debug_assert!(
            value_extent.includes(&default_values.extent()),
            "a per-row reduction's default must be representable in the source's values: \
             default {default_values} is not included in {value_extent}",
        );
        let tiling = with_values_at(default.tiling(), rows, values);
        Self {
            base: OperatorBase::new(tiling),
            source,
            default: Some(default),
            rows: rows.index(),
            value_extent,
        }
    }

    /// What one position of `source` holds: its levels minus the one being indexed.
    ///
    /// A one-level source holds a scalar per position; a deeper one holds a collection, and
    /// the final position's value is that collection rather than an element of it.
    fn source_codomain_tiling(source: &dyn TileOperator) -> Tiling {
        match source.tiling() {
            Tiling::DataFunction { codomain, .. } => *codomain.clone(),
            other => panic!("ExtractFinal source must have a collection tiling, got {other}"),
        }
    }
}

impl TileOperator for ExtractFinal {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("source", &*self.source));
        if let Some(default) = &self.default {
            visit(value("default", &**default));
        }
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Both sides advance on their own — the default with the drive that produces it,
        // the source with the recurrence beneath it — and a row is answerable only once
        // both hold it, so progress on either is news.
        let shared = shared_consumer(consumer);
        let source = self.source.subscribe(
            self.source.tiling().universal_guard(),
            forwarding_consumer(&shared, &scheduler.wakeup_queue()),
            scheduler,
        );
        let default = self.default.as_mut().map(|d| {
            d.subscribe(
                d.tiling().universal_guard(),
                forwarding_consumer(&shared, &scheduler.wakeup_queue()),
                scheduler,
            )
        });
        Box::new(ExtractFinalProducer {
            base: ProducerBase::new(ExtractFinalProducer::alloc_id(), self.tiling()),
            source,
            default,
            rows: self.rows,
            value_extent: self.value_extent.clone(),
            answered: HashMap::new(),
            released: Predicate::False,
        })
    }
}

struct ExtractFinalProducer {
    base: ProducerBase,
    source: Box<dyn TileProducer>,
    default: Option<Box<dyn TileProducer>>,
    /// How many collection levels stand above the reductions.
    rows: usize,
    value_extent: Extent,
    /// Each reduction's answer once its group has closed, keyed by the path that reaches
    /// it — the empty path where no rows stand above.
    ///
    /// Bounded by the live rows: [`release_impl`](TileProducer::release_impl) drops what
    /// its consumer releases.
    answered: HashMap<Path, Tile>,
    /// The rows the consumer has released, which are neither answered again nor re-emitted.
    /// `True` retires a reduction with no rows above it, whose one answer is released whole.
    released: Predicate,
}

impl ExtractFinalProducer {
    /// The level whose keys say a group is closed: the innermost row level, naming the row
    /// whose group it is. A reduction with no rows above it has no such level — its one
    /// group is closed when the source's own level says every position has arrived — and
    /// the empty path reads `True` there and nothing else, which is that statement.
    fn closing_level(&self) -> CurryLevel {
        CurryLevel::new(self.rows.saturating_sub(1))
    }

    /// Whether the group at `path` can gain no further position.
    ///
    /// With rows above the reductions, the innermost row level says it of that row's key.
    /// With none there is no key to ask about — the empty path names the tile itself — and
    /// the statement is the source's own level being closed, which is its terminality. The
    /// two are not the same question: a source over a tagged union domain is terminal with
    /// a `Union` predicate that admits every arm, and asking such a predicate to contain
    /// the empty path answers no.
    fn is_closed(&self, source: &Tile, closed: &Predicate, path: &[Value]) -> bool {
        match self.rows {
            0 => source.is_terminal(),
            _ => closed.contains_path(path),
        }
    }

    /// The rows the source offers, against the flat row index each one's group sits at.
    ///
    /// One unnamed row at index 0 where no rows stand above the reductions: the source is
    /// then the single group, and a tile's own row is the one every tile has.
    fn source_rows(&self, source: &Tile) -> HashMap<Vec<Value>, usize> {
        match self.rows.checked_sub(1) {
            Some(above) => source
                .paths_at(CurryLevel::new(above))
                .into_iter()
                .enumerate()
                .map(|(i, path)| (path, i))
                .collect(),
            None => HashMap::from([(Vec::new(), 0)]),
        }
    }

    /// The last live position of row `index`'s group, as the tile that position holds.
    ///
    /// `None` where the group holds no live position, which is a reduction whose loop ran
    /// nothing and so answers from its default.
    fn group_final(&self, groups: &Tile, index: usize) -> Option<Tile> {
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = groups
        else {
            panic!("a reduction reduces a collection of positions, got {groups:?}")
        };
        let (start, end) = groups.row_run(index);
        debug_assert!(
            (start + 1..end).all(|k| domain
                .index_at(k - 1)
                .partial_cmp(&domain.index_at(k))
                .is_some_and(Ordering::is_lt)),
            "a group's positions ascend, so the last one is the final: {domain:?}"
        );
        let last = (start..end).rev().find(|k| !deleted.contains(*k))?;
        Some(if codomain.is_data_function() {
            // Keeping one position leaves what it holds as a collection on its own, which is
            // its value. The group is closed and this is its last position, so what it holds
            // is the whole collection.
            let mut sub = codomain.select_rows(&[last]);
            if let Tile::DataFunction {
                domain_predicate, ..
            } = &mut sub
            {
                *domain_predicate = Predicate::True;
            }
            sub
        } else {
            let cv = scalar_tile_to_column_value((**codomain).clone());
            Tile::Scalar(ColumnValue::from_values(
                vec![cv.index_at(last)],
                &self.value_extent,
            ))
        })
    }
}

impl TileProducer for ExtractFinalProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        let node = node.child("source", self.source.inspect(opts));
        match &self.default {
            Some(d) => node.child("default", d.inspect(opts)),
            None => node.annotate("total (no default)".to_string()),
        }
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // A reduction with no rows above it is over once it has answered: its answer does
        // not change, and it released both inputs in full on the pull it took — pulling
        // them again would break that promise. With rows above, other rows are still
        // coming, so the pull goes on.
        if self.rows == 0 {
            if self.released.contains_path(&[]) {
                return self.tiling().empty_tile();
            }
            if let Some(answer) = self.answered.get(&Path::default()) {
                return answer.clone();
            }
        }
        let source_tiling = self.source.tiling().clone();
        let source = self.source.get(source_tiling.universal_guard());
        // The default is pulled where it is needed and not before. With rows above the
        // reductions it carries the row set, so every pull needs it; with none it is the
        // fallback for a source that ran nothing, and pulling it before that is known
        // drives an input this operator may never read.
        let mut default = (self.rows > 0)
            .then(|| {
                self.default
                    .as_mut()
                    .map(|d| d.get(d.tiling().universal_guard()))
            })
            .flatten();

        // A group's final is the value at its highest position, so it is the final only
        // once no position can follow it — the source's statement, read at the level the
        // rows sit at. A standing level above answers for every carrier beneath it rather
        // than for these rows, and the row the nest is waiting on is one of them.
        let closed = level_completion(&source, self.closing_level());
        let groups = source.values_at(CurryLevel::new(self.rows));
        // Where each row's group sits in the source, and where its fallback sits in the
        // default. **The rows themselves are the default's**: a row whose loop ran no
        // position has no group in the source at all, and that row's answer is exactly its
        // fallback, so iterating the source's rows would never reach it.
        let in_source = self.source_rows(&source);
        let row_paths: Vec<Vec<Value>> = match (&default, self.rows.checked_sub(1)) {
            (Some(tile), Some(above)) => tile.paths_at(CurryLevel::new(above)),
            // One reduction, at the path that names the tile itself.
            (_, None) => vec![Vec::new()],
            // With rows above, the default is pulled every pull because it is the row set.
            (None, Some(_)) => unreachable!("a reduction per row takes its rows from a default"),
        };
        // A row the default has decided it does not hold is one this reduction never
        // answers, so the source holding a group there is a row lost rather than a row not
        // yet arrived.
        #[cfg(debug_assertions)]
        if let (Some(tile), Some(above)) = (&default, self.rows.checked_sub(1)) {
            let decided = level_completion(tile, CurryLevel::new(above));
            let rows: std::collections::HashSet<&Vec<Value>> = row_paths.iter().collect();
            let lost: Vec<&Vec<Value>> = in_source
                .keys()
                .filter(|path| {
                    !self.released.contains_path(path)
                        && decided.contains_path(path)
                        && !rows.contains(path)
                })
                .collect();
            debug_assert!(
                lost.is_empty(),
                "every row of a per-row reduction's source is one of its default's rows: the \
                 default has decided rows {lost:?} absent that the source holds"
            );
        }
        // Answer every group that has closed and is neither answered nor released. A group
        // with no live position ran nothing, so it falls back to its default — collected
        // and filled below, because the default is not pulled until one does.
        let mut from_default: Vec<Path> = Vec::new();
        for path in &row_paths {
            let key = Path::from(path.clone());
            if self.answered.contains_key(&key) || self.released.contains_path(path) {
                continue;
            }
            if !self.is_closed(&source, &closed, path) {
                continue;
            }
            match in_source
                .get(path)
                .and_then(|index| self.group_final(groups, *index))
            {
                Some(answer) => {
                    self.answered.insert(key, answer);
                }
                // No group at all, or a group with no live position: this reduction ran
                // nothing, so its value is the one it started from.
                None => from_default.push(key),
            }
        }
        if !from_default.is_empty() {
            let Some(producer) = self.default.as_mut() else {
                // No default means the source was declared total — an exhaustive tag
                // partition always covers exactly one position. An empty source here is
                // that invariant being wrong, so fail rather than invent a value.
                panic!(
                    "ExtractFinal over a source declared total emitted no value; the \
                     partition feeding it was not exhaustive"
                );
            };
            let tile =
                default.get_or_insert_with(|| producer.get(producer.tiling().universal_guard()));
            // Where each row's fallback sits in the default, read once it is in hand: with
            // no rows above the reductions it is the one row every tile has.
            let default_rows: HashMap<Vec<Value>, usize> = match self.rows.checked_sub(1) {
                Some(above) => tile
                    .paths_at(CurryLevel::new(above))
                    .into_iter()
                    .enumerate()
                    .map(|(i, path)| (path, i))
                    .collect(),
                None => HashMap::from([(Vec::new(), 0)]),
            };
            let values = tile.values_at(CurryLevel::new(self.rows));
            // A collection-valued fallback is the whole collection, which has converged
            // once it is terminal; a scalar one is a value per row, which is there or is
            // not yet.
            let column =
                (!values.is_data_function()).then(|| scalar_tile_to_column_value(values.clone()));
            for key in from_default {
                let Some(row) = default_rows.get(key.as_ref()) else {
                    continue;
                };
                // With rows above the reductions the default **is** the row set, so a row
                // it holds has a value there by construction. With none it is an operator
                // of its own, which may still be converging, and a row is answered when it
                // has settled and not before.
                let answer = match &column {
                    Some(column) if column.len() > *row => Tile::Scalar(ColumnValue::from_values(
                        vec![column.index_at(*row)],
                        &self.value_extent,
                    )),
                    Some(column) => {
                        debug_assert_eq!(
                            self.rows,
                            0,
                            "a default that keys the rows holds a value at each of them: \
                             row {row} of {} values",
                            column.len()
                        );
                        continue;
                    }
                    // A collection-valued fallback is the whole collection, which has
                    // converged once it is terminal.
                    None if values.is_terminal() => values.clone(),
                    None => continue,
                };
                self.answered.insert(key, answer);
            }
        }

        let Some(rows_above) = self.rows.checked_sub(1) else {
            // No rows above: the whole output is the one answer, and the source is done
            // with once it has been taken.
            if self.released.contains_path(&[]) {
                return self.tiling().empty_tile();
            }
            let Some(answer) = self.answered.get(&Path::default()) else {
                // Not yet final. Only the highest position is ever wanted, so every
                // position below the highest seen so far is dead — release it. Without
                // this a never-terminating loop pins the whole changelog waiting for a
                // terminal that never comes. Positions ascend, so the highest is the last
                // live one, whatever the loop's domain is: a map-domain loop's positions are
                // its keys. A union key has no prefix spelling ([`Predicate::below`]), so
                // those positions wait for the whole release instead.
                if let Tile::DataFunction {
                    domain, deleted, ..
                } = &source
                    && let Some(last) = (0..domain.len()).rev().find(|i| !deleted.contains(*i))
                    && let highest = domain.index_at(last)
                    && !matches!(highest, Value::Union { .. })
                {
                    self.source
                        .release(TileGuard::Function(FunctionGuard::Domain(
                            Predicate::below(highest),
                        )));
                }
                return self.tiling().empty_tile();
            };
            // Final: nothing more is wanted from either input.
            self.source.release(source_tiling.universal_guard());
            if let Some(d) = self.default.as_mut() {
                d.release(d.tiling().universal_guard());
            }
            return answer.clone();
        };
        let rows_level = CurryLevel::new(rows_above);
        let Some(mut out) = default.take() else {
            unreachable!("a reduction per row takes its rows from a default")
        };
        // The rows this operator answers: the ones the source has closed, and the ones it
        // already holds an answer for whatever the source still says. The source's own
        // statement leads, because only it can say `True` — an enumeration of the rows
        // answered so far never can, and a consumer waiting for the whole collection to
        // close would wait forever on one.
        let answered_here = self.answered.keys().fold(closed.clone(), |acc, path| {
            // Only what the source has not said already: a union re-spells the predicate,
            // and a consumer comparing one against what it last saw would read the same
            // region written differently as news.
            match acc.contains_path(path) {
                true => acc,
                false => acc.union(&Predicate::exactly(path)),
            }
        });
        let Tile::DataFunction { domain, .. } = out.values_at(rows_level) else {
            unreachable!("a per-row reduction's default keys its rows: {out:?}")
        };
        let open = Predicate::from_column_value(domain).minus(&answered_here);
        if open.as_bool() != Some(false) {
            out.remove_guarded(
                rows_level.wrap_guard(TileGuard::Function(FunctionGuard::Domain(open))),
            );
        }
        out.compact();
        // At **every** level down to the rows, not the rows alone. A standing level above
        // answers for the carriers beneath it, so both operands have to have finished with
        // them — and [`Tile::is_terminal`] reads the outermost level, so a standing level
        // left at the default's statement is the whole tile calling itself final.
        for level in 0..=rows_above {
            let level = CurryLevel::new(level);
            let complete_here = if level == rows_level {
                answered_here.clone()
            } else {
                level_completion(&source, level)
            };
            let Tile::DataFunction {
                domain_predicate, ..
            } = out.values_at_mut(level)
            else {
                unreachable!("a per-row reduction's default keys its rows")
            };
            *domain_predicate = domain_predicate.intersect(&complete_here);
        }
        let finals: Vec<Value> = out
            .paths_at(rows_level)
            .into_iter()
            .map(|path| {
                let answer = self
                    .answered
                    .get(&Path::from(path.clone()))
                    .unwrap_or_else(|| {
                        unreachable!("a row left standing is one this reduction answered: {path:?}")
                    });
                materialized_row(answer.clone())
            })
            .collect();
        *out.values_at_mut(CurryLevel::new(self.rows)) =
            Tile::Scalar(ColumnValue::from_values(finals, &self.value_extent));
        out
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let Some(rows_above) = self.rows.checked_sub(1) else {
            // One reduction answers one value, so the only release of it is the whole
            // thing: that retires the operator and finishes with both inputs. Anything
            // else names nothing it holds.
            if obsolete_guard.expect_universal_or_empty(&self.name()) {
                self.released = Predicate::True;
                self.answered.clear();
                self.source.release(self.source.tiling().universal_guard());
                if let Some(d) = self.default.as_mut() {
                    d.release(d.tiling().universal_guard());
                }
            }
            return;
        };
        // The output's keys are the default's, so a release names the same rows there and
        // forwards verbatim, at whatever level it names them. The universal and empty
        // guards are respelled against its own tiling, as a zip's operands' are. This runs
        // for every release, including one naming a standing level above the rows, which
        // the source and the cache below have nothing to say about — a row of the output
        // that the default still held would otherwise come back after its release.
        if let Some(d) = self.default.as_mut() {
            d.release(match &obsolete_guard {
                g if g.is_universal() => d.tiling().universal_guard(),
                g if g.is_empty() => d.tiling().empty_guard(),
                g => g.clone(),
            });
        }
        // The rows sit one level above the reductions, so that is the depth the guard
        // names them at; one that stops above names every row beneath what it names, and
        // one that descends past says nothing about them.
        let Some(rows) = released_rows(&obsolete_guard, rows_above) else {
            return;
        };
        // A released row is one nothing will ask for again, so its held answer goes with
        // it — which is what keeps this cache the size of the live rows.
        self.released = self.released.union(&rows);
        self.answered.retain(|path, _| !rows.contains_path(path));
        // The source holds each row's positions beneath those rows, so what carries over
        // is the rows the guard names rather than the guard itself: one that descended
        // past them would name a shape the source does not have.
        self.source.release(
            CurryLevel::new(rows_above)
                .wrap_guard(TileGuard::Function(FunctionGuard::Domain(rows))),
        );
    }
}

/// What `tile` calls complete at `level` — the region of that level's keys whose values
/// will gain nothing further.
///
/// `False` where the tile holds no such level, which is a tile that has produced nothing
/// rather than one that has finished.
fn level_completion(tile: &Tile, level: CurryLevel) -> Predicate {
    match tile.values_at(level) {
        Tile::DataFunction {
            domain_predicate, ..
        } => domain_predicate.clone(),
        _ => Predicate::False,
    }
}

/// The keys `guard` names `depth` levels in, over whole paths, or `None` where it names
/// none there.
///
/// A guard that stops above that depth names every key beneath the ones it names, so it
/// is lifted to them as [`Tile::completion_at`] lifts a statement. One that descends past
/// it is about what sits under them, which is not a release of rows.
fn released_rows(guard: &TileGuard, depth: usize) -> Option<Predicate> {
    match guard {
        // A universal guard names every key of every level, whatever depth it is spelled
        // at: [`Tiling::universal_guard`] stops at the outermost one rather than
        // descending, so the walk below would find no arm to read at any greater depth.
        g if g.is_universal() => Some(Predicate::True),
        TileGuard::Or(arms) => arms
            .iter()
            .filter_map(|arm| released_rows(arm, depth))
            .reduce(|a, b| a.union(&b)),
        TileGuard::Function(FunctionGuard::Codomain(inner)) if depth > 0 => {
            released_rows(inner, depth - 1)
        }
        TileGuard::Function(FunctionGuard::Domain(pred)) => {
            Some((0..depth).fold(pred.clone(), |above, _| {
                Predicate::qualified(above, Predicate::True)
            }))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use super::*;
    use crate::interpreter::tile_operators::{FunctionGuard, Predicate};
    use crate::interpreter::{BaseType, Extent};

    /// A non-terminal `DataFunction` source with domain `[0, 1, 2]`, recording
    /// every domain-release watermark it receives. Never becomes terminal, so it
    /// exercises `ExtractFinal`'s incremental (pre-terminal) release path.
    struct PartialSource {
        tiling: Tiling,
        releases: Rc<RefCell<Vec<usize>>>,
    }

    struct PartialSourceProducer {
        base: ProducerBase,
        releases: Rc<RefCell<Vec<usize>>>,
    }

    impl TileOperator for PartialSource {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            Box::new(PartialSourceProducer {
                base: ProducerBase::new(PartialSourceProducer::alloc_id(), &self.tiling),
                releases: self.releases.clone(),
            })
        }
    }

    impl TileProducer for PartialSourceProducer {
        impl_producer_base!();
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            Tile::data_function(
                ColumnValue::from_uints(vec![0, 1, 2]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
                Predicate::False,
                bit_set::BitSet::new(),
            )
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            if let TileGuard::Function(FunctionGuard::Domain(released)) = &obsolete_guard
                && let Some(Value::UInt(w)) = released.as_at_or_below()
            {
                self.releases.borrow_mut().push(w);
            }
        }
    }

    /// A **terminal** `DataFunction` source carrying `codomain_tile` over
    /// `domain`, used to drive `ExtractFinal` to its extract / default paths.
    struct TerminalSource {
        tiling: Tiling,
        domain: ColumnValue,
        codomain_tile: ColumnValue,
    }

    struct TerminalSourceProducer {
        base: ProducerBase,
        domain: ColumnValue,
        codomain_tile: ColumnValue,
    }

    impl TileOperator for TerminalSource {
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            Box::new(TerminalSourceProducer {
                base: ProducerBase::new(TerminalSourceProducer::alloc_id(), &self.tiling),
                domain: self.domain.clone(),
                codomain_tile: self.codomain_tile.clone(),
            })
        }
    }

    impl TileProducer for TerminalSourceProducer {
        impl_producer_base!();
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            Tile::data_function(
                self.domain.clone(),
                Box::new(Tile::Scalar(self.codomain_tile.clone())),
                Predicate::True,
                bit_set::BitSet::new(),
            )
        }
        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
    }

    fn named_variant(arms: &[(&str, Extent)]) -> Extent {
        Extent::Union(crate::ccl::TagMap::from_arms(
            arms.iter()
                .map(|(t, e)| (crate::ccl::FieldKey::Name((*t).into()), e.clone()))
                .collect(),
        ))
    }

    fn union_value(tag: &str, inner: Value) -> Value {
        Value::Union {
            tag: crate::ccl::FieldKey::Name(tag.into()),
            inner: Box::new(inner),
        }
    }

    /// The tags a `ColumnValue::Union` carries, and which of them hold rows.
    fn arm_occupancy(cv: &ColumnValue) -> Vec<(String, usize)> {
        let ColumnValue::Union(arms) = cv else {
            panic!("expected a union column, got {cv:?}");
        };
        arms.iter()
            .map(|(k, arm)| (k.to_string(), arm.len()))
            .collect()
    }

    /// A conditional whose arms carry different tags collapses to the arms'
    /// **join**, so the value that survives has to be emitted at that merged tag
    /// set — every arm present, the ones that did not occur empty. Emitting the
    /// column the value alone implies would carry only `.pos`, which then fails to
    /// conform to this operator's own tiling and cannot merge with a sibling arm.
    #[test]
    fn extracted_variant_is_emitted_at_the_merged_tag_set() {
        let merged = named_variant(&[
            ("neg", Extent::Base(BaseType::Int)),
            ("pos", Extent::Base(BaseType::Int)),
        ]);
        let source = TerminalSource {
            tiling: Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(merged.clone()),
            ),
            domain: ColumnValue::from_uints(vec![0]),
            codomain_tile: ColumnValue::from_values(
                vec![union_value("pos", Value::Int(5))],
                &merged,
            ),
        };
        // The default is the *other* arm, so its own extent is width-narrower.
        let default = Constant::new(
            union_value("neg", Value::Int(0)),
            named_variant(&[("neg", Extent::Base(BaseType::Int))]),
        );
        let mut op = ExtractFinal::new(Box::new(source), Box::new(default));
        let guard = op.tiling().universal_guard();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());
        let tile = producer.get(producer.tiling().universal_guard());

        let Tile::Scalar(cv) = tile else {
            panic!("expected a scalar tile");
        };
        assert_eq!(
            arm_occupancy(&cv),
            vec![("neg".to_string(), 0), ("pos".to_string(), 1)],
            "both tags present, only the one that occurred inhabited"
        );
        assert_eq!(cv.as_single(), Some(union_value("pos", Value::Int(5))));
    }

    /// The same widening on the **default** path: a terminal-but-empty source
    /// falls back to the trailing arm, whose value carries only its own tag.
    #[test]
    fn default_variant_is_emitted_at_the_merged_tag_set() {
        let merged = named_variant(&[
            ("neg", Extent::Base(BaseType::Int)),
            ("pos", Extent::Base(BaseType::Int)),
        ]);
        let source = TerminalSource {
            tiling: Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(merged.clone()),
            ),
            domain: ColumnValue::from_uints(vec![]),
            codomain_tile: ColumnValue::from_values(vec![], &merged),
        };
        let default = Constant::new(
            union_value("neg", Value::Int(7)),
            named_variant(&[("neg", Extent::Base(BaseType::Int))]),
        );
        let mut op = ExtractFinal::new(Box::new(source), Box::new(default));
        let guard = op.tiling().universal_guard();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());
        let tile = producer.get(producer.tiling().universal_guard());

        let Tile::Scalar(cv) = tile else {
            panic!("expected a scalar tile");
        };
        assert_eq!(
            arm_occupancy(&cv),
            vec![("neg".to_string(), 1), ("pos".to_string(), 0)],
        );
        assert_eq!(cv.as_single(), Some(union_value("neg", Value::Int(7))));
    }

    // ── A reduction per row ───────────────────────────────────────────────────

    /// A double answering with a fixed tile and recording every release it is handed.
    struct Fixed {
        tiling: Tiling,
        tile: Tile,
        releases: Rc<RefCell<Vec<TileGuard>>>,
    }

    struct FixedProducer {
        base: ProducerBase,
        tile: Tile,
        releases: Rc<RefCell<Vec<TileGuard>>>,
    }

    impl TileOperator for Fixed {
        fn tiling(&self) -> &Tiling {
            &self.tiling
        }
        // A test double holds no operator, and no session walks one.
        fn visit_inputs(&self, _visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {}
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            Box::new(FixedProducer {
                base: ProducerBase::new(FixedProducer::alloc_id(), &self.tiling),
                tile: self.tile.clone(),
                releases: self.releases.clone(),
            })
        }
    }

    impl TileProducer for FixedProducer {
        impl_producer_base!();
        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            self.tile.clone()
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            self.releases.borrow_mut().push(obsolete_guard);
        }
    }

    fn int() -> Extent {
        Extent::Base(BaseType::Int)
    }

    fn uint() -> Extent {
        Extent::Base(BaseType::UInt)
    }

    /// `rows ⤇ (Pos ⤇ Int)` with one group per entry of `groups`, and `complete` naming
    /// the rows whose groups are closed.
    fn groups_tile(groups: &[(u64, &[(u64, i64)])], complete: Predicate) -> Tile {
        let mut starts = Vec::new();
        let mut positions = Vec::new();
        let mut values = Vec::new();
        for (_, run) in groups {
            starts.push(positions.len());
            positions.extend(run.iter().map(|(p, _)| *p as usize));
            values.extend(run.iter().map(|(_, v)| *v));
        }
        Tile::data_function(
            ColumnValue::from_uints(groups.iter().map(|(k, _)| *k as usize).collect()),
            Box::new(Tile::grouped(
                ColumnValue::UInts(starts),
                ColumnValue::from_uints(positions),
                Box::new(Tile::Scalar(ColumnValue::Ints(values))),
                Predicate::True,
                bit_set::BitSet::new(),
            )),
            complete,
            bit_set::BitSet::new(),
        )
    }

    /// `rows ⤇ Int`, one default per row.
    fn defaults_tile(rows: &[(u64, i64)], complete: Predicate) -> Tile {
        Tile::data_function(
            ColumnValue::from_uints(rows.iter().map(|(k, _)| *k as usize).collect()),
            Box::new(Tile::Scalar(ColumnValue::Ints(
                rows.iter().map(|(_, v)| *v).collect(),
            ))),
            complete,
            bit_set::BitSet::new(),
        )
    }

    /// A subscribed per-row reduction beside the releases each operand was handed.
    struct Wired {
        producer: Box<dyn TileProducer>,
        source_releases: Rc<RefCell<Vec<TileGuard>>>,
        default_releases: Rc<RefCell<Vec<TileGuard>>>,
    }

    fn map_extract_final(source: Tile, default: Tile) -> Wired {
        let src_rel = Rc::new(RefCell::new(Vec::new()));
        let def_rel = Rc::new(RefCell::new(Vec::new()));
        let source = Fixed {
            tiling: Tiling::data_function(
                uint(),
                Tiling::data_function(uint(), Tiling::Scalar(int())),
            ),
            tile: source,
            releases: src_rel.clone(),
        };
        let default = Fixed {
            tiling: Tiling::data_function(uint(), Tiling::Scalar(int())),
            tile: default,
            releases: def_rel.clone(),
        };
        let mut op =
            ExtractFinal::per_row_at(Box::new(source), Box::new(default), CurryLevel::new(1));
        let guard = op.tiling().universal_guard();
        Wired {
            producer: op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new()),
            source_releases: src_rel,
            default_releases: def_rel,
        }
    }

    fn answers(tile: &Tile) -> Vec<(usize, i64)> {
        let Tile::DataFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("expected a collection, got {tile:?}")
        };
        let Tile::Scalar(ColumnValue::Ints(vs)) = &**codomain else {
            panic!("expected scalar answers, got {codomain:?}")
        };
        (0..domain.len())
            .map(|i| match domain.index_at(i) {
                Value::UInt(k) => (k, vs[i]),
                other => panic!("expected a UInt key, got {other:?}"),
            })
            .collect()
    }

    /// **A row the source holds no group for answers its default.** That is the whole
    /// reason the rows come from the default: a nested carrier opens a row when it decides
    /// a position, so a row whose loop ran none is absent from the history entirely.
    #[test]
    fn a_row_the_source_never_ran_answers_its_default() {
        let Wired { mut producer, .. } = map_extract_final(
            groups_tile(&[(0, &[(0, 10), (1, 20)])], Predicate::True),
            defaults_tile(&[(0, 7), (1, 99)], Predicate::True),
        );
        let tile = producer.get(producer.tiling().universal_guard());
        assert_eq!(
            answers(&tile),
            vec![(0, 20), (1, 99)],
            "row 0 takes its group's last value, row 1 its default"
        );
    }

    /// A row whose group the source leaves **open** is not answered, and the output does
    /// not call it complete — the default states its own rows final as it delivers them,
    /// so the meet with the source's statement is what keeps the output honest. A consumer
    /// that released the row on the default's word alone would never be offered it again.
    #[test]
    fn an_open_group_is_neither_answered_nor_called_complete() {
        let Wired { mut producer, .. } = map_extract_final(
            groups_tile(
                &[(0, &[(0, 10)]), (1, &[(0, 30)])],
                Predicate::at_or_below(Value::UInt(0)),
            ),
            defaults_tile(&[(0, 7), (1, 99)], Predicate::True),
        );
        let tile = producer.get(producer.tiling().universal_guard());
        assert_eq!(answers(&tile), vec![(0, 10)], "only the closed row answers");
        assert!(
            !tile.is_terminal(),
            "the output is not final while the source leaves a row open: {tile:?}"
        );
        let Tile::DataFunction {
            domain_predicate, ..
        } = &tile
        else {
            unreachable!()
        };
        assert_eq!(*domain_predicate, Predicate::at_or_below(Value::UInt(0)));
    }

    /// A **universal** release reaches both operands. `Tiling::universal_guard` stops at
    /// the outermost level rather than descending, so a guard walk looking for the rows'
    /// own arm finds none — which would leave the source holding every group it ever ran.
    #[test]
    fn a_universal_release_reaches_both_operands() {
        let Wired {
            mut producer,
            source_releases,
            default_releases,
        } = map_extract_final(
            groups_tile(&[(0, &[(0, 10)])], Predicate::True),
            defaults_tile(&[(0, 7)], Predicate::True),
        );
        producer.release(producer.tiling().universal_guard());
        assert_eq!(
            default_releases.borrow().len(),
            1,
            "the default is released"
        );
        let released = source_releases.borrow();
        let [guard] = released.as_slice() else {
            panic!("the source is released exactly once, got {released:?}")
        };
        assert!(
            guard.is_universal(),
            "a universal release of the output is a universal release of the source: {guard:?}"
        );
    }

    /// A release of some rows carries to both operands, naming the same rows.
    #[test]
    fn a_row_release_carries_to_both_operands() {
        let Wired {
            mut producer,
            source_releases,
            default_releases,
        } = map_extract_final(
            groups_tile(&[(0, &[(0, 10)]), (1, &[(0, 30)])], Predicate::True),
            defaults_tile(&[(0, 7), (1, 99)], Predicate::True),
        );
        let rows = TileGuard::Function(FunctionGuard::Domain(Predicate::at_or_below(Value::UInt(
            0,
        ))));
        producer.release(rows.clone());
        assert_eq!(*default_releases.borrow(), vec![rows.clone()]);
        assert_eq!(*source_releases.borrow(), vec![rows]);
    }

    /// The same two operands one level deeper: a **standing** level above the rows, which
    /// is what a nest three deep has. Two things only this shape can catch.
    ///
    /// [`Tile::is_terminal`] reads the outermost level and does not descend, so a standing
    /// level left at the default's statement is the whole tile calling itself final while
    /// the source is still running. And `Tiling::universal_guard` stops at the outermost
    /// level rather than descending, so a guard walk looking for the rows' own arm finds
    /// none — the source would be released of nothing at all.
    fn standing_map_extract_final() -> Wired {
        let src_rel = Rc::new(RefCell::new(Vec::new()));
        let def_rel = Rc::new(RefCell::new(Vec::new()));
        let one_row = |inner: Tile, complete: Predicate| {
            Tile::data_function(
                ColumnValue::from_uints(vec![0]),
                Box::new(inner),
                complete,
                bit_set::BitSet::new(),
            )
        };
        // Standing row 0 holds rows 0 and 1; only row 0 ran a position. The standing level
        // is not done, the rows it holds are.
        let source = Fixed {
            tiling: Tiling::data_function(
                uint(),
                Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int()))),
            ),
            tile: one_row(
                Tile::grouped(
                    ColumnValue::UInts(vec![0]),
                    ColumnValue::from_uints(vec![0]),
                    Box::new(Tile::grouped(
                        ColumnValue::UInts(vec![0]),
                        ColumnValue::from_uints(vec![0]),
                        Box::new(Tile::Scalar(ColumnValue::Ints(vec![10]))),
                        Predicate::True,
                        bit_set::BitSet::new(),
                    )),
                    Predicate::True,
                    bit_set::BitSet::new(),
                ),
                Predicate::False,
            ),
            releases: src_rel.clone(),
        };
        let default = Fixed {
            tiling: Tiling::data_function(
                uint(),
                Tiling::data_function(uint(), Tiling::Scalar(int())),
            ),
            tile: one_row(
                Tile::grouped(
                    ColumnValue::UInts(vec![0]),
                    ColumnValue::from_uints(vec![0, 1]),
                    Box::new(Tile::Scalar(ColumnValue::Ints(vec![7, 99]))),
                    Predicate::True,
                    bit_set::BitSet::new(),
                ),
                Predicate::True,
            ),
            releases: def_rel.clone(),
        };
        let mut op =
            ExtractFinal::per_row_at(Box::new(source), Box::new(default), CurryLevel::new(2));
        let guard = op.tiling().universal_guard();
        Wired {
            producer: op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new()),
            source_releases: src_rel,
            default_releases: def_rel,
        }
    }

    #[test]
    fn a_standing_level_takes_the_meet_of_both_statements() {
        let Wired { mut producer, .. } = standing_map_extract_final();
        let tile = producer.get(producer.tiling().universal_guard());
        assert!(
            !tile.is_terminal(),
            "the standing level is the source's to close, and it has not: {tile:?}"
        );
        let Tile::DataFunction { codomain, .. } = &tile else {
            unreachable!()
        };
        assert_eq!(
            answers(codomain),
            vec![(0, 10), (1, 99)],
            "the row that ran takes its group's last value, the row that did not its default"
        );
    }

    #[test]
    fn a_universal_release_under_a_standing_level_reaches_the_source() {
        let Wired {
            mut producer,
            source_releases,
            ..
        } = standing_map_extract_final();
        producer.release(producer.tiling().universal_guard());
        let released = source_releases.borrow();
        let [guard] = released.as_slice() else {
            panic!("the source is released exactly once, got {released:?}")
        };
        assert!(
            guard.is_universal(),
            "a universal release of the output is a universal release of the source: {guard:?}"
        );
    }

    /// A release naming a standing row names every row beneath it, so it reaches the source
    /// and retires the answers held there.
    #[test]
    fn a_release_of_a_standing_row_reaches_the_source() {
        let Wired {
            mut producer,
            source_releases,
            ..
        } = standing_map_extract_final();
        let _ = producer.get(producer.tiling().universal_guard());
        let standing = TileGuard::Function(FunctionGuard::Domain(Predicate::from_column_value(
            &ColumnValue::from_uints(vec![0]),
        )));
        producer.release(standing.clone());
        assert_eq!(*source_releases.borrow(), vec![standing]);
    }

    /// On a non-terminal pull, `ExtractFinal` needs only the highest-domain value,
    /// so it releases everything below it — `[0, max)`. Over a source with domain
    /// `[0, 1, 2]`, it forwards a release `≤ 1`, freeing the prefix that a
    /// never-terminating scalar-final loop would otherwise pin.
    #[test]
    fn extract_final_releases_below_the_running_max() {
        let value_tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let releases = Rc::new(RefCell::new(Vec::<usize>::new()));
        let source = PartialSource {
            tiling: Tiling::data_function(Extent::Base(BaseType::UInt), value_tiling.clone()),
            releases: releases.clone(),
        };
        let default = Constant::new(Value::Int(0), Extent::Base(BaseType::Int));
        let mut op = ExtractFinal::new(Box::new(source), Box::new(default));
        let guard = op.tiling().universal_guard();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());

        // Non-terminal source → ExtractFinal emits empty but releases `[0, max)`.
        let tile = producer.get(producer.tiling().universal_guard());
        assert!(
            !tile.is_terminal(),
            "a non-terminal source stays non-terminal"
        );
        assert_eq!(
            releases.borrow().last().copied(),
            Some(1),
            "ExtractFinal must release below the running max (positions 0, 1), keeping position 2"
        );
    }

    /// A loop over a map runs its keys as its positions, so the release below the highest
    /// one seen is stated over those keys rather than skipped for not being counters.
    #[test]
    fn a_running_release_takes_the_loops_own_positions() {
        let releases = Rc::new(RefCell::new(Vec::new()));
        let string = Extent::Base(BaseType::String);
        let source = Fixed {
            tiling: Tiling::data_function(string.clone(), Tiling::Scalar(int())),
            tile: Tile::data_function(
                ColumnValue::from_values(
                    vec![Value::String("a".into()), Value::String("b".into())],
                    &string,
                ),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
                Predicate::False,
                bit_set::BitSet::new(),
            ),
            releases: releases.clone(),
        };
        let default = Constant::new(Value::Int(0), int());
        let mut op = ExtractFinal::new(Box::new(source), Box::new(default));
        let guard = op.tiling().universal_guard();
        let mut producer = op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());
        let _ = producer.get(producer.tiling().universal_guard());
        assert_eq!(
            *releases.borrow(),
            vec![TileGuard::Function(FunctionGuard::Domain(
                Predicate::below(Value::String("b".into()))
            ))]
        );
    }
}
