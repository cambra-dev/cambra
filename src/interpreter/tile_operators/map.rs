use bit_set::BitSet;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use super::*;
use crate::interpreter::operator_graph::value;
use crate::interpreter::{FieldPath, tuple_field};
use crate::{
    interpreter::{
        ColumnValue, Consumer, DataSourceDomainExtentImpl, Extent, Projection, Scheduler, Value,
        shared_consumer,
    },
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// Applies a function operator to the values of a collection at the level the program applies
/// it ([`MapResult::new_at`]).
///
/// The result takes the place of the value the function was applied to, so the function's
/// own levels come to sit under the input's.
pub struct MapResult {
    /// Output tiling matches `input` tiling, transforming the codomain according to `function`.
    base: OperatorBase,
    /// The function input to iterate over.
    input: Box<dyn TileOperator>,
    /// The function to apply to each element.
    function: Box<dyn TileOperator>,
    /// The level the arguments stand at ([`MapResult::new_at`]).
    level: CurryLevel,
}

impl MapResult {
    /// Apply `function` to each of `input`'s values at `level`: the iteration the
    /// application sits in, which the caller states from where it is in the program.
    ///
    /// Not read off `input`'s tiling: an argument may be a collection of its own, whose
    /// levels a descent to the input's values would take for more of the iteration. The
    /// codomain of `function` takes the argument's place, beneath the levels above it.
    pub fn new_at(
        input: Box<dyn TileOperator>,
        function: Box<dyn TileOperator>,
        level: CurryLevel,
    ) -> Self {
        let function_tiling = function.tiling();
        // Application consumes the function's outermost level and leaves whatever sits
        // under it, so a keyed collection `B ⤇ C ⤇ D` applied at a `B` yields the `C ⤇ D`
        // beneath, which goes where the argument was: that is how the function's levels come
        // to sit under the input's.
        let (fn_domain_extent, fn_result) = match function_tiling {
            Tiling::DataFunction { domain, codomain } => (domain.clone(), (**codomain).clone()),
            other => (
                other
                    .domain_extent()
                    .unwrap_or_else(|| panic!("Map function had non-function tiling {other}")),
                other
                    .codomain()
                    .unwrap_or_else(|| panic!("Map function had non-function tiling {other}")),
            ),
        };

        let input_tiling = input.tiling();
        let arguments = input_tiling.values_at(level);
        // A function applied to an argument holding a collection as a tile yields its
        // codomain's collections as tiles too ([`Tiling::from_extent`]): the argument could
        // not have been boxed into a column, and neither can the result. A function's type
        // says only its codomain extent, which cannot draw that distinction on its own.
        let fn_result = if arguments.holds_a_level() {
            Tiling::from_extent(&fn_result.extent())
        } else {
            fn_result
        };
        // Subtyping, not equality: an argument whose extent is a *width subtype* of the
        // function's domain applies soundly. A variant with fewer tags is the case that makes
        // this observable — the function handles tags this argument never carries, and
        // projecting one of those simply yields nothing — but the same holds for a record
        // with extra fields. [`Extent::includes`] is the runtime statement of that rule.
        assert!(
            fn_domain_extent.includes(&arguments.extent()),
            "Cannot apply {function_tiling} to the values of {input_tiling} at {level}"
        );
        // The result takes the place of the argument it was applied to, which is where the
        // program applies it: a collection-valued argument is itself one, so its own levels
        // are not the iteration.
        let tiling = with_values_at(input_tiling, level, fn_result);
        Self {
            base: OperatorBase::new(tiling),
            input,
            function,
            level,
        }
    }
}

/// The values an application yields, given the function's values and, per output row, the
/// entries of the function that row's argument matched.
///
/// Applying at a key yields that key's values. Where those values are a level, the key's
/// group becomes a level of the output and several matched entries run together; where they
/// are a record over the function's own rows, the key names one row of it and there is
/// nothing to group.
fn gather_applied(values: &Tile, groups: &[Vec<usize>]) -> Tile {
    if values.is_data_function() {
        return values.regroup_rows(groups);
    }
    let rows: Vec<usize> = groups.iter().flatten().copied().collect();
    // `MapResultProducer::get_impl` withholds every argument outside the function's
    // `domain_predicate` before applying it. An argument inside the predicate that the
    // function does not hold lies outside its domain, which the argument's type excludes.
    assert_eq!(
        rows.len(),
        groups.len(),
        "a function whose values are a record answers each argument with exactly one row"
    );
    values.select_rows(&rows)
}

/// The keys an application looks up that the function has not called complete, each with the
/// complete input paths that look it up. `lookups` pairs each input path with the key it looks
/// up; `complete` is the input's statement over whole paths.
///
/// Beneath every other complete input path the looked-up key is complete in the function, so
/// everything gathered beneath it is complete, and [`restate_gathered`] states that with one
/// arm however many paths share it.
fn incomplete_lookups(
    lookups: impl Iterator<Item = (Vec<Value>, Value)>,
    complete: &Predicate,
    f_domain_predicate: &Predicate,
) -> Vec<(Value, Predicate)> {
    // Keys in the order they first appear, so the statement is spelled the same way each time.
    let mut by_key: Vec<(Value, Vec<Predicate>)> = Vec::new();
    for (path, key) in lookups {
        if !complete.contains_path(&path) || f_domain_predicate.contains(&key) {
            continue;
        }
        let path = Predicate::exactly(&path);
        match by_key.iter_mut().find(|(k, _)| *k == key) {
            Some((_, paths)) => paths.push(path),
            None => by_key.push((key, vec![path])),
        }
    }
    by_key
        .into_iter()
        .map(|(key, paths)| (key, Predicate::flatten_or(paths)))
        .collect()
}

/// A level of the function's values, gathered beneath the input's paths, restated over those
/// paths. `stated` is the level's statement over the function's paths, `depth` levels beneath
/// the function's key.
///
/// A gathered path is complete where the input path above it is complete and the function
/// calls complete what lies beneath the key that path looks up. Beneath a key the function
/// calls complete, that is everything; beneath one of `incomplete` (from
/// [`incomplete_lookups`]), it is the function's own statement within that key
/// ([`Predicate::within`]), qualified by the paths that look it up.
fn restate_gathered(
    stated: &Predicate,
    depth: usize,
    complete: &Predicate,
    incomplete: &[(Value, Predicate)],
) -> Predicate {
    let looking_up_incomplete = incomplete
        .iter()
        .fold(Predicate::False, |all, (_, paths)| all.union(paths));
    incomplete.iter().fold(
        Predicate::True.qualified_by(&complete.minus(&looking_up_incomplete), depth),
        |all, (key, paths)| {
            all.union(
                &stated
                    .within(std::slice::from_ref(key), depth)
                    .qualified_by(paths, depth),
            )
        },
    )
}

impl TileOperator for MapResult {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
        visit(value("fn", &*self.function));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let (shared, gate) = shared_consumer(consumer);
        let values_are_keys = self
            .input
            .result_correlation()
            .is_some_and(|path| path.is_empty())
            && matches!(
                self.input.tiling(),
                Tiling::DataFunction { codomain, .. } if !codomain.holds_a_level()
            );
        let function_producer = subscribe_forwarding(&mut *self.function, &shared, scheduler);
        // The result's outermost keys are the input's where the function applies to the input's
        // values, one level in, so the input's region is the result's. Applied to the input
        // itself, or to a scalar, the function's own keys are the result's. The function operand
        // is read at every key, so a change to it is a change to all of them, which
        // `subscribe_forwarding` sends as `Everything`.
        let keeps_keys =
            self.level != CurryLevel::OUTERMOST && self.input.tiling().is_data_function();
        let input_producer =
            subscribe_forwarding_keeping_keys_if(keeps_keys, &mut *self.input, &shared, scheduler);
        Box::new(MapResultProducer {
            base: ProducerBase::new(
                MapResultProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            )
            .sharing(gate),
            input: input_producer,
            function: function_producer,
            values_are_keys,
            level: self.level,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        if let Some(mut input_corr) = self.input.result_correlation()
            && let Some(transform) = self.function.result_correlation()
        {
            input_corr.extend(transform);
            return Some(input_corr);
        }
        None
    }
}

struct MapResultProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    function: Box<dyn TileProducer>,
    /// Whether each of the input's values is its own key: a one-level stream such as an
    /// iteration's positions, which the function is then looked up at.
    values_are_keys: bool,
    /// The level the arguments stand at.
    level: CurryLevel,
}

impl MapResultProducer {
    /// Whether a projection of the keys is also a projection of the function operand's keys: a
    /// one-level stream whose values are its keys, mapped one level in, over a collection
    /// operand. The keys a projection admits are then the keys the function is looked up at.
    /// Anywhere else the lookups are not known before the input is read, and the operand is
    /// read whole.
    fn projection_reaches_function(&self) -> bool {
        self.values_are_keys
            && self.level == CurryLevel::new(1)
            && self.function.tiling().is_data_function()
    }

    /// The function applied at every argument the input holds, for the keys `projection` names.
    fn apply(&mut self, projection: &Projection) -> Tile {
        let f_tiling = self.function.tiling().clone();
        assert!(
            f_tiling.has_domain(),
            "MapResult expected function tiling, Got {f_tiling:?}"
        );
        let f_extent = f_tiling.extent();
        let (f_domain_extent, f_codomain_extent) = f_extent.split_function().unwrap();
        let i_tiling = self.input.tiling().clone();
        // A scalar input is a key looked up in the function, and the keys the projection names
        // are the function's own: the input has none, so it is read whole and the answer cut.
        let input_guard = match i_tiling.is_data_function() {
            true => projection.guard(&i_tiling),
            false => i_tiling.universal_guard(),
        };

        let mut input_tile = self.input.get(input_guard);
        // Drop logically-deleted rows before mapping. Release marks rows deleted
        // rather than removing them (`Tile::remove_guarded`), and the paths below
        // carry the input's `domain` through to the output while building the
        // codomain only from live rows — so a tile still carrying deleted rows
        // yields a domain and codomain of different lengths, which is not a valid
        // tile. `Restrict` upstream produces the same shape. Mapping a filtered row
        // could evaluate the partial expression the filter guards, so the rows are
        // dropped rather than carried; no consumer sees them, so this releases them.
        let dropped = input_tile.deleted_keys_guard();
        input_tile.compact();
        if let Some(dropped) = dropped {
            self.input.release(dropped);
        }
        let function_guard = match projection {
            Projection::Keys(_) if self.projection_reaches_function() => {
                projection.guard(self.function.tiling())
            }
            _ => self.function.tiling().universal_guard(),
        };
        let function_tile = self.function.get(function_guard);

        // A function whose values are themselves a collection needs special-case handling:
        // the application adds a level, so it rebuilds the tile around it rather than
        // replacing its values. The shape is read through a borrow so a one-level operand
        // does not move the tile out of the fall-through path below.
        let function_is_nested = matches!(&function_tile, Tile::DataFunction { codomain, .. } if codomain.is_data_function());
        if function_is_nested
            && let Tile::DataFunction {
                domain: f_domain,
                codomain: f_groups,
                domain_predicate: f_domain_predicate,
                ..
            } = function_tile
        {
            // The function's levels below the one this application consumes become further
            // levels of the output, so the operand may be a keyed collection of any depth.

            // A **scalar** input is a single-key lookup — `groupby(c, k)(v)`. It is the walk
            // below at one key, yielding that key's subtree directly rather than a family of
            // them keyed by the input's domain.
            if let Tile::Scalar(key_col) = input_tile {
                // A key absent from a **settled** grouping is a genuinely empty group; one
                // absent from an unsettled grouping is simply not answered yet. Only
                // `domain_predicate` separates those, which is the same thing the stream
                // case's incomplete-domain set records.
                let key = (key_col.len() == 1).then(|| key_col.index_at(0));
                let settled = key.as_ref().is_some_and(|k| f_domain_predicate.contains(k));
                let rows: Vec<usize> = match key.filter(|_| settled) {
                    Some(k) => (0..f_domain.len())
                        .filter(|&i| f_domain.index_at(i) == k)
                        .collect(),
                    None => Vec::new(),
                };
                // One group: with no level above, the matching keys' groups run together
                // into the collection this application yields.
                let mut out = gather_applied(&f_groups, &[rows]);
                // Only a settled key's group is answered, and that group is final at every
                // depth; an unsettled key answers nothing yet, so every level says nothing.
                out.map_level_predicates(&mut |_, _| match settled {
                    true => Predicate::True,
                    false => Predicate::False,
                });
                return out;
            }

            let Tile::DataFunction {
                domain,
                codomain: input_codomain,
                domain_predicate,
                ..
            } = input_tile
            else {
                panic!("Expected a collection tile");
            };

            let codomain_values = match *input_codomain {
                Tile::Scalar(ref cv) => cv.clone(),
                _ => panic!("MapResult with Function only supports Scalar codomains"),
            };

            // Sort the domain so the output's outermost level is ordered.
            let mut sort_indices: Vec<usize> = (0..domain.len()).collect();
            sort_indices.sort_by(|&a, &b| {
                domain
                    .index_at(a)
                    .partial_cmp(&domain.index_at(b))
                    .expect("Cannot compare keys values")
            });
            let sorted_domain =
                domain.select_indices(sort_indices.iter().cloned(), sort_indices.len());
            let sorted_codomain_values =
                codomain_values.select_indices(sort_indices.iter().cloned(), sort_indices.len());

            // Index the function's outermost level so each row costs one lookup. A value may
            // repeat, and every one of its entries contributes its subtree.
            let mut f_index: HashMap<Value, Vec<usize>> = HashMap::new();
            for i in 0..f_domain.len() {
                f_index.entry(f_domain.index_at(i)).or_default().push(i);
            }

            let domain_extent = i_tiling.domain_extent().unwrap();
            let mut kept_rows: Vec<usize> = Vec::new();
            // One group per kept row: its value's entries in the function, whose groups run
            // together under it.
            let mut groups: Vec<Vec<usize>> = Vec::new();
            // Input domain values whose mapping the function has not answered: its
            // `domain_predicate` is false for the corresponding input codomain value.
            let mut incomplete_domain = ColumnValue::from_values(Vec::new(), &domain_extent);

            for i in 0..sorted_domain.len() {
                let codomain_value = sorted_codomain_values.index_at(i);
                if !f_domain_predicate.contains(&codomain_value) {
                    incomplete_domain.append(ColumnValue::from_values(
                        vec![sorted_domain.index_at(i)],
                        &domain_extent,
                    ));
                }

                if let Some(entries) = f_index.get(&codomain_value) {
                    kept_rows.push(i);
                    groups.push(entries.clone());
                }
            }

            let new_domain =
                sorted_domain.select_indices(kept_rows.iter().copied(), kept_rows.len());

            // The output predicate is the input's minus the values the function has not
            // answered. The obsolete region is excluded: there is not enough here to reason
            // about a region the consumer has already taken.
            let domain_obsolete = match self.input.obsolete_guard() {
                g if g.is_universal() => Predicate::True,
                TileGuard::Function(FunctionGuard::Domain(p)) => p.clone(),
                _ => Predicate::False,
            };
            let incomplete_predicate =
                Predicate::from_column_value(&incomplete_domain).minus(&domain_obsolete);
            let output_domain_predicate = domain_predicate.minus(&incomplete_predicate);
            // Each group states its completeness over the function's paths, beneath the
            // function's key. Placed under output row `x`, it is restated over `x`'s paths
            // ([`restate_gathered`]): complete where `x` is complete in the input and the
            // function calls complete what lies beneath `x`'s value. Every input row counts,
            // kept or not: a complete row whose value's group has not arrived is still
            // looked up, and its group arrives beneath it later.
            let incomplete = incomplete_lookups(
                (0..sorted_domain.len()).map(|i| {
                    (
                        vec![sorted_domain.index_at(i)],
                        sorted_codomain_values.index_at(i),
                    )
                }),
                &domain_predicate,
                &f_domain_predicate,
            );
            let mut applied = gather_applied(&f_groups, &groups);
            applied.map_level_predicates(&mut |depth, stated| {
                restate_gathered(stated, depth, &domain_predicate, &incomplete)
            });
            return Tile::data_function(
                new_domain,
                Box::new(applied),
                output_domain_predicate,
                BitSet::new(),
            );
        }

        // A data function may be applied before it has answered every key:
        // `domain_predicate` separates a key the function will never answer from one it has
        // not answered yet. A key whose argument the function has not answered is withheld —
        // dropped from this tile, and subtracted from its predicate — so the consumer pulls
        // again once the function has it. A whole value is withheld whole, as no rows, which
        // is a value not known yet. The nested branch above draws the same distinction
        // through `incomplete_domain`.
        if let Tile::DataFunction {
            domain_predicate: f_domain_predicate,
            ..
        } = &function_tile
            && let Tile::Scalar(argument) = &input_tile
            && argument.len() == 1
            && !f_domain_predicate.contains(&argument.index_at(0))
        {
            input_tile = Tile::Scalar(argument.select_indices(std::iter::empty(), 0));
        }
        if let Tile::DataFunction {
            domain_predicate: f_domain_predicate,
            ..
        } = &function_tile
            && input_tile.is_data_function()
        {
            let Tile::Scalar(arguments) = input_tile.values_at(self.level) else {
                panic!(
                    "MapResult over a function expects a scalar argument column, got {:?}",
                    input_tile.values_at(self.level)
                );
            };
            // The key path of every argument, so a withheld one can be taken out of every
            // level's statement: its row arrives later beneath each prefix of its path, so no
            // level may call that prefix complete. The arguments stand beneath the keys of
            // the level above them, so their paths are the rows one level further in.
            let innermost = self
                .level
                .index()
                .checked_sub(1)
                .unwrap_or_else(|| unreachable!("the input was matched as a collection"));
            let paths = input_tile.row_paths_at(innermost + 1);
            let mut keep = vec![true; arguments.len()];
            let mut withheld: Vec<&[Value]> = Vec::new();
            for (i, path) in paths.iter().enumerate() {
                if !f_domain_predicate.contains(&arguments.index_at(i)) {
                    keep[i] = false;
                    withheld.push(path);
                }
            }
            if !withheld.is_empty() {
                input_tile.withhold(CurryLevel::new(innermost), &keep, &withheld);
            }
        }

        // A function whose values hold a level under a record cannot be applied through a
        // column, which has nowhere to put one. The arguments name rows of the function's
        // values, so the application gathers those rows and puts them where the argument
        // column was — at whatever depth the input carries it, unlike the level-valued case
        // above, which adds a level and so rebuilds the tile around it.
        if let Tile::DataFunction {
            domain: f_keys,
            codomain: f_values,
            domain_predicate: f_domain_predicate,
            ..
        } = &function_tile
            && f_values.holds_a_level()
        {
            let Tile::Scalar(arguments) = input_tile.values_at(self.level) else {
                panic!(
                    "MapResult over a function expects a scalar argument column, got {:?}",
                    input_tile.values_at(self.level)
                )
            };
            let rows: HashMap<Value, usize> =
                (0..f_keys.len()).map(|i| (f_keys.index_at(i), i)).collect();
            let groups: Vec<Vec<usize>> = (0..arguments.len())
                .map(|i| {
                    rows.get(&arguments.index_at(i))
                        .copied()
                        .into_iter()
                        .collect()
                })
                .collect();
            let mut gathered = gather_applied(f_values, &groups);
            // Each gathered row states its levels' completeness over the function's paths,
            // beneath the function's key. Placed where its argument was, it is restated over
            // the argument's path ([`restate_gathered`]), as the level-valued case above does.
            match self.level.index().checked_sub(1) {
                Some(innermost) => {
                    let paths = input_tile.row_paths_at(innermost + 1);
                    let complete = input_tile.completion_at(CurryLevel::new(innermost));
                    let incomplete = incomplete_lookups(
                        paths
                            .into_iter()
                            .enumerate()
                            .map(|(i, path)| (path, arguments.index_at(i))),
                        &complete,
                        f_domain_predicate,
                    );
                    gathered.map_level_predicates(&mut |depth, stated| {
                        restate_gathered(stated, depth, &complete, &incomplete)
                    });
                }
                // A scalar argument is a lookup with no path above it, so each level states
                // what the function states within the key looked up.
                None => {
                    let keys: Vec<Value> = (0..arguments.len())
                        .map(|i| arguments.index_at(i))
                        .collect();
                    gathered.map_level_predicates(&mut |depth, stated| {
                        keys.iter().fold(Predicate::True, |all, key| {
                            match f_domain_predicate.contains(key) {
                                true => all,
                                false => {
                                    all.intersect(&stated.within(std::slice::from_ref(key), depth))
                                }
                            }
                        })
                    });
                }
            }
            *input_tile.values_at_mut(self.level) = gathered;
            return input_tile;
        }

        // An argument carrying a level cannot be materialized into a column, so a computable
        // function that takes one is applied to the tile instead ([`FunctionDef::apply_tile`]
        // — `insert`, whose collection operand reaches it opened).
        let level = self.level;
        let arguments = std::mem::replace(
            input_tile.values_at_mut(level),
            Tile::Scalar(ColumnValue::Units(0)),
        );
        *input_tile.values_at_mut(level) = if arguments.rows() == 0 {
            // **No rows, no application.** The result has a row per argument, so it is the
            // empty one whatever the function is, built from the tiling. Applying instead
            // reads the arguments as a column, and an argument holding a level that no
            // computable function takes has none: a record with a collection field, which is
            // a transaction body's row once a universal release has emptied it.
            self.tiling().values_at(level).empty_at_no_rows()
        } else if arguments.holds_a_level()
            && let Tile::Scalar(f) = &function_tile
            && let Some(Value::ComputableFunction(f)) = f.as_single()
        {
            f.apply_tile(arguments, f_domain_extent)
        } else {
            // Standard logic for non-Function outputs
            process_tile_result(self.tiling().values_at(level), arguments, move |values| {
                apply_function_tile(function_tile, values, f_domain_extent, f_codomain_extent)
            })
        };
        input_tile
    }
}

impl TileProducer for MapResultProducer {
    impl_producer_base!();

    /// Applied one level in, beneath the input's keys, the function's result takes the place of
    /// each value and the keys stay the input's, as `MapResult::subscribe` forwards them; applied
    /// to the input itself, the keys are the function's. The function is read at the values it is
    /// applied to.
    #[cfg(test)]
    fn input_keys(&self, role: &str) -> Option<InputKeys> {
        let keeps_keys =
            self.level != CurryLevel::OUTERMOST && self.input.tiling().is_data_function();
        match role {
            "input" => keeps_keys.then_some(InputKeys::Same),
            "fn" => Some(InputKeys::NotKeys),
            _ => None,
        }
    }

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("fn", &*self.function);
        visit("input", &*self.input);
    }

    #[cfg(test)]
    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("fn", &mut *self.function);
        visit("input", &mut *self.input);
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let mut out = self.apply(&projection);
        // Part of an output value released names no part of the input, so the input keeps
        // the row and the value is recomputed on the next pull (`release_impl`); what the
        // consumer let go is taken back out here.
        if !self.base.obsolete_guard.is_empty() {
            out.remove_guarded(self.base.obsolete_guard.clone());
        }
        // Mapping keeps the input's keys, so the input already answered the projection; the
        // cut states it for an input that answered more.
        out.restrict_to(&projection, self.tiling());
        out
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // A guard is shaped by the tiling it is handed to, so the input's is built
        // from the input's tiling — never from the function's, whose tiling is
        // unrelated (a function tiling, against the input's stream).
        // Mapping is position-preserving, so a region of the output's keys names that same
        // region of the input's; beneath them the output holds the function's values, not the
        // input's arguments. The levels above the arguments are the ones the two sides share.
        let input = self.input.tiling();
        let upstream_guard = crate::interpreter::tiling::through_shared_levels(
            obsolete_guard,
            self.level.index(),
            input,
        );
        let done = upstream_guard.is_universal();
        // Where a projection reached the function, the keys a released data region named are
        // the keys it was looked up at, and are looked up no more.
        if !done
            && self.projection_reaches_function()
            && matches!(
                upstream_guard,
                TileGuard::Function(FunctionGuard::Domain(_))
            )
        {
            self.function.release(upstream_guard.clone());
        }
        self.input.release(upstream_guard);
        // The **function** is re-read on every pull, so it can only be released
        // once there will be no next pull — which is what a universal release from
        // the consumer says. Releasing it on a narrower guard would leave the next
        // pull mapping over an emptied function; never releasing it strands whatever
        // produces it, and a function operand is not always a small `Constant` (a
        // UDF's materialized table lives here too).
        if done {
            self.function
                .release(self.function.tiling().universal_guard());
        }
    }
}

/// Takes a function input and returns a function with the same structure
/// but with a constant swapped or zipped in for its values at one level, as determined by
/// the [`MapResultToConstMode`] param.
///
/// The level is the caller's to state ([`MapResultToConst::new_at`]), as
/// [`MapResult`]'s is: a value at it may be a collection of its own, whose levels are part
/// of the value rather than of the iteration.
///
/// A collection constant streams: each row holds what has arrived of it, and no row is
/// complete until it is. Every row reads all of it, so it is released once everything is.
pub struct MapResultToConst {
    /// Output tiling matches `input` tiling, with the values at `level` transformed.
    base: OperatorBase,
    /// The function input to iterate over.
    input: Box<dyn TileOperator>,
    /// The constant to apply to each element.
    constant: Box<dyn TileOperator>,
    /// Whether to zip with the constant instead of replacing with the constant.
    mode: MapResultToConstMode,
    /// The level whose values the constant replaces or pairs with.
    level: CurryLevel,
}

/// The type fof MapResultToConst operation to perform
#[derive(Debug, Clone, Copy)]
pub enum MapResultToConstMode {
    /// Replace the codomain with the constant
    Replace,
    /// Replace the codomain x with (constant, x)
    ZipLeft,
    /// Replace the codomain x with (x, constant)
    ZipRight,
}

impl MapResultToConst {
    /// Replace, or pair with the constant, each of `input`'s values at `level`: the
    /// iteration the node sits in, which the caller states from where it is in the program.
    pub fn new_at(
        input: Box<dyn TileOperator>,
        constant: Box<dyn TileOperator>,
        mode: MapResultToConstMode,
        level: CurryLevel,
    ) -> Self {
        let values = input.tiling().values_at(level).clone();
        let constant_tiling = constant.tiling().clone();
        let result = match mode {
            MapResultToConstMode::Replace => constant_tiling,
            MapResultToConstMode::ZipLeft => Tiling::tuple(&[constant_tiling, values]),
            MapResultToConstMode::ZipRight => Tiling::tuple(&[values, constant_tiling]),
        };
        let tiling = with_values_at(input.tiling(), level, result);
        Self {
            base: OperatorBase::new(tiling),
            input,
            constant,
            mode,
            level,
        }
    }
}

impl TileOperator for MapResultToConst {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        visit(value("input", &*self.input));
        visit(value("constant", &*self.constant));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let (shared, gate) = shared_consumer(consumer);
        let constant_producer = subscribe_forwarding(&mut *self.constant, &shared, scheduler);
        // The constant is read whole, since every row reads all of it, so its notification
        // widens; the input is pulled at the projection.
        let keeps_keys =
            self.level != CurryLevel::OUTERMOST && self.input.tiling().is_data_function();
        let input_producer =
            subscribe_forwarding_keeping_keys_if(keeps_keys, &mut *self.input, &shared, scheduler);
        Box::new(MapResultToConstProducer {
            base: ProducerBase::new(
                MapResultToConstProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            )
            .sharing(gate),
            input: input_producer,
            constant: constant_producer,
            mode: self.mode,
            level: self.level,
        })
    }
}

struct MapResultToConstProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    constant: Box<dyn TileProducer>,
    mode: MapResultToConstMode,
    level: CurryLevel,
}

impl MapResultToConstProducer {
    /// No rows, stating what `input` states except beneath the paths holding a live row.
    ///
    /// Each output value is the input's value at its path paired with the constant, so a
    /// path the input calls complete is complete here once the constant is terminal. A path
    /// holding no live row depends on nothing else: a filtered row never reaches the output
    /// and a missing one never arrives. A path holding a live row gains that row once the
    /// constant is terminal, so until then no level calls it complete
    /// (`src/interpreter/design-operators.md`, "The completeness contract").
    fn empty_beneath_live_rows(&self, input: &Tile) -> Tile {
        let mut out = self.tiling().empty_tile();
        for level in (0..self.level.index()).map(CurryLevel::new) {
            let (
                Tile::DataFunction {
                    domain_predicate: stated,
                    ..
                },
                Tile::DataFunction {
                    domain_predicate: out_stated,
                    ..
                },
            ) = (input.values_at(level), out.values_at_mut(level))
            else {
                unreachable!("MapResultToConst keeps its input's collection levels")
            };
            *out_stated = stated.clone();
        }
        self.open_live_rows(&Self::live_paths(input, self.level), &mut out);
        out
    }

    /// The path of every live row of `input` at each level above `level`, as one predicate
    /// per level.
    fn live_paths(input: &Tile, level: CurryLevel) -> Vec<Predicate> {
        let mut live = input.clone();
        live.compact();
        (0..level.index())
            .map(|depth| live.paths_predicate(CurryLevel::new(depth)))
            .collect()
    }

    /// Leave every path in `live` (one predicate per level above `self.level`) out of what
    /// `out`'s levels call complete. The levels the output shares with the input are the ones
    /// above `self.level`, since the constant replaces or pairs with what sits there; a
    /// collection constant adds levels of its own beneath those, and nothing in the input
    /// names them.
    fn open_live_rows(&self, live: &[Predicate], out: &mut Tile) {
        for (depth, held) in live.iter().enumerate() {
            let Tile::DataFunction {
                domain_predicate, ..
            } = out.values_at_mut(CurryLevel::new(depth))
            else {
                unreachable!("MapResultToConst keeps its input's collection levels")
            };
            if *held != Predicate::False {
                *domain_predicate = domain_predicate.minus(held);
            }
        }
    }
}

impl TileProducer for MapResultToConstProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
        visit("constant", &*self.constant);
    }

    #[cfg(test)]
    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("input", &mut *self.input);
        visit("constant", &mut *self.constant);
    }

    /// The input is pulled at the projection, since each output row is the input's row paired
    /// with the constant. The constant is read whole: every row reads all of it.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }

        self.apply(&projection)
    }

    /// The input shares the output's levels down to `level`, and beneath them the output
    /// holds the constant too, so only a release naming a whole value there reaches the
    /// input ([`through_shared_levels`]): the output is rebuilt from the input's rows on
    /// every pull, and a row the input gave back could not be rebuilt for what of it is still
    /// held here.
    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let upstream = crate::interpreter::tiling::through_shared_levels(
            obsolete_guard,
            self.level.index(),
            self.input.tiling(),
        );
        let done = upstream.is_universal();
        self.input.release(upstream);
        // The constant is re-read on every pull, and every row reads all of it, so it is
        // released once there will be no next pull, which is what a universal release says.
        if done {
            self.constant
                .release(self.constant.tiling().universal_guard());
        }
    }
}

impl MapResultToConstProducer {
    /// The output for the keys `projection` names.
    fn apply(&mut self, projection: &Projection) -> Tile {
        let c_tiling = self.constant.tiling();
        assert!(
            !matches!(c_tiling, Tiling::Aggregation { .. } | Tiling::Store { .. }),
            "MapResultToConst broadcasts a value, got {c_tiling:?}"
        );
        let i_tiling = self.input.tiling().clone();
        // A scalar input has no keys to project, so it is read whole and the answer cut. Applied
        // at the outermost level the constant replaces the whole input, so the output's keys are
        // the constant's and the projection names none of the input's.
        let input_guard = match i_tiling.is_data_function() && self.level != CurryLevel::OUTERMOST {
            true => projection.guard(&i_tiling),
            false => i_tiling.universal_guard(),
        };
        let input_tile = self.input.get(input_guard);
        // **Laziness — do not evaluate an off-path arm.** In the scalar value-`Case`
        // C-form a false first-match gate empties this arm's `Units(1)` driver — the
        // `Restrict` marks the driver row *deleted* rather than dropping it. When
        // every driver row is deleted, the arm contributes no live rows, so the
        // constant's value is never observed. Crucially we must not *pull* it: the
        // arm's value may be a partial expression (`//`, `%`, an index) the gate
        // exists to guard, and pulling it would evaluate e.g. `x // 0` and panic.
        // The data-collection fan-out is lazy the same way (an emptied restrict is never
        // iterated); this brings the scalar form in line.
        if input_tile.is_data_function() && input_tile.is_empty() {
            // The empty tile below drops the input's deleted rows, which no consumer then
            // sees, so this releases them.
            if let Some(dropped) = input_tile.deleted_keys_guard() {
                self.input.release(dropped);
            }
            return self.empty_beneath_live_rows(&input_tile);
        }
        let streams = c_tiling.is_data_function();
        let constant_guard = c_tiling.universal_guard();
        let constant_tile = self.constant.get(constant_guard);
        // A **scalar** constant must be fully known before it is replicated across the
        // input's domain: `repeat` fabricates nothing, it copies a single present value. A
        // constant that is still absent (e.g. a scalar read from a sibling induction loop
        // that has not yet converged) yields an empty output — the consumer re-pulls once it
        // lands, rather than us inventing a value for the unknown positions.
        //
        // This is one half of a single invariant — "never fabricate a position from a
        // not-yet-converged sibling read." The other half is the co-presence truncate in
        // `binop::zip_arithmetic`/`zip_concat`: a binop over a lagging operand combines only
        // the common prefix instead of returning the longer side's tail. Keep the two in step.
        //
        // A **collection** constant fabricates nothing by streaming: it states which of its
        // keys are complete, so each row is handed what it holds so far, and a row is complete
        // only once the constant is ([`Self::open_live_rows`]).
        if !constant_tile.is_terminal() && !streams {
            return match input_tile.is_data_function() {
                true => self.empty_beneath_live_rows(&input_tile),
                false => self.tiling().empty_tile(),
            };
        }
        let growing =
            (!constant_tile.is_terminal()).then(|| Self::live_paths(&input_tile, self.level));

        let mode = self.mode;
        // A collection constant repeated down a column states each copy's completeness without
        // knowing which row holds it, so it is qualified by the rows that do
        // (`src/interpreter/design-operators.md`, "The completeness contract").
        let held = self
            .level
            .enclosing()
            .map(|rows| input_tile.paths_predicate(rows));
        // Stated over tiles rather than columns: `Replace` never reads the values, and the
        // two `Zip` modes pair with them whatever they carry — a level included, which a
        // column has nowhere to put.
        let mut output = input_tile;
        let slot = output.values_at_mut(self.level);
        let values = std::mem::replace(slot, Tile::Scalar(ColumnValue::Units(0)));
        let mut const_tile = repeat_tile(constant_tile, values.rows());
        if let Some(held) = &held {
            const_tile.map_level_predicates(&mut |depth, pred| pred.qualified_by(held, depth));
        }
        *slot = match mode {
            MapResultToConstMode::Replace => const_tile,
            MapResultToConstMode::ZipLeft => Tile::tuple(vec![const_tile, values]),
            MapResultToConstMode::ZipRight => Tile::tuple(vec![values, const_tile]),
        };
        if let Some(live) = &growing {
            self.open_live_rows(live, &mut output);
        }
        // Each row is rebuilt from the input and the constant on every pull, so what a
        // consumer has released beneath a row still open comes back unless it is left out.
        output.remove_guarded(self.obsolete_guard().clone());
        output
    }
}
/// The extent of the leaves at `paths` of a source's values, given the extent of the values: the
/// values' own for no paths, one leaf's extent for one, and for several the record of their
/// extents under the component names of a tuple.
fn projected_extent(paths: &[FieldPath], values: Extent) -> Extent {
    if paths.is_empty() {
        return values;
    }
    let leaf = |path: &FieldPath| values.at_path(path).clone();
    match paths {
        [path] => leaf(path),
        paths => Extent::Record(
            paths
                .iter()
                .enumerate()
                .map(|(n, path)| (tuple_field(n), leaf(path)))
                .collect(),
        ),
    }
}

/// Produces a `DataFunction` tile that maps each domain element of a data
/// source to its corresponding output value.
///
/// Unlike [`IterateExtent`], which produces an identity function (domain→domain),
/// `MapResultWithSource` calls [`DataSourceDomainExtentImpl::get`] for each domain key to
/// look up the actual output value.  The result is
/// `DataFunction { domain: keys, codomain: Scalar(output_values) }`.
///
/// Notification at subscription time: if the source already has data when
/// `subscribe` is called, the consumer is notified immediately.
pub struct MapResultWithSource {
    input: Box<dyn TileOperator>,
    /// The data source providing both domain keys and value lookup.
    source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    /// The paths to the leaves of the source's values this reads, none for the whole value
    /// ([`DataSourceDomainExtentImpl::get_fields`]).
    fields: Vec<FieldPath>,
    /// Output tiling:
    /// `DataFunction { domain: DataSourceDomain, codomain: Scalar(output_value_extent) }`,
    /// where the extent is that of the leaves at `fields` of the value ([`projected_extent`]).
    base: OperatorBase,
}

impl MapResultWithSource {
    /// Create a new `MapResultWithSource` wrapping `source`.
    ///
    /// The output tiling is derived from the source's
    /// [`output_value_extent`](DataSourceDomainExtentImpl::output_value_extent).
    pub fn new(
        source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
        input: Box<dyn TileOperator>,
    ) -> Self {
        Self::projecting(source, input, Vec::new())
    }

    /// [`new`](Self::new) reading only the leaves at `fields` of the source's values: the whole
    /// value for none, that leaf alone for one, and the tuple of them for several.
    pub fn projecting(
        source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
        input: Box<dyn TileOperator>,
        fields: Vec<FieldPath>,
    ) -> Self {
        let source_domain_extent = Extent::DataSourceDomain(source.clone());
        let output_extent = projected_extent(&fields, source.borrow().output_value_extent());
        let tiling = change_tiling_result(input.tiling(), move |codomain_extent| {
            assert_eq!(source_domain_extent, *codomain_extent);
            Tiling::Scalar(output_extent)
        });
        Self {
            base: OperatorBase::new(tiling),
            input,
            source: source.clone(),
            fields,
        }
    }
}

impl TileOperator for MapResultWithSource {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        // The source is read here and states no edge: it is not a node of the
        // graph, and `input` descends from the `IterateExtent` over its domain.
        visit(value("input", &*self.input));
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // The input is pulled at the projection, so its output keys are the input's.
        let input =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(MapResultWithSourceProducer::new(
            ProducerBase::new(
                MapResultWithSourceProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            input,
            self.source.clone(),
            self.fields.clone(),
            self.input.result_correlation(),
        ))
    }
}

/// Producer for [`MapResultWithSource`]: maps each domain key to its output value on `get`.
struct MapResultWithSourceProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    /// The data source used for both domain enumeration and value lookup.
    source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    /// The paths to the leaves of the source's values this reads
    /// ([`MapResultWithSource::projecting`]).
    fields: Vec<FieldPath>,
    /// A correlation between the result values and some piece of the domain of the input tile.
    /// We need this in order to translate domain obsolete guards into releases of the underlying
    /// source.
    ///
    /// `None` where the input states none, as a pairing does: each of its rows reads every
    /// key the inner side holds, so no release short of the whole one frees a source row,
    /// and the source is held until then.
    result_correlation: Option<Vec<TilePathStep>>,
    /// What the input last read holds, where it holds a level beneath its keys: a release
    /// naming paths beneath particular keys is read against it
    /// ([`Self::released_beneath_every_key`]).
    last_nested_input: Option<HeldBeneathKeys>,
}

/// The parts of a two-level input a release beneath particular keys is read against, kept
/// in place of the input itself so a pull does not copy its values.
struct HeldBeneathKeys {
    /// The outermost level's own completeness.
    outer_stated: Predicate,
    /// The inner level's own completeness.
    inner_stated: Predicate,
    /// Which inner paths are complete, from any level on the path ([`Tile::completion_at`]).
    complete: Predicate,
    /// The outermost keys, each as its one-component path.
    outer_keys: Vec<Vec<Value>>,
    /// The path of every inner key.
    inner_paths: Vec<Vec<Value>>,
}

impl HeldBeneathKeys {
    /// What `input` holds beneath its keys, or `None` for an input that is not a two-level
    /// collection.
    fn of(input: &Tile) -> Option<Self> {
        let Tile::DataFunction {
            domain_predicate: outer_stated,
            ..
        } = input
        else {
            return None;
        };
        let Tile::DataFunction {
            domain_predicate: inner_stated,
            ..
        } = input.values_at(CurryLevel::new(1))
        else {
            return None;
        };
        Some(HeldBeneathKeys {
            outer_stated: outer_stated.clone(),
            inner_stated: inner_stated.clone(),
            complete: input.completion_at(CurryLevel::new(1)),
            outer_keys: input.paths_at(CurryLevel::OUTERMOST),
            inner_paths: input.paths_at(CurryLevel::new(1)),
        })
    }
}

impl MapResultWithSourceProducer {
    fn new(
        base: ProducerBase,
        input: Box<dyn TileProducer>,
        source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
        fields: Vec<FieldPath>,
        result_correlation: Option<Vec<TilePathStep>>,
    ) -> Self {
        let result = Self {
            base,
            input,
            source,
            fields,
            result_correlation,
            last_nested_input: None,
        };
        // Register this producer with the source by calling release with a false predicate.
        // This way the source knows about all producers that read it before execution starts.
        // This prevents sources from deleting data that a producer it doesn't know about yet might
        // need.
        result
            .source
            .borrow_mut()
            .release(&result.name(), Predicate::False);
        result
    }
}

impl MapResultWithSourceProducer {
    /// The inner keys a release of paths `[k, d]` frees for good: those released beneath
    /// every outer key, since the source row a value reads is read wherever that key stands.
    ///
    /// An unqualified release already says the same beneath every outer key. Otherwise `d` is
    /// free once every path this producer holds through `d` is released — by this release or
    /// an earlier one, so the accumulated `obsolete_guard` is what is read — and no path
    /// through `d` can still arrive: the input calls `d` complete beneath every outer key,
    /// either unqualified at the inner level or beneath each outer key of a complete outer
    /// level ([`Tile::completion_at`]).
    fn released_beneath_every_key(&self, pred: &Predicate) -> Predicate {
        let everywhere = pred.unqualified_arms();
        if !pred.qualifies() {
            return everywhere;
        }
        let Some(HeldBeneathKeys {
            outer_stated,
            inner_stated,
            complete,
            outer_keys,
            inner_paths,
        }) = &self.last_nested_input
        else {
            // Nothing pulled yet, so nothing is held beneath a key for a qualified arm to name.
            return everywhere;
        };
        let complete_under_every_key = inner_stated.unqualified_arms();
        let released = &self.base.obsolete_guard;
        let mut all_released: Vec<(Value, bool)> = Vec::new();
        for path in inner_paths {
            let key = path[path.len() - 1].clone();
            let covered = released.covers_path(path);
            match all_released.iter_mut().find(|(k, _)| *k == key) {
                Some((_, all)) => *all &= covered,
                None => all_released.push((key, covered)),
            }
        }
        all_released
            .into_iter()
            .filter(|(key, all)| {
                *all && (complete_under_every_key.contains(key)
                    || (outer_stated.is_true()
                        && outer_keys
                            .iter()
                            .all(|outer| complete.contains_path(&[outer[0].clone(), key.clone()]))))
            })
            .fold(everywhere, |all, (key, _)| {
                all.union(&Predicate::point(key))
            })
    }
}

impl TileProducer for MapResultWithSourceProducer {
    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("input", &*self.input);
    }

    #[cfg(test)]
    fn visit_input_producers_mut(&mut self, visit: &mut dyn FnMut(&str, &mut dyn TileProducer)) {
        visit("input", &mut *self.input);
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new(self.name())
            .annotate(self.source.borrow().get_id().to_string())
            .with_tiling(self.tiling().to_string())
            .child("input", self.input.inspect(opts))
    }

    /// The source is read at the keys the input answers, and the input is pulled at the
    /// projection, so a morsel reads only its own rows from the source.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let projection = projection_guard.projection(&self.name());
        if projection == Projection::Nothing {
            return self.tiling().empty_tile();
        }
        let input_tile = self.input.get(projection.guard(self.input.tiling()));
        if self.input.tiling().levels() > 1 {
            self.last_nested_input = HeldBeneathKeys::of(&input_tile);
        }
        let source = self.source.borrow();
        let fields = &self.fields;

        process_tile_result(self.tiling(), input_tile, move |codomain| {
            source.get_fields(codomain, fields)
        })
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let Some(correlation) = self.result_correlation.clone() else {
            if obsolete_guard.is_universal() {
                self.source
                    .borrow_mut()
                    .release(&self.name(), Predicate::True);
            }
            self.input.release(obsolete_guard);
            return;
        };
        match &obsolete_guard {
            TileGuard::Function(FunctionGuard::Domain(pred)) => {
                let extracted_pred = extract_predicate(pred, &correlation).clone();
                self.source
                    .borrow_mut()
                    .release(&self.name(), extracted_pred);
            }
            TileGuard::Function(FunctionGuard::Codomain(g))
                if matches!(**g, TileGuard::Function(FunctionGuard::Domain(_))) =>
            {
                if let TileGuard::Function(FunctionGuard::Domain(pred)) = &**g {
                    assert_eq!(correlation.first(), Some(&TilePathStep::Codomain));
                    // `released_beneath_every_key` reads the release at the level one beneath
                    // the outermost, which is where a source correlated through one codomain
                    // step stands. One correlated deeper has no reading here yet.
                    assert!(
                        !correlation[1..].contains(&TilePathStep::Codomain),
                        "a release beneath particular keys reaches a source correlated more \
                         than one level in, which nothing reads yet: {correlation:?}"
                    );
                    let keys = self.released_beneath_every_key(pred);
                    let extracted_pred = extract_predicate(&keys, &correlation[1..]).clone();
                    self.source
                        .borrow_mut()
                        .release(&self.name(), extracted_pred);
                }
            }
            g if g.is_universal() => {
                self.source
                    .borrow_mut()
                    .release(&self.name(), Predicate::True);
            }
            g if g.is_empty() => {}
            _ => panic!(
                "MapResultWithSourceProducer::release expected Domain or Universal guard, got {obsolete_guard:?}"
            ),
        }
        self.input.release(obsolete_guard);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{ReleaseSpy, TestTileProducer};
    use bit_set::BitSet;

    use crate::interpreter::{BaseType, ColumnValue, Extent, Value};

    /// Build a `MapResultProducer` whose `function` operand records its releases.
    fn map_result_with_function_spy() -> (MapResultProducer, Rc<RefCell<Vec<TileGuard>>>, Tiling) {
        let in_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let fn_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );
        let (fn_spy, released) = ReleaseSpy::new(
            Tile::data_function(
                ColumnValue::UInts(vec![0]),
                Box::new(Tile::grouped(
                    vec![0],
                    ColumnValue::UInts(vec![1]),
                    Box::new(Tile::Scalar(ColumnValue::UInts(vec![1]))),
                    Predicate::False,
                    BitSet::new(),
                )),
                Predicate::True,
                BitSet::new(),
            ),
            fn_tiling,
        );
        let input = TestTileProducer::new(
            Tile::data_function(
                ColumnValue::from_uints(vec![0]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![1]))),
                Predicate::True,
                BitSet::new(),
            ),
            in_tiling.clone(),
        );
        let producer = MapResultProducer {
            base: ProducerBase::unowned(MapResultProducer::alloc_id(), &in_tiling),
            input: Box::new(input),
            function: Box::new(fn_spy),
            values_are_keys: false,
            level: CurryLevel::new(1),
        };
        (producer, released, in_tiling)
    }

    /// The function operand is re-read on **every** pull, so it can only be
    /// released once there will be no next pull — which is what a universal release
    /// from the consumer says. Never releasing it strands whatever produces it, and
    /// a function operand is not always a small `Constant`.
    #[test]
    fn map_result_releases_its_function_when_the_consumer_is_done() {
        let (mut producer, released, tiling) = map_result_with_function_spy();
        producer.release(tiling.universal_guard());
        assert!(
            released.borrow().iter().any(|g| g.is_universal()),
            "a universal release means no further pull, so the function is free: {:?}",
            released.borrow()
        );
    }

    /// A narrower release must *not* reach the function: the next pull still needs
    /// it, and an emptied function would leave that pull mapping over nothing.
    #[test]
    fn map_result_keeps_its_function_for_a_narrower_release() {
        let (mut producer, released, _) = map_result_with_function_spy();
        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::at_or_below(Value::UInt(0)),
        )));
        assert!(
            released.borrow().is_empty(),
            "the function is still being read: {:?}",
            released.borrow()
        );
    }

    #[test]
    fn map_result_producer_two_levels() {
        // Test MapResultProducer directly with unsorted domain input
        // This tests the actual MapResultProducer.get_impl implementation

        // Create a DataFunction tile
        let two_level_fn_tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::UInts(vec![10, 20, 30]),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![100, 200, 300]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );

        let function_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );

        // Create a DataFunction tile with unsorted domain
        let one_level_fn_tile = Tile::data_function(
            ColumnValue::UInts(vec![2, 0, 1]),
            Box::new(Tile::Scalar(ColumnValue::UInts(vec![1, 0, 1]))),
            Predicate::True,
            BitSet::new(),
        );

        let input_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );

        // Create test producers
        let function_producer = TestTileProducer::new(two_level_fn_tile, function_tiling);
        let input_producer = TestTileProducer::new(one_level_fn_tile, input_tiling);

        // Create MapResultProducer and test it
        let output_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );

        let mut map_result = MapResultProducer {
            base: ProducerBase::unowned(MapResultProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
            function: Box::new(function_producer),
            values_are_keys: false,
            level: CurryLevel::new(1),
        };

        // Get the result from MapResultProducer
        let result = map_result.get(map_result.tiling().universal_guard());

        // Verify the result
        match result {
            Tile::DataFunction {
                domain: ref domain1,
                codomain: ref groups,
                ..
            } => {
                let Tile::DataFunction {
                    row_starts: offsets,
                    domain: domain2,
                    codomain,
                    ..
                } = groups.as_ref()
                else {
                    panic!("expected two levels")
                };
                let codomain = scalar_tile_to_column_value((**codomain).clone());
                // After sorting unsorted input {2, 0, 1} with codomain {1, 0, 1},
                // we get sorted {0, 1, 2} with codomain {0, 1, 1}
                assert_eq!(domain1.len(), 3, "domain1 should have 3 elements");
                assert_eq!(offsets.len(), 3, "offsets should have 3 elements");
                assert_eq!(domain2.len(), 4, "domain2 should have 4 elements");
                assert_eq!(codomain.len(), 4, "codomain should have 4 elements");

                // Verify domain1 is sorted: [0, 1, 2]
                if let ColumnValue::UInts(d1) = domain1 {
                    assert_eq!(*d1, vec![0, 1, 2], "domain1 should be sorted");
                } else {
                    panic!("domain1 should be UInts");
                }

                // Verify offsets: [0, 2, 3]
                assert_eq!(*offsets, vec![0, 2, 3], "offsets should be [0, 2, 3]");

                // Verify domain2: [10, 20, 30, 30]
                if let ColumnValue::UInts(d2) = domain2 {
                    assert_eq!(
                        *d2,
                        vec![10, 20, 30, 30],
                        "domain2 should be [10, 20, 30, 30]"
                    );
                } else {
                    panic!("domain2 should be UInts");
                }

                // Verify codomain: [100, 200, 300, 300]
                if let ColumnValue::UInts(cod) = codomain {
                    assert_eq!(
                        cod,
                        vec![100, 200, 300, 300],
                        "codomain should be [100, 200, 300, 300]"
                    );
                } else {
                    panic!("codomain should be UInts");
                }
            }
            _ => panic!("Expected a collection result"),
        }
    }

    /// Verifies that the output `domain_predicate` of `MapResultProducer` (Function
    /// branch) is derived correctly from the input predicate.
    ///
    /// Setup:
    ///   `input`: Function: domain=[0,1,2,3], codomain=[0,1,2,3], domain_predicate=True
    ///   `function`: Function:
    ///     domain1=[0, 1]       –- no info for 2 and 3
    ///     domain_predicate = Intervals covering only 0
    ///
    /// Expected output domain_predicate:
    ///   Only 0 is true for `function`'s domain_predicate, so only the preimage of 0 in
    ///   `input` (i.e. {0}), should be true in the output domain_predicate.
    #[test]
    fn map_result_producer_two_levels_domain_predicate() {
        let f_pred = Predicate::from_column_value(&ColumnValue::UInts(vec![0]));
        let two_level_fn_tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 1],
                ColumnValue::UInts(vec![10, 20]),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![100, 200]))),
                Predicate::False,
                BitSet::new(),
            )),
            f_pred,
            BitSet::new(),
        );
        let function_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );

        let one_level_fn_tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1, 2, 3]),
            Box::new(Tile::Scalar(ColumnValue::UInts(vec![0, 1, 2, 3]))),
            Predicate::True,
            BitSet::new(),
        );
        let input_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );

        let output_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );
        let mut map_result = MapResultProducer {
            base: ProducerBase::unowned(MapResultProducer::alloc_id(), &output_tiling),
            input: Box::new(TestTileProducer::new(one_level_fn_tile, input_tiling)),
            function: Box::new(TestTileProducer::new(two_level_fn_tile, function_tiling)),
            values_are_keys: false,
            level: CurryLevel::new(1),
        };

        let result = map_result.get(map_result.tiling().universal_guard());

        let Tile::DataFunction {
            domain,
            domain_predicate: out_pred,
            ..
        } = result
        else {
            panic!("Expected a collection");
        };

        // Only x=0 and x=1 have entries in the output (y=2,3 absent from the function).
        let ColumnValue::UInts(d1_vals) = &domain else {
            panic!("domain1 should be UInts");
        };
        assert_eq!(*d1_vals, vec![0, 1], "only x=0,1 should appear in domain1");

        assert!(
            out_pred.contains(&Value::UInt(0))
                && !out_pred.contains(&Value::UInt(1))
                && !out_pred.contains(&Value::UInt(2))
                && !out_pred.contains(&Value::UInt(3)),
            "Incorrect pred {out_pred:?}"
        );
    }

    /// When f_domain_predicate is True the output domain_predicate should equal the input's.
    #[test]
    fn map_result_producer_two_levels_domain_predicate_both_true() {
        let two_level_fn_tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 1],
                ColumnValue::UInts(vec![10, 20]),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![100, 200]))),
                Predicate::False,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let function_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );
        let one_level_fn_tile = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::UInts(vec![0, 1]))),
            Predicate::True,
            BitSet::new(),
        );
        let input_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );
        let output_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );
        let mut map_result = MapResultProducer {
            base: ProducerBase::unowned(MapResultProducer::alloc_id(), &output_tiling),
            input: Box::new(TestTileProducer::new(one_level_fn_tile, input_tiling)),
            function: Box::new(TestTileProducer::new(two_level_fn_tile, function_tiling)),
            values_are_keys: false,
            level: CurryLevel::new(1),
        };
        let result = map_result.get(map_result.tiling().universal_guard());
        let Tile::DataFunction {
            domain_predicate: out_pred,
            ..
        } = result
        else {
            panic!("Expected a collection");
        };
        assert_eq!(
            out_pred,
            Predicate::True,
            "both predicates True → output should be True (terminal)"
        );
    }

    /// A function whose values are a record holding a collection, applied over a streaming
    /// input: the gathered collection is restated beneath each input row it lands under,
    /// so it states nothing beneath a row the input has not called complete, and the pull that
    /// brings that row keeps the completeness contract.
    #[test]
    fn a_record_valued_function_states_nothing_beneath_an_incomplete_row() {
        use crate::interpreter::tile_operators::test_helpers::ScriptedProducer;
        let uint = || Extent::Base(BaseType::UInt);
        let value_tiling = Tiling::Record(HashMap::from([
            ("n".into(), Tiling::Scalar(Extent::Base(BaseType::Int))),
            (
                "xs".into(),
                Tiling::data_function(uint(), Tiling::Scalar(uint())),
            ),
        ]));
        let fn_tiling = Tiling::data_function(uint(), value_tiling.clone());
        let in_tiling = Tiling::data_function(uint(), Tiling::Scalar(uint()));
        let out_tiling = Tiling::data_function(uint(), value_tiling);
        // f = {5 ↦ (n: 1, xs: [7 ↦ 70])}, complete at every level.
        let f = Tile::data_function(
            ColumnValue::UInts(vec![5]),
            Box::new(Tile::record(HashMap::from([
                ("n".into(), Tile::Scalar(ColumnValue::Ints(vec![1]))),
                (
                    "xs".into(),
                    Tile::grouped(
                        vec![0],
                        ColumnValue::UInts(vec![7]),
                        Box::new(Tile::Scalar(ColumnValue::UInts(vec![70]))),
                        Predicate::True,
                        BitSet::new(),
                    ),
                ),
            ]))),
            Predicate::True,
            BitSet::new(),
        );
        // Every input row holds argument 5, and the rows through `upto` are complete.
        let input_at = |keys: Vec<u64>, upto: u64| {
            let n = keys.len();
            Tile::data_function(
                ColumnValue::UInts(keys),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![5; n]))),
                Predicate::at_or_below(Value::UInt(upto)),
                BitSet::new(),
            )
        };
        let (input, next) = ScriptedProducer::new(input_at(vec![0], 0), in_tiling);
        let mut producer = MapResultProducer {
            base: ProducerBase::unowned(MapResultProducer::alloc_id(), &out_tiling),
            input: Box::new(input),
            function: Box::new(TestTileProducer::new(f, fn_tiling)),
            values_are_keys: false,
            level: CurryLevel::new(1),
        };
        let out = producer.get(producer.tiling().universal_guard());
        let Tile::DataFunction { codomain, .. } = &out else {
            panic!("expected a collection, got {out:?}")
        };
        let Tile::Record { fields, .. } = &**codomain else {
            panic!("expected a record codomain, got {codomain:?}")
        };
        let Tile::DataFunction {
            domain_predicate: xs_stated,
            ..
        } = &fields["xs"]
        else {
            panic!("xs is a collection")
        };
        assert!(
            xs_stated.contains_path(&[Value::UInt(0), Value::UInt(7)]),
            "row 0 is complete and f calls 5 complete, so [0, 7] is complete: {xs_stated:?}"
        );
        assert!(
            !xs_stated.contains_path(&[Value::UInt(1), Value::UInt(7)]),
            "row 1 has not arrived, so nothing beneath it is complete: {xs_stated:?}"
        );
        // The debug completeness check in `get` compares this pull with the last.
        *next.borrow_mut() = input_at(vec![0, 1], 1);
        let _ = producer.get(producer.tiling().universal_guard());
    }

    /// An argument the function has not answered is withheld, and its row arrives later
    /// beneath each prefix of its path, so no level of the output calls that prefix complete.
    #[test]
    fn a_withheld_argument_is_taken_out_of_every_levels_statement() {
        use crate::interpreter::tile_operators::test_helpers::ScriptedProducer;
        let in_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );
        let fn_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let out_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(
                Extent::Base(BaseType::UInt),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        // Outer row 0 is open; its inner rows 0 and 1 (arguments 5 and 6) are complete.
        let input = Tile::data_function(
            ColumnValue::UInts(vec![0]),
            Box::new(Tile::grouped(
                vec![0],
                ColumnValue::UInts(vec![0, 1]),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![5, 6]))),
                Predicate::qualified(
                    Predicate::point(Value::UInt(0)),
                    Predicate::at_or_below(Value::UInt(1)),
                ),
                BitSet::new(),
            )),
            Predicate::False,
            BitSet::new(),
        );
        let f_at = |keys: Vec<u64>| {
            let vals: Vec<i64> = keys.iter().map(|k| *k as i64 * 10).collect();
            let pred = Predicate::from_column_value(&ColumnValue::UInts(keys.clone()));
            Tile::data_function(
                ColumnValue::UInts(keys),
                Box::new(Tile::Scalar(ColumnValue::Ints(vals))),
                pred,
                BitSet::new(),
            )
        };
        let (function, next) = ScriptedProducer::new(f_at(vec![5]), fn_tiling);
        let mut producer = MapResultProducer {
            base: ProducerBase::unowned(MapResultProducer::alloc_id(), &out_tiling),
            input: Box::new(TestTileProducer::new(input, in_tiling)),
            function: Box::new(function),
            values_are_keys: false,
            level: CurryLevel::new(2),
        };
        let out = producer.get(producer.tiling().universal_guard());
        let Tile::DataFunction { codomain, .. } = &out else {
            panic!("expected a collection, got {out:?}")
        };
        let Tile::DataFunction {
            domain_predicate: inner_stated,
            ..
        } = &**codomain
        else {
            panic!("expected a nested collection")
        };
        assert!(
            !inner_stated.contains_path(&[Value::UInt(0), Value::UInt(1)]),
            "[0, 1] was withheld, yet the inner level calls it complete: {out:?}"
        );
        *next.borrow_mut() = f_at(vec![5, 6]);
        let _ = producer.get(producer.tiling().universal_guard());
    }

    /// At a level above the innermost, `MapResultToConst` replaces each value there whole:
    /// over groups `0 ↦ [1]` and `1 ↦ [2, 3]` at level 1, each group becomes one constant,
    /// rather than each element.
    #[test]
    fn map_result_to_const_replaces_each_value_at_its_level() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let in_tiling =
            Tiling::data_function(uint(), Tiling::data_function(uint(), Tiling::Scalar(int())));
        let groups = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 1],
                ColumnValue::UInts(vec![0, 1, 2]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![1, 2, 3]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let operator = MapResultToConst::new_at(
            Box::new(Constant::collection(groups.clone(), in_tiling.clone())),
            Box::new(Constant::new(Value::Int(7), int())),
            MapResultToConstMode::Replace,
            CurryLevel::new(1),
        );
        assert_eq!(
            operator.tiling(),
            &Tiling::data_function(uint(), Tiling::Scalar(int()))
        );
        let mut producer = MapResultToConstProducer {
            base: ProducerBase::unowned(MapResultToConstProducer::alloc_id(), operator.tiling()),
            input: Box::new(TestTileProducer::new(groups, in_tiling)),
            constant: Box::new(TestTileProducer::new(
                Tile::Scalar(ColumnValue::Ints(vec![7])),
                Tiling::Scalar(int()),
            )),
            mode: MapResultToConstMode::Replace,
            level: CurryLevel::new(1),
        };
        let out = producer.get(producer.tiling().universal_guard());
        assert_eq!(
            out,
            Tile::data_function(
                ColumnValue::UInts(vec![0, 1]),
                Box::new(Tile::Scalar(ColumnValue::Ints(vec![7, 7]))),
                Predicate::True,
                BitSet::new(),
            )
        );
    }

    /// An argument with no rows yields no rows, even where it holds a level the function
    /// could not take as a column: a record whose field is a collection, applied a lookup
    /// table.
    #[test]
    fn map_result_over_no_arguments_is_empty_whatever_they_hold() {
        let uint = || Extent::Base(BaseType::UInt);
        let int = || Extent::Base(BaseType::Int);
        let row = Tiling::Record(HashMap::from([
            ("a".into(), Tiling::Scalar(int())),
            (
                "b".into(),
                Tiling::data_function(uint(), Tiling::Scalar(int())),
            ),
        ]));
        let in_tiling = Tiling::data_function(uint(), row.clone());
        let function = Constant::new(
            Value::Function(Vec::new()),
            Extent::Function {
                domain: Box::new(row.extent()),
                codomain: Box::new(int()),
            },
        );
        let operator = MapResult::new_at(
            Box::new(Constant::collection(
                in_tiling.empty_at_no_rows(),
                in_tiling.clone(),
            )),
            Box::new(function),
            CurryLevel::new(1),
        );
        let fn_tiling = operator.function.tiling().clone();
        let fn_tile = Tile::Scalar(ColumnValue::single(Value::Function(Vec::new())));
        let mut producer = MapResultProducer {
            base: ProducerBase::unowned(MapResultProducer::alloc_id(), operator.tiling()),
            input: Box::new(TestTileProducer::new(
                in_tiling.empty_at_no_rows(),
                in_tiling,
            )),
            function: Box::new(TestTileProducer::new(fn_tile, fn_tiling)),
            values_are_keys: false,
            level: CurryLevel::new(1),
        };
        let out = producer.get(producer.tiling().universal_guard());
        assert!(out.is_empty(), "no argument, no result: {out:?}");
    }

    /// While its constant is not terminal, `MapResultToConst` emits no rows and states what
    /// its input states except beneath the rows it holds live: it neither takes back a
    /// filtered key it called complete nor claims the live key it has not emitted.
    #[test]
    fn map_result_to_const_states_its_input_while_the_constant_is_incomplete() {
        use crate::interpreter::tile_operators::test_helpers::ScriptedProducer;
        let in_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let c_tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let out_tiling = in_tiling.clone();
        // Key 0 is filtered out (deleted); every other key is live.
        let input_at = |keys: Vec<u64>, vals: Vec<i64>, upto: u64| {
            Tile::data_function(
                ColumnValue::UInts(keys),
                Box::new(Tile::Scalar(ColumnValue::Ints(vals))),
                Predicate::at_or_below(Value::UInt(upto)),
                BitSet::from_iter([0usize]),
            )
        };
        let stated = |tile: &Tile| match tile {
            Tile::DataFunction {
                domain_predicate, ..
            } => domain_predicate.clone(),
            other => panic!("expected a collection, got {other:?}"),
        };
        // Pull 1: only the filtered key, so the constant is not pulled.
        let (input, next) = ScriptedProducer::new(input_at(vec![0], vec![1], 0), in_tiling);
        let mut producer = MapResultToConstProducer {
            base: ProducerBase::unowned(MapResultToConstProducer::alloc_id(), &out_tiling),
            input: Box::new(input),
            constant: Box::new(TestTileProducer::new(
                Tile::Scalar(ColumnValue::Ints(vec![])),
                c_tiling,
            )),
            mode: MapResultToConstMode::Replace,
            level: CurryLevel::new(1),
        };
        let first = producer.get(producer.tiling().universal_guard());
        assert_eq!(stated(&first), Predicate::at_or_below(Value::UInt(0)));
        // Pull 2: key 1 arrives live, and the constant is still not terminal.
        *next.borrow_mut() = input_at(vec![0, 1], vec![1, 10], 1);
        let second = producer.get(producer.tiling().universal_guard());
        assert!(second.is_empty(), "no row before the constant: {second:?}");
        assert_eq!(
            stated(&second),
            Predicate::at_or_below(Value::UInt(0)),
            "key 0 stays complete; key 1 waits for the constant"
        );
    }

    /// Source key 10, held beneath complete outer rows 0 and 1, released beneath them either
    /// one row at a time or by one guard naming both. Answers what the source has agreed to
    /// release after each step.
    fn release_a_source_key_beneath_two_rows(
        inner_stated: Predicate,
        one_guard: bool,
    ) -> Vec<Predicate> {
        use crate::interpreter::{DataSourceDomainExtentImpl, test_source::TestDataSource};
        let src = Rc::new(RefCell::new(TestDataSource::new(
            "source_key",
            crate::ccl::Type::Base(BaseType::String),
            Extent::Base(BaseType::String),
        )));
        src.borrow_mut()
            .add_data(&[(Value::UInt(10), Value::String("x".into()))]);
        let as_domain: Rc<RefCell<dyn DataSourceDomainExtentImpl>> = src.clone();
        let key_extent = Extent::DataSourceDomain(as_domain.clone());
        let in_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(key_extent.clone(), Tiling::Scalar(key_extent.clone())),
        );
        let out_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::data_function(key_extent, Tiling::Scalar(Extent::Base(BaseType::String))),
        );
        // Outer rows 0 and 1 are complete; each holds source key 10.
        let input = Tile::data_function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::grouped(
                vec![0, 1],
                ColumnValue::UInts(vec![10, 10]),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![10, 10]))),
                inner_stated,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let mut producer = MapResultWithSourceProducer::new(
            ProducerBase::unowned(MapResultWithSourceProducer::alloc_id(), &out_tiling),
            Box::new(TestTileProducer::new(input, in_tiling)),
            as_domain,
            Vec::new(),
            Some(vec![TilePathStep::Codomain]),
        );
        let _ = producer.get(producer.tiling().universal_guard());
        let beneath = |outer: u64| {
            TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Function(
                FunctionGuard::Domain(Predicate::qualified(
                    Predicate::point(Value::UInt(outer)),
                    Predicate::point(Value::UInt(10)),
                )),
            ))))
        };
        let mut agreed = Vec::new();
        if one_guard {
            producer.release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
                TileGuard::Function(FunctionGuard::Domain(Predicate::qualified(
                    Predicate::from_column_value(&ColumnValue::UInts(vec![0, 1])),
                    Predicate::point(Value::UInt(10)),
                ))),
            ))));
            agreed.push(Predicate::False);
            agreed.push(src.borrow().get_released_predicate());
            return agreed;
        }
        producer.release(beneath(0));
        agreed.push(src.borrow().get_released_predicate());
        producer.release(beneath(1));
        agreed.push(src.borrow().get_released_predicate());
        agreed
    }

    /// Released one row at a time, the source key is released only once the second row
    /// releases it.
    #[test]
    fn a_source_key_is_released_once_released_beneath_every_outer_row() {
        let agreed = release_a_source_key_beneath_two_rows(Predicate::True, false);
        assert!(!agreed[0].contains(&Value::UInt(10)), "{agreed:?}");
        assert!(agreed[1].contains(&Value::UInt(10)), "{agreed:?}");
    }

    /// One guard naming both rows releases the source key.
    #[test]
    fn a_source_key_is_released_by_one_release_naming_every_outer_row() {
        let agreed = release_a_source_key_beneath_two_rows(Predicate::True, true);
        assert!(agreed[1].contains(&Value::UInt(10)), "{agreed:?}");
    }

    /// The inner level states nothing itself, and the outer level calls both rows complete,
    /// which is complete at every depth, so no later path reaches key 10.
    #[test]
    fn a_source_key_is_released_when_completeness_is_stated_above_it() {
        let agreed = release_a_source_key_beneath_two_rows(Predicate::False, true);
        assert!(!agreed[0].contains(&Value::UInt(10)), "{agreed:?}");
        assert!(agreed[1].contains(&Value::UInt(10)), "{agreed:?}");
    }
}

/// How `MapResult` is pulled in the patterns it is used in: a stream of positions looked up in a
/// table (`xs ▷ map(c)`, read a morsel at a time), a stream whose values are not its keys, a
/// scalar function applied to a stream, and the groups a `Converse` produces, whose members are
/// looked up in the table the groups were built from.
#[cfg(test)]
mod projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, int_entries, ints_by_position, keys_between,
    };
    use crate::interpreter::{BaseType, FunctionDef, UnaryOpKind};
    use bit_set::BitSet;

    const ROWS: u64 = 10;

    /// The table `c` with `c[i] = 100 + 10 i`, the function operand of `map(c)`.
    fn table() -> (Tile, Tiling) {
        let values: Vec<i64> = (0..ROWS as i64).map(|i| 100 + 10 * i).collect();
        (
            ints_by_position(&values, true),
            Tiling::data_function(
                Extent::uint_range(ROWS),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        )
    }

    /// A stream whose value at each position is `values[position]`.
    fn stream(values: Vec<u64>) -> (Tile, Tiling) {
        (
            Tile::data_function(
                ColumnValue::UInts((0..values.len() as u64).collect()),
                Box::new(Tile::Scalar(ColumnValue::UInts(values))),
                Predicate::True,
                BitSet::new(),
            ),
            Tiling::data_function(
                Extent::uint_range(ROWS),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        )
    }

    fn output_tiling() -> Tiling {
        Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        )
    }

    /// The region a notification from the input reaches the consumer with is the input's, since
    /// the result's keys are the input's. A notification from the function operand is a change
    /// to the lookup at every key, which reaches the consumer as everything.
    #[test]
    fn a_map_result_forwards_its_inputs_region_and_everything_for_its_function() {
        use crate::interpreter::tile_operators::test_helpers::{
            NotifyingOp, RegionLog, notify_input,
        };
        let morsel = Projection::of(&keys_between(2, 4)).expect("keys");
        // One consumer notifies once between pulls, so each operand gets a subscription.
        let notified = |through_input: bool| {
            let (table_tile, table_tiling) = table();
            let positions = Tiling::data_function(
                Extent::uint_range(ROWS),
                Tiling::Scalar(Extent::uint_range(ROWS)),
            );
            let (input, input_consumer) =
                NotifyingOp::new(stream((0..ROWS).collect()).0, positions);
            let (function, function_consumer) = NotifyingOp::new(table_tile, table_tiling);
            let mut map =
                MapResult::new_at(Box::new(input), Box::new(function), CurryLevel::new(1));
            let (log, regions) = RegionLog::new();
            let _producer = map.subscribe(
                map.tiling().universal_guard(),
                Box::new(log),
                &mut Scheduler::new(),
            );
            let operand = if through_input {
                &input_consumer
            } else {
                &function_consumer
            };
            notify_input(operand, &morsel);
            let seen = regions.borrow_mut();
            seen.clone()
        };
        assert_eq!(notified(true), std::slice::from_ref(&morsel));
        assert_eq!(notified(false), [Projection::Everything]);
    }

    /// Applied to a whole collection at the outermost level, the function's keys are the
    /// result's, so a region of the collection's keys names none of them, though the input is a
    /// data function.
    #[test]
    fn a_map_result_at_the_outermost_level_sends_everything_for_a_region_of_its_input() {
        use crate::interpreter::tile_operators::test_helpers::{
            NotifyingOp, RegionLog, notify_input,
        };
        let positions = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::uint_range(ROWS)),
        );
        let (input, input_consumer) =
            NotifyingOp::new(stream((0..ROWS).collect()).0, positions.clone());
        let function = Constant::new(
            Value::Function(Vec::new()),
            Extent::Function {
                domain: Box::new(positions.extent()),
                codomain: Box::new(Extent::Base(BaseType::Int)),
            },
        );
        // A constant notifies its consumer when it is subscribed, which closes the gate, so a
        // stand-in of its tiling that does not notify takes its place.
        let function_tiling = function.tiling().clone();
        let (function, _) = NotifyingOp::new(function_tiling.empty_tile(), function_tiling);
        let mut map = MapResult::new_at(Box::new(input), Box::new(function), CurryLevel::OUTERMOST);
        let (log, regions) = RegionLog::new();
        let _producer = map.subscribe(
            map.tiling().universal_guard(),
            Box::new(log),
            &mut Scheduler::new(),
        );
        notify_input(
            &input_consumer,
            &Projection::of(&keys_between(2, 4)).expect("keys"),
        );
        assert_eq!(*regions.borrow_mut(), [Projection::Everything]);
    }

    /// Applied to a scalar at the outermost level, the function's keys are the result's, so a
    /// region of the input names none of them.
    #[test]
    fn a_map_result_over_a_scalar_sends_everything_for_a_region_of_its_input() {
        use crate::interpreter::tile_operators::test_helpers::{
            NotifyingOp, RegionLog, notify_input,
        };
        let (table_tile, table_tiling) = table();
        let scalar = Tiling::Scalar(Extent::uint_range(ROWS));
        let (input, input_consumer) =
            NotifyingOp::new(Tile::Scalar(ColumnValue::single(Value::UInt(3))), scalar);
        let (function, _) = NotifyingOp::new(table_tile, table_tiling);
        let mut map = MapResult::new_at(Box::new(input), Box::new(function), CurryLevel::OUTERMOST);
        let (log, regions) = RegionLog::new();
        let _producer = map.subscribe(
            map.tiling().universal_guard(),
            Box::new(log),
            &mut Scheduler::new(),
        );
        notify_input(
            &input_consumer,
            &Projection::of(&keys_between(2, 4)).expect("keys"),
        );
        assert_eq!(*regions.borrow_mut(), [Projection::Everything]);
    }

    /// The logs of a `MapResult` over two spies: the guards its input and its function operand
    /// were pulled with, and the guards released to each.
    struct Logs {
        input_pulled: GuardLog,
        function_pulled: GuardLog,
        input_released: GuardLog,
        function_released: GuardLog,
    }

    fn map_result(
        input: (Tile, Tiling),
        function: (Tile, Tiling),
        out: Tiling,
        values_are_keys: bool,
        level: CurryLevel,
    ) -> (MapResultProducer, Logs) {
        let (input, input_pulled, input_released) = ProjectionSpy::new(input.0, input.1);
        let (function, function_pulled, function_released) =
            ProjectionSpy::new(function.0, function.1);
        (
            MapResultProducer {
                base: ProducerBase::unowned(MapResultProducer::alloc_id(), &out),
                input: Box::new(input),
                function: Box::new(function),
                values_are_keys,
                level,
            },
            Logs {
                input_pulled,
                function_pulled,
                input_released,
                function_released,
            },
        )
    }

    /// `xs ▷ map(c)` over a stream of positions, whose values are its keys.
    fn lookup_over_positions() -> (MapResultProducer, Logs) {
        map_result(
            stream((0..ROWS).collect()),
            table(),
            output_tiling(),
            true,
            CurryLevel::new(1),
        )
    }

    /// A worker pulls its chain one morsel at a time. The morsel reaches the stream and the
    /// table alike, so no pull reads the table whole.
    #[test]
    fn a_stream_of_positions_looks_up_only_its_morsel() {
        let (mut map, logs) = lookup_over_positions();
        let morsel = map.get(keys_between(2, 4));
        assert_eq!(int_entries(&morsel), [(2, 120), (3, 130), (4, 140)]);
        assert_eq!(*logs.input_pulled.borrow(), [keys_between(2, 4)]);
        assert_eq!(*logs.function_pulled.borrow(), [keys_between(2, 4)]);
        let Tile::DataFunction {
            domain_predicate, ..
        } = &morsel
        else {
            panic!("a collection")
        };
        let TileGuard::Function(FunctionGuard::Domain(stated)) = keys_between(2, 4) else {
            unreachable!("a morsel is a domain guard")
        };
        assert_eq!(*domain_predicate, stated, "complete over the morsel alone");
    }

    /// The consumer releases the morsel it took, which retires the keys looked up and lets the
    /// next morsel be pulled: the table's completeness is stated per morsel.
    #[test]
    fn releasing_a_morsel_retires_the_table_keys_it_looked_up() {
        let (mut map, logs) = lookup_over_positions();
        map.get(keys_between(0, 3));
        map.release(keys_between(0, 3));
        assert_eq!(*logs.input_released.borrow(), [keys_between(0, 3)]);
        assert_eq!(*logs.function_released.borrow(), [keys_between(0, 3)]);
        let next = map.get(keys_between(4, 9));
        assert_eq!(
            int_entries(&next),
            (4..10)
                .map(|i| (i, 100 + 10 * i as i64))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn the_morsels_together_are_the_whole_pull() {
        for guard in [keys_between(0, 3), keys_between(8, 20), keys_between(5, 5)] {
            assert_conforms(|| Box::new(lookup_over_positions().0), guard);
        }
    }

    /// A stream whose values are indexes into the table, not its own keys: the lookups are
    /// known only once the stream is read, so the table is read whole and never released
    /// for a part of the stream.
    #[test]
    fn a_stream_of_indexes_reads_the_table_whole() {
        let (mut map, logs) = map_result(
            stream(vec![9, 8, 7, 6, 5, 4, 3, 2, 1, 0]),
            table(),
            output_tiling(),
            false,
            CurryLevel::new(1),
        );
        let morsel = map.get(keys_between(0, 1));
        assert_eq!(int_entries(&morsel), [(0, 190), (1, 180)]);
        assert_eq!(*logs.input_pulled.borrow(), [keys_between(0, 1)]);
        assert_eq!(
            *logs.function_pulled.borrow(),
            [table().1.universal_guard()],
            "the table is pulled in full"
        );
        map.release(keys_between(0, 1));
        assert!(logs.function_released.borrow().is_empty());
    }

    /// `map(-)` applies a scalar function value: the projection is the stream's, and the
    /// function is one value read whole.
    #[test]
    fn a_scalar_function_is_applied_to_the_projected_stream() {
        let negate = Tile::Scalar(ColumnValue::single(Value::ComputableFunction(
            FunctionDef::UnaryOp(UnaryOpKind::Neg),
        )));
        let negate_tiling = Tiling::Scalar(Extent::Function {
            domain: Box::new(Extent::Base(BaseType::Int)),
            codomain: Box::new(Extent::Base(BaseType::Int)),
        });
        let (mut map, logs) = map_result(
            (
                ints_by_position(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10], true),
                output_tiling(),
            ),
            (negate, negate_tiling.clone()),
            output_tiling(),
            false,
            CurryLevel::new(1),
        );
        let morsel = map.get(keys_between(3, 5));
        assert_eq!(int_entries(&morsel), [(3, -4), (4, -5), (5, -6)]);
        assert_eq!(*logs.input_pulled.borrow(), [keys_between(3, 5)]);
        assert_eq!(
            *logs.function_pulled.borrow(),
            [negate_tiling.universal_guard()]
        );
    }

    #[test]
    fn nothing_pulls_nothing() {
        let (mut map, logs) = lookup_over_positions();
        let nothing = map.tiling().empty_guard();
        assert_eq!(map.get(nothing), map.tiling().empty_tile());
        assert!(logs.input_pulled.borrow().is_empty());
        assert!(logs.function_pulled.borrow().is_empty());
    }

    /// The groups `Converse` makes: group `k` holds the positions that map to `k`, and
    /// `map(c)` looks each member up in the table the groups came from. The projection names
    /// groups, which are the outer keys the map leaves standing, so it reaches the groups and
    /// not the table: a member's position says nothing of which groups hold it.
    fn lookup_over_groups() -> (MapResultProducer, Logs) {
        // Group 1 holds positions 0 and 2, group 2 holds 1, group 3 holds 3.
        let groups = Tile::data_function(
            ColumnValue::Ints(vec![1, 2, 3]),
            Box::new(Tile::grouped(
                vec![0, 2, 3],
                ColumnValue::UInts(vec![0, 2, 1, 3]),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![0, 2, 1, 3]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let groups_tiling = Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::data_function(
                Extent::uint_range(ROWS),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );
        let out = Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::data_function(
                Extent::uint_range(ROWS),
                Tiling::Scalar(Extent::Base(BaseType::Int)),
            ),
        );
        map_result(
            (groups, groups_tiling),
            table(),
            out,
            false,
            CurryLevel::new(2),
        )
    }

    /// `groupby(c)(1)`: a scalar key looked up in the groups. The keys the projection names are
    /// the group's own, which the scalar input does not have, so it is read whole.
    #[test]
    fn a_projection_of_a_looked_up_group_reads_the_scalar_key_whole() {
        let groups = Tile::data_function(
            ColumnValue::Ints(vec![1, 2]),
            Box::new(Tile::grouped(
                vec![0, 2],
                ColumnValue::UInts(vec![0, 2, 1]),
                Box::new(Tile::Scalar(ColumnValue::UInts(vec![0, 2, 1]))),
                Predicate::True,
                BitSet::new(),
            )),
            Predicate::True,
            BitSet::new(),
        );
        let groups_tiling = Tiling::data_function(
            Extent::Base(BaseType::Int),
            Tiling::data_function(
                Extent::uint_range(ROWS),
                Tiling::Scalar(Extent::Base(BaseType::UInt)),
            ),
        );
        let key = Tiling::Scalar(Extent::Base(BaseType::Int));
        let out = Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );
        let (mut map, logs) = map_result(
            (Tile::Scalar(ColumnValue::Ints(vec![1])), key.clone()),
            (groups, groups_tiling),
            out,
            false,
            CurryLevel::OUTERMOST,
        );
        let answer = map.get(keys_between(0, 1));
        let Tile::DataFunction { domain, .. } = &answer else {
            panic!("a collection, got {answer:?}")
        };
        assert_eq!(*domain, ColumnValue::UInts(vec![0]), "group 1's key 0 only");
        assert_eq!(*logs.input_pulled.borrow(), [key.universal_guard()]);
    }

    fn groups_one_and_three() -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(
            Predicate::point(Value::Int(1)).union(&Predicate::point(Value::Int(3))),
        ))
    }

    #[test]
    fn a_projection_of_groups_reaches_the_groups_and_reads_the_table_whole() {
        let (mut map, logs) = lookup_over_groups();
        let answer = map.get(groups_one_and_three());
        let Tile::DataFunction { domain, .. } = &answer else {
            panic!("a collection")
        };
        assert_eq!(
            *domain,
            ColumnValue::Ints(vec![1, 3]),
            "groups 1 and 3 only"
        );
        assert_eq!(*logs.input_pulled.borrow(), [groups_one_and_three()]);
        assert_eq!(
            *logs.function_pulled.borrow(),
            [table().1.universal_guard()]
        );
    }

    #[test]
    fn the_groups_projected_are_the_whole_pull_cut_to_them() {
        assert_conforms(|| Box::new(lookup_over_groups().0), groups_one_and_three());
    }
}

/// `MapResultToConst` as a comprehension over a stream uses it: `[7 for x in xs]` replaces each
/// value with a constant, and `[(x, 2) for x in xs]` pairs each value with one. The stream is
/// cut into morsels and the constant is the same for every row.
#[cfg(test)]
mod const_projection_tests {
    use super::*;
    use crate::interpreter::BaseType;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, int_entries, ints_by_position, keys_between,
    };

    const ROWS: u64 = 10;

    fn int_stream_tiling() -> Tiling {
        Tiling::data_function(
            Extent::uint_range(ROWS),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        )
    }

    fn seven(complete: bool) -> (Tile, Tiling) {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        match complete {
            true => (Tile::Scalar(ColumnValue::Ints(vec![7])), tiling),
            false => (tiling.empty_tile(), tiling),
        }
    }

    fn broadcast(
        mode: MapResultToConstMode,
        constant: (Tile, Tiling),
    ) -> (MapResultToConstProducer, GuardLog, GuardLog) {
        let values: Vec<i64> = (0..ROWS as i64).map(|i| i * 3).collect();
        let (input, input_pulled, _) =
            ProjectionSpy::new(ints_by_position(&values, true), int_stream_tiling());
        let (constant, constant_pulled, _) = ProjectionSpy::new(constant.0, constant.1);
        let out = match mode {
            MapResultToConstMode::Replace => int_stream_tiling(),
            _ => Tiling::data_function(
                Extent::uint_range(ROWS),
                Tiling::Record(
                    [
                        (tuple_field(0), Tiling::Scalar(Extent::Base(BaseType::Int))),
                        (tuple_field(1), Tiling::Scalar(Extent::Base(BaseType::Int))),
                    ]
                    .into_iter()
                    .collect(),
                ),
            ),
        };
        (
            MapResultToConstProducer {
                base: ProducerBase::unowned(MapResultToConstProducer::alloc_id(), &out),
                input: Box::new(input),
                constant: Box::new(constant),
                mode,
                level: CurryLevel::new(1),
            },
            input_pulled,
            constant_pulled,
        )
    }

    /// Each worker's morsel of `[7 for x in xs]`: the stream is read at the morsel and the
    /// constant whole.
    #[test]
    fn a_replaced_stream_reads_the_morsel_and_the_constant_whole() {
        let (mut map, input_pulled, constant_pulled) =
            broadcast(MapResultToConstMode::Replace, seven(true));
        let morsel = map.get(keys_between(2, 4));
        assert_eq!(int_entries(&morsel), [(2, 7), (3, 7), (4, 7)]);
        assert_eq!(*input_pulled.borrow(), [keys_between(2, 4)]);
        assert_eq!(
            *constant_pulled.borrow(),
            [Tiling::Scalar(Extent::Base(BaseType::Int)).universal_guard()]
        );
    }

    #[test]
    fn a_paired_stream_is_the_whole_pull_cut_to_the_morsel() {
        for mode in [
            MapResultToConstMode::ZipLeft,
            MapResultToConstMode::ZipRight,
        ] {
            for guard in [keys_between(0, 2), keys_between(8, 30)] {
                assert_conforms(|| Box::new(broadcast(mode, seven(true)).0), guard);
            }
        }
    }

    /// A constant that has not landed yet, such as a scalar read from a loop that has not
    /// converged, fabricates no rows: the projection answers nothing until it does.
    #[test]
    fn a_constant_that_has_not_landed_answers_nothing_for_any_morsel() {
        let (mut map, _, _) = broadcast(MapResultToConstMode::Replace, seven(false));
        let morsel = map.get(keys_between(0, 3));
        assert!(int_entries(&morsel).is_empty());
    }

    #[test]
    fn nothing_pulls_nothing() {
        let (mut map, input_pulled, constant_pulled) =
            broadcast(MapResultToConstMode::Replace, seven(true));
        let nothing = map.tiling().empty_guard();
        assert_eq!(map.get(nothing), map.tiling().empty_tile());
        assert!(input_pulled.borrow().is_empty() && constant_pulled.borrow().is_empty());
    }
}

/// A program over a live source reads it as `iterate ▷ map_with_source`: the source's domain
/// supplies the keys, which this operator looks up, and a worker's morsel is a range of them.
#[cfg(test)]
mod source_projection_tests {
    use super::*;
    use crate::interpreter::BaseType;
    use crate::interpreter::test_source::TestDataSource;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpy, assert_conforms, int_entries, keys_between,
    };
    use bit_set::BitSet;

    const ROWS: u64 = 5;

    /// A source holding `10, 20, 30, 40, 50` at positions `0..5`, and the producer reading it
    /// over a stream of its positions, which `spy` stands in for the domain iteration of.
    fn read_source() -> (MapResultWithSourceProducer, GuardLog) {
        let source = Rc::new(RefCell::new(TestDataSource::new(
            "s",
            crate::ccl::Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )));
        source.borrow_mut().add_data(
            &(0..ROWS)
                .map(|i| (Value::UInt(i), Value::Int(10 * (i as i64 + 1))))
                .collect::<Vec<_>>(),
        );
        let positions = Tile::data_function(
            ColumnValue::UInts((0..ROWS).collect()),
            Box::new(Tile::Scalar(ColumnValue::UInts((0..ROWS).collect()))),
            Predicate::True,
            BitSet::new(),
        );
        let in_tiling = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );
        let out = Tiling::data_function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let (input, pulled, _) = ProjectionSpy::new(positions, in_tiling);
        (
            MapResultWithSourceProducer {
                base: ProducerBase::unowned(MapResultWithSourceProducer::alloc_id(), &out),
                input: Box::new(input),
                source,
                fields: Vec::new(),
                result_correlation: None,
                last_nested_input: None,
            },
            pulled,
        )
    }

    #[test]
    fn a_morsel_reads_only_its_rows_of_the_source() {
        let (mut read, pulled) = read_source();
        let morsel = read.get(keys_between(1, 3));
        assert_eq!(int_entries(&morsel), [(1, 20), (2, 30), (3, 40)]);
        assert_eq!(*pulled.borrow(), [keys_between(1, 3)]);
    }

    #[test]
    fn the_morsels_are_the_whole_pull_cut_to_them() {
        for guard in [keys_between(0, 1), keys_between(3, 9)] {
            assert_conforms(|| Box::new(read_source().0), guard);
        }
    }

    #[test]
    fn nothing_reads_nothing() {
        let (mut read, pulled) = read_source();
        let nothing = read.tiling().empty_guard();
        assert_eq!(read.get(nothing), read.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }
}
