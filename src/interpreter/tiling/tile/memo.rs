//! Insert-only writes to a memo's materialized tile.
use super::*;
use crate::interpreter::{Projection, tile_operators::guard_minus};

impl Tile {
    /// Materialize a memo delivery and return exactly the region newly complete in
    /// this cache. A later append can add descendants or close a row without a value.
    pub(crate) fn append(
        &mut self,
        mut incoming: Tile,
        projection: &Projection,
        tiling: &Tiling,
    ) -> TileGuard {
        #[cfg(test)]
        self.check_memo_row(&incoming, Some(0), 0, &mut Vec::new(), false);

        if let (
            Tile::DataFunction {
                codomain,
                domain: existing_keys,
                domain_predicate: before,
                ..
            },
            Tile::DataFunction {
                domain,
                codomain: values,
                domain_predicate: stated,
                ..
            },
        ) = (&*self, &mut incoming)
            && matches!((&**codomain, &**values), (Tile::Scalar(_), Tile::Scalar(_)))
            && codomain.holds_plain_values(existing_keys.len())
            && values.holds_plain_values(domain.len())
        {
            // Scalar rows are final on arrival. Keep that fact in the collection's own
            // statement so a subsequent close can subtract the keys any worker appended.
            let before = before.clone();
            if !values.is_empty() {
                *stated = stated.union(&Predicate::from_column_value(domain));
            }
            self.append_keys(incoming, true);
            self.close_memo_positions(tiling);
            let after = self.level_statement();
            return TileGuard::Function(FunctionGuard::Domain(after.minus(&before)));
        }

        if let Some(delta) = self.insert_memo_items(&mut incoming, projection, tiling) {
            return delta;
        }

        if projection.names_part_of_values() && incoming.to_guard().is_empty() {
            // A field release can leave only its enclosing key in an input answer.
            return tiling.empty_guard();
        }
        // A partial record may complete a field supplied by a peer, and a statement
        // can close a row with no physical items. Compare the cache across this
        // append, while its caller still has exclusive access to it.
        let before = self.to_guard();
        let nested = nested_answer(&incoming, projection);
        self.merge(incoming);
        if let Some(nested) = nested {
            nested.merge_into(self, tiling);
        }
        self.close_memo_positions(tiling);
        guard_minus(&self.to_guard(), &before)
    }

    fn close_memo_positions(&mut self, tiling: &Tiling) {
        for depth in (0..tiling.levels()).rev() {
            let level = CurryLevel::new(depth);
            if let Some(closed) = position_closure(self.values_at(level), tiling.values_at(level))
                && let Tile::DataFunction {
                    domain_predicate, ..
                } = self.values_at_mut(level)
            {
                *domain_predicate = closed;
            }
        }
    }

    /// Validate a delivery before mutating the cache. A repeated parent can carry new
    /// children or only a completion statement. A settled leaf can carry no second value,
    /// and a previously closed group can acquire no key, even one with an empty collection.
    #[cfg(test)]
    fn check_memo_row(
        &self,
        incoming: &Tile,
        cached_row: Option<usize>,
        row: usize,
        path: &mut Vec<Value>,
        closed: bool,
    ) {
        match (self, incoming) {
            (
                Self::DataFunction {
                    domain, codomain, ..
                },
                Self::DataFunction {
                    domain: added,
                    codomain: values,
                    ..
                },
            ) => {
                let (begin, end) = incoming.row_run(row);
                if begin == end {
                    return;
                }
                let (from, to) = cached_row.map(|i| self.row_run(i)).unwrap_or_default();
                let existing: HashMap<_, _> = (from..to).map(|i| (domain.index_at(i), i)).collect();
                let statement = self.level_statement();
                let mut seen = HashSet::new();
                for i in begin..end {
                    path.push(added.index_at(i));
                    let key = path.last().expect("just appended");
                    let previous = existing.get(key).copied();
                    let final_key = closed || statement.contains_path(path);
                    assert!(
                        seen.insert(key.clone()) && (!final_key || previous.is_some()),
                        "memo received a value for an already completed key at {path:?}"
                    );
                    codomain.check_memo_row(values, previous, i, path, final_key);
                    path.pop();
                }
            }
            (
                Self::Record { fields, absent },
                Self::Record {
                    fields: added,
                    absent: missing,
                },
            ) => {
                // An empty record is a complete value carried by its enclosing key.
                if fields.is_empty() && !path.is_empty() {
                    assert!(
                        cached_row.is_none() && !closed,
                        "memo received a value for an already completed key at {path:?}"
                    );
                }
                let physical = |field: &Tile, absent: Option<&BitSet>, i: usize| {
                    if let Some(bits) = absent {
                        if bits.contains(i) {
                            return None;
                        }
                        let i = i - bits.iter().take_while(|&r| r < i).count();
                        return (i < field.rows()).then_some(i);
                    }
                    (i < field.rows()).then_some(i)
                };
                for (name, value) in added {
                    if let Some(at) = physical(value, missing.get(name), row) {
                        let old = &fields[name];
                        let cached = cached_row.and_then(|i| physical(old, absent.get(name), i));
                        old.check_memo_row(value, cached, at, path, closed);
                    }
                }
            }
            (Self::Union(arms), Self::Union(added)) => {
                for (tag, arm) in added.iter() {
                    if let Ok(at) = arm.rows.binary_search(&row) {
                        let old = arms.get(tag).expect("memo and input share a tiling");
                        let cached = cached_row.and_then(|r| old.rows.binary_search(&r).ok());
                        if let Some(r) = cached_row {
                            assert!(
                                cached.is_some()
                                    || arms
                                        .values()
                                        .all(|other| other.rows.binary_search(&r).is_err()),
                                "memo received a different tag for a previously delivered key at {path:?}"
                            );
                        }
                        old.tile.check_memo_row(&arm.tile, cached, at, path, closed);
                        break;
                    }
                }
            }
            _ if !path.is_empty() && row < incoming.rows() => {
                let already_final =
                    cached_row.is_some_and(|i| i < self.rows() && self.finished_field_at(i));
                assert!(
                    !closed && !already_final,
                    "memo received a value for an already completed key at {path:?}"
                );
            }
            _ => {}
        }
    }

    /// Append complete items to a collection field of existing outer rows.
    /// The projection guarantees that no sibling field contributed data or completeness.
    fn insert_memo_items(
        &mut self,
        incoming: &mut Tile,
        projection: &Projection,
        tiling: &Tiling,
    ) -> Option<TileGuard> {
        let Projection::Within {
            level: CurryLevel::OUTERMOST,
            values,
            ..
        } = projection
        else {
            return None;
        };
        let Projection::Fields { fields, rest } = values.as_ref() else {
            return None;
        };
        if fields.len() != 1 || **rest != Projection::Nothing {
            return None;
        }
        let (name, _) = fields.first_key_value()?;
        let Tile::DataFunction {
            domain: parents,
            domain_predicate: closed_parents,
            codomain,
            keys_follow_beneath: follow,
            ..
        } = self
        else {
            return None;
        };
        let Tile::DataFunction {
            domain: added_parents,
            codomain: added_record,
            keys_follow_beneath: added_follow,
            domain_predicate: added_complete,
            ..
        } = incoming
        else {
            return None;
        };
        if !added_complete.is_false() || follow != added_follow {
            return None;
        }
        let (
            Tile::Record { fields, .. },
            Tile::Record {
                fields: added_fields,
                ..
            },
        ) = (codomain.as_mut(), added_record.as_mut())
        else {
            return None;
        };
        let existing = fields.get_mut(name)?;
        let addition = added_fields.get_mut(name)?;
        let arrived = existing.memo_item_delta(parents, addition, added_parents, closed_parents)?;
        let Tile::DataFunction {
            domain,
            codomain,
            row_starts,
            domain_predicate,
            ..
        } = existing
        else {
            unreachable!()
        };
        let Tile::DataFunction {
            domain: keys,
            codomain: values,
            row_starts: added_starts,
            domain_predicate: stated,
            ..
        } = addition
        else {
            unreachable!()
        };
        if parents == added_parents && domain.is_empty() {
            // The previous items have been released. The new columns already have
            // exactly the cache's row order, including empty runs.
            std::mem::swap(row_starts, added_starts);
            std::mem::swap(domain, keys);
            std::mem::swap(codomain, values);
        } else if let Some(parent) = added_parents.as_single() {
            let row = (0..parents.len()).find(|i| parents.index_at(*i) == parent)?;
            if !keys.is_empty() {
                let end = row_starts.get(row + 1).copied().unwrap_or(domain.len());
                domain.insert_column(end, keys.clone());
                codomain.insert_plain_rows(end, values);
                for offset in &mut row_starts[row + 1..] {
                    *offset += keys.len();
                }
            }
        } else {
            // Resolve every parent before changing any column: a new parent needs
            // the record merge to align its sibling fields as well.
            let mut incoming: HashMap<_, _> = (0..added_parents.len())
                .map(|r| {
                    (
                        added_parents.index_at(r),
                        level_run(added_starts, r, keys.len()),
                    )
                })
                .collect();
            let runs: Vec<_> = (0..parents.len())
                .map(|r| incoming.remove(&parents.index_at(r)).unwrap_or_default())
                .collect();
            if !incoming.is_empty() {
                return None;
            }
            if !keys.is_empty() {
                // Gather the old run followed by the new run for each parent. Moving
                // each suffix separately would copy the same later rows repeatedly.
                let old_len = domain.len();
                let mut order = Vec::with_capacity(old_len + keys.len());
                for (r, (from, to)) in runs.into_iter().enumerate() {
                    let (start, end) = level_run(row_starts, r, old_len);
                    row_starts[r] = order.len();
                    order.extend(start..end);
                    order.extend(old_len + from..old_len + to);
                }
                domain.extend_from(keys);
                codomain.insert_plain_rows(old_len, values);
                *domain = domain.select_indices(order.iter().copied(), order.len());
                **codomain = codomain.select_rows(&order);
            }
        }
        *domain_predicate = domain_predicate.union(stated);
        let TileGuard::Record(mut fields) = tiling.values_at(CurryLevel::new(1)).empty_guard()
        else {
            unreachable!()
        };
        fields.insert(
            name.clone(),
            TileGuard::Function(FunctionGuard::Domain(arrived)),
        );
        Some(TileGuard::Function(FunctionGuard::Codomain(Box::new(
            TileGuard::Record(fields),
        ))))
    }
    /// Compute the delta of a dense, single-assignment item column before inserting it.
    fn memo_item_delta(
        &self,
        parents: &ColumnValue,
        addition: &Tile,
        added_parents: &ColumnValue,
        closed_parents: &Predicate,
    ) -> Option<Predicate> {
        let Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            domain_predicate: known,
            keys_follow_beneath,
            deleted,
            ..
        } = self
        else {
            return None;
        };
        let Tile::DataFunction {
            row_starts: added_starts,
            domain: keys,
            codomain: values,
            domain_predicate: stated,
            keys_follow_beneath: new_follow,
            ..
        } = addition
        else {
            return None;
        };
        if !codomain.holds_plain_values(domain.len())
            || !values.holds_plain_values(keys.len())
            || codomain.has_absent_fields()
            || values.has_absent_fields()
            || !deleted.is_empty()
            || keys_follow_beneath != new_follow
        {
            return None;
        }
        if row_starts.len() != parents.len() || added_starts.len() != added_parents.len() {
            return None;
        }
        // Items are single-assignment. Only a completion statement can also name
        // previously appended items (including a peer's items awaiting input release).
        let paths = |column: &ColumnValue| {
            (0..column.len())
                .map(|i| vec![column.index_at(i)])
                .collect::<Vec<_>>()
        };
        let mut end = stated.minus(known).minus(&closed_parents.descend(1));
        if !end.is_false() && !domain.is_empty() {
            end = end.minus(&self.unstated_held_keys(&paths(parents)));
        }
        Some(
            addition
                .unstated_held_keys(&paths(added_parents))
                .union(&end),
        )
    }

    /// Insert a dense run of plain values in each of its columns at the same offset.
    fn insert_plain_rows(&mut self, at: usize, incoming: &Tile) {
        match (self, incoming) {
            (Self::Scalar(column), Self::Scalar(added)) => column.insert_column(at, added.clone()),
            (Self::Record { fields, .. }, Self::Record { fields: added, .. }) => {
                for (name, values) in added {
                    fields
                        .get_mut(name)
                        .expect("same record shape")
                        .insert_plain_rows(at, values);
                }
            }
            _ => unreachable!("a plain value is a scalar or a record of plain values"),
        }
    }
}

/// The keys a nested answer settled, and their enclosing rows if the answer holds
/// them all. An absence can settle paths in a row held only by an earlier answer.
struct NestedAnswer {
    level: CurryLevel,
    keys: Predicate,
    rows: Option<Vec<Vec<Value>>>,
}

fn nested_answer(input: &Tile, requested: &Projection) -> Option<NestedAnswer> {
    let Tile::DataFunction { codomain, .. } = input else {
        return None;
    };
    if !codomain.is_data_function() {
        return None;
    }
    let held = input.to_guard();
    let paths = Projection::of(&held).ok()?;
    let Projection::Keys { level, keys } = &paths else {
        return None;
    };
    if paths.minus(requested) != Projection::Nothing {
        return None;
    }
    let rows = level.enclosing().and_then(|parent| {
        let held_parents = Projection::keys_at(parent, input.paths_predicate(parent));
        (paths.above(*level).minus(&held_parents) == Projection::Nothing)
            .then(|| input.paths_at(parent))
    });
    Some(NestedAnswer {
        level: *level,
        keys: keys.clone(),
        rows,
    })
}

impl NestedAnswer {
    /// Record this answer's completed paths, propagating newly complete child
    /// collections to their enclosing rows before append computes the delta.
    fn merge_into(self, cache: &mut Tile, tiling: &Tiling) {
        let Self {
            mut level,
            keys: mut arrived,
            mut rows,
        } = self;
        loop {
            let node = cache.values_at_mut(level);
            let Tile::DataFunction {
                domain_predicate, ..
            } = node
            else {
                unreachable!()
            };
            *domain_predicate = domain_predicate.union(&arrived);
            let stated = node.level_statement();
            let extent = tiling.values_at(level).domain_extent();
            let Some(parent) = level.enclosing() else {
                if covers_domain(&stated, extent.as_ref()) {
                    let Tile::DataFunction {
                        domain_predicate, ..
                    } = cache
                    else {
                        unreachable!()
                    };
                    *domain_predicate = Predicate::True;
                }
                return;
            };
            let already_closed = cache.completion_at(parent);
            let mut closed = Vec::new();
            for path in rows.take().unwrap_or_else(|| cache.paths_at(parent)) {
                if already_closed.contains_path(&path) || arrived.within(&path, 0).is_false() {
                    continue;
                }
                let known = stated.within(&path, 0);
                if covers_domain(&known, extent.as_ref()) {
                    closed.push(Predicate::exactly(&path));
                }
            }
            if closed.is_empty() {
                return;
            }
            level = parent;
            arrived = Predicate::union_all(closed);
        }
    }
}

fn covers_domain(keys: &Predicate, extent: Option<&Extent>) -> bool {
    match extent {
        Some(Extent::UIntRange(positions)) => keys.covers_positions(positions),
        Some(Extent::Base(crate::interpreter::BaseType::Unit)) => {
            keys.unqualified_arms().contains(&Value::Unit)
        }
        _ => keys.is_true(),
    }
}

/// State `tile` complete where it states every key of its outermost collection, a finite range
/// of positions (`Extent::UIntRange`), without stating `True`.
///
/// A pull at some keys states completeness of those keys alone, so a cache merging the answers
/// to pulls at every key states each of them and not the whole. A reader holding the collection
/// beneath a level of its own states that level complete only where the collection states
/// `True`, so the cache states it once it can.
fn position_closure(tile: &Tile, tiling: &Tiling) -> Option<Predicate> {
    let Tile::DataFunction {
        domain,
        codomain,
        domain_predicate,
        ..
    } = tile
    else {
        return None;
    };
    if domain_predicate.is_true() {
        return None;
    }
    let whole_rows = matches!(codomain.as_ref(), Tile::DataFunction { domain_predicate, .. } if domain_predicate.is_true())
        .then(|| domain_predicate.union(&Predicate::from_column_value(domain)));
    if covers_domain(
        whole_rows.as_ref().unwrap_or(domain_predicate),
        tiling.domain_extent().as_ref(),
    ) {
        Some(Predicate::True)
    } else {
        whole_rows.filter(|rows| rows != domain_predicate)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    fn keyed(values: Tiling) -> Tiling {
        Tiling::data_function(Extent::Base(crate::interpreter::BaseType::UInt), values)
    }

    fn integer() -> Tiling {
        Tiling::Scalar(Extent::Base(crate::interpreter::BaseType::Int))
    }

    fn customers_tiling(item: Tiling) -> Tiling {
        keyed(Tiling::Record([("history".into(), keyed(item))].into()))
    }

    fn rejects_update(cache: &mut Tile, update: Tile, projection: &Projection, tiling: &Tiling) {
        let before = cache.clone();
        let fail = catch_unwind(AssertUnwindSafe(|| {
            cache.append(update, projection, tiling)
        }));
        let error = fail.expect_err("a completed key must reject a second value");
        let message = error
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| error.downcast_ref::<&str>().copied());
        assert!(
            message
                .unwrap_or_default()
                .contains("already completed key")
        );
        assert_eq!(
            *cache, before,
            "a rejected delivery must leave the old data intact"
        );
    }

    fn ints(keys: &[u64], values: &[i64]) -> Tile {
        Tile::data_function(
            ColumnValue::UInts(keys.to_vec()),
            Box::new(Tile::Scalar(ColumnValue::Ints(values.to_vec()))),
            Predicate::False,
            BitSet::new(),
        )
    }

    #[test]
    fn a_flat_memo_rejects_a_second_value_and_the_rest_of_its_batch() {
        let mut cache = ints(&[], &[]);
        cache.append(
            ints(&[3], &[30]),
            &Projection::Everything,
            &keyed(integer()),
        );
        for value in [30, 99] {
            rejects_update(
                &mut cache,
                ints(&[4, 3], &[40, value]),
                &Projection::Everything,
                &keyed(integer()),
            );
        }
        // Build a malformed delivery without the tile constructor's debug-only check.
        let mut duplicate = ints(&[4, 5], &[40, 41]);
        let Tile::DataFunction { domain, .. } = &mut duplicate else {
            unreachable!()
        };
        *domain = ColumnValue::UInts(vec![4, 4]);
        rejects_update(
            &mut cache,
            duplicate,
            &Projection::Everything,
            &keyed(integer()),
        );
    }

    #[test]
    fn a_bare_scalar_key_and_a_later_absence_are_disjoint_deltas() {
        let tiling = keyed(integer());
        let mut cache = tiling.empty_tile();
        let key = ints(&[3], &[]);
        let held = key.to_guard();
        assert_eq!(cache.append(key, &Projection::Everything, &tiling), held);
        let mut absent = ints(&[], &[]);
        let Tile::DataFunction {
            domain_predicate, ..
        } = &mut absent
        else {
            unreachable!()
        };
        *domain_predicate = Predicate::point(Value::UInt(9));
        let expected = absent.to_guard();
        let next = cache.append(absent, &Projection::Everything, &tiling);
        assert_eq!(next, expected);
        assert!(next.intersect(&held).is_empty());
    }

    #[test]
    fn a_key_holding_an_empty_record_is_already_a_complete_value() {
        let delivery = Tile::data_function(
            ColumnValue::UInts(vec![7]),
            Box::new(Tile::record(HashMap::new())),
            Predicate::False,
            BitSet::new(),
        );
        let mut cache = delivery.clone();
        rejects_update(
            &mut cache,
            delivery,
            &Projection::Everything,
            &keyed(Tiling::Record(Default::default())),
        );
    }

    #[test]
    fn a_finished_sum_for_a_key_cannot_be_folded_again_by_the_memo() {
        let total = |amount| {
            Tile::data_function(
                ColumnValue::UInts(vec![7]),
                Box::new(Tile::Aggregation {
                    kind: AggregateKind::Sum,
                    accumulator: Box::new(Tile::Scalar(ColumnValue::Ints(vec![amount]))),
                    terminal: ColumnValue::Bools(vec![true]),
                }),
                Predicate::False,
                BitSet::new(),
            )
        };
        let mut cache = total(30);
        rejects_update(
            &mut cache,
            total(99),
            &Projection::Everything,
            &keyed(Tiling::Aggregation {
                kind: AggregateKind::Sum,
                accumulator: Box::new(integer()),
            }),
        );
    }

    fn customers(parents: &[u64], starts: &[usize], keys: &[u64], amounts: &[i64]) -> Tile {
        let history = Tile::grouped(
            starts.to_vec(),
            ColumnValue::UInts(keys.to_vec()),
            Box::new(Tile::Scalar(ColumnValue::Ints(amounts.to_vec()))),
            Predicate::False,
            BitSet::new(),
        );
        Tile::data_function(
            ColumnValue::UInts(parents.to_vec()),
            Box::new(Tile::record(HashMap::from([("history".into(), history)]))),
            Predicate::False,
            BitSet::new(),
        )
    }

    #[rstest::rstest]
    fn an_exact_insert_preserves_the_next_customers_run_and_rejects_updates(
        #[values(false, true)] record_items: bool,
    ) {
        let orders = |parents: &[u64], starts: &[usize], keys: &[u64], amounts: &[i64]| {
            let mut tile = customers(parents, starts, keys, amounts);
            if record_items {
                let Tile::Record { fields, .. } = tile.deepest_values_mut() else {
                    unreachable!()
                };
                let history = fields.get_mut("history").unwrap().deepest_values_mut();
                *history = Tile::record(HashMap::from([("total".into(), history.clone())]));
            }
            tile
        };
        let mut cache = orders(&[7, 8], &[0, 1], &[1, 4], &[10, 84]);
        let order = |key| {
            Projection::within(
                CurryLevel::OUTERMOST,
                Predicate::point(Value::UInt(7)),
                Projection::of_field(
                    "history",
                    Projection::admitting(Predicate::point(Value::UInt(key))),
                ),
            )
        };
        for key in [4, 2] {
            let mut delivery = orders(&[7], &[0], &[key], &[key as i64 * 10]);
            assert!(
                cache
                    .insert_memo_items(
                        &mut delivery,
                        &order(key),
                        &customers_tiling(if record_items {
                            Tiling::Record([("total".into(), integer())].into())
                        } else {
                            integer()
                        })
                    )
                    .is_some()
            );
        }
        assert_eq!(
            cache,
            orders(&[7, 8], &[0, 3], &[1, 4, 2, 4], &[10, 40, 20, 84])
        );
        let update = orders(&[7], &[0], &[4], &[99]);
        let tiling = customers_tiling(if record_items {
            Tiling::Record([("total".into(), integer())].into())
        } else {
            integer()
        });
        rejects_update(&mut cache, update.clone(), &order(4), &tiling);
        rejects_update(&mut cache, update, &Projection::Everything, &tiling);
    }

    fn histories() -> Projection {
        Projection::within(
            CurryLevel::OUTERMOST,
            Predicate::point(Value::UInt(7)).union(&Predicate::point(Value::UInt(9))),
            Projection::of_field("history", Projection::Everything),
        )
    }

    #[test]
    fn batched_items_follow_the_cached_parent_order_and_preserve_siblings() {
        let mut cache = customers(&[7, 8, 9], &[0, 1, 2], &[1, 1, 1], &[71, 81, 91]);
        // Same item key under different parents; the producer enumerates the parents
        // in the opposite order. Row 8 has no delivery.
        let mut batch = customers(&[9, 7], &[0, 2], &[4, 2, 4], &[94, 92, 74]);
        let mut reference = cache.clone();
        reference.merge(batch.clone());
        assert!(
            cache
                .insert_memo_items(&mut batch, &histories(), &customers_tiling(integer()))
                .is_some()
        );
        assert_eq!(cache, reference);
        assert_eq!(
            cache,
            customers(
                &[7, 8, 9],
                &[0, 2, 3],
                &[1, 4, 1, 1, 4, 2],
                &[71, 74, 81, 91, 94, 92]
            )
        );

        // Closure without an item must survive even if no column is moved.
        let mut close = customers(&[9, 7], &[0, 0], &[], &[]);
        let Tile::Record { fields, .. } = close.deepest_values_mut() else {
            unreachable!()
        };
        let Tile::DataFunction {
            domain_predicate, ..
        } = fields.get_mut("history").unwrap()
        else {
            unreachable!()
        };
        *domain_predicate = Predicate::qualified(Predicate::point(Value::UInt(9)), Predicate::True);
        reference.merge(close.clone());
        assert!(
            cache
                .insert_memo_items(&mut close, &histories(), &customers_tiling(integer()))
                .is_some()
        );
        assert_eq!(cache, reference);
    }

    #[test]
    fn a_history_close_returns_only_the_end_even_before_the_items_are_published() {
        let tiling = customers_tiling(integer());
        let mut cache = customers(&[7, 9], &[0, 0], &[], &[]);
        let items = customers(&[9, 7], &[0, 1], &[4, 4], &[94, 74]);
        let payload = items.to_guard();
        let first = cache.append(items, &histories(), &tiling);
        assert_eq!(Projection::of(&first), Projection::of(&payload));

        let mut close = customers(&[9], &[0], &[], &[]);
        let Tile::Record { fields, .. } = close.deepest_values_mut() else {
            unreachable!()
        };
        let Tile::DataFunction {
            domain_predicate, ..
        } = fields.get_mut("history").unwrap()
        else {
            unreachable!()
        };
        *domain_predicate = Predicate::qualified(Predicate::point(Value::UInt(9)), Predicate::True);
        let whole_history = close.to_guard();
        let end = cache.append(close.clone(), &histories(), &tiling);
        let expected = guard_minus(&whole_history, &first);
        assert!(!end.is_empty());
        assert!(end.intersect(&first).is_empty());
        assert_eq!(Projection::of(&end), Projection::of(&expected));
        assert!(cache.append(close, &histories(), &tiling).is_empty());
    }

    #[test]
    fn a_new_parent_falls_back_before_any_cached_parent_is_changed() {
        let mut cache = customers(&[7], &[0], &[1], &[71]);
        let before = cache.clone();
        let mut batch = customers(&[7, 9], &[0, 1], &[2, 1], &[72, 91]);
        assert!(
            cache
                .insert_memo_items(&mut batch, &histories(), &customers_tiling(integer()))
                .is_none()
        );
        assert_eq!(cache, before);
        let mut reference = before;
        reference.merge(batch.clone());
        cache.append(batch, &histories(), &customers_tiling(integer()));
        assert_eq!(cache, reference);
    }

    #[test]
    fn a_closed_collection_rejects_a_new_customer_with_empty_history() {
        let mut cache = customers(&[7], &[0], &[], &[]);
        let Tile::DataFunction {
            domain_predicate, ..
        } = &mut cache
        else {
            unreachable!()
        };
        *domain_predicate = Predicate::True;
        let mut incoming = customers(&[8], &[0], &[], &[]);
        rejects_update(
            &mut cache,
            incoming.clone(),
            &Projection::Everything,
            &customers_tiling(integer()),
        );
        let Tile::DataFunction { domain, .. } = &mut incoming else {
            unreachable!()
        };
        *domain = ColumnValue::UInts(vec![7]);
        cache.append(
            incoming,
            &Projection::Everything,
            &customers_tiling(integer()),
        );
    }
}
