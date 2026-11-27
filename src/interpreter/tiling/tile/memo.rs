//! Insert-only writes to a memo's materialized tile.
use super::*;
use crate::interpreter::{Projection, tile_operators::guard_minus};

// A broad delivery may inspect prior coverage once. Reading this same cache a
// second time inside the direct calculation would reintroduce the snapshot fallback.
// Track the tile on its worker thread; input tiles and the test oracle are independent.
#[cfg(test)]
thread_local! {
    static CACHE_SNAPSHOTS: std::cell::Cell<Option<(*const Tile, bool)>> = const { std::cell::Cell::new(None) };
}

#[cfg(test)]
struct CacheSnapshotCheck(Option<(*const Tile, bool)>);

#[cfg(test)]
impl CacheSnapshotCheck {
    fn enter(cache: &Tile) -> Self {
        Self(CACHE_SNAPSHOTS.replace(Some((cache, false))))
    }
}

#[cfg(test)]
impl Drop for CacheSnapshotCheck {
    fn drop(&mut self) {
        CACHE_SNAPSHOTS.set(self.0);
    }
}

#[cfg(test)]
pub(super) fn check_cache_snapshot(tile: &Tile) {
    if let Some((cache, already_read)) = CACHE_SNAPSHOTS.get()
        && std::ptr::eq(cache, tile)
    {
        assert!(
            !already_read,
            "memo append took two whole-cache snapshots to produce a delta"
        );
        CACHE_SNAPSHOTS.set(Some((cache, true)));
    }
}

impl Tile {
    /// Materialize a delivery and return the newly completed region. Reclaimed
    /// regions are excluded even when a later statement covers them.
    pub(crate) fn append(
        &mut self,
        incoming: Tile,
        projection: &Projection,
        tiling: &Tiling,
        released: &TileGuard,
    ) -> TileGuard {
        #[cfg(test)]
        let before = self.to_guard().union(released);
        #[cfg(test)]
        let snapshots = CacheSnapshotCheck::enter(self);
        let delta = self.append_direct(incoming, projection, tiling, released);
        #[cfg(test)]
        {
            drop(snapshots);
            // Whole-cache reads are an independent oracle for all the direct append paths.
            let after = self.to_guard().union(released);
            let expected = guard_minus(&after, &before);
            assert!(
                delta.subsumes(&expected) && expected.subsumes(&delta),
                "memo append must return its exact delta for {projection:?}: returned {delta:?}, expected {expected:?}"
            );
        }
        delta
    }

    fn append_direct(
        &mut self,
        mut incoming: Tile,
        projection: &Projection,
        tiling: &Tiling,
        released: &TileGuard,
    ) -> TileGuard {
        #[cfg(any(test, debug_assertions))]
        self.check_memo_row(
            &incoming,
            Some(0),
            0,
            &mut Vec::new(),
            false,
            cfg!(test).then_some(released),
        );

        // The fast paths track cells still in the cache. A closing statement can
        // also cover cells the reader previously took and the cache has reclaimed.
        let unreleased = |delta: TileGuard| guard_minus(&delta, released);

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
            return unreleased(TileGuard::Function(FunctionGuard::Domain(
                after.minus(&before),
            )));
        }

        if let Some(delta) = self.insert_memo_items(&mut incoming, projection, tiling) {
            return unreleased(delta);
        }

        if projection.names_part_of_values() && incoming.to_guard().is_empty() {
            // A field release can leave only its enclosing key in an input answer.
            return tiling.empty_guard();
        }

        if let Some(nested) = NestedAppend::prepare(self, &incoming, projection, tiling) {
            self.merge(incoming);
            // merge already compacts earlier statements. Readers projecting below a
            // newly closed ancestor still need the child statement recorded by settle.
            return unreleased(nested.settle(self, tiling));
        }

        incoming.state_nested_memo_items();
        let arrived = incoming.to_guard();
        let known = self.memo_coverage_for(&arrived, tiling).union(released);
        let nested = nested_answer(&incoming, &arrived, projection);
        self.merge(incoming);
        if let Some(nested) = nested {
            nested.merge_into(self, tiling);
        }
        self.close_memo_positions(tiling);
        // A closure can add a statement without adding a physical item.
        guard_minus(&arrived.union(&self.statements_guard(0)), &known)
    }

    /// Previously held facts relevant to this delivery or a row end it can establish.
    /// Statements may cover absent rows and so are retained even for an empty selection.
    fn memo_coverage_for(&self, arrived: &TileGuard, ty: &Tiling) -> TileGuard {
        if let (Tile::Record { fields, .. }, Tiling::Record(types), TileGuard::Record(parts)) =
            (self, ty, arrived)
        {
            return TileGuard::Record(
                fields
                    .iter()
                    .map(|(name, field)| {
                        let ty = &types[name];
                        let known = match parts.get(name) {
                            Some(part) if !part.is_empty() => field.memo_coverage_for(part, ty),
                            _ => field.statements_guard(0),
                        };
                        (name.clone(), known)
                    })
                    .collect(),
            );
        }
        let Tile::DataFunction {
            domain, codomain, ..
        } = self
        else {
            return self.to_guard();
        };
        let touched = arrived.touched_keys();
        if touched.is_true()
            || covers_domain(
                &self.level_statement().union(&touched),
                ty.domain_extent().as_ref(),
            )
        {
            return self.to_guard();
        }
        let selected: Vec<_> = (0..domain.len())
            .filter(|&i| touched.contains(&domain.index_at(i)))
            .collect();
        if selected.is_empty() {
            return self.statements_guard(0);
        }
        let rows = Tile::data_function(
            domain.select_indices(selected.iter().copied(), selected.len()),
            Box::new(codomain.select_rows(&selected)),
            self.level_statement(),
            Default::default(),
        );
        rows.to_guard().union(&self.statements_guard(0))
    }

    fn state_nested_memo_items(&mut self) {
        let nested_scalars = |tile: &Tile| {
            tile.innermost_depth().is_some_and(|d| d > 0)
                && matches!(tile.deepest_values(), Tile::Scalar(_))
        };
        if let Tile::DataFunction {
            codomain, domain, ..
        } = self
            && let Tile::Record { fields, .. } = &mut **codomain
        {
            let mut paths = None;
            for field in fields.values_mut().filter(|v| nested_scalars(v)) {
                let rows = paths.get_or_insert_with(|| {
                    (0..domain.len())
                        .map(|i| vec![domain.index_at(i)])
                        .collect::<Vec<_>>()
                });
                field.state_held_values_under(rows);
            }
        } else if nested_scalars(self) {
            self.state_held_values_complete();
        }
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
    #[cfg(any(test, debug_assertions))]
    fn check_memo_row(
        &self,
        incoming: &Tile,
        cached_row: Option<usize>,
        row: usize,
        path: &mut Vec<Value>,
        closed: bool,
        released: Option<&TileGuard>,
    ) {
        let release = released.map(|guard| super::super::guard::Parts::of(Some(guard)));
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
                    codomain.check_memo_row(
                        values,
                        previous,
                        i,
                        path,
                        final_key,
                        release.as_ref().and_then(|p| p.codomain.as_ref()),
                    );
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
                let released_fields = release.as_ref().and_then(|p| p.record.as_ref());
                #[cfg(test)]
                if path.len() >= 2 {
                    // Readers can release an unused field before the item reaches this Memo.
                    // Among the remaining scalar siblings a delivery carries all or none.
                    let mut present = added.iter().filter_map(|(name, value)| {
                        if !matches!(value, Tile::Scalar(_)) {
                            return None;
                        }
                        if let Some(TileGuard::Scalar(rows)) =
                            released_fields.and_then(|f| f.get(name))
                            && TileGuard::leaf_rows(rows).contains_path(path)
                        {
                            return None;
                        }
                        Some(physical(value, missing.get(name), row).is_some())
                    });
                    if let Some(first) = present.next() {
                        assert!(
                            present.all(|here| here == first),
                            "memo needs direct delta support for split scalar fields of a nested record at {path:?}"
                        );
                    }
                }
                for (name, value) in added {
                    if let Some(at) = physical(value, missing.get(name), row) {
                        let old = &fields[name];
                        let cached = cached_row.and_then(|i| physical(old, absent.get(name), i));
                        old.check_memo_row(
                            value,
                            cached,
                            at,
                            path,
                            closed,
                            released_fields.and_then(|f| f.get(name)),
                        );
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
                                "memo received a different tag for a previously delivered key at \
                                 {path:?}"
                            );
                        }
                        old.tile.check_memo_row(
                            &arm.tile,
                            cached,
                            at,
                            path,
                            closed,
                            release.as_ref().and_then(|p| p.union.as_ref()?.get(tag)),
                        );
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
        let name = projected_field(projection)?;
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

/// Records keep their collection depth through both fields and variant arms.
/// The single field of existing or arriving outer rows named by an exact pull.
fn projected_field(projection: &Projection) -> Option<&SmolStr> {
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
    fields.first_key_value().map(|(name, _)| name)
}

/// One chain of nested collections, optionally rooted in a projected customer field.
/// Its statements use full key paths even inside a record.
struct NestedAppend<'a> {
    field: Option<&'a SmolStr>,
    tiling: &'a Tiling,
    previous: Predicate,
    /// Each level carries its completion statement and the parent paths in this delivery.
    levels: Vec<(Predicate, Vec<Vec<Value>>)>,
}

impl<'a> NestedAppend<'a> {
    fn prepare(
        cache: &Tile,
        input: &Tile,
        projection: &'a Projection,
        tiling: &'a Tiling,
    ) -> Option<Self> {
        let field = projected_field(projection);
        let (chain, old, ty, rows, outer_closed) = if let Some(name) = field {
            let Tile::DataFunction {
                domain,
                codomain,
                domain_predicate,
                ..
            } = input
            else {
                return None;
            };
            let Tile::Record { fields, .. } = &**codomain else {
                return None;
            };
            let Tile::Record {
                fields: previous, ..
            } = cache.values_at(CurryLevel::new(1))
            else {
                return None;
            };
            let Tiling::Record(types) = tiling.values_at(CurryLevel::new(1)) else {
                return None;
            };
            if !domain_predicate.is_false() {
                return None;
            }
            (
                fields.get(name)?,
                previous.get(name)?,
                types.get(name)?,
                (0..domain.len())
                    .map(|i| vec![domain.index_at(i)])
                    .collect(),
                cache.level_statement(),
            )
        } else {
            (input, cache, tiling, vec![Vec::new()], Predicate::False)
        };
        let levels = ty.levels();
        if levels < 2 || !matches!(ty.deepest_values(), Tiling::Scalar(_)) {
            return None;
        }
        let leaf = CurryLevel::new(levels - 1);
        let mut evidence = Vec::with_capacity(levels);
        let mut parents = rows;
        for depth in 0..levels {
            let node = chain.values_at(CurryLevel::new(depth));
            let mut stated = node.level_statement();
            if depth == leaf.index() {
                // A bare key awaiting a value cannot be recorded as a final scalar.
                let Tile::DataFunction {
                    domain, codomain, ..
                } = node
                else {
                    unreachable!()
                };
                let Tile::DataFunction {
                    domain: held,
                    codomain: values,
                    ..
                } = old.values_at(leaf)
                else {
                    unreachable!()
                };
                if !codomain.holds_plain_values(domain.len())
                    || !values.holds_plain_values(held.len())
                {
                    return None;
                }
                stated = stated.union(&node.unstated_held_keys(&parents));
            }
            let children = if depth < leaf.index() {
                node.key_paths(&parents)
            } else {
                Vec::new()
            };
            evidence.push((stated, parents));
            parents = children;
        }
        Some(Self {
            field,
            tiling: ty,
            previous: old.completion_at(leaf).union(&outer_closed.descend(levels)),
            levels: evidence,
        })
    }

    fn settle(self, cache: &mut Tile, root_tiling: &Tiling) -> TileGuard {
        let Self {
            field,
            tiling,
            previous,
            levels,
        } = self;
        let (chain, parents) = if let Some(name) = field {
            let Tile::DataFunction {
                domain, codomain, ..
            } = cache
            else {
                unreachable!()
            };
            let Tile::Record { fields, .. } = &mut **codomain else {
                unreachable!()
            };
            (fields.get_mut(name).unwrap(), Some(&*domain))
        } else {
            (cache, None)
        };
        let leaf = CurryLevel::new(levels.len() - 1);
        let mut from_children = Predicate::False;
        let mut delta = Predicate::False;
        for (depth, (arrived, rows)) in levels.into_iter().enumerate().rev() {
            let level = CurryLevel::new(depth);
            let mut changed = arrived.union(&from_children);
            let ext = tiling.values_at(level).domain_extent();
            let mut stated = chain.values_at(level).level_statement().union(&changed);
            // A statement covering the entire finite extent at a root-chain level
            // also covers future groups. An exact field delivery is scoped to its rows.
            if field.is_none() && covers_domain(&stated, ext.as_ref()) {
                stated = Predicate::True;
            }
            if stated.is_true() {
                // Merging a following child can also make the level universal.
                changed = Predicate::True;
            }
            let mut closed = if depth == 0 && field.is_none() {
                Predicate::False
            } else {
                closed_memo_rows(chain, parents, depth, &changed, &stated, ext.as_ref(), rows)
            };
            let Tile::DataFunction {
                domain_predicate, ..
            } = chain.values_at_mut(level)
            else {
                unreachable!()
            };
            *domain_predicate = stated;
            if depth == 0 {
                if field.is_some() {
                    closed = closed.descend(1);
                }
                *domain_predicate = domain_predicate.union(&closed);
                changed = changed.union(&closed);
            }
            delta = delta.union(&changed.descend(leaf.index() - depth));
            from_children = closed;
        }
        let new = delta.minus(&previous);
        let guard = leaf.wrap_guard(TileGuard::Function(FunctionGuard::Domain(new)));
        if let Some(name) = field {
            let TileGuard::Record(mut fields) =
                root_tiling.values_at(CurryLevel::new(1)).empty_guard()
            else {
                unreachable!()
            };
            fields.insert(name.clone(), guard);
            TileGuard::Function(FunctionGuard::Codomain(Box::new(TileGuard::Record(fields))))
        } else {
            // Keep whole rows in their canonical, shallow representation.
            Projection::of(&guard)
                .expect("a chain of collection keys")
                .guard(tiling)
        }
    }
}

/// Rows whose children now cover their extent. Usually the input identifies all
/// candidates. A statement of absence may carry no physical rows: look those up
/// in the cache, following only branches reached by the statement.
fn closed_memo_rows(
    chain: &Tile,
    parents: Option<&ColumnValue>,
    depth: usize,
    changed: &Predicate,
    stated: &Predicate,
    extent: Option<&Extent>,
    supplied: Vec<Vec<Value>>,
) -> Predicate {
    if changed.is_false() {
        return Predicate::False;
    }
    let level = CurryLevel::new(depth + usize::from(parents.is_some()));
    let affected = Projection::keys_at(level, changed.clone()).above(level);
    let present = Predicate::union_all(supplied.iter().map(|p| Predicate::exactly(p)).collect());
    let rows = if affected.minus(&Projection::keys_at(level.enclosing().unwrap(), present))
        == Projection::Nothing
    {
        supplied
    } else {
        let mut selected: Vec<_> = match parents {
            Some(keys) => (0..keys.len())
                .filter_map(|r| {
                    let path = vec![keys.index_at(r)];
                    (!changed.within(&path, depth).is_false()).then_some((r, path))
                })
                .collect(),
            None => vec![(0, Vec::new())],
        };
        for d in 0..depth {
            let node = chain.values_at(CurryLevel::new(d));
            let Tile::DataFunction { domain, .. } = node else {
                unreachable!()
            };
            let mut next = Vec::new();
            for (row, path) in selected {
                let (start, end) = node.row_run(row);
                for i in start..end {
                    let mut child = path.clone();
                    child.push(domain.index_at(i));
                    if !changed.within(&child, depth - d - 1).is_false() {
                        next.push((i, child));
                    }
                }
            }
            selected = next;
        }
        selected.into_iter().map(|(_, path)| path).collect()
    };
    completed_parents(rows.iter().map(Vec::as_slice), changed, stated, extent)
}

/// A parent closes on an affected path once its own children cover the domain.
fn completed_parents<'a>(
    paths: impl Iterator<Item = &'a [Value]>,
    changed: &Predicate,
    stated: &Predicate,
    extent: Option<&Extent>,
) -> Predicate {
    Predicate::union_all(
        paths
            .filter(|path| {
                !changed.within(path, 0).is_false()
                    && covers_domain(&stated.within(path, 0), extent)
            })
            .map(Predicate::exactly)
            .collect(),
    )
}

/// The keys a nested answer settled, and their enclosing rows if the answer holds
/// them all. An absence can settle paths in a row held only by an earlier answer.
struct NestedAnswer {
    level: CurryLevel,
    keys: Predicate,
    rows: Option<Vec<Vec<Value>>>,
}

fn nested_answer(input: &Tile, held: &TileGuard, requested: &Projection) -> Option<NestedAnswer> {
    let Tile::DataFunction { codomain, .. } = input else {
        return None;
    };
    if !codomain.is_data_function() {
        return None;
    }
    let paths = Projection::of(held).ok()?;
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
            let candidates = rows.take().unwrap_or_else(|| cache.paths_at(parent));
            arrived = completed_parents(
                candidates
                    .iter()
                    .map(Vec::as_slice)
                    .filter(|path| !already_closed.contains_path(path)),
                &arrived,
                &stated,
                extent.as_ref(),
            );
            if arrived.is_false() {
                return;
            }
            level = parent;
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
    let beneath_whole = matches!(
        codomain.as_ref(),
        Tile::DataFunction { domain_predicate, .. } if domain_predicate.is_true()
    );
    let whole_rows =
        beneath_whole.then(|| domain_predicate.union(&Predicate::from_column_value(domain)));
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
    use crate::interpreter::tile_operators::guard_minus;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    impl Tile {
        fn append_unreleased(
            &mut self,
            input: Tile,
            projection: &Projection,
            ty: &Tiling,
        ) -> TileGuard {
            self.append(input, projection, ty, &ty.empty_guard())
        }
    }

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
            cache.append_unreleased(update, projection, tiling)
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
    fn a_closure_only_append_excludes_reclaimed_keys_from_its_raw_delta() {
        let ty = keyed(integer());
        let keys = |keys: &[u64]| Predicate::from_column_value(&ColumnValue::UInts(keys.to_vec()));
        let guard = |keys| TileGuard::Function(FunctionGuard::Domain(keys));
        let mut cache = ty.empty_tile();
        let mut close = ty.empty_tile();
        let Tile::DataFunction {
            domain_predicate, ..
        } = &mut close
        else {
            unreachable!()
        };
        *domain_predicate = keys(&[4, 5, 6, 7]);
        let released = guard(keys(&[5, 6]));
        let delta = cache.append(close, &Projection::Everything, &ty, &released);
        assert_eq!(delta, guard(keys(&[4, 7])));
    }

    #[test]
    #[should_panic(expected = "memo append took two whole-cache snapshots")]
    fn a_second_snapshot_of_the_same_cache_fails_the_direct_append_check() {
        let cache = ints(&[0], &[1]);
        let input = cache.clone();
        let _check = CacheSnapshotCheck::enter(&cache);
        cache.to_guard();
        input.to_guard();
        cache.to_guard();
    }

    #[test]
    fn a_flat_memo_rejects_a_second_value_and_the_rest_of_its_batch() {
        let mut cache = ints(&[], &[]);
        cache.append_unreleased(
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
        assert_eq!(
            cache.append_unreleased(key, &Projection::Everything, &tiling),
            held
        );
        let mut absent = ints(&[], &[]);
        let Tile::DataFunction {
            domain_predicate, ..
        } = &mut absent
        else {
            unreachable!()
        };
        *domain_predicate = Predicate::point(Value::UInt(9));
        let expected = absent.to_guard();
        let next = cache.append_unreleased(absent, &Projection::Everything, &tiling);
        assert_eq!(next, expected);
        assert!(next.intersect(&held).is_empty());
    }

    #[test]
    fn a_complete_record_item_closes_its_single_item_day() {
        let record = Tile::record(
            [
                ("sku".into(), Tile::Scalar(ColumnValue::Ints(vec![812]))),
                ("qty".into(), Tile::Scalar(ColumnValue::Ints(vec![3]))),
            ]
            .into(),
        );
        let ty = keyed(Tiling::data_function(
            Extent::uint_range(1),
            Tiling::Record([("sku".into(), integer()), ("qty".into(), integer())].into()),
        ));
        let mut day = ints(&[3], &[]);
        let mut items = ints(&[0], &[]);
        *items.deepest_values_mut() = record;
        *day.deepest_values_mut() = items;
        let mut cache = ty.empty_tile();
        let delta = cache.append_unreleased(day, &Projection::Everything, &ty);
        let closed = Projection::admitting(Predicate::point(Value::UInt(3))).guard(&ty);
        assert!(delta.subsumes(&closed));
        assert!(cache.level_statement().contains(&Value::UInt(3)));
    }

    #[rstest::rstest]
    #[case::record(false)]
    #[case::tagged_record(true)]
    #[should_panic(expected = "memo needs direct delta support for split scalar fields")]
    fn a_nested_item_cannot_deliver_one_unreleased_scalar_field(#[case] tagged: bool) {
        let record = Tiling::Record([("sku".into(), integer()), ("qty".into(), integer())].into());
        let mut item = record.empty_tile();
        let Tile::Record { fields, absent } = &mut item else {
            unreachable!()
        };
        fields.insert("sku".into(), Tile::Scalar(ColumnValue::Ints(vec![812])));
        absent.insert("qty".into(), [0].into_iter().collect());
        let item_ty = if tagged {
            let tag = crate::ccl::FieldKey::Name("sale".into());
            item = Tile::Union(TagMap::from_arms(vec![(
                tag.clone(),
                UnionArmTile {
                    rows: vec![0],
                    tile: item,
                },
            )]));
            Tiling::Union(TagMap::from_arms(vec![(tag, record)]))
        } else {
            record
        };
        let ty = keyed(keyed(item_ty));
        let mut day = ints(&[3], &[]);
        let mut items = ints(&[0], &[]);
        *items.deepest_values_mut() = item;
        *day.deepest_values_mut() = items;
        ty.empty_tile()
            .append_unreleased(day, &Projection::Everything, &ty);
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
    fn an_unqualified_finite_child_statement_also_closes_future_groups_once() {
        let ty = keyed(Tiling::data_function(Extent::uint_range(2), integer()));
        let mut cache = ty.empty_tile();
        let mut absent = ty.empty_tile();
        let leaf = CurryLevel::new(1);
        let Tile::DataFunction {
            domain_predicate, ..
        } = absent.values_at_mut(leaf)
        else {
            unreachable!()
        };
        *domain_predicate = Predicate::from_column_value(&ColumnValue::UInts(vec![0, 1]));
        let delta = cache.append_unreleased(absent.clone(), &Projection::Everything, &ty);
        assert!(cache.values_at(leaf).level_statement().is_true());
        assert_eq!(Projection::of(&delta).unwrap(), Projection::Everything);
        assert!(
            cache
                .append_unreleased(absent, &Projection::Everything, &ty)
                .is_empty()
        );
    }

    #[test]
    fn an_absence_closes_only_its_customers_history_after_a_mixed_record_delivery() {
        let history = Tiling::data_function(
            Extent::uint_range(1),
            Tiling::data_function(Extent::uint_range(3), integer()),
        );
        let ty = keyed(Tiling::Record(
            [("id".into(), integer()), ("history".into(), history)].into(),
        ));
        let column = |starts, keys, values| {
            Tile::grouped(
                starts,
                ColumnValue::UInts(keys),
                Box::new(values),
                Predicate::False,
                Default::default(),
            )
        };
        // Both customers have day 0. Only customer 7 has its first two items.
        let days = column(
            vec![0, 1],
            vec![0, 0],
            column(
                vec![0, 2],
                vec![0, 1, 0],
                Tile::Scalar(ColumnValue::Ints(vec![70, 71, 90])),
            ),
        );
        let batch = column(
            vec![0],
            vec![7, 9],
            Tile::record(
                [
                    ("id".into(), Tile::Scalar(ColumnValue::Ints(vec![7, 9]))),
                    ("history".into(), days),
                ]
                .into(),
            ),
        );
        let mut cache = ty.empty_tile();
        let payload = cache.append_unreleased(batch, &Projection::Everything, &ty);
        let history_of = |key| {
            Projection::within(
                CurryLevel::OUTERMOST,
                Predicate::point(Value::UInt(key)),
                Projection::of_field("history", Projection::Everything),
            )
        };
        // No physical customer, day or item accompanies this statement.
        let mut absent = ty.empty_tile();
        let Tile::Record { fields, .. } = absent.deepest_values_mut() else {
            unreachable!()
        };
        let Tile::DataFunction {
            domain_predicate, ..
        } = fields
            .get_mut("history")
            .unwrap()
            .values_at_mut(CurryLevel::new(1))
        else {
            unreachable!()
        };
        *domain_predicate = Predicate::exactly(&[Value::UInt(7), Value::UInt(0), Value::UInt(2)]);
        let region = history_of(7);
        let end = cache.append_unreleased(absent.clone(), &region, &ty);
        let expected = region.minus(&Projection::of(&payload).unwrap());
        let actual = Projection::of(&end).unwrap();
        assert_eq!(expected.minus(&actual), Projection::Nothing);
        assert_eq!(actual.minus(&expected), Projection::Nothing);
        assert_eq!(actual.intersect(&history_of(9)), Projection::Nothing);
        assert!(cache.append_unreleased(absent, &region, &ty).is_empty());
    }

    #[test]
    fn a_history_close_returns_only_the_end_even_before_the_items_are_published() {
        let tiling = customers_tiling(integer());
        let mut cache = customers(&[7, 9], &[0, 0], &[], &[]);
        let items = customers(&[9, 7], &[0, 1], &[4, 4], &[94, 74]);
        let payload = items.to_guard();
        let first = cache.append_unreleased(items, &histories(), &tiling);
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
        let end = cache.append_unreleased(close.clone(), &histories(), &tiling);
        let expected = guard_minus(&whole_history, &first);
        assert!(!end.is_empty());
        assert!(end.intersect(&first).is_empty());
        assert_eq!(Projection::of(&end), Projection::of(&expected));
        assert!(
            cache
                .append_unreleased(close, &histories(), &tiling)
                .is_empty()
        );
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
        cache.append_unreleased(batch, &histories(), &customers_tiling(integer()));
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
        cache.append_unreleased(
            incoming,
            &Projection::Everything,
            &customers_tiling(integer()),
        );
    }
}
