//! Insert-only writes to a memo's materialized tile.
use super::*;
use crate::interpreter::Projection;

impl Tile {
    /// Materialize a memo delivery. Complete leaves are single-assignment. A later
    /// delivery can add descendants of an open row or advance its completion statement.
    pub(crate) fn append(&mut self, mut incoming: Tile, projection: &Projection) {
        #[cfg(test)]
        self.check_memo_row(&incoming, Some(0), 0, &mut Vec::new(), false);

        if self.insert_memo_items(&incoming, projection).is_some() {
            return;
        }
        if let (
            Tile::DataFunction { codomain, .. },
            Tile::DataFunction {
                domain: new,
                codomain: values,
                domain_predicate: stated,
                ..
            },
        ) = (&*self, &mut incoming)
            && matches!((&**codomain, &**values), (Tile::Scalar(_), Tile::Scalar(_)))
        {
            // A held scalar is final, so its key contributes to the completion statement.
            if !values.is_empty() {
                *stated = stated.union(&Predicate::from_column_value(new));
            }
            self.append_keys(incoming, true);
            return;
        }
        self.merge(incoming);
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

    /// Insert complete plain items into a single collection field of an existing outer row.
    /// The projection guarantees that no sibling field contributed data or completeness.
    fn insert_memo_items(&mut self, incoming: &Tile, projection: &Projection) -> Option<()> {
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
            codomain,
            keys_follow_beneath: follow,
            ..
        } = self
        else {
            return None;
        };
        let Tile::DataFunction {
            domain,
            codomain: added_record,
            keys_follow_beneath: added_follow,
            domain_predicate: added_complete,
            ..
        } = incoming
        else {
            return None;
        };
        let parent = domain.as_single()?;
        if !added_complete.is_false() || follow != added_follow {
            return None;
        }
        let row = (0..parents.len()).find(|i| parents.index_at(*i) == parent)?;
        let (
            Tile::Record { fields, .. },
            Tile::Record {
                fields: added_fields,
                ..
            },
        ) = (codomain.as_mut(), added_record.as_ref())
        else {
            return None;
        };
        let Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            domain_predicate,
            keys_follow_beneath,
            deleted,
            ..
        } = fields.get_mut(name)?
        else {
            return None;
        };
        let Tile::DataFunction {
            domain: keys,
            codomain: values,
            domain_predicate: stated,
            keys_follow_beneath: new_follow,
            ..
        } = added_fields.get(name)?
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
        if !keys.is_empty() {
            let end = row_starts.get(row + 1).copied().unwrap_or(domain.len());
            domain.insert_column(end, keys.clone());
            codomain.insert_plain_rows(end, values);
            for offset in &mut row_starts[row + 1..] {
                *offset += keys.len();
            }
        }
        *domain_predicate = domain_predicate.union(stated);
        Some(())
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    fn rejects_update(cache: &mut Tile, update: Tile, projection: &Projection) {
        let before = cache.clone();
        let fail = catch_unwind(AssertUnwindSafe(|| cache.append(update, projection)));
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
        cache.append(ints(&[3], &[30]), &Projection::Everything);
        for value in [30, 99] {
            rejects_update(
                &mut cache,
                ints(&[4, 3], &[40, value]),
                &Projection::Everything,
            );
        }
        // Build a malformed delivery without the tile constructor's debug-only check.
        let mut duplicate = ints(&[4, 5], &[40, 41]);
        let Tile::DataFunction { domain, .. } = &mut duplicate else {
            unreachable!()
        };
        *domain = ColumnValue::UInts(vec![4, 4]);
        rejects_update(&mut cache, duplicate, &Projection::Everything);
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
        rejects_update(&mut cache, delivery, &Projection::Everything);
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
        rejects_update(&mut cache, total(99), &Projection::Everything);
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
            let delivery = orders(&[7], &[0], &[key], &[key as i64 * 10]);
            assert!(cache.insert_memo_items(&delivery, &order(key)).is_some());
        }
        assert_eq!(
            cache,
            orders(&[7, 8], &[0, 3], &[1, 4, 2, 4], &[10, 40, 20, 84])
        );
        let update = orders(&[7], &[0], &[4], &[99]);
        rejects_update(&mut cache, update.clone(), &order(4));
        rejects_update(&mut cache, update, &Projection::Everything);
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
        rejects_update(&mut cache, incoming.clone(), &Projection::Everything);
        let Tile::DataFunction { domain, .. } = &mut incoming else {
            unreachable!()
        };
        *domain = ColumnValue::UInts(vec![7]);
        cache.append(incoming, &Projection::Everything);
    }
}
