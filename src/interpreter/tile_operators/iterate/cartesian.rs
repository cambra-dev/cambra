use super::*;

struct Side {
    name: SmolStr,
    extent: Extent,
    tile: Tile,
    released: Predicate,
    producer: String,
}

struct SourceHold {
    source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    producer: String,
    side: usize,
    direct: bool,
}

impl Drop for SourceHold {
    fn drop(&mut self) {
        match self.source.try_borrow_mut() {
            Ok(mut source) => source.retire_producer(&self.producer),
            Err(_) => debug_assert!(
                false,
                "a product retires its source hold outside a source borrow"
            ),
        }
    }
}

pub(super) fn subscribe(
    op: &IterateExtent,
    fields: &HashMap<SmolStr, Extent>,
    consumer: Box<dyn Consumer>,
    cx: &mut Scheduler,
) -> Box<dyn TileProducer> {
    let mut fields: Vec<_> = fields.iter().map(|(n, e)| (n.clone(), e.clone())).collect();
    fields.sort_by(|(a, _), (b, _)| a.cmp(b));
    let (wakeup, gate) = shared_consumer(consumer);
    let leaf = wakeup.shared().clone();
    IterateExtent::add_all_source_handles(&op.extent, leaf.clone(), cx);
    let base = ProducerBase::new(IterateExtentProducer::alloc_id(), op.tiling(), &op.base, cx)
        .sharing(gate)
        .leaf(leaf.clone());
    let mut holds = Vec::new();
    for (side, (_, extent)) in fields.iter().enumerate() {
        let mut sources = Vec::new();
        extent.for_each_source(&mut |source| {
            if !sources.iter().any(|seen| Rc::ptr_eq(seen, source)) {
                sources.push(source.clone());
            }
        });
        for source in sources {
            let producer = format!("IterateExtent#{}:{side}", base.id);
            source.borrow_mut().release(&producer, Predicate::False);
            cx.note_source_producer(producer.clone());
            holds.push(SourceHold {
                source,
                producer,
                side,
                direct: matches!(extent, Extent::DataSourceDomain(_)),
            });
        }
    }
    let sides = fields
        .into_iter()
        .enumerate()
        .map(|(side, (name, extent))| {
            let tiling =
                Tiling::data_function(extent.clone(), Tiling::Scalar(Extent::Base(BaseType::Unit)));
            Side {
                name,
                extent,
                tile: tiling.empty_tile(),
                released: Predicate::False,
                producer: format!("IterateExtent#{}:{side}", base.id),
            }
        })
        .collect();
    Box::new(IterateExtentProducer {
        base,
        iteration: Iteration::Cartesian(Box::new(CartesianIteration {
            sides,
            holds,
            _source_wakeup: leaf,
        })),
    })
}

pub(super) struct CartesianIteration {
    sides: Vec<Side>,
    // Each dimension retains source values independently for downstream lookups and future pairs.
    holds: Vec<SourceHold>,
    _source_wakeup: SharedConsumer,
}

impl CartesianIteration {
    fn read(&mut self, obsolete: &TileGuard) {
        for side in &mut self.sides {
            let known = side.tile.to_guard().projection("IterateExtent");
            let known = match known {
                Projection::Everything => Predicate::True,
                Projection::Nothing => Predicate::False,
                Projection::Keys { keys, .. } => keys,
            }
            .union(&side.released);
            let pending = Predicate::True.minus(&known);
            if pending.is_false() {
                continue;
            }
            let decided = side.extent.decided_region();
            let values = iterate_extent(&side.extent, &side.producer);
            let rows = values.len();
            let mut tile = Tile::data_function(
                values,
                Box::new(Tile::Scalar(ColumnValue::Units(rows))),
                decided.clone(),
                BitSet::new(),
            );
            let tiling = Tiling::data_function(
                side.extent.clone(),
                Tiling::Scalar(Extent::Base(BaseType::Unit)),
            );
            tile.restrict_to(&Projection::admitting(pending), &tiling);
            tile.compact();
            side.tile.merge(tile);
            let Tile::DataFunction {
                domain_predicate, ..
            } = &mut side.tile
            else {
                unreachable!()
            };
            *domain_predicate = domain_predicate.union(&decided);
        }
        self.reclaim_sides(obsolete);
    }

    fn keys(&self, guard: &TileGuard, tiling: &Tiling) -> ColumnValue {
        fn terms<'a>(predicate: &'a Predicate, into: &mut Vec<&'a Predicate>) {
            match predicate {
                Predicate::Or(arms) => arms.iter().for_each(|arm| terms(arm, into)),
                one => into.push(one),
            }
        }
        let region = match guard.projection("IterateExtent") {
            Projection::Everything => Predicate::True,
            Projection::Nothing => Predicate::False,
            Projection::Keys { keys, .. } => keys,
        };
        let fields: HashMap<_, _> = self
            .sides
            .iter()
            .map(|side| (side.name.clone(), side.extent.clone()))
            .collect();
        let mut arms = Vec::new();
        terms(&region, &mut arms);
        let mut seen = std::collections::HashSet::new();
        let mut keys = Vec::new();
        for arm in arms {
            let parts = arm.split_record(&fields);
            let columns = self
                .sides
                .iter()
                .map(|side| {
                    let Tile::DataFunction { domain, .. } = &side.tile else {
                        unreachable!()
                    };
                    let rows: Vec<_> = (0..domain.len())
                        .filter(|&row| parts[&side.name].contains(&domain.index_at(row)))
                        .collect();
                    (
                        side.name.clone(),
                        domain.select_indices(rows.iter().copied(), rows.len()),
                    )
                })
                .collect();
            let mut product = ColumnValue::cartesian_product(columns);
            for key in product.drain_to_value_iter() {
                if seen.insert(key.clone()) {
                    keys.push(key);
                }
            }
        }
        ColumnValue::from_values(
            keys,
            &tiling.domain_extent().expect("product keys have a domain"),
        )
    }

    fn reclaim_sides(&mut self, obsolete: &TileGuard) {
        let released = obsolete.whole_keys();
        if released.is_false() {
            return;
        }
        let fields: HashMap<_, _> = self
            .sides
            .iter()
            .map(|s| (s.name.clone(), s.extent.clone()))
            .collect();
        let mut freed: Vec<Predicate> = self.sides.iter().map(|_| Predicate::False).collect();
        let arms = match &released {
            Predicate::Or(arms) => arms.as_slice(),
            one => std::slice::from_ref(one),
        };
        for arm in arms {
            let parts = arm.split_record(&fields);
            for (index, side) in self.sides.iter().enumerate() {
                if parts
                    .iter()
                    .all(|(name, p)| name == &side.name || p.is_true())
                {
                    freed[index] = freed[index].union(&parts[&side.name]);
                }
            }
        }
        for (side, freed) in self.sides.iter_mut().zip(&freed) {
            side.released = side.released.union(freed);
            side.tile
                .remove_guarded(TileGuard::Function(FunctionGuard::Domain(freed.clone())));
            side.tile.compact();
        }
        for hold in &self.holds {
            let freed = &freed[hold.side];
            if hold.direct || freed.is_true() {
                hold.source
                    .borrow_mut()
                    .release(&hold.producer, freed.clone());
            }
        }
    }

    pub(super) fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::holding(self.sides.iter().map(|side| side.tile.cell_count()).sum())
    }

    pub(super) fn get(&mut self, guard: TileGuard, tiling: &Tiling, obsolete: &TileGuard) -> Tile {
        if !guard.is_empty() {
            self.read(obsolete);
        }
        self.offer(guard, tiling, obsolete)
    }

    pub(super) fn release(&mut self, obsolete: &TileGuard) {
        self.reclaim_sides(obsolete);
    }

    fn held(&self) -> TileGuard {
        let decided = self
            .sides
            .iter()
            .map(|side| {
                let Tile::DataFunction {
                    domain_predicate, ..
                } = &side.tile
                else {
                    unreachable!()
                };
                (side.name.clone(), domain_predicate.clone())
            })
            .collect();
        TileGuard::Function(FunctionGuard::Domain(Predicate::Record(decided)))
    }

    fn offer(&self, guard: TileGuard, tiling: &Tiling, obsolete: &TileGuard) -> Tile {
        let region = match guard.projection("IterateExtent") {
            Projection::Everything => Predicate::True,
            Projection::Nothing => Predicate::False,
            Projection::Keys { keys, .. } => keys,
        };
        let pending = Projection::admitting(region.minus(&obsolete.whole_keys())).guard(tiling);
        let keys = self.keys(&pending, tiling);
        let TileGuard::Function(FunctionGuard::Domain(decided)) = self.held() else {
            unreachable!()
        };
        let mut tile = Tile::data_function(
            keys.clone(),
            Box::new(Tile::Scalar(keys)),
            decided,
            BitSet::new(),
        );
        tile.restrict_to(&guard.projection("IterateExtent"), tiling);
        tile.remove_guarded(obsolete.clone());
        tile
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ccl::Type, interpreter::TestDataSource};

    fn source(name: &str) -> Rc<RefCell<TestDataSource>> {
        Rc::new(RefCell::new(TestDataSource::new(
            name,
            Type::Base(BaseType::Int),
            Extent::Base(BaseType::Int),
        )))
    }
    fn add(source: &Rc<RefCell<TestDataSource>>, keys: &[u64], decided: Predicate) {
        source.borrow_mut().add_data(
            &keys
                .iter()
                .map(|&k| (Value::UInt(k), Value::Int(k as i64)))
                .collect::<Vec<_>>(),
        );
        source.borrow_mut().set_yield_predicate(decided);
    }
    fn prefix(last: u64) -> Predicate {
        Predicate::at_or_below(Value::UInt(last))
    }
    fn product(a: Predicate, b: Predicate) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(Predicate::Record(HashMap::from([
            ("a".into(), a),
            ("b".into(), b),
        ]))))
    }
    fn head(a: Extent, b: Extent) -> Box<dyn TileProducer> {
        let mut op = IterateExtent::new(Extent::Record(HashMap::from([
            ("a".into(), a),
            ("b".into(), b),
        ])));
        op.subscribe(
            op.tiling().universal_guard(),
            Box::new(|| {}),
            &mut Scheduler::new(),
        )
    }
    fn rows(head: &mut dyn TileProducer) -> usize {
        let mut tile = head.get(head.tiling().universal_guard());
        tile.compact();
        let Tile::DataFunction { domain, .. } = tile else {
            panic!("a product is a collection")
        };
        domain.len()
    }

    #[test]
    fn release_of_a_pair_retains_both_inputs_for_future_partners() {
        let (a, b) = (source("a"), source("b"));
        add(&a, &[0], prefix(0));
        add(&b, &[0], prefix(0));
        let mut p = head(
            Extent::DataSourceDomain(a.clone()),
            Extent::DataSourceDomain(b.clone()),
        );
        assert_eq!(rows(&mut *p), 1);
        p.release(product(prefix(0), prefix(0)));
        assert!(a.borrow().get_released_predicate().is_false());
        assert!(b.borrow().get_released_predicate().is_false());
        add(&a, &[1], prefix(1));
        add(&b, &[1], prefix(1));
        assert_eq!(rows(&mut *p), 3);
        p.release(p.tiling().universal_guard());
        assert!(a.borrow().get_released_predicate().is_true());
        assert!(b.borrow().get_released_predicate().is_true());
    }

    #[test]
    fn a_released_slice_reclaims_only_its_dimension() {
        let a = source("a");
        add(&a, &[0], prefix(0));
        let mut p = head(Extent::DataSourceDomain(a.clone()), Extent::uint_range(2));
        assert_eq!(rows(&mut *p), 2);
        p.release(product(prefix(0), Predicate::True));
        assert!(
            a.borrow()
                .get_released_predicate()
                .contains(&Value::UInt(0))
        );
        add(&a, &[1], prefix(1));
        assert_eq!(rows(&mut *p), 2);
    }

    #[test]
    fn repeated_source_occurrences_hold_their_dimensions_independently() {
        let a = source("a");
        add(&a, &[0, 1], prefix(1));
        let mut p = head(
            Extent::DataSourceDomain(a.clone()),
            Extent::DataSourceDomain(a.clone()),
        );
        assert_eq!(rows(&mut *p), 4);
        p.release(product(prefix(0), Predicate::True));
        assert!(
            !a.borrow()
                .get_released_predicate()
                .contains(&Value::UInt(0))
        );
        add(&a, &[2], prefix(2));
        assert_eq!(rows(&mut *p), 6);
    }

    #[test]
    fn missing_keys_are_decided_without_becoming_product_values() {
        let (a, b) = (source("a"), source("b"));
        add(&a, &[0, 2], prefix(2));
        add(&b, &[0], prefix(0));
        let mut p = head(Extent::DataSourceDomain(a), Extent::DataSourceDomain(b));
        assert_eq!(rows(&mut *p), 2);
        let held = p.get(p.tiling().universal_guard()).to_guard();
        let key = Value::Record(HashMap::from([
            ("a".into(), Value::UInt(1)),
            ("b".into(), Value::UInt(0)),
        ]));
        assert!(held.covers_path(&[key]));
    }

    #[test]
    fn overlapping_product_regions_offer_each_requested_pair_once() {
        let a = source("a");
        add(&a, &[0, 1, 2], prefix(2));
        let mut p = head(Extent::DataSourceDomain(a), Extent::uint_range(3));
        assert_eq!(rows(&mut *p), 9);
        let guard = product(prefix(1), prefix(0)).union(&product(prefix(0), prefix(1)));
        let mut tile = p.get(guard.clone());
        tile.compact();
        let Tile::DataFunction { domain, .. } = tile else {
            panic!("a product is a collection")
        };
        assert_eq!(domain.len(), 3);
        for row in 0..domain.len() {
            assert!(guard.covers_path(&[domain.index_at(row)]));
        }
        p.release(guard);
        assert_eq!(rows(&mut *p), 6);
    }

    #[test]
    fn three_dimensions_retain_future_partners_after_a_slice_release() {
        let (a, b, c) = (source("a"), source("b"), source("c"));
        for source in [&a, &b, &c] {
            add(source, &[0, 1], prefix(1));
        }
        let mut op = IterateExtent::new(Extent::Record(HashMap::from([
            ("a".into(), Extent::DataSourceDomain(a.clone())),
            ("b".into(), Extent::DataSourceDomain(b.clone())),
            ("c".into(), Extent::DataSourceDomain(c.clone())),
        ])));
        let mut p = op.subscribe(
            op.tiling().universal_guard(),
            Box::new(|| {}),
            &mut Scheduler::new(),
        );
        assert_eq!(rows(&mut *p), 8);
        p.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::Record(HashMap::from([
                ("a".into(), prefix(0)),
                ("b".into(), Predicate::True),
                ("c".into(), Predicate::True),
            ])),
        )));
        assert!(
            a.borrow()
                .get_released_predicate()
                .contains(&Value::UInt(0))
        );
        assert!(b.borrow().get_released_predicate().is_false());
        assert!(c.borrow().get_released_predicate().is_false());
        add(&a, &[2], prefix(2));
        assert_eq!(rows(&mut *p), 8);
    }

    #[test]
    fn a_nested_record_dimension_keeps_keys_for_later_arrivals() {
        let a = source("a");
        add(&a, &[0, 1], prefix(1));
        let nested = Extent::Record(HashMap::from([
            ("x".into(), Extent::DataSourceDomain(a.clone())),
            ("y".into(), Extent::uint_range(2)),
        ]));
        let mut p = head(nested, Extent::uint_range(2));
        assert_eq!(rows(&mut *p), 8);
        p.release(product(
            Predicate::Record(HashMap::from([
                ("x".into(), prefix(0)),
                ("y".into(), Predicate::True),
            ])),
            Predicate::True,
        ));
        add(&a, &[2], prefix(2));
        assert_eq!(rows(&mut *p), 8);
        p.release(p.tiling().universal_guard());
        assert!(a.borrow().get_released_predicate().is_true());
    }

    #[test]
    fn a_key_delivered_before_its_decision_does_not_hide_later_progress() {
        let a = source("a");
        add(&a, &[0], Predicate::False);
        let mut p = head(Extent::DataSourceDomain(a.clone()), Extent::uint_range(2));
        assert_eq!(rows(&mut *p), 2);
        a.borrow_mut().set_yield_predicate(prefix(0));
        let tile = p.get(p.tiling().universal_guard());
        let Tile::DataFunction {
            domain_predicate,
            domain,
            ..
        } = tile
        else {
            panic!("a product is a collection")
        };
        assert_eq!(domain.len(), 2);
        assert!(domain_predicate.contains(&Value::Record(HashMap::from([
            ("a".into(), Value::UInt(0)),
            ("b".into(), Value::UInt(0)),
        ]))));
    }

    #[test]
    fn a_cartesian_iterator_is_a_leaf_and_reads_arrivals_on_get() {
        let (a, b) = (source("a"), source("b"));
        add(&a, &[0], prefix(0));
        add(&b, &[0], prefix(0));
        let mut p = head(
            Extent::DataSourceDomain(a.clone()),
            Extent::DataSourceDomain(b),
        );
        p.visit_input_producers(&mut |_, _| panic!("an extent iterator is a leaf"));
        assert_eq!(rows(&mut *p), 1);
        add(&a, &[1], prefix(1));
        assert_eq!(rows(&mut *p), 2);
        assert_eq!(rows(&mut *p), 2);
    }
}
