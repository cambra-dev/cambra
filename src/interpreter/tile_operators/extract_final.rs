use super::*;
use crate::{
    interpreter::{ColumnValue, Consumer, Scheduler, Value},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

// ---------------------------------------------------------------------------
// ExtractFinal / ExtractFinalProducer
// ---------------------------------------------------------------------------

/// Extracts the final value from a changelog store's dense read (or any
/// `SealedFunction`) output, converting the accumulated `SealedFunction` tiling
/// back to a `Scalar` — the scalar-final read of a mutation loop's accumulator.
///
/// When the source becomes terminal but emits no values (the empty-source
/// case, e.g. `for i in []: x += 1`), the `default` operator's scalar value
/// is emitted instead.  This keeps mutation loops total: the post-loop
/// accumulator always has a defined value, equal to the loop's initial
/// value when the body never ran.
///
/// Used as the terminal stage of a loop: `ExtractFinal(body.step, init)`.
pub struct ExtractFinal {
    /// Operator producing the `SealedFunction` tiling to extract from.
    source: Box<dyn TileOperator>,
    /// Fallback scalar operator, pulled when `source` is terminal and emits zero
    /// values.  Must have a `Scalar` tiling whose extent the output extent
    /// *includes* — a width-narrower variant is admitted and widened on emission.
    ///
    /// `None` when the source is known to be **total** — a tag partition over an
    /// exhaustive `match` always yields exactly one value, so there is no empty
    /// case to fall back from and no default value has to be invented. An empty
    /// source with no default is an invariant violation, not a fallback.
    default: Option<Box<dyn TileOperator>>,
    /// Output tiling — the codomain of the source SealedFunction (always `Scalar`).
    tiling: Tiling,
}

impl ExtractFinal {
    /// Construct a new `ExtractFinal` wrapping `source`, with `default`
    /// as the fallback for the empty-source case.
    ///
    /// `source` must have a `SealedFunction` tiling and `default` a `Scalar`
    /// tiling whose extent that codomain includes. The output tiling becomes
    /// the scalar codomain.
    pub fn new(source: Box<dyn TileOperator>, default: Box<dyn TileOperator>) -> Self {
        let tiling = Self::source_codomain_tiling(source.as_ref());
        // The default has to be *representable* in the output value space — neither
        // identically tiled nor even the same extent. Two independent reasons, both
        // live:
        //
        // - **Tiling shape.** A record/tuple value is `Scalar(Record)` coming from a
        //   mutable variable history but `Record({_0: Scalar, …})` (struct-of-arrays) from a
        //   literal. `get_impl` normalizes both through `scalar_tile_to_column_value`,
        //   so the structural tilings need not agree — only the value-spaces.
        // - **Width.** A tag `match`/conditional whose arms carry different tags
        //   collapses to the arms' join, and the trailing arm supplying the default is
        //   one of those arms, so its extent carries its own tag and not its siblings'.
        //   Emission builds the column at the declared extent, which is what makes the
        //   narrower value fit.
        debug_assert!(
            tiling.extent().includes(&default.tiling().extent()),
            "ExtractFinal default must be representable in the source codomain: \
             default {} is not included in {tiling}",
            default.tiling(),
        );
        Self {
            source,
            default: Some(default),
            tiling,
        }
    }

    /// Construct an `ExtractFinal` over a source known to be **total**.
    ///
    /// Used where the stream is a partition that always covers exactly one
    /// position — an exhaustive tag `match` — so the empty case cannot arise and
    /// no default value has to be fabricated. If the source does turn out empty,
    /// [`ExtractFinalProducer`] fails loudly rather than inventing a value.
    pub fn without_default(source: Box<dyn TileOperator>) -> Self {
        let tiling = Self::source_codomain_tiling(source.as_ref());
        Self {
            source,
            default: None,
            tiling,
        }
    }

    fn source_codomain_tiling(source: &dyn TileOperator) -> Tiling {
        match source.tiling() {
            Tiling::SealedFunction { codomain, .. } => *codomain.clone(),
            other => panic!("ExtractFinal source must have SealedFunction tiling, got {other}"),
        }
    }
}

impl TileOperator for ExtractFinal {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        let node = node.child("source", self.source.inspect(opts));
        match &self.default {
            Some(d) => node.child("default", d.inspect(opts)),
            None => node.annotate("total (no default)".to_string()),
        }
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Both branches need their own notification path: any progress on
        // either side may unblock the consumer (source becoming terminal,
        // default resolving its scalar value).  We give source the shared
        // consumer handle since it's the primary trigger; default uses a
        // no-op notifier because its readiness only matters at the moment
        // we discover an empty source — by then we're already in `get_impl`
        // and will pull it directly.
        let source_producer =
            self.source
                .subscribe(self.source.tiling().universal_guard(), consumer, scheduler);
        let default_producer = self
            .default
            .as_mut()
            .map(|d| d.subscribe(d.tiling().universal_guard(), Box::new(|| {}), scheduler));
        Box::new(ExtractFinalProducer {
            base: ProducerBase::new(ExtractFinalProducer::alloc_id(), &self.tiling),
            source: source_producer,
            default: default_producer,
            final_value: None,
            released: false,
        })
    }
}

struct ExtractFinalProducer {
    base: ProducerBase,
    source: Box<dyn TileProducer>,
    /// Default-value producer, pulled when `source` becomes terminal
    /// and emits zero values.  Subscribed eagerly alongside `source`;
    /// `get` is deferred until we know we need it.
    default: Option<Box<dyn TileProducer>>,
    /// Cached final scalar value.  `None` until the source becomes
    /// terminal; `Some(_)` thereafter.  Every subsequent `get` returns
    /// this same value until the consumer releases us with a universal
    /// guard — which then sets [`Self::released`] and we go quiet.
    /// Same emit-until-released protocol as [`Constant`], so consumers
    /// that pull repeatedly (e.g. sibling `Final` projections off a
    /// shared multi-accumulator mutation-loop) see a stable value
    /// instead of an empty source after the first terminal pull.
    final_value: Option<Value>,
    /// Set to `true` by [`Self::release_impl`] on a universal release.
    /// Returns an empty scalar from every subsequent `get`.  The
    /// surrounding `Memo` normally issues this universal release as
    /// soon as it has merged the value into its own cache, so
    /// post-release emissions are rare in normal data flow.
    released: bool,
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
        // Every emission below is built at the **declared** extent rather than
        // from the value alone. A variant value carries only the tag it holds, so
        // a column built from it would have just that one arm — narrower than this
        // operator's tiling whenever the alternatives it collapses carry more tags
        // between them. Building at the declared extent keeps every arm present,
        // with the ones that did not occur empty, which is the shape downstream
        // merges and appends require.
        let extent = self.tiling().extent();
        let empty = Tile::Scalar(ColumnValue::from_values(vec![], &extent));
        if self.released {
            return empty;
        }
        // Already extracted: keep re-emitting the same scalar until we
        // are released.  Downstream `Memo` typically releases on first
        // sight of a non-empty tile, so this branch only stays active
        // across pulls when the consumer doesn't release immediately
        // (e.g. while a sibling pipeline is still converging).
        if let Some(v) = &self.final_value {
            return Tile::Scalar(ColumnValue::from_values(vec![v.clone()], &extent));
        }
        let source_tiling = self.source.tiling().clone();
        let source_tile = self.source.get(source_tiling.universal_guard());
        if !source_tile.is_terminal() {
            // Source hasn't converged yet — emit an empty scalar of the
            // correct extent.  Our own tiling *is* the source's codomain
            // (always `Scalar`), so its extent gives us the value-space
            // directly without going through `Tiling::codomain` (which
            // would return `None` for a `Scalar`).
            //
            // Incremental release: we only ever need the *final* (highest-domain)
            // value, so every position below the highest one seen so far is dead —
            // release it. This is a promise never to re-request those positions;
            // the source decides what upstream storage that frees (for a changelog
            // dense read, the store prefix below the tail's carry source). Without
            // it, a never-terminating loop would pin the whole changelog until a
            // terminal that never comes.
            if let Tile::SealedFunction {
                domain, deleted, ..
            } = &source_tile
            {
                let max_pos = (0..domain.len())
                    .filter(|i| !deleted.contains(*i))
                    .filter_map(|i| match domain.index_at(i) {
                        Value::UInt(p) => Some(p),
                        _ => None,
                    })
                    .max();
                if let Some(max_pos) = max_pos
                    && max_pos >= 1
                {
                    self.source
                        .release(TileGuard::Function(FunctionGuard::Domain(
                            Predicate::LessThanEq(Value::UInt(max_pos - 1)),
                        )));
                }
            }
            return empty;
        }
        // Source is terminal — we've seen the final tile, so we'll
        // never need more data from it.  Release universally so
        // upstream chains (`FanOut`, `Memo`, mutation-loop body
        // sub-graphs) can in turn release their inputs and ultimately
        // reach the underlying data source.  Release is idempotent, so
        // a repeated call from the consumer's outer pull loop is fine.
        self.source.release(source_tiling.universal_guard());
        let Tile::SealedFunction {
            codomain, deleted, ..
        } = source_tile
        else {
            panic!("ExtractFinal source must be a SealedFunction tile");
        };
        let cv = scalar_tile_to_column_value(*codomain);
        let n = cv.len();
        // Try to extract the final non-deleted value from the source.
        // TODO don't assume sorting; we need to sort by the domain value instead.
        if let Some(final_idx) = (0..n).rev().find(|&i| !deleted.contains(i)) {
            let value = cv.index_at(final_idx);
            self.final_value = Some(value.clone());
            return Tile::Scalar(ColumnValue::from_values(vec![value], &extent));
        }
        // Source is terminal *and* empty (the loop body ran zero times).  Pull the
        // default scalar and emit that instead, then release the default so its
        // upstream chain can release too.
        let Some(default) = self.default.as_mut() else {
            // No default means the source was declared total — an exhaustive tag
            // partition always covers exactly one position. An empty source here is
            // that invariant being wrong, so fail rather than invent a value.
            panic!(
                "ExtractFinal over a source declared total emitted no value; the \
                 partition feeding it was not exhaustive"
            );
        };
        let default_tiling = default.tiling().clone();
        let default_tile = default.get(default_tiling.universal_guard());
        match scalar_tile_to_column_value(default_tile).as_single() {
            Some(value) => {
                default.release(default_tiling.universal_guard());
                self.final_value = Some(value.clone());
                Tile::Scalar(ColumnValue::from_values(vec![value], &extent))
            }
            // Default hasn't converged yet — emit empty.  Outer pull
            // loop will retry; once default resolves, we'll cache it.
            None => empty,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.released = true;
            self.source.release(self.source.tiling().universal_guard());
            if let Some(d) = self.default.as_mut() {
                d.release(d.tiling().universal_guard());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use super::*;
    use crate::interpreter::tile_operators::{FunctionGuard, Predicate};
    use crate::interpreter::{BaseType, Extent};

    /// A non-terminal `SealedFunction` source with domain `[0, 1, 2]`, recording
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
            Tile::SealedFunction {
                domain: ColumnValue::from_uints(vec![0, 1, 2]),
                codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
                domain_predicate: Predicate::False, // never terminal
                deleted: bit_set::BitSet::new(),
            }
        }
        fn release_impl(&mut self, obsolete_guard: TileGuard) {
            if let TileGuard::Function(FunctionGuard::Domain(Predicate::LessThanEq(Value::UInt(
                w,
            )))) = &obsolete_guard
            {
                self.releases.borrow_mut().push(*w);
            }
        }
    }

    /// A **terminal** `SealedFunction` source carrying `codomain_tile` over
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
            Tile::SealedFunction {
                domain: self.domain.clone(),
                codomain: Box::new(Tile::Scalar(self.codomain_tile.clone())),
                domain_predicate: Predicate::True, // terminal
                deleted: bit_set::BitSet::new(),
            }
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
            tiling: Tiling::SealedFunction {
                domain: Extent::Base(BaseType::UInt),
                codomain: Box::new(Tiling::Scalar(merged.clone())),
            },
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
            tiling: Tiling::SealedFunction {
                domain: Extent::Base(BaseType::UInt),
                codomain: Box::new(Tiling::Scalar(merged.clone())),
            },
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

    /// On a non-terminal pull, `ExtractFinal` needs only the highest-domain value,
    /// so it releases everything below it — `[0, max)`. Over a source with domain
    /// `[0, 1, 2]`, it forwards a release `≤ 1`, freeing the prefix that a
    /// never-terminating scalar-final loop would otherwise pin.
    #[test]
    fn extract_final_releases_below_the_running_max() {
        let value_tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let releases = Rc::new(RefCell::new(Vec::<usize>::new()));
        let source = PartialSource {
            tiling: Tiling::SealedFunction {
                domain: Extent::Base(BaseType::UInt),
                codomain: Box::new(value_tiling.clone()),
            },
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
}
