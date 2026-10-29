use super::*;
use crate::interpreter::operator_graph::value;
use crate::{
    interpreter::{ColumnValue, Consumer, Projection, Scheduler, Value},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

// ---------------------------------------------------------------------------
// ExtractFinal / ExtractFinalProducer
// ---------------------------------------------------------------------------

/// Extracts the final value of a `DataFunction` stream, the codomain at its highest
/// position once the stream is terminal, as a `Scalar`: `final_or_default(stream, default)`
/// over any stream but an induction accumulator's own history, whose final the store holds
/// ([`StoreFinalRead`](crate::interpreter::commit_operator::StoreFinalRead)).
///
/// When the source becomes terminal but emits no values, the `default` operator's scalar
/// value is emitted instead, so the read is total.
pub struct ExtractFinal {
    /// Operator producing the `DataFunction` tiling to extract from.
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
    /// Output tiling — what one position of the source holds.
    base: OperatorBase,
}

impl ExtractFinal {
    /// Construct a new `ExtractFinal` wrapping `source`, with `default`
    /// as the fallback for the empty-source case.
    ///
    /// `source` must have a `DataFunction` tiling and `default` a `Scalar`
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
            base: OperatorBase::new(tiling),
            source,
            default: Some(default),
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
            base: OperatorBase::new(tiling),
            source,
            default: None,
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
        // Both branches need their own notification path: any progress on
        // either side may unblock the consumer (source becoming terminal,
        // default resolving its scalar value).  We give source the shared
        // consumer handle since it's the primary trigger; default uses a
        // no-op notifier because its readiness only matters at the moment
        // we discover an empty source — by then we're already in `get_impl`
        // and will pull it directly.
        let source_producer = self.source.subscribe(
            self.source.tiling().universal_guard(),
            widening(consumer),
            scheduler,
        );
        let default_producer = self
            .default
            .as_mut()
            .map(|d| d.subscribe(d.tiling().universal_guard(), Box::new(|| {}), scheduler));
        Box::new(ExtractFinalProducer::new(
            ProducerBase::new(
                ExtractFinalProducer::alloc_id(),
                self.tiling(),
                &self.base,
                scheduler,
            ),
            source_producer,
            default_producer,
        ))
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
    /// The extracted result, re-emitted until released. A tile rather than a value: a
    /// collection-valued position holds a whole sub-tile.
    final_tile: Option<Tile>,
    /// Set to `true` by [`Self::release_impl`] on a universal release.
    /// Returns an empty scalar from every subsequent `get`.  The
    /// surrounding `Memo` normally issues this universal release as
    /// soon as it has merged the value into its own cache, so
    /// post-release emissions are rare in normal data flow.
    released: bool,
    /// The source rows [`BreakingProducer::consume_impl`] merged, kept to the row at the
    /// greatest key where the values are a column, and empty before the first consume.
    merged: Tile,
    /// Whether `consume_impl` has run: a consuming extraction answers from `final_tile`, and only
    /// `consume_impl` pulls its source and its default.
    consuming: bool,
}

/// The final value of `source`, falling back to `default`, that nothing subscribed, answering at
/// `tiling`, for a test that builds a chain of pipelines by hand.
#[cfg(test)]
pub(crate) fn extract_final_of(
    source: Box<dyn TileProducer>,
    default: Option<Box<dyn TileProducer>>,
    tiling: &Tiling,
) -> crate::interpreter::dispatcher::BreakerHandle {
    Rc::new(RefCell::new(ExtractFinalProducer::new(
        ProducerBase::unowned(ExtractFinalProducer::alloc_id(), tiling),
        source,
        default,
    )))
}

impl ExtractFinalProducer {
    fn new(
        base: ProducerBase,
        source: Box<dyn TileProducer>,
        default: Option<Box<dyn TileProducer>>,
    ) -> Self {
        let merged = source.tiling().empty_tile();
        Self {
            base,
            source,
            default,
            final_tile: None,
            released: false,
            merged,
            consuming: false,
        }
    }

    /// The value at row `final_idx` of a source whose keys are `domain`: the position being
    /// indexed is this collection's key, and what it holds is everything below it, a value where
    /// the values are a column and a whole collection where they are one.
    fn value_at(&self, domain: &ColumnValue, codomain: Tile, final_idx: usize) -> Tile {
        let extent = self.tiling().extent();
        if codomain.is_data_function() {
            // Keeping one row leaves that key's group standing alone, which is the
            // value at this position. The source is terminal and this is its last
            // position, so what it holds is the whole collection.
            let mut sub = codomain;
            sub.retain_rows(
                &(0..domain.len())
                    .map(|i| i == final_idx)
                    .collect::<Vec<bool>>(),
            );
            let Tile::DataFunction {
                domain_predicate, ..
            } = &mut sub
            else {
                unreachable!("retain keeps a collection a collection")
            };
            *domain_predicate = Predicate::True;
            sub
        } else {
            // Built at the *declared* extent: a tag `match` collapses its arms to their
            // join, and the arm that answers carries only its own tag. Laid out as this
            // operator's tiling, which keeps a product a record of columns.
            let cv = scalar_tile_to_column_value(codomain);
            column_value_to_tile(
                ColumnValue::from_values(vec![cv.index_at(final_idx)], &extent),
                self.tiling(),
            )
        }
    }

    /// The default's value once it has converged, which is when it is terminal, and `None`
    /// before. The default is released once it has been read.
    ///
    /// # Panics
    ///
    /// For a source declared total that emitted no value.
    fn pull_default(&mut self) -> Option<Tile> {
        let extent = self.tiling().extent();
        let yields_a_level = self.tiling().is_data_function();
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
        // A collection-valued position falls back to the whole collection, so the default
        // is the tile it is rather than a value to rebuild a column from. It has converged
        // once it is terminal, which is what `as_single` says for the scalar case.
        if yields_a_level {
            if !default_tile.is_terminal() {
                return None;
            }
            default.release(default_tiling.universal_guard());
            return Some(default_tile);
        }
        // Default hasn't converged yet when there is no single value: the outer pull loop
        // retries, and once the default resolves it is cached.
        let value = scalar_tile_to_column_value(default_tile).as_single()?;
        default.release(default_tiling.universal_guard());
        Some(Tile::Scalar(ColumnValue::from_values(vec![value], &extent)))
    }
}

impl TileProducer for ExtractFinalProducer {
    fn state_info(&self) -> ProducerStateInfo {
        ProducerStateInfo::holding(self.final_tile.as_ref().map_or(0, Tile::cell_count))
    }

    impl_producer_base!();

    fn visit_input_producers(&self, visit: &mut dyn FnMut(&str, &dyn TileProducer)) {
        visit("source", &*self.source);
        if let Some(default) = &self.default {
            visit("default", &**default);
        }
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        let node = node.child("source", self.source.inspect(opts));
        match &self.default {
            Some(d) => node.child("default", d.inspect(opts)),
            None => node.annotate("total (no default)".to_string()),
        }
    }

    /// The final position of a stream is one value, or one collection that a release takes
    /// whole, so the projection is all of it or none: the source is read whole whatever the
    /// consumer asks, because the last position is not known before the stream ends.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        if projection_of_one_value(&self.name(), "extracts one final value", &projection_guard)
            == Projection::Nothing
        {
            return self.tiling().empty_tile();
        }
        // Every emission below is built at the **declared** extent rather than
        // from the value alone. A variant value carries only the tag it holds, so
        // a column built from it would have just that one arm — narrower than this
        // operator's tiling whenever the alternatives it collapses carry more tags
        // between them. Building at the declared extent keeps every arm present,
        // with the ones that did not occur empty, which is the shape downstream
        // merges and appends require.
        let empty = self.tiling().empty_tile();
        if self.released {
            return empty;
        }
        if self.consuming {
            return self.offer_impl(projection_guard);
        }
        // Already extracted: keep re-emitting the same scalar until we
        // are released.  Downstream `Memo` typically releases on first
        // sight of a non-empty tile, so this branch only stays active
        // across pulls when the consumer doesn't release immediately
        // (e.g. while a sibling pipeline is still converging).
        if let Some(tile) = &self.final_tile {
            return tile.clone();
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
            if let Some(keys) = source_tile.live_keys() {
                let max_pos = keys
                    .filter_map(|(_, key)| match key {
                        Value::UInt(p) => Some(p),
                        _ => None,
                    })
                    .max();
                if let Some(max_pos) = max_pos
                    && max_pos >= 1
                {
                    self.source
                        .release(TileGuard::Function(FunctionGuard::Domain(
                            Predicate::at_or_below(Value::UInt(max_pos - 1)),
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
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = source_tile
        else {
            panic!("ExtractFinal source must be a collection tile");
        };
        // The position being indexed is this collection's key, and what it holds is
        // everything below it: a value where the values are a column, a whole collection
        // where they are one.
        // TODO don't assume sorting; we need to sort by the key value instead.
        let live_outer = (0..domain.len()).rev().find(|i| !deleted.contains(*i));
        if let Some(final_idx) = live_outer {
            let tile = self.value_at(&domain, *codomain, final_idx);
            self.final_tile = Some(tile.clone());
            return tile;
        }
        // Source is terminal *and* empty (the loop body ran zero times).  Pull the
        // default scalar and emit that instead, then release the default so its
        // upstream chain can release too.
        match self.pull_default() {
            Some(tile) => {
                self.final_tile = Some(tile.clone());
                tile
            }
            None => empty,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.released = true;
            self.final_tile = None;
            self.merged = self.source.tiling().empty_tile();
            self.source.release(self.source.tiling().universal_guard());
            if let Some(d) = self.default.as_mut() {
                d.release(d.tiling().universal_guard());
            }
        }
    }
}

impl BreakingProducer for ExtractFinalProducer {
    /// Merges the source rows it answers at `guard`, a guard of the source's tiling, keeps the
    /// row at the greatest key, and releases the source at what the answer stated. Rows merge in
    /// the order they arrive, so the last row is not the final one: the key says which is. Once
    /// the source has been released whole the value is extracted, or the default read when the
    /// source held nothing.
    fn consume_impl(&mut self, guard: TileGuard) {
        debug_assert!(
            guard.check_from(self.source.tiling()),
            "{} consumes a guard of its source's tiling: {guard:?}",
            self.name()
        );
        self.consuming = true;
        if self.released || self.final_tile.is_some() || guard.is_empty() {
            return;
        }
        let mut answered = self.source.get(guard);
        let upstream_guard = answered.to_guard();
        answered.compact();
        self.merged.merge(answered);
        self.keep_greatest_key();
        self.source.release(upstream_guard);
        if !self.source.obsolete_guard().is_universal() {
            return;
        }
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = &self.merged
        else {
            panic!("ExtractFinal source must be a collection tile");
        };
        self.final_tile = match greatest_live_key(domain, deleted) {
            Some(final_idx) => Some(self.value_at(domain, (**codomain).clone(), final_idx)),
            None => self.pull_default(),
        };
    }

    fn input_tiling(&self) -> Tiling {
        self.source.tiling().clone()
    }

    fn input_released(&self) -> TileGuard {
        self.source.obsolete_guard().clone()
    }

    /// The extracted value, once there is one: none while the source has not drained, or while a
    /// default it fell back to has not converged. The next `consume_impl` reads the default again.
    fn held(&self) -> TileGuard {
        match self.final_tile {
            Some(_) => self.tiling().universal_guard(),
            None => self.tiling().empty_guard(),
        }
    }

    /// Pushes the extracted value, as every breaker pushes its final guard.
    ///
    /// # Panics
    ///
    /// When the output is unreleased and no value has been extracted: the source has not been
    /// released whole, or the default it fell back to has not converged. A dispatcher finalizes
    /// a pipeline once and issues no `consume_impl` after it, so nothing would read that default
    /// again, and pushing nothing would leave the reader with no value.
    fn finalize(&mut self, pushes: &mut Pushes<'_>) {
        assert!(
            self.released || self.final_tile.is_some(),
            "{} finalizes after it extracted its value: the source released whole and any \
             default it fell back to converged",
            self.name()
        );
        pushes.push_final(self);
    }

    fn offer_impl(&mut self, guard: TileGuard) -> Tile {
        match guard.projection(&self.name()) {
            Projection::Nothing => self.tiling().empty_tile(),
            _ => self
                .final_tile
                .clone()
                .unwrap_or_else(|| self.tiling().empty_tile()),
        }
    }
}

impl ExtractFinalProducer {
    /// Drop every merged row but the one at the greatest key, which is the only one an
    /// extraction can still need, where the values are a column of scalars. Any other shape of
    /// value keeps every merged row.
    fn keep_greatest_key(&mut self) {
        let Tile::DataFunction {
            domain,
            codomain,
            deleted,
            ..
        } = &self.merged
        else {
            return;
        };
        let Tile::Scalar(values) = &**codomain else {
            return;
        };
        let Some(idx) = greatest_live_key(domain, deleted) else {
            return;
        };
        let Tile::DataFunction {
            domain_predicate, ..
        } = &self.merged
        else {
            return;
        };
        self.merged = Tile::data_function(
            domain.select_indices(std::iter::once(idx), 1),
            Box::new(Tile::Scalar(values.select_indices(std::iter::once(idx), 1))),
            domain_predicate.clone(),
            bit_set::BitSet::new(),
        );
    }
}

/// The row at the greatest key among the rows `deleted` does not name. Merged rows are in the
/// order they arrived, which is not the order of their keys.
fn greatest_live_key(domain: &ColumnValue, deleted: &bit_set::BitSet) -> Option<usize> {
    (0..domain.len())
        .filter(|row| !deleted.contains(*row))
        .max_by(|a, b| {
            domain
                .index_at(*a)
                .partial_cmp(&domain.index_at(*b))
                .expect("the keys of one collection compare")
        })
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
        releases: Rc<RefCell<Vec<u64>>>,
    }

    struct PartialSourceProducer {
        base: ProducerBase,
        releases: Rc<RefCell<Vec<u64>>>,
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
                base: ProducerBase::unowned(PartialSourceProducer::alloc_id(), &self.tiling),
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
                base: ProducerBase::unowned(TerminalSourceProducer::alloc_id(), &self.tiling),
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

    /// On a non-terminal pull, `ExtractFinal` needs only the highest-domain value,
    /// so it releases everything below it — `[0, max)`. Over a source with domain
    /// `[0, 1, 2]`, it forwards a release `≤ 1`, freeing the prefix that a
    /// never-terminating scalar-final loop would otherwise pin.
    #[test]
    fn extract_final_releases_below_the_running_max() {
        let value_tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let releases = Rc::new(RefCell::new(Vec::<u64>::new()));
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
}

#[cfg(test)]
mod projection_tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{
        GuardLog, ProjectionSpyOp, keys_between,
    };
    use crate::interpreter::{BaseType, Extent};

    /// `final_or_default(xs, 0)` over a finished stream `[10, 20, 30]`, with the pulls of the
    /// stream logged.
    fn final_of_finished_stream() -> (Box<dyn TileProducer>, GuardLog) {
        let int = || Extent::Base(BaseType::Int);
        let tiling = Tiling::data_function(Extent::uint_range(3), Tiling::Scalar(int()));
        let finished = Tile::data_function(
            ColumnValue::from_uints(vec![0, 1, 2]),
            Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30]))),
            Predicate::True,
            bit_set::BitSet::new(),
        );
        let (stream, pulled, _) = ProjectionSpyOp::new(finished, tiling);
        let mut op = ExtractFinal::new(
            Box::new(stream),
            Box::new(Constant::new(Value::Int(0), int())),
        );
        let guard = op.tiling().universal_guard();
        let producer = op.subscribe(guard, Box::new(|| {}), &mut Scheduler::new());
        (producer, pulled)
    }

    /// The last position is not known before the stream ends, so the source is read whole.
    #[test]
    fn the_stream_is_read_whole_to_find_its_last_position() {
        let (mut last, pulled) = final_of_finished_stream();
        let tile = last.get(last.tiling().universal_guard());
        assert_eq!(tile, Tile::Scalar(ColumnValue::Ints(vec![30])));
        assert_eq!(pulled.borrow().len(), 1);
        assert!(pulled.borrow()[0].is_universal());
    }

    #[test]
    fn asking_for_nothing_reads_nothing() {
        let (mut last, pulled) = final_of_finished_stream();
        let tile = last.get(last.tiling().empty_guard());
        assert_eq!(tile, last.tiling().empty_tile());
        assert!(pulled.borrow().is_empty());
    }

    #[test]
    #[should_panic(expected = "extracts one final value")]
    fn a_key_projection_is_rejected() {
        let (mut last, _) = final_of_finished_stream();
        last.get(keys_between(0, 1));
    }
}

/// A consuming `ExtractFinal` over an input that grows and is released: the value it extracts, what
/// it finalizes and what reaches the source, against a model of the keys consumed.
#[cfg(test)]
mod consuming_tests {
    use super::*;
    use std::collections::BTreeSet;

    use crate::interpreter::dispatcher::{Dispatcher, PipelineId};
    use crate::interpreter::tile_operators::growing::{
        Input, InputModel, KEYS, Region, Rng, Shared, Step, growing_source, ints, predicate,
        source, value,
    };
    use crate::interpreter::tile_operators::test_helpers::{
        ScriptedProducer, TestTileProducer, keys_between,
    };
    use crate::interpreter::{BaseType, Extent};
    use Region::{All, Keys};
    use Step::{Add, Close, Consume, Notify, Release};

    fn int() -> Tiling {
        Tiling::Scalar(Extent::Base(BaseType::Int))
    }

    fn default_of(value: i64) -> Option<Box<dyn TileProducer>> {
        Some(Box::new(TestTileProducer::new(
            Tile::Scalar(ColumnValue::Ints(vec![value])),
            int(),
        )))
    }

    fn final_over(source: &Shared, default: Option<Box<dyn TileProducer>>) -> ExtractFinalProducer {
        ExtractFinalProducer::new(
            ProducerBase::unowned(ExtractFinalProducer::alloc_id(), &int()),
            Box::new(Input::over(source)),
            default,
        )
    }

    fn scalar_of(tile: &Tile) -> Option<i64> {
        match tile {
            Tile::Scalar(ColumnValue::Ints(values)) => values.first().copied(),
            other if other.is_empty() => None,
            other => panic!("an integer, got {other:?}"),
        }
    }

    fn offer(extract: &mut ExtractFinalProducer) -> Option<i64> {
        scalar_of(&extract.get(int().universal_guard()))
    }

    /// Rows arrive in the order they are consumed, so the final value is the one at the greatest
    /// key, not the last to arrive.
    #[test]
    fn the_greatest_key_is_final_whatever_arrived_last() {
        let source = source(0..12);
        let mut extract = final_over(&source, None);
        extract.consume_impl(keys_between(8, 11));
        assert_eq!(
            offer(&mut extract),
            None,
            "the source has not stated everything complete"
        );
        // The rows below arrive after the row at key 11, which stays final.
        extract.consume_impl(ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(value(11)));
        assert_eq!(source.borrow().pulled.len(), 2);
    }

    /// Out-of-order morsels that end below the key a first morsel held leave that key final.
    #[test]
    fn a_later_morsel_with_smaller_keys_does_not_replace_the_final_row() {
        let source = source([1, 2, 9, 10]);
        let mut extract = final_over(&source, None);
        extract.consume_impl(keys_between(9, 11));
        extract.consume_impl(keys_between(0, 3));
        extract.consume_impl(ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(value(10)));
    }

    /// A region is pulled and released once, and a partial source yields no value.
    #[test]
    fn a_region_is_pulled_and_released_and_yields_no_value_yet() {
        let source = source(0..10);
        let mut extract = final_over(&source, None);
        extract.consume_impl(keys_between(2, 5));
        assert_eq!(source.borrow().pulled, vec![keys_between(2, 5)]);
        assert_eq!(source.borrow().released, vec![keys_between(2, 5)]);
        assert_eq!(offer(&mut extract), None);
        extract.consume_impl(keys_between(7, 9));
        extract.consume_impl(keys_between(4, 8));
        assert_eq!(
            source.borrow().released,
            vec![keys_between(2, 5), keys_between(7, 9), keys_between(4, 8)]
        );
    }

    #[test]
    fn nothing_consumed_pulls_nothing() {
        let source = source(0..10);
        let mut extract = final_over(&source, None);
        extract.consume_impl(ints().empty_guard());
        assert!(source.borrow().pulled.is_empty());
    }

    /// An empty source that has drained falls back to the default, read once.
    #[test]
    fn an_empty_drained_source_yields_the_default() {
        let source = source([]);
        let mut extract = final_over(&source, default_of(7));
        extract.consume_impl(ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(7));
        assert_eq!(extract.final_guard(), int().universal_guard());
    }

    /// A default that has not converged when the source drains leaves nothing held; the next
    /// consume reads it again, as every pull does in pull mode.
    #[test]
    fn an_unconverged_default_is_read_again_by_the_next_consume() {
        let source = source([]);
        let (default, cell) = ScriptedProducer::new(Tile::Scalar(ColumnValue::Ints(vec![])), int());
        let mut extract = final_over(&source, Some(Box::new(default)));
        extract.consume_impl(ints().universal_guard());
        assert_eq!(offer(&mut extract), None, "the default has not converged");
        assert_eq!(
            extract.final_guard(),
            int().empty_guard(),
            "nothing is held yet"
        );

        *cell.borrow_mut() = Tile::Scalar(ColumnValue::Ints(vec![7]));
        extract.consume_impl(ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(7));
        assert_eq!(extract.final_guard(), int().universal_guard());
    }

    /// A default that has not converged by `finalize` is never read again: the dispatcher issues
    /// no later `consume_impl`.
    #[test]
    #[should_panic(expected = "finalizes after it extracted its value")]
    fn finalize_with_an_unconverged_default_panics() {
        let source = source([]);
        let (default, _) = ScriptedProducer::new(Tile::Scalar(ColumnValue::Ints(vec![])), int());
        let mut extract = final_over(&source, Some(Box::new(default)));
        extract.consume_impl(ints().universal_guard());
        extract.finalize(&mut Dispatcher::new(vec![vec![]], usize::MAX).pushes(PipelineId(0)));
    }

    /// An output released before the value was extracted pushes nothing, and that is no error.
    #[test]
    fn finalize_after_the_output_was_released_pushes_nothing() {
        let source = growing_source(0..4);
        let mut extract = final_over(&source, None);
        extract.consume_impl(keys_between(0, 1));
        extract.release(int().universal_guard());
        let dispatcher = Dispatcher::new(vec![vec![], vec![0]], usize::MAX);
        dispatcher.finalize_by_hand(PipelineId(0), |pushes| extract.finalize(pushes));
        assert!(dispatcher.pop().is_none());
    }

    /// A total source that is empty is an invariant violation, as in pull mode.
    #[test]
    #[should_panic(expected = "declared total emitted no value")]
    fn an_empty_total_source_fails_loudly() {
        let source = source([]);
        let mut extract = final_over(&source, None);
        extract.consume_impl(ints().universal_guard());
    }

    #[test]
    fn finalize_holds_the_value_until_it_is_released() {
        let source = source(0..4);
        let mut extract = final_over(&source, None);
        extract.consume_impl(ints().universal_guard());
        assert_eq!(extract.final_guard(), int().universal_guard());
        extract.release(int().universal_guard());
        assert_eq!(extract.final_guard(), int().empty_guard());
        assert_eq!(offer(&mut extract), None);
    }

    #[test]
    fn a_consuming_extraction_offers_without_pulling() {
        let source = source(0..10);
        let mut extract = final_over(&source, None);
        extract.consume_impl(ints().universal_guard());
        let pulls = source.borrow().pulled.len();
        for _ in 0..3 {
            offer(&mut extract);
        }
        assert_eq!(source.borrow().pulled.len(), pulls);
    }

    /// A growing source withholds a key it does not hold yet: the release leaves it, and a row
    /// that arrives there later is the final one once the source closes.
    #[test]
    fn a_key_the_source_withheld_is_merged_by_a_later_consume() {
        let source = growing_source([0, 1, 2]);
        let mut extract = final_over(&source, None);
        extract.consume_impl(keys_between(0, 5));
        assert!(!predicate(&source.borrow().released[0]).contains(&Value::UInt(3)));
        source.borrow_mut().rows.insert(3, value(3));
        source.borrow_mut().closed = true;
        extract.consume_impl(ints().universal_guard());
        assert_eq!(offer(&mut extract), Some(value(3)));
    }

    /// A consume after the output was released pulls nothing: the source was released whole.
    #[test]
    fn a_consume_after_a_release_pulls_nothing() {
        let source = growing_source(0..4);
        let mut extract = final_over(&source, None);
        extract.consume_impl(keys_between(0, 1));
        extract.release(int().universal_guard());
        let pulls = source.borrow().pulled.len();
        extract.consume_impl(ints().universal_guard());
        assert_eq!(source.borrow().pulled.len(), pulls);
        assert_eq!(source.borrow().wasted, 0);
    }

    /// The model of a run over a growing source: the keys answered, whether the output was
    /// released, and the source.
    struct Run {
        sut: ExtractFinalProducer,
        sut_source: Shared,
        input: InputModel,
        answered: BTreeSet<u64>,
        /// Whether the value is extracted: the source drained by a consume, after which the
        /// extraction reads no more.
        extracted: bool,
        released: bool,
        trace: String,
    }

    impl Run {
        fn new(initial: &[u64], trace: String) -> Self {
            let sut_source = growing_source(initial.iter().copied());
            Self {
                sut: final_over(&sut_source, default_of(-1)),
                sut_source,
                input: InputModel::new(initial),
                answered: BTreeSet::new(),
                extracted: false,
                released: false,
                trace,
            }
        }

        fn apply(&mut self, step: Step) {
            self.trace.push_str(&format!(" {step:?}"));
            match step {
                Add(key) => {
                    if self.input.add(key) {
                        self.sut_source.borrow_mut().rows.insert(key, value(key));
                    }
                }
                Close => {
                    self.input.closed = true;
                    self.sut_source.borrow_mut().closed = true;
                }
                Notify(_) => unreachable!("an extraction listens to no region"),
                Consume(region) => {
                    self.sut.consume_impl(region.guard());
                    if self.released || self.extracted {
                        return;
                    }
                    self.answered.extend(self.input.pull(region).0);
                    self.extracted = self.input.drained();
                }
                Release(_) => {
                    self.sut.release(int().universal_guard());
                    if !self.released {
                        self.released = true;
                        self.input.release(All);
                    }
                }
            }
        }

        /// The value a drained source leaves: the greatest key answered, or the default.
        fn expected(&self) -> Option<i64> {
            match (self.released, self.extracted) {
                (true, _) | (_, false) => None,
                (false, true) => Some(self.answered.iter().max().map_or(-1, |key| value(*key))),
            }
        }

        fn check(&mut self) {
            let trace = self.trace.clone();
            self.input.check(&self.sut_source, &trace);
            if self.sut.consuming {
                assert_eq!(offer(&mut self.sut), self.expected(), "{trace}: the value");
            }
            if self.input.drained() {
                let expected = match self.extracted && !self.released {
                    true => int().universal_guard(),
                    false => int().empty_guard(),
                };
                assert_eq!(self.sut.final_guard(), expected, "{trace}: finalize");
            }
        }

        fn run(steps: &[Step], initial: &[u64]) {
            let mut run = Run::new(initial, format!("initial {initial:?} steps"));
            for step in steps {
                run.apply(*step);
                run.check();
            }
            run.finish();
        }

        fn finish(&mut self) {
            if !self.input.closed {
                self.apply(Close);
            }
            self.apply(Consume(All));
            self.check();
            if self.released {
                return;
            }
            // An extraction in pull mode over the keys that were answered yields the same value.
            let twin_source = source(self.answered.iter().copied());
            let mut twin = final_over(&twin_source, default_of(-1));
            assert_eq!(
                scalar_of(&twin.get(int().universal_guard())),
                offer(&mut self.sut),
                "{}: the answer in pull mode",
                self.trace
            );
        }
    }

    #[test]
    fn enumerated_interleavings_keep_the_model() {
        let sequences: &[&[Step]] = &[
            &[
                Consume(Keys(6, 9)),
                Consume(Keys(0, 3)),
                Add(10),
                Consume(Keys(4, 11)),
            ],
            &[Consume(Keys(0, 3)), Add(3), Add(9), Close, Consume(All)],
            &[Add(11), Consume(Keys(0, 5)), Release(All), Consume(All)],
            &[
                Consume(Keys(8, 11)),
                Add(9),
                Consume(Keys(8, 11)),
                Consume(Keys(0, 7)),
            ],
            &[Close, Consume(All), Add(11), Consume(All)],
        ];
        for steps in sequences {
            Run::run(steps, &[0, 1, 2, 4, 5, 6]);
        }
    }

    #[test]
    fn random_interleavings_keep_the_model() {
        const SEED: u64 = 0xd1b5_4a32_d192_ed03;
        let mut rng = Rng(SEED);
        for iteration in 0..300 {
            let initial: Vec<u64> = (0..KEYS).filter(|_| rng.below(2) == 0).collect();
            let trace = format!("seed {SEED:#x} iteration {iteration} initial {initial:?} steps");
            let mut run = Run::new(&initial, trace);
            for _ in 0..12 {
                let step = rng.step_among(&run.answered, false);
                run.apply(step);
                run.check();
            }
            run.finish();
        }
    }
}
