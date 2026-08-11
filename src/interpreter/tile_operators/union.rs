use bit_set::BitSet;
use std::{cell::RefCell, rc::Rc};

use super::*;
use crate::{
    ccl::TagMap,
    interpreter::{ColumnValue, Consumer, Extent, Scheduler, UnionArm, Value},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

// ---------------------------------------------------------------------------
// UnionOperator / UnionProducer
// ---------------------------------------------------------------------------

/// Merges N `SealedFunction` operators into one by taking the discriminated
/// union of their domains and the **join** of their codomains.
///
/// The output tiling is `SealedFunction { domain: Union(d₀, …, dₙ₋₁), codomain }`.
/// The domain keeps every arm apart — which arm a row came from is what
/// `final_or_default` dispatches on. The codomain does the opposite: the arms are
/// alternative values at one row, so it is their [`Extent::join`], falling back to
/// an anonymous positional sum only for arms that have none.
pub struct UnionOperator {
    tiling: Tiling,
    /// Input operators; each must have a `SealedFunction` tiling.
    inputs: Vec<Box<dyn TileOperator>>,
    /// Flat-merge mode (see [`new_flat`](Self::new_flat)): arms share one domain
    /// extent with disjoint positions, merged into a single flat `SealedFunction`
    /// (sorted by domain key) rather than a tagged `ColumnValue::Union`.
    flat: bool,
}

impl UnionOperator {
    /// Create a new `UnionOperator` from the given input operators.
    ///
    /// All inputs must be `SealedFunction` tilings.  The output domain is
    /// `Extent::Union` of all input domains; the codomain is the arms' join (see
    /// the type-level note above).
    pub fn new(inputs: Vec<Box<dyn TileOperator>>) -> Self {
        assert!(
            !inputs.is_empty(),
            "UnionOperator requires at least one input"
        );
        let domains: Vec<Extent> = inputs
            .iter()
            .map(|op| match op.tiling() {
                Tiling::SealedFunction { domain, .. } => domain.clone(),
                other => panic!("UnionOperator: expected SealedFunction, got {other}"),
            })
            .collect();
        let codomains: Vec<&Tiling> = inputs
            .iter()
            .map(|op| match op.tiling() {
                Tiling::SealedFunction { codomain, .. } => codomain.as_ref(),
                _ => unreachable!(),
            })
            .collect();

        // The codomain is the arms' **join** where they have one, and an anonymous
        // positional sum only where they do not.
        //
        // Agreeing arms are the join's trivial case. The one that matters is arms
        // whose *variants* differ: `` `pos(n) `` and `` `neg(n) `` are alternative values
        // of one result, and the column this operator actually merges them into is
        // the tag-merged sum carrying both tags with the arm that did not occur
        // left empty. Declaring a positional sum instead describes a value shaped
        // like "arm 0's variant *or* arm 1's variant", which is not what any row
        // holds — and the tile then fails to conform to its own tiling.
        //
        // Where the arms genuinely have no join, the positional sum is right: for
        // a concatenation the arm a row came from is part of its identity.
        let codomain = if codomains.windows(2).all(|w| w[0] == w[1]) {
            codomains[0].clone()
        } else {
            // Differing arms are alternative values at one row, so merging them
            // yields one *column* — which is also the only codomain shape
            // `UnionProducer` can build (it concatenates like columns, or
            // materialises `Value` rows into a `Variants` column). So an arm's
            // tiling is admissible here exactly when its values fit in one column:
            // a `Scalar`, or a `Record` of them — a compound register's arms are
            // the latter, and disagree on *layout* rather than on type (a
            // constructed tuple arrives as a record of columns, the carried
            // snapshot as one column of record values), which is precisely what
            // materialising into a single column reconciles.
            //
            // A function-tiled arm is the case that must not pass: flattening it
            // through `Tiling::extent` would declare a scalar column of
            // *functions*, a tile the producer cannot emit and panics on at the
            // first `get`. Reject it here, where the shape is already known.
            let exts: Vec<Extent> = codomains
                .iter()
                .map(|t| match t {
                    Tiling::Scalar(e) => e.clone(),
                    Tiling::Record(fields)
                        if fields.values().all(|f| matches!(f, Tiling::Scalar(_))) =>
                    {
                        t.extent()
                    }
                    other => panic!(
                        "UnionOperator: arms with differing codomains merge into one \
                         column, so each must be a `Scalar` or a `Record` of them; \
                         got {other}"
                    ),
                })
                .collect();
            let joined = exts
                .iter()
                .skip(1)
                .try_fold(exts[0].clone(), |acc, e| acc.join(e));
            match joined {
                Some(ext) => Tiling::Scalar(ext),
                None => {
                    let deduped = dedup_extents(exts);
                    Tiling::Scalar(if deduped.len() == 1 {
                        deduped.into_iter().next().unwrap()
                    } else {
                        Extent::Union(TagMap::from_positional(deduped))
                    })
                }
            }
        };

        let tiling = Tiling::SealedFunction {
            domain: Extent::Union(TagMap::from_positional(domains)),
            codomain: Box::new(codomain),
        };
        Self {
            tiling,
            inputs,
            flat: false,
        }
    }

    /// A **flat-merge** union: arms over the *same* base extent (disjoint runtime
    /// subsets of one domain) merge back to that base rather than a tagged
    /// `Extent::Union`, so the result co-iterates with a sibling field. This is the
    /// writer-body value-`Case` fan-out `⧺ᵢ filter_values(π̂ᵢ) ≫ eᵢ`: every arm
    /// filters the *same* fed element stream, so their domains share one extent and
    /// their positions are disjoint by first-match. (The tagged [`new`](Self::new)
    /// is for a sourceless union whose arms have genuinely distinct extents — a Σ /
    /// C-form dispatch read by `final_or_default`.)
    pub fn new_flat(inputs: Vec<Box<dyn TileOperator>>) -> Self {
        let mut op = Self::new(inputs);
        op.flat = true;
        if let Tiling::SealedFunction { domain, codomain } = op.tiling {
            let deduped = dedup_extents(match domain {
                Extent::Union(ds) => ds.into_values(),
                other => vec![other],
            });
            let domain = if deduped.len() == 1 {
                deduped.into_iter().next().unwrap()
            } else {
                Extent::Union(TagMap::from_positional(deduped))
            };
            op.tiling = Tiling::SealedFunction { domain, codomain };
        }
        op
    }
}

/// Flat-merge disjoint `SealedFunction` arms into one flat tile, sorted by domain
/// key. Each arm is a filtered slice of the *same* fed element stream (a
/// writer-body value-`Case` fan-out `⧺ᵢ filter_values(π̂ᵢ) ≫ eᵢ`), so the arms'
/// (`UInt`) positions are disjoint and reassemble the full column — which then
/// co-iterates with the decision record's sibling `commit` field. The codomain is
/// a scalar decision-field value, or a boxed-compound `Tile::Record` for a
/// tuple/record accumulator; the shared fed predicate is taken from the first arm
/// (all arms carry it).
fn flat_merge(tiles: Vec<Tile>, codomain_tiling: &Tiling) -> Tile {
    let value_extent = codomain_tiling.extent();
    let mut pairs: Vec<(usize, Value)> = Vec::new();
    let mut domain_predicate = Predicate::False;
    for (i, tile) in tiles.into_iter().enumerate() {
        let Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate: dp,
            deleted,
        } = tile
        else {
            panic!("flat_merge: expected SealedFunction arm, got {tile:?}");
        };
        if i == 0 {
            domain_predicate = dp;
        }
        // The decision field's value is usually a scalar, but a compound
        // (tuple/record) accumulator carries a struct-of-arrays `Tile::Record`
        // codomain; box it to a single record-valued column so each row extracts
        // as one `Value`. `scalar_tile_to_column_value` is identity on a scalar.
        // A function-valued codomain (a collection-valued register) is out of
        // scope and would panic generically inside the helper — name the boundary.
        debug_assert!(
            matches!(codomain.as_ref(), Tile::Scalar(_) | Tile::Record(_)),
            "flat_merge: a writer-body value-Case arm must have a scalar or \
             boxed-compound codomain, got {codomain:?}"
        );
        let values = scalar_tile_to_column_value(*codomain);
        for row in 0..domain.len() {
            if deleted.contains(row) {
                continue;
            }
            let key = domain.index_at(row);
            let Value::UInt(pos) = key else {
                // A flat merge reassembles the arms *by position* into one column, so
                // every arm's domain key has to be a position. A tagged key means the
                // arms came from a copairing — whose domain deliberately keeps the
                // arms apart — and those do not merge back onto one domain at all.
                panic!(
                    "flat_merge: arm {i} row {row} is keyed {key:?}, not a UInt \
                     position; a flat merge reassembles arms by position, so a \
                     tagged domain here means these arms are a copairing rather \
                     than a disjoint join. Arm domain: {domain:?}"
                );
            };
            pairs.push((pos, values.index_at(row)));
        }
    }
    // Disjoint by first-match, so a stable sort by position reassembles the full
    // column in the fed order — matching the sibling `commit` field's domain.
    pairs.sort_by_key(|(pos, _)| *pos);
    // Disjointness is a *precondition*, not something the merge can repair: two
    // arms claiming one position put two values at one domain key, which is a
    // monotonic-merge violation however it is resolved — and silently, since the
    // sort just leaves them adjacent and the longer column flows on. Check it
    // where the arms are actually side by side rather than trusting the caller: a
    // value-`Case` whose first-match gates overlap, and a tag fan-out that lost a
    // `variant_project` to const-reduction, both land here. The scan is free
    // beside the sort above, so this is a hard assert rather than a debug one.
    if let Some(w) = pairs.windows(2).find(|w| w[0].0 == w[1].0) {
        panic!(
            "flat_merge: arms are not disjoint — position {} is claimed by more \
             than one arm, so the merge would place two values at one domain key",
            w[0].0
        );
    }
    let positions: Vec<usize> = pairs.iter().map(|(pos, _)| *pos).collect();
    let values: Vec<Value> = pairs.into_iter().map(|(_, v)| v).collect();
    // Build the codomain to match the operator's *declared* tiling shape: a
    // scalar field stays `Tile::Scalar`, a compound (tuple/record) field unboxes
    // the record-valued column back into a struct-of-arrays `Tile::Record`.
    let cv = ColumnValue::from_values(values, &value_extent);
    Tile::SealedFunction {
        domain: ColumnValue::from_uints(positions),
        codomain: Box::new(column_value_to_tile(cv, codomain_tiling)),
        domain_predicate,
        deleted: BitSet::new(),
    }
}

/// Deduplicate a list of extents, preserving order of first occurrence.
fn dedup_extents(extents: Vec<Extent>) -> Vec<Extent> {
    let mut seen: Vec<Extent> = Vec::new();
    for e in extents {
        if !seen.contains(&e) {
            seen.push(e);
        }
    }
    seen
}

impl TileOperator for UnionOperator {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, mut node: InspectNode, opts: &VizOptions) -> InspectNode {
        for (i, input) in self.inputs.iter().enumerate() {
            node = node.child(format!("{i}"), input.inspect(opts));
        }
        node
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let consumer_wrapper = Rc::new(RefCell::new(move || {
            consumer.notify();
        }));
        let input_producers: Vec<Box<dyn TileProducer>> = self
            .inputs
            .iter_mut()
            .map(|op| {
                op.subscribe(
                    op.tiling().universal_guard(),
                    Box::new(consumer_wrapper.clone()),
                    scheduler,
                )
            })
            .collect();
        Box::new(UnionProducer {
            base: ProducerBase::new(UnionProducer::alloc_id(), &self.tiling),
            inputs: input_producers,
            flat: self.flat,
        })
    }
}

/// Producer for [`UnionOperator`]: concatenates all input `SealedFunction` tiles
/// into a single tile with a `ColumnValue::Union` domain and interleaved codomain.
struct UnionProducer {
    base: ProducerBase,
    inputs: Vec<Box<dyn TileProducer>>,
    /// Flat-merge mode (see [`UnionOperator::new_flat`]).
    flat: bool,
}

impl TileProducer for UnionProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, mut node: InspectNode, opts: &VizOptions) -> InspectNode {
        for (i, p) in self.inputs.iter().enumerate() {
            node = node.child(format!("_{i}"), p.inspect(opts));
        }
        node
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let tiles: Vec<Tile> = self
            .inputs
            .iter_mut()
            .map(|p| p.get(p.tiling().universal_guard()))
            .collect();

        if self.flat {
            let codomain_tiling = match self.tiling() {
                Tiling::SealedFunction { codomain, .. } => (**codomain).clone(),
                other => panic!("flat union tiling is a SealedFunction, got {other}"),
            };
            return flat_merge(tiles, &codomain_tiling);
        }

        let mut domains: Vec<ColumnValue> = Vec::new();
        let mut codomains: Vec<Tile> = Vec::new();
        let mut domain_predicates: Vec<Predicate> = Vec::new();
        let mut combined_deleted = BitSet::new();
        let mut domain_offset: usize = 0;

        for tile in tiles {
            match tile {
                Tile::SealedFunction {
                    domain,
                    codomain,
                    domain_predicate: dp,
                    deleted,
                } => {
                    // Shift each deleted index into the combined domain's position space.
                    for idx in deleted.iter() {
                        combined_deleted.insert(idx + domain_offset);
                    }
                    domain_offset += domain.len();
                    domains.push(domain);
                    codomains.push(*codomain);
                    domain_predicates.push(dp);
                }
                other => panic!("UnionProducer: expected SealedFunction, got {other:?}"),
            }
        }

        let domain_predicate = Predicate::Union(TagMap::from_positional(domain_predicates));

        // Build the discriminated-union domain column. Each arm occupies a
        // contiguous run of rows, in arm order.
        let mut next_row = 0usize;
        let union_domain = ColumnValue::Union(TagMap::from_positional(
            domains
                .into_iter()
                .map(|d| {
                    let rows: Vec<usize> = (next_row..next_row + d.len()).collect();
                    next_row += d.len();
                    UnionArm::new(rows, d)
                })
                .collect(),
        ));
        union_domain.debug_assert_union_invariants();

        // Build the interleaved codomain tile.
        // If all codomains are Scalar ColumnValues of the same variant, concatenate them.
        // Otherwise materialise each scalar as Value rows into a Variants column.
        let codomain_tile: Tile = {
            let all_scalar = codomains.iter().all(|c| matches!(c, Tile::Scalar(_)));
            let same_variant = all_scalar && {
                let first_disc = std::mem::discriminant(if let Tile::Scalar(cv) = &codomains[0] {
                    cv
                } else {
                    unreachable!()
                });
                codomains.iter().all(|c| {
                    if let Tile::Scalar(cv) = c {
                        std::mem::discriminant(cv) == first_disc
                    } else {
                        false
                    }
                })
            };
            if same_variant {
                let mut combined = match codomains.remove(0) {
                    Tile::Scalar(cv) => cv,
                    _ => unreachable!(),
                };
                for c in codomains {
                    match c {
                        Tile::Scalar(cv) => combined.append(cv),
                        _ => unreachable!(),
                    }
                }
                Tile::Scalar(combined)
            } else {
                // Heterogeneous codomains: materialise one Value per row in source order.
                let mut values: Vec<Value> = Vec::new();
                for cod in codomains {
                    let n = cod.len();
                    match cod {
                        Tile::Scalar(cv) => {
                            for i in 0..n {
                                values.push(cv.index_at(i));
                            }
                        }
                        other => panic!(
                            "UnionProducer: complex nested codomain tiles are not yet supported: {other:?}"
                        ),
                    }
                }
                Tile::Scalar(ColumnValue::Variants(values))
            }
        };

        Tile::SealedFunction {
            domain: union_domain,
            codomain: Box::new(codomain_tile),
            domain_predicate,
            deleted: combined_deleted,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        match obsolete_guard {
            g if g.is_empty() => {}
            g if g.is_universal() => {
                for input in &mut self.inputs {
                    input.release(input.tiling().universal_guard());
                }
            }
            // Split the per-variant predicates and forward each to the input that
            // produced that variant's data.
            TileGuard::Function(FunctionGuard::Domain(Predicate::Union(ps))) => {
                assert_eq!(
                    ps.len(),
                    self.inputs.len(),
                    "UnionProducer::release_impl: variant count mismatch"
                );
                for (input, (_, pred)) in self.inputs.iter_mut().zip(ps) {
                    input.release(TileGuard::Function(FunctionGuard::Domain(pred)));
                }
            }
            // A **flat** union has one flat domain (not per-variant tags), so a
            // released prefix over it forwards to every arm — each arm holds a
            // disjoint subset of those positions and ignores the rest.
            TileGuard::Function(FunctionGuard::Domain(pred)) if self.flat => {
                for input in &mut self.inputs {
                    input.release(TileGuard::Function(FunctionGuard::Domain(pred.clone())));
                }
            }
            other => panic!("UnionProducer::release_impl: unexpected guard {other:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::{BaseType, ColumnValue, Extent};
    use std::cell::RefCell;

    // ── UnionProducer::release_impl ───────────────────────────────────────────

    fn int_sealed_tiling() -> Tiling {
        Tiling::SealedFunction {
            domain: Extent::Base(BaseType::Int),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        }
    }

    fn int_sealed_tile() -> Tile {
        Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        }
    }

    /// A `SealedFunction` operator with a chosen tiling, for asserting on what
    /// [`UnionOperator::new`] *declares* (the tiling), independent of any data.
    struct TilingOnly(Tiling);

    impl TileOperator for TilingOnly {
        fn tiling(&self) -> &Tiling {
            &self.0
        }
        fn subscribe(
            &mut self,
            _intent_guard: TileGuard,
            _consumer: Box<dyn Consumer>,
            _scheduler: &mut Scheduler,
        ) -> Box<dyn TileProducer> {
            unimplemented!("tiling-only stub is never pulled")
        }
    }

    fn named_variant(arms: &[(&str, Extent)]) -> Extent {
        Extent::Union(TagMap::from_arms(
            arms.iter()
                .map(|(t, e)| (crate::ccl::FieldKey::Name((*t).into()), e.clone()))
                .collect(),
        ))
    }

    fn sealed_with_codomain(codomain: Extent) -> Box<dyn TileOperator> {
        Box::new(TilingOnly(Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Scalar(codomain)),
        }))
    }

    /// Arms whose codomains are differently-tagged variants are **alternative
    /// values of one result**, so the declared codomain is their merged tag set —
    /// which is the column the union actually builds, with the arm that did not
    /// occur left empty. Declaring a positional sum instead describes a value no
    /// row holds, and the tile then fails to conform to its own tiling.
    #[test]
    fn codomain_of_differently_tagged_variant_arms_is_the_merged_variant() {
        let op = UnionOperator::new(vec![
            sealed_with_codomain(named_variant(&[("pos", Extent::Base(BaseType::Int))])),
            sealed_with_codomain(named_variant(&[("neg", Extent::Base(BaseType::Int))])),
        ]);
        let Tiling::SealedFunction { codomain, .. } = op.tiling() else {
            panic!("union of sealed functions is a sealed function");
        };
        assert_eq!(
            **codomain,
            Tiling::Scalar(named_variant(&[
                ("neg", Extent::Base(BaseType::Int)),
                ("pos", Extent::Base(BaseType::Int)),
            ]))
        );
    }

    /// Agreeing arms are the join's trivial case and keep the shared codomain.
    #[test]
    fn codomain_of_agreeing_arms_is_shared() {
        let op = UnionOperator::new(vec![
            sealed_with_codomain(Extent::Base(BaseType::Int)),
            sealed_with_codomain(Extent::Base(BaseType::Int)),
        ]);
        let Tiling::SealedFunction { codomain, .. } = op.tiling() else {
            panic!("union of sealed functions is a sealed function");
        };
        assert_eq!(**codomain, Tiling::Scalar(Extent::Base(BaseType::Int)));
    }

    /// Arms with no join stay an anonymous positional sum: for a concatenation the
    /// arm a row came from is part of its identity, so the two are kept apart
    /// rather than merged.
    #[test]
    fn codomain_of_unjoinable_arms_stays_a_positional_sum() {
        let op = UnionOperator::new(vec![
            sealed_with_codomain(Extent::Base(BaseType::Int)),
            sealed_with_codomain(Extent::Base(BaseType::String)),
        ]);
        let Tiling::SealedFunction { codomain, .. } = op.tiling() else {
            panic!("union of sealed functions is a sealed function");
        };
        assert_eq!(
            **codomain,
            Tiling::Scalar(Extent::Union(TagMap::from_positional(vec![
                Extent::Base(BaseType::Int),
                Extent::Base(BaseType::String),
            ])))
        );
    }

    /// Differing arms merge into one *column*, which is also the only codomain
    /// shape `UnionProducer` can build. A non-`Scalar` arm is therefore rejected
    /// here rather than declared as a scalar column of functions — a tile the
    /// producer cannot emit, and which would have failed at the first `get`
    /// instead of at graph construction where the shape is known.
    #[test]
    #[should_panic(expected = "arms with differing codomains merge into one column")]
    fn differing_non_scalar_codomains_are_rejected_at_construction() {
        let nested = Box::new(TilingOnly(Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(int_sealed_tiling()),
        })) as Box<dyn TileOperator>;
        let _ = UnionOperator::new(vec![
            sealed_with_codomain(Extent::Base(BaseType::Int)),
            nested,
        ]);
    }

    // ── flat_merge: the arms' domains must partition, not overlap ─────────────

    /// A `SealedFunction` arm holding `(key, value)` pairs — one slice of the
    /// fed element stream, as a tag fan-out or a first-match value-`Case` produces.
    fn flat_arm(pairs: &[(usize, i64)]) -> Tile {
        Tile::SealedFunction {
            domain: ColumnValue::from_uints(pairs.iter().map(|(k, _)| *k).collect()),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(
                pairs.iter().map(|(_, v)| *v).collect(),
            ))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        }
    }

    /// The precondition holding: disjoint arms reassemble into the full column,
    /// sorted by position, whatever order the arms arrive in.
    #[test]
    fn flat_merge_reassembles_disjoint_arms_by_position() {
        let out = flat_merge(
            vec![flat_arm(&[(1, 20), (3, 40)]), flat_arm(&[(0, 10), (2, 30)])],
            &Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
        let Tile::SealedFunction {
            domain, codomain, ..
        } = out
        else {
            panic!("flat merge yields a SealedFunction");
        };
        assert_eq!(domain, ColumnValue::from_uints(vec![0, 1, 2, 3]));
        assert_eq!(
            *codomain,
            Tile::Scalar(ColumnValue::Ints(vec![10, 20, 30, 40]))
        );
    }

    /// The precondition violated. Overlapping arms are a **caller** bug — a
    /// value-`Case` whose first-match gates are not actually exclusive, or a tag
    /// fan-out that lost a `variant_project` — and the merge cannot repair it:
    /// two values at one domain key violate monotonic merge however it picks.
    /// Left unchecked it is silent, since the sort just leaves the duplicates
    /// adjacent and a column one row too long flows on downstream.
    #[test]
    #[should_panic(expected = "position 1 is claimed by more than one arm")]
    fn flat_merge_rejects_arms_that_claim_one_position_twice() {
        let _ = flat_merge(
            vec![flat_arm(&[(0, 10), (1, 20)]), flat_arm(&[(1, 99)])],
            &Tiling::Scalar(Extent::Base(BaseType::Int)),
        );
    }

    /// Build a `UnionProducer` with two spy inputs that record what guard they receive.
    ///
    /// Returns the producer plus `Rc<RefCell<Vec<TileGuard>>>` for each input.
    #[allow(clippy::type_complexity)]
    fn make_union_producer_with_spies() -> (
        UnionProducer,
        Rc<RefCell<Vec<TileGuard>>>,
        Rc<RefCell<Vec<TileGuard>>>,
    ) {
        struct SpyProducer {
            base: ProducerBase,
            tile: Tile,
            log: Rc<RefCell<Vec<TileGuard>>>,
        }

        impl TileProducer for SpyProducer {
            impl_producer_base!();
            fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
                node
            }
            fn get_impl(&mut self, _: TileGuard) -> Tile {
                self.tile.clone()
            }
            fn release_impl(&mut self, obsolete_guard: TileGuard) {
                self.log.borrow_mut().push(obsolete_guard);
            }
        }

        let log0: Rc<RefCell<Vec<TileGuard>>> = Rc::new(RefCell::new(Vec::new()));
        let log1: Rc<RefCell<Vec<TileGuard>>> = Rc::new(RefCell::new(Vec::new()));

        let union_tiling = Tiling::SealedFunction {
            domain: Extent::Union(TagMap::from_positional(vec![
                Extent::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            ])),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };

        let producer = UnionProducer {
            base: ProducerBase::new(UnionProducer::alloc_id(), &union_tiling),
            inputs: vec![
                Box::new(SpyProducer {
                    base: ProducerBase::new(0, &int_sealed_tiling()),
                    tile: int_sealed_tile(),
                    log: log0.clone(),
                }),
                Box::new(SpyProducer {
                    base: ProducerBase::new(1, &int_sealed_tiling()),
                    tile: int_sealed_tile(),
                    log: log1.clone(),
                }),
            ],
            flat: false,
        };

        (producer, log0, log1)
    }

    /// An empty guard is a no-op: no release signal reaches any input.
    #[test]
    fn union_producer_release_empty_is_noop() {
        let (mut producer, log0, log1) = make_union_producer_with_spies();
        producer.release(producer.tiling().empty_guard());
        assert!(
            log0.borrow().is_empty(),
            "input 0 should receive no release"
        );
        assert!(
            log1.borrow().is_empty(),
            "input 1 should receive no release"
        );
    }

    /// A universal guard forwards a universal guard to every input.
    #[test]
    fn union_producer_release_universal_forwards_to_all_inputs() {
        let (mut producer, log0, log1) = make_union_producer_with_spies();
        producer.release(producer.tiling().universal_guard());
        let l0 = log0.borrow();
        let l1 = log1.borrow();
        assert_eq!(l0.len(), 1, "input 0 should receive exactly one release");
        assert_eq!(l1.len(), 1, "input 1 should receive exactly one release");
        assert!(
            l0[0].is_universal(),
            "input 0 should receive a universal guard"
        );
        assert!(
            l1[0].is_universal(),
            "input 1 should receive a universal guard"
        );
    }

    /// A `Predicate::Union` guard splits per-variant predicates to the correct inputs.
    #[test]
    fn union_producer_release_union_pred_routes_to_correct_inputs() {
        let (mut producer, log0, log1) = make_union_producer_with_spies();

        let pred0 = Predicate::from_column_value(&ColumnValue::Ints(vec![1, 2]));
        let pred1 = Predicate::from_column_value(&ColumnValue::Ints(vec![3, 4]));
        let guard = TileGuard::Function(FunctionGuard::Domain(Predicate::Union(
            TagMap::from_positional(vec![pred0.clone(), pred1.clone()]),
        )));

        producer.release(guard);

        let l0 = log0.borrow();
        let l1 = log1.borrow();
        assert_eq!(l0.len(), 1, "input 0 should receive exactly one release");
        assert_eq!(l1.len(), 1, "input 1 should receive exactly one release");
        assert_eq!(
            l0[0],
            TileGuard::Function(FunctionGuard::Domain(pred0)),
            "input 0 should receive pred0"
        );
        assert_eq!(
            l1[0],
            TileGuard::Function(FunctionGuard::Domain(pred1)),
            "input 1 should receive pred1"
        );
    }
}
