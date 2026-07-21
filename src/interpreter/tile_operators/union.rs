use bit_set::BitSet;
use std::{cell::RefCell, iter, rc::Rc};

use super::*;
use crate::{
    interpreter::{ColumnValue, Consumer, Extent, Scheduler, Value},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

// ---------------------------------------------------------------------------
// UnionOperator / UnionProducer
// ---------------------------------------------------------------------------

/// Merges N `SealedFunction` operators into one by taking the discriminated
/// union of their domains and the deduplicated union of their codomains.
///
/// The output tiling is `SealedFunction { domain: Union(d₀, …, dₙ₋₁), codomain }`,
/// where `codomain` is the shared codomain tiling when all inputs agree, or a
/// `Scalar(Union(…))` wrapping otherwise.
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
    /// `Extent::Union` of all input domains; the codomain is shared if
    /// all inputs agree, or `Extent::Union` (deduplicated) otherwise.
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

        // Dedup codomains: if all agree use the shared tiling, else wrap in Union.
        let codomain = if codomains.windows(2).all(|w| w[0] == w[1]) {
            codomains[0].clone()
        } else {
            let exts: Vec<Extent> = codomains.iter().map(|t| t.extent()).collect();
            let deduped = dedup_extents(exts);
            Tiling::Scalar(if deduped.len() == 1 {
                deduped.into_iter().next().unwrap()
            } else {
                Extent::Union(deduped)
            })
        };

        let tiling = Tiling::SealedFunction {
            domain: Extent::Union(domains),
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
                Extent::Union(ds) => ds,
                other => vec![other],
            });
            let domain = if deduped.len() == 1 {
                deduped.into_iter().next().unwrap()
            } else {
                Extent::Union(deduped)
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
            let Value::UInt(pos) = domain.index_at(row) else {
                panic!("flat_merge: writer-body fan-out arms have UInt (position) domains");
            };
            pairs.push((pos, values.index_at(row)));
        }
    }
    // Disjoint by first-match, so a stable sort by position reassembles the full
    // column in the fed order — matching the sibling `commit` field's domain.
    pairs.sort_by_key(|(pos, _)| *pos);
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

        let domain_predicate = Predicate::Union(domain_predicates);

        // Build the discriminated-union domain column.
        let total_len: usize = domains.iter().map(|d| d.len()).sum();
        let mut tags: Vec<usize> = Vec::with_capacity(total_len);
        for (i, d) in domains.iter().enumerate() {
            tags.extend(iter::repeat_n(i, d.len()));
        }
        let union_domain = ColumnValue::Union {
            tags,
            variants: domains,
        };

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
                let mut values: Vec<Value> = Vec::with_capacity(total_len);
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
                for (input, pred) in self.inputs.iter_mut().zip(ps) {
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
            domain: Extent::Union(vec![
                Extent::Base(BaseType::Int),
                Extent::Base(BaseType::Int),
            ]),
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
        let guard = TileGuard::Function(FunctionGuard::Domain(Predicate::Union(vec![
            pred0.clone(),
            pred1.clone(),
        ])));

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
