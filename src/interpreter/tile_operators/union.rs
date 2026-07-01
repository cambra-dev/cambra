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
        Self { tiling, inputs }
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
        })
    }
}

/// Producer for [`UnionOperator`]: concatenates all input `SealedFunction` tiles
/// into a single tile with a `ColumnValue::Union` domain and interleaved codomain.
struct UnionProducer {
    base: ProducerBase,
    inputs: Vec<Box<dyn TileProducer>>,
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
            other => panic!("UnionProducer::release_impl: unexpected guard {other:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::{BaseType, ColumnValue, Extent};
    use std::cell::RefCell;
    use std::rc::Rc;

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
