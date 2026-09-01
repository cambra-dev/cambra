use bit_set::BitSet;
use log::trace;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use super::*;
use crate::interpreter::operator_graph::value_at;
use crate::{
    interpreter::{ColumnValue, Consumer, Extent, Scheduler, tuple_field},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// Combines multiple sealed-function operators sharing the same domain into a
/// single sealed-function operator whose codomain is a record of all their codomains.
///
/// All inputs must have `SealedFunction` tilings with compatible domains.
/// Output fields are named `_0`, `_1`, … matching the input order.
pub struct FanIn {
    /// Identity and the output tiling: either a
    /// `SealedFunction { domain, codomain: Record { … } }` or a
    /// `CurriedFunction { domain1, domain2, codomain: Record { … } }`, depending
    /// on the input operators.
    base: OperatorBase,
    /// Field names in input order, used when producing the output Record tile.
    names: Vec<String>,
    /// The input function operators to zip together (either all `SealedFunction` or all `CurriedFunction`).
    inputs: Vec<Box<dyn TileOperator>>,
}

impl FanIn {
    /// Create a new `FanIn` operator over the given input operators.
    ///
    /// All inputs must be either all `SealedFunction` tilings with the same domain,
    /// or all `CurriedFunction` tilings with the same domain1, offsets, and domain2.
    /// The output `tiling` and `extent` are derived: each input's codomain extent
    /// becomes a field (`_0`, `_1`, …) in a `Record` codomain.
    pub fn new(inputs: Vec<Box<dyn TileOperator>>) -> Self {
        trace!(
            "Creating zip with inputs {}",
            inputs
                .iter()
                .map(|i| i.tiling().to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        assert!(!inputs.is_empty(), "FanIn requires at least one input");
        let names = (0..inputs.len()).map(tuple_field).collect();
        Self::new_impl(names, inputs)
    }

    /// Construct a `FanIn` with explicit named fields for record literals.
    ///
    /// Like [`Self::new`] but uses caller-supplied field names instead of
    /// the synthetic `_0`, `_1`, … names used for tuples.
    pub fn new_named(inputs: Vec<(String, Box<dyn TileOperator>)>) -> Self {
        assert!(!inputs.is_empty(), "FanIn requires at least one input");
        let (names, ops) = inputs.into_iter().unzip();
        Self::new_impl(names, ops)
    }

    fn new_impl(names: Vec<String>, ops: Vec<Box<dyn TileOperator>>) -> Self {
        // The [`fan_in`] dispatcher guarantees all inputs are function-typed
        // (otherwise it routes to [`ScalarFanIn`]).  Inputs may still have
        // *different* tile-level presence at runtime — e.g. one branch has
        // emitted positions 0..3 while another has only 0..2 — which is
        // handled by an intersection step in `FanInProducer::get_impl`.
        let first_tiling = ops[0].tiling();
        let tiling = match first_tiling {
            Tiling::SealedFunction { domain, .. } => {
                for op in ops.iter().skip(1) {
                    if let Tiling::SealedFunction { domain: d, .. } = op.tiling() {
                        assert_eq!(
                            domain, d,
                            "FanIn: all SealedFunction inputs must have the same domain"
                        );
                    } else {
                        panic!(
                            "FanIn: all inputs must be the same type (all SealedFunction or all CurriedFunction)"
                        );
                    }
                }
                Tiling::SealedFunction {
                    domain: domain.clone(),
                    codomain: Box::new(Tiling::Record(
                        names
                            .iter()
                            .zip(ops.iter())
                            .map(|(name, op)| {
                                (
                                    name.clone(),
                                    op.tiling()
                                        .codomain()
                                        .unwrap_or_else(|| {
                                            panic!("Expected function, got {}", op.tiling())
                                        })
                                        .clone(),
                                )
                            })
                            .collect(),
                    )),
                }
            }
            Tiling::CurriedFunction {
                domain1, domain2, ..
            } => {
                for op in ops.iter().skip(1) {
                    if let Tiling::CurriedFunction {
                        domain1: d1,
                        domain2: d2,
                        ..
                    } = op.tiling()
                    {
                        assert_eq!(
                            domain1, d1,
                            "FanIn: all CurriedFunction inputs must have the same domain1"
                        );
                        assert_eq!(
                            domain2, d2,
                            "FanIn: all CurriedFunction inputs must have the same domain2"
                        );
                    } else {
                        panic!(
                            "FanIn: all inputs must be the same type (all SealedFunction or all CurriedFunction)"
                        );
                    }
                }
                Tiling::CurriedFunction {
                    domain1: domain1.clone(),
                    domain2: domain2.clone(),
                    codomain: Extent::Record(
                        names
                            .iter()
                            .zip(ops.iter())
                            .map(|(name, op)| {
                                let Tiling::CurriedFunction { codomain: cod, .. } = op.tiling()
                                else {
                                    panic!("Expected CurriedFunction, got {}", op.tiling())
                                };
                                (name.clone(), cod.clone())
                            })
                            .collect(),
                    ),
                }
            }
            _ => panic!(
                "FanIn: all inputs must have function tilings (SealedFunction or CurriedFunction)"
            ),
        };
        let edges: Vec<InputEdgeSpec> = ops
            .iter()
            .enumerate()
            .map(|(i, op)| value_at(i, &**op))
            .collect();
        Self {
            base: OperatorBase::new::<Self>(tiling, &edges),
            names,
            inputs: ops,
        }
    }
}

/// Tile-polymorphic fan-in factory.
///
/// Given N operators representing the arms of a CCL-level `zip(f₀, …, fₙ₋₁)`,
/// returns the correct tile-level combinator for the arms' runtime tilings:
///
/// - If every arm has a scalar tiling (`Scalar` or a `Record` of scalars),
///   the fan-in is just a record-of-values and [`ScalarFanIn`] is returned.
/// - Otherwise the arms carry function tilings and [`FanIn`] is returned,
///   which fans the shared domain out into a record-codomain sealed/curried
///   function.
///
/// Callers at op-conversion can hand the compiled arms to this factory
/// without knowing what tiling the arms ended up with — the upstream
/// `input` at the zip call site determines that, and the factory picks
/// the right combinator. See the "CCL types vs. tilings" section of
/// [`design-operators.md`](./design-operators.md) for why the same
/// CCL-level `zip` compiles to two different tile operators.
pub fn fan_in(inputs: Vec<Box<dyn TileOperator>>) -> Box<dyn TileOperator> {
    if inputs.iter().all(|op| op.tiling().is_scalar()) {
        Box::new(ScalarFanIn::new(inputs))
    } else {
        Box::new(FanIn::new(inputs))
    }
}

/// Named-field variant of [`fan_in`]: like [`fan_in`] but uses caller-supplied
/// field names instead of the synthetic `_0`, `_1`, … names.
pub fn fan_in_named(inputs: Vec<(String, Box<dyn TileOperator>)>) -> Box<dyn TileOperator> {
    if inputs.iter().all(|(_, op)| op.tiling().is_scalar()) {
        Box::new(ScalarFanIn::new_named(inputs))
    } else {
        Box::new(FanIn::new_named(inputs))
    }
}

impl TileOperator for FanIn {
    impl_operator_base!();

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
        Box::new(FanInProducer {
            base: ProducerBase::new(FanInProducer::alloc_id(), &self.base.tiling),
            names: self.names.clone(),
            inputs: self
                .inputs
                .iter_mut()
                .map(|i| {
                    i.subscribe(
                        i.tiling().universal_guard(),
                        Box::new(consumer_wrapper.clone()),
                        scheduler,
                    )
                })
                .collect(),
        })
    }
}

/// Producer for [`FanIn`]: pulls each input and assembles a record-codomain tile.
struct FanInProducer {
    base: ProducerBase,
    /// Field names in input order, used when producing the output Record tile.
    names: Vec<String>,
    /// Live input producers, in field order.
    inputs: Vec<Box<dyn TileProducer>>,
}

impl TileProducer for FanInProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, mut node: InspectNode, opts: &VizOptions) -> InspectNode {
        for (i, input) in self.inputs.iter().enumerate() {
            node = node.child(format!("_{i}"), input.inspect(opts));
        }
        node
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // Cost note: the presence-intersection path below runs
        // unconditionally on every pull — N predicate intersections, N
        // `to_remove` minuses, and one `remove_guarded` per input.  Non-
        // cyclic FanIns over well-aligned inputs pay the same per-pull
        // cost as the mutation-loop body's lagging-branch case (where the
        // recursive_input legitimately trails the source branch).  If
        // profiling later shows this on a hot path, consider gating the
        // intersection on a `cyclic: bool` constructor flag (mirroring
        // `FanOut::new` vs `FanOut::new_cyclic`) and keeping the simpler
        // "all inputs agree" path for fan-ins that can't lag.
        let tiles: Vec<Tile> = self
            .inputs
            .iter_mut()
            .map(|i| i.get(i.tiling().universal_guard()))
            .collect();

        match &tiles[0] {
            Tile::SealedFunction { .. } => {
                // All inputs are SealedFunction tiles, but they may differ in
                // which *actual rows* are present — one branch may have
                // emitted positions 0..3 while another has only 0..2 (or one
                // input's upstream release shrank its known region).  We
                // compute the intersection of every input's actually-present
                // positions (a `Predicate` built from each tile's `domain`
                // column), filter every tile down to it, and only then build
                // the combined codomain record.
                //
                // We separately intersect the inputs' `domain_predicate`s for
                // the *output* tile's predicate — that's purely forward-
                // looking finality, not what governs which rows to keep,
                // because a non-terminal input (e.g. an incremental data
                // source) carries `domain_predicate: False` alongside
                // fully-valid concrete rows.
                let mut presence: Option<Predicate> = None;
                let mut domain_pred: Option<Predicate> = None;
                for t in tiles.iter() {
                    let Tile::SealedFunction {
                        domain,
                        domain_predicate,
                        ..
                    } = t
                    else {
                        panic!("FanIn: cannot mix SealedFunction and other tile types")
                    };
                    let p = Predicate::from_column_value(domain);
                    presence = Some(match presence {
                        None => p,
                        Some(prev) => prev.intersect(&p),
                    });
                    domain_pred = Some(match domain_pred {
                        None => domain_predicate.clone(),
                        Some(prev) => prev.intersect(domain_predicate),
                    });
                }
                let presence = presence.unwrap();
                let intersect_pred = domain_pred.unwrap();

                // Filter each tile to the intersection of present positions
                // (compute "to_remove" as that tile's domain minus the
                // intersection, then drop those rows).
                let mut output_domain: Option<ColumnValue> = None;
                let mut codomains: Vec<Tile> = Vec::with_capacity(tiles.len());
                for t in tiles.into_iter() {
                    let Tile::SealedFunction {
                        domain: tile_domain,
                        codomain,
                        domain_predicate,
                        deleted,
                    } = t
                    else {
                        unreachable!()
                    };
                    let domain_presence = Predicate::from_column_value(&tile_domain);
                    let to_remove = domain_presence.minus(&presence);
                    let mut filtered = Tile::SealedFunction {
                        domain: tile_domain,
                        codomain,
                        domain_predicate,
                        deleted,
                    };
                    if to_remove.as_bool() != Some(false) {
                        filtered
                            .remove_guarded(TileGuard::Function(FunctionGuard::Domain(to_remove)));
                    }
                    filtered.compact();
                    let Tile::SealedFunction {
                        domain, codomain, ..
                    } = filtered
                    else {
                        unreachable!()
                    };
                    if output_domain.is_none() {
                        output_domain = Some(domain);
                    }
                    codomains.push(*codomain);
                }

                let names = &self.names;
                let codomain_record = Tile::Record(
                    codomains
                        .into_iter()
                        .enumerate()
                        .map(move |(i, cv)| (names[i].clone(), cv))
                        .collect(),
                );
                Tile::SealedFunction {
                    domain: output_domain.unwrap(),
                    codomain: Box::new(codomain_record),
                    domain_predicate: intersect_pred,
                    deleted: BitSet::new(),
                }
            }
            Tile::CurriedFunction { .. } => {
                // All inputs are CurriedFunction tiles
                let mut domain1: Option<ColumnValue> = None;
                let mut offsets: Option<ColumnValue> = None;
                let mut domain2: Option<ColumnValue> = None;
                let mut domain_pred: Option<Predicate> = None;
                let mut codomains = Vec::new();

                for t in tiles.into_iter() {
                    match t {
                        Tile::CurriedFunction {
                            domain1: d1,
                            offsets: offs,
                            domain2: d2,
                            codomain: cod,
                            domain_predicate,
                            ..
                        } => {
                            if let Some(ref prev_d1) = domain1 {
                                assert_eq!(
                                    prev_d1, &d1,
                                    "FanIn: all inputs must have the same domain1"
                                );
                            }
                            if let Some(ref prev_offs) = offsets {
                                assert_eq!(
                                    prev_offs, &offs,
                                    "FanIn: all inputs must have the same offsets"
                                );
                            }
                            if let Some(ref prev_d2) = domain2 {
                                assert_eq!(
                                    prev_d2, &d2,
                                    "FanIn: all inputs must have the same domain2"
                                );
                            }
                            if let Some(ref mut prev) = domain_pred {
                                *prev = prev.intersect(&domain_predicate);
                            } else {
                                domain_pred = Some(domain_predicate.clone());
                            }
                            domain1 = Some(d1);
                            offsets = Some(offs);
                            domain2 = Some(d2);
                            codomains.push(cod);
                        }
                        _ => panic!("FanIn: cannot mix CurriedFunction and other tile types"),
                    }
                }

                let names = &self.names;
                let codomain_record = ColumnValue::Records(
                    codomains
                        .into_iter()
                        .enumerate()
                        .map(move |(i, cv)| (names[i].clone(), cv))
                        .collect(),
                );
                Tile::CurriedFunction {
                    domain1: domain1.unwrap(),
                    offsets: offsets.unwrap(),
                    domain2: domain2.unwrap(),
                    codomain: codomain_record,
                    domain_predicate: domain_pred.unwrap(),
                    deleted: BitSet::new(),
                }
            }
            _ => panic!("FanIn: all inputs must be SealedFunction or CurriedFunction tiles"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        self.inputs.iter_mut().for_each(|i| {
            i.release(match &obsolete_guard {
                g if g.is_universal() => i.tiling().universal_guard(),
                g if g.is_empty() => i.tiling().empty_guard(),
                TileGuard::Function(FunctionGuard::Domain(p)) => {
                    TileGuard::Function(FunctionGuard::Domain(p.clone()))
                }
                TileGuard::Function(FunctionGuard::Codomain(g)) => {
                    TileGuard::Function(FunctionGuard::Codomain(g.clone()))
                }
                g => unimplemented!("FanIn cannot honor the release guard {g:?}"),
            })
        });
    }
}

/// Pack N scalar inputs into a single scalar [`Tile::Record`] output.
///
/// Analogous to [`FanIn`] for function tiles, but operates entirely on scalars:
/// each input must produce a `Tile::Scalar` and the output is a
/// `Tile::Scalar(ColumnValue::Records)` keyed `_0`, `_1`, …, `_N-1`.
pub struct ScalarFanIn {
    /// Identity and the output tiling: a `Record` of the inputs' scalar tilings.
    base: OperatorBase,
    /// Field names in input order, used when producing `Tile::Record` tiles.
    names: Vec<String>,
    inputs: Vec<Box<dyn TileOperator>>,
}

impl ScalarFanIn {
    /// Construct a `ScalarFanIn` from N scalar input operators.
    ///
    /// All inputs must have scalar tilings. The output `extent` and `tiling`
    /// are derived: each input's scalar extent becomes a field (`_0`, `_1`, …)
    /// in the output `Extent::Record`.
    pub fn new(inputs: Vec<Box<dyn TileOperator>>) -> Self {
        assert!(
            !inputs.is_empty(),
            "ScalarFanIn requires at least one input"
        );
        let names = (0..inputs.len()).map(tuple_field).collect();
        Self::new_impl(names, inputs)
    }

    /// Construct a `ScalarFanIn` with explicit named fields for record literals.
    ///
    /// Like [`Self::new`] but uses the caller-supplied field names instead of
    /// the synthetic `_0`, `_1`, … names used for tuples.
    pub fn new_named(inputs: Vec<(String, Box<dyn TileOperator>)>) -> Self {
        assert!(
            !inputs.is_empty(),
            "ScalarFanIn requires at least one input"
        );
        let (names, ops) = inputs.into_iter().unzip();
        Self::new_impl(names, ops)
    }

    fn new_impl(names: Vec<String>, inputs: Vec<Box<dyn TileOperator>>) -> Self {
        let tiling = Tiling::Record(
            names
                .iter()
                .zip(inputs.iter())
                .map(|(name, op)| (name.clone(), op.tiling().clone()))
                .collect(),
        );
        let edges: Vec<InputEdgeSpec> = inputs
            .iter()
            .enumerate()
            .map(|(i, op)| value_at(i, &**op))
            .collect();
        Self {
            base: OperatorBase::new::<Self>(tiling, &edges),
            names,
            inputs,
        }
    }
}

impl TileOperator for ScalarFanIn {
    impl_operator_base!();

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
        Box::new(ScalarFanInProducer {
            base: ProducerBase::new(ScalarFanInProducer::alloc_id(), &self.base.tiling),
            names: self.names.clone(),
            inputs: self
                .inputs
                .iter_mut()
                .map(|i| {
                    i.subscribe(
                        i.tiling().universal_guard(),
                        Box::new(consumer_wrapper.clone()),
                        scheduler,
                    )
                })
                .collect(),
        })
    }
}

/// Producer for [`ScalarFanIn`]: pulls each scalar input and combines them into
/// a `Tile::Scalar(ColumnValue::Records)`.
struct ScalarFanInProducer {
    base: ProducerBase,
    names: Vec<String>,
    inputs: Vec<Box<dyn TileProducer>>,
}

impl TileProducer for ScalarFanInProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, mut node: InspectNode, opts: &VizOptions) -> InspectNode {
        for (i, input) in self.inputs.iter().enumerate() {
            node = node.child(format!("{i}"), input.inspect(opts));
        }
        node
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let fields: HashMap<String, Tile> = self
            .names
            .iter()
            .zip(self.inputs.iter_mut())
            .map(|(name, input)| {
                let tile = input.get(input.tiling().universal_guard());
                (name.clone(), tile)
            })
            .collect();
        Tile::Record(fields)
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.expect_universal_or_empty(&self.name()) {
            self.inputs
                .iter_mut()
                .for_each(|i| i.release(i.tiling().universal_guard()));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{ReleaseSpy, TestTileProducer};
    use crate::interpreter::{BaseType, ColumnValue, Extent};

    /// A `ScalarFanIn` re-reads every operand on every pull, so it can only pass a
    /// release on once there will be no next pull — which is exactly what a
    /// universal release from its consumer says. Swallowing it strands every
    /// producer beneath a binop operand or record field, and because [`FanOut`]
    /// forwards the *intersection* of its branches' guards, one branch that never
    /// releases blocks reclamation for all of them.
    #[test]
    fn scalar_fan_in_forwards_a_universal_release_to_every_operand() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let mut logs = Vec::new();
        let mut inputs: Vec<Box<dyn TileProducer>> = Vec::new();
        for _ in 0..2 {
            let (spy, log) =
                ReleaseSpy::new(Tile::Scalar(ColumnValue::Ints(vec![1])), tiling.clone());
            logs.push(log);
            inputs.push(Box::new(spy));
        }
        let out_tiling = Tiling::Record((0..2).map(|i| (tuple_field(i), tiling.clone())).collect());
        let mut producer = ScalarFanInProducer {
            base: ProducerBase::new(ScalarFanInProducer::alloc_id(), &out_tiling),
            names: (0..2).map(tuple_field).collect(),
            inputs,
        };

        producer.release(out_tiling.universal_guard());
        for (i, log) in logs.iter().enumerate() {
            let seen = log.borrow();
            assert!(
                seen.iter().any(|g| g.is_universal()),
                "operand {i} should have been released universally, saw {seen:?}"
            );
        }
    }

    /// Nothing narrower travels: a scalar has no sub-region, so a partial guard
    /// names no operand positions to free — and the operands are still being read.
    #[test]
    fn scalar_fan_in_does_not_forward_a_narrower_release() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let (spy, log) = ReleaseSpy::new(Tile::Scalar(ColumnValue::Ints(vec![1])), tiling.clone());
        let out_tiling = Tiling::Record([(tuple_field(0), tiling.clone())].into_iter().collect());
        let mut producer = ScalarFanInProducer {
            base: ProducerBase::new(ScalarFanInProducer::alloc_id(), &out_tiling),
            names: vec![tuple_field(0)],
            inputs: vec![Box::new(spy)],
        };

        producer.release(out_tiling.empty_guard());
        assert!(
            log.borrow().is_empty(),
            "an empty release names nothing to free, so nothing is forwarded"
        );
    }

    /// A guard between the two extremes is **rejected, not ignored**. A
    /// `ScalarFanIn` re-reads every operand on every pull, so it cannot stop
    /// requesting one released field; silently dropping the guard would leave it
    /// re-emitting that field, which the producer has already promised not to do.
    #[test]
    #[should_panic(expected = "cannot honor the partial release guard")]
    fn scalar_fan_in_rejects_a_partial_record_release() {
        let tiling = Tiling::Scalar(Extent::Base(BaseType::Int));
        let mut inputs: Vec<Box<dyn TileProducer>> = Vec::new();
        for _ in 0..2 {
            let (spy, _log) =
                ReleaseSpy::new(Tile::Scalar(ColumnValue::Ints(vec![1])), tiling.clone());
            inputs.push(Box::new(spy));
        }
        let names: Vec<String> = (0..2).map(tuple_field).collect();
        let out_tiling =
            Tiling::Record(names.iter().map(|n| (n.clone(), tiling.clone())).collect());
        let mut producer = ScalarFanInProducer {
            base: ProducerBase::new(ScalarFanInProducer::alloc_id(), &out_tiling),
            names: names.clone(),
            inputs,
        };

        // Field `_0` released, `_1` still live — neither empty nor universal.
        let partial = TileGuard::Record(
            [
                (names[0].clone(), TileGuard::Scalar(true)),
                (names[1].clone(), TileGuard::Scalar(false)),
            ]
            .into_iter()
            .collect(),
        );
        producer.release(partial);
    }

    // ── FanInProducer: asymmetric per-branch presence ────────────────────────
    //
    // Regression for the per-branch presence-intersection added to
    // `FanInProducer::get_impl` for cyclic mutation loops, where one branch
    // (the body) can have emitted more positions than another (a still-
    // converging `recursive_input`).  Before the intersection step, the
    // output tile carried whichever branch happened to be at index 0 of
    // the inputs vec — fine for branches that always advance in lockstep,
    // wrong as soon as they don't.
    //
    // We construct two `SealedFunction` test tiles over the same domain
    // type but with *different actual positions present* (branch A has
    // positions [0, 1, 2]; branch B has only [0, 1]) and a `FanInProducer`
    // directly over them, then check that the merged output is restricted
    // to the intersection [0, 1].

    /// Two `SealedFunction` inputs with different sets of present positions.
    /// The output should restrict to the intersection of those positions.
    #[test]
    fn fan_in_producer_intersects_branch_presence() {
        let input_tiling = Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::UInt))),
        };
        let tile_a = Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![0, 1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::UInts(vec![10, 11, 12]))),
            // Non-terminal: branch A has emitted [0, 1, 2] but its
            // upstream hasn't yet signaled "no more".
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        };
        let tile_b = Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![0, 1]),
            codomain: Box::new(Tile::Scalar(ColumnValue::UInts(vec![20, 21]))),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        };

        let output_tiling = Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Record(HashMap::from([
                (
                    "a".to_string(),
                    Tiling::Scalar(Extent::Base(BaseType::UInt)),
                ),
                (
                    "b".to_string(),
                    Tiling::Scalar(Extent::Base(BaseType::UInt)),
                ),
            ]))),
        };
        let mut fan_in = FanInProducer {
            base: ProducerBase::new(FanInProducer::alloc_id(), &output_tiling),
            names: vec!["a".to_string(), "b".to_string()],
            inputs: vec![
                Box::new(TestTileProducer::new(tile_a, input_tiling.clone())),
                Box::new(TestTileProducer::new(tile_b, input_tiling)),
            ],
        };

        let result = fan_in.get(fan_in.tiling().universal_guard());
        let Tile::SealedFunction {
            domain, codomain, ..
        } = result
        else {
            panic!("expected SealedFunction output, got {result:?}");
        };
        // Intersection of [0, 1, 2] and [0, 1] is [0, 1].
        let ColumnValue::UInts(domain_vals) = domain else {
            panic!("expected UInts domain, got {domain:?}");
        };
        assert_eq!(
            domain_vals,
            vec![0, 1],
            "output domain should be the intersection of input presences"
        );

        let Tile::Record(field_tiles) = *codomain else {
            panic!("expected Record codomain");
        };
        assert_eq!(
            scalar_tile_to_column_value(field_tiles.get("a").unwrap().clone()),
            ColumnValue::UInts(vec![10, 11]),
            "branch a's codomain should be filtered to positions [0, 1]",
        );
        assert_eq!(
            scalar_tile_to_column_value(field_tiles.get("b").unwrap().clone()),
            ColumnValue::UInts(vec![20, 21]),
            "branch b's codomain should remain [0, 1] (already its full presence)",
        );
    }
}
