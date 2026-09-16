use std::collections::HashMap;

use super::*;
use crate::interpreter::operator_graph::value_at;
use crate::{
    interpreter::{Consumer, Scheduler, forwarding_consumer, shared_consumer, tuple_field},
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// Combines multiple function operators sharing the same domain into a single function
/// operator whose codomain is a record of all their codomains.
///
/// All inputs must be collections over compatible keys.
/// Output fields are named `_0`, `_1`, … matching the input order.
pub struct FanIn {
    /// Output tiling: the ambient levels, with a `Record` where the operands' values sat.
    base: OperatorBase,
    /// Field names in input order, used when producing the output Record tile.
    names: Vec<String>,
    /// The input collections to pair.
    inputs: Vec<Box<dyn TileOperator>>,
    /// The ambient levels the pair sits under.
    depth: usize,
}

/// The number of collection levels `tiling` carries before its values.
pub fn level_count(tiling: &Tiling) -> usize {
    match tiling {
        Tiling::Function { codomain, .. } => 1 + level_count(codomain),
        _ => 0,
    }
}

/// `tiling`'s first `depth` levels, with `inner` beneath them.
fn with_values_at(tiling: &Tiling, depth: usize, inner: Tiling) -> Tiling {
    if depth == 0 {
        return inner;
    }
    let Tiling::Function { domain, codomain } = tiling else {
        unreachable!("the depth was counted off this tiling")
    };
    Tiling::Function {
        domain: domain.clone(),
        codomain: Box::new(with_values_at(codomain, depth - 1, inner)),
    }
}

impl FanIn {
    /// Create a `FanIn` pairing its operands over their first `depth` levels.
    ///
    /// `depth` is the **ambient iteration** — how many levels the operands were applied
    /// over. It is the caller's to state, not something the operands say: two arms that
    /// agree below the ambient (two projections of one grouped row, say) look pairable all
    /// the way down, and two that differ there are the collection-valued component case.
    pub fn new_at(names: Vec<String>, ops: Vec<Box<dyn TileOperator>>, depth: usize) -> Self {
        assert!(!ops.is_empty(), "FanIn requires at least one input");
        assert!(depth > 0, "FanIn pairs under at least one ambient level");
        // The operands agree on the ambient levels — they were applied over them — and may
        // differ below. Their runtime *presence* may still differ (one branch has emitted
        // 0..3 while another has 0..2), which `FanInProducer::get_impl` intersects.
        for op in ops.iter() {
            for d in 0..depth {
                let (Tiling::Function { domain, .. }, Tiling::Function { domain: other, .. }) =
                    (ops[0].tiling().values_at(d), op.tiling().values_at(d))
                else {
                    panic!(
                        "FanIn pairs collections over {depth} ambient level(s), got {} and {}",
                        ops[0].tiling(),
                        op.tiling()
                    )
                };
                assert_eq!(
                    domain, other,
                    "FanIn's operands share the ambient iteration, so they agree on its keys \
                     at every level"
                );
            }
        }
        let record = Tiling::Record(
            names
                .iter()
                .zip(ops.iter())
                .map(|(name, op)| (name.clone(), op.tiling().values_at(depth).clone()))
                .collect(),
        );
        let tiling = with_values_at(ops[0].tiling(), depth, record);
        Self {
            base: OperatorBase::new(tiling),
            names,
            inputs: ops,
            depth,
        }
    }
}

pub fn fan_in_at(inputs: Vec<Box<dyn TileOperator>>, depth: usize) -> Box<dyn TileOperator> {
    if inputs.iter().all(|op| op.tiling().is_scalar()) {
        return Box::new(ScalarFanIn::new(inputs));
    }
    let names = (0..inputs.len()).map(tuple_field).collect();
    Box::new(FanIn::new_at(names, inputs, depth))
}

/// Named-field variant of [`fan_in_at`]: like [`fan_in_at`] but uses caller-supplied
/// field names instead of the synthetic `_0`, `_1`, … names.
pub fn fan_in_named_at(
    inputs: Vec<(String, Box<dyn TileOperator>)>,
    depth: usize,
) -> Box<dyn TileOperator> {
    if inputs.iter().all(|(_, op)| op.tiling().is_scalar()) {
        return Box::new(ScalarFanIn::new_named(inputs));
    }
    let (names, ops) = inputs.into_iter().unzip();
    Box::new(FanIn::new_at(names, ops, depth))
}

impl TileOperator for FanIn {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        for (i, input) in self.inputs.iter().enumerate() {
            visit(value_at(i, &**input));
        }
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let shared = shared_consumer(consumer);
        Box::new(FanInProducer {
            depth: self.depth,
            base: ProducerBase::new(FanInProducer::alloc_id(), self.tiling()),
            names: self.names.clone(),
            inputs: self
                .inputs
                .iter_mut()
                .map(|i| {
                    i.subscribe(
                        i.tiling().universal_guard(),
                        forwarding_consumer(&shared),
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
    /// The ambient levels the pair sits under ([`FanIn`]).
    depth: usize,
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
            Tile::Function { .. } => {
                // All inputs are Function tiles, but they may differ in
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
                    let Tile::Function {
                        domain,
                        domain_predicate,
                        ..
                    } = t
                    else {
                        panic!("FanIn: cannot mix collection and non-collection tiles")
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
                let mut skeleton: Option<Tile> = None;
                let mut codomains: Vec<Tile> = Vec::with_capacity(tiles.len());
                for mut filtered in tiles.into_iter() {
                    let Tile::Function { domain, .. } = &filtered else {
                        unreachable!()
                    };
                    let to_remove = Predicate::from_column_value(domain).minus(&presence);
                    if to_remove.as_bool() != Some(false) {
                        filtered
                            .remove_guarded(TileGuard::Function(FunctionGuard::Domain(to_remove)));
                    }
                    filtered.compact();
                    // Lift the values out, leaving the chain of keys behind: what stays is
                    // the output's own shape, and every input has to agree on it.
                    codomains.push(std::mem::replace(
                        filtered.values_at_mut(self.depth),
                        Tile::Record(HashMap::new()),
                    ));
                    debug_assert!(
                        skeleton.as_ref().is_none_or(|s: &Tile| {
                            s.key_levels()[..self.depth] == filtered.key_levels()[..self.depth]
                        }),
                        "FanIn: inputs disagree on the levels they are paired over"
                    );
                    skeleton.get_or_insert(filtered);
                }

                let names = &self.names;
                let codomain_record = Tile::Record(
                    codomains
                        .into_iter()
                        .enumerate()
                        .map(move |(i, cv)| (names[i].clone(), cv))
                        .collect(),
                );
                let mut out = skeleton.expect("FanIn has at least one input");
                *out.values_at_mut(self.depth) = codomain_record;
                let Tile::Function {
                    domain_predicate, ..
                } = &mut out
                else {
                    unreachable!("the skeleton is one of the collection inputs")
                };
                *domain_predicate = intersect_pred;
                out
            }
            other => panic!("FanIn: every input must be a collection tile, got {other:?}"),
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
        Self {
            base: OperatorBase::new(tiling),
            names,
            inputs,
        }
    }
}

impl TileOperator for ScalarFanIn {
    impl_operator_base!();

    fn visit_inputs(&self, visit: &mut dyn FnMut(InputEdgeSpec<'_>)) {
        for (i, input) in self.inputs.iter().enumerate() {
            visit(value_at(i, &**input));
        }
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let shared = shared_consumer(consumer);
        Box::new(ScalarFanInProducer {
            base: ProducerBase::new(ScalarFanInProducer::alloc_id(), self.tiling()),
            names: self.names.clone(),
            inputs: self
                .inputs
                .iter_mut()
                .map(|i| {
                    i.subscribe(
                        i.tiling().universal_guard(),
                        forwarding_consumer(&shared),
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
    use bit_set::BitSet;

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
    // We construct two `Function` test tiles over the same domain
    // type but with *different actual positions present* (branch A has
    // positions [0, 1, 2]; branch B has only [0, 1]) and a `FanInProducer`
    // directly over them, then check that the merged output is restricted
    // to the intersection [0, 1].

    /// Two `Function` inputs with different sets of present positions.
    /// The output should restrict to the intersection of those positions.
    #[test]
    fn fan_in_producer_intersects_branch_presence() {
        let input_tiling = Tiling::function(
            Extent::Base(BaseType::UInt),
            Tiling::Scalar(Extent::Base(BaseType::UInt)),
        );
        let tile_a = Tile::function(
            ColumnValue::UInts(vec![0, 1, 2]),
            Box::new(Tile::Scalar(ColumnValue::UInts(vec![10, 11, 12]))),
            // Non-terminal: branch A has emitted [0, 1, 2] but its
            // upstream hasn't yet signaled "no more".
            Predicate::False,
            BitSet::new(),
        );
        let tile_b = Tile::function(
            ColumnValue::UInts(vec![0, 1]),
            Box::new(Tile::Scalar(ColumnValue::UInts(vec![20, 21]))),
            Predicate::False,
            BitSet::new(),
        );

        let output_tiling = Tiling::function(
            Extent::Base(BaseType::UInt),
            Tiling::Record(HashMap::from([
                (
                    "a".to_string(),
                    Tiling::Scalar(Extent::Base(BaseType::UInt)),
                ),
                (
                    "b".to_string(),
                    Tiling::Scalar(Extent::Base(BaseType::UInt)),
                ),
            ])),
        );
        let mut fan_in = FanInProducer {
            depth: 1,
            base: ProducerBase::new(FanInProducer::alloc_id(), &output_tiling),
            names: vec!["a".to_string(), "b".to_string()],
            inputs: vec![
                Box::new(TestTileProducer::new(tile_a, input_tiling.clone())),
                Box::new(TestTileProducer::new(tile_b, input_tiling)),
            ],
        };

        let result = fan_in.get(fan_in.tiling().universal_guard());
        let Tile::Function {
            domain, codomain, ..
        } = result
        else {
            panic!("expected Function output, got {result:?}");
        };
        // Intersection of [0, 1, 2] and [0, 1] is [0, 1].
        let ColumnValue::UInts(domain_vals) = domain else {
            panic!("expected UInts keys, got {domain:?}");
        };
        assert_eq!(
            domain_vals,
            vec![0, 1],
            "output keys should be the intersection of input presences"
        );

        let Tile::Record(field_tiles) = *codomain else {
            panic!("expected Record values");
        };
        assert_eq!(
            scalar_tile_to_column_value(field_tiles.get("a").unwrap().clone()),
            ColumnValue::UInts(vec![10, 11]),
            "branch a's values should be filtered to positions [0, 1]",
        );
        assert_eq!(
            scalar_tile_to_column_value(field_tiles.get("b").unwrap().clone()),
            ColumnValue::UInts(vec![20, 21]),
            "branch b's values should remain [0, 1] (already its full presence)",
        );
    }
}
