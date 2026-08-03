use bit_set::BitSet;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use super::*;
use crate::{
    interpreter::{
        BaseType, ColumnValue, Consumer, DataSourceDomainExtentImpl, Extent, Scheduler, Value,
    },
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// Applies a function operator element-wise over a function input, N curried levels deep.
///
/// `input` must be a `SealedFunction` or `CurriedFunction` tile, with the appropriate level
/// of nesting.
pub struct MapResult {
    /// Output tiling matches `input` tiling, transforming the codomain according to `function`.
    tiling: Tiling,
    /// The sealed-function input to iterate over.
    input: Box<dyn TileOperator>,
    /// The function to apply to each element.
    function: Box<dyn TileOperator>,
}

impl MapResult {
    /// Create a new `Map` operator applying `function` to each element of `input`.
    ///
    /// The output `tiling` and `extent` are derived from the inputs: the codomain
    /// of `function` becomes the output value extent, threaded through the domain
    /// (if any) of `input`.
    pub fn new(input: Box<dyn TileOperator>, function: Box<dyn TileOperator>) -> Self {
        let function_tiling = function.tiling();

        // Special case: when function is CurriedFunction(B, C, D), we need to produce a CurriedFunction output.
        // The input domain becomes the output domain1, and the function's domain2/codomain become output domain2/codomain.
        if let Tiling::CurriedFunction {
            domain1: fn_domain1,
            domain2: fn_domain2,
            codomain: fn_codomain,
        } = function_tiling
        {
            let input_tiling = input.tiling();
            let input_domain = match input_tiling {
                Tiling::SealedFunction {
                    domain: d,
                    codomain: c,
                    ..
                } => {
                    // Verify the codomain matches the function's domain1
                    assert_eq!(
                        c.extent(),
                        *fn_domain1,
                        "Input codomain extent must match function domain1"
                    );
                    d.clone()
                }
                Tiling::CurriedFunction {
                    domain1: d,
                    codomain: c,
                    ..
                } => {
                    // Verify the codomain matches the function's domain1
                    assert_eq!(
                        c, fn_domain1,
                        "Input codomain extent must match function domain1"
                    );
                    d.clone()
                }
                _ => panic!(
                    "MapResult with CurriedFunction function requires SealedFunction or CurriedFunction input, got {:?}",
                    input_tiling
                ),
            };
            // Output is CurriedFunction(input_domain, fn_domain2, fn_codomain)
            let tiling = Tiling::CurriedFunction {
                domain1: input_domain,
                domain2: fn_domain2.clone(),
                codomain: fn_codomain.clone(),
            };
            return Self {
                tiling,
                input,
                function,
            };
        }

        // Standard logic for non-CurriedFunction functions
        let function_domain_extent = function_tiling.domain_extent().unwrap_or_else(|| {
            panic!("Map function had non-function tiling {:?}", function_tiling)
        });
        let output_tiling = function_tiling.codomain().unwrap_or_else(|| {
            panic!("Map function had non-function tiling {:?}", function_tiling)
        });
        let input_tiling = input.tiling();
        let tiling = change_tiling_result(input.tiling(), move |codomain_extent| {
            assert_eq!(
                function_domain_extent, *codomain_extent,
                "Cannot apply {} to {}",
                function_tiling, input_tiling
            );
            output_tiling
        });
        Self {
            tiling,
            input,
            function,
        }
    }
}

impl TileOperator for MapResult {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("fn", self.function.inspect(opts))
            .child("input", self.input.inspect(opts))
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
        let function_producer = self.function.subscribe(
            self.function.tiling().universal_guard(),
            Box::new(consumer_wrapper.clone()),
            scheduler,
        );
        let input_producer = self.input.subscribe(
            self.input.tiling().universal_guard(),
            Box::new(consumer_wrapper.clone()),
            scheduler,
        );
        Box::new(MapResultProducer {
            base: ProducerBase::new(MapResultProducer::alloc_id(), &self.tiling),
            input: input_producer,
            function: function_producer,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        if let Some(mut input_corr) = self.input.result_correlation()
            && let Some(transform) = self.function.result_correlation()
        {
            input_corr.extend(transform);
            return Some(input_corr);
        }
        None
    }
}

struct MapResultProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    function: Box<dyn TileProducer>,
}

impl TileProducer for MapResultProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("fn", self.function.inspect(opts))
            .child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let f_tiling = self.function.tiling().clone();
        assert!(
            f_tiling.is_function(),
            "MapResult expected function tiling, Got {f_tiling:?}"
        );
        let f_extent = f_tiling.extent();
        let (f_domain_extent, f_codomain_extent) = f_extent.split_function().unwrap();
        let i_tiling = self.input.tiling().clone();
        let input_guard = match projection_guard {
            TileGuard::Function(FunctionGuard::Domain(p)) => {
                TileGuard::Function(FunctionGuard::Domain(p))
            }
            _ => i_tiling.universal_guard(),
        };

        let input_tile = self.input.get(input_guard);
        let function_tile = self.function.get(self.function.tiling().universal_guard());

        // When the function is a CurriedFunction, we need special-case handling.
        if let Tile::CurriedFunction {
            domain1: f_domain,
            offsets,
            domain2: f_domain2,
            codomain: f_codomain,
            domain_predicate: f_domain_predicate,
            ..
        } = function_tile
        {
            let Tile::SealedFunction {
                domain,
                codomain: input_codomain,
                domain_predicate,
                ..
            } = input_tile
            else {
                panic!("Expected SealedFunction");
            };

            // Extract codomain values. For a Scalar codomain, get the ColumnValue directly.
            // For other types, need to handle appropriately.
            let codomain_values = match *input_codomain {
                Tile::Scalar(ref cv) => cv.clone(),
                _ => panic!("MapResult with CurriedFunction only supports Scalar codomains"),
            };

            // Get the correct extents from the CurriedFunction tiling
            // For CurriedFunction(A, B, C), we need B and C extents for domain2 and codomain
            let (f_domain2_extent, f_codomain_extent) = if let Tiling::CurriedFunction {
                domain2: d2_extent,
                codomain: c_extent,
                ..
            } = &f_tiling
            {
                (d2_extent.clone(), c_extent.clone())
            } else {
                panic!("Expected CurriedFunction tiling for CurriedFunction tile")
            };

            // Sort domain to ensure consistent ordering
            let mut sort_indices: Vec<usize> = (0..domain.len()).collect();
            sort_indices.sort_by(|&a, &b| {
                domain
                    .index_at(a)
                    .partial_cmp(&domain.index_at(b))
                    .expect("Cannot compare domain values")
            });

            // Reorder domain and codomain by sort indices
            let sorted_domain =
                domain.select_indices(sort_indices.iter().cloned(), sort_indices.len());
            let sorted_codomain_values =
                codomain_values.select_indices(sort_indices.iter().cloned(), sort_indices.len());

            // For each element in sorted domain, find the corresponding codomain value,
            // then look up that codomain value in f_domain to get f_domain2 and f_codomain values.
            // TODO this is doing filtering implicitly here, but we should do it in a separate step.
            // in order to do this we need to be able to construct a filter based on the presence of domain
            // elements in another function, and we don't have that capability yet.
            let domain_extent = i_tiling.domain_extent().unwrap();
            let mut new_domain = ColumnValue::from_values(Vec::new(), &domain_extent);
            let mut new_offsets =
                ColumnValue::from_values(Vec::new(), &Extent::Base(BaseType::UInt));
            let mut new_domain2 = ColumnValue::from_values(Vec::new(), &f_domain2_extent);
            let mut new_codomain = ColumnValue::from_values(Vec::new(), &f_codomain_extent);
            // Collects `input`` domain values whose CurriedFunction mapping is incomplete.
            // More precisely, this is the set of domain values of `input` such that the corresponding
            // codomain value does not satisfy the the domain_predicate of `function`.
            let mut incomplete_domain = ColumnValue::from_values(Vec::new(), &domain_extent);

            // Build an index from f_domain values to their first and last indices.
            // This avoids O(n*m) lookup by allowing O(1) range retrieval per value.
            let mut f_domain_index: HashMap<Value, (usize, usize)> = HashMap::new();
            for f_idx in 0..f_domain.len() {
                let val = f_domain.index_at(f_idx);
                f_domain_index
                    .entry(val.clone())
                    .and_modify(|(_, last)| *last = f_idx)
                    .or_insert((f_idx, f_idx));
            }

            let mut current_offset = 0usize;
            for i in 0..sorted_domain.len() {
                let domain_value = sorted_domain.index_at(i);
                let codomain_value = sorted_codomain_values.index_at(i);

                // A domain value maps to an incomplete value when the domain_predicate of the
                // `function` is false for the corresponding input codomain value.
                if !f_domain_predicate.contains(&codomain_value) {
                    incomplete_domain.append(ColumnValue::from_values(
                        vec![domain_value.clone()],
                        &domain_extent,
                    ));
                }

                // Look up index range for this codomain_value in O(1) time.
                if let Some(&(first, last)) = f_domain_index.get(&codomain_value) {
                    // Record this domain element and its starting offset
                    new_domain.append(ColumnValue::from_values(vec![domain_value], &domain_extent));
                    new_offsets.append(ColumnValue::from_values(
                        vec![Value::UInt(current_offset)],
                        &Extent::Base(BaseType::UInt),
                    ));

                    // Collect f_domain2 and f_codomain elements for this codomain value
                    for f_idx in first..=last {
                        // For each match in f_domain, get the corresponding group from offsets
                        let group_start = offsets.index_at(f_idx).as_uint();
                        let group_end = if f_idx + 1 < f_domain.len() {
                            offsets.index_at(f_idx + 1).as_uint()
                        } else {
                            f_domain2.len()
                        };

                        // Append the group's domain2 and codomain values
                        for group_idx in group_start..group_end {
                            new_domain2.append(ColumnValue::from_values(
                                vec![f_domain2.index_at(group_idx)],
                                &f_domain2_extent,
                            ));
                            new_codomain.append(ColumnValue::from_values(
                                vec![f_codomain.index_at(group_idx)],
                                &f_codomain_extent,
                            ));
                            current_offset += 1;
                        }
                    }
                }
            }

            // The output domain_predicate is the input's predicate minus the input domain values
            // for which the CurriedFunction's mapping is not yet complete.
            // We should exlude the obsolete portion of the domain from this logic since we don't
            // have sufficient info to reason about that region.
            let domain_obsolete = match self.input.obsolete_guard() {
                g if g.is_universal() => Predicate::True,
                TileGuard::Function(FunctionGuard::Domain(p)) => p.clone(),
                _ => Predicate::False,
            };
            let incomplete_predicate =
                Predicate::from_column_value(&incomplete_domain).minus(&domain_obsolete);
            let output_domain_predicate = domain_predicate.minus(&incomplete_predicate);
            // Build new CurriedFunction with filtered domain and transformed codomain
            return Tile::CurriedFunction {
                domain1: new_domain,
                offsets: new_offsets,
                domain2: new_domain2,
                codomain: new_codomain,
                domain_predicate: output_domain_predicate,
                deleted: BitSet::new(),
            };
        }

        // Standard logic for non-CurriedFunction outputs
        process_tile_result(self.tiling(), input_tile, move |codomain| {
            apply_function_tile(function_tile, codomain, f_domain_extent, f_codomain_extent)
        })
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // TODO once we have guards that express codomain predicates, handle them here
        // A guard is shaped by the tiling it is handed to, so the input's is built
        // from the input's tiling — never from the function's, whose tiling is
        // unrelated (a function tiling, against the input's stream).
        let upstream_guard = match obsolete_guard {
            g if g.is_empty() => self.input.tiling().empty_guard(),
            g if g.is_universal() => self.input.tiling().universal_guard(),
            TileGuard::Function(FunctionGuard::Domain(p)) => {
                TileGuard::Function(FunctionGuard::Domain(p))
            }
            TileGuard::Function(FunctionGuard::Codomain(g)) => {
                TileGuard::Function(FunctionGuard::Codomain(g))
            }
            g => todo!("Unimplemented guard in MapResultProducer: {g:?}"),
        };
        let done = upstream_guard.is_universal();
        self.input.release(upstream_guard);
        // The **function** is re-read on every pull, so it can only be released
        // once there will be no next pull — which is what a universal release from
        // the consumer says. Releasing it on a narrower guard would leave the next
        // pull mapping over an emptied function; never releasing it strands whatever
        // produces it, and a function operand is not always a small `Constant` (a
        // UDF's materialized table lives here too).
        if done {
            self.function
                .release(self.function.tiling().universal_guard());
        }
    }
}

/// Takes a function input and returns a function with the same structure
/// but with a constant codomain swapped or zipped in, as determined by the [`MapResultToConstMode`]
/// param.
///
/// `input` must be a `SealedFunction` or `CurriedFunction` tile; `constant` must be a Scalar.
pub struct MapResultToConst {
    /// Output tiling matches `input` tiling, transforming the codomain to `constant`.
    tiling: Tiling,
    /// The sealed-function input to iterate over.
    input: Box<dyn TileOperator>,
    /// The constant to apply to each element.
    constant: Box<dyn TileOperator>,
    /// Whether to zip with the constant instead of replacing with the constant.
    mode: MapResultToConstMode,
}

/// The type fof MapResultToConst operation to perform
#[derive(Debug, Clone, Copy)]
pub enum MapResultToConstMode {
    /// Replace the codomain with the constant
    Replace,
    /// Replace the codomain x with (constant, x)
    FanInLeft,
    /// Replace the codomain x with (x, constant)
    FanInRight,
}

impl MapResultToConst {
    /// Create a new `MapResultToConst` operator that maps any codomain to the given constant.
    pub fn new(
        input: Box<dyn TileOperator>,
        constant: Box<dyn TileOperator>,
        mode: MapResultToConstMode,
    ) -> Self {
        let tiling = match mode {
            MapResultToConstMode::Replace => {
                change_tiling_result(input.tiling(), |_| constant.tiling().clone())
            }
            MapResultToConstMode::FanInLeft => change_tiling_result(input.tiling(), |e| {
                Tiling::tuple(&[constant.tiling().clone(), Tiling::Scalar(e.clone())])
            }),
            MapResultToConstMode::FanInRight => change_tiling_result(input.tiling(), |e| {
                Tiling::tuple(&[Tiling::Scalar(e.clone()), constant.tiling().clone()])
            }),
        };
        Self {
            tiling,
            input,
            constant,
            mode,
        }
    }
}

impl TileOperator for MapResultToConst {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
            .child("constant", self.constant.inspect(opts))
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
        let constant_producer = self.constant.subscribe(
            self.constant.tiling().universal_guard(),
            Box::new(consumer_wrapper.clone()),
            scheduler,
        );
        let input_producer = self.input.subscribe(
            self.input.tiling().universal_guard(),
            Box::new(consumer_wrapper.clone()),
            scheduler,
        );
        Box::new(MapResultToConstProducer {
            base: ProducerBase::new(MapResultToConstProducer::alloc_id(), &self.tiling),
            input: input_producer,
            constant: constant_producer,
            mode: self.mode,
        })
    }
}

struct MapResultToConstProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    constant: Box<dyn TileProducer>,
    mode: MapResultToConstMode,
}

impl TileProducer for MapResultToConstProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
            .child("constant", self.constant.inspect(opts))
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let c_tiling = self.constant.tiling();
        assert!(
            c_tiling.is_scalar(),
            "MapResultToConst expected scalar tiling, Got {c_tiling:?}"
        );
        let i_tiling = self.input.tiling().clone();
        let input_guard = match projection_guard {
            TileGuard::Function(FunctionGuard::Domain(p)) => {
                TileGuard::Function(FunctionGuard::Domain(p))
            }
            _ => i_tiling.universal_guard(),
        };
        let input_tile = self.input.get(input_guard);
        // **Laziness — do not evaluate an off-path arm.** In the scalar value-`Case`
        // C-form a false first-match gate empties this arm's `Units(1)` driver — the
        // `Restrict` marks the driver row *deleted* rather than dropping it. When
        // every driver row is deleted, the arm contributes no live rows, so the
        // constant's value is never observed. Crucially we must not *pull* it: the
        // arm's value may be a partial expression (`//`, `%`, an index) the gate
        // exists to guard, and pulling it would evaluate e.g. `x // 0` and panic.
        // Return a terminal-empty tile carrying the input's decidedness, so the
        // union / `final_or_default` sees this arm resolve to nothing rather than
        // waiting forever. The data-collection fan-out is lazy the same way (an
        // emptied restrict is never iterated); this brings the scalar form in line.
        if let Tile::SealedFunction {
            domain,
            deleted,
            domain_predicate,
            ..
        } = &input_tile
            && (0..domain.len()).all(|i| deleted.contains(i))
        {
            let mut out = self.tiling().empty_tile();
            if let Tile::SealedFunction {
                domain_predicate: out_pred,
                ..
            } = &mut out
            {
                // Carry the input's decidedness so a decided (false-gate) arm reads
                // terminal-empty — the union / `final_or_default` sees it resolve to
                // nothing rather than waiting forever.
                *out_pred = domain_predicate.clone();
            } else {
                // MapResultToConst's output is always a function tiling; a
                // non-`SealedFunction` here would silently drop the decidedness
                // carry-over and leave a decided arm reading non-terminal forever.
                unreachable!("MapResultToConst output tiling is always SealedFunction");
            }
            return out;
        }
        let constant_tile = {
            // The broadcast value must be fully known before we can replicate it
            // across the input's domain: `repeat` fabricates nothing, it copies a
            // single present value. A constant that is still absent (e.g. a scalar
            // read from a sibling induction loop that has not yet converged) yields
            // an empty (non-terminal) output — the consumer re-pulls once it lands,
            // rather than us inventing a value for the unknown positions.
            //
            // This is one half of a single invariant — "never fabricate a position
            // from a not-yet-converged sibling read." The other half is the
            // co-presence truncate in `binop::zip_arithmetic`/`zip_concat`: a binop
            // over a lagging operand combines only the common prefix instead of
            // returning the longer side's tail. Keep the two in step.
            let ct = self.constant.get(c_tiling.universal_guard());
            if !ct.is_terminal() {
                return self.tiling().empty_tile();
            }
            ct
        };

        let mode = self.mode;
        process_tile_result(self.tiling(), input_tile, move |codomain| {
            let const_tile = repeat_tile(constant_tile, codomain.len());
            let result_tile = match mode {
                MapResultToConstMode::Replace => const_tile,
                MapResultToConstMode::FanInLeft => {
                    Tile::tuple(vec![const_tile, Tile::Scalar(codomain)])
                }
                MapResultToConstMode::FanInRight => {
                    Tile::tuple(vec![Tile::Scalar(codomain), const_tile])
                }
            };
            scalar_tile_to_column_value(result_tile)
        })
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // TODO once we have guards that express codomain predicates, handle them here
        self.input.release(obsolete_guard);
    }
}
/// Produces a `SealedFunction` tile that maps each domain element of a data
/// source to its corresponding output value.
///
/// Unlike [`IterateExtent`], which produces an identity function (domain→domain),
/// `MapResultWithSource` calls [`DataSourceDomainExtentImpl::get`] for each domain key to
/// look up the actual output value.  The result is
/// `SealedFunction { domain: keys, codomain: Scalar(output_values) }`.
///
/// Notification at subscription time: if the source already has data when
/// `subscribe` is called, the consumer is notified immediately.
pub struct MapResultWithSource {
    input: Box<dyn TileOperator>,
    /// The data source providing both domain keys and value lookup.
    source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    /// Output tiling: `SealedFunction { domain: DataSourceDomain, codomain: Scalar(output_value_extent) }`.
    tiling: Tiling,
}

impl MapResultWithSource {
    /// Create a new `MapResultWithSource` wrapping `source`.
    ///
    /// The output tiling is derived from the source's
    /// [`output_value_extent`](DataSourceDomainExtentImpl::output_value_extent).
    pub fn new(
        source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
        input: Box<dyn TileOperator>,
    ) -> Self {
        let source_domain_extent = Extent::DataSourceDomain(source.clone());
        let output_extent = source.borrow().output_value_extent();
        let tiling = change_tiling_result(input.tiling(), move |codomain_extent| {
            assert_eq!(source_domain_extent, *codomain_extent);
            Tiling::Scalar(output_extent)
        });
        Self {
            input,
            source: source.clone(),
            tiling,
        }
    }
}

impl TileOperator for MapResultWithSource {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(MapResultWithSourceProducer::new(
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler),
            self.source.clone(),
            self.tiling().clone(),
            self.input
                .result_correlation()
                .expect("MapResultWithSource requires input result_correlation"),
        ))
    }
}

/// Producer for [`MapNSource`]: maps each domain key to its output value on `get`.
struct MapResultWithSourceProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    /// The data source used for both domain enumeration and value lookup.
    source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    /// A correlation between the result values and some piece of the domain of the input tile.
    /// We need this in order to translate domain obsolete guards into releases of the underlying
    /// source.
    result_correlation: Vec<TilePathStep>,
}

impl MapResultWithSourceProducer {
    fn new(
        input: Box<dyn TileProducer>,
        source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
        tiling: Tiling,
        result_correlation: Vec<TilePathStep>,
    ) -> Self {
        let result = Self {
            base: ProducerBase::new(MapResultWithSourceProducer::alloc_id(), &tiling),
            input,
            source,
            result_correlation,
        };
        // Register this producer with the source by calling release with a false predicate.
        // This way the source knows about all producers that read it before execution starts.
        // This prevents sources from deleting data that a producer it doesn't know about yet might
        // need.
        result
            .source
            .borrow_mut()
            .release(&result.name(), Predicate::False);
        result
    }
}

impl TileProducer for MapResultWithSourceProducer {
    impl_producer_base!();

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new(self.name())
            .annotate(self.source.borrow().get_id().to_string())
            .with_tiling(self.tiling().to_string())
            .child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        let source = self.source.borrow();
        process_tile_result(self.tiling(), input_tile, move |codomain| {
            source.get(codomain)
        })
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        match &obsolete_guard {
            TileGuard::Function(FunctionGuard::Domain(pred)) => {
                let extracted_pred = extract_predicate(pred, &self.result_correlation).clone();
                self.source
                    .borrow_mut()
                    .release(&self.name(), extracted_pred);
            }
            TileGuard::Function(FunctionGuard::Codomain(g))
                if matches!(**g, TileGuard::Function(FunctionGuard::Domain(_))) =>
            {
                if let TileGuard::Function(FunctionGuard::Domain(pred)) = &**g {
                    assert_eq!(
                        self.result_correlation.first(),
                        Some(&TilePathStep::Codomain)
                    );
                    let extracted_pred =
                        extract_predicate(pred, &self.result_correlation[1..]).clone();
                    self.source
                        .borrow_mut()
                        .release(&self.name(), extracted_pred);
                }
            }
            g if g.is_universal() => {
                self.source
                    .borrow_mut()
                    .release(&self.name(), Predicate::True);
            }
            g if g.is_empty() => {}
            _ => panic!(
                "MapResultWithSourceProducer::release expected Domain or Universal guard, got {obsolete_guard:?}"
            ),
        }
        self.input.release(obsolete_guard);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::tile_operators::test_helpers::{ReleaseSpy, TestTileProducer};
    use crate::interpreter::{BaseType, ColumnValue, Extent, Value};

    /// Build a `MapResultProducer` whose `function` operand records its releases.
    fn map_result_with_function_spy() -> (MapResultProducer, Rc<RefCell<Vec<TileGuard>>>, Tiling) {
        let in_tiling = Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let fn_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };
        let (fn_spy, released) = ReleaseSpy::new(
            Tile::CurriedFunction {
                domain1: ColumnValue::UInts(vec![0]),
                offsets: ColumnValue::UInts(vec![0]),
                domain2: ColumnValue::UInts(vec![1]),
                codomain: ColumnValue::UInts(vec![1]),
                domain_predicate: Predicate::True,
                deleted: BitSet::new(),
            },
            fn_tiling,
        );
        let input = TestTileProducer::new(
            Tile::SealedFunction {
                domain: ColumnValue::from_uints(vec![0]),
                codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![1]))),
                domain_predicate: Predicate::True,
                deleted: BitSet::new(),
            },
            in_tiling.clone(),
        );
        let producer = MapResultProducer {
            base: ProducerBase::new(MapResultProducer::alloc_id(), &in_tiling),
            input: Box::new(input),
            function: Box::new(fn_spy),
        };
        (producer, released, in_tiling)
    }

    /// The function operand is re-read on **every** pull, so it can only be
    /// released once there will be no next pull — which is what a universal release
    /// from the consumer says. Never releasing it strands whatever produces it, and
    /// a function operand is not always a small `Constant`.
    #[test]
    fn map_result_releases_its_function_when_the_consumer_is_done() {
        let (mut producer, released, tiling) = map_result_with_function_spy();
        producer.release(tiling.universal_guard());
        assert!(
            released.borrow().iter().any(|g| g.is_universal()),
            "a universal release means no further pull, so the function is free: {:?}",
            released.borrow()
        );
    }

    /// A narrower release must *not* reach the function: the next pull still needs
    /// it, and an emptied function would leave that pull mapping over nothing.
    #[test]
    fn map_result_keeps_its_function_for_a_narrower_release() {
        let (mut producer, released, _) = map_result_with_function_spy();
        producer.release(TileGuard::Function(FunctionGuard::Domain(
            Predicate::LessThanEq(Value::UInt(0)),
        )));
        assert!(
            released.borrow().is_empty(),
            "the function is still being read: {:?}",
            released.borrow()
        );
    }

    #[test]
    fn map_result_producer_curried_function() {
        // Test MapResultProducer directly with unsorted domain input
        // This tests the actual MapResultProducer.get_impl implementation

        // Create a CurriedFunction tile
        let curried_fn_tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![0, 1]),
            offsets: ColumnValue::UInts(vec![0, 2]),
            domain2: ColumnValue::UInts(vec![10, 20, 30]),
            codomain: ColumnValue::UInts(vec![100, 200, 300]),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };

        let function_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };

        // Create a SealedFunction tile with unsorted domain
        let sealed_fn_tile = Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![2, 0, 1]),
            codomain: Box::new(Tile::Scalar(ColumnValue::UInts(vec![1, 0, 1]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };

        let input_tiling = Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::UInt))),
        };

        // Create test producers
        let function_producer = TestTileProducer::new(curried_fn_tile, function_tiling);
        let input_producer = TestTileProducer::new(sealed_fn_tile, input_tiling);

        // Create MapResultProducer and test it
        let output_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };

        let mut map_result = MapResultProducer {
            base: ProducerBase::new(MapResultProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
            function: Box::new(function_producer),
        };

        // Get the result from MapResultProducer
        let result = map_result.get(map_result.tiling().universal_guard());

        // Verify the result
        match result {
            Tile::CurriedFunction {
                domain1,
                offsets,
                domain2,
                codomain,
                ..
            } => {
                // After sorting unsorted input {2, 0, 1} with codomain {1, 0, 1},
                // we get sorted {0, 1, 2} with codomain {0, 1, 1}
                assert_eq!(domain1.len(), 3, "domain1 should have 3 elements");
                assert_eq!(offsets.len(), 3, "offsets should have 3 elements");
                assert_eq!(domain2.len(), 4, "domain2 should have 4 elements");
                assert_eq!(codomain.len(), 4, "codomain should have 4 elements");

                // Verify domain1 is sorted: [0, 1, 2]
                if let ColumnValue::UInts(d1) = domain1 {
                    assert_eq!(d1, vec![0, 1, 2], "domain1 should be sorted");
                } else {
                    panic!("domain1 should be UInts");
                }

                // Verify offsets: [0, 2, 3]
                if let ColumnValue::UInts(offs) = offsets {
                    assert_eq!(offs, vec![0, 2, 3], "offsets should be [0, 2, 3]");
                } else {
                    panic!("offsets should be UInts");
                }

                // Verify domain2: [10, 20, 30, 30]
                if let ColumnValue::UInts(d2) = domain2 {
                    assert_eq!(
                        d2,
                        vec![10, 20, 30, 30],
                        "domain2 should be [10, 20, 30, 30]"
                    );
                } else {
                    panic!("domain2 should be UInts");
                }

                // Verify codomain: [100, 200, 300, 300]
                if let ColumnValue::UInts(cod) = codomain {
                    assert_eq!(
                        cod,
                        vec![100, 200, 300, 300],
                        "codomain should be [100, 200, 300, 300]"
                    );
                } else {
                    panic!("codomain should be UInts");
                }
            }
            _ => panic!("Expected CurriedFunction result"),
        }
    }

    /// Verifies that the output `domain_predicate` of `MapResultProducer` (CurriedFunction
    /// branch) is derived correctly from the input predicate.
    ///
    /// Setup:
    ///   `input`: SealedFunction: domain=[0,1,2,3], codomain=[0,1,2,3], domain_predicate=True
    ///   `function`: CurriedFunction:
    ///     domain1=[0, 1]       –- no info for 2 and 3
    ///     domain_predicate = Intervals covering only 0
    ///
    /// Expected output domain_predicate:
    ///   Only 0 is true for `function`'s domain_predicate, so only the preimage of 0 in
    ///   `input` (i.e. {0}), should be true in the output domain_predicate.
    #[test]
    fn map_result_producer_curried_function_domain_predicate() {
        let f_pred = Predicate::from_column_value(&ColumnValue::UInts(vec![0]));
        let curried_fn_tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![0, 1]),
            offsets: ColumnValue::UInts(vec![0, 1]),
            domain2: ColumnValue::UInts(vec![10, 20]),
            codomain: ColumnValue::UInts(vec![100, 200]),
            domain_predicate: f_pred,
            deleted: BitSet::new(),
        };
        let function_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };

        let sealed_fn_tile = Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![0, 1, 2, 3]),
            codomain: Box::new(Tile::Scalar(ColumnValue::UInts(vec![0, 1, 2, 3]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let input_tiling = Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::UInt))),
        };

        let output_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };
        let mut map_result = MapResultProducer {
            base: ProducerBase::new(MapResultProducer::alloc_id(), &output_tiling),
            input: Box::new(TestTileProducer::new(sealed_fn_tile, input_tiling)),
            function: Box::new(TestTileProducer::new(curried_fn_tile, function_tiling)),
        };

        let result = map_result.get(map_result.tiling().universal_guard());

        let Tile::CurriedFunction {
            domain1,
            domain_predicate: out_pred,
            ..
        } = result
        else {
            panic!("Expected CurriedFunction");
        };

        // Only x=0 and x=1 have entries in the output (y=2,3 absent from CurriedFunction).
        let ColumnValue::UInts(d1_vals) = domain1 else {
            panic!("domain1 should be UInts");
        };
        assert_eq!(d1_vals, vec![0, 1], "only x=0,1 should appear in domain1");

        assert!(
            out_pred.contains(&Value::UInt(0))
                && !out_pred.contains(&Value::UInt(1))
                && !out_pred.contains(&Value::UInt(2))
                && !out_pred.contains(&Value::UInt(3)),
            "Incorrect pred {out_pred:?}"
        );
    }

    /// When f_domain_predicate is True the output domain_predicate should equal the input's.
    #[test]
    fn map_result_producer_curried_function_domain_predicate_both_true() {
        let curried_fn_tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![0, 1]),
            offsets: ColumnValue::UInts(vec![0, 1]),
            domain2: ColumnValue::UInts(vec![10, 20]),
            codomain: ColumnValue::UInts(vec![100, 200]),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let function_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };
        let sealed_fn_tile = Tile::SealedFunction {
            domain: ColumnValue::UInts(vec![0, 1]),
            codomain: Box::new(Tile::Scalar(ColumnValue::UInts(vec![0, 1]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let input_tiling = Tiling::SealedFunction {
            domain: Extent::Base(BaseType::UInt),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::UInt))),
        };
        let output_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };
        let mut map_result = MapResultProducer {
            base: ProducerBase::new(MapResultProducer::alloc_id(), &output_tiling),
            input: Box::new(TestTileProducer::new(sealed_fn_tile, input_tiling)),
            function: Box::new(TestTileProducer::new(curried_fn_tile, function_tiling)),
        };
        let result = map_result.get(map_result.tiling().universal_guard());
        let Tile::CurriedFunction {
            domain_predicate: out_pred,
            ..
        } = result
        else {
            panic!("Expected CurriedFunction");
        };
        assert_eq!(
            out_pred,
            Predicate::True,
            "both predicates True → output should be True (terminal)"
        );
    }
}
