//! Tile operator and producer types for the CCL dataflow graph.
//!
//! A [`TileOperator`] is a static descriptor of a computation node — it knows
//! its output [`Tiling`] and can create a live [`TileProducer`] via
//! [`TileOperator::subscribe`].  A [`TileProducer`] is the runtime counterpart:
//! it can answer `get` queries and accept `release` notifications.
//!
//! Operators and producers mirror each other: `FooOperator` / `FooProducer`
//! pairs appear throughout the module.

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    hash::Hash,
    iter,
    rc::Rc,
    sync::{Mutex, OnceLock},
};

use bit_set::BitSet;
use bit_vec::BitVec;
use intervalsets::{Bounding, Interval, IntervalSet, ops::Difference};
use log::trace;

pub use crate::interpreter::tiling::{FunctionGuard, Predicate, Tile, TileGuard, Tiling};
use crate::{
    ccl::AggregateKind,
    interpreter::{
        BaseType, ColumnValue, Consumer, DataSourceDomainExtentImpl, Extent, FunctionDef,
        NotifyOrSubscribeResult, Scheduler, Value, bindings_are_list, transform_hashmap_values,
        tuple_field, validate_tile,
    },
    pretty_graph::VizOptions,
    pretty_tree::InspectNode,
};

/// Static descriptor of a computation node in the tile dataflow graph.
///
/// An operator knows its output [`Tiling`] and can instantiate a live
/// [`TileProducer`] by subscribing a [`Consumer`].  Operators are
/// constructed at compile time; producers are created on demand at runtime.
pub trait TileOperator {
    /// Get the extent (type) of this operator.
    fn extent(&self) -> Extent {
        self.tiling().extent()
    }

    /// Return the [`Tiling`] that describes this operator's output shape.
    /// If the operator has unbound arguments, the tiling will be a curried function
    /// from inputs to the output.
    fn tiling(&self) -> &Tiling;

    /// Subscribe to this operator with an intent guard and consumer.
    /// Returns a producer that allows the consumer to get data and release regions.
    ///
    /// # Arguments
    /// * `intent_guard` - The region of the operator's extent that the consumer
    ///   is interested in
    /// * `consumer` - The consumer that will receive notifications when data is ready
    /// * `var_scope` - The variable scope for looking up variables, wrapped in Rc
    ///   to match the internal parent representation and allow cheap sharing
    ///   (e.g., Lambda stores the scope for child scope construction).
    ///
    /// # Returns
    /// A producer that provides access to the data and allows releasing regions
    fn subscribe(
        &mut self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer>;

    /// Inspect this producer as an [`InspectNode`] for visualization.
    ///
    /// Always includes name and tiling, and impls can add children with `add_inspect_children`
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let name: &'static str = std::any::type_name::<Self>().rsplit_once("::").unwrap().1;
        self.add_inspect_children(
            InspectNode::new(name).with_tiling(self.tiling().to_string()),
            opts,
        )
    }

    /// Hook for adding any children to the InspectNode.
    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node
    }

    /// If Some, represents an equality constraint between all or part of the domain
    /// and the result (i.e. the deepest codomain) of the output of this operator.
    /// Individual operators should override this when they are able to automatically detect this constraint.
    /// For example, [`IterateExtent`] always produces an identity function output, so it returns `Some([])`.
    /// Other operators like [`FanOut`] and [`Memo`] preserve structure, so they pass the value through from their
    /// input
    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        None
    }
}

/// Per-display-name instance counters, shared across all producer types.
///
/// Each key is the display name of a producer (e.g. `"MapApply"`, `"Memo"`),
/// and the value is the next ID to assign.  IDs start at 1.
static PRODUCER_COUNTERS: OnceLock<Mutex<HashMap<&'static str, usize>>> = OnceLock::new();

/// Common identity and tiling state shared by every [`TileProducer`].
///
/// Storing these together avoids repeating the same two fields and their
/// trivial accessor implementations across every producer struct.
pub struct ProducerBase {
    /// Instance-unique ID, allocated by [`TileProducer::alloc_id`].
    pub id: usize,
    /// Output tiling for this producer.
    pub tiling: Tiling,
    /// Obsolete region of the tiling
    pub obsolete_guard: TileGuard,
}

impl ProducerBase {
    fn new(id: usize, tiling: &Tiling) -> Self {
        Self {
            id,
            tiling: tiling.clone(),
            obsolete_guard: tiling.empty_guard(),
        }
    }
}

/// Implement [`TileProducer::base`] and [`TileProducer::base_mut`] for a concrete
/// producer struct that stores its shared state in a field named `base: ProducerBase`.
///
/// Usage: place `impl_producer_base!();` inside the `impl TileProducer for Foo` block
/// in place of the two boilerplate accessor methods.
macro_rules! impl_producer_base {
    () => {
        fn base(&self) -> &ProducerBase {
            &self.base
        }
        fn base_mut(&mut self) -> &mut ProducerBase {
            &mut self.base
        }
    };
}

/// Live runtime counterpart of a [`TileOperator`].
///
/// Created by [`TileOperator::subscribe`], a producer services `get` queries
/// and accepts `release` notifications from its consumer.
pub trait TileProducer {
    /// Return the shared identity/tiling state for this producer.
    fn base(&self) -> &ProducerBase;

    /// Return the shared identity/tiling state for this producer.
    fn base_mut(&mut self) -> &mut ProducerBase;

    /// Return the [`Tiling`] that describes this producer's output shape.
    fn tiling(&self) -> &Tiling {
        &self.base().tiling
    }

    /// Return the instance-unique numeric ID assigned at construction.
    fn producer_id(&self) -> usize {
        self.base().id
    }

    /// Allocate the next instance ID for this producer type.
    ///
    /// The counter key is derived from `Self`'s type name with the `"Producer"`
    /// suffix stripped.  Call this from each producer's constructor to
    /// initialise its `id` field: `id: Self::alloc_id()`.
    fn alloc_id() -> usize
    where
        Self: Sized,
    {
        let raw: &'static str = std::any::type_name::<Self>().rsplit_once("::").unwrap().1;
        let key: &'static str = raw.strip_suffix("Producer").unwrap_or(raw);
        let map = PRODUCER_COUNTERS.get_or_init(|| Mutex::new(HashMap::new()));
        let mut counters = map.lock().unwrap();
        let counter = counters.entry(key).or_insert(0);
        *counter += 1;
        *counter
    }

    /// Return the name of the concrete producer type, disambiguated by instance.
    ///
    /// The default implementation derives the display name from the concrete
    /// type name by stripping the `"Producer"` suffix, then appends `#<id>`.
    /// For example, `MapApplyProducer` with id 3 → `"MapApply#3"`.
    fn name(&self) -> String {
        let raw = std::any::type_name::<Self>().rsplit_once("::").unwrap().1;
        let base = raw.strip_suffix("Producer").unwrap_or(raw);
        format!("{}#{}", base, self.producer_id())
    }

    /// Returns the current obsolete guard for this producer. The producer will
    /// never return any more data in the guarded region via `get`.
    fn obsolete_guard(&self) -> &TileGuard {
        &self.base().obsolete_guard
    }

    /// Fetch the current tile value.  Contains generic logic for all producers
    fn get(&mut self, projection_guard: TileGuard) -> Tile {
        let result = self.get_impl(projection_guard);
        trace!(
            "{} produced {:?} for tiling {}",
            self.name(),
            result,
            self.tiling()
        );
        debug_assert!(validate_tile(&result), "Invalid tile: {result:?}");
        assert!(
            result.check_from(self.tiling()),
            "{result:?} vs {:?}",
            self.tiling()
        );
        result
    }

    /// Fetch the current tile value.  Producer-specific logic
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile;

    /// Release interest in a region.
    /// The `obsolete_guard` specifies a sub-region of the subscription that
    /// is no longer needed. Returns an expanded obsolete guard that may be
    /// larger if the producer has additional obsolescence information (e.g.,
    /// from variables with their own obsolete guards).
    fn release(&mut self, obsolete_guard: TileGuard) {
        trace!("{} release: {obsolete_guard:?}", self.name());
        assert!(
            obsolete_guard.check_from(self.tiling()),
            "{obsolete_guard:?} vs {:?}",
            self.tiling()
        );
        let new_guard = self.base().obsolete_guard.union(&obsolete_guard);
        if new_guard != self.base().obsolete_guard {
            self.base_mut().obsolete_guard = new_guard;
            self.release_impl(obsolete_guard);
        }
    }

    /// Release interest in a region.
    /// Contains producer-specific release logic.
    fn release_impl(&mut self, obsolete_guard: TileGuard);

    /// Inspect this producer as an [`InspectNode`] for visualization.
    ///
    /// Always includes name and tiling, and impls can add children with `add_inspect_children`
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        self.add_inspect_children(
            InspectNode::new(self.name()).with_tiling(self.tiling().to_string()),
            opts,
        )
    }

    /// Hook for adding any children to the InspectNode.
    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node
    }
}

/// Represents a step on a path through a Tile structure
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TilePathStep {
    /// A step into a specific field of a Record
    Record(String),
    /// A step into the codomain of a function
    Codomain,
}

/// Repeat a scalar or record-of-scalars tile `len` times along the domain axis.
///
/// Used by [`MapToConstProducer`] to broadcast a constant value across all
/// domain elements: `Tile::Scalar(cv)` → `Tile::Scalar(cv.repeat(len))`;
/// `Tile::Record(m)` → `Tile::Record(m.map(t → repeat_tile(t, len)))`.
fn repeat_tile(tile: Tile, len: usize) -> Tile {
    match tile {
        Tile::Scalar(cv) => Tile::Scalar(cv.repeat(len)),
        Tile::Record(m) => Tile::Record(
            m.into_iter()
                .map(|(k, t)| (k, repeat_tile(t, len)))
                .collect(),
        ),
        other => panic!("repeat_tile: unsupported tile shape {other:?}"),
    }
}

/// Converts a Scalar tile or Record of Scalars to its underlying [`ColumnValue`].
pub fn scalar_tile_to_column_value(tile: Tile) -> ColumnValue {
    match tile {
        Tile::Scalar(cv) => cv,
        Tile::Record(m) => {
            ColumnValue::Records(extract_hashmap_values(m, scalar_tile_to_column_value))
        }
        _ => panic!("Not scalar"),
    }
}

/// Apply a function tile over a column of input values, producing a column of outputs.
///
/// Handles all four function tile representations:
/// - [`Tile::Scalar`] wrapping a [`Value::ComputableFunction`]: calls `f.apply` directly.
/// - [`Tile::Scalar`] wrapping a [`Value::Function`] (bindings table): maps each element
///   through the table.
/// - [`Tile::SealedFunction`]: treated as a point-lookup table keyed by domain value.
/// - [`Tile::CurriedFunction`]: each input value maps to a [`Value::Function`] bag of the
///   matching codomain group.
///
/// `output_extent` types the output column for the bindings-table and `SealedFunction`
/// cases; it is unused for `ComputableFunction` (which determines its own output type)
/// and `CurriedFunction` (which always produces [`ColumnValue::Variants`]).
fn apply_function_tile(
    function_tile: Tile,
    mut input: ColumnValue,
    input_extent: &Extent,
    output_extent: &Extent,
) -> ColumnValue {
    match function_tile {
        Tile::Scalar(func) => match func.as_single() {
            Some(Value::ComputableFunction(f)) => f.apply(input),
            Some(Value::Function(bindings)) => {
                if bindings_are_list(&bindings) {
                    // Inputs are sequential u0, u1, … so input holds raw indices.
                    let table = ColumnValue::from_values(
                        bindings.into_iter().map(|b| b.output).collect(),
                        output_extent,
                    );
                    input.transform_by_list(table)
                } else {
                    let (keys, values) = bindings.into_iter().map(|b| (b.input, b.output)).unzip();
                    let keys = ColumnValue::from_values(keys, input_extent);
                    let values = ColumnValue::from_values(values, output_extent);
                    input.transform_by_map(keys, values)
                }
            }
            None => ColumnValue::from_values(Vec::new(), output_extent),
            _ => panic!("apply_function_tile: Scalar tile is not a function value"),
        },
        Tile::SealedFunction {
            domain, codomain, ..
        } => input.transform_by_map(domain, scalar_tile_to_column_value(*codomain)),
        tile => panic!("apply_function_tile: not a function tile: {tile:?}"),
    }
}

/// Inverse of [`scalar_tile_to_column_value`]: reconstructs a [`Tile`] from a
/// [`ColumnValue`] using the given [`Tiling`] to determine the output shape.
///
/// - `Tiling::Scalar` → `Tile::Scalar(cv)`
/// - `Tiling::Record` → `Tile::Record(fields)` where each field is rebuilt recursively
fn column_value_to_tile(cv: ColumnValue, tiling: &Tiling) -> Tile {
    match tiling {
        Tiling::Scalar(_) => Tile::Scalar(cv),
        Tiling::Record(fields) => {
            let ColumnValue::Records(mut cv_fields) = cv else {
                panic!(
                    "column_value_to_tile: expected Records ColumnValue for Record tiling, got {cv:?}"
                );
            };
            Tile::Record(
                fields
                    .iter()
                    .map(|(k, t)| {
                        let field_cv = cv_fields
                            .remove(k)
                            .unwrap_or_else(|| panic!("column_value_to_tile: missing field {k}"));
                        (k.clone(), column_value_to_tile(field_cv, t))
                    })
                    .collect(),
            )
        }
        other => panic!("column_value_to_tile: unsupported tiling {other:?}"),
    }
}

/// Creates a new tiling based on the input tiling and a transformation of the deepest codomain
/// of the input (i.e. the "result" of the tiling).
fn change_tiling_result(
    input_tiling: &Tiling,
    transformation: impl FnOnce(&Extent) -> Tiling,
) -> Tiling {
    match input_tiling {
        Tiling::Scalar(e) => transformation(e),
        Tiling::Record(fields) => {
            transformation(&Extent::Record(transform_hashmap_values(fields, |t| {
                t.extent()
            })))
        }
        Tiling::SealedFunction { domain, codomain } => Tiling::SealedFunction {
            domain: domain.clone(),
            codomain: Box::new(change_tiling_result(codomain, transformation)),
        },
        Tiling::CurriedFunction {
            domain1,
            domain2,
            codomain,
        } => Tiling::CurriedFunction {
            domain1: domain1.clone(),
            domain2: domain2.clone(),
            codomain: transformation(codomain).extent(),
        },
        _ => panic!("Cannot apply Map to {input_tiling}"),
    }
}

/// Apply the given transformation to the ColumnValue that is the deepest codomain of the
/// provided nested function tile (i.e. the "result" of the tile).
fn process_tile_result(
    input_tiling: &Tiling,
    input_tile: Tile,
    transformation: impl FnOnce(ColumnValue) -> ColumnValue,
) -> Tile {
    match input_tile {
        Tile::Scalar(t) => column_value_to_tile(transformation(t), input_tiling),
        Tile::Record(fields) => column_value_to_tile(
            transformation(scalar_tile_to_column_value(Tile::Record(fields))),
            input_tiling,
        ),
        Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate,
            deleted,
        } => Tile::SealedFunction {
            domain,
            domain_predicate,
            deleted,
            codomain: Box::new(process_tile_result(
                &input_tiling.codomain().unwrap_or_else(|| unreachable!()),
                *codomain,
                transformation,
            )),
        },
        Tile::CurriedFunction {
            domain1,
            offsets,
            domain2,
            codomain,
            domain_predicate,
            deleted,
        } => Tile::CurriedFunction {
            domain1,
            offsets,
            domain2,
            codomain: transformation(codomain),
            domain_predicate,
            deleted,
        },
        _ => panic!("Cannot apply Map to {input_tile:?}"),
    }
}

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
            "MapApply expected function tiling, Got {f_tiling:?}"
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
        let upstream_guard = match obsolete_guard {
            g if g.is_empty() => self.function.tiling().empty_guard(),
            g if g.is_universal() => self.input.tiling().universal_guard(),
            TileGuard::Function(FunctionGuard::Domain(p)) => {
                TileGuard::Function(FunctionGuard::Domain(p))
            }
            TileGuard::Function(FunctionGuard::Codomain(g)) => {
                TileGuard::Function(FunctionGuard::Codomain(g))
            }
            g => todo!("Unimplemented guard in MapResultProducer: {g:?}"),
        };
        self.input.release(upstream_guard);
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
        Box::new(MapToConstProducer {
            base: ProducerBase::new(MapToConstProducer::alloc_id(), &self.tiling),
            input: input_producer,
            constant: constant_producer,
            mode: self.mode,
        })
    }
}

struct MapToConstProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    constant: Box<dyn TileProducer>,
    mode: MapResultToConstMode,
}

impl TileProducer for MapToConstProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
            .child("constant", self.constant.inspect(opts))
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let c_tiling = self.constant.tiling();
        assert!(
            c_tiling.is_scalar(),
            "MapToConst expected scalar tiling, Got {c_tiling:?}"
        );
        let i_tiling = self.input.tiling().clone();
        let input_guard = match projection_guard {
            TileGuard::Function(FunctionGuard::Domain(p)) => {
                TileGuard::Function(FunctionGuard::Domain(p))
            }
            _ => i_tiling.universal_guard(),
        };
        let input_tile = self.input.get(input_guard);
        let constant_tile = self.constant.get(c_tiling.universal_guard());

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

/// Produces a sealed-function tile whose domain and codomain both equal `extent`.
///
/// Used to enumerate all values in an extent: the resulting tile maps each
/// element to itself (`identity`)
pub struct IterateExtent {
    /// The extent to iterate over.
    pub extent: Extent,
    /// The tiling — always `Tiling::SealedFunction { domain: extent, codomain: extent }`.
    pub tiling: Tiling,
}

impl IterateExtent {
    pub fn new(extent: Extent) -> Self {
        let tiling = Tiling::SealedFunction {
            domain: extent.clone(),
            codomain: Box::new(Tiling::Scalar(extent.clone())),
        };
        Self { tiling, extent }
    }

    fn add_all_source_handles(
        extent: &Extent,
        consumer: Rc<RefCell<dyn Consumer>>,
        scheduler: &mut Scheduler,
    ) {
        match extent {
            Extent::DataSourceDomain(extent_impl, ..) => {
                let c = consumer.clone();
                scheduler.add_source_handle(
                    extent_impl.clone(),
                    Box::new(move || c.borrow_mut().notify()),
                );
            }
            Extent::Record(fields) => {
                for field_extent in fields.values() {
                    Self::add_all_source_handles(field_extent, consumer.clone(), scheduler);
                }
            }
            Extent::Restricted { base, .. } => {
                Self::add_all_source_handles(base, consumer, scheduler);
            }
            Extent::Union(extents) => {
                for extent in extents {
                    Self::add_all_source_handles(extent, consumer.clone(), scheduler);
                }
            }
            // Nothing to do for other extents since they all complete from the start of the program
            _ => {}
        }
    }
}

impl TileOperator for IterateExtent {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let mut producer = Box::new(IterateExtentProducer {
            base: ProducerBase::new(IterateExtentProducer::alloc_id(), &self.tiling),
            extent: self.extent.clone(),
            released: Predicate::False,
        });

        let NotifyOrSubscribeResult { notify, subscribe } =
            self.extent.subscribe_to_iteration_action();
        if notify {
            consumer.notify();
        }
        if subscribe {
            let consumer_wrapper = Rc::new(RefCell::new(move || {
                consumer.notify();
            }));
            Self::add_all_source_handles(&self.extent, consumer_wrapper, scheduler);
            let name = producer.name();
            // Register this producer with any data sources in the extent by calling release with
            // a false predicate.  This way the sources knows about all producers that read it
            //before execution starts.
            release_extent(&mut producer.extent, &Predicate::False, &name);
        }

        producer
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        Some(Vec::new())
    }
}

/// Producer for [`IterateExtent`]: emits an identity sealed-function tile.
struct IterateExtentProducer {
    base: ProducerBase,
    /// The extent being iterated.
    ///
    /// For `UIntRange` extents this is an `IntervalSet<usize>` that shrinks
    /// directly as sub-intervals are released.
    extent: Extent,
    /// Accumulates every predicate that has been released so far.
    ///
    /// Used for pair-level filtering in `get_impl`: after `iterate_extent`
    /// produces the cross-product, any row whose domain value satisfies this
    /// predicate is removed before returning the tile.  This is necessary for
    /// `Extent::Record` cross-products where individual source extents cannot
    /// be safely shrunk (shrinking source2's key 0 would prevent future
    /// cross-product pairs like (1, 0) from ever being produced).
    released: Predicate,
}

fn get_iterate_extent_predicate(extent: &Extent) -> Predicate {
    match extent {
        Extent::DataSourceDomain(source) => source.borrow().get_yield_predicate(),
        // For a cross-product, the domain_predicate must be the conjunction (AND / Record) of
        // each field's predicate.  Only pairs where EVERY field's value has already been
        // committed by its source can be guaranteed to have already been delivered; a pair
        // where even one field comes from a source that can still grow might be new next time.
        //
        // An OR would over-claim: e.g. arm {_1:≤u0, _0:True} says "(x,0) for any x has
        // already been seen", but if source0 later adds key 1 then (1,0) is genuinely new.
        Extent::Record(fields) => Predicate::Record(
            fields
                .iter()
                .map(|(f, e)| (f.clone(), get_iterate_extent_predicate(e)))
                .collect(),
        ),
        // For a disjoint union, each variant contributes its own predicate over
        // its own tag; combine them positionally so downstream consumers can
        // split per-variant releases back to their source sub-extents.
        Extent::Union(variants) => {
            Predicate::Union(variants.iter().map(get_iterate_extent_predicate).collect())
        }
        _ => Predicate::True,
    }
}

/// Convert a `IntervalSet<Value::UInt>` values into an
/// `IntervalSet<usize>`, preserving bound types.
///
/// Discrete `Value` intervals are normalised to closed form by `intervalsets`,
/// so the resulting `usize` intervals are also closed.
fn predicate_intervals_to_usize(intervals: &IntervalSet<Value>) -> IntervalSet<usize> {
    IntervalSet::from_iter(intervals.intervals().iter().map(|iv| {
        // Left-unbounded intervals (e.g. (-∞, 3]) are clamped to [0, r] since
        // UIntRange indices are always non-negative.
        let left: usize = iv.lval().map_or(0, |v| v.as_uint());
        match iv.rval() {
            Some(r) => Interval::closed(left, r.as_uint()),
            None => Interval::closed_unbound(left),
        }
    }))
}

/// Release values from `extent` that are covered by `pred`.
///
/// For [`Extent::UIntRange`] extents, released sub-intervals are subtracted
/// directly from the stored [`IntervalSet<usize>`], so arbitrary non-contiguous
/// releases are handled without any external accumulator.
fn release_extent(extent: &mut Extent, pred: &Predicate, releaser: &str) {
    match extent {
        Extent::Record(fields) => match pred {
            p if p.as_bool().is_some_and(|p| p) => {
                for e in fields.values_mut() {
                    release_extent(e, &Predicate::True, releaser);
                }
            }
            p if p.as_bool().is_some_and(|p| !p) => {
                for e in fields.values_mut() {
                    release_extent(e, &Predicate::False, releaser);
                }
            }
            // Or: apply each arm independently.  Each arm describes a distinct
            // sub-region; releasing all arms releases their union.
            Predicate::Or(arms) => {
                for arm in arms {
                    release_extent(extent, arm, releaser);
                }
            }
            p => {
                // A Record predicate is a conjunction: {f0: p0, f1: p1} means
                // "release pairs where p0(f0) AND p1(f1)".  We can only safely
                // advance a dimension's extent when all other dimensions are
                // unconstrained (Predicate::True), because the AND means the
                // full cross-product sub-space is released along that axis.
                let field_preds = p.split_record(fields);
                for (f, e) in fields.iter_mut() {
                    let others_all_true = field_preds
                        .iter()
                        .all(|(k, p)| k == f || *p == Predicate::True);
                    if others_all_true {
                        release_extent(e, &field_preds[f], releaser);
                    } else {
                        // TODO: handle the case where multiple fields have
                        // non-trivial predicates; requires releasing the
                        // intersection of projected ranges per dimension.
                    }
                }
            }
        },
        Extent::DataSourceDomain(source) => {
            source.borrow_mut().release(releaser, pred.clone());
        }
        Extent::UIntRange(remaining) => match pred {
            Predicate::True => {
                *remaining = IntervalSet::from(Interval::<usize>::empty());
            }
            Predicate::False => {}
            Predicate::LessThanEq(v) => {
                // Release every index up to and including v.
                let to_remove = IntervalSet::from(Interval::closed(0usize, v.as_uint()));
                *remaining = remaining.difference(&to_remove);
            }
            Predicate::Intervals(intervals) => {
                // Subtract the released sub-intervals directly from the remaining set.
                let to_remove = predicate_intervals_to_usize(intervals);
                *remaining = remaining.difference(&to_remove);
            }
            _ => todo!("Got {pred:?} for UIntRange"),
        },
        Extent::Base(BaseType::Unit) => {}
        Extent::Union(variants) => match pred {
            p if p.as_bool().is_some_and(|p| p) => {
                for v in variants.iter_mut() {
                    release_extent(v, &Predicate::True, releaser);
                }
            }
            p if p.as_bool().is_some_and(|p| !p) => {
                for v in variants.iter_mut() {
                    release_extent(v, &Predicate::False, releaser);
                }
            }
            // A Union predicate aligns positionally with the variants: each
            // arm releases its corresponding sub-extent.
            Predicate::Union(arms) if arms.len() == variants.len() => {
                for (v, arm) in variants.iter_mut().zip(arms.iter()) {
                    release_extent(v, arm, releaser);
                }
            }
            _ => todo!("Got {pred:?} for Union extent"),
        },
        _ => panic!("Unexpected extent: {extent:?}"),
    }
}

/// Produce all values for the given extent.
fn iterate_extent(extent: &Extent, producer: &str) -> ColumnValue {
    match extent {
        Extent::Base(BaseType::Unit) => ColumnValue::Units(1),
        Extent::UIntRange(remaining) => {
            // Discrete intervals are normalised to closed bounds, so iterate
            // each [a, b] as a..=b to produce all remaining indices.
            let values: Vec<usize> = remaining
                .intervals()
                .iter()
                .flat_map(|iv| {
                    let left = *iv
                        .lval()
                        .expect("UIntRange: unexpected left-unbounded interval");
                    let right = *iv
                        .rval()
                        .expect("UIntRange: unexpected right-unbounded interval");
                    left..=right
                })
                .collect();
            ColumnValue::from_uints(values)
        }
        Extent::DataSourceDomain(source_impl) => source_impl.borrow_mut().get_elements(producer),
        Extent::Record(fields) => iterate_record(fields, producer),
        Extent::Union(variants) => iterate_union(variants, producer),
        Extent::Restricted { .. } => {
            panic!("Iterating over restricted extents not supported; use Filter operators instead")
        }
        _ => panic!("Attempted to iterate on infinite Extent"),
    }
}

/// Iterate a [`Extent::Union`] by enumerating each variant in turn and
/// stitching the results into a single [`ColumnValue::Union`] column with
/// per-variant tags assigned in order.
fn iterate_union(variants: &[Extent], producer: &str) -> ColumnValue {
    let columns: Vec<ColumnValue> = variants
        .iter()
        .map(|v| iterate_extent(v, producer))
        .collect();
    let mut tags: Vec<usize> = Vec::with_capacity(columns.iter().map(|c| c.len()).sum());
    for (i, c) in columns.iter().enumerate() {
        tags.extend(iter::repeat_n(i, c.len()));
    }
    ColumnValue::Union {
        tags,
        variants: columns,
    }
}

fn iterate_record(fields: &HashMap<String, Extent>, producer: &str) -> ColumnValue {
    let data: HashMap<String, ColumnValue> = fields
        .iter()
        .map(|(field, field_extent)| (field.clone(), iterate_extent(field_extent, producer)))
        .collect();
    ColumnValue::cartesian_product(data)
}

impl TileProducer for IterateExtentProducer {
    impl_producer_base!();

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let values = iterate_extent(&self.extent, &self.name());
        let domain_predicate = get_iterate_extent_predicate(&self.extent);
        let mut tile = Tile::SealedFunction {
            domain: values.clone(),
            codomain: Box::new(Tile::Scalar(values)),
            domain_predicate,
            deleted: BitSet::new(),
        };
        // Filter out any domain rows that have already been released.
        // Values may also be removed from underlying sources for efficiency, but
        // this filter here is ultimately responsible for not returning released data.
        tile.remove_guarded(TileGuard::Function(FunctionGuard::Domain(
            self.released.clone(),
        )));
        tile
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let name = self.name();
        let TileGuard::Function(FunctionGuard::Domain(pred)) = obsolete_guard else {
            panic!("IterateExtent::release expected Domain guard, got {obsolete_guard:?}")
        };
        // Accumulate so get_impl can filter already-released rows.
        self.released = self.released.union(&pred);
        // Also propagate to sub-extents where safe (e.g. full-slice UIntRange
        // shrinks, or single-dimension DataSourceDomain releases when all other
        // dimensions are unconstrained).
        release_extent(&mut self.extent, &pred, &name);
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

fn extract_predicate(pred: &Predicate, path: &[TilePathStep]) -> Predicate {
    if path.is_empty() || pred.as_bool().is_some() {
        return pred.clone();
    };

    if let Predicate::Or(arms) = pred {
        return Predicate::flatten_or(
            arms.iter()
                .map(|arm| extract_predicate(arm, path))
                .collect(),
        );
    }

    match &path[0] {
        TilePathStep::Record(f) => {
            if let Predicate::Record(fields) = pred {
                // If we see a Record predicate with our field where all other fields are false, then
                // return our field.  Correlated predicates don't give us any information about the
                // requested field in isolation, so return false.
                if fields.iter().all(|(field, p)| field == f || p.is_true()) {
                    extract_predicate(&fields[f], &path[1..])
                } else {
                    Predicate::False
                }
            } else {
                panic!("Expected record predicate, got {pred:?}");
            }
        }
        _ => todo!("We don't support correlated function preds yet"),
    }
}

/// Combines multiple sealed-function operators sharing the same domain into a
/// single sealed-function operator whose codomain is a record of all their codomains.
///
/// All inputs must have `SealedFunction` tilings with compatible domains.
/// Output fields are named `_0`, `_1`, … matching the input order.
pub struct FanIn {
    /// Output tiling: either a `SealedFunction { domain, codomain: Record { … } }`
    /// or a `CurriedFunction { domain1, domain2, codomain: Record { … } }`,
    /// depending on the input operators.
    tiling: Tiling,
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
        Self {
            tiling,
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
        Box::new(FanInProducer {
            base: ProducerBase::new(FanInProducer::alloc_id(), &self.tiling),
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
                g => unimplemented!("Unexpected guard {g:?}"),
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
    tiling: Tiling,
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
            tiling,
            names,
            inputs,
        }
    }
}

impl TileOperator for ScalarFanIn {
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
        Box::new(ScalarFanInProducer {
            base: ProducerBase::new(ScalarFanInProducer::alloc_id(), &self.tiling),
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

    fn release_impl(&mut self, _obsolete_guard: TileGuard) {
        // Nothing to do
    }
}

/// Inverts a sealed-function operator, producing a lookup-function from codomain to domain.
///
/// For an input `domain → codomain`, `Converse` produces a
/// `CurriedFunction { domain: codomain, codomain: domain }`.  Each codomain
/// value maps to the list of domain values that produce it.
pub struct Converse {
    /// Output tiling: `CurriedFunction { domain: input.codomain, codomain: input.domain }`.
    tiling: Tiling,
    /// The sealed-function input to invert.
    input: Box<dyn TileOperator>,
}

impl Converse {
    /// Create a `Converse` operator that inverts `input`.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let (domain, codomain) = input
            .tiling()
            .split_function_extent()
            .unwrap_or_else(|| panic!("Converse expected function, got {:?}", input.tiling()));
        let tiling = Tiling::CurriedFunction {
            domain1: codomain,
            domain2: domain.clone(),
            codomain: domain,
        };
        Self { tiling, input }
    }
}

impl TileOperator for Converse {
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
        Box::new(ConverseProducer {
            base: ProducerBase::new(ConverseProducer::alloc_id(), self.tiling()),
            input: self
                .input
                .subscribe(self.tiling().universal_guard(), consumer, scheduler),
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        Some(vec![TilePathStep::Codomain])
    }
}

/// Producer for [`Converse`]: inverts a sealed-function tile into a lookup-function tile.
struct ConverseProducer {
    base: ProducerBase,
    /// The upstream producer whose output is inverted.
    input: Box<dyn TileProducer>,
}

/// Sort row indices by typed key, detect group boundaries, and assemble the
/// curried-function tile for [`ConverseProducer`].
///
/// `K` is the native element type of the codomain column; using it directly
/// avoids boxing to [`Value`] for most column types. `codomain` and `domain`
/// are re-indexed via [`ColumnValue::select_indices`].
fn converse_group_by_key<K: PartialOrd>(
    keys: &[K],
    codomain: &ColumnValue,
    domain: &ColumnValue,
    domain_predicate: Predicate,
    input_deleted: &BitSet,
) -> Tile {
    let n = keys.len();
    // Sort row indices by codomain key; equal keys will be adjacent.
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_unstable_by(|&a, &b| keys[a].partial_cmp(&keys[b]).expect("Type mismatch"));
    // Identify group boundaries: a new group starts wherever the sorted key changes.
    let mut group_starts: Vec<usize> = Vec::new();
    for i in 0..n {
        if i == 0 || keys[order[i]] != keys[order[i - 1]] {
            group_starts.push(i);
        }
    }
    let num_groups = group_starts.len();
    // domain1: one codomain value per group (the key for the outer lookup).
    let domain1_col = codomain.select_indices(group_starts.iter().map(|&s| order[s]), num_groups);
    // Remap deleted bits: output position j corresponds to input row order[j].
    let output_deleted: BitSet = order
        .iter()
        .enumerate()
        .filter(|(_, src)| input_deleted.contains(**src))
        .map(|(j, _)| j)
        .collect();
    // domain2/codomain_out: original domain values reordered to match sorted groups.
    let domain2_col = domain.select_indices(order.into_iter(), n);
    Tile::curried_function(
        domain1_col,
        ColumnValue::UInts(group_starts),
        domain2_col.clone(),
        domain2_col,
        if domain_predicate.as_bool().unwrap_or(false) {
            Predicate::True
        } else {
            Predicate::False
        },
        output_deleted,
    )
}

impl TileProducer for ConverseProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        match input_tile {
            Tile::SealedFunction {
                domain,
                codomain,
                domain_predicate,
                deleted,
            } => match *codomain {
                Tile::Scalar(codomain) => {
                    // Dispatch on the native element type of the codomain column so that
                    // sorting uses typed comparison (PartialOrd) and avoids boxing to Value
                    // wherever the inner type is already ordered natively.
                    match &codomain {
                        ColumnValue::Units(n) => {
                            // All codomains are unit; create one group with all rows in order.
                            let keys = vec![(); *n];
                            converse_group_by_key(
                                &keys,
                                &codomain,
                                &domain,
                                domain_predicate,
                                &deleted,
                            )
                        }
                        ColumnValue::Ints(v) => {
                            converse_group_by_key(v, &codomain, &domain, domain_predicate, &deleted)
                        }
                        ColumnValue::UInts(v) => {
                            converse_group_by_key(v, &codomain, &domain, domain_predicate, &deleted)
                        }
                        ColumnValue::Strings(v) => {
                            converse_group_by_key(v, &codomain, &domain, domain_predicate, &deleted)
                        }
                        ColumnValue::Bools(bv) => {
                            // Materialise as Vec<bool> so the element type is PartialOrd.
                            let v: Vec<bool> = bv.iter().collect();
                            converse_group_by_key(
                                &v,
                                &codomain,
                                &domain,
                                domain_predicate,
                                &deleted,
                            )
                        }
                        ColumnValue::Variants(v) => {
                            // Value is PartialOrd; pass the inner vec directly.
                            converse_group_by_key(v, &codomain, &domain, domain_predicate, &deleted)
                        }
                        ColumnValue::Records(_) => {
                            // No native slice to borrow; materialise one Value per row for sorting.
                            // TODO: benchmark this and figure out a way to avoid if needed.
                            let n = codomain.len();
                            let keys: Vec<Value> = (0..n).map(|i| codomain.index_at(i)).collect();
                            converse_group_by_key(
                                &keys,
                                &codomain,
                                &domain,
                                domain_predicate,
                                &deleted,
                            )
                        }
                        ColumnValue::FunctionBindings { .. } => {
                            panic!(
                                "Cannot converse a function whose codomain is a function binding"
                            )
                        }
                        ColumnValue::Union { .. } => {
                            // Materialise one tagged Value per row for sorting.
                            let n = codomain.len();
                            let keys: Vec<Value> = (0..n).map(|i| codomain.index_at(i)).collect();
                            converse_group_by_key(
                                &keys,
                                &codomain,
                                &domain,
                                domain_predicate,
                                &deleted,
                            )
                        }
                    }
                }
                _ => panic!("Can only converse functions with scalar codomains"),
            },
            _ => panic!("Can only converse functions"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        match obsolete_guard {
            g if g.is_universal() => self.input.release(self.input.tiling().universal_guard()),
            TileGuard::Function(FunctionGuard::Codomain(g)) => {
                if let TileGuard::Function(FunctionGuard::Domain(p)) = g.as_ref() {
                    self.input
                        .release(TileGuard::Function(FunctionGuard::Domain(p.clone())))
                }
            }
            _ => {}
        }
    }
}

/// Replaces the codomain of a sealed function with the domain values themselves,
/// creating an identity mapping where the codomain is a copy of the domain.
///
/// Takes a `SealedFunction(domain → codomain)` and produces `SealedFunction(domain → Scalar(domain))`.
/// The output domain is unchanged; the codomain becomes a scalar version of the same domain values.
pub struct MapDomain {
    /// Output tiling: `SealedFunction { domain, codomain: Scalar(domain) }`.
    tiling: Tiling,
    /// The sealed-function input.
    input: Box<dyn TileOperator>,
}

impl MapDomain {
    /// Create a `MapDomain` operator that replaces the codomain with the domain values.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let Tiling::SealedFunction { domain, .. } = input.tiling() else {
            panic!(
                "MapDomain expected SealedFunction, got {:?}",
                input.tiling()
            )
        };
        let tiling = Tiling::SealedFunction {
            domain: domain.clone(),
            codomain: Box::new(Tiling::Scalar(domain.clone())),
        };
        Self { tiling, input }
    }
}

impl TileOperator for MapDomain {
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
        Box::new(MapDomainProducer {
            base: ProducerBase::new(MapDomainProducer::alloc_id(), self.tiling()),
            input: self
                .input
                .subscribe(self.tiling().universal_guard(), consumer, scheduler),
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        Some(Vec::new())
    }
}

/// Producer for [`MapDomain`]: replaces a sealed-function's codomain with its domain.
struct MapDomainProducer {
    base: ProducerBase,
    /// The upstream producer whose codomain is replaced.
    input: Box<dyn TileProducer>,
}

impl TileProducer for MapDomainProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        match input_tile {
            Tile::SealedFunction {
                domain,
                domain_predicate,
                deleted,
                ..
            } => Tile::SealedFunction {
                codomain: Box::new(Tile::Scalar(domain.clone())),
                domain,
                domain_predicate,
                deleted,
            },
            _ => panic!("MapDomain expected SealedFunction tile"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        self.input.release(match obsolete_guard {
            g if g.is_universal() => self.input.tiling().universal_guard(),
            g if g.is_empty() => self.input.tiling().empty_guard(),
            TileGuard::Function(FunctionGuard::Domain(p)) => {
                TileGuard::Function(FunctionGuard::Domain(p))
            }
            _ => todo!(),
        });
    }
}

/// Flattens a curried function into a sealed function with a pair domain.
///
/// Takes a `CurriedFunction(A → B → C)` and produces `SealedFunction(Record(A, B) → Scalar(C))`.
/// The two domain extents are packed into a record domain with fields `_0` (outer domain) and `_1` (inner domain),
/// while the codomain becomes a scalar version of the original codomain.
pub struct Uncurry {
    /// Output tiling: `SealedFunction { domain: Record { _0: A, _1: B }, codomain: Scalar(C) }`.
    tiling: Tiling,
    /// The curried-function input.
    input: Box<dyn TileOperator>,
}

impl Uncurry {
    /// Create an `Uncurry` operator that flattens a curried function into a sealed function.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let Tiling::CurriedFunction {
            domain1,
            domain2,
            codomain,
        } = input.tiling()
        else {
            panic!("Uncurry expected CurriedFunction, got {:?}", input.tiling())
        };
        let pair_extent = Extent::Record(HashMap::from([
            (tuple_field(0), domain1.clone()),
            (tuple_field(1), domain2.clone()),
        ]));
        let tiling = Tiling::SealedFunction {
            domain: pair_extent,
            codomain: Box::new(Tiling::Scalar(codomain.clone())),
        };
        Self { tiling, input }
    }
}

impl TileOperator for Uncurry {
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
        Box::new(UncurryProducer {
            base: ProducerBase::new(UncurryProducer::alloc_id(), self.tiling()),
            input: self
                .input
                .subscribe(self.tiling().universal_guard(), consumer, scheduler),
        })
    }
}

/// Producer for [`Uncurry`]: flattens a curried-function tile into a sealed-function tile with pair domain.
struct UncurryProducer {
    base: ProducerBase,
    /// The upstream producer whose curried function is flattened.
    input: Box<dyn TileProducer>,
}

impl TileProducer for UncurryProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        match input_tile {
            Tile::CurriedFunction {
                domain1,
                offsets,
                domain2,
                codomain,
                domain_predicate,
                ..
            } => {
                // Extract offsets as a vec of usize.
                let ColumnValue::UInts(offsets_vec) = offsets else {
                    panic!("CurriedFunction offsets must be ColumnValue::UInts");
                };

                // Build an expansion index iterator: for each group i,
                // emit i repeated (group_end - group_start) times.
                let mut expansion_indices = Vec::new();
                for i in 0..domain1.len() {
                    let group_start = offsets_vec[i];
                    let group_end = if i + 1 < offsets_vec.len() {
                        offsets_vec[i + 1]
                    } else {
                        domain2.len()
                    };
                    for _ in group_start..group_end {
                        expansion_indices.push(i);
                    }
                }

                let total_rows = expansion_indices.len();
                let expanded_domain1 =
                    domain1.select_indices(expansion_indices.into_iter(), total_rows);

                // Build the pair domain column as Record with fields _0 and _1.
                let pair_domain = ColumnValue::Records(HashMap::from([
                    (tuple_field(0), expanded_domain1),
                    (tuple_field(1), domain2),
                ]));

                let inner_pred = if domain_predicate.as_bool().unwrap_or(true) {
                    Predicate::True
                } else {
                    Predicate::False
                };
                let mut result = Tile::SealedFunction {
                    domain: pair_domain,
                    codomain: Box::new(Tile::Scalar(codomain)),
                    domain_predicate: Predicate::Record(HashMap::from([
                        (tuple_field(0), domain_predicate),
                        (tuple_field(1), inner_pred),
                    ])),
                    deleted: BitSet::new(),
                };
                result.remove_guarded(self.base().obsolete_guard.clone());
                result
            }
            _ => panic!("Uncurry expected CurriedFunction tile"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let input_guard = match &obsolete_guard {
            // Pass through empty and universal guards unchanged.
            g if g.is_empty() => self.input.tiling().empty_guard(),
            g if g.is_universal() => self.input.tiling().universal_guard(),
            // Split domain guards on the pair domain (_0, _1) into record predicates.
            TileGuard::Function(FunctionGuard::Domain(pred)) => {
                let pair_fields = HashMap::from([(tuple_field(0), ()), (tuple_field(1), ())]);

                let preds: Box<dyn Iterator<Item = &Predicate>> = match pred {
                    Predicate::Or(preds) => Box::new(preds.iter()),
                    _ => Box::new(iter::once(pred)),
                };

                let mut domain_guard = TileGuard::Function(FunctionGuard::Domain(Predicate::False));
                for pred in preds {
                    let mut split_preds = pred.split_record(&pair_fields);
                    let outer_pred = split_preds.remove(&tuple_field(0)).unwrap();
                    let inner_pred = split_preds.remove(&tuple_field(1)).unwrap();
                    if inner_pred.as_bool().is_some_and(|x| x) {
                        domain_guard = domain_guard
                            .union(&TileGuard::Function(FunctionGuard::Domain(outer_pred)));
                    }
                }
                domain_guard
            }
            g => panic!("Unsupported obsolete guard: {g:?}"),
        };
        trace!("{} releasing up with: {input_guard:?}", self.name());
        self.input.release(input_guard);
    }
}

/// Filters a function tile by a predicate, keeping only pairs whose domain element
/// maps to `true` under the predicate.
///
/// The `predicate` operator must produce a function from the input's domain type to
/// `bool`. For each domain element in the input tile, the predicate is evaluated;
/// only elements where it returns `true` are retained together with their associated
/// codomain values.
///
/// TODO we should replace this with a Restrict node that filters based on a function of the domain,
/// rather than this which filters based on a function of the codomain.
pub struct Filter {
    /// Output tiling, equal to the input tiling (filtering preserves the type).
    tiling: Tiling,
    /// The sealed-function input to filter.
    input: Box<dyn TileOperator>,
    /// The boolean predicate applied to each domain element.
    predicate: Box<dyn TileOperator>,
}

impl Filter {
    /// Create a `Filter` that retains elements of `input` for which `predicate` is `true`.
    pub fn new(input: Box<dyn TileOperator>, predicate: Box<dyn TileOperator>) -> Self {
        let tiling = input.tiling().clone();
        Self {
            tiling,
            input,
            predicate,
        }
    }
}

impl TileOperator for Filter {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
            .child("predicate", self.predicate.inspect(opts))
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
        let predicate_producer = self.predicate.subscribe(
            self.predicate.tiling().universal_guard(),
            Box::new(consumer_wrapper.clone()),
            scheduler,
        );
        let input_producer = self.input.subscribe(
            self.input.tiling().universal_guard(),
            Box::new(consumer_wrapper.clone()),
            scheduler,
        );
        Box::new(FilterProducer {
            base: ProducerBase::new(FilterProducer::alloc_id(), &self.tiling),
            input: input_producer,
            predicate: predicate_producer,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        self.input.result_correlation()
    }
}

struct FilterProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    predicate: Box<dyn TileProducer>,
}

impl TileProducer for FilterProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
            .child("predicate", self.predicate.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let pred_guard = self.predicate.tiling().universal_guard();
        let i_guard = self.input.tiling().universal_guard();
        let predicate_result = self.predicate.get(pred_guard);
        let input_result = self.input.get(i_guard);

        match (predicate_result, input_result) {
            // Scalar predicate applied element-wise to a function tile's domain.
            (
                Tile::Scalar(pred),
                Tile::SealedFunction {
                    domain,
                    codomain,
                    domain_predicate,
                    deleted,
                },
            ) => match pred.as_single() {
                Some(Value::ComputableFunction(f)) => {
                    let func_result = f.apply(domain.clone());
                    let mask = func_result
                        .as_bitvec()
                        .unwrap_or_else(|| panic!("Expected boolean mask"));
                    let mut output = Tile::SealedFunction {
                        domain,
                        codomain,
                        domain_predicate,
                        deleted,
                    };
                    output.mark_deleted(mask);
                    output
                }
                _ => panic!("Filter predicate is not a function"),
            },
            // Both predicate and input are function tiles sharing the same domain.
            (
                Tile::SealedFunction {
                    domain: pred_inputs,
                    codomain: pred_outputs,
                    ..
                },
                Tile::SealedFunction {
                    domain: i_inputs,
                    codomain: i_outputs,
                    domain_predicate,
                    deleted,
                },
            ) => {
                // We rely on having the predicate and input sharing exactly the same domain
                // so that we can cheaply extract the bitmask from the predicate codomain.
                // This check is expensive, so only run it in debug builds.
                debug_assert_eq!(pred_inputs, i_inputs);
                let pred_outputs = scalar_tile_to_column_value(*pred_outputs);
                // Build a domain-value → bool map from the predicate tile.
                let mask = pred_outputs
                    .as_bitvec()
                    .unwrap_or_else(|| panic!("Expected bools"));
                let mut output = Tile::SealedFunction {
                    domain: i_inputs,
                    codomain: i_outputs,
                    domain_predicate,
                    deleted,
                };
                output.retain(mask);
                output
            }
            _ => panic!("Invalid Filter input tiles"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if matches!(self.predicate.tiling(), Tiling::SealedFunction { .. }) {
            // Both predicate and input share the same underlying domain source, so both
            // must be released together; releasing only one leaves the other's upstream
            // FanOutProducer release-guard stale, causing it to re-deliver already-consumed
            // data while the other side returns nothing on the next get().
            self.predicate.release(obsolete_guard.clone());
        }
        self.input.release(obsolete_guard);
    }
}

/// Applies a boolean predicate function to its own domain, producing an identity
/// function over the surviving elements.
///
/// Unlike [`Filter`], which requires a separately-provided input stream and predicate
/// stream that must share the same domain, `Restrict` derives the identity input
/// directly from the predicate's domain. This avoids domain-mismatch panics when the
/// predicate itself contains inner [`Filter`] operators that narrow the domain before
/// the boolean values are produced.
///
/// The predicate operator must produce a `SealedFunction { domain: D, codomain: Bool }`.
/// `Restrict` returns `SealedFunction { domain: D', codomain: D' }` where D' ⊆ D is the
/// subset of domain elements for which the predicate is `true`.
pub struct Restrict {
    /// Output tiling — `SealedFunction(D, D)` mirroring an [`IterateExtent`] over D.
    tiling: Tiling,
    /// The boolean predicate over the domain to restrict.
    predicate: Box<dyn TileOperator>,
}

impl Restrict {
    /// Create a `Restrict` from a predicate operator.
    ///
    /// Panics if `predicate` does not have a `SealedFunction` tiling.
    pub fn new(predicate: Box<dyn TileOperator>) -> Self {
        let domain_extent = match predicate.tiling() {
            Tiling::SealedFunction { domain, .. } => domain.clone(),
            other => panic!("Restrict expects SealedFunction predicate tiling, got {other:?}"),
        };
        let tiling = Tiling::SealedFunction {
            domain: domain_extent.clone(),
            codomain: Box::new(Tiling::Scalar(domain_extent)),
        };
        Self { tiling, predicate }
    }
}

impl TileOperator for Restrict {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("predicate", self.predicate.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        let predicate_producer = self.predicate.subscribe(
            self.predicate.tiling().universal_guard(),
            consumer,
            scheduler,
        );
        Box::new(RestrictProducer {
            base: ProducerBase::new(RestrictProducer::alloc_id(), &self.tiling),
            predicate: predicate_producer,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        Some(Vec::new())
    }
}

struct RestrictProducer {
    base: ProducerBase,
    predicate: Box<dyn TileProducer>,
}

impl TileProducer for RestrictProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("predicate", self.predicate.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let pred_guard = self.predicate.tiling().universal_guard();
        let pred_result = self.predicate.get(pred_guard);
        match pred_result {
            Tile::SealedFunction {
                domain,
                codomain,
                domain_predicate,
                deleted,
            } => {
                let pred_bools = scalar_tile_to_column_value(*codomain);
                let mask = pred_bools
                    .as_bitvec()
                    .unwrap_or_else(|| panic!("Restrict: expected boolean predicate codomain"));
                // Build identity: each surviving domain element maps to itself.
                let mut output = Tile::SealedFunction {
                    codomain: Box::new(Tile::Scalar(domain.clone())),
                    domain,
                    domain_predicate,
                    deleted,
                };
                output.mark_deleted(mask);
                output
            }
            _ => panic!("Restrict: predicate must produce a SealedFunction tile"),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        self.predicate.release(obsolete_guard);
    }
}

/// Reduces a `SealedFunction` input to a single scalar via an aggregation operation.
///
/// On each `get`, reads all codomain values from the input and folds them into a
/// running `Tile::Aggregation` accumulator. The result becomes terminal once the
/// input's `domain_predicate` is `True` (all elements seen).
pub struct Aggregate {
    /// The `SealedFunction`-typed input whose codomain elements are aggregated.
    input: Box<dyn TileOperator>,
    /// Output tiling — always `Tiling::Aggregation { accumulator: <output extent> }`.
    tiling: Tiling,
}

impl Aggregate {
    /// Construct an `Aggregate` operator.
    ///
    /// Panics if `input` does not have a `SealedFunction` tiling, or if `kind`
    /// does not support the codomain element type.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        let err = || panic!("Cannot apply {kind:?} to non-function {:?}", input.tiling());
        let codomain_extent = input
            .tiling()
            .codomain()
            .map(|t| t.extent())
            .unwrap_or_else(err);
        let tiling = Tiling::Aggregation {
            kind,
            accumulator: kind.output_extent(&codomain_extent).unwrap_or_else(err),
        };
        Self { input, tiling }
    }
}

impl TileOperator for Aggregate {
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
        let input_producer =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(AggregateProducer::new(self.tiling.clone(), input_producer))
    }
}

struct AggregateProducer {
    base: ProducerBase,
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation.
    kind: AggregateKind,
    /// Running accumulation state; updated in place on each `get`.
    accumulator: Tile,
}

impl AggregateProducer {
    /// Construct an `AggregateProducer`, seeding the accumulator with the identity element.
    fn new(tiling: Tiling, input: Box<dyn TileProducer>) -> Self {
        let (kind, accumulator) = match &tiling {
            Tiling::Aggregation {
                kind,
                accumulator: acc_extent,
            } => (
                *kind,
                Tile::Aggregation {
                    kind: *kind,
                    accumulator: kind.initial_accumulator(acc_extent),
                    terminal: ColumnValue::Bools(BitVec::from_elem(1, false)),
                },
            ),
            other => panic!("AggregateProducer created with non-Aggregation tiling: {other:?}"),
        };
        Self {
            base: ProducerBase::new(Self::alloc_id(), &tiling),
            input,
            kind,
            accumulator,
        }
    }
}

impl TileProducer for AggregateProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let i_tiling = self.input.tiling().clone();
        let mut input_result = self.input.get(i_tiling.universal_guard());
        let upstream_guard = input_result.to_guard();
        input_result.compact();
        let Tile::SealedFunction { codomain, .. } = input_result else {
            panic!("Aggregate expected function tiling, got {input_result:?}");
        };
        self.input.release(upstream_guard);
        let values = scalar_tile_to_column_value(*codomain);

        let is_terminal = self.input.obsolete_guard().is_universal();
        trace!(
            "Aggregate input is_terminal: {is_terminal} from guard {:?}",
            self.input.obsolete_guard()
        );
        let Tile::Aggregation {
            kind: _,
            ref mut accumulator,
            terminal: ColumnValue::Bools(ref mut terminal),
        } = self.accumulator
        else {
            panic!("Accumulator must be Aggregation tile")
        };
        self.kind.accumulate(accumulator, &values, 0, values.len());
        terminal.set(0, is_terminal);
        self.accumulator.clone()
    }

    fn release_impl(&mut self, _obsolete_guard: TileGuard) {
        // Nothing to do. We could consider sanity checking that get is not called
        // after a universal release.
    }
}

pub struct ExtractAggregate {
    input: Box<dyn TileOperator>,
    tiling: Tiling,
    kind: AggregateKind,
    only_terminal: bool,
}

impl ExtractAggregate {
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind, only_terminal: bool) -> Self {
        let tiling = if only_terminal {
            Tiling::Scalar(input.extent())
        } else {
            todo!("functions on partial aggregates")
        };
        Self {
            input,
            tiling,
            kind,
            only_terminal,
        }
    }
}

impl TileOperator for ExtractAggregate {
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
        Box::new(ExtractAggregateProducer {
            base: ProducerBase::new(ExtractAggregateProducer::alloc_id(), self.tiling()),
            input: self
                .input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler),
            kind: self.kind,
            only_terminal: self.only_terminal,
        })
    }
}

struct ExtractAggregateProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    kind: AggregateKind,
    only_terminal: bool,
}

impl TileProducer for ExtractAggregateProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_result = self.input.get(self.input.tiling().universal_guard());
        let Tile::Aggregation {
            kind: _,
            accumulator,
            terminal,
        } = input_result
        else {
            panic!(
                "ExtractAggregate expected Aggregation tiling, got {:?}",
                self.input.tiling()
            );
        };
        if self.only_terminal {
            if terminal.index_at(0).as_bool() {
                Tile::Scalar(self.kind.extract(accumulator))
            } else {
                self.tiling().empty_tile()
            }
        } else {
            todo!()
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.is_universal() {
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

/// Extracts terminal per-key aggregation results from a
/// `SealedFunction(D, Aggregation)`, producing a `SealedFunction(D, Scalar)`.
///
/// For each domain element, the aggregation value is extracted and emitted only
/// when that element's terminal flag is `true`.  Non-terminal elements are
/// filtered out of the output domain.
pub struct MapExtractAggregate {
    /// The `SealedFunction(D, Aggregation)`-typed input.
    input: Box<dyn TileOperator>,
    /// The aggregation operation used to extract final values from accumulators.
    kind: AggregateKind,
    /// Output tiling: `SealedFunction { domain: input.domain, codomain: Scalar(output_extent) }`.
    tiling: Tiling,
}

impl MapExtractAggregate {
    /// Create a new `MapExtractAggregate` operator.
    ///
    /// `input` must have a `SealedFunction` tiling whose codomain is
    /// `Aggregation { accumulator: A }`.  The output tiling is
    /// `SealedFunction { domain: input.domain, codomain: Scalar(A) }`.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        let tiling = match input.tiling() {
            Tiling::SealedFunction { domain, codomain } => match codomain.as_ref() {
                Tiling::Aggregation { accumulator, .. } => Tiling::SealedFunction {
                    domain: domain.clone(),
                    codomain: Box::new(Tiling::Scalar(accumulator.clone())),
                },
                t => panic!(
                    "MapExtractAggregate expected SealedFunction(Aggregation) codomain, got {t:?}"
                ),
            },
            t => panic!("MapExtractAggregate expected SealedFunction input, got {t:?}"),
        };
        Self {
            input,
            kind,
            tiling,
        }
    }
}

impl TileOperator for MapExtractAggregate {
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
        let input_producer =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(MapExtractAggregateProducer {
            base: ProducerBase::new(MapExtractAggregateProducer::alloc_id(), &self.tiling),
            input: input_producer,
            kind: self.kind,
        })
    }
}

/// Producer for [`MapExtractAggregate`].
struct MapExtractAggregateProducer {
    base: ProducerBase,
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation used to extract final values.
    kind: AggregateKind,
}

impl TileProducer for MapExtractAggregateProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_result = self.input.get(self.input.tiling().universal_guard());
        let Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate,
            ..
        } = input_result
        else {
            panic!("MapExtractAggregate expected SealedFunction tile")
        };
        let Tile::Aggregation {
            accumulator,
            terminal,
            ..
        } = *codomain
        else {
            panic!("MapExtractAggregate expected SealedFunction(Aggregation) codomain")
        };
        // Emit only the domain elements whose per-key aggregation is terminal.
        let mask = terminal
            .as_bitvec()
            .unwrap_or_else(|| panic!("Expected bools"));
        let mut output = Tile::SealedFunction {
            domain,
            codomain: Box::new(Tile::Scalar(self.kind.extract(accumulator))),
            domain_predicate,
            deleted: BitSet::new(),
        };
        output.retain(mask);
        output
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        self.input.release(match obsolete_guard {
            g if g.is_universal() => self.input.tiling().universal_guard(),
            g if g.is_empty() => self.input.tiling().empty_guard(),
            TileGuard::Function(FunctionGuard::Domain(p)) => {
                TileGuard::Function(FunctionGuard::Domain(p))
            }
            _ => todo!(),
        });
    }
}

/// Performs a per-key aggregation over a [`Tile::CurriedFunction`], producing a
/// `SealedFunction` that maps each domain key to an in-progress aggregation.
///
/// For a lookup `D → [C]` and an [`AggregateKind`], `MapAggregate` produces a
/// sealed function `D → Aggregation(C)`.  New data from partial lookups is
/// merged into per-key accumulators on each `get`; each key's aggregation
/// becomes terminal when the input lookup's `domain_predicate` is `True`.
pub struct MapAggregate {
    /// The lookup-function input to aggregate per key.
    input: Box<dyn TileOperator>,
    /// The aggregation operation (Sum, Max, …).
    kind: AggregateKind,
    /// Output tiling: `SealedFunction { domain: input.domain, codomain: Aggregation { accumulator: output_extent } }`.
    tiling: Tiling,
}

impl MapAggregate {
    /// Create a new `MapAggregate` operator.
    ///
    /// `input` must have a `CurriedFunction` tiling; `kind` must support the
    /// lookup's codomain element type.  The output tiling is
    /// `SealedFunction { domain: input.domain, codomain: Aggregation { accumulator: output_extent } }`.
    pub fn new(input: Box<dyn TileOperator>, kind: AggregateKind) -> Self {
        let (domain, input_codomain) = match input.tiling() {
            Tiling::CurriedFunction {
                domain1, codomain, ..
            } => (domain1.clone(), codomain.clone()),
            t => panic!("MapAggregate requires CurriedFunction input, got {t:?}"),
        };
        let output_extent = kind.output_extent(&input_codomain).unwrap_or_else(|| {
            panic!("Cannot apply {kind:?} to codomain extent {input_codomain:?}")
        });
        let tiling = Tiling::SealedFunction {
            domain,
            codomain: Box::new(Tiling::Aggregation {
                kind,
                accumulator: output_extent,
            }),
        };
        Self {
            input,
            kind,
            tiling,
        }
    }
}

impl TileOperator for MapAggregate {
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
        let input_producer =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(MapAggregateProducer {
            base: ProducerBase::new(MapAggregateProducer::alloc_id(), &self.tiling),
            input: input_producer,
            kind: self.kind,
            accumulators: HashMap::new(),
        })
    }
}

/// Producer for [`MapAggregate`].
struct MapAggregateProducer {
    base: ProducerBase,
    /// The subscribed lookup-function producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation.
    kind: AggregateKind,
    /// Running per-key accumulators, grown as new keys arrive across `get` calls.
    accumulators: HashMap<Value, ColumnValue>,
}

impl TileProducer for MapAggregateProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let mut input_tile = self.input.get(self.input.tiling().universal_guard());
        trace!("{} received {input_tile:?}", self.name());
        let upstream_guard = input_tile.to_guard();
        input_tile.compact();
        let Tile::CurriedFunction {
            domain1,
            offsets,
            domain2: _,
            codomain,
            domain_predicate,
            ..
        } = input_tile
        else {
            panic!("MapAggregate requires a CurriedFunction tile")
        };
        // output_extent is the accumulator extent from the Aggregation codomain tiling.
        let output_extent = self.tiling().codomain().unwrap().extent();
        let domain_extent = self.tiling().domain_extent().unwrap();
        // Merge newly arrived values into per-key accumulators.
        let kind = &self.kind;
        let accumulators = &mut self.accumulators;
        let n = domain1.len();
        for i in 0..n {
            let key = domain1.index_at(i);
            let start = offsets.index_at(i).as_uint();
            let end = if i + 1 < n {
                offsets.index_at(i + 1).as_uint()
            } else {
                codomain.len()
            };
            let acc = accumulators
                .entry(key)
                .or_insert_with(|| kind.initial_accumulator(&output_extent));
            kind.accumulate(acc, &codomain, start, end);
        }

        // Release received values
        self.input.release(upstream_guard);

        // Build the output tile from all known per-key accumulators.
        // TODO apply the domain predicate to each domain value.
        let is_terminal = domain_predicate.as_bool().unwrap_or(false);
        let n = self.accumulators.len();
        let (domain_values, accumulator_values): (Vec<Value>, Vec<Value>) = self
            .accumulators
            .iter()
            .map(|(key, acc)| (key.clone(), acc.as_single().unwrap()))
            .unzip();
        Tile::SealedFunction {
            domain: ColumnValue::from_values(domain_values, &domain_extent),
            codomain: Box::new(Tile::Aggregation {
                kind: self.kind,
                accumulator: ColumnValue::from_values(accumulator_values, &output_extent),
                terminal: ColumnValue::Bools(BitVec::from_elem(n, is_terminal)),
            }),
            domain_predicate,
            deleted: BitSet::new(),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.is_universal() {
            self.accumulators.clear();
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

/// Re-entrancy bookkeeping for cyclic op graphs.  Stored in
/// [`FanOutShared::reentrancy`] only for fan-outs constructed via
/// [`FanOut::new_cyclic`]; non-cyclic fan-outs leave it `None` and pay
/// none of the cyclic-mode overhead.
///
/// A fan-out is "cyclic" iff one of its branches feeds (transitively)
/// back into its own input.  In practice this is only the mutation-loop
/// body fan-out: one branch is wired into `Recurse::recursive_input` and
/// the body's `acc_var` reads close the cycle.  In that setup,
/// subscribing or pulling one branch can synchronously trigger the same
/// operation on a sibling branch — the re-entrancy state below catches
/// that and serves from the cache instead of recursively re-entering the
/// inner producer.
struct FanOutReentrancy {
    /// Cache of the most-recently-returned tile from the inner producer,
    /// used to serve re-entrant `FanOutProducer::get_impl` calls.
    ///
    /// **Replace, not merge**: typical inner producers ([`Memo`] in
    /// particular) already return cumulative tiles, so each non-reentrant
    /// pull supplants the previous cache rather than appending to it.
    cached_tile: Tile,
    /// Re-entrancy guard for the inner subscribe path.  `FanOutBranch::subscribe`
    /// of one branch can transitively trigger `subscribe` on a sibling
    /// (e.g. the loop body's `acc_var` reads close back through `Recurse`).
    /// The re-entrant call sees this set, skips the inner subscribe (the
    /// outer call is doing it), and just returns a `FanOutProducer`.
    subscribing_inner: bool,
}

/// Mutable state shared across all branches from the same [`FanOut`] and all
/// [`FanOutProducer`]s it creates.  Wrapping this in `Rc<RefCell<...>>` and
/// creating it eagerly in [`FanOut::new`] ensures that every branch produced by
/// [`FanOut::branch`] shares the same object from the start — even before any
/// [`TileOperator::subscribe`] call has initialised the inner producer.
struct FanOutShared {
    /// Instance ID shared by all [`FanOutProducer`]s from the same fan-out group.
    id: usize,
    /// Inner producer, set on the first [`FanOutBranch::subscribe`] call.
    ///
    /// In cyclic mode (see [`FanOutReentrancy`]), this is also **taken out**
    /// during the inner pull in `FanOutProducer::get_impl` so that
    /// re-entrant calls from cyclic op graphs can detect re-entrance by
    /// finding `None` and fall back to the cached tile.
    producer: Option<Box<dyn TileProducer>>,
    /// Every consumer registered via [`FanOutBranch::subscribe`], in order.
    ///
    /// Stored as `Rc<RefCell<...>>` so that the notification closure can clone the
    /// handles, release the `shared` borrow, and then call each consumer without
    /// holding `shared` across the notification.  This prevents a re-entrant panic
    /// when a consumer (e.g. `SinkConsumer`) calls back into `FanOutProducer::get_impl`,
    /// which itself needs `shared.borrow_mut()`.
    consumers: Vec<Rc<RefCell<Box<dyn Consumer>>>>,
    /// Per-subscriber release guards; intersected before passing upstream.
    release_guards: Vec<TileGuard>,
    /// Re-entrancy bookkeeping for cyclic op graphs.  `None` for non-cyclic
    /// fan-outs (the overwhelming majority); `Some` only when constructed
    /// via [`FanOut::new_cyclic`].
    reentrancy: Option<FanOutReentrancy>,
}

/// RAII guard for the cyclic `FanOut` `subscribing_inner` flag.  Created
/// when we set the flag `true` to drive the inner `subscribe`; its `Drop`
/// resets the flag to `false`.  This makes the path panic-safe — if
/// `input.subscribe(...)` unwinds, the flag is still reset so a later
/// (re-)subscribe attempt doesn't get silently skipped.
struct SubscribingInnerGuard<'a> {
    shared: &'a Rc<RefCell<FanOutShared>>,
}

impl<'a> Drop for SubscribingInnerGuard<'a> {
    fn drop(&mut self) {
        if let Some(re) = self.shared.borrow_mut().reentrancy.as_mut() {
            re.subscribing_inner = false;
        }
    }
}

/// RAII guard for the cyclic `FanOut`'s "producer taken out" pattern in
/// `FanOutProducer::get_impl`.  Owns the temporarily-extracted inner
/// producer and on `Drop` puts it back into `shared.producer`, so a
/// panic from the inner `producer.get(...)` doesn't leave
/// `shared.producer = None` forever (which would break every later
/// pull on this fan-out).
struct TakenProducerGuard<'a> {
    shared: &'a Rc<RefCell<FanOutShared>>,
    /// Wrapped in `Option` so the destructor can `take()` the producer
    /// and move it back into `shared` (you can't move out of `&mut self`
    /// fields in `Drop`, but `Option::take` swaps the value).
    producer: Option<Box<dyn TileProducer>>,
}

impl<'a> Drop for TakenProducerGuard<'a> {
    fn drop(&mut self) {
        if let Some(producer) = self.producer.take() {
            self.shared.borrow_mut().producer = Some(producer);
        }
    }
}

/// Allows for creating multiple TileOperators that all point to the same
/// underlying operator.  Call [`FanOut::branch`] to get additional handles;
/// subscribing to any handle will reuse the same inner producer.
pub struct FanOut {
    input: Rc<RefCell<Box<dyn TileOperator>>>,
    tiling: Tiling,
    /// All mutable shared state.  Created eagerly so that branches produced by
    /// [`FanOut::branch`] always share the same object.
    shared: Rc<RefCell<FanOutShared>>,
    /// Whether any branches have been created yet.
    used: RefCell<bool>,
}

impl FanOut {
    /// Construct a new `FanOut` wrapping `input`.  Use this for ordinary
    /// (non-cyclic) op graphs; the resulting fan-out doesn't pay any
    /// cyclic-mode overhead.  If a branch of this fan-out ends up
    /// feeding back into its own input (e.g. via `Recurse::recursive_input`),
    /// use [`FanOut::new_cyclic`] instead.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        Self::new_with_reentrancy(input, None)
    }

    /// Construct a cyclic [`FanOut`].  Sets up the re-entrancy bookkeeping
    /// (a cached tile snapshot + a subscribe-in-progress flag) needed when
    /// a branch of this fan-out transitively feeds back into its own input.
    ///
    /// The cost relative to [`FanOut::new`] is one `Tile` clone per pull
    /// (to refresh the cache).  The mutation-loop body fan-out is the only
    /// caller today; non-cyclic users should stick with `new`.
    pub fn new_cyclic(input: Box<dyn TileOperator>) -> Self {
        let cached_tile = input.tiling().empty_tile();
        Self::new_with_reentrancy(
            input,
            Some(FanOutReentrancy {
                cached_tile,
                subscribing_inner: false,
            }),
        )
    }

    fn new_with_reentrancy(
        input: Box<dyn TileOperator>,
        reentrancy: Option<FanOutReentrancy>,
    ) -> Self {
        let tiling = input.tiling().clone();
        let shared = Rc::new(RefCell::new(FanOutShared {
            id: FanOutProducer::alloc_id(),
            producer: None,
            consumers: Vec::new(),
            release_guards: Vec::new(),
            reentrancy,
        }));
        Self {
            input: Rc::new(RefCell::new(input)),
            tiling,
            shared,
            used: RefCell::new(false),
        }
    }

    /// Return a new branch handle on this fan-out.  All branches share the same
    /// inner producer and consumer list; subscribing to any of them is
    /// equivalent.
    pub fn branch(&self) -> Box<dyn TileOperator> {
        let result = FanOutBranch {
            input: self.input.clone(),
            tiling: self.tiling.clone(),
            shared: self.shared.clone(), // shares the Rc — always connected
            primary: !*self.used.borrow(),
        };
        *self.used.borrow_mut() = true;
        Box::new(result)
    }

    pub fn tiling(&self) -> &Tiling {
        &self.tiling
    }
}

struct FanOutBranch {
    input: Rc<RefCell<Box<dyn TileOperator>>>,
    tiling: Tiling,
    /// All mutable shared state.  Created eagerly so that branches produced by
    /// [`FanOut::branch`] always share the same object.
    shared: Rc<RefCell<FanOutShared>>,
    /// True for the first handle returned by [`FanOut::branch`], false for subsequent ones.
    /// The primary renders its input subtree in inspect; copies emit a back-reference.
    primary: bool,
}

impl TileOperator for FanOutBranch {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let id = self.shared.borrow().id;
        if self.primary {
            InspectNode::new(format!("FanOut#{id}"))
                .with_tiling(self.tiling().to_string())
                .child("input", self.input.borrow().inspect(opts))
        } else {
            InspectNode::leaf(format!("→ FanOut#{id}"))
        }
    }

    fn subscribe(
        &mut self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Register the consumer and reserve its release-guard slot.
        let index = {
            let mut shared = self.shared.borrow_mut();
            let index = shared.consumers.len();
            shared.consumers.push(Rc::new(RefCell::new(consumer)));
            shared.release_guards.push(self.tiling.empty_guard());
            index
        }; // borrow released here before we might call input.subscribe

        // Decide whether *this* call should drive the inner subscribe.
        // `producer.is_none()` is the standard "first subscription" check;
        // in cyclic mode, `!reentrancy.subscribing_inner` makes the path
        // re-entrancy-safe: a sibling-branch subscribe triggered from
        // inside the inner subscribe call sees the flag set and just
        // returns a producer (the outer call will populate `producer`
        // before anyone pulls).
        let should_subscribe = {
            let mut shared = self.shared.borrow_mut();
            if shared.producer.is_some() {
                false
            } else if let Some(re) = shared.reentrancy.as_mut() {
                if re.subscribing_inner {
                    false
                } else {
                    re.subscribing_inner = true;
                    true
                }
            } else {
                true
            }
        };

        // Drive the inner subscribe (first non-reentrant subscriber only).
        // We must not hold a borrow of `shared` during `input.subscribe`
        // because that call may synchronously fire the notification closure,
        // which itself borrows `shared`.
        if should_subscribe {
            // RAII: any path out of this block (success or panic) resets
            // `subscribing_inner` to `false`.  Without the guard, a panic
            // from `input.subscribe(...)` would leave the flag set
            // forever and silently skip every future subscribe attempt
            // on this fan-out.
            let _guard = SubscribingInnerGuard {
                shared: &self.shared,
            };
            let shared_rc = self.shared.clone();
            let inner = self.input.borrow_mut().subscribe(
                intent_guard,
                Box::new(move || {
                    // Clone the consumer handles while holding a short borrow,
                    // then release the borrow before calling notify().  This
                    // prevents a re-entrant panic when a consumer (e.g.
                    // SinkConsumer) calls FanOutProducer::get_impl(), which
                    // needs shared.borrow_mut() for the same Rc.
                    let consumers = shared_rc.borrow().consumers.clone();
                    for c in &consumers {
                        c.borrow_mut().notify();
                    }
                }),
                scheduler,
            );
            self.shared.borrow_mut().producer = Some(inner);
            // `_guard` drops here, resetting `subscribing_inner`.
        }

        Box::new(FanOutProducer {
            base: ProducerBase::new(self.shared.borrow().id, &self.tiling),
            shared: self.shared.clone(),
            index,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        self.input.borrow().result_correlation()
    }
}

struct FanOutProducer {
    base: ProducerBase,
    /// Shared state (consumers + release guards).
    shared: Rc<RefCell<FanOutShared>>,
    /// This producer's index into `shared.consumers` and `shared.release_guards`.
    index: usize,
}

impl TileProducer for FanOutProducer {
    impl_producer_base!();

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        if self.index == 0 {
            InspectNode::new(self.name())
                .with_tiling(self.tiling().to_string())
                .child(
                    "input",
                    self.shared
                        .borrow()
                        .producer
                        .as_ref()
                        .unwrap()
                        .inspect(opts),
                )
        } else {
            InspectNode::leaf(format!("→ {}", self.name()))
        }
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        // In cyclic mode, take the inner producer out during the pull so
        // sibling-branch re-entrance can detect re-entrance by finding
        // `producer == None` and serve from the cached tile.  In
        // non-cyclic mode, the producer stays in `shared` and we pull
        // through a regular borrow.
        let cyclic = self.shared.borrow().reentrancy.is_some();
        let mut result = if cyclic {
            let producer_opt = self.shared.borrow_mut().producer.take();
            if let Some(producer) = producer_opt {
                // RAII: put the producer back into `shared` on any exit
                // path (success or panic).  Without this guard, a panic
                // from `producer.get(...)` would leave `shared.producer
                // = None` forever, silently breaking every subsequent
                // pull on this fan-out.
                let mut guard = TakenProducerGuard {
                    shared: &self.shared,
                    producer: Some(producer),
                };
                let tile = guard.producer.as_mut().unwrap().get(projection_guard);
                trace!("{} received {tile:?}", self.name());
                // Refresh the re-entrancy cache before the guard drops.
                // We replace (not merge) — inner producers like `Memo`
                // already return cumulative tiles, so each pull
                // supplants the previous cached snapshot.
                self.shared
                    .borrow_mut()
                    .reentrancy
                    .as_mut()
                    .unwrap()
                    .cached_tile = tile.clone();
                tile
                // `guard` drops here, restoring `shared.producer`.
            } else {
                // Re-entrant pull: another branch's outer `get_impl` is
                // currently holding the producer.  Serve the latest known
                // emission instead of re-entering the inner producer (which
                // would alias `&mut`).
                let cached = self
                    .shared
                    .borrow()
                    .reentrancy
                    .as_ref()
                    .unwrap()
                    .cached_tile
                    .clone();
                trace!("{} serving cached (re-entrant): {cached:?}", self.name());
                cached
            }
        } else {
            self.shared
                .borrow_mut()
                .producer
                .as_mut()
                .unwrap()
                .get(projection_guard)
        };

        // Filter by the stored obsolete guard. Because upstream retains data according to the
        // intersection of all obsolete guards, it may have more data than this specific consumer
        // is interested in.
        let guard = self.shared.borrow().release_guards[self.index].clone();
        trace!("{} removing {guard:?} from {result:?}", self.name());
        result.remove_guarded(guard);
        result
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let mut shared = self.shared.borrow_mut();
        // Union with the existing stored guard so that the accumulated set of
        // delivered data grows monotonically.  Replacing (instead of union-ing)
        // would forget previously-released ranges, causing FanOutBranch to
        // re-deliver data that a consumer has already released.
        let accumulated = shared.release_guards[self.index].union(&obsolete_guard);
        shared.release_guards[self.index] = accumulated;
        let intersection = shared
            .release_guards
            .iter()
            .fold(self.tiling().universal_guard(), |acc, g| acc.intersect(g));
        trace!("{} releasing: {intersection:?}", self.name());
        // In cyclic mode the inner producer can be temporarily taken out
        // by a sibling-branch `get_impl`; skip the inner release in that
        // case (the next non-reentrant release will recompute and
        // forward).  Non-cyclic mode always has `producer = Some(_)`.
        if let Some(producer) = shared.producer.as_mut() {
            producer.release(intersection);
        } else {
            debug_assert!(
                shared.reentrancy.is_some(),
                "non-cyclic FanOut's producer should never be absent during release"
            );
        }
    }
}

/// An operator that logically forwards data from its input to its
/// consumer, but caches it so that the data doesn't have to be recomputed.
/// This involves storing the current Tile, merging new Tiles in as they arrive,
/// and immediately releasing upstream according to the received Tiles.
pub struct Memo {
    pub input: Box<dyn TileOperator>,
    pub tiling: Tiling,
}

impl Memo {
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let tiling = input.tiling().clone();
        Self { input, tiling }
    }
}

impl TileOperator for Memo {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(MemoProducer {
            base: ProducerBase::new(MemoProducer::alloc_id(), &self.tiling),
            input: self.input.subscribe(intent_guard, consumer, scheduler),
            cached_tile: self.tiling().empty_tile(),
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        self.input.result_correlation()
    }
}

struct MemoProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    cached_tile: Tile,
}

impl TileProducer for MemoProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let mut input = self.input.get(projection_guard);
        trace!("{} received {input:?}", self.name());
        let upstream_obsolete = input.to_guard();
        input.compact();
        trace!("{} releasing {upstream_obsolete:?}", self.name());
        self.input.release(upstream_obsolete);
        trace!(
            "{} merging {input:?} into {:?}",
            self.name(),
            self.cached_tile
        );
        self.cached_tile.merge(input);
        self.cached_tile.clone()
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Remove any released data from the cached tile since the consumer
        // is no longer interested.
        self.cached_tile.remove_guarded(obsolete_guard.clone());
        // Compact so that logically-deleted entries are physically gone.
        self.cached_tile.compact();
        // Also release upstream to handle the case where the consumer releases
        // data that was never produced.
        self.input.release(obsolete_guard.clone());
        trace!("{} now has cached {:?}", self.name(), self.cached_tile);
    }
}

/// An operator that permutes the fields of the domain of a `SealedFunction`, according
/// to a specified permutation of field indices.
///
/// For now, this only supports record types that represent tuples, but can
/// be extended if needed.
pub struct PermuteRecordDomain {
    input: Box<dyn TileOperator>,
    tiling: Tiling,
    permutation: Vec<usize>,
}

fn permute_record<T>(mut input: HashMap<String, T>, permutation: &[usize]) -> HashMap<String, T> {
    HashMap::from_iter(permutation.iter().enumerate().map(|(idx, target)| {
        (
            tuple_field(idx),
            input
                .remove(&tuple_field(*target))
                .unwrap_or_else(|| panic!("Input record missing {target}")),
        )
    }))
}

impl PermuteRecordDomain {
    pub fn new(input: Box<dyn TileOperator>, permutation: Vec<usize>) -> Self {
        let Tiling::SealedFunction { domain, codomain } = input.tiling() else {
            panic!(
                "PermuteRecordDomain requires SealedFunction input, got {}",
                input.tiling()
            );
        };
        let Extent::Record(input_fields) = domain else {
            panic!(
                "PermuteRecordDomain requires input with Record domain, got {}",
                input.tiling()
            );
        };
        let tiling = Tiling::SealedFunction {
            domain: Extent::Record(permute_record(input_fields.clone(), &permutation)),
            codomain: codomain.clone(),
        };
        Self {
            input,
            tiling,
            permutation,
        }
    }
}

impl TileOperator for PermuteRecordDomain {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(PermuteRecordDomainProducer {
            base: ProducerBase::new(PermuteRecordDomainProducer::alloc_id(), &self.tiling),
            input: self.input.subscribe(intent_guard, consumer, scheduler),
            permutation: self.permutation.clone(),
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        permute_result_correlation(self.input.result_correlation()?, &self.permutation)
    }
}

/// Translates a `result_correlation` path through a `PermuteRecordDomain` operation.
///
/// The first `Record` step in `corr` names a field in the INPUT domain; after permutation,
/// that field is at the inverse-permuted index in the output domain. An empty path (domain
/// identity) cannot be preserved because the domain is renamed while the codomain is not.
fn permute_result_correlation(
    mut corr: Vec<TilePathStep>,
    permutation: &[usize],
) -> Option<Vec<TilePathStep>> {
    let Some(TilePathStep::Record(f)) = corr.first_mut() else {
        // Empty path means domain == codomain; permuting domain breaks that identity.
        // Non-Record first steps (e.g. Codomain) are unaffected by domain renaming.
        return if corr.is_empty() { None } else { Some(corr) };
    };

    // Build inverse permutation: inv_perm[j] = i where permutation[i] = j.
    // Input field _j is now at output field _inv_perm[j].
    let mut inv_perm = vec![0usize; permutation.len()];
    for (i, &target) in permutation.iter().enumerate() {
        inv_perm[target] = i;
    }
    let j = tuple_field_index(f);
    *f = tuple_field(inv_perm[j]);
    Some(corr)
}

struct PermuteRecordDomainProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    // TODO support non-tuple records
    permutation: Vec<usize>,
}

impl TileProducer for PermuteRecordDomainProducer {
    impl_producer_base!();

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        let Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate,
            deleted,
        } = input_tile
        else {
            unreachable!();
        };
        let ColumnValue::Records(input_fields) = domain else {
            unreachable!();
        };
        let output_domain = ColumnValue::Records(permute_record(input_fields, &self.permutation));
        let output_domain_pred = match domain_predicate {
            g @ Predicate::True | g @ Predicate::False => g,
            Predicate::Record(fields) => {
                Predicate::Record(permute_record(fields, &self.permutation))
            }
            _ => unreachable!(),
        };
        Tile::SealedFunction {
            domain: output_domain,
            codomain,
            domain_predicate: output_domain_pred,
            deleted,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let upstream_guard = match obsolete_guard {
            g if g.is_universal() => self.input.tiling().universal_guard(),
            g if g.is_empty() => self.input.tiling().empty_guard(),
            TileGuard::Function(FunctionGuard::Domain(Predicate::Record(fields))) => {
                TileGuard::Function(FunctionGuard::Domain(Predicate::Record(permute_record(
                    fields,
                    &self.permutation,
                ))))
            }
            _ => {
                unreachable!();
            }
        };
        self.input.release(upstream_guard);
    }
}

/// Parses the numeric index from a tuple field name like `"_3"`.
fn tuple_field_index(field: &str) -> usize {
    field
        .strip_prefix('_')
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| panic!("non-tuple field name: {field}"))
}

/// Converts a `Predicate` written over a nested-record domain into one over the flat
/// positional-tuple domain produced by `FlattenTupleDomain`.
///
/// `field_map[i]` describes where flat field `_i` came from in the nested record:
/// - `(outer_key, None)` — `_i` is the outer field `outer_key` passed through unchanged.
/// - `(outer_key, Some(inner_key))` — `_i` was flattened out of the sub-record at `outer_key`,
///   specifically its field `inner_key`.
///
/// Example: nested type `{a: {x: T, y: T}, b: T}` flattens to `(_0, _1, _2)` with
/// `field_map = [("a", Some("x")), ("a", Some("y")), ("b", None)]`.
/// A predicate `{a: {x: P1, y: P2}, b: P3}` on the nested domain becomes
/// `{_0: P1, _1: P2, _2: P3}` on the flat domain.
fn flatten_predicate(pred: &Predicate, field_map: &[(String, Option<String>)]) -> Predicate {
    match pred {
        Predicate::True | Predicate::False => pred.clone(),
        Predicate::Record(outer_preds) => Predicate::Record(
            field_map
                .iter()
                .enumerate()
                .map(|(out_idx, (outer_k, inner_k_opt))| {
                    let outer_pred = outer_preds
                        .get(outer_k)
                        .unwrap_or_else(|| panic!("missing outer field {outer_k} in predicate"));
                    let out_pred = match inner_k_opt {
                        None => outer_pred.clone(),
                        Some(inner_k) => match outer_pred {
                            Predicate::True => Predicate::True,
                            Predicate::False => Predicate::False,
                            Predicate::Record(inner_preds) => {
                                inner_preds.get(inner_k).cloned().unwrap_or_else(|| {
                                    panic!("missing inner field {inner_k} in sub-predicate")
                                })
                            }
                            p => panic!("unexpected predicate for outer field {outer_k}: {p:?}"),
                        },
                    };
                    (tuple_field(out_idx), out_pred)
                })
                .collect(),
        ),
        p => panic!("FlattenTupleDomain: unsupported domain predicate: {p:?}"),
    }
}

/// Converts a flat-domain `Predicate` back into a nested-tuple `Predicate`.
///
/// Inverse of [`flatten_predicate`]; used when propagating release guards upstream.
fn unflatten_predicate(pred: &Predicate, field_map: &[(String, Option<String>)]) -> Predicate {
    match pred {
        Predicate::True | Predicate::False => pred.clone(),
        Predicate::Record(flat_preds) => {
            let mut outer_groups: HashMap<String, HashMap<String, Predicate>> = HashMap::new();
            let mut pass_through: HashMap<String, Predicate> = HashMap::new();
            for (out_idx, (outer_k, inner_k_opt)) in field_map.iter().enumerate() {
                let flat_pred = flat_preds
                    .get(&tuple_field(out_idx))
                    .unwrap_or_else(|| panic!("missing flat field _{out_idx} in predicate"))
                    .clone();
                match inner_k_opt {
                    None => {
                        pass_through.insert(outer_k.clone(), flat_pred);
                    }
                    Some(inner_k) => {
                        outer_groups
                            .entry(outer_k.clone())
                            .or_default()
                            .insert(inner_k.clone(), flat_pred);
                    }
                }
            }
            let mut result: HashMap<String, Predicate> = pass_through;
            for (outer_k, inner_preds) in outer_groups {
                result.insert(outer_k, Predicate::Record(inner_preds));
            }
            Predicate::Record(result)
        }
        Predicate::Or(preds) => Predicate::Or(
            preds
                .iter()
                .map(|p| unflatten_predicate(p, field_map))
                .collect(),
        ),
        p => panic!("FlattenTupleDomain: unsupported flat predicate: {p:?}"),
    }
}

/// Translates a `result_correlation` path through a [`FlattenTupleDomain`] operation.
///
/// `field_map[i] = (outer_key, inner_key_opt)` describes how the input's nested domain maps to
/// the flat output domain. A two-step `[Record(outer), Record(inner), ...]` path collapses to
/// `[Record(flat_i), ...]` where `flat_i` is the index in `field_map` matching `(outer, Some(inner))`.
/// A single `[Record(outer)]` step is preserved only when `outer` is a pass-through field
/// (`inner_key_opt = None`); flattened outer fields expand to multiple flat fields and cannot
/// be expressed as a single path step, so `None` is returned. An empty path (domain == codomain
/// identity) is also not preservable after flattening and returns `None`.
fn flatten_result_correlation(
    corr: Vec<TilePathStep>,
    field_map: &[(String, Option<String>)],
) -> Option<Vec<TilePathStep>> {
    let Some(first) = corr.first() else {
        return None; // empty path: flat domain ≠ nested codomain
    };
    match first {
        TilePathStep::Codomain => Some(corr), // codomain steps are unaffected by domain renaming
        TilePathStep::Record(outer_key) => {
            let outer_key = outer_key.clone();
            match corr.get(1) {
                Some(TilePathStep::Record(inner_key)) => {
                    // Two-level path: collapse [Record(outer), Record(inner)] to [Record(flat_i)].
                    let inner_key = inner_key.clone();
                    let flat_idx = field_map.iter().position(|(ok, ik)| {
                        ok == &outer_key && ik.as_deref() == Some(inner_key.as_str())
                    })?;
                    let mut result = vec![TilePathStep::Record(tuple_field(flat_idx))];
                    result.extend_from_slice(&corr[2..]);
                    Some(result)
                }
                _ => {
                    // Single Record step: valid only for pass-through (non-flattened) outer fields.
                    let flat_idx = field_map
                        .iter()
                        .position(|(ok, ik)| ok == &outer_key && ik.is_none())?;
                    let mut result = vec![TilePathStep::Record(tuple_field(flat_idx))];
                    result.extend_from_slice(&corr[1..]);
                    Some(result)
                }
            }
        }
    }
}

/// Flattens selected fields of a `SealedFunction` whose domain is a tuple into a single-level tuple domain.
///
/// Only outer fields whose indices appear in `indices_to_flatten` are expanded; all other outer
/// fields are passed through unchanged. For flattened fields, the inner `Record` fields are
/// spliced in sequence. Only one level is flattened; inner fields that are themselves records
/// are preserved unchanged.
///
/// For example, with domain `(_0: (_0: A, (_0: B, _1: C)), _1: (_0: D), _2: E)` and `indices_to_flatten = [0, 1]`,
/// the output domain is `(_0: A, _1: (_0: B, _1: C), _2: D, _3: E)`.
pub struct FlattenTupleDomain {
    /// Output tiling: `SealedFunction` with a single-level `Record` domain.
    tiling: Tiling,
    /// Input operator whose domain is a `Record`.
    input: Box<dyn TileOperator>,
    /// Maps output field index `i` to `(outer_field_key, inner_field_key_opt)`.
    ///
    /// `inner_field_key_opt = Some(k)` for flattened fields; `None` for pass-through fields.
    field_map: Vec<(String, Option<String>)>,
}

impl FlattenTupleDomain {
    /// Create a `FlattenTupleDomain` operator.
    ///
    /// Outer fields whose tuple index is in `indices_to_flatten` must be `Record`-typed and will
    /// be expanded; all other outer fields are passed through as-is. Panics if the input tiling
    /// is not a `SealedFunction` with a `Record` domain, or if a field marked for flattening is
    /// not a `Record`.
    pub fn new(input: Box<dyn TileOperator>, indices_to_flatten: Vec<usize>) -> Self {
        let Tiling::SealedFunction { domain, codomain } = input.tiling() else {
            panic!(
                "FlattenTupleDomain requires SealedFunction input, got {}",
                input.tiling()
            )
        };
        let Extent::Record(outer_fields) = domain else {
            panic!(
                "FlattenTupleDomain requires a Record domain, got {}",
                input.tiling()
            )
        };

        let mut sorted_outer: Vec<(&String, &Extent)> = outer_fields.iter().collect();
        sorted_outer.sort_by_key(|(k, _)| tuple_field_index(k));

        let mut field_map: Vec<(String, Option<String>)> = Vec::new();
        let mut flat_extent: HashMap<String, Extent> = HashMap::new();
        let mut out_idx = 0usize;

        for (outer_key, outer_extent) in sorted_outer {
            let outer_idx = tuple_field_index(outer_key);
            if indices_to_flatten.contains(&outer_idx) {
                let Extent::Record(inner_fields) = outer_extent else {
                    panic!(
                        "FlattenTupleDomain: outer field {outer_key} marked for flattening is not a Record, got {outer_extent}"
                    )
                };
                let mut sorted_inner: Vec<(&String, &Extent)> = inner_fields.iter().collect();
                sorted_inner.sort_by_key(|(k, _)| tuple_field_index(k));
                for (inner_key, inner_extent) in sorted_inner {
                    field_map.push((outer_key.clone(), Some(inner_key.clone())));
                    flat_extent.insert(tuple_field(out_idx), inner_extent.clone());
                    out_idx += 1;
                }
            } else {
                field_map.push((outer_key.clone(), None));
                flat_extent.insert(tuple_field(out_idx), outer_extent.clone());
                out_idx += 1;
            }
        }

        let tiling = Tiling::SealedFunction {
            domain: Extent::Record(flat_extent),
            codomain: codomain.clone(),
        };
        Self {
            tiling,
            input,
            field_map,
        }
    }
}

impl TileOperator for FlattenTupleDomain {
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
        Box::new(FlattenTupleDomainProducer {
            base: ProducerBase::new(FlattenTupleDomainProducer::alloc_id(), &self.tiling),
            input: self
                .input
                .subscribe(self.tiling().universal_guard(), consumer, scheduler),
            field_map: self.field_map.clone(),
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        flatten_result_correlation(self.input.result_correlation()?, &self.field_map)
    }
}

/// Producer for [`FlattenTupleDomain`]: rewrites a nested-tuple domain tile to a flat one.
struct FlattenTupleDomainProducer {
    base: ProducerBase,
    /// Upstream producer whose domain is a tuple of tuples.
    input: Box<dyn TileProducer>,
    /// Maps output field index `i` to `(outer_field_key, inner_field_key_opt)`.
    ///
    /// `inner_field_key_opt = Some(k)` for flattened fields; `None` for pass-through fields.
    field_map: Vec<(String, Option<String>)>,
}

impl TileProducer for FlattenTupleDomainProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        let Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate,
            deleted,
        } = input_tile
        else {
            panic!("FlattenTupleDomain expected SealedFunction tile");
        };
        let ColumnValue::Records(outer_cols) = domain else {
            panic!("FlattenTupleDomain expected Records domain column");
        };

        let flat_domain = ColumnValue::Records(
            self.field_map
                .iter()
                .enumerate()
                .map(|(out_idx, (outer_k, inner_k_opt))| {
                    let col = match inner_k_opt {
                        None => outer_cols
                            .get(outer_k)
                            .cloned()
                            .unwrap_or_else(|| panic!("missing outer column {outer_k}")),
                        Some(inner_k) => match outer_cols.get(outer_k) {
                            Some(ColumnValue::Records(inner_map)) => inner_map
                                .get(inner_k)
                                .cloned()
                                .unwrap_or_else(|| panic!("missing inner column {inner_k}")),
                            _ => panic!("outer column {outer_k} is not a Records ColumnValue"),
                        },
                    };
                    (tuple_field(out_idx), col)
                })
                .collect(),
        );

        let flat_pred = flatten_predicate(&domain_predicate, &self.field_map);

        Tile::SealedFunction {
            domain: flat_domain,
            codomain,
            domain_predicate: flat_pred,
            deleted,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let upstream_guard = match obsolete_guard {
            g if g.is_universal() => self.input.tiling().universal_guard(),
            g if g.is_empty() => self.input.tiling().empty_guard(),
            TileGuard::Function(FunctionGuard::Domain(pred)) => TileGuard::Function(
                FunctionGuard::Domain(unflatten_predicate(&pred, &self.field_map)),
            ),
            g => panic!("FlattenTupleDomain: unsupported obsolete guard: {g:?}"),
        };
        self.input.release(upstream_guard);
    }
}

/// A tile operator that always produces the same scalar value.
pub struct Constant {
    /// The fixed value emitted on every `get`.
    value: Value,
    /// The extent (type) of the produced value.
    pub extent: Extent,
    /// The tiling — always `Tiling::Scalar`.
    pub tiling: Tiling,
}

impl Constant {
    /// Create a new `Constant` operator for the given value.
    /// TODO `extent` should be `Extent::for_value(&value)`, but we don't have sufficient
    /// type derivation information for Value::ComputableFunction yet.
    pub fn new(value: Value, extent: Extent) -> Self {
        let tiling = Tiling::Scalar(extent.clone());
        Self {
            value,
            extent,
            tiling,
        }
    }
}

impl TileOperator for Constant {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node.annotate(format!("{}", self.value))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        _scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        consumer.notify();
        Box::new(ConstantProducer {
            base: ProducerBase::new(ConstantProducer::alloc_id(), &self.tiling),
            value: self.value.clone(),
            released: false,
        })
    }

    fn result_correlation(&self) -> Option<Vec<TilePathStep>> {
        if let Value::ComputableFunction(func) = &self.value {
            match func {
                FunctionDef::RecordField(f) => Some(vec![TilePathStep::Record(f.clone())]),
                _ => None,
            }
        } else {
            None
        }
    }
}

struct ConstantProducer {
    base: ProducerBase,
    value: Value,
    released: bool,
}

impl TileProducer for ConstantProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
        node.annotate(format!("{}", self.value))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        if self.released {
            self.tiling().empty_tile()
        } else {
            Tile::Scalar(ColumnValue::single(self.value.clone()))
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.is_universal() {
            self.released = true;
        }
    }
}

/// Unwraps a `SealedFunction` with `domain = Units(1)` to produce its single codomain element.
///
/// The input must have a `SealedFunction` tiling with `domain = Extent::Units(1)`.
/// The output tiling is the codomain of that `SealedFunction`.
pub struct ToScalar {
    /// The `SealedFunction`-typed input to unwrap.
    input: Box<dyn TileOperator>,
    /// Output tiling: the codomain of the input's `SealedFunction` tiling.
    tiling: Tiling,
}

impl ToScalar {
    /// Construct a `ToScalar` operator.
    ///
    /// Panics if `input` does not have a `SealedFunction` tiling.
    /// The domain `Units(1)` constraint is checked at `get`-time.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let tiling = input.tiling().codomain().unwrap_or_else(|| {
            panic!(
                "ToScalar input had non-function tiling {:?}",
                input.tiling()
            )
        });
        Self { input, tiling }
    }
}

impl TileOperator for ToScalar {
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
        let input_producer =
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler);
        Box::new(ToScalarProducer {
            base: ProducerBase::new(ToScalarProducer::alloc_id(), &self.tiling),
            input: input_producer,
        })
    }
}

struct ToScalarProducer {
    base: ProducerBase,
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
}

impl TileProducer for ToScalarProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_result = self.input.get(self.input.tiling().universal_guard());
        let Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate: _,
            ..
        } = input_result
        else {
            panic!("ToScalarProducer expected SealedFunction")
        };
        assert_eq!(domain, ColumnValue::Units(1));
        *codomain
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // The input is always read in full (universal guard), so only a universal
        // release can be propagated meaningfully.
        if obsolete_guard.is_universal() {
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

fn extract_hashmap_values<K: Clone + Eq + Hash, InputV, V, F: Fn(InputV) -> V>(
    source: HashMap<K, InputV>,
    f: F,
) -> HashMap<K, V> {
    source.into_iter().map(|(k, v)| (k.clone(), f(v))).collect()
}

// ---------------------------------------------------------------------------
// Recurse  (mutation-loop driver, single output port)
// ---------------------------------------------------------------------------

/// Loop driver for mutation accumulation.  Takes three inputs (init,
/// domain, recursive_input) and is itself a `TileOperator` whose
/// emitted tile is the *previous-accumulator* stream — `init` at
/// position 0, `recursive_input[i-1]` at position `i` for `i > 0`.
///
/// Op-conversion wraps `Recurse` in a `FanOut`; one branch is read by
/// the loop body as `acc_var`, and another branch is the loop's
/// external prev-acc stream.  The loop body itself is always a
/// `Record({step, tap_*})` and is wrapped in `FanOut(Memo(...))`: one
/// branch is projected to `.step` and feeds back into `recursive_input`
/// (closing the cycle), the other is the external output (exposed
/// directly as the running Record stream).  The body fan-out's
/// re-entrancy support ([`FanOutShared`]) lets the cyclic subscribe
/// and pull paths close back through it without `RefCell` aliasing.
///
/// **Inputs:**
/// 1. **init** — any tiling.  `Scalar(T)` for single-accumulator
///    loops, `Record({f_i: Scalar(T_i)})` for multi-accumulator loops
///    (the per-variable inits combined via `ScalarFanIn` by
///    op-conversion).  The codomain tiling of this `Recurse` mirrors
///    `init.tiling()` exactly.
/// 2. **domain** — a `SealedFunction(D, Scalar(D_elem))` (typically an
///    [`IterateExtent`]) whose codomain values enumerate the iteration
///    positions in canonical order.
/// 3. **recursive_input** — a `SealedFunction(D, init.tiling)`
///    carrying the new accumulator value at each position.  Wired in
///    after construction via the closure returned by
///    [`Recurse::recursive_input_setter`], since the body has to be
///    compiled around our output port before it's available.
///
/// **Output**: the *prev-acc* stream `SealedFunction(D, init.tiling)`
/// — `init` at position 0, `recursive_input[i-1]` at position
/// `i > 0`.  `acc_var` reads inside the loop body resolve to this
/// stream; surrounding lowering composes against this stream and
/// inlines any pending mutations to recover the right per-iteration
/// accumulator view (see [`crate::ccl::lower::lower_mutation_loop`]).
///
/// The body's external `Fun(D, Record({step, tap_*}))` output is
/// exposed directly; downstream lowering picks each accumulator off
/// via `Proj("step") [▷ Proj(i)] ▷ Last` and each feed via
/// `Proj("tap_*")`.
///
/// **Wiring order** (see `interpreter::operator_conversion`'s `Loop` arm):
/// ```text
/// 1. Construct Recurse with init and domain inputs.
/// 2. Grab `recursive_input_setter` BEFORE moving Recurse into a Box —
///    this is the only way to wire recursive_input later, since the
///    body needs Recurse already wrapped as a TileOperator.
/// 3. Wrap Recurse in `FanOut`; use one of its branches as acc_var.
/// 4. Compile loop_body in a scope where `acc_var` resolves to that
///    FanOut branch — its output is the new-accumulator Record stream.
/// 5. Wrap the body in `FanOut(Memo(...))`; call the setter from step 2
///    with the `.step` projection of one branch (closing the cycle).
///    Use another branch as the external output (exposed directly).
/// ```
///
/// **Cycle convergence.**  `RecurseProducer::get_impl` drives the cycle
/// by pulling `recursive_input` once per call.  Because `Recurse` is
/// wrapped in a `FanOut`, only one `RecurseProducer` is ever
/// constructed; the body's `acc_var` reads close back through that
/// fan-out, not through a fresh call into `get_impl`, so there's no
/// in-process re-entrance into the producer.  The body fan-out's own
/// re-entrancy support makes the re-entrant pull on `recursive_input`
/// itself safe: the outer call has the inner producer taken out, so
/// the inner pull sees `producer = None` and serves from the
/// fan-out's `cached_tile` (which is the body's prior emission —
/// exactly what `recurse_step` needs to record into `known` to
/// advance the cycle).
pub struct Recurse {
    /// Init operator, set at construction and subscribed on `subscribe`.
    init_op: Box<dyn TileOperator>,
    /// Domain operator, set at construction and subscribed on `subscribe`.
    domain_op: Box<dyn TileOperator>,
    /// Recursive input — the body fan-out's branch back into us.  Wired
    /// in by the closure returned from [`Recurse::recursive_input_setter`]
    /// after the loop body has been compiled.  Behind `Rc<RefCell<...>>`
    /// so the setter can mutate it after `self` has been moved into a
    /// `Box<dyn TileOperator>` — the body lives downstream of us in
    /// the op graph and can only be wired in once we've been boxed for
    /// use as a `TileOperator`.
    recursive_input_op: Rc<RefCell<Option<Box<dyn TileOperator>>>>,
    output_tiling: Tiling,
    domain_extent: Extent,
    /// The tiling of the accumulator (mirrors `init.tiling()`).  Drives
    /// the codomain shape of emitted tiles: a [`Tiling::Scalar`] codomain
    /// emits `Tile::Scalar`, a [`Tiling::Record`] codomain emits
    /// `Tile::Record` with per-field scalar sub-tiles built by
    /// [`build_codomain_tile_from_values`].  See [`Recurse::new`].
    codomain_tiling: Tiling,
}

impl Recurse {
    /// Construct a new `Recurse` with `init` and `domain` inputs wired.
    /// The recursive input is wired in later via the closure returned
    /// from [`Recurse::recursive_input_setter`], once the loop body
    /// has been compiled around our output port.
    ///
    /// The codomain tiling of this `Recurse` mirrors `init.tiling()`
    /// exactly, so a `Tiling::Scalar(T)` init produces a `SealedFunction(D,
    /// Scalar(T))` output (single-accumulator scalar Joins) while a
    /// `Tiling::Record({f_i: Scalar(T_i)})` init produces `SealedFunction(D,
    /// Record({f_i: Scalar(T_i)}))` — the shape used by multi-accumulator
    /// mutation loops where op-conversion combines the per-variable inits
    /// into a single `ScalarFanIn` so one `Recurse` drives every cycle.
    pub fn new(init: Box<dyn TileOperator>, domain: Box<dyn TileOperator>) -> Self {
        let domain_extent = match domain.tiling() {
            Tiling::SealedFunction { domain, .. } => domain.clone(),
            other => panic!("Recurse domain must have SealedFunction tiling, got {other}"),
        };
        let codomain_tiling = init.tiling().clone();
        // `Recurse`'s codomain mirrors `init.tiling()`, and downstream
        // [`build_codomain_tile_from_values`] only knows how to construct
        // `Tile::Scalar` and `Tile::Record` codomains from value vectors —
        // anything else (SealedFunction, CurriedFunction, Aggregation)
        // panics deep inside the producer.  Catch the misuse here, where
        // the failure points at the `Recurse::new` caller (op-conversion's
        // `Loop` arm or a future caller) rather than at a per-tile
        // construction failure many iterations later.
        debug_assert!(
            codomain_tiling.is_scalar(),
            "Recurse init must have a scalar or scalar-record tiling, got {codomain_tiling}",
        );
        let output_tiling = Tiling::SealedFunction {
            domain: domain_extent.clone(),
            codomain: Box::new(codomain_tiling.clone()),
        };
        Self {
            init_op: init,
            domain_op: domain,
            recursive_input_op: Rc::new(RefCell::new(None)),
            output_tiling,
            domain_extent,
            codomain_tiling,
        }
    }

    /// Return a closure that wires the recursive input — typically the
    /// compiled loop body's `FanOut` branch, after the body has been
    /// built around `Recurse`.
    ///
    /// Returned as a setter rather than a `&self` method so that
    /// op-conversion can hold onto the setter after `Recurse` itself
    /// has been moved into a `Box<dyn TileOperator>` (and from there
    /// into the `FanOut` that splits the prev-acc stream to its
    /// consumers).  The body can't be compiled until `Recurse` is a
    /// `TileOperator` (it reads `acc_var` = our output port), so this
    /// construction-time ordering is the natural one.
    pub fn recursive_input_setter(&self) -> impl FnOnce(Box<dyn TileOperator>) + use<> {
        let slot = self.recursive_input_op.clone();
        move |op| {
            *slot.borrow_mut() = Some(op);
        }
    }
}

impl TileOperator for Recurse {
    fn tiling(&self) -> &Tiling {
        &self.output_tiling
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        // Kick the body chain immediately: the value at position 0 (the
        // `init` value) is always available, so this port has data to
        // serve as soon as it is subscribed.  This is what lets the
        // surrounding drain loop make progress on its first iteration —
        // without this notify, the body's subscription would idle until
        // something else notified it.
        consumer.notify();
        let init_guard = self.init_op.tiling().universal_guard();
        let init_producer = self
            .init_op
            .subscribe(init_guard, Box::new(|| {}), scheduler);
        let domain_guard = self.domain_op.tiling().universal_guard();
        let domain_producer = self
            .domain_op
            .subscribe(domain_guard, Box::new(|| {}), scheduler);
        let mut recursive_input_op = self
            .recursive_input_op
            .borrow_mut()
            .take()
            .expect("Recurse: recursive_input not wired (call recursive_input_setter)");
        let recursive_input_guard = recursive_input_op.tiling().universal_guard();
        let recursive_input_producer =
            recursive_input_op.subscribe(recursive_input_guard, Box::new(|| {}), scheduler);
        Box::new(RecurseProducer {
            base: ProducerBase::new(RecurseProducer::alloc_id(), &self.output_tiling),
            init_producer,
            domain_producer,
            recursive_input_producer,
            init_value: None,
            domain_values: Vec::new(),
            known: HashMap::new(),
            recorded_positions: HashSet::new(),
            domain_extent: self.domain_extent.clone(),
            codomain_tiling: self.codomain_tiling.clone(),
            released_cycle_positions: Predicate::False,
            recursive_input_released: Predicate::False,
        })
    }
}

struct RecurseProducer {
    base: ProducerBase,
    init_producer: Box<dyn TileProducer>,
    domain_producer: Box<dyn TileProducer>,
    recursive_input_producer: Box<dyn TileProducer>,
    /// Cached `init` value — fetched once on the first iteration step
    /// (`init` may itself be a previous loop's scalar Join, which
    /// can take several pulls to resolve under the single-step model).
    /// For multi-accumulator loops this is a [`Value::Record`] packing
    /// every accumulator's initial value; for scalar loops it is a
    /// primitive value.  Mirrors the body's per-iteration emission shape.
    init_value: Option<Value>,
    /// Cached `domain` codomain values, in canonical order.  Maintained
    /// *cumulatively*: old positions stay even after the body has
    /// released them, so the index-based prev-acc lookup below
    /// (`init` at index 0, `known[domain_values[i-1]]` at index `i`)
    /// stays stable as the source frontier advances.
    domain_values: Vec<Value>,
    /// Recorded `recursive_input` values, indexed by domain value.
    /// Each `recurse_step` records observed (domain, codomain) pairs
    /// here so the next prev-acc tile emission can serve them.  Each
    /// value matches `codomain_tiling`'s shape (scalar primitive or
    /// `Value::Record` for multi-accumulator loops).
    known: HashMap<Value, Value>,
    /// Set of domain values whose `recursive_input` value has been
    /// observed at some point.  Grows monotonically — never shrinks,
    /// even when [`Self::release_impl`] drops the corresponding entry
    /// from `known` after downstream consumers release their successor
    /// positions.  The `fully_drained` check (in [`Self::get_impl`])
    /// uses this to detect convergence; using `known.contains_key` for
    /// that purpose would break once incremental release starts
    /// freeing entries before terminal.
    recorded_positions: HashSet<Value>,
    domain_extent: Extent,
    /// Tiling of the codomain.  Drives the per-pull tile construction
    /// in [`Self::get_impl`] via [`build_codomain_tile_from_values`].
    codomain_tiling: Tiling,
    /// Cumulative predicate over cycle output positions that downstream
    /// consumers have released.  Each release call unions the new
    /// guard into this set; [`Self::release_impl`] uses it both as the
    /// release predicate to forward to `domain_producer` (cycle and
    /// source share a domain) and — shifted by one position — as the
    /// predicate to forward to `recursive_input_producer` and to drop
    /// from `known`.  Streaming sources rely on this to free upstream
    /// state as positions are consumed, rather than holding everything
    /// until source convergence.
    released_cycle_positions: Predicate,
    /// Cumulative predicate already forwarded to
    /// `recursive_input_producer` (the *shifted* form of
    /// `released_cycle_positions`).  Tracked so each `release_impl`
    /// call only forwards the *new* shifted positions rather than the
    /// whole cumulative set every time.  `release` is idempotent so
    /// double-release would be safe, just wasteful for long-running
    /// streams.
    recursive_input_released: Predicate,
}

impl RecurseProducer {
    /// Pull `init_producer` (once it converges to a single scalar) and
    /// cache the result.  Returns `None` if `init` is still un-resolved
    /// — happens when `init` is itself a previous loop's scalar Join
    /// (a sequential `for` chain) which can take several pulls to
    /// converge.  Callers handle `None` by bailing out with a
    /// non-terminal empty tile; the outer consumer's pull loop will
    /// retry.
    fn ensure_init_value(&mut self) -> Option<Value> {
        if let Some(v) = &self.init_value {
            return Some(v.clone());
        }
        let tile = self
            .init_producer
            .get(self.init_producer.tiling().universal_guard());
        let resolved = scalar_tile_to_column_value(tile).as_single();
        if let Some(v) = &resolved {
            self.init_value = Some(v.clone());
        }
        resolved
    }

    /// Pull `domain_producer` and append any newly-seen positions to
    /// `domain_values` (cumulatively — old positions stay even after
    /// the body has released them, so index-based prev-acc lookup
    /// stays stable).  Returns whether the domain is now terminal.
    fn refresh_domain_values(&mut self) -> bool {
        let tile = self
            .domain_producer
            .get(self.domain_producer.tiling().universal_guard());
        let domain_terminal = tile.is_terminal();
        let Tile::SealedFunction { codomain, .. } = tile else {
            panic!("Recurse: domain must produce a SealedFunction tile");
        };
        let cv = scalar_tile_to_column_value(*codomain);
        // Append any positions we haven't already seen.  Domain emits in
        // canonical order and positions never disappear from our
        // cumulative list, so an O(N) "is this already present" check
        // is fine — a HashSet would just trade one allocation for another.
        for i in 0..cv.len() {
            let v = cv.index_at(i);
            if !self.domain_values.contains(&v) {
                self.domain_values.push(v);
            }
        }
        domain_terminal
    }

    /// Pull `recursive_input_producer` once and record any newly-observed
    /// positions into `known`.  This is a *re-entrant* pull through the
    /// body fan-out: the outer caller (a `FanOut` branch on this
    /// `Recurse`) has the inner producer taken out, so this pull serves
    /// from the body fan-out's cached tile (the body's prior emission)
    /// rather than re-driving body.
    ///
    /// **Release happens out-of-band in [`Self::release_impl`].**
    /// `recurse_step` only records.  When a downstream consumer
    /// releases cycle positions, `release_impl` forwards a
    /// shifted-by-one release into `recursive_input_producer` (so the
    /// body fan-out's recursive-input branch can advance its
    /// per-branch release predicate, eventually freeing the body's
    /// cached tile and the source).  The universal release on
    /// `fully_drained` (in `get_impl`) catches anything left at
    /// convergence.
    fn recurse_step(&mut self) {
        let universal = self.recursive_input_producer.tiling().universal_guard();
        let mut tile = self.recursive_input_producer.get(universal);
        tile.compact();
        let Tile::SealedFunction {
            domain, codomain, ..
        } = tile
        else {
            panic!("Recurse: recursive_input must produce SealedFunction tiles");
        };
        let cv = scalar_tile_to_column_value(*codomain);
        for i in 0..domain.len() {
            let dval = domain.index_at(i);
            if self.recorded_positions.contains(&dval) {
                continue;
            }
            self.recorded_positions.insert(dval.clone());
            self.known.insert(dval, cv.index_at(i));
        }
    }
}

impl TileProducer for RecurseProducer {
    impl_producer_base!();

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // `init` may be a previous loop's scalar Join — under the
        // single-step model, that producer may need several pulls to
        // converge.  Bail out early with a non-terminal empty tile if
        // so; the outer consumer's loop will keep calling `get` until
        // everything is terminal.
        let Some(init_value) = self.ensure_init_value() else {
            // `Tiling::empty_tile` produces the structurally-valid empty
            // SealedFunction with `Predicate::False` we want as the
            // "not ready yet" signal.  The outer consumer's loop will
            // retry on the next pull.
            return self.tiling().empty_tile();
        };
        let domain_terminal = self.refresh_domain_values();
        self.recurse_step();

        // Emit the full prev_acc tile (every domain position we've seen
        // with a known prev-acc value).  We don't filter by what
        // consumers have released — the surrounding `FanOut` does
        // per-branch release filtering on the way out, so each branch
        // sees only what its own consumer still cares about.
        let mut domain_out: Vec<Value> = Vec::new();
        let mut codomain_out: Vec<Value> = Vec::new();
        for (i, dval) in self.domain_values.iter().enumerate() {
            let value = if i == 0 {
                init_value.clone()
            } else {
                let prev_dval = &self.domain_values[i - 1];
                match self.known.get(prev_dval) {
                    Some(v) => v.clone(),
                    None => continue, // Not yet computed — skip until it's filled in.
                }
            };
            domain_out.push(dval.clone());
            codomain_out.push(value);
        }
        let domain = ColumnValue::from_values(domain_out, &self.domain_extent);
        let codomain_tile = build_codomain_tile_from_values(codomain_out, &self.codomain_tiling);
        // The shifted prev_acc stream is fully drained iff the source's
        // `domain` operator declared its tile terminal *and* every
        // announced position has a `known` entry (i.e. `recursive_input`
        // delivered a value for it).  At that point we can advertise
        // `Predicate::True` so downstream operators (FanIn, ExtractLast,
        // etc.) see the tile as terminal.  Otherwise we fall back to the
        // explicit position list — which signals "these positions are
        // present, more may arrive".
        // Convergence: every announced position has had its
        // `recursive_input` value recorded.  We track this against
        // `recorded_positions` rather than `known` because
        // `release_impl` may have already evicted entries from `known`
        // whose successor cycle positions were released by downstream
        // — those positions were still seen, just no longer needed
        // for emission.
        let fully_drained = domain_terminal
            && self
                .domain_values
                .iter()
                .all(|v| self.recorded_positions.contains(v));
        let domain_predicate = if fully_drained {
            Predicate::True
        } else if domain.is_empty() {
            Predicate::False
        } else {
            Predicate::from_column_value(&domain)
        };
        // On convergence, universally release both internal subscriptions
        // so the source sees a `Predicate::True` release from this
        // `Recurse` group.  A `DataSource`'s released-predicate is the
        // intersection across every subscriber; if `domain_producer`
        // (our own `IterateExtent` over the source) and
        // `recursive_input_producer` (the body fan-out's branch back to
        // us) don't both reach universal, the source's intersection
        // stays narrower than `True`.  We do it here — not in
        // `release_impl` — because the public consumer (e.g. `ExtractLast`
        // wrapping the body fan-out's other branch) doesn't necessarily
        // release us when the cycle finishes.  Release is idempotent, so
        // doing it on every post-convergence pull is fine.
        if fully_drained {
            self.domain_producer
                .release(self.domain_producer.tiling().universal_guard());
            self.recursive_input_producer
                .release(self.recursive_input_producer.tiling().universal_guard());
        }
        Tile::SealedFunction {
            domain_predicate,
            domain,
            codomain: Box::new(codomain_tile),
            deleted: BitSet::new(),
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        // Universal release: forward universally to both upstream subs.
        // (Idempotent with the `fully_drained` path in `get_impl`, which
        // also fires universal releases on convergence.)
        if obsolete_guard.is_universal() {
            self.released_cycle_positions = Predicate::True;
            self.recursive_input_released = Predicate::True;
            self.domain_producer
                .release(self.domain_producer.tiling().universal_guard());
            self.recursive_input_producer
                .release(self.recursive_input_producer.tiling().universal_guard());
            self.known.clear();
            return;
        }

        // Per-position release: a downstream consumer has signalled
        // that some cycle positions are no longer needed.  Three things
        // to do:
        //
        //   1. Forward the release to `domain_producer` directly —
        //      we and the source share a domain, so the cycle release
        //      and the source release are the same predicate.
        //
        //   2. Forward a *shifted* release to `recursive_input_producer`:
        //      cycle position `i` was emitted using
        //      `known[domain_values[i-1]]`, so releasing cycle
        //      position `i` makes `recursive_input` at
        //      `domain_values[i-1]` obsolete (for `i > 0`; the very
        //      first position uses `init_value`, not a recursive_input
        //      value).
        //
        //   3. Drop the corresponding entries from `known`, since
        //      those values are no longer needed for prev-acc lookup
        //      of any unreleased cycle position.
        let new_pred = match &obsolete_guard {
            TileGuard::Function(FunctionGuard::Domain(p)) => p.clone(),
            other => panic!("Recurse: unsupported release guard {other:?}"),
        };
        self.released_cycle_positions = self.released_cycle_positions.union(&new_pred);
        self.domain_producer
            .release(TileGuard::Function(FunctionGuard::Domain(new_pred)));

        // Compute the shifted predicate over `domain_values`:
        // predecessors of positions newly released as cycle outputs
        // and not yet released as recursive_input positions.  Done by
        // walking `domain_values` rather than by a generic predicate
        // shift because the "shift" depends on the source's actual
        // emission order, which lives in this Vec.
        let mut new_shifted: Vec<Value> = Vec::new();
        for i in 1..self.domain_values.len() {
            let dval = &self.domain_values[i];
            if !self.released_cycle_positions.contains(dval) {
                continue;
            }
            let pred_dval = &self.domain_values[i - 1];
            if self.recursive_input_released.contains(pred_dval) {
                continue;
            }
            new_shifted.push(pred_dval.clone());
        }
        if !new_shifted.is_empty() {
            let cv = ColumnValue::from_values(new_shifted.clone(), &self.domain_extent);
            let shifted_pred = Predicate::from_column_value(&cv);
            self.recursive_input_released = self.recursive_input_released.union(&shifted_pred);
            self.recursive_input_producer
                .release(TileGuard::Function(FunctionGuard::Domain(shifted_pred)));
            for v in new_shifted {
                self.known.remove(&v);
            }
        }
    }
}

/// Build a codomain [`Tile`] from a stream of accumulator values laid out
/// in domain-position order, mirroring `tiling`'s shape.
///
/// - For [`Tiling::Scalar`], emit `Tile::Scalar(ColumnValue::from_values(…))` —
///   the existing scalar-Recurse path.
/// - For [`Tiling::Record`], split each [`Value::Record`] into per-field
///   value columns and recurse, producing `Tile::Record({field: Tile::Scalar(…)})`
///   that matches what [`FanIn`] emits for the body of a multi-accumulator
///   mutation loop (so `recursive_input` feeds back tile-shape-compatibly
///   with our output).
///
/// Panics on tilings we don't currently produce as a `Recurse` codomain.
fn build_codomain_tile_from_values(values: Vec<Value>, tiling: &Tiling) -> Tile {
    match tiling {
        Tiling::Scalar(extent) => Tile::Scalar(ColumnValue::from_values(values, extent)),
        Tiling::Record(fields) => {
            let mut field_tiles: HashMap<String, Tile> = HashMap::with_capacity(fields.len());
            for (field_name, field_tiling) in fields {
                let field_values: Vec<Value> = values
                    .iter()
                    .map(|v| match v {
                        Value::Record(r) => r
                            .get(field_name)
                            .cloned()
                            .expect("Record value missing expected field"),
                        other => panic!(
                            "build_codomain_tile_from_values: expected Value::Record, got {other:?}"
                        ),
                    })
                    .collect();
                field_tiles.insert(
                    field_name.clone(),
                    build_codomain_tile_from_values(field_values, field_tiling),
                );
            }
            Tile::Record(field_tiles)
        }
        other => panic!("Recurse: unsupported codomain tiling {other}"),
    }
}

// ---------------------------------------------------------------------------
// ExtractLast / ExtractLastProducer
// ---------------------------------------------------------------------------

/// Extracts the last value from a [`Recurse`] (or any `SealedFunction`) output,
/// converting the accumulated `SealedFunction` tiling back to a `Scalar`.
///
/// When the source becomes terminal but emits no values (the empty-source
/// case, e.g. `for i in []: x += 1`), the `default` operator's scalar value
/// is emitted instead.  This keeps mutation loops total: the post-loop
/// accumulator always has a defined value, equal to the loop's initial
/// value when the body never ran.
///
/// Used as the terminal stage of a loop: `ExtractLast(body.step, init)`.
pub struct ExtractLast {
    /// Operator producing the `SealedFunction` tiling to extract from.
    source: Box<dyn TileOperator>,
    /// Fallback scalar operator, pulled when `source` is terminal and
    /// emits zero values.  Must have a `Scalar` tiling whose extent
    /// matches `source`'s codomain extent.
    default: Box<dyn TileOperator>,
    /// Output tiling — the codomain of the source SealedFunction (always `Scalar`).
    tiling: Tiling,
}

impl ExtractLast {
    /// Construct a new `ExtractLast` wrapping `source`, with `default`
    /// as the fallback for the empty-source case.
    ///
    /// `source` must have a `SealedFunction` tiling and `default` must
    /// have a `Scalar` tiling with the same extent as `source`'s codomain.
    /// The output tiling becomes that scalar codomain.
    pub fn new(source: Box<dyn TileOperator>, default: Box<dyn TileOperator>) -> Self {
        let tiling = match source.tiling() {
            Tiling::SealedFunction { codomain, .. } => *codomain.clone(),
            other => panic!("ExtractLast source must have SealedFunction tiling, got {other}"),
        };
        debug_assert_eq!(
            default.tiling(),
            &tiling,
            "ExtractLast default tiling must match source codomain tiling",
        );
        Self {
            source,
            default,
            tiling,
        }
    }
}

impl TileOperator for ExtractLast {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("source", self.source.inspect(opts))
            .child("default", self.default.inspect(opts))
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
        let default_producer = self.default.subscribe(
            self.default.tiling().universal_guard(),
            Box::new(|| {}),
            scheduler,
        );
        Box::new(ExtractLastProducer {
            base: ProducerBase::new(ExtractLastProducer::alloc_id(), &self.tiling),
            source: source_producer,
            default: default_producer,
            final_value: None,
            released: false,
        })
    }
}

struct ExtractLastProducer {
    base: ProducerBase,
    source: Box<dyn TileProducer>,
    /// Default-value producer, pulled when `source` becomes terminal
    /// and emits zero values.  Subscribed eagerly alongside `source`;
    /// `get` is deferred until we know we need it.
    default: Box<dyn TileProducer>,
    /// Cached final scalar value.  `None` until the source becomes
    /// terminal; `Some(_)` thereafter.  Every subsequent `get` returns
    /// this same value until the consumer releases us with a universal
    /// guard — which then sets [`Self::released`] and we go quiet.
    /// Same emit-until-released protocol as [`Constant`], so consumers
    /// that pull repeatedly (e.g. sibling `Last` projections off a
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

impl TileProducer for ExtractLastProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("source", self.source.inspect(opts))
            .child("default", self.default.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let empty = Tile::Scalar(ColumnValue::from_values(vec![], &self.tiling().extent()));
        if self.released {
            return empty;
        }
        // Already extracted: keep re-emitting the same scalar until we
        // are released.  Downstream `Memo` typically releases on first
        // sight of a non-empty tile, so this branch only stays active
        // across pulls when the consumer doesn't release immediately
        // (e.g. while a sibling pipeline is still converging).
        if let Some(v) = &self.final_value {
            return Tile::Scalar(ColumnValue::single(v.clone()));
        }
        let source_tiling = self.source.tiling().clone();
        let source_tile = self.source.get(source_tiling.universal_guard());
        if !source_tile.is_terminal() {
            // Source hasn't converged yet — emit an empty scalar of the
            // correct extent.  Our own tiling *is* the source's codomain
            // (always `Scalar`), so its extent gives us the value-space
            // directly without going through `Tiling::codomain` (which
            // would return `None` for a `Scalar`).
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
            panic!("ExtractLast source must be a SealedFunction tile");
        };
        let cv = scalar_tile_to_column_value(*codomain);
        let n = cv.len();
        // Try to extract the last non-deleted value from the source.
        // TODO don't assume sorting; we need to sort by the domain value instead.
        if let Some(last_idx) = (0..n).rev().find(|&i| !deleted.contains(i)) {
            let value = cv.index_at(last_idx);
            self.final_value = Some(value.clone());
            return Tile::Scalar(ColumnValue::single(value));
        }
        // Source is terminal *and* empty (the loop body ran zero
        // times).  Pull the default scalar and emit that instead, then
        // release the default so its upstream chain can release too.
        let default_tiling = self.default.tiling().clone();
        let default_tile = self.default.get(default_tiling.universal_guard());
        match scalar_tile_to_column_value(default_tile).as_single() {
            Some(value) => {
                self.default.release(default_tiling.universal_guard());
                self.final_value = Some(value.clone());
                Tile::Scalar(ColumnValue::single(value))
            }
            // Default hasn't converged yet — emit empty.  Outer pull
            // loop will retry; once default resolves, we'll cache it.
            None => empty,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.is_universal() {
            self.released = true;
            self.source.release(self.source.tiling().universal_guard());
            self.default
                .release(self.default.tiling().universal_guard());
        }
    }
}

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
    use intervalsets::MaybeEmpty;
    use intervalsets::ops::Contains;

    use std::cell::RefCell;
    use std::rc::Rc;

    use super::*;
    use crate::interpreter::{ColumnValue, Extent, Value};

    /// Helper: extract the `IntervalSet<usize>` from a `UIntRange` extent.
    fn uint_range_set(extent: &Extent) -> &IntervalSet<usize> {
        let Extent::UIntRange(s) = extent else {
            panic!("expected UIntRange, got {extent:?}");
        };
        s
    }

    /// `Predicate::True` releases everything — extent becomes empty.
    #[test]
    fn release_extent_predicate_true_clears_uint_range() {
        let mut extent = Extent::uint_range(5); // [0, 4]
        release_extent(&mut extent, &Predicate::True, "");
        assert!(
            uint_range_set(&extent).is_empty(),
            "True release should empty the extent"
        );
    }

    /// `Predicate::False` releases nothing — extent is unchanged.
    #[test]
    fn release_extent_predicate_false_is_noop() {
        let mut extent = Extent::uint_range(5); // [0, 4]
        release_extent(&mut extent, &Predicate::False, "");
        let s = uint_range_set(&extent);
        for i in 0..5usize {
            assert!(s.contains(&i), "{i} should still be present");
        }
    }

    /// `Predicate::LessThanEq(v)` releases [0, v] inclusive.
    #[test]
    fn release_extent_less_than_eq_releases_prefix() {
        let mut extent = Extent::uint_range(10); // [0, 9]
        release_extent(&mut extent, &Predicate::LessThanEq(Value::UInt(4)), "");
        let s = uint_range_set(&extent);
        for i in 0..=4usize {
            assert!(!s.contains(&i), "{i} should be released");
        }
        for i in 5..10usize {
            assert!(s.contains(&i), "{i} should remain");
        }
    }

    /// `Predicate::Intervals` with only bounded intervals subtracts each one.
    #[test]
    fn release_extent_bounded_intervals_predicate() {
        // Release {2, 3} ∪ {7} from [0, 9].
        let p = Predicate::from_column_value(&ColumnValue::UInts(vec![2, 3, 7]));
        let mut extent = Extent::uint_range(10);
        release_extent(&mut extent, &p, "");
        let s = uint_range_set(&extent);
        assert!(!s.contains(&2usize), "2 should be released");
        assert!(!s.contains(&3usize), "3 should be released");
        assert!(!s.contains(&7usize), "7 should be released");
        for i in [0, 1, 4, 5, 6, 8, 9usize] {
            assert!(s.contains(&i), "{i} should remain");
        }
    }

    /// `Predicate::Intervals` with a right-unbounded interval (e.g. [5, +∞))
    /// releases everything from 5 to the end of the extent.
    #[test]
    fn release_extent_right_unbounded_intervals_predicate() {
        // LessThanEq(4) union True = True, so build the right-unbounded interval
        // directly via the complement: values NOT ≤ 4 are > 4, i.e. [5, +∞).
        // We exercise this by unioning {5} with a GreaterThan-style Intervals predicate.
        // Simplest path: union two Intervals so the result stays as Intervals.
        let p = Predicate::from_column_value(&ColumnValue::UInts(vec![5])).union(
            &Predicate::from_column_value(&ColumnValue::UInts(vec![6, 7, 8, 9, 10])),
        );
        let mut extent = Extent::uint_range(10); // [0, 9]
        release_extent(&mut extent, &p, "");
        let s = uint_range_set(&extent);
        for i in 0..5usize {
            assert!(s.contains(&i), "{i} should remain");
        }
        for i in 5..10usize {
            assert!(!s.contains(&i), "{i} should be released");
        }
    }

    /// Releasing a `Predicate::Intervals` that contains a left-unbounded interval
    /// (produced by `Predicate::union(LessThanEq, Intervals)`) must subtract the
    /// full interval from the `UIntRange` extent, not silently drop it.
    #[test]
    fn release_extent_left_unbounded_intervals_predicate() {
        // Build the predicate that union() produces from LessThanEq(3) | {7}:
        // result is Predicate::Intervals containing (-∞, 3] ∪ {7}.
        let p = Predicate::LessThanEq(Value::UInt(3))
            .union(&Predicate::from_column_value(&ColumnValue::UInts(vec![7])));

        let mut extent = Extent::uint_range(10); // [0, 9]
        release_extent(&mut extent, &p, "");

        // After releasing (-∞, 3] ∪ {7}, remaining should be {4, 5, 6, 8, 9}.
        let Extent::UIntRange(ref remaining) = extent else {
            panic!("expected UIntRange");
        };
        assert!(!remaining.contains(&0usize), "0 should be released");
        assert!(!remaining.contains(&3usize), "3 should be released");
        assert!(remaining.contains(&4usize), "4 should remain");
        assert!(!remaining.contains(&7usize), "7 should be released");
        assert!(remaining.contains(&9usize), "9 should remain");
    }

    #[test]
    fn iterate_extent_fragmented_uint_range() {
        // Simulate [0,5) with indices 1,2,3 already released → {[0,0],[4,4]}
        let mut extent = Extent::uint_range(5);
        // release [1,3]
        if let Extent::UIntRange(ref mut set) = extent {
            let to_remove = IntervalSet::from(Interval::closed(1usize, 3usize));
            *set = set.difference(&to_remove);
        }
        let tiling = Tiling::SealedFunction {
            domain: extent.clone(),
            codomain: Box::new(Tiling::Scalar(extent.clone())),
        };
        let mut producer = IterateExtentProducer {
            base: ProducerBase::new(0, &tiling),
            extent,
            released: Predicate::False,
        };
        let tile = producer.get(producer.tiling().universal_guard());
        let Tile::SealedFunction { domain, .. } = tile else {
            panic!()
        };
        let ColumnValue::UInts(vals) = domain else {
            panic!()
        };
        assert_eq!(vals, vec![0, 4]);
    }

    /// A test helper TileProducer that returns a pre-determined tile.
    /// Useful for testing TileOperators by injecting tiles directly.
    struct TestTileProducer {
        base: ProducerBase,
        tile: Tile,
    }

    impl TestTileProducer {
        fn new(tile: Tile, tiling: Tiling) -> Self {
            Self {
                base: ProducerBase::new(Self::alloc_id(), &tiling),
                tile,
            }
        }
    }

    impl TileProducer for TestTileProducer {
        impl_producer_base!();

        fn add_inspect_children(&self, node: InspectNode, _opts: &VizOptions) -> InspectNode {
            node
        }

        fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
            self.tile.clone()
        }

        fn release_impl(&mut self, _obsolete_guard: TileGuard) {}
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

    #[test]
    fn uncurry_producer_basic() {
        // Test UncurryProducer.get_impl with a simple CurriedFunction
        //
        // Creates a CurriedFunction with:
        // - domain1: [1, 2] (two keys)
        // - offsets: [0, 2] (key 1 has 2 items, key 2 has 1 item [implicit end at domain2.len()])
        // - domain2: [10, 20, 30] (flattened second-level domain)
        // - codomain: [100, 200, 300] (flattened codomain)
        //
        // Expected expansion_indices: [0, 0, 1] (key 0 repeated 2 times, key 1 repeated 1 time)
        // Expected expanded_domain1: [1, 1, 2]
        // Expected pair domain: Record with _0=[1,1,2] and _1=[10,20,30]

        let curried_tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![1, 2]),
            offsets: ColumnValue::UInts(vec![0, 2]),
            domain2: ColumnValue::UInts(vec![10, 20, 30]),
            codomain: ColumnValue::UInts(vec![100, 200, 300]),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };

        let curried_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };

        let input_producer = TestTileProducer::new(curried_tile, curried_tiling.clone());

        // Create UncurryProducer with the test producer as input
        let output_tiling = Tiling::SealedFunction {
            domain: Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::UInt)),
                    (tuple_field(1), Extent::Base(BaseType::UInt)),
                ]
                .into_iter()
                .collect(),
            ),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::UInt))),
        };

        let mut uncurry = UncurryProducer {
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
        };

        // Get the result from UncurryProducer
        let result = uncurry.get(uncurry.tiling().universal_guard());

        // Verify the result is a SealedFunction
        match result {
            Tile::SealedFunction {
                domain,
                codomain,
                domain_predicate,
                ..
            } => {
                // Verify the domain is a Record with fields _0 and _1
                match domain {
                    ColumnValue::Records(fields) => {
                        assert_eq!(fields.len(), 2, "domain should have 2 fields");
                        assert!(
                            fields.contains_key(&tuple_field(0)),
                            "domain should have _0 field"
                        );
                        assert!(
                            fields.contains_key(&tuple_field(1)),
                            "domain should have _1 field"
                        );

                        // Verify expanded_domain1 (field _0): [1, 1, 2]
                        let field_0 = &fields[&tuple_field(0)];
                        if let ColumnValue::UInts(vals) = field_0 {
                            assert_eq!(vals, &vec![1, 1, 2], "_0 should be expanded domain1");
                        } else {
                            panic!("_0 field should be UInts");
                        }

                        // Verify domain2 (field _1): [10, 20, 30]
                        let field_1 = &fields[&tuple_field(1)];
                        if let ColumnValue::UInts(vals) = field_1 {
                            assert_eq!(vals, &vec![10, 20, 30], "_1 should be domain2");
                        } else {
                            panic!("_1 field should be UInts");
                        }
                    }
                    _ => panic!("domain should be a Record"),
                }

                // Verify codomain is a Scalar
                match *codomain {
                    Tile::Scalar(ColumnValue::UInts(ref vals)) => {
                        assert_eq!(vals, &vec![100, 200, 300], "codomain should match original");
                    }
                    _ => panic!("codomain should be Scalar(UInts)"),
                }

                // Verify domain_predicate is transformed appropriately
                assert_eq!(
                    domain_predicate,
                    Predicate::Record(HashMap::from([
                        (tuple_field(0), Predicate::True),
                        (tuple_field(1), Predicate::True),
                    ])),
                    "domain_predicate should be preserved"
                );
            }
            _ => panic!("Expected SealedFunction result"),
        }
    }

    #[test]
    fn uncurry_producer_with_single_elements() {
        // Test UncurryProducer with groups containing single elements
        //
        // - domain1: [A, B, C] (three keys)
        // - offsets: [0, 1, 2] (each key has exactly 1 item [last implicit end at domain2.len()])
        // - domain2: [X, Y, Z]
        // - codomain: [1, 2, 3]
        //
        // Expected expansion_indices: [0, 1, 2]
        // Expected expanded_domain1: [A, B, C]

        let curried_tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![100, 200, 300]),
            offsets: ColumnValue::UInts(vec![0, 1, 2]),
            domain2: ColumnValue::UInts(vec![10, 20, 30]),
            codomain: ColumnValue::UInts(vec![1, 2, 3]),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        };

        let curried_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };

        let input_producer = TestTileProducer::new(curried_tile, curried_tiling);

        let output_tiling = Tiling::SealedFunction {
            domain: Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::UInt)),
                    (tuple_field(1), Extent::Base(BaseType::UInt)),
                ]
                .into_iter()
                .collect(),
            ),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::UInt))),
        };

        let mut uncurry = UncurryProducer {
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
        };

        let result = uncurry.get(uncurry.tiling().universal_guard());

        match result {
            Tile::SealedFunction {
                domain,
                codomain: _,
                domain_predicate,
                ..
            } => {
                match domain {
                    ColumnValue::Records(fields) => {
                        let field_0 = &fields[&tuple_field(0)];
                        if let ColumnValue::UInts(vals) = field_0 {
                            assert_eq!(
                                vals,
                                &vec![100, 200, 300],
                                "expanded domain1 should be unchanged"
                            );
                        } else {
                            panic!("_0 field should be UInts");
                        }

                        let field_1 = &fields[&tuple_field(1)];
                        if let ColumnValue::UInts(vals) = field_1 {
                            assert_eq!(vals, &vec![10, 20, 30], "domain2 should be unchanged");
                        } else {
                            panic!("_1 field should be UInts");
                        }
                    }
                    _ => panic!("domain should be a Record"),
                }

                // Verify domain_predicate is transformed appropriately
                assert_eq!(
                    domain_predicate,
                    Predicate::Record(HashMap::from([
                        (tuple_field(0), Predicate::False),
                        (tuple_field(1), Predicate::False),
                    ])),
                    "domain_predicate should be preserved"
                );
            }
            _ => panic!("Expected SealedFunction result"),
        }
    }

    #[test]
    fn uncurry_domain_predicate_transformation_with_true() {
        // Test that UncurryProducer.get() transforms domain_predicate correctly
        // when the input has Predicate::True
        //
        // Previously, Predicate::True was preserved directly.
        // Now, it should be transformed into a Record predicate with both
        // fields (_0 and _1) set to Predicate::True.

        let curried_tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![1, 2, 3]),
            offsets: ColumnValue::UInts(vec![0, 1, 2]),
            domain2: ColumnValue::UInts(vec![10, 20, 30]),
            codomain: ColumnValue::UInts(vec![100, 200, 300]),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };

        let curried_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };

        let input_producer = TestTileProducer::new(curried_tile, curried_tiling);

        let output_tiling = Tiling::SealedFunction {
            domain: Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::UInt)),
                    (tuple_field(1), Extent::Base(BaseType::UInt)),
                ]
                .into_iter()
                .collect(),
            ),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::UInt))),
        };

        let mut uncurry = UncurryProducer {
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
        };

        let result = uncurry.get(uncurry.tiling().universal_guard());

        match result {
            Tile::SealedFunction {
                domain_predicate, ..
            } => {
                // Verify domain_predicate is transformed into a Record with both fields True
                assert_eq!(
                    domain_predicate,
                    Predicate::Record(HashMap::from([
                        (tuple_field(0), Predicate::True),
                        (tuple_field(1), Predicate::True),
                    ])),
                    "domain_predicate should be transformed into Record(_0: True, _1: True)"
                );
            }
            _ => panic!("Expected SealedFunction result"),
        }
    }

    #[test]
    fn iterate_extent_predicate_with_record() {
        // Test that get_iterate_extent_predicate generates correct OR predicates for records
        //
        // When iterating over a record extent with multiple fields, the predicate
        // should be the union of field-specific predicates (one predicate per field
        // with that field's predicate true and others true, then OR'd together).

        // Create a test extent with a record of base types
        let extent = Extent::Record(
            [
                (tuple_field(0), Extent::Base(BaseType::UInt)),
                (tuple_field(1), Extent::Base(BaseType::Int)),
            ]
            .into_iter()
            .collect(),
        );

        let predicate = get_iterate_extent_predicate(&extent);

        // For a record extent with base-type fields, the predicate should be
        // a union of field predicates. Since each field's predicate is True
        // for base types, the resulting Record predicates are all identical
        // {_0: True, _1: True} and may collapse.
        match predicate {
            Predicate::Record(fields) => {
                // When two identical record predicates with all True union,
                // they may collapse to a single Record
                assert_eq!(fields.len(), 2, "Record should have 2 fields");
                assert_eq!(
                    fields.get(&tuple_field(0)),
                    Some(&Predicate::True),
                    "_0 field should be True"
                );
                assert_eq!(
                    fields.get(&tuple_field(1)),
                    Some(&Predicate::True),
                    "_1 field should be True"
                );
            }
            Predicate::True => {
                // Also accept True if all record fields are True
            }
            Predicate::Or(preds) => {
                // Or accept OR if it wasn't simplified
                assert!(!preds.is_empty(), "OR predicate should have terms");
                for pred in &preds {
                    match pred {
                        Predicate::Record(fields) => {
                            assert_eq!(fields.len(), 2, "Record predicate should have all fields");
                        }
                        _ => panic!("Expected Record predicates in OR, got {pred:?}"),
                    }
                }
            }
            other => panic!("Unexpected predicate for record extent with base types: {other:?}"),
        }
    }

    #[test]
    fn uncurry_domain_predicate_transformation_with_false() {
        // Test that UncurryProducer.get() transforms domain_predicate correctly
        // when the input has Predicate::False
        //
        // Previously, Predicate::False was preserved directly.
        // Now, it should be transformed into a Record predicate with both
        // fields (_0 and _1) set to Predicate::False.

        let curried_tile = Tile::CurriedFunction {
            domain1: ColumnValue::UInts(vec![1, 2]),
            offsets: ColumnValue::UInts(vec![0, 1]),
            domain2: ColumnValue::UInts(vec![10, 20]),
            codomain: ColumnValue::UInts(vec![100, 200]),
            domain_predicate: Predicate::False,
            deleted: BitSet::new(),
        };

        let curried_tiling = Tiling::CurriedFunction {
            domain1: Extent::Base(BaseType::UInt),
            domain2: Extent::Base(BaseType::UInt),
            codomain: Extent::Base(BaseType::UInt),
        };

        let input_producer = TestTileProducer::new(curried_tile, curried_tiling);

        let output_tiling = Tiling::SealedFunction {
            domain: Extent::Record(
                [
                    (tuple_field(0), Extent::Base(BaseType::UInt)),
                    (tuple_field(1), Extent::Base(BaseType::UInt)),
                ]
                .into_iter()
                .collect(),
            ),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::UInt))),
        };

        let mut uncurry = UncurryProducer {
            base: ProducerBase::new(UncurryProducer::alloc_id(), &output_tiling),
            input: Box::new(input_producer),
        };

        let result = uncurry.get(uncurry.tiling().universal_guard());

        match result {
            Tile::SealedFunction {
                domain_predicate, ..
            } => {
                // Verify domain_predicate is transformed into a Record with both fields False
                assert_eq!(
                    domain_predicate,
                    Predicate::Record(HashMap::from([
                        (tuple_field(0), Predicate::False),
                        (tuple_field(1), Predicate::False),
                    ])),
                    "domain_predicate should be transformed into Record(_0: False, _1: False)"
                );
            }
            _ => panic!("Expected SealedFunction result"),
        }
    }

    /// Build a `ConverseProducer` wrapping the given input tile and call `get`.
    fn run_converse(input_tile: Tile, input_tiling: Tiling) -> Tile {
        let output_tiling = {
            let (domain, codomain) = input_tiling.split_function_extent().unwrap();
            Tiling::CurriedFunction {
                domain1: codomain,
                domain2: domain.clone(),
                codomain: domain,
            }
        };
        let mut producer = ConverseProducer {
            base: ProducerBase::new(ConverseProducer::alloc_id(), &output_tiling),
            input: Box::new(TestTileProducer::new(input_tile, input_tiling)),
        };
        producer.get(producer.tiling().universal_guard())
    }

    fn sealed_fn_tiling() -> Tiling {
        Tiling::SealedFunction {
            domain: Extent::Base(BaseType::Int),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        }
    }

    /// Basic converse: `{0→10, 1→20, 2→10}` groups by codomain value.
    /// Expected output: domain1=[10,20], each group lists the domain values that map to it.
    #[test]
    fn converse_producer_basic_grouping() {
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![0, 1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![10, 20, 10]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let result = run_converse(tile, sealed_fn_tiling());
        let Tile::CurriedFunction {
            domain1,
            offsets,
            domain2,
            domain_predicate,
            deleted,
            ..
        } = result
        else {
            panic!("expected CurriedFunction");
        };
        // Two distinct codomain values: 10 and 20.
        assert_eq!(domain1, ColumnValue::Ints(vec![10, 20]));
        // Group for 10 starts at 0 (rows 0 and 2 map to 10); group for 20 starts at 2.
        assert_eq!(offsets, ColumnValue::UInts(vec![0, 2]));
        // domain2 is sorted by codomain key: [0, 2] for key 10, then [1] for key 20.
        assert_eq!(domain2, ColumnValue::Ints(vec![0, 2, 1]));
        assert_eq!(domain_predicate, Predicate::True);
        assert!(deleted.is_empty(), "no deleted entries expected");
    }

    /// Converse with no deleted entries on a single-entry input is a trivial sanity check.
    #[test]
    fn converse_producer_single_entry_no_deleted() {
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![42]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![7]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let result = run_converse(tile, sealed_fn_tiling());
        let Tile::CurriedFunction { deleted, .. } = result else {
            panic!("expected CurriedFunction");
        };
        assert!(deleted.is_empty());
    }

    /// Deleted bit on an input row must appear at the correct remapped position in the output.
    ///
    /// Input: domain=[0,1,2], codomain=[20,10,20], deleted={0}  (row 0 is logically removed).
    /// Sort order by codomain: [1(→10), 0(→20), 2(→20)].
    /// After remapping, input row 0 lands at output position 1, so output deleted={1}.
    #[test]
    fn converse_producer_deleted_remapped_through_sort() {
        let mut input_deleted = BitSet::new();
        input_deleted.insert(0); // row 0 is logically removed
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![0, 1, 2]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![20, 10, 20]))),
            domain_predicate: Predicate::True,
            deleted: input_deleted,
        };
        let result = run_converse(tile, sealed_fn_tiling());
        let Tile::CurriedFunction {
            deleted, domain2, ..
        } = result
        else {
            panic!("expected CurriedFunction");
        };
        // Sorted order: row 1 (key 10) first, then row 0 (key 20), then row 2 (key 20).
        // Output position 1 holds original row 0, which was deleted.
        assert_eq!(domain2, ColumnValue::Ints(vec![1, 0, 2]));
        let mut expected = BitSet::new();
        expected.insert(1);
        assert_eq!(deleted, expected);
    }

    /// Multiple deleted rows are all remapped correctly.
    ///
    /// Input: domain=[0,1,2,3], codomain=[30,10,20,10], deleted={1,3}.
    /// Sort order by codomain: [1(10), 3(10), 2(20), 0(30)].
    /// Input rows 1 and 3 land at output positions 0 and 1, so output deleted={0,1}.
    #[test]
    fn converse_producer_multiple_deleted_remapped() {
        let mut input_deleted = BitSet::new();
        input_deleted.insert(1);
        input_deleted.insert(3);
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Ints(vec![0, 1, 2, 3]),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![30, 10, 20, 10]))),
            domain_predicate: Predicate::True,
            deleted: input_deleted,
        };
        let result = run_converse(tile, sealed_fn_tiling());
        let Tile::CurriedFunction { deleted, .. } = result else {
            panic!("expected CurriedFunction");
        };
        let mut expected = BitSet::new();
        expected.insert(0);
        expected.insert(1);
        assert_eq!(deleted, expected);
    }

    // ── FlattenTupleDomain helpers ────────────────────────────────────────────

    /// Build the nested outer `Extent` used by the `FlattenTupleDomain` tests:
    /// `(_0: (Int, Int), _1: (Int,))`.
    fn nested_outer_extent() -> Extent {
        let inner0 = Extent::Record(HashMap::from([
            (tuple_field(0), Extent::Base(BaseType::Int)),
            (tuple_field(1), Extent::Base(BaseType::Int)),
        ]));
        let inner1 = Extent::Record(HashMap::from([(
            tuple_field(0),
            Extent::Base(BaseType::Int),
        )]));
        Extent::Record(HashMap::from([
            (tuple_field(0), inner0),
            (tuple_field(1), inner1),
        ]))
    }

    /// `FlattenTupleDomain::new` produces the correct flat domain tiling.
    ///
    /// Input domain: `(_0: (Int, Int), _1: (Int,))`
    /// Expected output domain: `(_0: Int, _1: Int, _2: Int)`
    #[test]
    fn flatten_tuple_domain_tiling_is_correct() {
        // IterateExtent produces SealedFunction(outer → outer); the codomain is
        // irrelevant here — FlattenTupleDomain only inspects the domain.
        let input = Box::new(IterateExtent::new(nested_outer_extent()));
        let op = FlattenTupleDomain::new(input, vec![0, 1]);
        let Tiling::SealedFunction { domain, .. } = op.tiling() else {
            panic!("expected SealedFunction tiling");
        };
        let Extent::Record(fields) = domain else {
            panic!("expected Record domain");
        };
        assert_eq!(fields.len(), 3);
        assert!(matches!(
            fields.get("_0"),
            Some(Extent::Base(BaseType::Int))
        ));
        assert!(matches!(
            fields.get("_1"),
            Some(Extent::Base(BaseType::Int))
        ));
        assert!(matches!(
            fields.get("_2"),
            Some(Extent::Base(BaseType::Int))
        ));
    }

    /// `flatten_predicate` with `Predicate::True` is a no-op (passes through).
    ///
    /// Input domain: `{ _0: { _0: [10, 20], _1: [30, 40] }, _1: { _0: [50, 60] } }`
    /// Expected output columns after flattening: `{ _0: [10,20], _1: [30,40], _2: [50,60] }`.
    #[test]
    fn flatten_tuple_domain_get_flattens_columns() {
        let field_map = vec![
            (tuple_field(0), Some(tuple_field(0))),
            (tuple_field(0), Some(tuple_field(1))),
            (tuple_field(1), Some(tuple_field(0))),
        ];
        let outer_cols = HashMap::from([
            (
                tuple_field(0),
                ColumnValue::Records(HashMap::from([
                    (tuple_field(0), ColumnValue::Ints(vec![10, 20])),
                    (tuple_field(1), ColumnValue::Ints(vec![30, 40])),
                ])),
            ),
            (
                tuple_field(1),
                ColumnValue::Records(HashMap::from([(
                    tuple_field(0),
                    ColumnValue::Ints(vec![50, 60]),
                )])),
            ),
        ]);

        let flat_domain: HashMap<String, ColumnValue> = field_map
            .iter()
            .enumerate()
            .map(|(out_idx, (outer_k, inner_k))| {
                let inner_col = match outer_cols.get(outer_k) {
                    Some(ColumnValue::Records(inner_map)) => {
                        inner_map[inner_k.as_ref().unwrap()].clone()
                    }
                    _ => panic!("expected Records for outer field {outer_k}"),
                };
                (tuple_field(out_idx), inner_col)
            })
            .collect();
        assert_eq!(
            flat_domain[&tuple_field(0)],
            ColumnValue::Ints(vec![10, 20])
        );
        assert_eq!(
            flat_domain[&tuple_field(1)],
            ColumnValue::Ints(vec![30, 40])
        );
        assert_eq!(
            flat_domain[&tuple_field(2)],
            ColumnValue::Ints(vec![50, 60])
        );

        assert_eq!(
            flatten_predicate(&Predicate::True, &field_map),
            Predicate::True
        );
    }

    /// `flatten_predicate` expands `Predicate::Record { _0: Record { _0: pA, _1: pB }, _1: Record { _0: pC } }`.
    #[test]
    fn flatten_predicate_expands_nested_record_predicate() {
        let field_map = vec![
            (tuple_field(0), Some(tuple_field(0))),
            (tuple_field(0), Some(tuple_field(1))),
            (tuple_field(1), Some(tuple_field(0))),
        ];
        let pred = Predicate::Record(HashMap::from([
            (
                tuple_field(0),
                Predicate::Record(HashMap::from([
                    (tuple_field(0), Predicate::True),
                    (tuple_field(1), Predicate::False),
                ])),
            ),
            (tuple_field(1), Predicate::True),
        ]));
        let flat = flatten_predicate(&pred, &field_map);
        let Predicate::Record(fields) = flat else {
            panic!("expected Record predicate");
        };
        assert_eq!(fields[&tuple_field(0)], Predicate::True);
        assert_eq!(fields[&tuple_field(1)], Predicate::False);
        assert_eq!(fields[&tuple_field(2)], Predicate::True);
    }

    /// `unflatten_predicate` is the inverse of `flatten_predicate` for Record predicates.
    #[test]
    fn unflatten_predicate_is_inverse_of_flatten() {
        let field_map = vec![
            (tuple_field(0), Some(tuple_field(0))),
            (tuple_field(0), Some(tuple_field(1))),
            (tuple_field(1), Some(tuple_field(0))),
        ];
        let flat = Predicate::Record(HashMap::from([
            (tuple_field(0), Predicate::True),
            (tuple_field(1), Predicate::False),
            (tuple_field(2), Predicate::True),
        ]));
        let nested = unflatten_predicate(&flat, &field_map);
        let Predicate::Record(outer) = nested else {
            panic!("expected Record predicate");
        };
        let Predicate::Record(inner0) = &outer[&tuple_field(0)] else {
            panic!("expected inner Record for _0");
        };
        assert_eq!(inner0[&tuple_field(0)], Predicate::True);
        assert_eq!(inner0[&tuple_field(1)], Predicate::False);
        let Predicate::Record(inner1) = &outer[&tuple_field(1)] else {
            panic!("expected inner Record for _1");
        };
        assert_eq!(inner1[&tuple_field(0)], Predicate::True);
    }

    // ── permute_record ────────────────────────────────────────────────────────

    /// `permute_record` with `[2, 0, 1]`: out_0 ← in_2, out_1 ← in_0, out_2 ← in_1.
    #[test]
    fn permute_record_reorders_fields() {
        let input = HashMap::from([
            (tuple_field(0), 10u32),
            (tuple_field(1), 20u32),
            (tuple_field(2), 30u32),
        ]);
        let result = permute_record(input, &[2, 0, 1]);
        assert_eq!(result[&tuple_field(0)], 30);
        assert_eq!(result[&tuple_field(1)], 10);
        assert_eq!(result[&tuple_field(2)], 20);
    }

    /// Identity permutation leaves every field in place.
    #[test]
    fn permute_record_identity_is_noop() {
        let input = HashMap::from([(tuple_field(0), 10u32), (tuple_field(1), 20u32)]);
        let result = permute_record(input, &[0, 1]);
        assert_eq!(result[&tuple_field(0)], 10);
        assert_eq!(result[&tuple_field(1)], 20);
    }

    // ── FlattenTupleDomainProducer ────────────────────────────────────────────

    /// Returns a nested outer `Tiling` matching `nested_outer_extent()`.
    fn nested_outer_tiling() -> Tiling {
        Tiling::SealedFunction {
            domain: nested_outer_extent(),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        }
    }

    /// Returns a flat three-field `Tiling` with all-`Int` domain.
    fn flat_three_int_tiling() -> Tiling {
        Tiling::SealedFunction {
            domain: Extent::Record(HashMap::from([
                (tuple_field(0), Extent::Base(BaseType::Int)),
                (tuple_field(1), Extent::Base(BaseType::Int)),
                (tuple_field(2), Extent::Base(BaseType::Int)),
            ])),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        }
    }

    /// `FlattenTupleDomainProducer::get_impl` flattens a nested `Records` domain column.
    ///
    /// Input: `{ _0: { _0: [10,20], _1: [30,40] }, _1: { _0: [50,60] } }`
    /// Expected: `{ _0: [10,20], _1: [30,40], _2: [50,60] }`, predicate unchanged (`True`).
    #[test]
    fn flatten_producer_get_flattens_nested_domain() {
        let field_map = vec![
            (tuple_field(0), Some(tuple_field(0))),
            (tuple_field(0), Some(tuple_field(1))),
            (tuple_field(1), Some(tuple_field(0))),
        ];
        let input_tile = Tile::SealedFunction {
            domain: ColumnValue::Records(HashMap::from([
                (
                    tuple_field(0),
                    ColumnValue::Records(HashMap::from([
                        (tuple_field(0), ColumnValue::Ints(vec![10, 20])),
                        (tuple_field(1), ColumnValue::Ints(vec![30, 40])),
                    ])),
                ),
                (
                    tuple_field(1),
                    ColumnValue::Records(HashMap::from([(
                        tuple_field(0),
                        ColumnValue::Ints(vec![50, 60]),
                    )])),
                ),
            ])),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 0]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let flat_tiling = flat_three_int_tiling();
        let mut producer = FlattenTupleDomainProducer {
            base: ProducerBase::new(FlattenTupleDomainProducer::alloc_id(), &flat_tiling),
            input: Box::new(TestTileProducer::new(input_tile, nested_outer_tiling())),
            field_map,
        };
        let result = producer.get(producer.tiling().universal_guard());
        let Tile::SealedFunction {
            domain,
            domain_predicate,
            ..
        } = result
        else {
            panic!("expected SealedFunction");
        };
        let ColumnValue::Records(cols) = domain else {
            panic!("expected Records domain");
        };
        assert_eq!(cols[&tuple_field(0)], ColumnValue::Ints(vec![10, 20]));
        assert_eq!(cols[&tuple_field(1)], ColumnValue::Ints(vec![30, 40]));
        assert_eq!(cols[&tuple_field(2)], ColumnValue::Ints(vec![50, 60]));
        assert_eq!(domain_predicate, Predicate::True);
    }

    /// `FlattenTupleDomainProducer::get_impl` passes through non-flattened outer fields unchanged.
    ///
    /// Input: `{ _0: { _0: [10,20] }, _1: [99, 88] }` with field_map `[("_0", Some("_0")), ("_1", None)]`.
    /// Expected: `{ _0: [10,20], _1: [99, 88] }`.
    #[test]
    fn flatten_producer_get_passes_through_non_flattened_field() {
        let field_map = vec![
            (tuple_field(0), Some(tuple_field(0))),
            (tuple_field(1), None),
        ];
        let pass_through_tiling = Tiling::SealedFunction {
            domain: Extent::Record(HashMap::from([
                (
                    tuple_field(0),
                    Extent::Record(HashMap::from([(
                        tuple_field(0),
                        Extent::Base(BaseType::Int),
                    )])),
                ),
                (tuple_field(1), Extent::Base(BaseType::Int)),
            ])),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let input_tile = Tile::SealedFunction {
            domain: ColumnValue::Records(HashMap::from([
                (
                    tuple_field(0),
                    ColumnValue::Records(HashMap::from([(
                        tuple_field(0),
                        ColumnValue::Ints(vec![10, 20]),
                    )])),
                ),
                (tuple_field(1), ColumnValue::Ints(vec![99, 88])),
            ])),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 0]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        let out_tiling = Tiling::SealedFunction {
            domain: Extent::Record(HashMap::from([
                (tuple_field(0), Extent::Base(BaseType::Int)),
                (tuple_field(1), Extent::Base(BaseType::Int)),
            ])),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let mut producer = FlattenTupleDomainProducer {
            base: ProducerBase::new(FlattenTupleDomainProducer::alloc_id(), &out_tiling),
            input: Box::new(TestTileProducer::new(input_tile, pass_through_tiling)),
            field_map,
        };
        let result = producer.get(producer.tiling().universal_guard());
        let Tile::SealedFunction { domain, .. } = result else {
            panic!("expected SealedFunction");
        };
        let ColumnValue::Records(cols) = domain else {
            panic!("expected Records domain");
        };
        assert_eq!(cols[&tuple_field(0)], ColumnValue::Ints(vec![10, 20]));
        assert_eq!(cols[&tuple_field(1)], ColumnValue::Ints(vec![99, 88]));
    }

    // ── PermuteRecordDomainProducer ───────────────────────────────────────────

    /// Helper: build a three-field `SealedFunction` tile and tiling with all-`Int` `Records` domain.
    fn make_three_field_records_tile_and_tiling() -> (Tile, Tiling) {
        let tiling = Tiling::SealedFunction {
            domain: Extent::Record(HashMap::from([
                (tuple_field(0), Extent::Base(BaseType::Int)),
                (tuple_field(1), Extent::Base(BaseType::Int)),
                (tuple_field(2), Extent::Base(BaseType::Int)),
            ])),
            codomain: Box::new(Tiling::Scalar(Extent::Base(BaseType::Int))),
        };
        let tile = Tile::SealedFunction {
            domain: ColumnValue::Records(HashMap::from([
                (tuple_field(0), ColumnValue::Ints(vec![1, 2])),
                (tuple_field(1), ColumnValue::Ints(vec![3, 4])),
                (tuple_field(2), ColumnValue::Ints(vec![5, 6])),
            ])),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(vec![0, 0]))),
            domain_predicate: Predicate::True,
            deleted: BitSet::new(),
        };
        (tile, tiling)
    }

    /// `PermuteRecordDomainProducer::get_impl` reorders domain columns by permutation.
    ///
    /// Permutation `[2, 0, 1]`: out_0 ← in_2, out_1 ← in_0, out_2 ← in_1.
    #[test]
    fn permute_producer_get_permutes_domain_fields() {
        let (input_tile, input_tiling) = make_three_field_records_tile_and_tiling();
        let permutation = vec![2usize, 0, 1];
        let mut producer = PermuteRecordDomainProducer {
            base: ProducerBase::new(
                PermuteRecordDomainProducer::alloc_id(),
                &flat_three_int_tiling(),
            ),
            input: Box::new(TestTileProducer::new(input_tile, input_tiling)),
            permutation,
        };
        let result = producer.get(producer.tiling().universal_guard());
        let Tile::SealedFunction { domain, .. } = result else {
            panic!("expected SealedFunction");
        };
        let ColumnValue::Records(cols) = domain else {
            panic!("expected Records domain");
        };
        assert_eq!(cols[&tuple_field(0)], ColumnValue::Ints(vec![5, 6]));
        assert_eq!(cols[&tuple_field(1)], ColumnValue::Ints(vec![1, 2]));
        assert_eq!(cols[&tuple_field(2)], ColumnValue::Ints(vec![3, 4]));
    }

    /// `PermuteRecordDomainProducer::get_impl` with identity permutation leaves domain unchanged.
    #[test]
    fn permute_producer_get_identity_permutation_is_noop() {
        let (input_tile, input_tiling) = make_three_field_records_tile_and_tiling();
        let permutation = vec![0usize, 1, 2];
        let mut producer = PermuteRecordDomainProducer {
            base: ProducerBase::new(
                PermuteRecordDomainProducer::alloc_id(),
                &flat_three_int_tiling(),
            ),
            input: Box::new(TestTileProducer::new(input_tile, input_tiling)),
            permutation,
        };
        let result = producer.get(producer.tiling().universal_guard());
        let Tile::SealedFunction { domain, .. } = result else {
            panic!("expected SealedFunction");
        };
        let ColumnValue::Records(cols) = domain else {
            panic!("expected Records domain");
        };
        assert_eq!(cols[&tuple_field(0)], ColumnValue::Ints(vec![1, 2]));
        assert_eq!(cols[&tuple_field(1)], ColumnValue::Ints(vec![3, 4]));
        assert_eq!(cols[&tuple_field(2)], ColumnValue::Ints(vec![5, 6]));
    }

    /// `PermuteRecordDomainProducer::get_impl` permutes a `Record` domain predicate.
    ///
    /// Permutation `[2, 0, 1]` on predicate `{_0: True, _1: False, _2: True}` →
    /// `{_0: True, _1: True, _2: False}` (out_0 ← in_2 = True, out_1 ← in_0 = True, out_2 ← in_1 = False).
    #[test]
    fn permute_producer_get_permutes_record_predicate() {
        let (mut input_tile, input_tiling) = make_three_field_records_tile_and_tiling();
        // Override the predicate on the input tile.
        if let Tile::SealedFunction {
            ref mut domain_predicate,
            ..
        } = input_tile
        {
            *domain_predicate = Predicate::Record(HashMap::from([
                (tuple_field(0), Predicate::True),
                (tuple_field(1), Predicate::False),
                (tuple_field(2), Predicate::True),
            ]));
        }
        let permutation = vec![2usize, 0, 1];
        let mut producer = PermuteRecordDomainProducer {
            base: ProducerBase::new(
                PermuteRecordDomainProducer::alloc_id(),
                &flat_three_int_tiling(),
            ),
            input: Box::new(TestTileProducer::new(input_tile, input_tiling)),
            permutation,
        };
        let result = producer.get(producer.tiling().universal_guard());
        let Tile::SealedFunction {
            domain_predicate, ..
        } = result
        else {
            panic!("expected SealedFunction");
        };
        let Predicate::Record(fields) = domain_predicate else {
            panic!("expected Record predicate");
        };
        assert_eq!(fields[&tuple_field(0)], Predicate::True); // in_2 = True
        assert_eq!(fields[&tuple_field(1)], Predicate::True); // in_0 = True
        assert_eq!(fields[&tuple_field(2)], Predicate::False); // in_1 = False
    }

    /// `PermuteRecordDomainProducer::release_impl` applies the permutation to a `Record` guard.
    ///
    /// Release guard `{_0: True, _1: False, _2: True}` with permutation `[2, 0, 1]`.
    /// Upstream receives `{_0: True, _1: True, _2: False}`.
    #[test]
    fn permute_producer_release_record_guard_is_permuted() {
        use std::sync::mpsc;
        let (tx, rx) = mpsc::channel::<TileGuard>();

        struct SenderProducer {
            base: ProducerBase,
            tile: Tile,
            tx: mpsc::Sender<TileGuard>,
        }
        impl TileProducer for SenderProducer {
            impl_producer_base!();
            fn add_inspect_children(&self, node: InspectNode, _: &VizOptions) -> InspectNode {
                node
            }
            fn get_impl(&mut self, _: TileGuard) -> Tile {
                self.tile.clone()
            }
            fn release_impl(&mut self, guard: TileGuard) {
                let _ = self.tx.send(guard);
            }
        }

        let (input_tile, input_tiling) = make_three_field_records_tile_and_tiling();
        let sender = SenderProducer {
            base: ProducerBase::new(SenderProducer::alloc_id(), &input_tiling),
            tile: input_tile,
            tx,
        };
        let out_tiling = flat_three_int_tiling();
        let mut producer = PermuteRecordDomainProducer {
            base: ProducerBase::new(PermuteRecordDomainProducer::alloc_id(), &out_tiling),
            input: Box::new(sender),
            permutation: vec![2usize, 0, 1],
        };
        let obsolete =
            TileGuard::Function(FunctionGuard::Domain(Predicate::Record(HashMap::from([
                (tuple_field(0), Predicate::True),
                (tuple_field(1), Predicate::False),
                (tuple_field(2), Predicate::True),
            ]))));
        producer.release(obsolete);
        let upstream = rx.recv().expect("release_impl did not send upstream guard");
        let TileGuard::Function(FunctionGuard::Domain(Predicate::Record(fields))) = upstream else {
            panic!("expected Function/Domain/Record guard, got {upstream:?}");
        };
        // permutation [2,0,1]: upstream field `target` receives the downstream field at that index.
        // `release_impl` calls permute_record(fields, permutation):
        //   upstream._0 ← downstream._2 = True
        //   upstream._1 ← downstream._0 = True
        //   upstream._2 ← downstream._1 = False
        assert_eq!(fields[&tuple_field(0)], Predicate::True);
        assert_eq!(fields[&tuple_field(1)], Predicate::True);
        assert_eq!(fields[&tuple_field(2)], Predicate::False);
    }

    // ── permute_result_correlation ────────────────────────────────────────────

    fn tuple_step(idx: usize) -> TilePathStep {
        TilePathStep::Record(tuple_field(idx))
    }

    /// `(A, B) -> A`: correlation `[_0]` with permutation `[1, 0]` → `[_1]`.
    #[test]
    fn permute_result_correlation_swaps_two_fields() {
        let result = permute_result_correlation(vec![tuple_step(0)], &[1, 0]);
        assert_eq!(result, Some(vec![tuple_step(1)]));
    }

    /// Permutation `[2, 0, 1]` with correlation `[_0]`: inv_perm[0] = 1 → `[_1]`.
    #[test]
    fn permute_result_correlation_three_arm() {
        let result = permute_result_correlation(vec![tuple_step(0)], &[2, 0, 1]);
        assert_eq!(result, Some(vec![tuple_step(1)]));
    }

    /// Permutation `[2, 0, 1]` with correlation `[_2]`: inv_perm[2] = 0 → `[_0]`.
    #[test]
    fn permute_result_correlation_three_arm_field_two() {
        let result = permute_result_correlation(vec![tuple_step(2)], &[2, 0, 1]);
        assert_eq!(result, Some(vec![tuple_step(0)]));
    }

    /// Extra path steps after the Record step are passed through unchanged.
    #[test]
    fn permute_result_correlation_preserves_tail() {
        let result =
            permute_result_correlation(vec![tuple_step(0), TilePathStep::Codomain], &[1, 0]);
        assert_eq!(result, Some(vec![tuple_step(1), TilePathStep::Codomain]));
    }

    /// Empty correlation (identity) returns `None` — domain renamed but codomain unchanged.
    #[test]
    fn permute_result_correlation_empty_returns_none() {
        assert_eq!(permute_result_correlation(vec![], &[1, 0]), None);
    }

    /// Non-Record first step passes through unchanged.
    #[test]
    fn permute_result_correlation_codomain_first_step_passes_through() {
        let corr = vec![TilePathStep::Codomain, tuple_step(0)];
        assert_eq!(
            permute_result_correlation(corr.clone(), &[1, 0]),
            Some(corr)
        );
    }

    // ── flatten_result_correlation ────────────────────────────────────────────

    /// field_map for `{ _0: A, _1: (B, C) }` with both flattened:
    /// flat._0 = outer._0 (pass-through), flat._1 = outer._1._0 (B), flat._2 = outer._1._1 (C).
    fn nested_field_map() -> Vec<(String, Option<String>)> {
        vec![
            (tuple_field(0), None),
            (tuple_field(1), Some(tuple_field(0))),
            (tuple_field(1), Some(tuple_field(1))),
        ]
    }

    /// `(A, (B, C)) -> B`: `[_1, _0]` → `[_1]` (outer._1, inner._0 = B is at flat._1).
    #[test]
    fn flatten_result_correlation_two_level_collapses_to_flat_index() {
        let result =
            flatten_result_correlation(vec![tuple_step(1), tuple_step(0)], &nested_field_map());
        assert_eq!(result, Some(vec![tuple_step(1)]));
    }

    /// `(A, (B, C)) -> C`: `[_1, _1]` → `[_2]` (outer._1, inner._1 = C is at flat._2).
    #[test]
    fn flatten_result_correlation_two_level_inner_field_one() {
        let result =
            flatten_result_correlation(vec![tuple_step(1), tuple_step(1)], &nested_field_map());
        assert_eq!(result, Some(vec![tuple_step(2)]));
    }

    /// Pass-through outer field: `[_0]` → `[_0]` (outer._0 = A is at flat._0).
    #[test]
    fn flatten_result_correlation_passthrough_field_maps_to_flat_index() {
        let result = flatten_result_correlation(vec![tuple_step(0)], &nested_field_map());
        assert_eq!(result, Some(vec![tuple_step(0)]));
    }

    /// Flattened outer field with single step (no inner step): returns `None`.
    #[test]
    fn flatten_result_correlation_flattened_outer_single_step_returns_none() {
        // outer._1 is flattened; there is no single flat field for the whole of _1.
        let result = flatten_result_correlation(vec![tuple_step(1)], &nested_field_map());
        assert_eq!(result, None);
    }

    /// Empty correlation returns `None`.
    #[test]
    fn flatten_result_correlation_empty_returns_none() {
        assert_eq!(
            flatten_result_correlation(vec![], &nested_field_map()),
            None
        );
    }

    /// `Codomain` first step passes through unchanged.
    #[test]
    fn flatten_result_correlation_codomain_first_step_passes_through() {
        let corr = vec![TilePathStep::Codomain, tuple_step(0)];
        assert_eq!(
            flatten_result_correlation(corr.clone(), &nested_field_map()),
            Some(corr)
        );
    }

    /// Extra path steps after the collapsed pair are preserved.
    #[test]
    fn flatten_result_correlation_preserves_tail_after_two_level() {
        let result = flatten_result_correlation(
            vec![tuple_step(1), tuple_step(0), TilePathStep::Codomain],
            &nested_field_map(),
        );
        assert_eq!(result, Some(vec![tuple_step(1), TilePathStep::Codomain]));
    }

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
