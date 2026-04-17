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
    collections::HashMap,
    hash::Hash,
    iter,
    rc::Rc,
    sync::{Mutex, OnceLock},
};

use bit_vec::BitVec;
use intervalsets::{ops::Difference, Bounding, Interval, IntervalSet};
use log::trace;

pub use crate::interpreter::tiling::{FunctionGuard, Predicate, Tile, TileGuard, Tiling};
use crate::{
    ccl::AggregateKind,
    interpreter::{
        bindings_are_list, transform_hashmap_values, tuple_field, validate_tile, BaseType,
        ColumnValue, Consumer, DataSourceDomainExtentImpl, Extent, NotifyOrSubscribeResult,
        Scheduler, Value,
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
                panic!("column_value_to_tile: expected Records ColumnValue for Record tiling, got {cv:?}");
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
        } => Tile::SealedFunction {
            domain,
            domain_predicate,
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
        } => Tile::CurriedFunction {
            domain1,
            offsets,
            domain2,
            codomain: transformation(codomain),
            domain_predicate,
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
                Tiling::SealedFunction { domain: d, codomain: c, .. } => {
                    // Verify the codomain matches the function's domain1
                    assert_eq!(
                        c.extent(),
                        *fn_domain1,
                        "Input codomain extent must match function domain1"
                    );
                    d.clone()
                }
                Tiling::CurriedFunction { domain1: d, codomain: c, .. } => {
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
        let tiling = change_tiling_result(input.tiling(), move |codomain_extent| {
            assert_eq!(function_domain_extent, *codomain_extent);
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
        } = function_tile
        {
            let Tile::SealedFunction {
                domain,
                codomain: input_codomain,
                domain_predicate,
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
    ZipLeft,
    /// Replace the codomain x with (x, constant)
    ZipRight,
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
            MapResultToConstMode::ZipLeft => change_tiling_result(input.tiling(), |e| {
                Tiling::tuple(&[constant.tiling().clone(), Tiling::Scalar(e.clone())])
            }),
            MapResultToConstMode::ZipRight => change_tiling_result(input.tiling(), |e| {
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
                MapResultToConstMode::ZipLeft => {
                    Tile::tuple(vec![const_tile, Tile::Scalar(codomain)])
                }
                MapResultToConstMode::ZipRight => {
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
        Extent::Restricted { .. } => {
            panic!("Iterating over restricted extents not supported; use Filter operators instead")
        }
        _ => panic!("Attempted to iterate on infinite Extent"),
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
        ))
    }
}

/// Producer for [`MapNSource`]: maps each domain key to its output value on `get`.
struct MapResultWithSourceProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    /// The data source used for both domain enumeration and value lookup.
    source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
}

impl MapResultWithSourceProducer {
    fn new(
        input: Box<dyn TileProducer>,
        source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
        tiling: Tiling,
    ) -> Self {
        let result = Self {
            base: ProducerBase::new(MapResultWithSourceProducer::alloc_id(), &tiling),
            input,
            source,
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
                self.source.borrow_mut().release(&self.name(), pred.clone());
            }
            TileGuard::Function(FunctionGuard::Codomain(g)) => {
                if let TileGuard::Function(FunctionGuard::Domain(pred)) = &**g {
                    self.source.borrow_mut().release(&self.name(), pred.clone());
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

/// Combines multiple sealed-function operators sharing the same domain into a
/// single sealed-function operator whose codomain is a record of all their codomains.
///
/// All inputs must have `SealedFunction` tilings with compatible domains.
/// Output fields are named `_0`, `_1`, … matching the input order.
pub struct Zip {
    /// Output tiling: either a `SealedFunction { domain, codomain: Record { _0, _1, … } }`
    /// or a `CurriedFunction { domain1, domain2, codomain: Record { _0, _1, … } }`,
    /// depending on the input operators.
    tiling: Tiling,
    /// The input function operators to zip together (either all `SealedFunction` or all `CurriedFunction`).
    inputs: Vec<Box<dyn TileOperator>>,
}

impl Zip {
    /// Create a new `Zip` operator over the given input operators.
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
        assert!(!inputs.is_empty(), "Zip requires at least one input");

        let first_tiling = inputs[0].tiling();
        let tiling = match first_tiling {
            Tiling::SealedFunction { domain, .. } => {
                // Verify all inputs are SealedFunction with the same domain
                for op in inputs.iter() {
                    if let Tiling::SealedFunction { domain: d, .. } = op.tiling() {
                        assert_eq!(
                            domain, d,
                            "Zip: all SealedFunction inputs must have the same domain"
                        );
                    } else {
                        panic!("Zip: all inputs must be the same type (all SealedFunction or all CurriedFunction)");
                    }
                }
                Tiling::SealedFunction {
                    domain: domain.clone(),
                    codomain: Box::new(Tiling::Record(
                        inputs
                            .iter()
                            .enumerate()
                            .map(|(i, op)| {
                                (
                                    tuple_field(i),
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
                domain1,
                domain2,
                codomain: _,
            } => {
                // Verify all inputs are CurriedFunction with the same domain1 and domain2
                for op in inputs.iter() {
                    if let Tiling::CurriedFunction {
                        domain1: d1,
                        domain2: d2,
                        ..
                    } = op.tiling()
                    {
                        assert_eq!(
                            domain1, d1,
                            "Zip: all CurriedFunction inputs must have the same domain1"
                        );
                        assert_eq!(
                            domain2, d2,
                            "Zip: all CurriedFunction inputs must have the same domain2"
                        );
                    } else {
                        panic!("Zip: all inputs must be the same type (all SealedFunction or all CurriedFunction)");
                    }
                }
                Tiling::CurriedFunction {
                    domain1: domain1.clone(),
                    domain2: domain2.clone(),
                    codomain: Extent::Record(
                        inputs
                            .iter()
                            .enumerate()
                            .map(|(i, op)| {
                                if let Tiling::CurriedFunction { codomain: cod, .. } = op.tiling() {
                                    (tuple_field(i), cod.clone())
                                } else {
                                    panic!("Expected CurriedFunction, got {}", op.tiling())
                                }
                            })
                            .collect(),
                    ),
                }
            }
            _ => panic!(
                "Zip: all inputs must have function tilings (SealedFunction or CurriedFunction)"
            ),
        };
        Self { tiling, inputs }
    }
}

impl TileOperator for Zip {
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
        Box::new(ZipProducer {
            base: ProducerBase::new(ZipProducer::alloc_id(), &self.tiling),
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

/// Producer for [`Zip`]: pulls each input and assembles a record-codomain tile.
struct ZipProducer {
    base: ProducerBase,
    /// Live input producers, in field order.
    inputs: Vec<Box<dyn TileProducer>>,
}

impl TileProducer for ZipProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, mut node: InspectNode, opts: &VizOptions) -> InspectNode {
        for (i, input) in self.inputs.iter().enumerate() {
            node = node.child(format!("_{i}"), input.inspect(opts));
        }
        node
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let tiles: Vec<Tile> = self
            .inputs
            .iter_mut()
            .map(|i| i.get(i.tiling().universal_guard()))
            .collect();

        match &tiles[0] {
            Tile::SealedFunction { .. } => {
                // All inputs are SealedFunction tiles
                let mut domain_pred: Option<Predicate> = None;
                let mut output_domain: Option<ColumnValue> = None;
                let mut codomains = Vec::new();
                for t in tiles.into_iter() {
                    match t {
                        Tile::SealedFunction {
                            domain,
                            codomain,
                            domain_predicate,
                        } => {
                            if let Some(ref mut prev) = domain_pred {
                                *prev = prev.intersect(&domain_predicate);
                            } else {
                                domain_pred = Some(domain_predicate.clone());
                            }
                            output_domain = Some(domain);
                            codomains.push(*codomain);
                        }
                        _ => panic!("Zip: cannot mix SealedFunction and other tile types"),
                    }
                }

                let codomain_record = Tile::Record(
                    codomains
                        .into_iter()
                        .enumerate()
                        .map(move |(i, cv)| (tuple_field(i), cv))
                        .collect(),
                );
                Tile::SealedFunction {
                    domain: output_domain.unwrap(),
                    codomain: Box::new(codomain_record),
                    domain_predicate: domain_pred.unwrap(),
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
                        } => {
                            if let Some(ref prev_d1) = domain1 {
                                assert_eq!(
                                    prev_d1, &d1,
                                    "Zip: all inputs must have the same domain1"
                                );
                            }
                            if let Some(ref prev_offs) = offsets {
                                assert_eq!(
                                    prev_offs, &offs,
                                    "Zip: all inputs must have the same offsets"
                                );
                            }
                            if let Some(ref prev_d2) = domain2 {
                                assert_eq!(
                                    prev_d2, &d2,
                                    "Zip: all inputs must have the same domain2"
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
                        _ => panic!("Zip: cannot mix CurriedFunction and other tile types"),
                    }
                }

                let codomain_record = ColumnValue::Records(
                    codomains
                        .into_iter()
                        .enumerate()
                        .map(move |(i, cv)| (tuple_field(i), cv))
                        .collect(),
                );
                Tile::CurriedFunction {
                    domain1: domain1.unwrap(),
                    offsets: offsets.unwrap(),
                    domain2: domain2.unwrap(),
                    codomain: codomain_record,
                    domain_predicate: domain_pred.unwrap(),
                }
            }
            _ => panic!("Zip: all inputs must be SealedFunction or CurriedFunction tiles"),
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
/// Analogous to [`Zip`] for function tiles, but operates entirely on scalars:
/// each input must produce a `Tile::Scalar` and the output is a
/// `Tile::Scalar(ColumnValue::Records)` keyed `_0`, `_1`, …, `_N-1`.
pub struct ScalarTuple {
    tiling: Tiling,
    inputs: Vec<Box<dyn TileOperator>>,
}

impl ScalarTuple {
    /// Construct a `ScalarTuple` from N scalar input operators.
    ///
    /// All inputs must have scalar tilings. The output `extent` and `tiling`
    /// are derived: each input's scalar extent becomes a field (`_0`, `_1`, …)
    /// in the output `Extent::Record`.
    pub fn new(inputs: Vec<Box<dyn TileOperator>>) -> Self {
        assert!(
            !inputs.is_empty(),
            "ScalarTuple requires at least one input"
        );
        let tiling = Tiling::Record(
            inputs
                .iter()
                .enumerate()
                .map(|(i, op)| (tuple_field(i), op.tiling().clone()))
                .collect(),
        );
        Self { tiling, inputs }
    }
}

impl TileOperator for ScalarTuple {
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
        Box::new(ScalarTupleProducer {
            base: ProducerBase::new(ScalarTupleProducer::alloc_id(), &self.tiling),
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

/// Producer for [`ScalarTuple`]: pulls each scalar input and combines them into
/// a `Tile::Scalar(ColumnValue::Records)`.
struct ScalarTupleProducer {
    base: ProducerBase,
    inputs: Vec<Box<dyn TileProducer>>,
}

impl TileProducer for ScalarTupleProducer {
    impl_producer_base!();

    fn add_inspect_children(&self, mut node: InspectNode, opts: &VizOptions) -> InspectNode {
        for (i, input) in self.inputs.iter().enumerate() {
            node = node.child(format!("{i}"), input.inspect(opts));
        }
        node
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let fields: HashMap<String, Tile> = self
            .inputs
            .iter_mut()
            .enumerate()
            .map(|(i, input)| {
                let tile = input.get(input.tiling().universal_guard());
                (tuple_field(i), tile)
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
            } => match *codomain {
                Tile::Scalar(codomain) => {
                    // Dispatch on the native element type of the codomain column so that
                    // sorting uses typed comparison (PartialOrd) and avoids boxing to Value
                    // wherever the inner type is already ordered natively.
                    match &codomain {
                        ColumnValue::Units(n) => {
                            // All codomains are unit; create one group with all rows in order.
                            let keys = vec![(); *n];
                            converse_group_by_key(&keys, &codomain, &domain, domain_predicate)
                        }
                        ColumnValue::Ints(v) => {
                            converse_group_by_key(v, &codomain, &domain, domain_predicate)
                        }
                        ColumnValue::UInts(v) => {
                            converse_group_by_key(v, &codomain, &domain, domain_predicate)
                        }
                        ColumnValue::Strings(v) => {
                            converse_group_by_key(v, &codomain, &domain, domain_predicate)
                        }
                        ColumnValue::Bools(bv) => {
                            // Materialise as Vec<bool> so the element type is PartialOrd.
                            let v: Vec<bool> = bv.iter().collect();
                            converse_group_by_key(&v, &codomain, &domain, domain_predicate)
                        }
                        ColumnValue::Variants(v) => {
                            // Value is PartialOrd; pass the inner vec directly.
                            converse_group_by_key(v, &codomain, &domain, domain_predicate)
                        }
                        ColumnValue::Records(_) => {
                            // No native slice to borrow; materialise one Value per row for sorting.
                            // TODO: benchmark this and figure out a way to avoid if needed.
                            let n = codomain.len();
                            let keys: Vec<Value> = (0..n).map(|i| codomain.index_at(i)).collect();
                            converse_group_by_key(&keys, &codomain, &domain, domain_predicate)
                        }
                        ColumnValue::FunctionBindings { .. } => {
                            panic!(
                                "Cannot converse a function whose codomain is a function binding"
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
                ..
            } => Tile::SealedFunction {
                codomain: Box::new(Tile::Scalar(domain.clone())),
                domain,
                domain_predicate,
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
                    };
                    output.retain(mask);
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
            // SplitProducer release-guard stale, causing it to re-deliver already-consumed
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
                };
                output.retain(mask);
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
            kind: kind.clone(),
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
                kind.clone(),
                Tile::Aggregation {
                    kind: kind.clone(),
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
        let input_result = self.input.get(i_tiling.universal_guard());
        let upstream_guard = input_result.to_guard();
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
            kind: self.kind.clone(),
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
            kind: self.kind.clone(),
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
                kind: kind.clone(),
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
            kind: self.kind.clone(),
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
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        trace!("{} received {input_tile:?}", self.name());
        let upstream_guard = input_tile.to_guard();
        let Tile::CurriedFunction {
            domain1,
            offsets,
            domain2: _,
            codomain,
            domain_predicate,
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
                kind: self.kind.clone(),
                accumulator: ColumnValue::from_values(accumulator_values, &output_extent),
                terminal: ColumnValue::Bools(BitVec::from_elem(n, is_terminal)),
            }),
            domain_predicate,
        }
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        if obsolete_guard.is_universal() {
            self.accumulators.clear();
            self.input.release(self.input.tiling().universal_guard());
        }
    }
}

/// Mutable state shared across all clones of the same [`Split`] and all
/// [`SplitProducer`]s it creates.  Wrapping this in `Rc<RefCell<...>>` and
/// creating it eagerly in [`Split::new`] ensures that every clone produced by
/// [`Split::split`] shares the same object from the start — even before any
/// [`TileOperator::subscribe`] call has initialised the inner producer.
struct SplitShared {
    /// Instance ID shared by all [`SplitProducer`]s from the same split group.
    id: usize,
    /// Inner producer, set on the first [`Split::subscribe`] call.
    producer: Option<Box<dyn TileProducer>>,
    /// Every consumer registered via [`Split::subscribe`], in order.
    consumers: Vec<Box<dyn Consumer>>,
    /// Per-subscriber release guards; intersected before passing upstream.
    release_guards: Vec<TileGuard>,
}

/// Allows for creating multiple TileOperators that all point to the same
/// underlying operator.  Call [`Split::split`] to get additional handles;
/// subscribing to any handle will reuse the same inner producer.
pub struct Splitter {
    input: Rc<RefCell<Box<dyn TileOperator>>>,
    tiling: Tiling,
    /// All mutable shared state.  Created eagerly so that clones produced by
    /// [`Split::split`] always share the same object.
    shared: Rc<RefCell<SplitShared>>,
    /// Whether any Splits have been created yet.
    used: RefCell<bool>,
}

impl Splitter {
    /// Construct a new `Split` wrapping `input`.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let tiling = input.tiling().clone();
        let shared = Rc::new(RefCell::new(SplitShared {
            id: SplitProducer::alloc_id(),
            producer: None,
            consumers: Vec::new(),
            release_guards: Vec::new(),
        }));
        Self {
            input: Rc::new(RefCell::new(input)),
            tiling,
            shared,
            used: RefCell::new(false),
        }
    }

    /// Return a new handle to the same split.  All handles share the same
    /// inner producer and consumer list; subscribing to any of them is
    /// equivalent.
    pub fn split(&self) -> Box<dyn TileOperator> {
        let result = Split {
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

struct Split {
    input: Rc<RefCell<Box<dyn TileOperator>>>,
    tiling: Tiling,
    /// All mutable shared state.  Created eagerly so that clones produced by
    /// [`Split::split`] always share the same object.
    shared: Rc<RefCell<SplitShared>>,
    /// True for the first handle returned by [`Splitter::split`], false for subsequent ones.
    /// The primary renders its input subtree in inspect; copies emit a back-reference.
    primary: bool,
}

impl TileOperator for Split {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let id = self.shared.borrow().id;
        if self.primary {
            InspectNode::new(format!("Split#{id}"))
                .with_tiling(self.tiling().to_string())
                .child("input", self.input.borrow().inspect(opts))
        } else {
            InspectNode::leaf(format!("→ Split#{id}"))
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
            shared.consumers.push(consumer);
            shared.release_guards.push(self.tiling.empty_guard());
            index
        }; // borrow released here before we might call input.subscribe

        // Create the inner producer on the first subscription only.
        // We must not hold a borrow of `shared` during `input.subscribe`
        // because that call may synchronously fire the notification closure,
        // which itself borrows `shared`.
        if self.shared.borrow().producer.is_none() {
            let shared_rc = self.shared.clone();
            let inner = self.input.borrow_mut().subscribe(
                intent_guard,
                Box::new(move || {
                    shared_rc
                        .borrow_mut()
                        .consumers
                        .iter_mut()
                        .for_each(|c| c.notify());
                }),
                scheduler,
            );
            self.shared.borrow_mut().producer = Some(inner);
        }

        Box::new(SplitProducer {
            base: ProducerBase::new(self.shared.borrow().id, &self.tiling),
            shared: self.shared.clone(),
            index,
        })
    }
}

struct SplitProducer {
    base: ProducerBase,
    /// Shared state (consumers + release guards).
    shared: Rc<RefCell<SplitShared>>,
    /// This producer's index into `shared.consumers` and `shared.release_guards`.
    index: usize,
}

impl TileProducer for SplitProducer {
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
        let mut result = self
            .shared
            .borrow_mut()
            .producer
            .as_mut()
            .unwrap()
            .get(projection_guard);

        // Filter by the stored obsolete guard. Because upstream retains data according to the
        // intersection of all obsolete guards, it may have more data than this specific consumer
        // is interested in.
        let guard = self.shared.borrow().release_guards[self.index].clone();
        trace!("{} removing {guard:?} from {result:?}", self.name());
        result.remove_guarded(guard);
        result
    }

    fn release_impl(&mut self, obsolete_guard: TileGuard) {
        let result = {
            let mut shared = self.shared.borrow_mut();
            // Union with the existing stored guard so that the accumulated set of
            // delivered data grows monotonically.  Replacing (instead of union-ing)
            // would forget previously-released ranges, causing Split to re-deliver
            // data that a consumer has already released.
            let accumulated = shared.release_guards[self.index].union(&obsolete_guard);
            shared.release_guards[self.index] = accumulated;
            shared
                .release_guards
                .iter()
                .fold(self.tiling().universal_guard(), |acc, g| acc.intersect(g))
        };
        trace!("{} releasing: {result:?}", self.name());
        self.shared
            .borrow_mut()
            .producer
            .as_mut()
            .unwrap()
            .release(result);
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
        let input = self.input.get(projection_guard);
        trace!("{} received {input:?}", self.name());
        let upstream_obsolete = input.to_guard();
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
        // Also release upstream to handle the case where the consumer releases
        // data that was never produced.
        self.input.release(obsolete_guard.clone());
        trace!("{} now has cached {:?}", self.name(), self.cached_tile);
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

#[cfg(test)]
mod tests {
    use intervalsets::ops::Contains;
    use intervalsets::MaybeEmpty;

    use super::*;
    use crate::interpreter::{ColumnValue, Extent, Value};

    /// Helper: extract the `IntervalSet<usize>` from a `UIntRange` extent.
    fn uint_range_set(extent: &Extent) -> &IntervalSet<usize> {
        let Extent::UIntRange(ref s) = extent else {
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
}
