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
    rc::Rc,
    sync::{Mutex, OnceLock},
};

use bit_vec::BitVec;
use intervalsets::{ops::Difference, Bounding, Interval, IntervalSet};
use log::{debug, trace};

pub use crate::interpreter::tiling::{FunctionGuard, Predicate, Tile, TileGuard, Tiling};
use crate::{
    ccl::AggregateKind,
    interpreter::{
        bindings_are_list, transform_hashmap_values, tuple_field, BaseType, ColumnValue, Consumer,
        DataSourceDomainExtentImpl, Extent, NotifyOrSubscribeResult, Scheduler, Value,
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
}

/// Live runtime counterpart of a [`TileOperator`].
///
/// Created by [`TileOperator::subscribe`], a producer services `get` queries
/// and accepts `release` notifications from its consumer.
pub trait TileProducer {
    /// Return the shared identity/tiling state for this producer.
    ///
    /// Implement as `fn base(&self) -> &ProducerBase { &self.base }`.
    fn base(&self) -> &ProducerBase;

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

    /// Fetch the current tile value.
    fn get(&mut self, projection_guard: TileGuard) -> Tile {
        let result = self.get_impl(projection_guard);
        trace!(
            "{} produced {:?} for tiling {}",
            self.name(),
            result,
            self.tiling()
        );
        assert!(
            result.check_from(self.tiling()),
            "{result:?} vs {:?}",
            self.tiling()
        );
        result
    }

    /// Fetch the current tile value.
    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile;

    /// Release interest in a region.
    /// The `obsolete_guard` specifies a sub-region of the subscription that
    /// is no longer needed. Returns an expanded obsolete guard that may be
    /// larger if the producer has additional obsolescence information (e.g.,
    /// from variables with their own obsolete guards).
    fn release(&mut self, obsolete_guard: TileGuard);

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
        let function_domain_extent = function.tiling().domain_extent().unwrap_or_else(|| {
            panic!(
                "Map function had non-function tiling {:?}",
                function.tiling()
            )
        });
        let output_tiling = function.tiling().codomain().unwrap_or_else(|| {
            panic!(
                "Map function had non-function tiling {:?}",
                function.tiling()
            )
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
            base: ProducerBase {
                id: MapResultProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
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
    fn base(&self) -> &ProducerBase {
        &self.base
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("fn", self.function.inspect(opts))
            .child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let f_tiling = self.function.tiling();
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
        process_tile_result(self.tiling(), input_tile, move |codomain| {
            apply_function_tile(function_tile, codomain, f_domain_extent, f_codomain_extent)
        })
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
        // TODO once we have guards that express codomain predicates, handle them here
        self.input.release(obsolete_guard);
    }
}

/// Takes a function input and returns a function with the same structure
/// but with a constant codomain.
///
/// `input` must be a `SealedFunction` or `CurriedFunction` tile; `constant` must be a Scalar.
pub struct MapResultToConst {
    /// Output tiling matches `input` tiling, transforming the codomain to `constant`.
    tiling: Tiling,
    /// The sealed-function input to iterate over.
    input: Box<dyn TileOperator>,
    /// The constant to apply to each element.
    constant: Box<dyn TileOperator>,
}

impl MapResultToConst {
    /// Create a new `MapResultToConst` operator that maps any codomain to the given constant.
    pub fn new(input: Box<dyn TileOperator>, constant: Box<dyn TileOperator>) -> Self {
        let tiling = change_tiling_result(input.tiling(), |_| constant.tiling().clone());
        Self {
            tiling,
            input,
            constant,
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
            base: ProducerBase {
                id: MapToConstProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
            input: input_producer,
            constant: constant_producer,
        })
    }
}

struct MapToConstProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    constant: Box<dyn TileProducer>,
}

impl TileProducer for MapToConstProducer {
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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

        process_tile_result(self.tiling(), input_tile, move |codomain| {
            scalar_tile_to_column_value(repeat_tile(constant_tile, codomain.len()))
        })
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
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
        }

        Box::new(IterateExtentProducer {
            base: ProducerBase {
                id: IterateExtentProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
            extent: self.extent.clone(),
        })
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
}

fn get_iterate_extent_predicate(extent: &Extent) -> Predicate {
    match extent {
        Extent::DataSourceDomain(source) => source.borrow().get_yield_predicate(),
        Extent::Record(fields) => Predicate::Record(transform_hashmap_values(
            fields,
            get_iterate_extent_predicate,
        )),
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
fn release_extent(extent: &mut Extent, pred: &Predicate) {
    match extent {
        Extent::Record(fields) => match pred {
            Predicate::True => {
                for e in fields.values_mut() {
                    release_extent(e, &Predicate::True);
                }
            }
            Predicate::False => {}
            // Or: apply each arm independently.  Each arm describes a distinct
            // sub-region; releasing all arms releases their union.
            Predicate::Or(arms) => {
                for arm in arms {
                    release_extent(extent, arm);
                }
            }
            p => {
                // A Record predicate is a conjunction: {f0: p0, f1: p1} means
                // "release pairs where p0(f0) AND p1(f1)".  We can only safely
                // advance a dimension's extent when all other dimensions are
                // unconstrained (Predicate::True), because the AND means the
                // full cross-product sub-space is released along that axis.
                let field_preds = p.split_record(fields);
                if field_preds
                    .values()
                    .filter(|p| **p == Predicate::True)
                    .count()
                    < field_preds.len() - 1
                {
                    unimplemented!("Got predicate {p:?}")
                }
                for (f, e) in fields.iter_mut() {
                    let others_all_true = field_preds
                        .iter()
                        .all(|(k, p)| k == f || *p == Predicate::True);
                    if others_all_true {
                        release_extent(e, &field_preds[f]);
                    } else {
                        // TODO: handle the case where multiple fields have
                        // non-trivial predicates; requires releasing the
                        // intersection of projected ranges per dimension.
                    }
                }
            }
        },
        Extent::DataSourceDomain(source) => {
            source.borrow_mut().release(pred.clone());
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
fn iterate_extent(extent: &Extent) -> ColumnValue {
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
        Extent::DataSourceDomain(source_impl) => source_impl.borrow_mut().get_elements(),
        Extent::Record(fields) => iterate_record(fields),
        Extent::Restricted { .. } => {
            panic!("Iterating over restricted extents not supported; use Filter operators instead")
        }
        _ => panic!("Attempted to iterate on infinite Extent"),
    }
}

fn iterate_record(fields: &HashMap<String, Extent>) -> ColumnValue {
    let data: HashMap<String, ColumnValue> = fields
        .iter()
        .map(|(field, field_extent)| (field.clone(), iterate_extent(field_extent)))
        .collect();
    ColumnValue::cartesian_product(data)
}

impl TileProducer for IterateExtentProducer {
    fn base(&self) -> &ProducerBase {
        &self.base
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let values = iterate_extent(&self.extent);
        let domain_predicate = get_iterate_extent_predicate(&self.extent);
        Tile::SealedFunction {
            domain: values.clone(),
            codomain: Box::new(Tile::Scalar(values)),
            domain_predicate,
        }
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
        let TileGuard::Function(FunctionGuard::Domain(pred)) = obsolete_guard else {
            panic!("IterateExtent::release expected Domain guard, got {obsolete_guard:?}")
        };
        release_extent(&mut self.extent, &pred);
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
        Box::new(MapResultWithSourceProducer {
            base: ProducerBase {
                id: MapResultWithSourceProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
            input: self
                .input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler),
            source: self.source.clone(),
        })
    }
}

/// Producer for [`MapNSource`]: maps each domain key to its output value on `get`.
struct MapResultWithSourceProducer {
    base: ProducerBase,
    input: Box<dyn TileProducer>,
    /// The data source used for both domain enumeration and value lookup.
    source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
}

impl TileProducer for MapResultWithSourceProducer {
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
        self.input.release(obsolete_guard);
    }
}

/// Combines multiple sealed-function operators sharing the same domain into a
/// single sealed-function operator whose codomain is a record of all their codomains.
///
/// All inputs must have `SealedFunction` tilings with compatible domains.
/// Output fields are named `_0`, `_1`, … matching the input order.
pub struct Zip {
    /// Output tiling: `SealedFunction { domain: shared_domain, codomain: Record { _0, _1, … } }`.
    tiling: Tiling,
    /// The input sealed-function operators to zip together.
    inputs: Vec<Box<dyn TileOperator>>,
}

impl Zip {
    /// Create a new `Zip` operator over the given input operators.
    ///
    /// All inputs must be `SealedFunction` tilings with the same domain.
    /// The output `tiling` and `extent` are derived: each input's value extent
    /// becomes a field (`_0`, `_1`, …) in a `Record` codomain.
    pub fn new(inputs: Vec<Box<dyn TileOperator>>) -> Self {
        assert!(!inputs.is_empty(), "Zip requires at least one input");
        let domain = inputs[0]
            .tiling()
            .domain_extent()
            .expect("Zip: all inputs must have a SealedFunction tiling")
            .clone();
        let tiling = Tiling::SealedFunction {
            domain,
            codomain: Box::new(Tiling::Record(
                inputs
                    .iter()
                    .enumerate()
                    .map(|(i, op)| {
                        (
                            tuple_field(i),
                            op.tiling().codomain().expect("Expected function").clone(),
                        )
                    })
                    .collect(),
            )),
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
            base: ProducerBase {
                id: ZipProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
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
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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
                    if let Some(ref prev) = domain_pred {
                        assert_eq!(
                            prev, &domain_predicate,
                            "Zip: all inputs must have the same domain predicate"
                        );
                    }
                    domain_pred = Some(domain_predicate);
                    output_domain = Some(domain);
                    codomains.push(*codomain);
                }
                _ => panic!("Can only zip functions"),
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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
        self.inputs.iter_mut().for_each(|i| {
            i.release(match &obsolete_guard {
                g if g.is_universal() => i.tiling().universal_guard(),
                g if g.is_empty() => i.tiling().empty_guard(),
                TileGuard::Function(FunctionGuard::Domain(p)) => {
                    TileGuard::Function(FunctionGuard::Domain(p.clone()))
                }
                _ => todo!(),
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
            base: ProducerBase {
                id: ScalarTupleProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
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
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
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
            base: ProducerBase {
                id: ConverseProducer::alloc_id(),
                tiling: self.tiling().clone(),
            },
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
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
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
            base: ProducerBase {
                id: FilterProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
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
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
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
            base: ProducerBase {
                id: RestrictProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
            predicate: predicate_producer,
        })
    }
}

struct RestrictProducer {
    base: ProducerBase,
    predicate: Box<dyn TileProducer>,
}

impl TileProducer for RestrictProducer {
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
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
            base: ProducerBase {
                id: Self::alloc_id(),
                tiling,
            },
            input,
            kind,
            accumulator,
        }
    }
}

impl TileProducer for AggregateProducer {
    fn base(&self) -> &ProducerBase {
        &self.base
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let i_tiling = self.input.tiling().clone();
        let input_result = self.input.get(i_tiling.universal_guard());
        let is_terminal = input_result.is_terminal();
        let upstream_guard = input_result.to_guard();
        let values = match input_result {
            Tile::SealedFunction { codomain, .. } => {
                self.input.release(upstream_guard);
                scalar_tile_to_column_value(*codomain)
            }
            Tile::Scalar(ColumnValue::Variants(v)) if matches!(v[0], Value::Function(..)) => {
                ColumnValue::from_values(
                    v[0].as_function()
                        .iter()
                        .map(|b| b.output.clone())
                        .collect(),
                    &i_tiling.codomain().unwrap().extent(),
                )
            }
            t => panic!("Aggregate expected function tiling, got {t:?}"),
        };
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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
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
            base: ProducerBase {
                id: ExtractAggregateProducer::alloc_id(),
                tiling: self.tiling().clone(),
            },
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
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
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
            base: ProducerBase {
                id: MapExtractAggregateProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
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
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
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
            base: ProducerBase {
                id: MapAggregateProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
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
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
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
            base: ProducerBase {
                id: self.shared.borrow().id,
                tiling: self.tiling.clone(),
            },
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
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!(
            "Release called on {} with stored guards {:?}: {obsolete_guard:?}",
            self.name(),
            self.shared.borrow().release_guards
        );
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
        debug!("{} releasing: {result:?}", self.name());
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
            base: ProducerBase {
                id: MemoProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
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
    fn base(&self) -> &ProducerBase {
        &self.base
    }

    fn add_inspect_children(&self, node: InspectNode, opts: &VizOptions) -> InspectNode {
        node.child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let input = self.input.get(projection_guard);
        trace!("{} received {input:?}", self.name());
        let upstream_obsolete = input.to_guard();
        debug!("{} releasing {upstream_obsolete:?}", self.name());
        self.input.release(upstream_obsolete);
        trace!(
            "{} merging {input:?} into {:?}",
            self.name(),
            self.cached_tile
        );
        self.cached_tile.merge(input);
        self.cached_tile.clone()
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("Release called on {}: {obsolete_guard:?}", self.name());
        // Remove any released data from the cached tile since the consumer
        // is no longer interested.
        self.cached_tile.remove_guarded(obsolete_guard.clone());
        // Also release upstream to handle the case where the consumer releases
        // data that was never produced.
        self.input.release(obsolete_guard);
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
            base: ProducerBase {
                id: ConstantProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
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
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
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
            base: ProducerBase {
                id: ToScalarProducer::alloc_id(),
                tiling: self.tiling.clone(),
            },
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
    fn base(&self) -> &ProducerBase {
        &self.base
    }

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

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("{} release: {obsolete_guard:?}", self.name());
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
        release_extent(&mut extent, &Predicate::True);
        assert!(
            uint_range_set(&extent).is_empty(),
            "True release should empty the extent"
        );
    }

    /// `Predicate::False` releases nothing — extent is unchanged.
    #[test]
    fn release_extent_predicate_false_is_noop() {
        let mut extent = Extent::uint_range(5); // [0, 4]
        release_extent(&mut extent, &Predicate::False);
        let s = uint_range_set(&extent);
        for i in 0..5usize {
            assert!(s.contains(&i), "{i} should still be present");
        }
    }

    /// `Predicate::LessThanEq(v)` releases [0, v] inclusive.
    #[test]
    fn release_extent_less_than_eq_releases_prefix() {
        let mut extent = Extent::uint_range(10); // [0, 9]
        release_extent(&mut extent, &Predicate::LessThanEq(Value::UInt(4)));
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
        release_extent(&mut extent, &p);
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
        release_extent(&mut extent, &p);
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
        release_extent(&mut extent, &p);

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
            base: ProducerBase { id: 0, tiling },
            extent,
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
}
