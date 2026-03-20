//! Tile operator and producer types for the CCL dataflow graph.
//!
//! A [`TileOperator`] is a static descriptor of a computation node — it knows
//! its output [`Tiling`] and can create a live [`TileProducer`] via
//! [`TileOperator::subscribe`].  A [`TileProducer`] is the runtime counterpart:
//! it can answer `get` queries and accept `release` notifications.
//!
//! Operators and producers mirror each other: `FooOperator` / `FooProducer`
//! pairs appear throughout the module.

use std::{cell::RefCell, collections::HashMap, hash::Hash, rc::Rc};

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

    /// Render this operator as an [`InspectNode`] for visualization.
    fn inspect(&self, _opts: &VizOptions) -> InspectNode;
}

/// Live runtime counterpart of a [`TileOperator`].
///
/// Created by [`TileOperator::subscribe`], a producer services `get` queries
/// and accepts `release` notifications from its consumer.
pub trait TileProducer {
    /// Return the [`Tiling`] that describes this producer's output shape.
    /// If the operator has unbound arguments, the tiling will be a curried function
    /// from inputs to the output.
    fn tiling(&self) -> &Tiling;

    /// Return the name of the concrete producer type.
    fn name(&self) -> &'static str {
        std::any::type_name::<Self>().rsplit_once("::").unwrap().1
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
    /// The default implementation heuristically extracts the type name from Debug
    /// output. Override this for proper visualization — the fallback exists only
    /// so that new Producer types are displayable before a custom impl is added.
    fn inspect(&self, _opts: &VizOptions) -> InspectNode;
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
    output_extent: &Extent,
) -> ColumnValue {
    match function_tile {
        Tile::Scalar(func) => match func.as_single() {
            Some(Value::ComputableFunction(f)) => f.apply(input),
            Some(Value::Function(bindings)) => {
                let output_values: Vec<Value> = if bindings_are_list(&bindings) {
                    let table: Vec<Value> = bindings.into_iter().map(|b| b.output).collect();
                    input
                        .drain_to_value_iter()
                        .map(|v| table[v.as_uint()].clone())
                        .collect()
                } else {
                    let table: HashMap<Value, Value> =
                        bindings.into_iter().map(|b| (b.input, b.output)).collect();
                    input
                        .drain_to_value_iter()
                        .map(|v| table[&v].clone())
                        .collect()
                };
                ColumnValue::from_values(output_values, output_extent)
            }
            None => ColumnValue::from_values(Vec::new(), output_extent),
            _ => panic!("apply_function_tile: Scalar tile is not a function value"),
        },
        Tile::SealedFunction {
            mut domain,
            codomain,
            ..
        } => {
            let Tile::Scalar(mut codomain_col) = *codomain else {
                panic!("apply_function_tile: SealedFunction must have a Scalar codomain")
            };
            let table: HashMap<Value, Value> = domain
                .drain_to_value_iter()
                .zip(codomain_col.drain_to_value_iter())
                .collect();
            let output_values: Vec<Value> = input
                .drain_to_value_iter()
                .map(|v| table[&v].clone())
                .collect();
            ColumnValue::from_values(output_values, output_extent)
        }
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

/// Applies a function operator element-wise over a sealed-function input.
///
/// `input` must be a `SealedFunction` tile; `function` is applied to each
/// codomain element.  The output is a `SealedFunction` with the same domain
/// and the function's codomain.
pub struct MapApply {
    /// Output tiling: `SealedFunction { domain: input.domain, codomain: function.codomain }`.
    tiling: Tiling,
    /// The sealed-function input to iterate over.
    input: Box<dyn TileOperator>,
    /// The function to apply to each element.
    function: Box<dyn TileOperator>,
}

impl MapApply {
    /// Create a new `Map` operator applying `function` to each element of `input`.
    ///
    /// The output `tiling` and `extent` are derived from the inputs: the codomain
    /// of `function` becomes the output value extent, threaded through the domain
    /// (if any) of `input`.
    pub fn new(input: Box<dyn TileOperator>, function: Box<dyn TileOperator>) -> Self {
        let output_tiling = function.tiling().codomain().unwrap_or_else(|| {
            panic!(
                "Map function had non-function tiling {:?}",
                function.tiling()
            )
        });
        let tiling = if let Tiling::SealedFunction {
            domain: input_domain_extent,
            codomain: input_codomain_tiling,
        } = input.tiling()
        {
            assert!(function
                .tiling()
                .domain_extent()
                .unwrap()
                .includes(&input_codomain_tiling.extent()));
            Tiling::SealedFunction {
                domain: input_domain_extent.clone(),
                codomain: Box::new(output_tiling),
            }
        } else {
            panic!(
                "Map requires SealedFunction input, got {:?}",
                input.tiling()
            );
        };
        Self {
            tiling,
            input,
            function,
        }
    }
}

impl TileOperator for MapApply {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("MapApply")
            .with_tiling(self.tiling.to_string())
            .child("fn", self.function.inspect(opts))
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
        Box::new(MapApplyProducer::new(
            self.tiling.clone(),
            input_producer,
            function_producer,
        ))
    }
}

struct MapApplyProducer {
    tiling: Tiling,
    input: Box<dyn TileProducer>,
    function: Box<dyn TileProducer>,
}

impl MapApplyProducer {
    pub fn new(
        tiling: Tiling,
        input: Box<dyn TileProducer>,
        function: Box<dyn TileProducer>,
    ) -> Self {
        Self {
            tiling,
            input,
            function,
        }
    }
}

impl TileProducer for MapApplyProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("MapApply")
            .with_tiling(self.tiling.to_string())
            .child("fn", self.function.inspect(opts))
            .child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let f_tiling = self.function.tiling();
        assert!(
            f_tiling.is_function(),
            "MapApply expected function tiling, Got {f_tiling:?}"
        );
        let f_codomain_extent = f_tiling.extent().split_function().unwrap().1.clone();
        let i_tiling = self.input.tiling();
        let input_guard = match projection_guard {
            TileGuard::Function(FunctionGuard::Domain(p)) => {
                TileGuard::Function(FunctionGuard::Domain(p))
            }
            _ => i_tiling.universal_guard(),
        };
        let input_result = self.input.get(input_guard);

        let Tile::SealedFunction {
            domain: i_domain,
            codomain: i_codomain,
            domain_predicate: i_domain_predicate,
        } = input_result
        else {
            panic!("Map only applies to SealedFunction tilings")
        };

        let function_result = self.function.get(f_tiling.universal_guard());
        let input = scalar_tile_to_column_value(*i_codomain);
        let output = apply_function_tile(function_result, input, &f_codomain_extent);
        Tile::SealedFunction {
            domain: i_domain,
            codomain: Box::new(Tile::Scalar(output)),
            domain_predicate: i_domain_predicate,
        }
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("MapApplyProducer release: {obsolete_guard:?}");
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

/// Takes a SealedFunction input and returns a SealedFunction with same domain
/// but with a constant codomain.
///
/// `input` must be a `SealedFunction` tile; `constant` must be a Scalar.
pub struct MapToConst {
    /// Output tiling: `SealedFunction { domain: input.domain, codomain: constant.codomain }`.
    tiling: Tiling,
    /// The sealed-function input to iterate over.
    input: Box<dyn TileOperator>,
    /// The constant to apply to each element.
    constant: Box<dyn TileOperator>,
}

impl MapToConst {
    /// Create a new `MapToConst` operator that maps any codomain to the given constant.
    pub fn new(input: Box<dyn TileOperator>, constant: Box<dyn TileOperator>) -> Self {
        let tiling = if let Tiling::SealedFunction {
            domain: input_domain_tiling,
            codomain: _,
        } = input.tiling()
        {
            assert!(constant.tiling().is_scalar());
            Tiling::SealedFunction {
                domain: input_domain_tiling.clone(),
                codomain: Box::new(constant.tiling().clone()),
            }
        } else {
            panic!(
                "Map requires SealedFunction input, got {:?}",
                input.tiling()
            );
        };
        Self {
            tiling,
            input,
            constant,
        }
    }
}

impl TileOperator for MapToConst {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("Map")
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
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
        Box::new(MapToConstProducer::new(
            self.tiling.clone(),
            input_producer,
            constant_producer,
        ))
    }
}

struct MapToConstProducer {
    tiling: Tiling,
    input: Box<dyn TileProducer>,
    constant: Box<dyn TileProducer>,
}

impl MapToConstProducer {
    pub fn new(
        tiling: Tiling,
        input: Box<dyn TileProducer>,
        constant: Box<dyn TileProducer>,
    ) -> Self {
        Self {
            tiling,
            input,
            constant,
        }
    }
}

impl TileProducer for MapToConstProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("Map")
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
            .child("constant", self.constant.inspect(opts))
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        let c_tiling = self.constant.tiling();
        assert!(
            c_tiling.is_scalar(),
            "MapToConst expected scalar tiling, Got {c_tiling:?}"
        );
        let i_tiling = self.input.tiling();
        let input_guard = match projection_guard {
            TileGuard::Function(FunctionGuard::Domain(p)) => {
                TileGuard::Function(FunctionGuard::Domain(p))
            }
            _ => i_tiling.universal_guard(),
        };
        let input_result = self.input.get(input_guard);

        let Tile::SealedFunction {
            domain: i_domain,
            codomain: _,
            domain_predicate: i_domain_predicate,
        } = input_result
        else {
            panic!("Map only applies to SealedFunction tilings")
        };

        let len = i_domain.len();
        let constant_result = self.constant.get(c_tiling.universal_guard());

        Tile::SealedFunction {
            domain: i_domain,
            codomain: Box::new(repeat_tile(constant_result, len)),
            domain_predicate: i_domain_predicate,
        }
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("MapToConstProducer release: {obsolete_guard:?}");
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

    fn inspect(&self, _opts: &VizOptions) -> InspectNode {
        InspectNode::leaf("IterateExtent").with_tiling(self.tiling().to_string())
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

        Box::new(IterateExtentProducer::new(
            self.extent.clone(),
            self.tiling.clone(),
        ))
    }
}

/// Producer for [`IterateExtent`]: emits an identity sealed-function tile.
struct IterateExtentProducer {
    /// The extent being iterated.
    ///
    /// For `UIntRange` extents this is an `IntervalSet<usize>` that shrinks
    /// directly as sub-intervals are released.
    extent: Extent,
    /// Output tiling.
    tiling: Tiling,
}

impl IterateExtentProducer {
    /// Create a new `IterateExtentProducer` for the given extent and tiling.
    pub fn new(extent: Extent, tiling: Tiling) -> Self {
        Self { extent, tiling }
    }
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

/// Release values from `extent` according to `obsolete_guard`.
///
/// For [`Extent::UIntRange`] extents, released sub-intervals are subtracted
/// directly from the stored [`IntervalSet<usize>`], so arbitrary non-contiguous
/// releases are handled without any external accumulator.
fn release_extent(extent: &mut Extent, obsolete_guard: &FunctionGuard) {
    match extent {
        Extent::Record(fields) => match obsolete_guard {
            g if g.is_univeral() => {
                for e in fields.values_mut() {
                    release_extent(e, g);
                }
            }
            g if g.is_empty() => {}
            FunctionGuard::Domain(p) => {
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
                        release_extent(e, &FunctionGuard::Domain(field_preds[f].clone()));
                    } else {
                        // TODO: handle the case where multiple fields have
                        // non-trivial predicates; requires releasing the
                        // intersection of projected ranges per dimension.
                    }
                }
            }
            _ => panic!("Unexected guard {obsolete_guard:?}"),
        },
        Extent::DataSourceDomain(source) => {
            source.borrow_mut().release(match obsolete_guard {
                FunctionGuard::Universal => Predicate::True,
                FunctionGuard::Domain(p) => p.clone(),
                _ => Predicate::False,
            });
        }
        Extent::UIntRange(remaining) => match obsolete_guard {
            FunctionGuard::Universal | FunctionGuard::Domain(Predicate::True) => {
                *remaining = IntervalSet::from(Interval::<usize>::empty());
            }
            FunctionGuard::Empty | FunctionGuard::Domain(Predicate::False) => {}
            FunctionGuard::Domain(Predicate::LessThanEq(v)) => {
                // Release every index up to and including v.
                let to_remove = IntervalSet::from(Interval::closed(0usize, v.as_uint()));
                *remaining = remaining.difference(&to_remove);
            }
            FunctionGuard::Domain(Predicate::Intervals(intervals)) => {
                // Subtract the released sub-intervals directly from the remaining set.
                let to_remove = predicate_intervals_to_usize(intervals);
                *remaining = remaining.difference(&to_remove);
            }
            _ => todo!("Got {obsolete_guard:?} for UIntRange"),
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
    fn inspect(&self, _opts: &VizOptions) -> InspectNode {
        InspectNode::leaf("IterateExtent").with_tiling(self.tiling().to_string())
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
        debug!("IterateExtentProducer release: {obsolete_guard:?}");
        let TileGuard::Function(obsolete_guard) = obsolete_guard else {
            panic!("IterateExtent::release expected SealedFunctionGuard, got {obsolete_guard:?}")
        };
        release_extent(&mut self.extent, &obsolete_guard);
    }

    fn tiling(&self) -> &Tiling {
        &self.tiling
    }
}

/// Produces a `SealedFunction` tile that maps each domain element of a data
/// source to its corresponding output value.
///
/// Unlike [`IterateExtent`], which produces an identity function (domain→domain),
/// `MapSource` calls [`DataSourceDomainExtentImpl::get`] for each domain key to
/// look up the actual output value.  The result is
/// `SealedFunction { domain: keys, codomain: Scalar(output_values) }`.
///
/// Notification at subscription time: if the source already has data when
/// `subscribe` is called, the consumer is notified immediately.
pub struct MapSource {
    input: Box<dyn TileOperator>,
    /// The data source providing both domain keys and value lookup.
    source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    /// Output tiling: `SealedFunction { domain: DataSourceDomain, codomain: Scalar(output_value_extent) }`.
    tiling: Tiling,
}

impl MapSource {
    /// Create a new `MapSource` wrapping `source`.
    ///
    /// The output tiling is derived from the source's
    /// [`output_value_extent`](DataSourceDomainExtentImpl::output_value_extent).
    pub fn new(
        source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
        input: Box<dyn TileOperator>,
    ) -> Self {
        let domain = Extent::DataSourceDomain(source.clone());
        let output_extent = source.borrow().output_value_extent();
        let tiling = Tiling::SealedFunction {
            domain,
            codomain: Box::new(Tiling::Scalar(output_extent)),
        };
        Self {
            input,
            source: source.clone(),
            tiling,
        }
    }
}

impl TileOperator for MapSource {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("MapSource")
            .annotate(self.source.borrow().get_id().to_string())
            .with_tiling(self.tiling().to_string())
            .child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(MapSourceProducer::new(
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler),
            self.source.clone(),
            self.tiling.clone(),
        ))
    }
}

/// Producer for [`MapSource`]: maps each domain key to its output value on `get`.
struct MapSourceProducer {
    input: Box<dyn TileProducer>,
    /// The data source used for both domain enumeration and value lookup.
    source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    /// Output tiling.
    tiling: Tiling,
}

impl MapSourceProducer {
    fn new(
        input: Box<dyn TileProducer>,
        source: Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
        tiling: Tiling,
    ) -> Self {
        Self {
            input,
            source,
            tiling,
        }
    }
}

impl TileProducer for MapSourceProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("MapSource")
            .annotate(self.source.borrow().get_id().to_string())
            .with_tiling(self.tiling().to_string())
            .child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_result = self.input.get(self.input.tiling().universal_guard());
        let Tile::SealedFunction {
            codomain: i_codomain,
            domain_predicate,
            ..
        } = input_result
        else {
            panic!("MapSource expected SealedFunction input tile")
        };
        let Tile::Scalar(domain) = *i_codomain else {
            panic!("MapSource expected SealedFunction input tile")
        };
        let source = self.source.borrow();
        let output_extent = source.output_value_extent();
        let output_values: Vec<Value> = domain
            .clone()
            .drain_to_value_iter()
            .map(|key| source.get(&key))
            .collect();
        let codomain = ColumnValue::from_values(output_values, &output_extent);
        Tile::SealedFunction {
            domain,
            codomain: Box::new(Tile::Scalar(codomain)),
            domain_predicate,
        }
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("MapSourceProducer release: {obsolete_guard:?}");
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

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut node = InspectNode::new("Zip").with_tiling(self.tiling.to_string());
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
        Box::new(ZipProducer::new(
            self.tiling.clone(),
            self.inputs
                .iter_mut()
                .map(|i| {
                    i.subscribe(
                        i.tiling().universal_guard(),
                        Box::new(consumer_wrapper.clone()),
                        scheduler,
                    )
                })
                .collect(),
        ))
    }
}

/// Producer for [`Zip`]: pulls each input and assembles a record-codomain tile.
pub struct ZipProducer {
    /// Output tiling.
    tiling: Tiling,
    /// Live input producers, in field order.
    inputs: Vec<Box<dyn TileProducer>>,
}

impl ZipProducer {
    /// Create a new `ZipProducer` from a tiling and a list of input producers.
    pub fn new(tiling: Tiling, inputs: Vec<Box<dyn TileProducer>>) -> Self {
        Self { tiling, inputs }
    }
}

impl TileProducer for ZipProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut node = InspectNode::new("Zip").with_tiling(self.tiling.to_string());
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
        debug!("ZipProducer release: {obsolete_guard:?}");
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

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut node = InspectNode::new("ScalarTuple").with_tiling(self.tiling.to_string());
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
        Box::new(ScalarTupleProducer::new(
            self.tiling.clone(),
            self.inputs
                .iter_mut()
                .map(|i| {
                    i.subscribe(
                        i.tiling().universal_guard(),
                        Box::new(consumer_wrapper.clone()),
                        scheduler,
                    )
                })
                .collect(),
        ))
    }
}

/// Producer for [`ScalarTuple`]: pulls each scalar input and combines them into
/// a `Tile::Scalar(ColumnValue::Records)`.
pub struct ScalarTupleProducer {
    tiling: Tiling,
    inputs: Vec<Box<dyn TileProducer>>,
}

impl ScalarTupleProducer {
    /// Create a new `ScalarTupleProducer` from a tiling and a list of input producers.
    pub fn new(tiling: Tiling, inputs: Vec<Box<dyn TileProducer>>) -> Self {
        Self { tiling, inputs }
    }
}

impl TileProducer for ScalarTupleProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut node = InspectNode::new("ScalarTuple").with_tiling(self.tiling.to_string());
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
        debug!("ScalarTupleProducer release: {obsolete_guard:?}");
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

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("Converse")
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(ConverseProducer::new(
            self.tiling().clone(),
            self.input
                .subscribe(self.tiling().universal_guard(), consumer, scheduler),
        ))
    }
}

/// Producer for [`Converse`]: inverts a sealed-function tile into a lookup-function tile.
pub struct ConverseProducer {
    /// Output tiling.
    tiling: Tiling,
    /// The upstream producer whose output is inverted.
    input: Box<dyn TileProducer>,
}

impl ConverseProducer {
    /// Create a new `ConverseProducer` from a tiling and an input producer.
    pub fn new(tiling: Tiling, input: Box<dyn TileProducer>) -> Self {
        Self { tiling, input }
    }
}

impl TileProducer for ConverseProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("Converse")
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        match input_tile {
            Tile::SealedFunction {
                mut domain,
                codomain,
                domain_predicate,
            } => match *codomain {
                Tile::Scalar(mut codomain) => {
                    // Invert the function: group domain values by their output value.
                    let mut grouped: HashMap<Value, Vec<Value>> = HashMap::new();
                    for (i, o) in domain
                        .drain_to_value_iter()
                        .zip(codomain.drain_to_value_iter())
                    {
                        grouped.entry(o).or_default().push(i);
                    }
                    // Sort by key so downstream consumers can do O(log n) binary-search lookups.
                    let mut sorted: Vec<(Value, Vec<Value>)> = grouped.into_iter().collect();
                    sorted.sort_by(|(a, _), (b, _)| {
                        a.partial_cmp(b)
                            .expect("CurriedFunction domain values must be comparable")
                    });
                    let (out_domain_extent, out_codomain_extent) = match &self.tiling {
                        Tiling::CurriedFunction {
                            domain1, codomain, ..
                        } => (domain1.clone(), codomain.clone()),
                        _ => unreachable!(),
                    };
                    let mut domain_vals: Vec<Value> = Vec::with_capacity(sorted.len());
                    let mut offset_vals: Vec<usize> = Vec::with_capacity(sorted.len());
                    let mut codomain_vals: Vec<Value> = Vec::new();
                    for (key, values) in sorted {
                        domain_vals.push(key);
                        offset_vals.push(codomain_vals.len());
                        codomain_vals.extend(values);
                    }
                    let output_codomain =
                        ColumnValue::from_values(codomain_vals, &out_codomain_extent);
                    Tile::curried_function(
                        ColumnValue::from_values(domain_vals, &out_domain_extent),
                        ColumnValue::UInts(offset_vals),
                        output_codomain.clone(),
                        output_codomain,
                        if domain_predicate.as_bool().unwrap_or(false) {
                            Predicate::True
                        } else {
                            Predicate::False
                        },
                    )
                }
                _ => panic!("Can only converse functions with scalar codomains"),
            },
            _ => panic!("Can only converse functions"),
        }
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("ConverseProducer release: {obsolete_guard:?}");
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

/// Applies a function to every value in a [`Tile::CurriedFunction`], producing a new
/// `CurriedFunction` with the same domain but mapped codomain values.
///
/// For a input `D → [C]` and a function `C → E`, `MapCompose` produces `D → [E]`
/// by applying the function independently to every element in each codomain list.
pub struct MapCompose {
    /// Output tiling: `CurriedFunction { domain: input.domain, codomain: function.output_extent }`.
    tiling: Tiling,
    /// The lookup-function input whose values are transformed.
    input: Box<dyn TileOperator>,
    /// The function applied to each value in the input's codomain lists.
    function: Box<dyn TileOperator>,
}

impl MapCompose {
    /// Create a new `MapCompose` operator.
    ///
    /// `input` must have a `CurriedFunction` tiling; `function` must have a function
    /// tiling whose domain includes the input's codomain extent.  The output tiling is
    /// `CurriedFunction { domain: input.domain, codomain: function.output_extent }`.
    pub fn new(input: Box<dyn TileOperator>, function: Box<dyn TileOperator>) -> Self {
        let (domain1, domain2, input_codomain) = match input.tiling() {
            Tiling::CurriedFunction {
                domain1,
                domain2,
                codomain,
            } => (domain1.clone(), domain2.clone(), codomain.clone()),
            t => panic!("MapCompose requires CurriedFunction input, got {t:?}"),
        };
        let output_tiling = function.tiling().codomain().unwrap_or_else(|| {
            panic!(
                "MapCompose function had non-function tiling {:?}",
                function.tiling()
            )
        });
        assert!(
            function
                .tiling()
                .domain_extent()
                .unwrap()
                .includes(&input_codomain),
            "MapCompose function domain must include input codomain"
        );
        let tiling = Tiling::CurriedFunction {
            domain1,
            domain2,
            codomain: output_tiling.extent(),
        };
        Self {
            tiling,
            input,
            function,
        }
    }
}

impl TileOperator for MapCompose {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("MapCompose")
            .with_tiling(self.tiling.to_string())
            .child("fn", self.function.inspect(opts))
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
        Box::new(MapComposeProducer {
            tiling: self.tiling.clone(),
            input: input_producer,
            function: function_producer,
        })
    }
}

/// Producer for [`MapCompose`].
struct MapComposeProducer {
    /// Output tiling.
    tiling: Tiling,
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
    /// The subscribed function producer.
    function: Box<dyn TileProducer>,
}

impl TileProducer for MapComposeProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("MapCompose")
            .with_tiling(self.tiling.to_string())
            .child("fn", self.function.inspect(opts))
            .child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let out_codomain_extent = match &self.tiling {
            Tiling::CurriedFunction { codomain, .. } => codomain.clone(),
            t => panic!("MapCompose output tiling is not CurriedFunction: {t:?}"),
        };
        let f_tiling = self.function.tiling();
        assert!(
            f_tiling.is_function(),
            "MapCompose expected function tiling, got {f_tiling:?}"
        );
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        let Tile::CurriedFunction {
            domain1,
            offsets,
            domain2,
            codomain,
            domain_predicate,
        } = input_tile
        else {
            panic!("MapCompose requires a CurriedFunction tile")
        };
        let function_tile = self.function.get(f_tiling.universal_guard());
        // All function representations map each codomain element 1-to-1, so domain
        // and offsets carry over unchanged; only the codomain values are remapped.
        let new_codomain = apply_function_tile(function_tile, codomain, &out_codomain_extent);
        Tile::curried_function(domain1, offsets, domain2, new_codomain, domain_predicate)
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("MapComposeProducer release: {obsolete_guard:?}");
        match obsolete_guard {
            g if g.is_universal() => self.input.release(self.input.tiling().universal_guard()),
            TileGuard::Function(FunctionGuard::Domain(p)) => self
                .input
                .release(TileGuard::Function(FunctionGuard::Domain(p))),
            TileGuard::Function(FunctionGuard::Codomain(g))
                if matches!(*g, TileGuard::Function(FunctionGuard::Domain(_))) =>
            {
                self.input
                    .release(TileGuard::Function(FunctionGuard::Codomain(g)))
            }
            _ => panic!("Unexpected obsolete guard: {obsolete_guard:?}"),
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

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("Filter")
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
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
        Box::new(FilterProducer::new(
            self.tiling.clone(),
            input_producer,
            predicate_producer,
        ))
    }
}

struct FilterProducer {
    tiling: Tiling,
    input: Box<dyn TileProducer>,
    predicate: Box<dyn TileProducer>,
}

impl FilterProducer {
    pub fn new(
        tiling: Tiling,
        input: Box<dyn TileProducer>,
        predicate: Box<dyn TileProducer>,
    ) -> Self {
        Self {
            tiling,
            input,
            predicate,
        }
    }
}

impl TileProducer for FilterProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("Filter")
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
            .child("predicate", self.predicate.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let pred_guard = self.predicate.tiling().universal_guard();
        let i_guard = self.input.tiling().universal_guard();
        let (domain_extent, codomain_tiling) = match self.tiling() {
            Tiling::SealedFunction { domain, codomain } => {
                (domain.clone(), codomain.as_ref().clone())
            }
            _ => panic!("Filter tiling must be SealedFunction"),
        };
        let codomain_extent = codomain_tiling.extent();
        let predicate_result = self.predicate.get(pred_guard);
        let input_result = self.input.get(i_guard);

        match (predicate_result, input_result) {
            // Scalar predicate applied element-wise to a function tile's domain.
            (
                Tile::Scalar(pred),
                Tile::SealedFunction {
                    mut domain,
                    codomain,
                    domain_predicate,
                },
            ) => {
                let mut codomain = scalar_tile_to_column_value(*codomain);
                match pred.as_single() {
                    Some(Value::Function(f)) => {
                        // Build the set of domain values where the predicate is true.
                        let keep_set: std::collections::HashSet<Value> = f
                            .into_iter()
                            .filter_map(|b| (b.output == Value::Bool(true)).then_some(b.input))
                            .collect();
                        let (kept_domain, kept_codomain): (Vec<Value>, Vec<Value>) = domain
                            .drain_to_value_iter()
                            .zip(codomain.drain_to_value_iter())
                            .filter(|(d, _)| keep_set.contains(d))
                            .unzip();
                        Tile::SealedFunction {
                            domain: ColumnValue::from_values(kept_domain, &domain_extent),
                            codomain: Box::new(column_value_to_tile(
                                ColumnValue::from_values(kept_codomain, &codomain_extent),
                                &codomain_tiling,
                            )),
                            domain_predicate,
                        }
                    }
                    Some(Value::ComputableFunction(f)) => {
                        // Apply predicate to all domain values at once to get a bool mask.
                        let mut mask = f.apply(domain.clone());
                        let (kept_domain, kept_codomain): (Vec<Value>, Vec<Value>) = domain
                            .drain_to_value_iter()
                            .zip(codomain.drain_to_value_iter())
                            .zip(mask.drain_to_value_iter())
                            .filter_map(|((d, c), m)| (m == Value::Bool(true)).then_some((d, c)))
                            .unzip();
                        Tile::SealedFunction {
                            domain: ColumnValue::from_values(kept_domain, &domain_extent),
                            codomain: Box::new(column_value_to_tile(
                                ColumnValue::from_values(kept_codomain, &codomain_extent),
                                &codomain_tiling,
                            )),
                            domain_predicate,
                        }
                    }
                    _ => panic!("Filter predicate is not a function"),
                }
            }
            // Both predicate and input are function tiles sharing the same domain.
            (
                Tile::SealedFunction {
                    domain: mut pred_inputs,
                    codomain: pred_outputs,
                    ..
                },
                Tile::SealedFunction {
                    domain: mut i_inputs,
                    codomain: i_outputs,
                    domain_predicate,
                },
            ) => {
                let mut pred_outputs = scalar_tile_to_column_value(*pred_outputs);
                let mut i_outputs = scalar_tile_to_column_value(*i_outputs);
                // Build a domain-value → bool map from the predicate tile.
                let keep_map: HashMap<Value, bool> = pred_inputs
                    .drain_to_value_iter()
                    .zip(pred_outputs.drain_to_value_iter())
                    .map(|(k, v)| (k, v == Value::Bool(true)))
                    .collect();
                let (kept_domain, kept_codomain): (Vec<Value>, Vec<Value>) = i_inputs
                    .drain_to_value_iter()
                    .zip(i_outputs.drain_to_value_iter())
                    .filter(|(d, _)| *keep_map.get(d).unwrap_or(&false))
                    .unzip();
                Tile::SealedFunction {
                    domain: ColumnValue::from_values(kept_domain, &domain_extent),
                    codomain: Box::new(column_value_to_tile(
                        ColumnValue::from_values(kept_codomain, &codomain_extent),
                        &codomain_tiling,
                    )),
                    domain_predicate,
                }
            }
            _ => panic!("Invalid Filter input tiles"),
        }
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("FilterProducer release: {obsolete_guard:?}");
        self.input.release(obsolete_guard);
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
    /// The aggregation operation (Sum, Max, …).
    kind: AggregateKind,
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
            accumulator: kind.output_extent(&codomain_extent).unwrap_or_else(err),
        };
        Self {
            input,
            kind,
            tiling,
        }
    }
}

impl TileOperator for Aggregate {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("Aggregate")
            .annotate(format!("({:?})", self.kind))
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
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
        Box::new(AggregateProducer::new(
            self.tiling.clone(),
            input_producer,
            self.kind.clone(),
        ))
    }
}

struct AggregateProducer {
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation.
    kind: AggregateKind,
    /// Output tiling.
    tiling: Tiling,
    /// Running accumulation state; updated in place on each `get`.
    accumulator: Tile,
}

impl AggregateProducer {
    /// Construct an `AggregateProducer`, seeding the accumulator with the identity element.
    fn new(tiling: Tiling, input: Box<dyn TileProducer>, kind: AggregateKind) -> Self {
        let accumulator = match &tiling {
            Tiling::Aggregation {
                accumulator: acc_extent,
            } => Tile::Aggregation {
                accumulator: kind.initial_accumulator(acc_extent),
                terminal: ColumnValue::Bools(BitVec::from_elem(1, false)),
            },
            other => panic!("AggregateProducer created with non-Aggregation tiling: {other:?}"),
        };
        Self {
            tiling,
            input,
            kind,
            accumulator,
        }
    }
}

impl TileProducer for AggregateProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("Aggregate")
            .annotate(format!("({:?})", self.kind))
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let i_tiling = self.input.tiling().clone();
        let input_result = self.input.get(i_tiling.universal_guard());
        let is_terminal = input_result.is_terminal();
        let values = match input_result {
            Tile::SealedFunction {
                domain,
                codomain,
                domain_predicate,
            } => {
                self.input
                    .release(TileGuard::Function(FunctionGuard::Domain(
                        Predicate::from_column_value(&domain).union(&domain_predicate),
                    )));
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
        debug!("AggregateProducer release: {obsolete_guard:?}");
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

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("ExtractAggregate").child("input", self.input.inspect(opts))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        consumer: Box<dyn Consumer>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        Box::new(ExtractAggregateProducer::new(
            self.tiling().clone(),
            self.input
                .subscribe(self.input.tiling().universal_guard(), consumer, scheduler),
            self.kind.clone(),
            self.only_terminal,
        ))
    }
}

struct ExtractAggregateProducer {
    input: Box<dyn TileProducer>,
    tiling: Tiling,
    kind: AggregateKind,
    only_terminal: bool,
}

impl ExtractAggregateProducer {
    pub fn new(
        tiling: Tiling,
        input: Box<dyn TileProducer>,
        kind: AggregateKind,
        only_terminal: bool,
    ) -> Self {
        Self {
            input,
            tiling,
            kind,
            only_terminal,
        }
    }
}

impl TileProducer for ExtractAggregateProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("ExtractAggregate").child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_result = self.input.get(self.input.tiling().universal_guard());
        let Tile::Aggregation {
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
                Tile::Scalar(ColumnValue::single(self.kind.extract(&accumulator)))
            } else {
                self.tiling().empty_tile()
            }
        } else {
            todo!()
        }
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("ExtractAggregateProducer release: {obsolete_guard:?}");
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
                Tiling::Aggregation { accumulator } => Tiling::SealedFunction {
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

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("MapExtractAggregate")
            .annotate(format!("({:?})", self.kind))
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
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
            tiling: self.tiling.clone(),
            input: input_producer,
            kind: self.kind.clone(),
        })
    }
}

/// Producer for [`MapExtractAggregate`].
struct MapExtractAggregateProducer {
    /// Output tiling.
    tiling: Tiling,
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation used to extract final values.
    kind: AggregateKind,
}

impl TileProducer for MapExtractAggregateProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("MapExtractAggregate")
            .annotate(format!("({:?})", self.kind))
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_result = self.input.get(self.input.tiling().universal_guard());
        let Tile::SealedFunction {
            mut domain,
            codomain,
            domain_predicate,
        } = input_result
        else {
            panic!("MapExtractAggregate expected SealedFunction tile")
        };
        let Tile::Aggregation {
            mut accumulator,
            mut terminal,
        } = *codomain
        else {
            panic!("MapExtractAggregate expected SealedFunction(Aggregation) codomain")
        };
        let output_extent = self.tiling.codomain().unwrap().extent();
        let domain_extent = self.tiling.domain_extent().unwrap();
        // Emit only the domain elements whose per-key aggregation is terminal.
        let (kept_domain, kept_values): (Vec<Value>, Vec<Value>) = domain
            .drain_to_value_iter()
            .zip(accumulator.drain_to_value_iter())
            .zip(terminal.drain_to_value_iter())
            .filter_map(|((d, a), t)| {
                if t.as_bool() {
                    Some((d, self.kind.extract(&ColumnValue::single(a))))
                } else {
                    None
                }
            })
            .unzip();
        Tile::SealedFunction {
            domain: ColumnValue::from_values(kept_domain, &domain_extent),
            codomain: Box::new(Tile::Scalar(ColumnValue::from_values(
                kept_values,
                &output_extent,
            ))),
            domain_predicate,
        }
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("MapExtractAggregateProducer release: {obsolete_guard:?}");
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

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("MapAggregate")
            .annotate(format!("({:?})", self.kind))
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
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
            tiling: self.tiling.clone(),
            input: input_producer,
            kind: self.kind.clone(),
            accumulators: HashMap::new(),
        })
    }
}

/// Producer for [`MapAggregate`].
struct MapAggregateProducer {
    /// Output tiling.
    tiling: Tiling,
    /// The subscribed lookup-function producer.
    input: Box<dyn TileProducer>,
    /// The aggregation operation.
    kind: AggregateKind,
    /// Running per-key accumulators, grown as new keys arrive across `get` calls.
    accumulators: HashMap<Value, ColumnValue>,
}

impl TileProducer for MapAggregateProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("MapAggregate")
            .annotate(format!("({:?})", self.kind))
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        let input_tile = self.input.get(self.input.tiling().universal_guard());
        let Tile::CurriedFunction {
            domain1,
            offsets,
            domain2,
            codomain,
            domain_predicate,
        } = input_tile
        else {
            panic!("MapAggregate requires a CurriedFunction tile")
        };
        // output_extent is the accumulator extent from the Aggregation codomain tiling.
        let output_extent = self.tiling.codomain().unwrap().extent();
        let domain_extent = self.tiling.domain_extent().unwrap();
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
        self.input
            .release(TileGuard::Function(FunctionGuard::Codomain(Box::new(
                TileGuard::Function(FunctionGuard::Domain(Predicate::from_column_value(
                    &domain2,
                ))),
            ))));

        // Build the output tile from all known per-key accumulators.
        // TODO apply the domain predicate to each domain value.
        let is_terminal = domain_predicate.as_bool().unwrap_or(false);
        let n = self.accumulators.len();
        let (domain_values, accumulator_values): (Vec<Value>, Vec<Value>) = self
            .accumulators
            .iter()
            .map(|(key, acc)| (key.clone(), self.kind.extract(acc)))
            .unzip();
        Tile::SealedFunction {
            domain: ColumnValue::from_values(domain_values, &domain_extent),
            codomain: Box::new(Tile::Aggregation {
                accumulator: ColumnValue::from_values(accumulator_values, &output_extent),
                terminal: ColumnValue::Bools(BitVec::from_elem(n, is_terminal)),
            }),
            domain_predicate,
        }
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("MapAggregateProducer release: {obsolete_guard:?}");
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
pub struct Split {
    input: Rc<RefCell<Box<dyn TileOperator>>>,
    tiling: Tiling,
    /// All mutable shared state.  Created eagerly so that clones produced by
    /// [`Split::split`] always share the same object.
    shared: Rc<RefCell<SplitShared>>,
    /// True for the original handle returned by [`Split::new`]; false for
    /// every copy returned by [`Split::split`].  The primary renders its input
    /// subtree in inspect; copies emit a back-reference.
    primary: bool,
}

impl Split {
    /// Construct a new `Split` wrapping `input`.
    pub fn new(input: Box<dyn TileOperator>) -> Self {
        let tiling = input.tiling().clone();
        let shared = Rc::new(RefCell::new(SplitShared {
            producer: None,
            consumers: Vec::new(),
            release_guards: Vec::new(),
        }));
        Self {
            input: Rc::new(RefCell::new(input)),
            tiling,
            shared,
            primary: true,
        }
    }

    /// Return a new handle to the same split.  All handles share the same
    /// inner producer and consumer list; subscribing to any of them is
    /// equivalent.
    pub fn split(&self) -> Self {
        Self {
            input: self.input.clone(),
            tiling: self.tiling.clone(),
            shared: self.shared.clone(), // shares the Rc — always connected
            primary: false,
        }
    }
}

impl TileOperator for Split {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let id = Rc::as_ptr(&self.shared) as usize;
        if self.primary {
            InspectNode::new(format!("Split#{id:x}"))
                .with_tiling(self.tiling().to_string())
                .child("input", self.input.borrow().inspect(opts))
        } else {
            InspectNode::leaf(format!("→ Split#{id:x}"))
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
            shared.release_guards.push(self.tiling.universal_guard());
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
            tiling: self.tiling.clone(),
            shared: self.shared.clone(),
            index,
        })
    }
}

struct SplitProducer {
    tiling: Tiling,
    /// Shared state (consumers + release guards).
    shared: Rc<RefCell<SplitShared>>,
    /// This producer's index into `shared.consumers` and `shared.release_guards`.
    index: usize,
}

impl TileProducer for SplitProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let id = Rc::as_ptr(&self.shared) as usize;
        if self.index == 0 {
            InspectNode::new(format!("Split#{id:x}"))
                .with_tiling(self.tiling.to_string())
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
            InspectNode::leaf(format!("→ Split#{id:x}"))
        }
    }

    fn get_impl(&mut self, projection_guard: TileGuard) -> Tile {
        self.shared
            .borrow_mut()
            .producer
            .as_mut()
            .unwrap()
            .get(projection_guard)
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("SplitProducer release: {obsolete_guard:?}");
        let result = {
            let mut shared = self.shared.borrow_mut();
            shared.release_guards[self.index] = obsolete_guard;
            shared
                .release_guards
                .iter()
                .fold(self.tiling.universal_guard(), |acc, g| acc.intersect(g))
        };
        self.shared
            .borrow_mut()
            .producer
            .as_mut()
            .unwrap()
            .release(result);
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

    fn inspect(&self, _opts: &VizOptions) -> InspectNode {
        InspectNode::leaf("Constant")
            .with_tiling(self.tiling.to_string())
            .annotate(format!("{}", self.value))
    }

    fn subscribe(
        &mut self,
        _intent_guard: TileGuard,
        mut consumer: Box<dyn Consumer>,
        _scheduler: &mut Scheduler,
    ) -> Box<dyn TileProducer> {
        consumer.notify();
        Box::new(ConstantProducer {
            value: self.value.clone(),
            tiling: self.tiling.clone(),
            released: false,
        })
    }
}

struct ConstantProducer {
    value: Value,
    tiling: Tiling,
    released: bool,
}

impl TileProducer for ConstantProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, _opts: &VizOptions) -> InspectNode {
        InspectNode::leaf("Constant")
            .with_tiling(self.tiling.to_string())
            .annotate(format!("{}", self.value))
    }

    fn get_impl(&mut self, _projection_guard: TileGuard) -> Tile {
        // sanity check we don't call get after a universal release
        assert!(!self.released);
        Tile::Scalar(ColumnValue::single(self.value.clone()))
    }

    fn release(&mut self, obsolete_guard: TileGuard) {
        debug!("ConstantProducer release: {obsolete_guard:?}");
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

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("ToScalar")
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
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
            input: input_producer,
            tiling: self.tiling.clone(),
        })
    }
}

struct ToScalarProducer {
    /// The subscribed input producer.
    input: Box<dyn TileProducer>,
    /// Cached output tiling (the codomain of the input's `SealedFunction`).
    tiling: Tiling,
}

impl TileProducer for ToScalarProducer {
    fn tiling(&self) -> &Tiling {
        &self.tiling
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("ToScalar")
            .with_tiling(self.tiling.to_string())
            .child("input", self.input.inspect(opts))
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
        debug!("ToScalarProducer release: {obsolete_guard:?}");
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

    /// `FunctionGuard::Universal` releases everything — extent becomes empty.
    #[test]
    fn release_extent_universal_clears_uint_range() {
        let mut extent = Extent::uint_range(5); // [0, 4]
        release_extent(&mut extent, &FunctionGuard::Universal);
        assert!(
            uint_range_set(&extent).is_empty(),
            "universal release should empty the extent"
        );
    }

    /// `Predicate::True` is equivalent to `Universal` — same result.
    #[test]
    fn release_extent_predicate_true_clears_uint_range() {
        let mut extent = Extent::uint_range(5);
        release_extent(&mut extent, &FunctionGuard::Domain(Predicate::True));
        assert!(uint_range_set(&extent).is_empty());
    }

    /// `FunctionGuard::Empty` releases nothing — extent is unchanged.
    #[test]
    fn release_extent_empty_guard_is_noop() {
        let mut extent = Extent::uint_range(5); // [0, 4]
        release_extent(&mut extent, &FunctionGuard::Empty);
        let s = uint_range_set(&extent);
        for i in 0..5usize {
            assert!(s.contains(&i), "{i} should still be present");
        }
    }

    /// `Predicate::False` also releases nothing.
    #[test]
    fn release_extent_predicate_false_is_noop() {
        let mut extent = Extent::uint_range(5);
        release_extent(&mut extent, &FunctionGuard::Domain(Predicate::False));
        let s = uint_range_set(&extent);
        for i in 0..5usize {
            assert!(s.contains(&i), "{i} should still be present");
        }
    }

    /// `Predicate::LessThanEq(v)` releases [0, v] inclusive.
    #[test]
    fn release_extent_less_than_eq_releases_prefix() {
        let mut extent = Extent::uint_range(10); // [0, 9]
        release_extent(
            &mut extent,
            &FunctionGuard::Domain(Predicate::LessThanEq(Value::UInt(4))),
        );
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
        release_extent(&mut extent, &FunctionGuard::Domain(p));
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
        release_extent(&mut extent, &FunctionGuard::Domain(p));
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
        release_extent(&mut extent, &FunctionGuard::Domain(p));

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
        let mut producer = IterateExtentProducer::new(extent, tiling);
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
