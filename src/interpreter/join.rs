//! Join and restriction operators for multi-generator list comprehensions.
//!
//! This module provides the restriction computation infrastructure used when evaluating
//! `where`-clause predicates over cross-products of generators, as well as the [`Converse`]
//! operator that inverts a function mapping for reverse lookups.
//!
//! ## Restriction operators
//!
//! [`ComputeRestriction`] wraps any boolean-typed [`Operator`] (typically a `Lambda`)
//! and records the join strategy it represents via [`RestrictionType`]:
//!
//! - [`RestrictionType::ArbitraryPred`]: evaluates the predicate for every element via a
//!   loop join and returns a `BitVec` correlation vector.
//! - [`RestrictionType::HashJoin`]: the wrapped operator is a hash-join kernel that returns
//!   matching `(build, probe)` index pairs in O(N+M) time.
//!
//! TODO: unifiy the two approaches so that they are composable
//!
//! The produced data is consumed by [`Restriction::get_correlations`] in `types.rs`, which
//! dispatches on [`RestrictionType`] to interpret the raw [`ColumnValue`] correctly.
//!
//! ## Converse operator
//!
//! [`Converse`] inverts a function `A → B` into a lookup table `B → List(A)`.  It is used
//! wherever the interpreter needs to apply a relation in reverse — for example, computing
//! the pre-image of a value under a data-source mapping.

use std::rc::Rc;

use log::trace;

use crate::interpreter::{
    ColumnValue, Consumer, Extent, FuncBinding, GetResult, Guard, Operator, Producer, Scheduler,
    Value, VarScope,
};
use crate::pretty_graph::{fmt_extent, InspectNode, VizOptions};

/// Discriminates how a [`ComputeRestriction`] should be interpreted by the caller.
///
/// The two variants correspond to different join strategies: a general predicate loop and
/// an equality hash join. The strategy determines what [`ColumnValue`] shape the operator
/// produces, and [`Restriction::get_correlations`] uses this tag to decode it correctly.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum RestrictionType {
    /// An arbitrary boolean predicate evaluated element-wise on the full cartesian product
    /// of the input extent.
    ///
    /// The operator produces `FunctionBindings { inputs: domain_elements, outputs: Bools }`,
    /// where each `bool` at position `i` indicates whether element `i` passes the predicate.
    FilteredProduct,
    /// An equality hash join kernel.
    ///
    /// The operator produces `FunctionBindings { inputs: build_elements, outputs: Functions }`,
    /// where each output function encodes the matching probe elements for the corresponding
    /// build element. See [`Restriction::get_correlations`] for the decoding logic.
    HashJoin,
}

/// Operator that computes a restriction (filter) for an extent.
///
/// Wraps any predicate [`Operator`] and tags it with a [`RestrictionType`] so that
/// [`Restriction::get_correlations`] knows how to decode the resulting [`ColumnValue`].
/// The wrapped operator is subscribed and its producer is driven directly by the
/// [`Restriction`] machinery in `types.rs`.
///
/// TODO consider whether ComputeRestriction should not actually be an operator.
#[derive(Debug)]
pub struct ComputeRestriction {
    /// The predicate operator whose output encodes the matching rows.
    predicate: Box<dyn Operator>,
    /// Placeholder extent (Base(Bool)) required by the [`Operator`] trait.
    extent: Extent,
    /// Which join strategy this restriction uses, forwarded to [`Restriction::get_correlations`].
    restriction_type: RestrictionType,
}

impl ComputeRestriction {
    /// Create a restriction that evaluates an arbitrary boolean predicate element-wise.
    ///
    /// `predicate` must produce `FunctionBindings { outputs: Bools }` when subscribed.
    pub fn new_predicate(predicate: Box<dyn Operator>) -> Self {
        let extent = Extent::Base(super::BaseType::Bool);
        Self {
            predicate,
            extent,
            restriction_type: RestrictionType::FilteredProduct,
        }
    }

    /// Create a restriction backed by a hash-join operator tree.
    ///
    /// `predicate` must produce `FunctionBindings { inputs: build_elements, outputs: Functions }`
    /// encoding the matching `(build, probe)` pairs when subscribed.
    pub fn new_join(predicate: Box<dyn Operator>) -> Self {
        // TODO fix extent
        let extent = Extent::Base(super::BaseType::Bool);
        Self {
            predicate,
            extent,
            restriction_type: RestrictionType::HashJoin,
        }
    }

    /// Return the join strategy used by this restriction.
    pub fn restriction_type(&self) -> RestrictionType {
        self.restriction_type
    }
}

impl Operator for ComputeRestriction {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    fn subscribe(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        _scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        self.predicate.subscribe(
            intent_guard,
            consumer,
            var_scope,
            // Don't forward the scheduler; we don't want to trigger notifications from
            // the branch that computes the restriction.
            &mut Scheduler::noop(),
        )
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::new("ComputeRestriction");
        if opts.show_extents {
            desc = desc.annotate(format!(": {}", fmt_extent(&self.extent)));
        }
        desc.child("predicate", self.predicate.inspect(opts))
    }
}

/// Operator that inverts a function mapping, turning `A ⇒ B` into `B ⇒ List(A)`.
///
/// Given an input operator with extent `A ⇒ B`, `Converse` produces an operator with
/// extent `{ count: B ⇒ Nat, converses: {b: B, i: Nat<(count(b))} ⇒ A}` — i.e., each output
/// value maps to the (indexed) list of input values that produced it.  This enables
/// reverse lookups such as "which source rows have this attribute value?".
///
/// We don't currently represent the above dependent type in the code, and instead just use
/// a UInt placeholder extent.
///
/// `subscribe` returns a [`ConverseProducer`] that calls [`ColumnValue::function_converse`]
/// on the raw result.  `subscribe_to_application` additionally applies the resulting
/// lookup table to a column of argument values via [`ConverseApplicationProducer`].
///
/// Note: the way ConverseProducer, ConverseApplicationProducer, and the Apply on top is
/// somewhat awkward.  We can probably clean this up significantly when we move to the new
/// op sem model.
#[derive(Debug)]
pub struct Converse {
    /// The function operator to invert.
    input: Box<dyn Operator>,
    /// The inverted extent: `codomain(input) → (UInt → domain(input))`.
    extent: Extent,
}

impl Converse {
    /// Construct a `Converse` over `input`.
    ///
    /// Panics if `input` does not have a `Function` extent.
    pub fn new(input: Box<dyn Operator>) -> Self {
        let input_extent = input.extent();
        let extent = match input_extent {
            Extent::Function { domain, codomain } => Extent::Function {
                domain: codomain.clone(),
                codomain: Box::new(Extent::Function {
                    domain: Box::new(Extent::Base(crate::interpreter::BaseType::UInt)),
                    codomain: domain.clone(),
                }),
            },
            other => panic!("Converse operator requires a function input, got extent {other:?}"),
        };
        Self { input, extent }
    }
}

/// Convert an intent guard on the converse's output extent to one suitable for its input.
///
/// Currently only universal and empty guards are supported; function/domain guards
/// are left as a TODO.
fn invert_function_intent_guard(guard: &Guard) -> Guard {
    match guard {
        g if g.is_universal() => Guard::Universal,
        g if g.is_empty() => Guard::Empty,
        // TODO implement Function and Domain guards
        _ => panic!("Converse operator requires a function intent guard, got {guard:?}"),
    }
}

impl Operator for Converse {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    fn subscribe(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        Box::new(ConverseProducer::new(self.input.subscribe(
            invert_function_intent_guard(&intent_guard),
            consumer,
            var_scope,
            scheduler,
        )))
    }

    fn subscribe_to_application(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        binding: &mut dyn Operator,
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        Box::new(ConverseApplicationProducer::new(
            Box::new(ConverseProducer::new(self.input.subscribe(
                intent_guard.clone(),
                consumer,
                var_scope.clone(),
                scheduler,
            ))),
            binding.subscribe(intent_guard, Box::new(|| {}), var_scope, scheduler),
        ))
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::new("Converse");
        if opts.show_extents {
            desc = desc.annotate(format!(": {}", fmt_extent(&self.extent)));
        }
        desc.child("input", self.input.inspect(opts))
    }
}

/// Producer that inverts the data from its input producer.
///
/// Calls [`ColumnValue::function_converse`] on the raw `FunctionBindings` result,
/// converting it into a `LookupTable` (output → list of inputs).
#[derive(Debug)]
struct ConverseProducer {
    /// The producer for the function being inverted.
    input: Box<dyn Producer>,
}

impl ConverseProducer {
    fn new(input: Box<dyn Producer>) -> Self {
        Self { input }
    }
}

impl Producer for ConverseProducer {
    fn get(&mut self) -> GetResult {
        let input_result = self.input.get();
        trace!("Converse producer got {:?}", &input_result.column_value);

        let result = GetResult {
            column_value: ColumnValue::function_converse(input_result.column_value),
            // TODO appropriately invert function guards passing through.
            yield_guard: input_result.yield_guard.to_universal_or_empty(),
        };
        trace!("Converse producer output {:?}", &result.column_value);
        result
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        // TODO impl
        obsolete_guard
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("ConverseProducer").child("input", self.input.inspect(opts))
    }
}

/// Producer that applies a `LookupTable` to a column of argument values.
///
/// Fetches the inverted function from `input` (a [`ConverseProducer`]) and the argument
/// column from `argument`, then for each argument looks up its converse (pre-image list) in
/// the table.  The result is a `FunctionBindings` pairing each argument value with its
/// converse as a `Value::Function`.
#[derive(Debug)]
struct ConverseApplicationProducer {
    /// Producer yielding the `LookupTable` (output of [`ConverseProducer`]).
    input: Box<dyn Producer>,
    /// Producer yielding the column of values to look up in the table.
    argument: Box<dyn Producer>,
}

impl ConverseApplicationProducer {
    fn new(input: Box<dyn Producer>, argument: Box<dyn Producer>) -> Self {
        Self { input, argument }
    }
}

impl Producer for ConverseApplicationProducer {
    fn get(&mut self) -> GetResult {
        let input_result = self.input.get();
        trace!(
            "ConverseApplicationProducer got input {:?}",
            &input_result.column_value
        );
        let mut argument_result = self.argument.get();
        trace!(
            "ConverseApplicationProducer got argument {:?}",
            &argument_result.column_value
        );
        let inputs = input_result.column_value.clone();
        if let ColumnValue::LookupTable(map) = input_result.column_value {
            let mut outputs = Vec::new();
            for arg_value in argument_result.column_value.drain_to_value_iter() {
                outputs.push(Value::Function(
                    map.get(&arg_value)
                        .map(move |v| {
                            v.iter()
                                .enumerate()
                                .map(move |(i, x)| FuncBinding {
                                    input: Value::UInt(i),
                                    output: x.clone(),
                                })
                                .collect()
                        })
                        .unwrap_or_else(Vec::new),
                ));
            }

            let result = GetResult {
                column_value: ColumnValue::function_bindings(
                    inputs,
                    ColumnValue::Variants(outputs),
                ),
                yield_guard: match &input_result.yield_guard {
                    Guard::Domain(g) => *g.clone(),
                    g if g.is_universal() => Guard::Universal,
                    g if g.is_empty() => Guard::Empty,
                    g => panic!("Got unexpected guard {:?}", *g),
                },
            };
            trace!(
                "ConverseApplicationProducer output {:?}",
                &result.column_value
            );
            result
        } else {
            panic!("Expected LookupTable for Converse application")
        }
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        // TODO impl
        obsolete_guard
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("ConverseApplicationProducer").child("input", self.input.inspect(opts))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::{Apply, Lambda, ListLiteral, Literal, Value, Var, VarRef};
    use bit_vec::BitVec;
    use std::cell::RefCell;
    use std::rc::Rc;
    use test_log::test;

    /// Subscribe a `ComputeRestriction` and return the `BitVec` correlation vector.
    ///
    /// Uses an all-universal intent guard and no outer var scope (the predicate lambda
    /// manages its own scope internally).
    fn eval_correlation(cr: &mut ComputeRestriction) -> BitVec {
        let notified = Rc::new(RefCell::new(false));
        let notified_clone = notified.clone();
        let consumer: Box<dyn Consumer> = Box::new(move || {
            *notified_clone.borrow_mut() = true;
        });
        let mut scheduler = Scheduler::new();
        let mut producer = cr.subscribe(Guard::universal(), consumer, None, &mut scheduler);
        // Static extents (UIntRange) notify synchronously; no external scheduler tick needed.
        assert!(
            *notified.borrow(),
            "Expected synchronous notification from static extent"
        );
        let result = producer.get();
        match result.column_value {
            ColumnValue::FunctionBindings { outputs, .. } => match *outputs {
                ColumnValue::Bools(bools) => bools,
                other => panic!("Expected Bools in ComputeRestriction outputs, got {other:?}"),
            },
            other => panic!("Expected FunctionBindings from ComputeRestriction, got {other:?}"),
        }
    }

    #[test]
    fn test_compute_restriction_all_true() {
        // Lambda(x ∈ UIntRange{0,3}, true) → all three entries pass.
        let var = Var::new("x", Extent::UIntRange { start: 0, end: 3 });
        let lambda = Lambda::new(var, Box::new(Literal::new(Value::Bool(true))));
        let mut cr = ComputeRestriction::new_predicate(Box::new(lambda));
        assert_eq!(eval_correlation(&mut cr), BitVec::from_elem(3, true));
    }

    #[test]
    fn test_compute_restriction_all_false() {
        // Lambda(x ∈ UIntRange{0,3}, false) → no entries pass.
        let var = Var::new("x", Extent::UIntRange { start: 0, end: 3 });
        let lambda = Lambda::new(var, Box::new(Literal::new(Value::Bool(false))));
        let mut cr = ComputeRestriction::new_predicate(Box::new(lambda));
        assert_eq!(eval_correlation(&mut cr), BitVec::from_elem(3, false));
    }

    #[test]
    fn test_compute_restriction_mixed_predicate() {
        // Source list [true, true, false, false] applied to the outer index.
        // Lambda(outer ∈ UIntRange{0,4}, Apply(source, VarRef(outer)))
        // → correlation vector [true, true, false, false].
        let source = ListLiteral::new(vec![
            Value::Bool(true),
            Value::Bool(true),
            Value::Bool(false),
            Value::Bool(false),
        ]);
        let outer = Var::new("outer", Extent::UIntRange { start: 0, end: 4 });
        let outer_ref = VarRef::new("outer", Extent::UIntRange { start: 0, end: 4 });
        let apply = Apply::new(Box::new(source), Box::new(outer_ref));
        let lambda = Lambda::new(outer, Box::new(apply));
        let mut cr = ComputeRestriction::new_predicate(Box::new(lambda));
        let mut expected = BitVec::from_elem(4, false);
        expected.set(0, true);
        expected.set(1, true);
        assert_eq!(eval_correlation(&mut cr), expected);
    }
}
