use crate::interpreter::{
    Consumer, Extent, GetResult, Guard, Operator, Producer, Scheduler, VarScope,
};
use crate::pretty_graph::{fmt_extent, InspectNode, VizOptions};

/// Operator that computes a restriction for an extent.
/// Currently, this is implemented as a loop join, so it iterates over
/// the entire extent and evaulates the predicate for each values.
#[derive(Debug)]
pub struct ComputeRestriction {
    predicate: Box<dyn Operator>,
    extent: Extent,
}

impl ComputeRestriction {
    pub fn new(predicate: Box<dyn Operator>) -> Self {
        let extent = Extent::Base(super::BaseType::Bool);
        Self { predicate, extent }
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
        var_scope: Option<std::rc::Rc<VarScope>>,
        _scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        Box::new(ComputeRestrictionProducer::new(self.predicate.subscribe(
            intent_guard,
            consumer,
            var_scope,
            // Don't forward the scheduler; we don't want to trigger notifications from
            // the branch that computes the restriction.
            &mut Scheduler::noop(),
        )))
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::new("ComputeRestriction");
        if opts.show_extents {
            desc = desc.annotate(format!(": {}", fmt_extent(&self.extent)));
        }
        desc.child("predicate", self.predicate.inspect(opts))
    }
}

#[derive(Debug)]
struct ComputeRestrictionProducer {
    input: Box<dyn Producer>,
}

impl ComputeRestrictionProducer {
    fn new(input: Box<dyn Producer>) -> Self {
        Self { input }
    }
}

impl Producer for ComputeRestrictionProducer {
    fn get(&mut self) -> GetResult {
        self.input.get()
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        obsolete_guard
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("ComputeRestrictionProducer").child("input", self.input.inspect(opts))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpreter::{
        Apply, ColumnValue, Lambda, ListLiteral, Literal, Notification, Value, Var, VarRef,
    };
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
        let consumer: Box<dyn Consumer> = Box::new(move |n: Notification| {
            if matches!(n, Notification::NewData) {
                *notified_clone.borrow_mut() = true;
            }
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
        let mut cr = ComputeRestriction::new(Box::new(lambda));
        assert_eq!(eval_correlation(&mut cr), BitVec::from_elem(3, true));
    }

    #[test]
    fn test_compute_restriction_all_false() {
        // Lambda(x ∈ UIntRange{0,3}, false) → no entries pass.
        let var = Var::new("x", Extent::UIntRange { start: 0, end: 3 });
        let lambda = Lambda::new(var, Box::new(Literal::new(Value::Bool(false))));
        let mut cr = ComputeRestriction::new(Box::new(lambda));
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
        let mut cr = ComputeRestriction::new(Box::new(lambda));
        let mut expected = BitVec::from_elem(4, false);
        expected.set(0, true);
        expected.set(1, true);
        assert_eq!(eval_correlation(&mut cr), expected);
    }
}
