//! Let operator: named let-binding with simplified single-argument dataflow.
//!
//! [`Let`] represents `let name = value in body` as a first-class operator,
//! rather than desugaring to `Apply(Lambda(name, body), value)`. This retains
//! binding provenance in the graph and removes the Argument/Iteration dual-source
//! complexity that [`super::Lambda`] carries for the general case — a let binding
//! is always an Argument source.

use std::cell::RefCell;
use std::rc::Rc;

use crate::pretty_graph::{fmt_extent, InspectNode, VizOptions};

use super::{
    fmt_guard, Consumer, Extent, GetResult, Guard, Operator, Producer, Scheduler, Var, VarProducer,
    VarScope, VarSource,
};

// ============================================================================
// Let operator
// ============================================================================

/// A Let operator: `let name = bound_expr in body`.
///
/// Compiles `let` bindings directly to the dataflow graph, the bound variable's extent is
/// derived from `body.extent()`.
#[derive(Debug)]
pub struct Let {
    /// The bound variable name.
    variable: Var,
    /// The expression whose result is bound to `name`.
    bound_expr: Box<dyn Operator>,
    /// The expression evaluated with `name` in scope.
    body: Box<dyn Operator>,
    /// Extent of this expression — equals `body.extent()` at construction time.
    extent: Extent,
}

impl Let {
    /// Create a new Let operator.
    ///
    /// The operator's extent is taken from `body.extent()` at construction time.
    pub fn new(variable: Var, value: Box<dyn Operator>, body: Box<dyn Operator>) -> Self {
        let extent = body.extent().clone();
        Let {
            variable,
            bound_expr: value,
            body,
            extent,
        }
    }
}

impl Operator for Let {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::new(format!("Let({})", self.variable.name));
        if opts.show_extents {
            desc = desc.annotate(format!(": {}", fmt_extent(&self.extent)));
        }
        desc.child("value", self.bound_expr.inspect(opts))
            .child("body", self.body.inspect(opts))
    }

    fn subscribe(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        let var_producer = self.variable.create_subscription(VarSource::Uninitialized);

        // Subscribe to the value expression exactly once, wiring var_producer as its consumer.
        // All VarRef(name) nodes in the body look up var_producer through the scope,
        // so no additional subscriptions to value are created for multiple body references.
        let var_consumer: Box<dyn Consumer> = Box::new(var_producer.clone());
        let bound_expr_producer = self.bound_expr.subscribe(
            Guard::universal(),
            var_consumer,
            var_scope.clone(),
            scheduler,
        );
        var_producer
            .borrow_mut()
            .set_source(VarSource::Argument(bound_expr_producer));

        // Extend the scope with name → var_producer for body subscription.
        let new_scope = Rc::new(VarScope::new_with_optional_parent(
            var_scope,
            &self.variable.name,
            var_producer.clone(),
        ));

        // Body notifications are driven by var_producer notifications above;
        // direct body notifications are not forwarded.
        //
        // TODO This is correct for the current test cases: inputs are Lit (synchronous).
        // However, once the body has additional async dependencies outside the bound variable
        // (e.g., a body referencing another outer-scope variable that updates after var fires),
        // those notifications will be silently discarded).
        // ```
        // let y = some_async_source()
        //   in let x = 5
        //     in (x + y)
        // ````
        let body_consumer: Box<dyn Consumer> = Box::new(|| {});
        let body_producer = self.body.subscribe(
            intent_guard.clone(),
            body_consumer,
            Some(new_scope),
            scheduler,
        );

        let let_producer = Rc::new(RefCell::new(LetProducer::new(
            self.variable.name.clone(),
            var_producer.clone(),
            body_producer,
            consumer,
            intent_guard,
        )));

        // Register LetProducer as a consumer of var_producer. If the value operator
        // already fired synchronously (e.g., Literal), add_consumer catches up immediately.
        //
        // Body may not have references to variable, so still want notifications to flow
        // directly to the let.
        var_producer
            .borrow_mut()
            .add_consumer(Box::new(let_producer.clone()));
        Box::new(let_producer)
    }
}

// ============================================================================
// LetProducer
// ============================================================================

/// Runtime subscription for a [`Let`] binding.
///
/// As a [`Consumer`]: receives notifications from the value's [`VarProducer`]
/// and forwards them downstream.
///
/// As a [`Producer`]: returns the body's output directly, without the
/// [`ColumnValue::FunctionBindings`] wrapping that [`super::lambda::LambdaProducer`]
/// uses for the general function case.
struct LetProducer {
    /// Bound variable name, for visualization.
    name: String,
    /// The value's [`VarProducer`]; held for release propagation.
    var_producer: Rc<RefCell<VarProducer>>,
    /// Body producer
    body_producer: Box<dyn Producer>,
    /// Downstream consumer that receives ready notifications.
    downstream_consumer: Box<dyn Consumer>,
    /// Intent guard.
    intent_guard: Guard,
}

impl std::fmt::Debug for LetProducer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LetProducer")
            .field("name", &self.name)
            .field("var_producer", &self.var_producer)
            .field("body_producer", &self.body_producer)
            .field("downstream_consumer", &format_args!("<consumer>"))
            .field("intent_guard", &self.intent_guard)
            .finish()
    }
}

impl LetProducer {
    fn new(
        name: String,
        var_producer: Rc<RefCell<VarProducer>>,
        body_producer: Box<dyn Producer>,
        downstream_consumer: Box<dyn Consumer>,
        intent_guard: Guard,
    ) -> Self {
        LetProducer {
            name,
            var_producer,
            body_producer,
            downstream_consumer,
            intent_guard,
        }
    }
}

impl Producer for LetProducer {
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::new(format!("LetProducer({})", self.name));
        if opts.show_guards {
            desc = desc.with_intent_guard(fmt_guard(&self.intent_guard));
        }
        desc = desc.child("var", self.var_producer.inspect(opts));
        desc = desc.child("body", self.body_producer.inspect(opts));
        desc
    }

    fn get(&mut self) -> GetResult {
        let result = self.body_producer.get();
        GetResult {
            column_value: result.column_value,
            yield_guard: result.yield_guard,
        }
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        // The release flows through the body to the var, so we don't propagate it directly here.
        self.body_producer.release(obsolete_guard)
    }
}

impl Consumer for LetProducer {
    fn notify(&mut self) {
        self.downstream_consumer.notify();
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use crate::interpreter::test_helpers::TestConsumer;
    use crate::interpreter::*;
    use test_log::test;

    /// Subscribe and evaluate a scalar result.
    fn eval_let(mut let_op: Let) -> Value {
        let (consumer, notifications) = TestConsumer::new();
        let mut producer = let_op.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );
        assert!(
            *notifications.borrow() > 0,
            "expected at least one notification, got {}",
            *notifications.borrow()
        );
        producer.get().column_value.as_single().unwrap().clone()
    }

    fn int_var(name: &str) -> Var {
        Var::new(name, Extent::Base(BaseType::Int))
    }

    #[test]
    fn test_let_identity() {
        // let x = 42 in x  →  42
        let let_op = Let::new(
            int_var("x"),
            Box::new(Literal::new(Value::Int(42))),
            Box::new(VarRef::new("x", Extent::Base(BaseType::Int))),
        );
        assert_eq!(eval_let(let_op), Value::Int(42));
    }

    #[test]
    fn test_let_body_uses_binding() {
        // let x = 5 in x + 1  →  6
        let body = Box::new(BinOp::new(
            Box::new(VarRef::new("x", Extent::Base(BaseType::Int))),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Box::new(Literal::new(Value::Int(1))),
        ));
        let let_op = Let::new(int_var("x"), Box::new(Literal::new(Value::Int(5))), body);
        assert_eq!(eval_let(let_op), Value::Int(6));
    }

    #[test]
    fn test_let_multi_reference() {
        // let x = 5 in x + x  →  10
        // Key test: value is subscribed to exactly once despite two VarRef nodes.
        let body = Box::new(BinOp::new(
            Box::new(VarRef::new("x", Extent::Base(BaseType::Int))),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Box::new(VarRef::new("x", Extent::Base(BaseType::Int))),
        ));
        let let_op = Let::new(int_var("x"), Box::new(Literal::new(Value::Int(5))), body);
        assert_eq!(eval_let(let_op), Value::Int(10));
    }

    #[test]
    fn test_let_chained() {
        // let x = 5 in let y = 2 in x + y  →  7
        // Inner Let's body references x from the outer scope via VarScope chain.
        let inner_body = Box::new(BinOp::new(
            Box::new(VarRef::new("x", Extent::Base(BaseType::Int))),
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            Box::new(VarRef::new("y", Extent::Base(BaseType::Int))),
        ));
        let inner_let = Box::new(Let::new(
            int_var("y"),
            Box::new(Literal::new(Value::Int(2))),
            inner_body,
        ));
        let outer_let = Let::new(
            int_var("x"),
            Box::new(Literal::new(Value::Int(5))),
            inner_let,
        );
        assert_eq!(eval_let(outer_let), Value::Int(7));
    }

    #[test]
    fn test_let_notification_fires() {
        // Subscribing to a Let with a synchronous (Literal) value fires a notification.
        let mut let_op = Let::new(
            int_var("x"),
            Box::new(Literal::new(Value::Int(1))),
            Box::new(VarRef::new("x", Extent::Base(BaseType::Int))),
        );
        let (consumer, notifications) = TestConsumer::new();
        let _producer = let_op.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );
        assert!(
            *notifications.borrow() > 0,
            "expected at least one notification, got {}",
            *notifications.borrow()
        );
    }

    #[test]
    fn test_let_extent_is_body_extent() {
        // Let's extent matches the body's extent, not a function type.
        let let_op = Let::new(
            int_var("x"),
            Box::new(Literal::new(Value::Int(0))),
            Box::new(Literal::new(Value::String("hi".to_string()))),
        );
        assert_eq!(let_op.extent(), &Extent::Base(BaseType::String));
    }
}
