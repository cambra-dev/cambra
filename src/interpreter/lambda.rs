//! Lambda operator: lambda expressions with variable binding and scope management.

use std::cell::RefCell;
use std::rc::Rc;

use crate::{
    interpreter::NotifyOrSubscribeResult,
    pretty_graph::{fmt_extent, InspectNode, VizOptions},
};
use log::{debug, trace};

use super::{
    fmt_guard, ColumnValue, Consumer, Extent, GetResult, Guard, Notification, Operator, Producer,
    Scheduler, Var, VarProducer, VarScope, VarSource,
};

/// A Lambda operator represents a lambda expression.
/// It has a variable and a body, and manages the variable scope.
#[derive(Debug)]
pub struct Lambda {
    variable: Var,
    body: Box<dyn Operator>,
    extent: Extent,
}

/// Runtime subscription for a [`Lambda`]: sits at an intermediate node in the dataflow graph,
/// implementing both sides of the protocol.
///
/// As a [`Consumer`]: receives notifications from the variable (domain) subscription and
/// forwards them downstream, wrapping yield guards in `Guard::Domain`. Body (codomain)
/// notifications are handled by the companion [`LambdaBodyConsumer`].
///
/// As a [`Producer`]: provides function bindings via `get()` and handles `release()`.
struct LambdaProducer {
    /// The variable name (for visualization)
    var_name: String,
    /// Reference to the variable subscription (for domain values)
    variable_subscription: Rc<RefCell<VarProducer>>,
    /// The body producer (for codomain values). Set after body subscription.
    body_producer: Option<Box<dyn Producer>>,
    /// The downstream consumer that will receive notifications
    downstream_consumer: Box<dyn Consumer>,
    /// Yield guard from the variable (domain)
    variable_yield_guard: Guard,
    /// Yield guard from the body (codomain)
    body_yield_guard: Guard,
    /// The intent guard for this lambda subscription
    intent_guard: Guard,
}

impl std::fmt::Debug for LambdaProducer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LambdaProducer")
            .field("var_name", &self.var_name)
            .field("variable_subscription", &self.variable_subscription)
            .field("body_producer", &self.body_producer)
            .field("downstream_consumer", &format_args!("<consumer>"))
            .field("variable_yield_guard", &self.variable_yield_guard)
            .field("body_yield_guard", &self.body_yield_guard)
            .field("intent_guard", &self.intent_guard)
            .finish()
    }
}

impl LambdaProducer {
    /// Create a new LambdaProducer. The body_producer should be set via set_body_producer().
    fn new(
        var_name: String,
        variable_subscription: Rc<RefCell<VarProducer>>,
        downstream_consumer: Box<dyn Consumer>,
        intent_guard: Guard,
    ) -> Self {
        LambdaProducer {
            var_name,
            variable_subscription,
            body_producer: None,
            downstream_consumer,
            variable_yield_guard: Guard::Empty,
            body_yield_guard: Guard::Empty,
            intent_guard,
        }
    }

    /// Set the body producer after creation.
    fn set_body_producer(&mut self, producer: Box<dyn Producer>) {
        self.body_producer = Some(producer);
    }
}

impl Producer for LambdaProducer {
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::new(format!("LambdaProducer({})", self.var_name));
        if opts.show_guards {
            desc = desc.with_intent_guard(fmt_guard(&self.intent_guard));
        }
        // Inspect variable subscription (borrows VarProducer then drops before body)
        let var_desc = self.variable_subscription.inspect(opts);
        desc = desc.child("var", var_desc);
        // Inspect body producer
        match &self.body_producer {
            Some(p) => desc = desc.child("body", p.inspect(opts)),
            None => desc = desc.child("body", InspectNode::leaf("<not subscribed>")),
        }
        desc
    }

    /// Get the function bindings by combining domain values from the variable
    /// and codomain values from the body.
    fn get(&mut self) -> GetResult {
        // Get domain values from variable
        let domain_result = self.variable_subscription.borrow_mut().get();

        // Get codomain values from body (columnar)
        let codomain_result = self
            .body_producer
            .as_mut()
            .expect("body_producer should be set before get()")
            .get();

        self.variable_yield_guard = domain_result.yield_guard.clone();
        self.body_yield_guard = codomain_result.yield_guard.clone();
        let domain_column = domain_result.column_value;
        let codomain_column = codomain_result.column_value;
        let codomain_is_scalar = codomain_column.is_scalar();

        // If the body of a lambda is a scalar (single-element), expand it out to one copy per element in the domain.
        let codomain_data = if codomain_is_scalar {
            codomain_column.repeat(domain_column.len())
        } else {
            assert_eq!(
                domain_column.len(),
                codomain_column.len(),
                "Domain and codomain columns have different lengths"
            );
            codomain_column
        };

        GetResult {
            column_value: ColumnValue::function_bindings(domain_column, codomain_data),
            yield_guard: Guard::Domain(Box::new(domain_result.yield_guard))
                .intersect(self.intent_guard.clone()),
        }
    }

    /// Release interest in a region by splitting the obsolete guard and
    /// releasing both the variable and body.
    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        if let Guard::Domain(domain_obsolete_guard) = &obsolete_guard {
            self.variable_subscription
                .borrow_mut()
                .release(*domain_obsolete_guard.clone());
            obsolete_guard
        } else {
            debug!("Lambda::release with {obsolete_guard:?}");
            // Split obsolete guard into domain and codomain
            let (domain_obsolete, codomain_obsolete) = obsolete_guard
                .split_function()
                .unwrap_or((Guard::Empty, Guard::Empty));

            // Release the variable (domain)
            let expanded_domain_obsolete = self
                .variable_subscription
                .borrow_mut()
                .release(domain_obsolete);

            // Release the body (codomain)
            let expanded_codomain_obsolete = self
                .body_producer
                .as_mut()
                .expect("body_producer should be set before release()")
                .release(codomain_obsolete);

            // Combine the expanded guards back into a function guard
            Guard::from_independent_function_parts(
                expanded_domain_obsolete,
                expanded_codomain_obsolete,
            )
        }
    }
}

impl Consumer for LambdaProducer {
    /// Receives notifications from the variable (domain) subscription and forwards
    /// them downstream, wrapping yield guards in `Guard::Domain`.
    fn notify(&mut self, notification: Notification) {
        match notification {
            Notification::Yield(guard) => {
                self.variable_yield_guard = guard.clone();
                let new_guard = Guard::Domain(Box::new(guard));
                self.downstream_consumer
                    .notify(Notification::Yield(new_guard));
            }
            Notification::NewData => self.downstream_consumer.notify(Notification::NewData),
        }
    }
}

/// Receives notifications from the body (codomain) subscription and forwards them
/// to the LambdaProducer, combining the current variable yield guard with the
/// body yield guard.
struct LambdaBodyConsumer(Rc<RefCell<LambdaProducer>>);

impl Consumer for LambdaBodyConsumer {
    fn notify(&mut self, notification: Notification) {
        debug!("Lambda body_consumer notified with {notification:?}");
        let mut producer = self.0.borrow_mut();
        match notification {
            Notification::Yield(guard) => {
                producer.body_yield_guard = guard.clone();
                let new_guard = Guard::from_independent_function_parts(
                    producer.variable_yield_guard.clone(),
                    guard,
                );
                producer
                    .downstream_consumer
                    .notify(Notification::Yield(new_guard));
            }
            // Lambda ignores NewData on the body side; action is taken on variable notification.
            Notification::NewData => {}
        }
    }
}

impl Lambda {
    pub fn new(variable: Var, body: Box<dyn Operator>) -> Self {
        // Compute the extent: function type from domain (variable) to codomain (body)
        let domain = variable.extent().clone();
        let codomain = body.extent().clone();
        let extent = Extent::function(domain, codomain);
        Lambda {
            variable,
            body,
            extent,
        }
    }

    /// Internal subscribe implementation that handles both argument and iteration sources.
    fn subscribe_internal(
        &mut self,
        intent_guard: Guard,
        mut consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        binding: Option<&mut dyn Operator>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        // Split intent guard into domain and codomain
        let (domain_guard, codomain_guard) = intent_guard
            .split_function()
            .unwrap_or((Guard::universal(), Guard::universal()));

        // For argument source: subscribe to the binding operator with VarProducer as consumer
        // This ensures VarProducer receives notifications and can forward to its consumers
        let variable_subscription = if let Some(binding_op) = binding {
            let subscription = self.variable.create_subscription(VarSource::Uninitialized);

            // Subscribe to binding with VarProducer as the consumer
            // VarProducer implements Consumer, so it will receive notifications
            let var_sub_consumer: Box<dyn Consumer> = Box::new(subscription.clone());
            let binding_producer = binding_op.subscribe(
                domain_guard.clone(),
                var_sub_consumer,
                var_scope.clone(),
                scheduler,
            );

            // Now set the source to `Argument` with the actual producer
            subscription
                .borrow_mut()
                .set_source(VarSource::Argument(binding_producer));
            subscription
        } else {
            // Iteration source
            self.variable.create_subscription(VarSource::Iteration {
                extent: self.variable.extent().clone(),
            })
        };

        // Set up notifications based on the variable's source and extent.
        // For Argument sources, the binding producer notifies VarProducer directly via the
        // Consumer impl, which then propagates to LambdaProducer via add_consumer — no
        // scheduler registration or direct consumer notification needed here.
        // For Iteration sources, we either register with the scheduler (for data sources that
        // need polling) or notify the consumer immediately (for literal ranges).
        if variable_subscription.borrow().is_iteration() {
            // Register the outer variable with the scheduler first so it gets polled before any
            // restriction producer.  If the outer source is a data source, this ensures the
            // outer VarProducer consumes the `check_for_new_data` flag before the restriction's
            // inner variable does (the restriction's data is fetched on-demand, not via the flag).
            let NotifyOrSubscribeResult { notify, subscribe } =
                self.variable.extent().subscribe_to_iteration_action();
            if notify {
                consumer.notify(Notification::NewData);
            }
            if subscribe {
                scheduler.add_source(variable_subscription.clone());
            }
        }

        let name = self.variable.name.clone();
        if self.variable.owns_restriction() {
            if let Extent::Restricted { restriction, .. } = self.variable.extent_mut() {
                debug!("Setting up producer for restriction of variable {name} in lambda with scope {var_scope:?}");
                restriction.borrow_mut().set_up_producer(
                    intent_guard.clone(),
                    var_scope.clone(),
                    scheduler,
                );
            }
        }

        // Create LambdaProducer with the variable subscription (body_producer set later)
        let lambda_producer = Rc::new(RefCell::new(LambdaProducer::new(
            self.variable.name.clone(),
            variable_subscription.clone(),
            consumer,
            intent_guard.clone(),
        )));

        // Rc<RefCell<LambdaProducer>> implements Consumer via the blanket impl.
        // For Bound mode: VarProducer may have already been notified by the binding, and add_consumer
        // will immediately notify this consumer if yield_guard is non-empty.
        variable_subscription
            .borrow_mut()
            .add_consumer(Box::new(lambda_producer.clone()));

        // Create a new VarScope with this variable
        let new_scope = if let Some(parent) = var_scope {
            VarScope::child(parent, &self.variable.name, variable_subscription)
        } else {
            VarScope::new(&self.variable.name, variable_subscription)
        };

        let body_consumer: Box<dyn Consumer> =
            Box::new(LambdaBodyConsumer(lambda_producer.clone()));

        let body_producer = self.body.subscribe(
            codomain_guard,
            body_consumer,
            Some(Rc::new(new_scope)),
            scheduler,
        );

        // Set the body producer
        lambda_producer
            .borrow_mut()
            .set_body_producer(body_producer);

        // Return the LambdaProducer as a Producer
        Box::new(lambda_producer)
    }
}

impl Operator for Lambda {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut var_desc = InspectNode::new(format!("Var({})", self.variable.name));
        if opts.show_extents {
            var_desc = var_desc.annotate(format!(": {}", fmt_extent(self.variable.extent())));
        }
        if self.variable.owns_restriction() {
            if let Extent::Restricted { restriction, .. } = self.variable.extent() {
                var_desc = var_desc.child("restriction", restriction.borrow().inspect(opts));
            }
        }
        let body_desc = self.body.inspect(opts);
        let mut desc = InspectNode::new(format!("Lambda({})", self.variable.name));
        if opts.show_extents {
            desc = desc.annotate(format!(": {}", fmt_extent(&self.extent)));
        }
        desc.child("var", var_desc).child("body", body_desc)
    }

    // Subscribe to the lambda with iteration source, producing (input, output) pairs for every
    // input value in the input's Extent
    fn subscribe(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        // When subscribe is called without a binding, the variable has iteration source.
        // This happens when the lambda is consumed directly (e.g., by aggregation or output).
        self.subscribe_internal(intent_guard, consumer, var_scope, None, scheduler)
    }

    // Subscribe to the lambda bound to the given input. Produces (input, output) pairs
    // corresponding to the inputs produced by the Producer created by `binding`.
    fn subscribe_to_application(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        binding: &mut dyn Operator,
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        self.subscribe_internal(intent_guard, consumer, var_scope, Some(binding), scheduler)
    }
}

#[derive(Debug)]
pub struct Apply {
    lambda: Box<dyn Operator>,
    argument: Box<dyn Operator>,
}

impl Apply {
    pub fn new(lambda: Box<dyn Operator>, argument: Box<dyn Operator>) -> Self {
        Apply { lambda, argument }
    }
}

impl Operator for Apply {
    fn extent(&self) -> &Extent {
        // The extent of applying a lambda is the codomain of the lambda
        match self.lambda.extent() {
            Extent::Function { codomain, .. } => codomain.as_ref(),
            _ => panic!("Expected function extent for lambda"),
        }
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::new("Apply");
        if opts.show_extents {
            desc = desc.annotate(format!(": {}", fmt_extent(self.extent())));
        }
        desc.child("lambda", self.lambda.inspect(opts))
            .child("argument", self.argument.inspect(opts))
    }

    fn subscribe(
        &mut self,
        intent_guard: Guard,
        mut consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        // Subscribe to the lambda applied to the argument.
        // Note: this should ideally transform the output yield guard according to the body
        // of the lambda. For now, we treat the body as a black box and just forward Universal
        // or Empty.
        let apply_consumer = move |notification: Notification| {
            let downstream_notification = match &notification {
                Notification::NewData => Notification::NewData,
                Notification::Yield(g) => Notification::Yield(g.to_universal_or_empty()),
            };
            debug!("Apply notified with {notification:?}, forwarding {downstream_notification:?}");
            consumer.notify(downstream_notification);
        };
        Box::new(ApplyProducer::new(self.lambda.subscribe_to_application(
            intent_guard,
            Box::new(apply_consumer),
            var_scope,
            &mut *self.argument,
            scheduler,
        )))
    }
}

#[derive(Debug)]
struct ApplyProducer {
    lambda_producer: Box<dyn Producer>,
}

impl ApplyProducer {
    fn new(lambda_producer: Box<dyn Producer>) -> Self {
        ApplyProducer { lambda_producer }
    }
}

impl Producer for ApplyProducer {
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new("ApplyProducer").child("lambda", self.lambda_producer.inspect(opts))
    }

    fn get(&mut self) -> GetResult {
        // Get the function bindings from the lambda producer
        let GetResult {
            yield_guard,
            column_value: lambda_column,
        } = self.lambda_producer.get();
        match lambda_column {
            ColumnValue::FunctionBindings { outputs, .. } => {
                trace!("ApplyProducer producing {:?}", *outputs);
                GetResult {
                    column_value: *outputs,
                    yield_guard: yield_guard.to_universal_or_empty(),
                }
            }
            other => panic!("Expected FunctionBindings from lambda producer, got {other:?}"),
        }
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        // For simplicity, we just pass through the release to the lambda producer
        self.lambda_producer.release(obsolete_guard)
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter::test_helpers::TestConsumer;
    use crate::interpreter::*;
    use std::rc::Rc;
    use test_log::test;

    #[test]
    fn test_lambda_extent() {
        // Create a lambda: λ x . x (identity function)
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let lambda = Lambda::new(variable, body);

        // Check that extent is a function from Int to Int
        let extent = lambda.extent();
        match extent {
            Extent::Function { domain, codomain } => {
                assert_eq!(domain.as_ref(), &Extent::Base(BaseType::Int));
                assert_eq!(codomain.as_ref(), &Extent::Base(BaseType::Int));
            }
            _ => panic!("Expected function extent, got {extent:?}"),
        }
    }

    #[test]
    fn test_lambda_simple_identity() {
        // Create a lambda: λ x . x (identity function)
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        // Body just returns the variable
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let mut lambda = Lambda::new(variable, body);

        let mut binding_literal = Literal::new(Value::Int(42));

        let (consumer, notifications) = TestConsumer::new();
        let mut producer = lambda.subscribe_to_application(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut binding_literal,
            &mut Scheduler::new(),
        );

        // Check notifications - we should get one when both are ready
        let notifications_borrowed = notifications.borrow();
        assert!(
            !notifications_borrowed.is_empty(),
            "Expected at least 1 notification, got {}",
            notifications_borrowed.len()
        );

        // Get the function bindings
        let result = producer.get();
        assert_eq!(
            result.column_value,
            ColumnValue::function_bindings(
                ColumnValue::Ints(vec![42]),
                ColumnValue::Ints(vec![42])
            ),
        );
    }

    #[test]
    fn test_lambda_with_literal_body() {
        // Create a lambda: λ x . 10 (constant function)
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(Literal::new(Value::Int(10)));
        let mut lambda = Lambda::new(variable, body);

        let mut binding_literal = Literal::new(Value::Int(0));

        // Subscribe to the lambda with the binding operator
        let (consumer, notifications) = TestConsumer::new();
        let mut producer = lambda.subscribe_to_application(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut binding_literal,
            &mut Scheduler::new(),
        );

        // Both variable and body should notify
        let notifications_borrowed = notifications.borrow();
        assert!(
            !notifications_borrowed.is_empty(),
            "Expected at least 1 notification, got {}",
            notifications_borrowed.len()
        );

        // Get the function bindings
        let result = producer.get();
        assert_eq!(
            result.column_value,
            ColumnValue::function_bindings(ColumnValue::Ints(vec![0]), ColumnValue::Ints(vec![10]))
        );
    }

    #[test]
    fn test_lambda_release() {
        // Create a lambda: λ x . x
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let mut lambda = Lambda::new(variable, body);

        let mut binding_literal = Literal::new(Value::Int(42));

        // Subscribe to the lambda with the binding operator
        let (consumer, _) = TestConsumer::new();
        let mut producer = lambda.subscribe_to_application(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut binding_literal,
            &mut Scheduler::new(),
        );

        // Call get to ensure everything is set up
        let _value = producer.get();

        // Release with a function guard
        let release_guard = Guard::from_function_parts(Guard::universal(), Guard::universal());
        let released = producer.release(release_guard);

        // The released guard should be a function guard (possibly expanded)
        // We just verify it's not empty
        assert!(!released.is_empty());
    }

    #[test]
    fn test_lambda_with_function_guard() {
        // Create a lambda: λ x . x
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let mut lambda = Lambda::new(variable, body);

        let mut binding_literal = Literal::new(Value::Int(42));

        // Subscribe with a function guard
        let domain_guard = Guard::Equality {
            variable: "x".to_string(),
            value: Value::Int(42),
        };
        let codomain_guard = Guard::universal();
        let intent_guard = Guard::from_function_parts(domain_guard, codomain_guard);

        let (consumer, notifications) = TestConsumer::new();
        let mut producer = lambda.subscribe_to_application(
            intent_guard,
            Box::new(consumer),
            None,
            &mut binding_literal,
            &mut Scheduler::new(),
        );

        // Should receive notification
        let notifications_borrowed = notifications.borrow();
        assert!(
            !notifications_borrowed.is_empty(),
            "Expected at least 1 notification"
        );

        // Get should work
        let result = producer.get();
        match &result.column_value {
            ColumnValue::FunctionBindings { inputs, .. } => {
                assert!(!inputs.is_empty());
            }
            other => panic!("Expected FunctionBindings, got {other:?}"),
        }
    }

    #[test]
    fn test_lambda_nested_scope() {
        // Test that lambda creates a new scope for its variable
        // Create: λ x . x where x is defined in the lambda
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let mut lambda = Lambda::new(variable, body);

        // Create a parent scope with a different variable "x" receiving argument 200
        let parent_variable = Var::new("x", Extent::Base(BaseType::Int));
        // Create parent subscription and wire up binding properly
        let parent_subscription = parent_variable.create_subscription(VarSource::Uninitialized);
        let mut parent_literal = Literal::new(Value::Int(200));
        let parent_sub_consumer: Box<dyn Consumer> = Box::new(parent_subscription.clone());
        let parent_binding = parent_literal.subscribe(
            Guard::universal(),
            parent_sub_consumer,
            None,
            &mut Scheduler::new(),
        );
        parent_subscription
            .borrow_mut()
            .set_source(VarSource::Argument(parent_binding));
        let parent_scope = VarScope::new("x", parent_subscription);

        let mut binding_literal = Literal::new(Value::Int(100));

        // Subscribe to lambda with parent scope and binding operator
        // The lambda should create its own scope, so the body should reference
        // the lambda's variable (100), not the parent's (200)
        let (consumer, _) = TestConsumer::new();
        let mut producer = lambda.subscribe_to_application(
            Guard::universal(),
            Box::new(consumer),
            Some(Rc::new(parent_scope)),
            &mut binding_literal,
            &mut Scheduler::new(),
        );

        // Get the value - should use lambda's variable (100), not parent's (200)
        let result = producer.get();
        assert_eq!(
            result.column_value,
            ColumnValue::function_bindings(
                ColumnValue::Ints(vec![100]),
                ColumnValue::Ints(vec![100])
            )
        );
    }

    #[test]
    fn test_lambda_notifications_from_both_sources() {
        // Test that notifications work correctly when both variable and body notify
        // Create a lambda where both variable binding and body are literals (they notify immediately)
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(Literal::new(Value::Int(2)));
        let mut lambda = Lambda::new(variable, body);

        let mut binding_literal = Literal::new(Value::Int(1));

        let (consumer, notifications) = TestConsumer::new();
        let _producer = lambda.subscribe_to_application(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut binding_literal,
            &mut Scheduler::new(),
        );

        // Both variable binding and body should notify, and LambdaProducer should
        // notify downstream when both are ready
        let notifications_borrowed = notifications.borrow();
        // We should get at least one notification when both guards are ready
        assert!(
            !notifications_borrowed.is_empty(),
            "Expected notification when both variable and body are ready, got {}",
            notifications_borrowed.len()
        );

        // The notification should be NewData
        let last_notification = notifications_borrowed.last().unwrap();
        assert!(matches!(last_notification, Notification::NewData));
    }

    #[test]
    fn test_binding_notifications_flow_through_varproducer() {
        // This test verifies that binding notifications flow through VarProducer to VarRefProducer.
        // Previously, we had a bug where the binding's consumer was a TestConsumer,
        // so notifications never reached VarProducer. VarProducer's yield_guard was set manually,
        // which made add_consumer() notify immediately, masking the issue.
        //
        // This test catches the bug by:
        // 1. Creating a lambda with a VarRef body (so VarRefProducer is in the consumers list)
        // 2. Verifying a notification is received by the lambda's consumer.

        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let mut lambda = Lambda::new(variable, body);

        let mut binding_literal = Literal::new(Value::Int(42));

        let (consumer, notifications) = TestConsumer::new();
        let _producer = lambda.subscribe_to_application(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut binding_literal,
            &mut Scheduler::new(),
        );

        assert!(
            !notifications.borrow().is_empty(),
            "Expected at least one notification from proper binding flow, got {:#?}.",
            notifications.borrow()
        );
    }

    #[test]
    fn test_apply() {
        // (λx. x)(42) = 42 — apply identity to a literal
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let lambda = Lambda::new(variable, body);
        let argument = Literal::new(Value::Int(42));

        let mut apply = Apply::new(Box::new(lambda), Box::new(argument));

        // Extent should be the codomain (Int)
        assert_eq!(apply.extent(), &Extent::Base(BaseType::Int));

        let (consumer, notifications) = TestConsumer::new();
        let mut producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        assert!(
            !notifications.borrow().is_empty(),
            "Expected at least one notification"
        );

        // Get should return the unwrapped output value: 42
        let column = producer.get().column_value;
        assert_eq!(column, ColumnValue::Ints(vec![42]));
    }

    #[test]
    fn test_apply_constant_function() {
        // (λx. 10)(42) = 10 — apply constant function
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(Literal::new(Value::Int(10)));
        let lambda = Lambda::new(variable, body);
        let argument = Literal::new(Value::Int(42));

        let mut apply = Apply::new(Box::new(lambda), Box::new(argument));

        let (consumer, _) = TestConsumer::new();
        let mut producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        let column = producer.get().column_value;
        assert_eq!(column, ColumnValue::Ints(vec![10]));
    }

    #[test]
    fn test_apply_extent_is_codomain() {
        // Apply's extent should be the codomain of the lambda
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(Literal::new(Value::String("hello".to_string())));
        let lambda = Lambda::new(variable, body);
        let argument = Literal::new(Value::Int(1));

        let apply = Apply::new(Box::new(lambda), Box::new(argument));

        // Lambda: Int -> String, so Apply's extent should be String
        assert_eq!(apply.extent(), &Extent::Base(BaseType::String));
    }

    #[test]
    fn test_apply_release_passes_through() {
        // Verify release passes through to the lambda producer
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let lambda = Lambda::new(variable, body);
        let argument = Literal::new(Value::Int(42));

        let mut apply = Apply::new(Box::new(lambda), Box::new(argument));

        let (consumer, _) = TestConsumer::new();
        let mut producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        let _result = producer.get();

        // Release with Universal should propagate through
        let released = producer.release(Guard::Universal);
        assert!(!released.is_empty());
    }

    #[test]
    fn test_apply_forwards_new_data_notifications() {
        // Verify Apply forwards NewData notifications to its consumer
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let lambda = Lambda::new(variable, body);
        let argument = Literal::new(Value::Int(42));

        let mut apply = Apply::new(Box::new(lambda), Box::new(argument));

        let (consumer, notifications) = TestConsumer::new();
        let _producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        let notifs = notifications.borrow();
        let new_data_count = notifs
            .iter()
            .filter(|n| matches!(n, Notification::NewData))
            .count();
        assert!(
            new_data_count > 0,
            "Expected at least one NewData notification, got: {:?}",
            *notifs
        );
    }

    #[test]
    fn test_apply_yield_guard_is_universal_for_literals() {
        // When applying to a literal, the yield guard from get() should be Universal
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let lambda = Lambda::new(variable, body);
        let argument = Literal::new(Value::Int(42));

        let mut apply = Apply::new(Box::new(lambda), Box::new(argument));

        let (consumer, _) = TestConsumer::new();
        let mut producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        let result = producer.get();
        assert!(
            result.yield_guard.is_universal(),
            "Expected Universal yield guard from apply on literals, got {:?}",
            result.yield_guard
        );
    }

    #[test]
    fn test_apply_with_binop_body() {
        // (λx. x + 1)(42) = 43
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let var_ref = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let one = Box::new(Literal::new(Value::Int(1)));
        let body = Box::new(BinOp::new(
            var_ref,
            BinOpKind::Arithmetic(ArithmeticKind::Add),
            one,
        ));
        let lambda = Lambda::new(variable, body);
        let argument = Literal::new(Value::Int(42));

        let mut apply = Apply::new(Box::new(lambda), Box::new(argument));

        let (consumer, _) = TestConsumer::new();
        let mut producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        let column = producer.get().column_value;
        assert_eq!(column, ColumnValue::Ints(vec![43]));
    }

    #[test]
    fn test_apply_with_string_value() {
        // (λx. x)("hello") = "hello"
        let variable = Var::new("x", Extent::Base(BaseType::String));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::String)));
        let lambda = Lambda::new(variable, body);
        let argument = Literal::new(Value::String("hello".to_string()));

        let mut apply = Apply::new(Box::new(lambda), Box::new(argument));

        let (consumer, _) = TestConsumer::new();
        let mut producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        let column = producer.get().column_value;
        assert_eq!(column, ColumnValue::Strings(vec!["hello".to_string()]));
    }

    #[test]
    fn test_apply_with_parent_scope() {
        // Apply where the body references a variable from an outer scope
        // outer y = 100; (λx. y)(42) = 100
        let parent_variable = Var::new("y", Extent::Base(BaseType::Int));
        let parent_subscription = parent_variable.create_subscription(VarSource::Uninitialized);
        let mut parent_literal = Literal::new(Value::Int(100));
        let parent_sub_consumer: Box<dyn Consumer> = Box::new(parent_subscription.clone());
        let parent_binding = parent_literal.subscribe(
            Guard::universal(),
            parent_sub_consumer,
            None,
            &mut Scheduler::new(),
        );
        parent_subscription
            .borrow_mut()
            .set_source(VarSource::Argument(parent_binding));
        let parent_scope = Rc::new(VarScope::new("y", parent_subscription));

        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("y", Extent::Base(BaseType::Int)));
        let lambda = Lambda::new(variable, body);
        let argument = Literal::new(Value::Int(42));

        let mut apply = Apply::new(Box::new(lambda), Box::new(argument));

        let (consumer, _) = TestConsumer::new();
        let mut producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            Some(parent_scope),
            &mut Scheduler::new(),
        );

        let column = producer.get().column_value;
        assert_eq!(column, ColumnValue::Ints(vec![100]));
    }

    #[test]
    fn test_apply_nested() {
        // (λx. (λy. x)(0))(42) = 42
        // Inner apply: (λy. x)(0), which should return x from outer scope
        let inner_variable = Var::new("y", Extent::Base(BaseType::Int));
        let inner_body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let inner_lambda = Lambda::new(inner_variable, inner_body);
        let inner_argument = Literal::new(Value::Int(0));
        let inner_apply = Apply::new(Box::new(inner_lambda), Box::new(inner_argument));

        let outer_variable = Var::new("x", Extent::Base(BaseType::Int));
        let outer_lambda = Lambda::new(outer_variable, Box::new(inner_apply));
        let outer_argument = Literal::new(Value::Int(42));

        let mut apply = Apply::new(Box::new(outer_lambda), Box::new(outer_argument));

        let (consumer, _) = TestConsumer::new();
        let mut producer = apply.subscribe(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut Scheduler::new(),
        );

        let column = producer.get().column_value;
        assert_eq!(column, ColumnValue::Ints(vec![42]));
    }
}
