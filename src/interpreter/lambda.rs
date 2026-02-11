//! Lambda operator: lambda expressions with variable binding and scope management.

use std::cell::RefCell;
use std::rc::Rc;

use super::{
    ColumnValue, Consumer, Extent, FuncBinding, Guard, Operator, Producer, Value, Var, VarScope,
    VarSource, VarSub,
};

/// A Lambda operator represents a lambda expression.
/// It has a variable and a body, and manages the variable scope.
#[derive(Debug)]
pub struct Lambda {
    variable: Var,
    body: Box<dyn Operator>,
    extent: Extent,
}

/// LambdaProducer implements both Producer and Consumer.
/// As a Consumer: receives notifications from variable and body, tracks yield guards,
/// and notifies downstream when function bindings are ready.
/// As a Producer: provides function bindings via get(), handles release.
struct LambdaProducer {
    /// Reference to the variable subscription (for domain values)
    variable_subscription: Rc<RefCell<VarSub>>,
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
        variable_subscription: Rc<RefCell<VarSub>>,
        downstream_consumer: Box<dyn Consumer>,
        intent_guard: Guard,
    ) -> Self {
        LambdaProducer {
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

    /// Check if both variable and body have yielded data, and notify downstream if so.
    fn check_and_notify(&mut self) {
        // Both guards must be non-empty for us to have data
        if !self.variable_yield_guard.is_empty() && !self.body_yield_guard.is_empty() {
            // Combine the yield guards into a function guard
            let combined_yield_guard = Guard::from_independent_function_parts(
                self.variable_yield_guard.clone(),
                self.body_yield_guard.clone(),
            );

            let restricted_guard = combined_yield_guard.intersect(self.intent_guard.clone());

            self.downstream_consumer.notify(restricted_guard);
        }
    }
}

impl Producer for LambdaProducer {
    /// Get the function bindings by combining domain values from the variable
    /// and codomain values from the body.
    fn get(&mut self) -> ColumnValue {
        // Get domain values from variable
        let domain_column = self.variable_subscription.borrow_mut().get();

        // Get codomain values from body (columnar)
        let codomain_column = self
            .body_producer
            .as_mut()
            .expect("body_producer should be set before get()")
            .get();

        // Combine domain and codomain into function bindings
        // The domain and codomain columns should be aligned (same length)
        // Each pair (domain[i], codomain[i]) forms a binding
        let bindings: Vec<FuncBinding> = domain_column
            .values
            .iter()
            .zip(codomain_column.values.iter())
            .map(|(input, output)| FuncBinding {
                input: input.clone(),
                output: output.clone(),
            })
            .collect();

        // Return as a single Function value containing all bindings
        // The parent_indices from the domain column are preserved for alignment
        ColumnValue {
            values: vec![Value::Function(bindings)],
            parent_indices: domain_column.parent_indices,
        }
    }

    /// Release interest in a region by splitting the obsolete guard and
    /// releasing both the variable and body.
    fn release(&mut self, obsolete_guard: Guard) -> Guard {
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
        Guard::from_independent_function_parts(expanded_domain_obsolete, expanded_codomain_obsolete)
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

    /// Subscribe to this lambda with an explicit binding operator for the variable.
    /// This is used by Application to bind the argument to the lambda's variable.
    ///
    /// # Arguments
    /// * `intent_guard` - The region of the function extent the consumer is interested in
    /// * `consumer` - The consumer that will receive notifications
    /// * `var_scope` - The variable scope for looking up outer variables
    /// * `binding` - The operator that provides values for the lambda's variable (Bound mode)
    pub fn subscribe_with_binding(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        binding: &mut dyn Operator,
    ) -> Box<dyn Producer> {
        self.subscribe_internal(intent_guard, consumer, var_scope, Some(binding))
    }

    /// Internal subscribe implementation that handles both bound and scanning modes.
    fn subscribe_internal(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        binding: Option<&mut dyn Operator>,
    ) -> Box<dyn Producer> {
        // Split intent guard into domain and codomain
        let (domain_guard, codomain_guard) = intent_guard
            .split_function()
            .unwrap_or((Guard::universal(), Guard::universal()));

        // For Bound mode: subscribe to the binding operator with VarSub as consumer
        // This ensures VarSub receives notifications and can forward to its consumers
        let variable_subscription = if let Some(binding_op) = binding {
            let subscription = self.variable.create_subscription(VarSource::Uninitialized);

            // Subscribe to binding with VarSub as the consumer
            // VarSub implements Consumer, so it will receive notifications
            let var_sub_consumer: Box<dyn Consumer> = Box::new(subscription.clone());
            let binding_producer =
                binding_op.subscribe(domain_guard.clone(), var_sub_consumer, None);

            // Now set the source to Bound with the actual producer
            subscription
                .borrow_mut()
                .set_source(VarSource::Bound(binding_producer));
            subscription
        } else {
            // Scanning mode
            self.variable.create_subscription(VarSource::Scanning {
                extent: self.variable.extent().clone(),
                predicate: domain_guard.clone(),
            })
        };

        // Create LambdaProducer with the variable subscription (body_producer set later)
        let lambda_producer = Rc::new(RefCell::new(LambdaProducer::new(
            variable_subscription.clone(),
            consumer,
            intent_guard.clone(),
        )));

        // Create the variable consumer closure that captures LambdaProducer
        // This is added to VarSub's consumers so it gets notified when the variable is ready
        let lambda_producer_for_var = lambda_producer.clone();
        let variable_consumer: Box<dyn Consumer> = Box::new(move |yield_guard: Guard| {
            let mut producer = lambda_producer_for_var.borrow_mut();
            producer.variable_yield_guard = yield_guard;
            producer.check_and_notify();
        });

        // Add the consumer to the variable subscription
        // For Bound mode: VarSub may have already been notified by the binding, and add_consumer
        // will immediately notify this consumer if yield_guard is non-empty
        variable_subscription
            .borrow_mut()
            .add_consumer(variable_consumer);

        // Create a new VarScope with this variable
        let new_scope = if let Some(parent) = var_scope {
            VarScope::child(parent, &self.variable.name, variable_subscription)
        } else {
            VarScope::new(&self.variable.name, variable_subscription)
        };

        // Create closure for body notifications: updates body_yield_guard and checks if ready
        let lambda_producer_for_body = lambda_producer.clone();
        let body_consumer: Box<dyn Consumer> = Box::new(move |yield_guard: Guard| {
            let mut producer = lambda_producer_for_body.borrow_mut();
            producer.body_yield_guard = yield_guard;
            producer.check_and_notify();
        });

        // Subscribe to the body with the closure as consumer
        let body_producer =
            self.body
                .subscribe(codomain_guard, body_consumer, Some(Rc::new(new_scope)));

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

    fn subscribe(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
    ) -> Box<dyn Producer> {
        // When subscribe is called without a binding, the variable is in scanning mode.
        // This happens when the lambda is used by an aggregation operator (e.g., sum).
        self.subscribe_internal(intent_guard, consumer, var_scope, None)
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter::test_helpers::TestConsumer;
    use crate::interpreter::*;
    use std::rc::Rc;

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
            _ => panic!("Expected function extent, got {:?}", extent),
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
        let mut producer = lambda.subscribe_with_binding(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut binding_literal,
        );

        // Check notifications - we should get one when both are ready
        let notifications_borrowed = notifications.borrow();
        assert!(
            !notifications_borrowed.is_empty(),
            "Expected at least 1 notification, got {}",
            notifications_borrowed.len()
        );

        // Get the function bindings (as a single-element column containing a Function value)
        let column = producer.get();
        assert_eq!(column.values.len(), 1);
        match &column.values[0] {
            Value::Function(bindings) => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].input, Value::Int(42));
                assert_eq!(bindings[0].output, Value::Int(42));
            }
            _ => panic!("Expected Function value, got {:?}", column.values[0]),
        }
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
        let mut producer = lambda.subscribe_with_binding(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut binding_literal,
        );

        // Both variable and body should notify
        let notifications_borrowed = notifications.borrow();
        assert!(
            !notifications_borrowed.is_empty(),
            "Expected at least 1 notification, got {}",
            notifications_borrowed.len()
        );

        // Get the function bindings (as a single-element column containing a Function value)
        let column = producer.get();
        assert_eq!(column.values.len(), 1);
        match &column.values[0] {
            Value::Function(bindings) => {
                assert_eq!(bindings.len(), 1);
                // Input is from binding (literal 0)
                assert_eq!(bindings[0].input, Value::Int(0));
                // Output is from body (literal 10)
                assert_eq!(bindings[0].output, Value::Int(10));
            }
            _ => panic!("Expected Function value, got {:?}", column.values[0]),
        }
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
        let mut producer = lambda.subscribe_with_binding(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut binding_literal,
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
        let mut producer = lambda.subscribe_with_binding(
            intent_guard,
            Box::new(consumer),
            None,
            &mut binding_literal,
        );

        // Should receive notification
        let notifications_borrowed = notifications.borrow();
        assert!(
            !notifications_borrowed.is_empty(),
            "Expected at least 1 notification"
        );

        // Get should work
        let column = producer.get();
        assert_eq!(column.values.len(), 1);
        match &column.values[0] {
            Value::Function(bindings) => {
                assert!(!bindings.is_empty());
            }
            _ => panic!("Expected Function value"),
        }
    }

    #[test]
    fn test_lambda_nested_scope() {
        // Test that lambda creates a new scope for its variable
        // Create: λ x . x where x is defined in the lambda
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let mut lambda = Lambda::new(variable, body);

        // Create a parent scope with a different variable "x" bound to 200
        let parent_variable = Var::new("x", Extent::Base(BaseType::Int));
        // Create parent subscription and wire up binding properly
        let parent_subscription = parent_variable.create_subscription(VarSource::Uninitialized);
        let mut parent_literal = Literal::new(Value::Int(200));
        let parent_sub_consumer: Box<dyn Consumer> = Box::new(parent_subscription.clone());
        let parent_binding =
            parent_literal.subscribe(Guard::universal(), parent_sub_consumer, None);
        parent_subscription
            .borrow_mut()
            .set_source(VarSource::Bound(parent_binding));
        let parent_scope = VarScope::new("x", parent_subscription);

        let mut binding_literal = Literal::new(Value::Int(100));

        // Subscribe to lambda with parent scope and binding operator
        // The lambda should create its own scope, so the body should reference
        // the lambda's variable (100), not the parent's (200)
        let (consumer, _) = TestConsumer::new();
        let mut producer = lambda.subscribe_with_binding(
            Guard::universal(),
            Box::new(consumer),
            Some(Rc::new(parent_scope)),
            &mut binding_literal,
        );

        // Get the value - should use lambda's variable (100), not parent's (200)
        let column = producer.get();
        assert_eq!(column.values.len(), 1);
        match &column.values[0] {
            Value::Function(bindings) => {
                assert_eq!(bindings.len(), 1);
                // The input should be from the lambda's variable binding
                assert_eq!(bindings[0].input, Value::Int(100));
                // The output should also be 100 (identity function)
                assert_eq!(bindings[0].output, Value::Int(100));
            }
            _ => panic!("Expected Function value"),
        }
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
        let _producer = lambda.subscribe_with_binding(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut binding_literal,
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

        // The notification should be a function guard (or restricted version)
        let last_notification = notifications_borrowed.last().unwrap();
        // It should not be empty
        assert!(!last_notification.is_empty());
    }

    #[test]
    fn test_binding_notifications_flow_through_varsub() {
        // This test verifies that binding notifications flow through VarSub to VarRefSub.
        // Previously, we had a bug where the binding's consumer was a TestConsumer,
        // so notifications never reached VarSub. VarSub's yield_guard was set manually,
        // which made add_consumer() notify immediately, masking the issue.
        //
        // This test catches the bug by:
        // 1. Creating a lambda with a VarRef body (so VarRefSub is in the consumers list)
        // 2. Verifying a notification is received by the lambda's consumer.

        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x", Extent::Base(BaseType::Int)));
        let mut lambda = Lambda::new(variable, body);

        let mut binding_literal = Literal::new(Value::Int(42));

        let (consumer, notifications) = TestConsumer::new();
        let _producer = lambda.subscribe_with_binding(
            Guard::universal(),
            Box::new(consumer),
            None,
            &mut binding_literal,
        );

        assert!(
            notifications.borrow().len() == 1,
            "Expected exactly 1 notification from proper binding flow, got {:#?}.",
            notifications.borrow()
        );
    }
}
