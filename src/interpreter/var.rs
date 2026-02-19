//! Variable system: VarScope, VarSource, Var, VarSub, VarRef, VarRefSub, compose_indices.

use std::cell::RefCell;
use std::rc::Rc;

use super::{
    guard_summary, ColumnValue, Consumer, Extent, GetResult, Guard, InspectNode, Notification,
    Operator, ParentIndices, Producer, Scheduler,
};
use log::debug;

/// A variable subscription paired with the chain of iteration-source variables between
/// the current scope and the found variable, used for alignment composition.
type VarWithIterationChain = (Rc<RefCell<VarSub>>, Vec<Rc<RefCell<VarSub>>>);

/// Variable scope for looking up variables.
/// Each scope contains exactly one variable (the lambda's variable).
/// Variables are looked up by name, searching up the parent chain if not found.
#[derive(Debug)]
pub struct VarScope {
    /// Optional parent scope (for nested scopes)
    parent: Option<Rc<VarScope>>,
    /// The variable name in this scope
    name: String,
    /// The variable subscription in this scope
    subscription: Rc<RefCell<VarSub>>,
}

impl VarScope {
    /// Create a new root scope with a single variable.
    pub fn new(name: &str, subscription: Rc<RefCell<VarSub>>) -> Self {
        VarScope {
            parent: None,
            name: name.to_string(),
            subscription,
        }
    }

    /// Create a child scope with a parent.
    pub fn child(parent: Rc<VarScope>, name: &str, subscription: Rc<RefCell<VarSub>>) -> Self {
        VarScope {
            parent: Some(parent),
            name: name.to_string(),
            subscription,
        }
    }

    pub fn new_with_optional_parent(
        parent: Option<Rc<VarScope>>,
        name: &str,
        subscription: Rc<RefCell<VarSub>>,
    ) -> Self {
        VarScope {
            parent,
            name: name.to_string(),
            subscription,
        }
    }

    /// Look up a variable by name, searching up the parent chain.
    /// Returns (subscription, iteration_chain) where iteration_chain contains any iteration-source
    /// variables between the current scope and the found variable (for alignment).
    pub fn lookup_variable(&self, name: &str) -> Option<VarWithIterationChain> {
        self.lookup_with_chain(name, Vec::new())
    }

    fn lookup_with_chain(
        &self,
        name: &str,
        mut chain: Vec<Rc<RefCell<VarSub>>>,
    ) -> Option<VarWithIterationChain> {
        if self.name == name {
            // Found the variable - return it with the chain of inner iterations
            Some((self.subscription.clone(), chain))
        } else {
            // If this scope's variable has iteration source, add it to the chain
            if self.subscription.borrow().is_iteration() {
                chain.push(self.subscription.clone());
            }
            // Continue searching in parent
            self.parent.as_ref()?.lookup_with_chain(name, chain)
        }
    }

    pub fn get_parent(&self) -> Option<Rc<VarScope>> {
        self.parent.clone()
    }
}

// ============================================================================
// Variable Source (Argument vs Iteration)
// ============================================================================

/// The source of values for a variable subscription.
/// Determines whether the variable receives from an argument or iterates over its extent.
#[derive(Debug)]
pub enum VarSource {
    /// Uninitialized state - used during construction when source will be set later.
    /// VarSub operations will panic if called while in this state.
    Uninitialized,
    /// Variable receives values from an argument producer (via Apply).
    /// The variable forwards values from this producer.
    Argument(Box<dyn Producer>),
    /// Variable iterates over its extent (for output or aggregation).
    /// The variable generates values by iterating over all values in its extent.
    Iteration {
        extent: Extent,
        predicate: Guard,
        // TODO: correlations for join execution
    },
}

/// A Var operator represents a variable definition.
/// It holds the variable's name, extent, and predicate - but NOT a static definition.
/// The variable's values are injected at run time either via application (argument source)
/// or direct iteration (iteration source).
#[derive(Debug)]
pub struct Var {
    /// The name of the variable
    pub name: String,
    /// The extent of this variable (may be restricted by predicates)
    extent: Extent,
    /// Predicate that restricts this variable's extent
    /// Applied to guards before propagating to the operator
    predicate: Guard,
}

impl Var {
    /// Create a new variable operator with the given name and extent.
    pub fn new(name: &str, extent: Extent) -> Self {
        Var {
            name: name.to_string(),
            extent,
            predicate: Guard::Universal,
        }
    }

    /// Get the variable's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the extent (type) of this variable.
    pub fn extent(&self) -> &Extent {
        &self.extent
    }

    /// Set a predicate that restricts this variable's extent.
    /// The predicate is applied to guards before propagating to the operator.
    /// Use `Guard::Universal` to remove the predicate (no restriction).
    pub fn set_predicate(&mut self, predicate: Guard) {
        self.predicate = predicate;
    }

    /// Create a VarSub for this variable with the given source.
    ///
    /// The subscription starts with an empty yield guard. For `Argument` source, the
    /// binding operator will notify VarSub when data is ready. For `Iteration` source,
    /// the scheduler will trigger a check for progress, which notifies when data is available.
    ///
    /// Consumers can be added later via `VarSub::add_consumer()`.
    pub fn create_subscription(&self, source: VarSource) -> Rc<RefCell<VarSub>> {
        Rc::new(RefCell::new(VarSub::new(source, self.extent())))
    }
}

// Note: Var does not implement Operator because it cannot be subscribed to directly.
// Variables are always managed by their enclosing context (Lambda, Let, etc.) which
// creates the VarSub with the appropriate VarSource (Argument or Iteration).

/// VarSub implements both Producer and Consumer.
/// It stores the yield guard (monotonically growing) and forwards notifications to all consumers.
pub struct VarSub {
    /// The Extent of the Var
    extent: Extent,
    /// The source of values for this variable (Argument or Iteration)
    source: VarSource,
    /// The current yield guard (monotonically growing)
    /// The contract of `notify` guarantees that guards are monotonically growing.
    yield_guard: Guard,
    /// Whether data is available from the source (set on NewData notification)
    data_available: bool,
    /// All consumers that have subscribed to this variable
    consumers: Vec<Box<dyn Consumer>>,
    /// The stored release guard for use by variable references
    stored_release_guard: Guard,
}

impl std::fmt::Debug for VarSub {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VarSub")
            .field("source", &self.source)
            .field("yield_guard", &self.yield_guard)
            .field("data_available", &self.data_available)
            .field(
                "consumers",
                &format_args!("<{} consumers>", self.consumers.len()),
            )
            .field("stored_release_guard", &self.stored_release_guard)
            .finish()
    }
}

impl VarSub {
    /// Create a new VarSub with the given source.
    fn new(source: VarSource, extent: &Extent) -> Self {
        VarSub {
            extent: extent.clone(),
            source,
            yield_guard: Guard::Empty,
            data_available: false,
            consumers: Vec::new(),
            stored_release_guard: Guard::Empty,
        }
    }

    /// Add a consumer and catch it up to the current state.
    pub fn add_consumer(&mut self, mut consumer: Box<dyn Consumer>) {
        // This fires when the binding operator completed synchronously
        // during subscribe() (e.g., Literal). At subscribe time, no
        // releases have happened, so data_available is trustworthy.
        if self.data_available {
            // Prioritize NewData since get() returns the authoritative
            // guard, so the consumer gets both data and progress in one call.
            consumer.notify(Notification::NewData);
        } else if !self.yield_guard.is_empty() {
            consumer.notify(Notification::Yield(self.yield_guard.clone()));
        }
        debug_assert!(
            self.stored_release_guard.is_empty(),
            "add_consumer called after releases have occurred"
        );
        self.consumers.push(consumer);
    }

    /// Get the current yield guard.
    pub fn get_yield_guard(&self) -> Guard {
        self.yield_guard.clone()
    }

    /// Store a release guard.
    fn store_release_guard(&mut self, guard: Guard) {
        self.stored_release_guard = guard;
    }

    /// Get the stored release guard.
    pub fn get_stored_release_guard(&self) -> Guard {
        self.stored_release_guard.clone()
    }

    /// Check if this variable has iteration source.
    pub fn is_iteration(&self) -> bool {
        matches!(self.source, VarSource::Iteration { .. })
    }

    /// Set the source for this variable subscription.
    /// Used when the source needs to be updated after creation (e.g., for `Argument` source).
    pub fn set_source(&mut self, source: VarSource) {
        assert!(
            matches!(self.source, VarSource::Uninitialized),
            "VarSub::set_source() called while source is not Uninitialized"
        );
        self.source = source;
    }

    pub fn check_for_notification(&mut self) {
        match &mut self.source {
            VarSource::Iteration {
                extent: Extent::DataSourceDomain(extent_impl),
                ..
            } => {
                let notification = if extent_impl.borrow_mut().check_for_new_data() {
                    Notification::NewData
                } else {
                    self.yield_guard = extent_impl.borrow().get_yield_guard();
                    Notification::Yield(self.yield_guard.clone())
                };
                self.consumers
                    .iter_mut()
                    .for_each(|c| c.notify(notification.clone()));
            }
            _ => panic!(
                "Expected VarSub with DataSource input, got {:?}",
                self.source
            ),
        };
    }

    pub fn get_extent(&self) -> &Extent {
        &self.extent
    }
}

impl Producer for VarSub {
    fn get(&mut self) -> GetResult {
        match &mut self.source {
            VarSource::Uninitialized => {
                panic!("VarSub::get() called while source is Uninitialized")
            }
            VarSource::Argument(producer) => producer.get(),
            VarSource::Iteration {
                extent,
                predicate: _,
            } => match extent {
                Extent::UIntRange { start, end } => {
                    self.yield_guard = Guard::Universal;
                    GetResult {
                        column_value: ColumnValue::from_uints((*start..*end).collect()),
                        yield_guard: Guard::Universal,
                    }
                }
                Extent::DataSourceDomain(source_impl) => {
                    let values = source_impl.borrow_mut().get_elements();
                    let yield_guard = source_impl.borrow().get_yield_guard();
                    self.yield_guard = yield_guard.clone();
                    let get_result = GetResult {
                        column_value: ColumnValue::from_column_data(values),
                        yield_guard,
                    };
                    debug!("Generating source values {get_result:#?}");
                    get_result
                }
                _ => panic!("Attempted to iterate on infinite Extent"),
            },
        }
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        // Store the release guard for use by variable references
        self.store_release_guard(obsolete_guard.clone());
        // Forward release to source
        match &mut self.source {
            VarSource::Uninitialized => {
                panic!("VarSub::release() called while source is Uninitialized")
            }
            VarSource::Argument(producer) => producer.release(obsolete_guard),
            VarSource::Iteration {
                extent: Extent::DataSourceDomain(source_impl),
                ..
            } => source_impl.borrow_mut().release(obsolete_guard),
            VarSource::Iteration { .. } => {
                // For iteration over literal sources, nothing to do
                obsolete_guard
            }
        }
    }

    // TODO: Include ref to corresponding Var so we know what the VarSub is.
    fn inspect(&self) -> InspectNode {
        let source_label = match &self.source {
            VarSource::Uninitialized => "Uninitialized".to_string(),
            VarSource::Argument(_) => "Argument".to_string(),
            VarSource::Iteration { extent, .. } => format!("Iteration({extent:?})"),
        };
        let children = match &self.source {
            VarSource::Argument(p) => vec![p.inspect()],
            _ => vec![],
        };
        InspectNode {
            type_name: "VarSub".to_string(),
            label: format!("{}, {} consumers", source_label, self.consumers.len()),
            yield_guard: guard_summary(&self.yield_guard),
            data_summary: String::new(),
            children,
        }
    }
}

impl Consumer for VarSub {
    fn notify(&mut self, notification: Notification) {
        match &notification {
            Notification::Yield(guard) => {
                debug!("Setting VarSub yield guard {guard:?}");
                self.yield_guard = guard.clone();
            }
            Notification::NewData => {
                self.data_available = true;
            }
        }
        // Forward to all consumers
        for consumer in self.consumers.iter_mut() {
            consumer.notify(notification.clone());
        }
    }
}

/// A VarRef operator represents a reference to a variable.
/// It holds the variable name and looks it up in the VarScope when subscribing.
#[derive(Debug)]
pub struct VarRef {
    /// The name of the variable being referenced
    name: String,
    /// The extent (cached from the variable when found)
    extent: Extent,
}

impl VarRef {
    /// Create a new variable reference.
    pub fn new(name: &str, extent: Extent) -> Self {
        VarRef {
            name: name.to_string(),
            extent,
        }
    }
}

impl Operator for VarRef {
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
        // Look up the variable in the scope
        let var_scope = var_scope.expect("VarRef requires a VarScope");
        let (variable_subscription, iteration_chain) = var_scope
            .lookup_variable(&self.name)
            .unwrap_or_else(|| panic!("Variable '{}' not found in scope", self.name));

        // Create VarRefSub with the consumer and iteration chain for alignment
        let ref_subscription = Rc::new(RefCell::new(VarRefSub {
            variable_subscription: variable_subscription.clone(),
            iteration_chain,
            intent_guard,
            consumer,
        }));

        // Add the VarRefSub as the consumer of the variable subscription
        let ref_subscription_consumer: Box<dyn Consumer> = Box::new(ref_subscription.clone());
        variable_subscription
            .borrow_mut()
            .add_consumer(ref_subscription_consumer);

        Box::new(ref_subscription) // As a producer.
    }
}

/// VarRefSub implements both Producer and Consumer.
/// As a Consumer: it receives notifications from VarSub, intersects
/// the yield guard with its intent guard, and forwards to the actual consumer.
/// As a Producer: it provides access to data and handles release requests.
struct VarRefSub {
    /// Reference to the VarSub
    variable_subscription: Rc<RefCell<VarSub>>,
    /// Chain of iteration-source variables between current scope and referenced variable (for alignment)
    iteration_chain: Vec<Rc<RefCell<VarSub>>>,
    /// The intent guard for this subscription
    intent_guard: Guard,
    /// The consumer of the variable ref that will receive filtered notifications
    consumer: Box<dyn Consumer>,
}

impl std::fmt::Debug for VarRefSub {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VarRefSub")
            .field("variable_subscription", &self.variable_subscription)
            .field("iteration_chain", &self.iteration_chain)
            .field("intent_guard", &self.intent_guard)
            .field("consumer", &format_args!("<consumer>"))
            .finish()
    }
}

impl Consumer for VarRefSub {
    fn notify(&mut self, notification: Notification) {
        match notification {
            Notification::Yield(guard) => {
                let restricted = guard.intersect(self.intent_guard.clone());
                self.consumer.notify(Notification::Yield(restricted));
            }
            Notification::NewData => {
                self.consumer.notify(Notification::NewData);
            }
        }
    }
}

/// Compose parent indices: maps inner indices through outer indices.
/// For inner[i], result[i] = outer[inner[i]]
pub fn compose_indices(outer: &[usize], inner: &[usize]) -> Vec<usize> {
    inner.iter().map(|&i| outer[i]).collect()
}

impl Producer for VarRefSub {
    fn get(&mut self) -> GetResult {
        // Get data from variable subscription
        let var_result = self.variable_subscription.borrow_mut().get();

        // TODO: Filter data based on intent guard

        // If no iteration chain, no alignment needed
        if self.iteration_chain.is_empty() {
            return var_result;
        }

        // Compose parent_indices from innermost iteration to outermost
        // The chain is ordered from innermost (first after current scope) to outermost (closest to variable)
        let mut composed_indices: Option<Vec<usize>> = None;
        for iter_var in self.iteration_chain.iter().rev() {
            // Get this iteration variable's parent_indices
            let iter_result = iter_var.borrow_mut().get();
            if let ParentIndices::Parent(parent_indices) = iter_result.column_value.parent_indices {
                composed_indices = Some(match composed_indices {
                    None => parent_indices,
                    Some(inner) => compose_indices(&parent_indices, &inner),
                });
            }
        }

        // Expand column using composed indices
        match composed_indices {
            Some(indices) => GetResult {
                column_value: var_result.column_value.expand(&indices),
                yield_guard: var_result.yield_guard,
            },
            None => var_result,
        }
    }

    fn release(&mut self, _obsolete_guard: Guard) -> Guard {
        // Return the stored release guard from the variable subscription
        self.variable_subscription
            .borrow()
            .get_stored_release_guard()
    }

    // TODO: Make node collapsed by default so it's not confusing to see the same VarSub
    // in multiple places in the tree. Maybe draw an arrow to the VarSub, or color coordinate them?
    fn inspect(&self) -> InspectNode {
        InspectNode {
            type_name: "VarRefSub".to_string(),
            label: format!("intent: {}", guard_summary(&self.intent_guard)),
            yield_guard: guard_summary(&self.variable_subscription.borrow().yield_guard),
            data_summary: String::new(),
            children: vec![self.variable_subscription.borrow().inspect()],
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter::test_helpers::TestConsumer;
    use crate::interpreter::*;
    use std::rc::Rc;
    use test_log::test;

    #[test]
    fn test_variable_proxy() {
        // Create variable and its reference
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let mut var_ref = VarRef::new("x", Extent::Base(BaseType::Int));

        assert_eq!(var_ref.extent(), &Extent::Base(BaseType::Int));

        // Create VarSub in Uninitialized state first
        let var_subscription = variable.create_subscription(VarSource::Uninitialized);

        // Subscribe to the binding literal with VarSub as the consumer
        // This ensures VarSub receives notifications
        let mut binding_literal = Literal::new(Value::Int(42));
        let var_sub_consumer: Box<dyn Consumer> = Box::new(var_subscription.clone());
        let binding_producer = binding_literal.subscribe(
            Guard::universal(),
            var_sub_consumer,
            None,
            &mut Scheduler::new(),
        );

        // Now set VarSub's source to `Argument` with the producer
        var_subscription
            .borrow_mut()
            .set_source(VarSource::Argument(binding_producer));

        // Create a VarScope with the variable
        let var_scope = VarScope::new("x", var_subscription);

        // Subscribe and verify it works
        let (consumer, notifications) = TestConsumer::new();
        let mut producer = var_ref.subscribe(
            Guard::universal(),
            Box::new(consumer),
            Some(Rc::new(var_scope)),
            &mut Scheduler::new(),
        );

        // Verify notification was received (flows: Literal → VarSub → VarRefSub → consumer)
        let notifications_borrowed = notifications.borrow();
        assert_eq!(notifications_borrowed.len(), 1);
        assert!(matches!(notifications_borrowed[0], Notification::NewData));

        // Verify get returns the value (as a single-element column)
        let result = producer.get();
        assert_eq!(result.column_value.as_single().unwrap(), Value::Int(42));

        // Verify release returns stored release guard (initially empty)
        let released = producer.release(Guard::universal());
        assert_eq!(released, Guard::Empty);
    }
}
