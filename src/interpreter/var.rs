//! Variable system: VarScope, VarSource, Var, VarSub, VarRef, VarRefSub, compose_indices.

use std::cell::RefCell;
use std::rc::Rc;

use crate::interpreter::{GetResult, Notification, Value};

use super::{BaseType, ColumnValue, Consumer, Extent, Guard, Operator, Producer};

/// A variable subscription paired with the chain of scanning variables between
/// the current scope and the found variable, used for alignment composition.
type VarWithScanChain = (Rc<RefCell<VarSub>>, Vec<Rc<RefCell<VarSub>>>);

/// Variable scope for looking up variables.
/// Each scope contains exactly one variable (the lambda's bound variable).
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
    /// Returns (subscription, scan_chain) where scan_chain contains any scanning
    /// variables between the current scope and the found variable (for alignment).
    pub fn lookup_variable(&self, name: &str) -> Option<VarWithScanChain> {
        self.lookup_with_chain(name, Vec::new())
    }

    fn lookup_with_chain(
        &self,
        name: &str,
        mut chain: Vec<Rc<RefCell<VarSub>>>,
    ) -> Option<VarWithScanChain> {
        if self.name == name {
            // Found the variable - return it with the chain of inner scans
            Some((self.subscription.clone(), chain))
        } else {
            // If this scope's variable is scanning, add it to the chain
            if self.subscription.borrow().is_scanning() {
                chain.push(self.subscription.clone());
            }
            // Continue searching in parent
            self.parent.as_ref()?.lookup_with_chain(name, chain)
        }
    }
}

// ============================================================================
// Variable Source (Bound vs Scanning)
// ============================================================================

/// The source of values for a variable subscription.
/// Determines whether the variable is bound to a producer or scanning its extent.
#[derive(Debug)]
pub enum VarSource {
    /// Uninitialized state - used during construction when source will be set later.
    /// VarSub operations will panic if called while in this state.
    Uninitialized,
    /// Variable is bound to a producer (from Application).
    /// The variable forwards values from this producer.
    Bound(Box<dyn Producer>),
    /// Variable scans its extent (for aggregation).
    /// The variable iterates over all values in its extent.
    Scanning {
        extent: Extent,
        predicate: Guard,
        // TODO: correlations for join execution
    },
}

/// A Var operator represents a variable definition.
/// It holds the variable's name, extent, and predicate - but NOT a static definition.
/// Binding happens dynamically via Application (Bound mode) or aggregation (Scanning mode).
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
    /// The subscription starts with an empty yield guard. For Bound mode, the
    /// binding operator will notify VarSub when data is ready. For Scanning mode,
    /// the scan will notify when data is available.
    ///
    /// Consumers can be added later via `VarSub::add_consumer()`.
    pub fn create_subscription(&self, source: VarSource) -> Rc<RefCell<VarSub>> {
        Rc::new(RefCell::new(VarSub::new(source)))
    }
}

// Note: Var does not implement Operator because it cannot be subscribed to directly.
// Variables are always managed by their enclosing context (Lambda, Let, etc.) which
// creates the VarSub with the appropriate VarSource (Bound or Scanning).

/// VarSub implements both Producer and Consumer.
/// It stores the yield guard (monotonically growing) and forwards notifications to all consumers.
pub struct VarSub {
    /// The source of values for this variable (Bound or Scanning)
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
    fn new(source: VarSource) -> Self {
        VarSub {
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

    /// Check if this variable is in scanning mode.
    pub fn is_scanning(&self) -> bool {
        matches!(self.source, VarSource::Scanning { .. })
    }

    /// Set the source for this variable subscription.
    /// Used when the source needs to be updated after creation (e.g., for Bound mode).
    pub fn set_source(&mut self, source: VarSource) {
        assert!(
            matches!(self.source, VarSource::Uninitialized),
            "VarSub::set_source() called while source is not Uninitialized"
        );
        self.source = source;
    }
}

impl Producer for VarSub {
    fn get(&mut self) -> GetResult {
        match &mut self.source {
            VarSource::Uninitialized => {
                panic!("VarSub::get() called while source is Uninitialized")
            }
            VarSource::Bound(producer) => producer.get(),
            VarSource::Scanning {
                extent,
                predicate: _,
            } => {
                // TODO: Implement actual scanning over extent
                // For now, return a placeholder based on extent type
                let data = match extent {
                    Extent::UIntRange { start, end } => ColumnValue::from_values(
                        (*start as i64..*end as i64).map(Value::Int).collect(),
                    ),
                    Extent::Base(BaseType::Int) => {
                        // Placeholder: return empty column for now
                        // Real implementation would scan the extent
                        ColumnValue::from_values(vec![])
                    }
                    _ => ColumnValue::from_values(vec![]),
                };
                GetResult {
                    column_value: data,
                    yield_guard: self.yield_guard.clone(),
                }
            }
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
            VarSource::Bound(producer) => producer.release(obsolete_guard),
            VarSource::Scanning { .. } => {
                // For scanning, just return the obsolete guard unchanged
                // TODO: Once we support scanning over data-defined extents, propagate releases into it.
                obsolete_guard
            }
        }
    }
}

impl Consumer for VarSub {
    fn notify(&mut self, notification: Notification) {
        match &notification {
            Notification::Yield(guard) => {
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
    ) -> Box<dyn Producer> {
        // Look up the variable in the scope
        let var_scope = var_scope.expect("VarRef requires a VarScope");
        let (variable_subscription, scan_chain) = var_scope
            .lookup_variable(&self.name)
            .unwrap_or_else(|| panic!("Variable '{}' not found in scope", self.name));

        // Create VarRefSub with the consumer and scan chain for alignment
        let ref_subscription = Rc::new(RefCell::new(VarRefSub {
            variable_subscription: variable_subscription.clone(),
            scan_chain,
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
    /// Chain of scanning variables between current scope and referenced variable (for alignment)
    scan_chain: Vec<Rc<RefCell<VarSub>>>,
    /// The intent guard for this subscription
    intent_guard: Guard,
    /// The consumer of the variable ref that will receive filtered notifications
    consumer: Box<dyn Consumer>,
}

impl std::fmt::Debug for VarRefSub {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VarRefSub")
            .field("variable_subscription", &self.variable_subscription)
            .field("scan_chain", &self.scan_chain)
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

        // If no scan chain, no alignment needed
        if self.scan_chain.is_empty() {
            return var_result;
        }

        // Compose parent_indices from innermost scan to outermost
        // The chain is ordered from innermost (first after current scope) to outermost (closest to variable)
        let mut composed_indices: Option<Vec<usize>> = None;
        for scan in self.scan_chain.iter().rev() {
            // Get this scan's parent_indices
            let scan_result = scan.borrow_mut().get();
            if let Some(parent_indices) = scan_result.column_value.parent_indices {
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
}

#[cfg(test)]
mod tests {
    use crate::interpreter::test_helpers::TestConsumer;
    use crate::interpreter::*;
    use std::rc::Rc;

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
        let binding_producer =
            binding_literal.subscribe(Guard::universal(), var_sub_consumer, None);

        // Now set VarSub's source to Bound with the producer
        var_subscription
            .borrow_mut()
            .set_source(VarSource::Bound(binding_producer));

        // Create a VarScope with the variable
        let var_scope = VarScope::new("x", var_subscription);

        // Subscribe and verify it works
        let (consumer, notifications) = TestConsumer::new();
        let mut producer = var_ref.subscribe(
            Guard::universal(),
            Box::new(consumer),
            Some(Rc::new(var_scope)),
        );

        // Verify notification was received (flows: Literal → VarSub → VarRefSub → consumer)
        let notifications_borrowed = notifications.borrow();
        assert_eq!(notifications_borrowed.len(), 1);
        assert!(matches!(notifications_borrowed[0], Notification::NewData));

        // Verify get returns the value (as a single-element column)
        let result = producer.get();
        assert_eq!(result.column_value.values.len(), 1);
        assert_eq!(result.column_value.values[0], Value::Int(42));

        // Verify release returns stored release guard (initially empty)
        let released = producer.release(Guard::universal());
        assert_eq!(released, Guard::Empty);
    }
}
