//! PCL (Pototo Core Language) Interpreter
//!
//! This module implements the dataflow-based interpreter for PCL.
//! Execution proceeds via a producer/consumer protocol using guards and extents.

use std::collections::HashMap;

/// A Guard represents a region (subset of an extent) via a set of predicates.
/// Guards are used to:
/// - Specify intent (what region a consumer is interested in)
/// - Track yield (what region is ready and won't see further data)
/// - Track obsolescence (what region is no longer needed)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Guard {
    /// The universal guard representing the entire extent
    Universal,
    /// An empty guard representing no region
    Empty,
    /// A guard representing equality: variable == value
    Equality { variable: String, value: Value },
    /// A guard representing set membership: variable ∈ set
    Membership {
        variable: String,
        values: Vec<Value>,
    },
    /// A guard representing inequality: variable != value
    Inequality { variable: String, value: Value },
    /// A conjunction of guards (all must be satisfied)
    And(Vec<Guard>),
    /// A disjunction of guards (at least one must be satisfied)
    Or(Vec<Guard>),
    /// A guard for a function type: combines domain and codomain guards
    Function {
        domain: Box<Guard>,
        codomain: Box<Guard>,
    },
    /// A guard for a record type: maps field names to their guards
    Record(HashMap<String, Guard>),
}

impl Guard {
    /// Create an empty guard
    pub fn empty() -> Self {
        Guard::Empty
    }

    /// Create a universal guard
    pub fn universal() -> Self {
        Guard::Universal
    }

    /// Check if this guard is empty (represents no region)
    pub fn is_empty(&self) -> bool {
        matches!(self, Guard::Empty)
    }

    /// Check if this guard is universal (represents entire extent)
    pub fn is_universal(&self) -> bool {
        matches!(self, Guard::Universal)
    }

    /// Intersect two guards (conjunction)
    pub fn intersect(self, other: Guard) -> Guard {
        match (self, other) {
            (Guard::Empty, _) | (_, Guard::Empty) => Guard::Empty,
            (Guard::Universal, g) | (g, Guard::Universal) => g,
            (Guard::And(mut guards), g) => {
                guards.push(g);
                Guard::And(guards)
            }
            (g, Guard::And(mut guards)) => {
                guards.insert(0, g);
                Guard::And(guards)
            }
            (g1, g2) => Guard::And(vec![g1, g2]),
        }
    }

    /// Union two guards (disjunction)
    pub fn union(self, other: Guard) -> Guard {
        match (self, other) {
            (Guard::Empty, g) | (g, Guard::Empty) => g,
            (Guard::Universal, _) | (_, Guard::Universal) => Guard::Universal,
            (Guard::Or(mut guards), g) => {
                guards.push(g);
                Guard::Or(guards)
            }
            (g, Guard::Or(mut guards)) => {
                guards.insert(0, g);
                Guard::Or(guards)
            }
            (g1, g2) => Guard::Or(vec![g1, g2]),
        }
    }

    /// Split a function guard into domain and codomain guards
    pub fn split_function(&self) -> Option<(Guard, Guard)> {
        match self {
            Guard::Function { domain, codomain } => Some((*domain.clone(), *codomain.clone())),
            Guard::Universal => {
                // Universal function guard means universal domain and codomain
                Some((Guard::Universal, Guard::Universal))
            }
            _ => None,
        }
    }

    /// Split a record guard into field guards
    pub fn split_record(&self) -> Option<HashMap<String, Guard>> {
        match self {
            Guard::Record(fields) => Some(fields.clone()),
            Guard::Universal => {
                // Universal record guard means universal for all fields
                // This is a placeholder - in practice we'd need the record schema
                Some(HashMap::new())
            }
            _ => None,
        }
    }

    /// Create a function guard from domain and codomain guards
    pub fn from_function_parts(domain: Guard, codomain: Guard) -> Self {
        Guard::Function {
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// Create a function guard from independent domain and codomain guards
    pub fn from_independent_function_parts(domain: Guard, codomain: Guard) -> Self {
        Guard::union(
            Guard::Function {
                domain: Box::new(domain),
                codomain: Box::new(Guard::Universal),
            },
            Guard::Function {
                domain: Box::new(Guard::Universal),
                codomain: Box::new(codomain),
            },
        )
    }

    /// Create a record guard from field guards
    pub fn from_record_parts(fields: HashMap<String, Guard>) -> Self {
        Guard::Record(fields)
    }
}

/// An Extent represents the set of values a term can take on (its type).
/// Each operator has an extent that corresponds exactly to its type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Extent {
    /// A base type (e.g., integer, string, boolean)
    Base(BaseType),
    /// A function type: domain -> codomain
    Function {
        domain: Box<Extent>,
        codomain: Box<Extent>,
    },
    /// A record type: map of field names to their extents
    Record(HashMap<String, Extent>),
    /// A union type: one of several possible extents
    Union(Vec<Extent>),
}

impl Extent {
    /// Create a function extent from domain and codomain
    pub fn function(domain: Extent, codomain: Extent) -> Self {
        Extent::Function {
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// Create a record extent from field extents
    pub fn record(fields: HashMap<String, Extent>) -> Self {
        Extent::Record(fields)
    }

    /// Split a function extent into domain and codomain
    pub fn split_function(&self) -> Option<(&Extent, &Extent)> {
        match self {
            Extent::Function { domain, codomain } => Some((domain, codomain)),
            _ => None,
        }
    }

    /// Split a record extent into field extents
    pub fn split_record(&self) -> Option<&HashMap<String, Extent>> {
        match self {
            Extent::Record(fields) => Some(fields),
            _ => None,
        }
    }

    /// Create a guard from parts (for function types: domain + codomain guards)
    pub fn create_guard_from_parts(&self, parts: Vec<Guard>) -> Guard {
        match self {
            Extent::Function { .. } => {
                if parts.len() == 2 {
                    Guard::from_function_parts(parts[0].clone(), parts[1].clone())
                } else {
                    Guard::Universal
                }
            }
            Extent::Record(_) => {
                // For records, parts should be a map of field names to guards
                // This is a simplified version - in practice we'd need proper mapping
                Guard::Universal
            }
            _ => {
                if parts.len() == 1 {
                    parts[0].clone()
                } else {
                    Guard::Universal
                }
            }
        }
    }
}

/// Base types in PCL
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BaseType {
    Int,
    String,
    Bool,
    Unit,
}

/// Values in PCL
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Int(i64),
    String(String),
    Bool(bool),
    Unit,
    /// A function value (collection of bindings)
    Function(Vec<FuncBinding>),
    /// A record value
    Record(HashMap<String, Value>),
}

/// A function binding represents a single input-output pair for a function
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncBinding {
    pub input: Value,
    pub output: Value,
}

/// A columnar value representation for vectorized execution.
/// Contains a batch of values with optional alignment information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ColumnValue {
    /// The batch of values
    pub values: Vec<Value>,
    /// Indices into the parent level's batch for alignment with outer scans.
    /// None if this is the outermost level or independent.
    pub parent_indices: Option<Vec<usize>>,
}

impl ColumnValue {
    /// Create a new ColumnValue with a single value (no parent alignment).
    pub fn single(value: Value) -> Self {
        ColumnValue {
            values: vec![value],
            parent_indices: None,
        }
    }

    /// Create a new ColumnValue from a vector of values (no parent alignment).
    pub fn from_values(values: Vec<Value>) -> Self {
        ColumnValue {
            values,
            parent_indices: None,
        }
    }

    /// Create a new ColumnValue with parent alignment indices.
    pub fn with_parent_indices(values: Vec<Value>, parent_indices: Vec<usize>) -> Self {
        ColumnValue {
            values,
            parent_indices: Some(parent_indices),
        }
    }

    /// Check if this column contains a single value.
    pub fn is_single(&self) -> bool {
        self.values.len() == 1
    }

    /// Get the single value if this column contains exactly one value.
    pub fn as_single(&self) -> Option<&Value> {
        if self.values.len() == 1 {
            Some(&self.values[0])
        } else {
            None
        }
    }

    /// Get the number of values in this column.
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Check if this column is empty.
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Expand this column's values using the given parent_indices.
    /// Used when an outer variable needs to be aligned with an inner scan.
    pub fn expand(&self, indices: &[usize]) -> ColumnValue {
        let expanded_values: Vec<Value> = indices.iter().map(|&i| self.values[i].clone()).collect();
        ColumnValue {
            values: expanded_values,
            // The expanded column inherits the indices as its own parent_indices
            parent_indices: Some(indices.to_vec()),
        }
    }
}

// ============================================================================
// Producer/Consumer Protocol
// ============================================================================

/// A Consumer receives notifications when data is ready.
/// The consumer is notified by the producer with a yield guard indicating
/// what region is ready and won't see further data.
pub trait Consumer {
    /// Notify the consumer that data is ready.
    /// The `yield_guard` specifies a region that is ready and will not see
    /// any further data.
    // TODO: should we take Guard by ref?
    fn notify(&mut self, yield_guard: Guard);
}

/// Blanket implementation: Rc<RefCell<C>> implements Consumer when C does.
impl<C: Consumer> Consumer for Rc<RefCell<C>> {
    fn notify(&mut self, yield_guard: Guard) {
        self.borrow_mut().notify(yield_guard)
    }
}

/// Blanket implementation: FnMut(Guard) implements Consumer.
/// This allows closures to be used as consumers.
impl<F> Consumer for F
where
    F: FnMut(Guard),
{
    fn notify(&mut self, yield_guard: Guard) {
        self(yield_guard)
    }
}

/// A Producer provides data and handles release requests.
/// The producer is created by an operator's `subscribe` method and allows
/// the consumer to retrieve data and release regions.
pub trait Producer {
    /// Get the data that is ready.
    /// Returns a columnar representation of the values in the ready region.
    /// The structure depends on the operator's type (records have fields,
    /// functions are collections, etc.).
    fn get(&mut self) -> ColumnValue;

    /// Release interest in a region.
    /// The `obsolete_guard` specifies a sub-region of the subscription that
    /// is no longer needed. Returns an expanded obsolete guard that may be
    /// larger if the producer has additional obsolescence information (e.g.,
    /// from variables with their own obsolete guards).
    fn release(&mut self, obsolete_guard: Guard) -> Guard;
}

/// Blanket implementation: Rc<RefCell<P>> implements Producer when P does.
impl<P: Producer> Producer for Rc<RefCell<P>> {
    fn get(&mut self) -> ColumnValue {
        self.borrow_mut().get()
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        self.borrow_mut().release(obsolete_guard)
    }
}

/// A dataflow operator that can be subscribed to.
/// Operators implement this trait to provide a subscription interface.
/// The `subscribe` method takes an intent guard (specifying what region the
/// consumer is interested in) and a consumer, and returns a producer that
/// allows the consumer to get data and release regions.
pub trait Operator {
    /// Get the extent (type) of this operator.
    fn extent(&self) -> &Extent;

    /// Subscribe to this operator with an intent guard and consumer.
    /// Returns a producer that allows the consumer to get data and release regions.
    ///
    /// # Arguments
    /// * `intent_guard` - The region of the operator's extent that the consumer
    ///   is interested in
    /// * `consumer` - The consumer that will receive notifications when data is ready
    ///
    /// # Arguments
    /// * `var_scope` - The variable scope for looking up variables
    ///
    /// # Returns
    /// A producer that provides access to the data and allows releasing regions
    fn subscribe(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>, // TODO: Should we make this a trait bound so we don't assume a Box pointer type?
        var_scope: Option<VarScope>,
    ) -> Box<dyn Producer>;
}

// ============================================================================
// Literal Operator
// ============================================================================

/// A literal operator represents a constant value.
/// According to the design: Subscribe calls Notify on the consumer immediately.
/// Notify calls Get. Get returns a constant. Release is a no-op.
pub struct Literal {
    value: Value,
    extent: Extent,
}

impl Literal {
    /// Create a new literal operator from a value.
    pub fn new(value: Value) -> Self {
        let extent = Self::extent_for_value(&value);
        Literal { value, extent }
    }

    /// Determine the extent for a given value.
    fn extent_for_value(value: &Value) -> Extent {
        match value {
            Value::Int(_) => Extent::Base(BaseType::Int),
            Value::String(_) => Extent::Base(BaseType::String),
            Value::Bool(_) => Extent::Base(BaseType::Bool),
            Value::Unit => Extent::Base(BaseType::Unit),
            Value::Function(bindings) => {
                // For a function literal, we need to infer the domain and codomain
                // from the bindings. For now, we'll use a simplified approach.
                // TODO: Properly infer function types from bindings
                if bindings.is_empty() {
                    Extent::function(Extent::Base(BaseType::Unit), Extent::Base(BaseType::Unit))
                } else {
                    // Infer from first binding as a placeholder
                    let domain = Self::extent_for_value(&bindings[0].input);
                    let codomain = Self::extent_for_value(&bindings[0].output);
                    Extent::function(domain, codomain)
                }
            }
            Value::Record(fields) => {
                let field_extents: HashMap<String, Extent> = fields
                    .iter()
                    .map(|(name, val)| (name.clone(), Self::extent_for_value(val)))
                    .collect();
                Extent::record(field_extents)
            }
        }
    }
}

impl Operator for Literal {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    fn subscribe(
        &mut self,
        _intent_guard: Guard,
        mut consumer: Box<dyn Consumer>,
        _var_scope: Option<VarScope>,
    ) -> Box<dyn Producer> {
        consumer.notify(Guard::universal());

        Box::new(LiteralProducer {
            value: self.value.clone(),
        })
    }
}

struct LiteralProducer {
    value: Value,
}

impl Producer for LiteralProducer {
    fn get(&mut self) -> ColumnValue {
        ColumnValue::single(self.value.clone())
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        // Release is a no-op for literals - just return the obsolete guard unchanged
        obsolete_guard
    }
}

// ============================================================================
// Variable System
// ============================================================================

use std::cell::RefCell;
use std::rc::Rc;

/// Variable scope for looking up variables.
/// Each scope contains exactly one variable (the lambda's bound variable).
/// Variables are looked up by name, searching up the parent chain if not found.
pub struct VarScope {
    /// Optional parent scope (for nested scopes)
    parent: Option<Box<VarScope>>,
    /// The variable name in this scope
    name: String,
    /// The variable subscription in this scope
    subscription: Rc<RefCell<VarSub>>,
}

impl VarScope {
    /// Create a new root scope with a single variable.
    pub fn new(name: String, subscription: Rc<RefCell<VarSub>>) -> Self {
        VarScope {
            parent: None,
            name,
            subscription,
        }
    }

    /// Create a child scope with a parent.
    pub fn child(parent: VarScope, name: String, subscription: Rc<RefCell<VarSub>>) -> Self {
        VarScope {
            parent: Some(Box::new(parent)),
            name,
            subscription,
        }
    }

    /// Look up a variable by name, searching up the parent chain.
    /// Returns (subscription, scan_chain) where scan_chain contains any scanning
    /// variables between the current scope and the found variable (for alignment).
    pub fn lookup_variable(
        &self,
        name: &str,
    ) -> Option<(Rc<RefCell<VarSub>>, Vec<Rc<RefCell<VarSub>>>)> {
        self.lookup_with_chain(name, Vec::new())
    }

    fn lookup_with_chain(
        &self,
        name: &str,
        mut chain: Vec<Rc<RefCell<VarSub>>>,
    ) -> Option<(Rc<RefCell<VarSub>>, Vec<Rc<RefCell<VarSub>>>)> {
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
    pub fn new(name: String, extent: Extent) -> Self {
        Var {
            name,
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
    /// All consumers that have subscribed to this variable
    consumers: Vec<Box<dyn Consumer>>,
    /// The stored release guard for use by variable references
    stored_release_guard: Guard,
}

impl VarSub {
    /// Create a new VarSub with the given source.
    fn new(source: VarSource) -> Self {
        VarSub {
            source,
            yield_guard: Guard::Empty,
            consumers: Vec::new(),
            stored_release_guard: Guard::Empty,
        }
    }

    /// Add a consumer to be notified when yield guards arrive.
    /// If there's already a yield guard (data is ready), notify the new consumer immediately.
    pub fn add_consumer(&mut self, mut consumer: Box<dyn Consumer>) {
        // If data is already ready, notify the new consumer immediately
        if !self.yield_guard.is_empty() {
            consumer.notify(self.yield_guard.clone());
        }
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
    fn get(&mut self) -> ColumnValue {
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
                match extent {
                    Extent::Base(BaseType::Int) => {
                        // Placeholder: return empty column for now
                        // Real implementation would scan the extent
                        ColumnValue::from_values(vec![])
                    }
                    _ => ColumnValue::from_values(vec![]),
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
    /// Notify this subscription of a yield guard (called by definition).
    fn notify(&mut self, yield_guard: Guard) {
        self.yield_guard = yield_guard.clone();

        // Forward to all consumers
        let yield_guard = self.get_yield_guard();
        for consumer in self.consumers.iter_mut() {
            consumer.notify(yield_guard.clone());
        }
    }
}

/// A VarRef operator represents a reference to a variable.
/// It holds the variable name and looks it up in the VarScope when subscribing.
pub struct VarRef {
    /// The name of the variable being referenced
    name: String,
    /// The extent (cached from the variable when found)
    extent: Extent,
}

impl VarRef {
    /// Create a new variable reference.
    pub fn new(name: String, extent: Extent) -> Self {
        VarRef { name, extent }
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
        var_scope: Option<VarScope>,
    ) -> Box<dyn Producer> {
        // Look up the variable in the scope
        let var_scope = var_scope.expect("VarRef requires a VarScope");
        let (variable_subscription, scan_chain) = var_scope
            .lookup_variable(&self.name)
            .expect(&format!("Variable '{}' not found in scope", self.name));

        // Create VarRefSub with the consumer and scan chain for alignment
        let ref_subscription = Rc::new(RefCell::new(VarRefSub {
            variable_subscription,
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

impl Consumer for VarRefSub {
    /// Notify this subscription of a yield guard from the variable.
    fn notify(&mut self, yield_guard: Guard) {
        let restricted_guard = yield_guard.intersect(self.intent_guard.clone());
        self.consumer.notify(restricted_guard);
    }
}

/// Compose parent indices: maps inner indices through outer indices.
/// For inner[i], result[i] = outer[inner[i]]
fn compose_indices(outer: &[usize], inner: &[usize]) -> Vec<usize> {
    inner.iter().map(|&i| outer[i]).collect()
}

impl Producer for VarRefSub {
    fn get(&mut self) -> ColumnValue {
        // Get data from variable subscription
        let column = self.variable_subscription.borrow_mut().get();

        // TODO: Filter data based on intent guard

        // If no scan chain, no alignment needed
        if self.scan_chain.is_empty() {
            return column;
        }

        // Compose parent_indices from innermost scan to outermost
        // The chain is ordered from innermost (first after current scope) to outermost (closest to variable)
        let mut composed_indices: Option<Vec<usize>> = None;
        for scan in self.scan_chain.iter().rev() {
            // Get this scan's parent_indices
            let scan_column = scan.borrow_mut().get();
            if let Some(parent_indices) = scan_column.parent_indices {
                composed_indices = Some(match composed_indices {
                    None => parent_indices,
                    Some(inner) => compose_indices(&parent_indices, &inner),
                });
            }
        }

        // Expand column using composed indices
        match composed_indices {
            Some(indices) => column.expand(&indices),
            None => column,
        }
    }

    fn release(&mut self, _obsolete_guard: Guard) -> Guard {
        // Return the stored release guard from the variable subscription
        self.variable_subscription
            .borrow()
            .get_stored_release_guard()
    }
}

// ============================================================================
// Lambda Operator
// ============================================================================

/// A Lambda operator represents a lambda expression.
/// It has a variable and a body, and manages the variable scope.
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
        var_scope: Option<VarScope>,
        binding: &mut dyn Operator,
    ) -> Box<dyn Producer> {
        self.subscribe_internal(intent_guard, consumer, var_scope, Some(binding))
    }

    /// Internal subscribe implementation that handles both bound and scanning modes.
    fn subscribe_internal(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>,
        var_scope: Option<VarScope>,
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
            VarScope::child(parent, self.variable.name.clone(), variable_subscription)
        } else {
            VarScope::new(self.variable.name.clone(), variable_subscription)
        };

        // Create closure for body notifications: updates body_yield_guard and checks if ready
        let lambda_producer_for_body = lambda_producer.clone();
        let body_consumer: Box<dyn Consumer> = Box::new(move |yield_guard: Guard| {
            let mut producer = lambda_producer_for_body.borrow_mut();
            producer.body_yield_guard = yield_guard;
            producer.check_and_notify();
        });

        // Subscribe to the body with the closure as consumer
        let body_producer = self
            .body
            .subscribe(codomain_guard, body_consumer, Some(new_scope));

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
        var_scope: Option<VarScope>,
    ) -> Box<dyn Producer> {
        // When subscribe is called without a binding, the variable is in scanning mode.
        // This happens when the lambda is used by an aggregation operator (e.g., sum).
        self.subscribe_internal(intent_guard, consumer, var_scope, None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    /// A test consumer that stores notifications in shared state.
    /// The notifications Vec is kept by the test, allowing access to notifications
    /// even after the consumer is moved into subscribe.
    /// Uses Rc<RefCell<>> for single-threaded, lock-free shared state.
    pub struct TestConsumer {
        notifications: Rc<RefCell<Vec<Guard>>>,
    }

    impl TestConsumer {
        /// Create a new TestConsumer and return both the consumer and the shared notifications Vec.
        /// The consumer can be moved into subscribe, while the notifications Vec allows
        /// reading notifications from outside.
        pub fn new() -> (Self, Rc<RefCell<Vec<Guard>>>) {
            let notifications = Rc::new(RefCell::new(Vec::new()));
            (
                TestConsumer {
                    notifications: notifications.clone(),
                },
                notifications,
            )
        }
    }

    impl Consumer for TestConsumer {
        fn notify(&mut self, yield_guard: Guard) {
            // Push the notification to the shared Vec
            self.notifications.borrow_mut().push(yield_guard);
        }
    }

    #[test]
    fn test_literal_int() {
        let mut literal = Literal::new(Value::Int(42));

        // Check extent
        assert_eq!(literal.extent(), &Extent::Base(BaseType::Int));

        // Create consumer with shared notifications Vec - keep the Vec reference
        let (consumer, notifications) = TestConsumer::new();
        let mut producer = literal.subscribe(Guard::universal(), Box::new(consumer), None);

        // The consumer should have been notified immediately
        // Now we can check the notification via the shared Vec
        let notifications_borrowed = notifications.borrow();
        assert_eq!(notifications_borrowed.len(), 1);
        assert_eq!(notifications_borrowed[0], Guard::universal());

        // Verify get returns the constant value (as a single-element column)
        let column = producer.get();
        assert_eq!(column.values.len(), 1);
        assert_eq!(column.values[0], Value::Int(42));
        assert!(column.parent_indices.is_none());

        // Verify release is a no-op
        let released = producer.release(Guard::universal());
        assert_eq!(released, Guard::universal());
    }

    #[test]
    fn test_literal_string() {
        let mut literal = Literal::new(Value::String("hello".to_string()));

        assert_eq!(literal.extent(), &Extent::Base(BaseType::String));

        let (consumer, notifications) = TestConsumer::new();
        let mut producer = literal.subscribe(Guard::universal(), Box::new(consumer), None);

        // Verify we received the notification
        let notifications_borrowed = notifications.borrow();
        assert_eq!(notifications_borrowed.len(), 1);
        assert_eq!(notifications_borrowed[0], Guard::universal());

        let column = producer.get();
        assert_eq!(column.values.len(), 1);
        assert_eq!(column.values[0], Value::String("hello".to_string()));
    }

    #[test]
    fn test_variable_proxy() {
        // Create variable and its reference
        let variable = Var::new("x".to_string(), Extent::Base(BaseType::Int));
        let mut var_ref = VarRef::new("x".to_string(), Extent::Base(BaseType::Int));

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
        let var_scope = VarScope::new("x".to_string(), var_subscription);

        // Subscribe and verify it works
        let (consumer, notifications) = TestConsumer::new();
        let mut producer =
            var_ref.subscribe(Guard::universal(), Box::new(consumer), Some(var_scope));

        // Verify notification was received (flows: Literal → VarSub → VarRefSub → consumer)
        let notifications_borrowed = notifications.borrow();
        assert_eq!(notifications_borrowed.len(), 1);
        assert_eq!(notifications_borrowed[0], Guard::universal());

        // Verify get returns the value (as a single-element column)
        let column = producer.get();
        assert_eq!(column.values.len(), 1);
        assert_eq!(column.values[0], Value::Int(42));

        // Verify release returns stored release guard (initially empty)
        let released = producer.release(Guard::universal());
        assert_eq!(released, Guard::Empty);
    }

    #[test]
    fn test_lambda_extent() {
        // Create a lambda: λ x . x (identity function)
        let variable = Var::new("x".to_string(), Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x".to_string(), Extent::Base(BaseType::Int)));
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
        let variable = Var::new("x".to_string(), Extent::Base(BaseType::Int));
        // Body just returns the variable
        let body = Box::new(VarRef::new("x".to_string(), Extent::Base(BaseType::Int)));
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
            notifications_borrowed.len() >= 1,
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
        let variable = Var::new("x".to_string(), Extent::Base(BaseType::Int));
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
            notifications_borrowed.len() >= 1,
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
        let variable = Var::new("x".to_string(), Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x".to_string(), Extent::Base(BaseType::Int)));
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
        let variable = Var::new("x".to_string(), Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x".to_string(), Extent::Base(BaseType::Int)));
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
            notifications_borrowed.len() >= 1,
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
        let variable = Var::new("x".to_string(), Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x".to_string(), Extent::Base(BaseType::Int)));
        let mut lambda = Lambda::new(variable, body);

        // Create a parent scope with a different variable "x" bound to 200
        let parent_variable = Var::new("x".to_string(), Extent::Base(BaseType::Int));
        // Create parent subscription and wire up binding properly
        let parent_subscription = parent_variable.create_subscription(VarSource::Uninitialized);
        let mut parent_literal = Literal::new(Value::Int(200));
        let parent_sub_consumer: Box<dyn Consumer> = Box::new(parent_subscription.clone());
        let parent_binding =
            parent_literal.subscribe(Guard::universal(), parent_sub_consumer, None);
        parent_subscription
            .borrow_mut()
            .set_source(VarSource::Bound(parent_binding));
        let parent_scope = VarScope::new("x".to_string(), parent_subscription);

        let mut binding_literal = Literal::new(Value::Int(100));

        // Subscribe to lambda with parent scope and binding operator
        // The lambda should create its own scope, so the body should reference
        // the lambda's variable (100), not the parent's (200)
        let (consumer, _) = TestConsumer::new();
        let mut producer = lambda.subscribe_with_binding(
            Guard::universal(),
            Box::new(consumer),
            Some(parent_scope),
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
        let variable = Var::new("x".to_string(), Extent::Base(BaseType::Int));
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
            notifications_borrowed.len() >= 1,
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

        let variable = Var::new("x".to_string(), Extent::Base(BaseType::Int));
        let body = Box::new(VarRef::new("x".to_string(), Extent::Base(BaseType::Int)));
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
