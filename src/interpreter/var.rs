//! Variable system: VarScope, VarSource, Var, VarProducer, VarRef, VarRefProducer.

use std::rc::Rc;
use std::{cell::RefCell, collections::HashMap};

use bit_set::BitSet;
use log::trace;

use crate::interpreter::{Correlations, Restriction};
/// A variable subscription paired with the chain of iteration-source variables between
use crate::{
    interpreter::DataSourceDomainExtentImpl,
    pretty_graph::{fmt_extent, InspectNode, VizOptions, MODE_ARGUMENT, MODE_ITERATION},
};

use super::{
    fmt_guard, ColumnValue, Consumer, Extent, GetResult, Guard, Operator, Producer, Scheduler,
};
/// A variable subscription paired with the chain of scanning variables between
/// the current scope and the found variable, used for alignment composition.
type VarWithIterationChain = (Rc<RefCell<VarProducer>>, Vec<Rc<RefCell<VarProducer>>>);

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
    subscription: Rc<RefCell<VarProducer>>,
}

impl VarScope {
    /// Create a new root scope with a single variable.
    pub fn new(name: &str, subscription: Rc<RefCell<VarProducer>>) -> Self {
        VarScope {
            parent: None,
            name: name.to_string(),
            subscription,
        }
    }

    /// Create a child scope with a parent.
    pub fn child(parent: Rc<VarScope>, name: &str, subscription: Rc<RefCell<VarProducer>>) -> Self {
        VarScope {
            parent: Some(parent),
            name: name.to_string(),
            subscription,
        }
    }

    pub fn new_with_optional_parent(
        parent: Option<Rc<VarScope>>,
        name: &str,
        subscription: Rc<RefCell<VarProducer>>,
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
        mut chain: Vec<Rc<RefCell<VarProducer>>>,
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
    /// VarProducer operations will panic if called while in this state.
    Uninitialized,
    /// Variable receives values from an argument producer (via Apply).
    /// The variable forwards values from this producer.
    Argument(Box<dyn Producer>),
    /// Variable iterates over its extent (for output or aggregation).
    /// The variable generates values by iterating over all values in its extent.
    /// Variable iterates over its extent (for output or aggregation).
    /// The variable generates values by iterating over all values in its extent.
    Iteration {
        extent: Extent,
        // TODO: correlations for join execution
    },
}

/// A Var operator represents a variable definition.
/// It holds the variable's name and extent, but NOT a static definition.
/// The variable's values are injected at run time either via application (argument source)
/// or direct iteration (iteration source).
#[derive(Debug, Clone)]
pub struct Var {
    /// The name of the variable
    pub name: String,
    /// The extent of this variable (may be restricted by predicates)
    extent: Extent,
    /// Whether this variable is responsible for setting up the producer for its restriction (if any)
    /// The producer needs to be set up in the narrowest scope that contains the restriction, which
    /// is information that is only available in the compiler. Thus, we record that info here.
    owns_restriction: bool,
}

impl Var {
    /// Create a new variable operator with the given name and extent.
    pub fn new(name: &str, extent: Extent) -> Self {
        Var {
            name: name.to_string(),
            extent,
            owns_restriction: false,
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

    /// Get the extent of this variable as a mutable ref.
    pub fn extent_mut(&mut self) -> &mut Extent {
        &mut self.extent
    }

    /// Create a VarProducer for this variable with the given source.
    ///
    /// The subscription starts with an empty yield guard. For `Argument` source, the
    /// binding operator will notify VarProducer when data is ready. For `Iteration` source,
    /// the scheduler will trigger a check for progress, which notifies when data is available.
    ///
    /// Consumers can be added later via `VarProducer::add_consumer()`.
    pub fn create_subscription(&self, source: VarSource) -> Rc<RefCell<VarProducer>> {
        Rc::new(RefCell::new(VarProducer::new(
            self.name.clone(),
            source,
            self.extent(),
        )))
    }

    pub fn owns_restriction(&self) -> bool {
        self.owns_restriction
    }

    pub fn set_owns_restriction(&mut self, owns_restriction: bool) {
        self.owns_restriction = owns_restriction;
    }
}

// Note: Var does not implement Operator because it cannot be subscribed to directly.
// Variables are always managed by their enclosing context (Lambda, Let, etc.) which
// creates the VarProducer with the appropriate VarSource (Argument or Iteration).

/// VarProducer implements both Producer and Consumer.
/// It stores the yield guard (monotonically growing) and forwards notifications to all consumers.
pub struct VarProducer {
    /// The variable name (for visualization)
    name: String,
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

impl std::fmt::Debug for VarProducer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VarProducer")
            .field("name", &self.name)
            .field("source", &self.source)
            .field("data_available", &self.data_available)
            .field(
                "consumers",
                &format_args!("<{} consumers>", self.consumers.len()),
            )
            .field("stored_release_guard", &self.stored_release_guard)
            .finish()
    }
}

impl VarProducer {
    /// Create a new VarProducer with the given source.
    fn new(name: String, source: VarSource, extent: &Extent) -> Self {
        VarProducer {
            name,
            source,
            extent: extent.clone(),
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
            consumer.notify();
        }
        debug_assert!(
            self.stored_release_guard.is_empty(),
            "add_consumer called after releases have occurred"
        );
        self.consumers.push(consumer);
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
            "VarProducer::set_source() called while source is not Uninitialized"
        );
        self.source = source;
    }

    fn check_for_notifications_by_extent(&mut self, extent: &Extent) {
        match extent {
            Extent::DataSourceDomain(extent_impl, ..) => {
                if extent_impl.borrow_mut().check_for_new_data() {
                    self.consumers.iter_mut().for_each(|c| c.notify());
                }
            }
            Extent::Record(fields) => {
                for field_extent in fields.values() {
                    self.check_for_notifications_by_extent(field_extent);
                }
            }
            Extent::Restricted { base, .. } => {
                self.check_for_notifications_by_extent(base);
            }
            // Nothing to do for other extents since they all complete from the start of the program
            _ => {}
        }
    }

    pub fn check_for_notification(&mut self) {
        let extent = match &self.source {
            VarSource::Iteration { extent, .. } => extent,
            _ => panic!(
                "Expected VarProducer with DataSource input, got {:?}",
                self.source
            ),
        }
        .clone();
        self.check_for_notifications_by_extent(&extent);
    }

    pub fn get_extent(&self) -> &Extent {
        &self.extent
    }
    /// Non-guard status parts for use in annotations and `summary_line`.
    fn non_guard_status_parts(&self) -> Vec<String> {
        let mode = if self.is_iteration() {
            MODE_ITERATION
        } else {
            MODE_ARGUMENT
        };
        let mut parts = vec![mode.to_string()];
        if self.data_available {
            parts.push("ready".to_string());
        }
        parts
    }

    /// One-line summary for use in VarRefPrducer's compact display.
    ///
    /// This is a text-only path; it embeds all status including the yield guard
    /// inline so the summary reads naturally in a single line.
    pub fn summary_line(&self, opts: &VizOptions) -> String {
        let mode = if self.is_iteration() {
            MODE_ITERATION
        } else {
            MODE_ARGUMENT
        };
        let mut parts = vec![mode.to_string()];
        if opts.show_guards {
            parts.push(format!(
                "release: {}",
                fmt_guard(&self.stored_release_guard)
            ));
        }
        if self.data_available {
            parts.push("ready".to_string());
        }
        parts.push(format!("{} consumers", self.consumers.len()));
        format!("VarProducer({}) [{}]", self.name, parts.join(", "))
    }
}

impl Producer for VarProducer {
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let non_guard_parts = self.non_guard_status_parts();
        let mut desc = InspectNode::new(format!("VarProducer({})", self.name))
            .annotate(format!("[{}]", non_guard_parts.join(", ")))
            .with_yield_guard(fmt_guard(&self.yield_guard));
        if opts.show_guards {
            desc = desc.with_obsolete_guard(fmt_guard(&self.stored_release_guard));
        }
        match &self.source {
            VarSource::Argument(producer) => {
                desc = desc.child("source", producer.inspect(opts));
            }
            VarSource::Iteration { .. } => {
                if let Extent::Restricted { restriction, .. } = &self.extent {
                    desc = desc.child("restriction", restriction.borrow().inspect(opts));
                }
            }
            VarSource::Uninitialized => {
                desc = desc.annotate("[uninitialized]".to_string());
            }
        }
        desc
    }
    fn get(&mut self) -> GetResult {
        let result = match &mut self.source {
            VarSource::Uninitialized => {
                panic!("VarProducer::get() called while source is Uninitialized")
            }
            VarSource::Argument(producer) => producer.get(),
            VarSource::Iteration { extent } => iterate_extent(extent, None),
        };
        self.yield_guard = result.yield_guard.clone();
        result
    }

    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        // Store the release guard for use by variable references
        self.store_release_guard(obsolete_guard.clone());
        // Forward release to source
        match &mut self.source {
            VarSource::Uninitialized => {
                panic!("VarProducer::release() called while source is Uninitialized")
            }
            VarSource::Argument(producer) => producer.release(obsolete_guard),
            VarSource::Iteration { extent, .. } => release_for_extent(extent, obsolete_guard),
        }
    }
}

/// Produce all values for the given extent, applying the outer filter if provided.
/// For now the filters are simple BitSets, but in the future they will be some more compressed structure.
fn iterate_extent(extent: &Extent, outer_filter: Option<&Correlations>) -> GetResult {
    match extent {
        Extent::UIntRange { start, end, .. } => iterate_uint_range(*start, *end, outer_filter),
        Extent::DataSourceDomain(source_impl) => {
            iterate_data_source_domain(source_impl, outer_filter)
        }
        Extent::Record(fields) => iterate_record(fields, outer_filter),
        Extent::Restricted { base, restriction } => {
            iterate_restricted_extent(base.as_ref(), restriction, outer_filter)
        }
        _ => panic!("Attempted to iterate on infinite Extent"),
    }
}

fn iterate_uint_range(start: usize, end: usize, outer_filter: Option<&Correlations>) -> GetResult {
    match outer_filter {
        Some(Correlations::Positional(restriction)) => {
            let filtered: Vec<usize> = (start..end)
                .enumerate()
                .filter(|(i, _)| restriction.contains(*i))
                .map(|(_, v)| v)
                .collect();
            GetResult {
                column_value: ColumnValue::from_uints(filtered),
                yield_guard: Guard::Universal,
            }
        }
        Some(Correlations::Tuples(..)) => panic!("Unexpected correlations"),
        None => GetResult {
            column_value: ColumnValue::from_uints((start..end).collect()),
            yield_guard: Guard::Universal,
        },
    }
}

fn iterate_data_source_domain(
    source_impl: &Rc<RefCell<dyn DataSourceDomainExtentImpl>>,
    outer_filter: Option<&Correlations>,
) -> GetResult {
    let values = source_impl.borrow_mut().get_elements();
    let yield_guard = source_impl.borrow().get_yield_guard();
    let n = values.len();
    let output = if let Some(Correlations::Positional(outer_filter)) = outer_filter {
        ColumnValue::from_values(
            (0..n)
                .filter(|i| outer_filter.contains(*i))
                .map(|i| values.index_at(i))
                .collect(),
            &source_impl.borrow().element_extent(),
        )
    } else {
        values
    };
    GetResult {
        column_value: output,
        yield_guard,
    }
}

fn iterate_record_positions(
    fields: &HashMap<String, Extent>,
    outer_filter: Option<&BitSet>,
) -> GetResult {
    let mut output_data: HashMap<String, GetResult> = fields
        .iter()
        .map(|(field, field_extent)| (field.clone(), iterate_extent(field_extent, None)))
        .collect();
    let yield_guard = Guard::Record(
        output_data
            .iter()
            .map(|(field, get_result)| (field.clone(), get_result.yield_guard.clone()))
            .collect(),
    );
    let data = output_data
        .drain()
        .map(|(field, get_result)| (field.clone(), get_result.column_value))
        .collect();
    GetResult {
        column_value: ColumnValue::cartesian_product_with_correlation(data, outer_filter),
        yield_guard,
    }
}

fn iterate_record(
    fields: &HashMap<String, Extent>,
    outer_filter: Option<&Correlations>,
) -> GetResult {
    match outer_filter {
        Some(Correlations::Positional(outer_filter_positions)) => {
            iterate_record_positions(fields, Some(outer_filter_positions))
        }
        Some(Correlations::Tuples(elements)) => {
            let mut v0 = Vec::new();
            let mut v1 = Vec::new();
            for e in elements.iter() {
                v0.push(e[1].clone());
                v1.push(e[0].clone());
            }
            GetResult {
                column_value: ColumnValue::Records(HashMap::from([
                    (
                        "_0".to_string(),
                        ColumnValue::from_values(v0, &fields["_0"]),
                    ),
                    (
                        "_1".to_string(),
                        ColumnValue::from_values(v1, &fields["_1"]),
                    ),
                ])),
                yield_guard: Guard::Empty,
            }
        }
        None => iterate_record_positions(fields, None),
    }
}

fn iterate_restricted_extent(
    base: &Extent,
    restriction: &Rc<RefCell<Restriction>>,
    outer_filter: Option<&Correlations>,
) -> GetResult {
    let mut filter = restriction.borrow_mut().get_correlations();
    if let Some(outer_filter) = outer_filter {
        filter.intersect_with(outer_filter);
    }
    iterate_extent(base, Some(&filter))
}

fn release_for_extent(extent: &mut Extent, obsolete_guard: Guard) -> Guard {
    match extent {
        Extent::DataSourceDomain(source_impl) => source_impl.borrow_mut().release(obsolete_guard),
        Extent::Record(fields) => {
            for (field, field_extent) in fields.iter_mut() {
                release_for_extent(
                    field_extent,
                    obsolete_guard
                        .get_record_field(field)
                        .unwrap_or_else(|| panic!("Not Record Guard: {obsolete_guard:?}")),
                );
            }
            obsolete_guard
        }
        Extent::Restricted { base, .. } => release_for_extent(base.as_mut(), obsolete_guard),
        _ => obsolete_guard,
    }
}

impl Consumer for VarProducer {
    fn notify(&mut self) {
        self.data_available = true;
        // Forward to all consumers
        for consumer in self.consumers.iter_mut() {
            consumer.notify();
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

    /// Create a new variable reference to the given Var.
    pub fn from_var(var: &Var) -> Self {
        Self::new(var.name(), var.extent().clone())
    }
}

impl Operator for VarRef {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::leaf(format!("VarRef({})", self.name));
        if opts.show_extents {
            desc = desc.annotate(format!(": {}", fmt_extent(&self.extent)));
        }
        desc
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

        // Create VarRefProducer with the consumer and iteration chain for alignment
        let ref_subscription = Rc::new(RefCell::new(VarRefProducer {
            var_name: self.name.clone(),
            variable_subscription: variable_subscription.clone(),
            iteration_chain,
            intent_guard,
            consumer,
        }));

        // Add the VarRefProducer as the consumer of the variable subscription
        let ref_subscription_consumer: Box<dyn Consumer> = Box::new(ref_subscription.clone());
        variable_subscription
            .borrow_mut()
            .add_consumer(ref_subscription_consumer);

        Box::new(ref_subscription) // As a producer.
    }
}

/// VarRefProducer implements both Producer and Consumer.
/// As a Consumer: it receives notifications from VarProducer, intersects
/// the yield guard with its intent guard, and forwards to the actual consumer.
/// As a Producer: it provides access to data and handles release requests.
struct VarRefProducer {
    /// The variable name (for visualization)
    var_name: String,
    /// Reference to the VarProducer
    variable_subscription: Rc<RefCell<VarProducer>>,
    /// Chain of iteration-source variables between current scope and referenced variable (for alignment)
    iteration_chain: Vec<Rc<RefCell<VarProducer>>>,
    /// The intent guard for this subscription
    intent_guard: Guard,
    /// The consumer of the variable ref that will receive filtered notifications
    consumer: Box<dyn Consumer>,
}

impl std::fmt::Debug for VarRefProducer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VarRefProducer")
            .field("var_name", &self.var_name)
            .field("variable_subscription", &self.variable_subscription)
            .field("iteration_chain", &self.iteration_chain)
            .field("intent_guard", &self.intent_guard)
            .field("consumer", &format_args!("<consumer>"))
            .finish()
    }
}

impl Consumer for VarRefProducer {
    fn notify(&mut self) {
        self.consumer.notify();
    }
}

impl Producer for VarRefProducer {
    // TODO: Make node collapsed by default so it's not confusing to see the same VarProducer
    // in multiple places in the tree. Maybe draw an arrow to the VarProducer, or color coordinate them?
    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::new(format!("VarRefProducer({})", self.var_name));
        if opts.show_guards {
            desc = desc.with_intent_guard(fmt_guard(&self.intent_guard));
        }
        if !self.iteration_chain.is_empty() {
            let names: Vec<String> = self
                .iteration_chain
                .iter()
                .filter_map(|s: &Rc<RefCell<VarProducer>>| {
                    s.try_borrow().ok().map(|b| b.name.clone())
                })
                .collect();
            desc = desc.annotate(format!(
                "[iteration_chain({}): {}]",
                self.iteration_chain.len(),
                names.join(" → ")
            ));
        }
        // Show a one-line summary reference to the VarProducer rather than recursing
        // into its full subtree, because VarProducer appears elsewhere in the graph
        // (e.g., as a child of LambdaProducer). Expanding it here would duplicate
        // entire subtrees in what is actually a DAG, not a tree.
        match self.variable_subscription.try_borrow() {
            Ok(var_sub) => {
                let summary = var_sub.summary_line(opts);
                desc = desc.child("", InspectNode::leaf(format!("→ {}", summary)));
            }
            Err(_) => {
                desc = desc.child("", InspectNode::leaf("→ VarProducer(<locked>)".to_string()));
            }
        }
        desc
    }

    fn get(&mut self) -> GetResult {
        // Get data from variable subscription
        let var_result = self.variable_subscription.borrow_mut().get();

        // TODO: Filter data based on intent guard

        trace!(
            "VarRefProducer for '{}' returning: {:?}",
            self.var_name,
            var_result.column_value
        );

        var_result
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
    use test_log::test;

    #[test]
    fn test_variable_proxy() {
        // Create variable and its reference
        let variable = Var::new("x", Extent::Base(BaseType::Int));
        let mut var_ref = VarRef::new("x", Extent::Base(BaseType::Int));

        assert_eq!(var_ref.extent(), &Extent::Base(BaseType::Int));

        // Create VarProducer in Uninitialized state first
        let var_subscription = variable.create_subscription(VarSource::Uninitialized);

        // Subscribe to the binding literal with VarProducer as the consumer
        // This ensures VarProducer receives notifications
        let mut binding_literal = Literal::new(Value::Int(42));
        let var_sub_consumer: Box<dyn Consumer> = Box::new(var_subscription.clone());
        let binding_producer = binding_literal.subscribe(
            Guard::universal(),
            var_sub_consumer,
            None,
            &mut Scheduler::new(),
        );

        // Now set VarProducer's source to `Argument` with the producer
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

        // Verify notification was received (flows: Literal → VarProducer → VarRefProducer → consumer)
        assert_eq!(*notifications.borrow(), 1);

        // Verify get returns the value (as a single-element column)
        let result = producer.get();
        assert_eq!(result.column_value.as_single().unwrap(), Value::Int(42));

        // Verify release returns stored release guard (initially empty)
        let released = producer.release(Guard::universal());
        assert_eq!(released, Guard::Empty);
    }
}
