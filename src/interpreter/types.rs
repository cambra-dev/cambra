//! Core types for the CCL interpreter: Guard, Extent, BaseType, Value, FuncBinding, ColumnValue.

use std::{cell::RefCell, cmp::Ordering, collections::HashMap, hash::Hash, rc::Rc};

use bit_set::BitSet;
use bit_vec::BitVec;
use log::trace;

use crate::interpreter::{ComputeRestriction, Operator, Producer, Scheduler, VarScope};

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
    /// A guard representing disequality: variable != value
    Disequality(Value),
    /// A guard representing an upper bound: variable <= value
    LessThanOrEq(Value),
    /// A conjunction of guards (all must be satisfied)
    And(Vec<Guard>),
    /// A disjunction of guards (at least one must be satisfied)
    Or(Vec<Guard>),
    /// A guard for a function type, denoting a subset of functions of that type.
    /// A function is in this guard iff, for all arguments in the domain guard,
    /// it maps to values in the codomain guard.
    Function {
        domain: Box<Guard>,
        codomain: Box<Guard>,
    },
    /// A guard for a function type that only describes the domain of the function
    Domain(Box<Guard>),
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
        match self {
            Guard::Universal => true,
            Guard::Domain(domain) => domain.is_universal(),
            Guard::Or(guards) => guards.iter().any(Guard::is_universal),
            Guard::And(guards) => guards.iter().all(Guard::is_universal),
            Guard::Record(guards) => guards.values().all(Guard::is_universal),
            _ => false,
        }
    }

    /// Returns Universal if this guard is universal, or else returns Empty
    pub fn to_universal_or_empty(&self) -> Guard {
        if self.is_universal() {
            Guard::Universal
        } else {
            Guard::Empty
        }
    }

    /// Intersect two guards (conjunction)
    pub fn intersect(self, other: Guard) -> Guard {
        match (self, other) {
            (Guard::Empty, _) | (_, Guard::Empty) => Guard::Empty,
            (g1, g2) if g2.is_empty() || g1.is_empty() => Guard::Empty,
            (Guard::Universal, g) | (g, Guard::Universal) => g,
            (g1, g2) if g2.is_universal() => g1,
            (g1, g2) if g1.is_universal() => g2,
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
            (g1, g2) if g2.is_empty() => g1,
            (g1, g2) if g1.is_empty() => g2,
            (Guard::Universal, _) | (_, Guard::Universal) => Guard::Universal,
            (g1, g2) if g2.is_universal() || g1.is_universal() => Guard::Universal,
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
            Guard::Or(guards) => {
                let mut domain = Guard::Empty;
                let mut codomain = Guard::Empty;
                for g in guards.iter() {
                    let (d, c) = g
                        .split_function()
                        .unwrap_or_else(|| panic!("Expected Function guard, got {g:?}"));
                    domain = domain.union(d);
                    codomain = codomain.union(c);
                }
                Some((domain, codomain))
            }
            Guard::And(guards) => {
                let mut domain = Guard::Empty;
                let mut codomain = Guard::Empty;
                for g in guards.iter() {
                    let (d, c) = g
                        .split_function()
                        .unwrap_or_else(|| panic!("Expected Function guard, got {g:?}"));
                    domain = domain.intersect(d);
                    codomain = codomain.intersect(c);
                }
                Some((domain, codomain))
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

    pub fn get_record_attribute(&self, attr: &str) -> Option<Guard> {
        match self {
            Guard::Record(fields) => fields.get(attr).cloned(),
            g if g.is_universal() => Some(Guard::Universal),
            g if g.is_empty() => Some(Guard::Empty),
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
#[derive(Clone)]
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
    // Right-open range of indices: [start, end)
    UIntRange {
        start: usize,
        end: usize,
    },
    DataSourceDomain(Rc<RefCell<dyn DataSourceDomainExtentImpl>>),
    /// A restricted extent: wraps another extent with a restriction predicate.
    Restricted {
        base: Box<Extent>,
        restriction: Rc<RefCell<Restriction>>,
    },
}

impl PartialEq for Extent {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Extent::Base(t1), Extent::Base(t2)) => t1 == t2,
            (
                Extent::Function {
                    domain: d1,
                    codomain: c1,
                },
                Extent::Function {
                    domain: d2,
                    codomain: c2,
                },
            ) => d1 == d2 && c1 == c2,
            (Extent::Record(a1), Extent::Record(a2)) => a1 == a2,
            (
                Extent::Restricted {
                    base: b1,
                    restriction: r1,
                },
                Extent::Restricted {
                    base: b2,
                    restriction: r2,
                },
            ) => b1 == b2 && Rc::ptr_eq(r1, r2),
            // Union equality is order-sensitive (structural).
            (Extent::Union(u1), Extent::Union(u2)) => u1 == u2,
            (
                Extent::UIntRange { start: s1, end: e1 },
                Extent::UIntRange { start: s2, end: e2 },
            ) => s1 == s2 && e1 == e2,
            (Extent::DataSourceDomain(d1), Extent::DataSourceDomain(d2)) => {
                d1.borrow().get_id() == d2.borrow().get_id()
            }
            _ => false,
        }
    }
}

impl Eq for Extent {}

pub struct NotifyOrSubscribeResult {
    pub notify: bool,
    pub subscribe: bool,
}

impl Extent {
    /// When subscribing to this extent as an iteration, returns whether to immediately
    /// notify true and whether to add the iterating variable to the scheduler.
    pub fn subscribe_to_iteration_action(&self) -> NotifyOrSubscribeResult {
        match self {
            // DataSource extents need to be registered so that the scheduling loop can
            // poll them for notifications
            Extent::DataSourceDomain(..) => NotifyOrSubscribeResult {
                notify: false,
                subscribe: true,
            },
            // Literal range extents are fully ready immediately
            Extent::UIntRange { .. } => NotifyOrSubscribeResult {
                notify: true,
                subscribe: false,
            },
            // Record extents are immediately ready if all attributes are ready,
            // otherwise we register with the scheduler.
            Extent::Record(attributes) => attributes
                .values()
                .map(|extent| extent.subscribe_to_iteration_action())
                .fold(
                    NotifyOrSubscribeResult {
                        notify: true,
                        subscribe: false,
                    },
                    |acc, value| NotifyOrSubscribeResult {
                        notify: acc.notify && value.notify,
                        subscribe: acc.subscribe || value.subscribe,
                    },
                ),
            // Restricted extents behave like their base record, but also set up the
            // restriction producer so it can compute correlation vectors at runtime.
            Extent::Restricted { base, .. } => base.subscribe_to_iteration_action(),
            // Other Extents cannot be iterated, so nothing to do
            _ => NotifyOrSubscribeResult {
                notify: false,
                subscribe: false,
            },
        }
    }

    /// Determine the extent for a given value.
    pub fn for_value(value: &Value) -> Extent {
        match value {
            Value::Int(_) => Extent::Base(BaseType::Int),
            Value::UInt(_) => Extent::Base(BaseType::UInt),
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
                    let domain = Self::for_value(&bindings[0].input);
                    let codomain = Self::for_value(&bindings[0].output);
                    Extent::function(domain, codomain)
                }
            }
            Value::Record(fields) => {
                let field_extents: HashMap<String, Extent> = fields
                    .iter()
                    .map(|(name, val)| (name.clone(), Self::for_value(val)))
                    .collect();
                Extent::record(field_extents)
            }
        }
    }
}

pub struct Restriction {
    compute_op: Option<Box<ComputeRestriction>>,
    compute_producer: Option<Box<dyn Producer>>,
}

impl Default for Restriction {
    fn default() -> Self {
        Self::new()
    }
}

impl Restriction {
    pub fn new() -> Self {
        Self {
            compute_op: None,
            compute_producer: None,
        }
    }

    pub fn set_compute_op(&mut self, compute_op: Box<ComputeRestriction>) {
        self.compute_op = Some(compute_op);
    }

    pub fn set_up_producer(
        &mut self,
        intent_guard: Guard,
        var_scope: Option<Rc<VarScope>>,
        scheduler: &mut Scheduler,
    ) {
        if self.compute_producer.is_none() {
            if let Some(op) = &mut self.compute_op {
                self.compute_producer =
                    Some(op.subscribe(intent_guard, Box::new(|_| {}), var_scope, scheduler));
            } else {
                panic!("Missing compute_op in Restriction");
            }
        }
    }

    pub fn get_correlation_vector(&mut self) -> BitVec {
        let data = self.compute_producer.as_mut().unwrap().get();
        match data.column_value.data {
            ColumnData::FunctionBindings { outputs, .. } => match *outputs {
                ColumnData::Bools(bools) => {
                    trace!("Got restriction vector {}", bools);
                    bools
                }
                _ => panic!("Expected Bools from compute_producer outputs"),
            },
            _ => panic!("Expected FunctionBindings from compute_producer"),
        }
    }
}

/// The Extent of the domain of a Data Source
pub trait DataSourceDomainExtentImpl {
    fn get_id(&self) -> &str;
    fn check_for_new_data(&mut self) -> bool;
    fn get_yield_guard(&self) -> Guard;
    fn get_elements(&self) -> ColumnData;
    /// Returns the [`Extent`] of each individual domain element.
    /// Used to construct a typed empty [`ColumnData`] when the domain is empty.
    fn element_extent(&self) -> Extent;
    fn release(&mut self, obsolete_guard: Guard) -> Guard;
}

impl PartialEq for dyn DataSourceDomainExtentImpl {
    fn eq(&self, other: &Self) -> bool {
        self.get_id() == other.get_id()
    }
}
impl Eq for dyn DataSourceDomainExtentImpl {}

impl std::fmt::Debug for Extent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Extent::Base(base) => write!(f, "{base:?}"),
            Extent::Function { domain, codomain } => write!(f, "({domain:?} -> {codomain:?})"),
            Extent::Record(attributes) => {
                let field_strs: Vec<String> = attributes
                    .iter()
                    .map(|(name, extent)| format!("{name}: {extent:?}"))
                    .collect();
                write!(f, "{{{}}}", field_strs.join(", "))
            }
            Extent::Union(extents) => {
                let extent_strs: Vec<String> = extents.iter().map(|e| format!("{e:?}")).collect();
                write!(f, "({})", extent_strs.join(" | "))
            }
            Extent::UIntRange { start, end } => write!(f, "[{start}, {end})"),
            Extent::DataSourceDomain(_) => write!(f, "DataSource"),
            Extent::Restricted { base, .. } => write!(f, "Restricted({base:?})"),
        }
    }
}

impl Extent {
    /// Create a function extent from domain and codomain
    pub fn function(domain: Extent, codomain: Extent) -> Self {
        Extent::Function {
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// Create a record extent from attribute extents
    pub fn record(attributes: HashMap<String, Extent>) -> Self {
        Extent::Record(attributes)
    }

    /// Create a restricted record extent: a [`Restricted`] wrapping a [`Record`].
    pub fn restricted_record(attributes: HashMap<String, Extent>) -> Self {
        Extent::restricted(Extent::Record(attributes))
    }

    /// Wrap any extent in a [`Restricted`] with a fresh [`Restriction`].
    pub fn restricted(base: Extent) -> Self {
        Extent::Restricted {
            base: Box::new(base),
            restriction: Rc::new(RefCell::new(Restriction::new())),
        }
    }

    /// Return the restriction handle if this is a [`Restricted`] extent.
    pub fn restriction(&mut self) -> Option<Rc<RefCell<Restriction>>> {
        match self {
            Extent::Restricted { restriction, .. } => Some(restriction.clone()),
            _ => None,
        }
    }

    /// Return the attribute map if this extent is a [`Record`], or a [`Restricted`] wrapping one.
    pub fn record_attributes(&self) -> Option<&HashMap<String, Extent>> {
        match self {
            Extent::Record(attributes) => Some(attributes),
            Extent::Restricted { base, .. } => base.record_attributes(),
            _ => None,
        }
    }

    /// Split a function extent into domain and codomain
    pub fn split_function(&self) -> Option<(&Extent, &Extent)> {
        match self {
            Extent::Function { domain, codomain } => Some((domain, codomain)),
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
            Extent::Record(..) => {
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

/// Base types in CCL
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BaseType {
    Int,
    UInt,
    String,
    Bool,
    Unit,
}

/// Values in CCL
#[derive(Clone, PartialEq, Eq)]
pub enum Value {
    Int(i64),
    UInt(usize),
    String(String),
    Bool(bool),
    Unit,
    /// A function value (collection of bindings)
    Function(Vec<FuncBinding>),
    /// A record value
    Record(HashMap<String, Value>),
}

impl Hash for Value {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Value::Int(i) => i.hash(state),
            Value::UInt(i) => i.hash(state),
            Value::String(s) => s.hash(state),
            Value::Bool(b) => b.hash(state),
            Value::Unit => {}
            Value::Function(bindings) => bindings.hash(state),
            Value::Record(fields) => {
                fields.len().hash(state);
                let mut entries: Vec<_> = fields.iter().collect();
                entries.sort_by_key(|(k, _)| *k);
                for (k, v) in entries {
                    k.hash(state);
                    v.hash(state);
                }
            }
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self {
            Value::Int(i) => {
                if let Value::Int(o) = other {
                    i.partial_cmp(o)
                } else {
                    None
                }
            }
            Value::UInt(i) => {
                if let Value::UInt(o) = other {
                    i.partial_cmp(o)
                } else {
                    None
                }
            }
            Value::String(s) => {
                if let Value::String(o) = other {
                    s.partial_cmp(o)
                } else {
                    None
                }
            }
            Value::Bool(b) => {
                if let Value::Bool(o) = other {
                    b.partial_cmp(o)
                } else {
                    None
                }
            }
            Value::Unit => {
                if let Value::Unit = other {
                    Some(Ordering::Equal)
                } else {
                    None
                }
            }
            // Order records lexicographically if they have the same schema.
            Value::Record(attrs) => {
                if let Value::Record(o_attrs) = other {
                    if attrs.keys().collect::<std::collections::HashSet<_>>()
                        != o_attrs.keys().collect::<std::collections::HashSet<_>>()
                    {
                        return None; // Records with different keys are not comparable
                    }
                    let mut entries: Vec<_> = attrs.iter().collect();
                    let mut o_entries: Vec<_> = o_attrs.iter().collect();
                    entries.sort_by_key(|(k, _)| *k);
                    o_entries.sort_by_key(|(k, _)| *k);
                    entries.partial_cmp(&o_entries)
                } else {
                    None
                }
            }
            _ => todo!("Ordering not implemented yet: {self:?}"),
        }
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{i}"),
            Value::UInt(i) => write!(f, "u{i}"),
            Value::String(s) => write!(f, "\"{s}\""),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Unit => write!(f, "()"),
            Value::Function(bindings) => {
                let binding_strs: Vec<String> = bindings
                    .iter()
                    .map(|b| format!("{:?} -> {:?}", b.input, b.output))
                    .collect();
                write!(f, "Function [ {} ]", binding_strs.join(", "))
            }
            Value::Record(fields) => {
                let field_strs: Vec<String> = fields
                    .iter()
                    .map(|(name, val)| format!("{name}: {val:?}"))
                    .collect();
                write!(f, "{{{}}}", field_strs.join(", "))
            }
        }
    }
}

impl Value {
    pub fn as_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            _ => panic!("Not bool: {self:?}"),
        }
    }

    pub fn as_int(&self) -> i64 {
        match self {
            Value::Int(i) => *i,
            _ => panic!("Not int: {self:?}"),
        }
    }

    pub fn as_uint(&self) -> usize {
        match self {
            Value::UInt(i) => *i,
            _ => panic!("Not uint: {self:?}"),
        }
    }

    pub fn as_string(&self) -> &str {
        match self {
            Value::String(s) => s,
            _ => panic!("Not string: {self:?}"),
        }
    }
}

/// A function binding represents a single input-output pair for a function
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncBinding {
    pub input: Value,
    pub output: Value,
}

/// Notification from a producer to a consumer, indicating the availability of new data,
/// or progress in the absence of data.
#[derive(Debug, Clone)]
pub enum Notification {
    /// A region has completed with no new data to retrieve.
    /// The consumer should NOT call get() in response to this.
    Yield(Guard),
    /// New data is available. The consumer should call get() to retrieve it.
    NewData,
}

/// Result of calling get() on a producer.
///
/// Conceptually a snapshot of a producer's current state — data and yield guard
/// are returned together to guarantee they are synchronized.
#[derive(Debug)]
pub struct GetResult {
    pub column_value: ColumnValue,
    /// The yield guard covering all data retrieved so far, including the data in this result.
    /// Monotonically growing across successive get() calls.
    pub yield_guard: Guard,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParentIndices {
    Scalar,             // single value that broadcasts over any batch size
    TopLevelVector,     // top-level batch — no outer scan
    Parent(Vec<usize>), // each element maps to a row in the parent batch
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ColumnData {
    Units(usize),
    Ints(Vec<i64>),
    UInts(Vec<usize>),
    Strings(Vec<String>),
    Bools(BitVec),
    Variants(Vec<Value>),
    FunctionBindings {
        inputs: Box<ColumnData>,
        outputs: Box<ColumnData>,
    },
    Records(HashMap<String, ColumnData>),
}

impl ColumnData {
    pub fn function_bindings(inputs: ColumnData, outputs: ColumnData) -> ColumnData {
        Self::FunctionBindings {
            inputs: Box::new(inputs),
            outputs: Box::new(outputs),
        }
    }

    /// Get a value at a specific index.
    pub fn index_at(&self, i: usize) -> Value {
        match self {
            ColumnData::Units(_) => Value::Unit,
            ColumnData::Bools(v) => Value::Bool(v[i]),
            ColumnData::Ints(v) => Value::Int(v[i]),
            ColumnData::UInts(v) => Value::UInt(v[i]),
            ColumnData::Strings(v) => Value::String(v[i].clone()),
            ColumnData::Variants(v) => v[i].clone(),
            ColumnData::FunctionBindings { inputs, outputs } => {
                Value::Function(vec![FuncBinding {
                    input: inputs.index_at(i),
                    output: outputs.index_at(i),
                }])
            }
            ColumnData::Records(r) => {
                Value::Record(r.iter().map(|(k, v)| (k.clone(), v.index_at(i))).collect())
            }
        }
    }

    /// Repeat a single-element ColumnData to the given length.
    pub fn repeat(&self, n: usize) -> ColumnData {
        assert_eq!(self.len(), 1, "repeat requires single-element ColumnData");
        match self {
            ColumnData::Units(_) => ColumnData::Units(n),
            ColumnData::Bools(v) => ColumnData::Bools(BitVec::from_elem(n, v[0])),
            ColumnData::Ints(v) => ColumnData::Ints(vec![v[0]; n]),
            ColumnData::UInts(v) => ColumnData::UInts(vec![v[0]; n]),
            ColumnData::Strings(v) => ColumnData::Strings(vec![v[0].clone(); n]),
            ColumnData::Variants(v) => ColumnData::Variants(vec![v[0].clone(); n]),
            _ => panic!("Cannot repeat composite ColumnData"),
        }
    }

    /// Convert a Vec<Value> into typed ColumnData.
    pub fn from_values(values: Vec<Value>, extent: &Extent) -> ColumnData {
        match extent {
            Extent::Base(BaseType::Unit) => ColumnData::Units(values.len()),
            Extent::Base(BaseType::Bool) => {
                ColumnData::Bools(values.iter().map(Value::as_bool).collect())
            }
            Extent::Base(BaseType::Int) => {
                ColumnData::Ints(values.iter().map(Value::as_int).collect())
            }
            Extent::Base(BaseType::UInt) => {
                ColumnData::UInts(values.iter().map(Value::as_uint).collect())
            }
            Extent::Base(BaseType::String) => {
                ColumnData::Strings(values.iter().map(|v| v.as_string().to_string()).collect())
            }
            Extent::Record(m) => {
                // Pivot the list of Records into a Record of ColumnDatas
                let keys: Vec<String> = m.keys().cloned().collect();
                let fields = keys
                    .into_iter()
                    .map(|key| {
                        let field_values = values
                            .iter()
                            .map(|v| match v {
                                Value::Record(r) => r[&key].clone(),
                                _ => panic!("Expected Record in from_values, got {v:?}"),
                            })
                            .collect();
                        (
                            key.clone(),
                            ColumnData::from_values(
                                field_values,
                                extent
                                    .record_attributes()
                                    .and_then(|attrs| attrs.get(&key))
                                    .unwrap_or_else(|| {
                                        panic!("Record extent missing attribute '{key}'")
                                    }),
                            ),
                        )
                    })
                    .collect();
                ColumnData::Records(fields)
            }
            _ => ColumnData::Variants(values),
        }
    }

    /// Sort FunctionBindings by their input values.
    pub fn sort_by_inputs(&self) -> ColumnData {
        match self {
            ColumnData::FunctionBindings { inputs, outputs } => {
                let n = inputs.len();
                let mut indices: Vec<usize> = (0..n).collect();
                indices.sort_by(|&a, &b| {
                    inputs
                        .index_at(a)
                        .partial_cmp(&inputs.index_at(b))
                        .expect("Cannot compare inputs")
                });
                ColumnData::function_bindings(
                    inputs.select_indices(&indices),
                    outputs.select_indices(&indices),
                )
            }
            other => other.clone(),
        }
    }

    /// Select elements at the given indices.
    pub fn select_indices(&self, indices: &[usize]) -> ColumnData {
        match self {
            ColumnData::Units(_) => ColumnData::Units(indices.len()),
            ColumnData::Bools(v) => ColumnData::Bools(indices.iter().map(|&i| v[i]).collect()),
            ColumnData::Ints(v) => ColumnData::Ints(indices.iter().map(|&i| v[i]).collect()),
            ColumnData::UInts(v) => ColumnData::UInts(indices.iter().map(|&i| v[i]).collect()),
            ColumnData::Strings(v) => {
                ColumnData::Strings(indices.iter().map(|&i| v[i].clone()).collect())
            }
            ColumnData::Variants(v) => {
                ColumnData::Variants(indices.iter().map(|&i| v[i].clone()).collect())
            }
            ColumnData::FunctionBindings { inputs, outputs } => ColumnData::function_bindings(
                inputs.select_indices(indices),
                outputs.select_indices(indices),
            ),
            ColumnData::Records(r) => ColumnData::Records(
                r.iter()
                    .map(|(k, v)| (k.clone(), v.select_indices(indices)))
                    .collect(),
            ),
        }
    }

    pub fn len(&self) -> usize {
        match &self {
            ColumnData::Units(len) => *len,
            ColumnData::Bools(v) => v.len(),
            ColumnData::Ints(v) => v.len(),
            ColumnData::UInts(v) => v.len(),
            ColumnData::Strings(v) => v.len(),
            ColumnData::Variants(v) => v.len(),
            ColumnData::Records(m) => m.values().next().expect("Empty Record").len(),
            ColumnData::FunctionBindings { inputs, .. } => inputs.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the single value if this column contains exactly one value.
    pub fn as_single(&self) -> Option<Value> {
        if self.len() == 1 {
            match self {
                ColumnData::Units(len) => {
                    if *len == 1 {
                        Some(Value::Unit)
                    } else {
                        None
                    }
                }
                ColumnData::Bools(v) => Some(Value::Bool(v[0])),
                ColumnData::Ints(v) => Some(Value::Int(v[0])),
                ColumnData::UInts(v) => Some(Value::UInt(v[0])),
                ColumnData::Strings(v) => Some(Value::String(v[0].clone())),
                ColumnData::Variants(v) => Some(v[0].clone()),
                ColumnData::FunctionBindings { inputs, outputs } => {
                    Some(Value::Function(vec![FuncBinding {
                        input: inputs.as_single().expect("Not single").clone(),
                        output: outputs.as_single().expect("Not single").clone(),
                    }]))
                }
                ColumnData::Records(r) => Some(Value::Record(
                    r.iter()
                        .map(|e| (e.0.clone(), e.1.as_single().expect("Not single").clone()))
                        .collect(),
                )),
            }
        } else {
            None
        }
    }

    /// Compute the cartesian product of a map of named column datas.
    ///
    /// Returns a [`ColumnData::Records`] where each field is expanded so that the fields
    /// together enumerate every combination of rows across all input columns. The total
    /// row count is the product of all input column lengths.
    ///
    /// # Example
    /// Given `{"a": [1, 2], "b": [3, 4]}`, returns
    /// `Records {"a": [1, 1, 2, 2], "b": [3, 4, 3, 4]}`.
    pub fn cartesian_product_with_correlation(
        data: HashMap<String, ColumnData>,
        correlations: &Option<BitSet>,
    ) -> ColumnData {
        if data.is_empty() {
            return ColumnData::Records(HashMap::new());
        }
        // Sort keys for a deterministic column order when computing strides.
        let mut keys: Vec<String> = data.keys().cloned().collect();
        keys.sort();
        let lengths: Vec<usize> = keys.iter().map(|k| data[k].len()).collect();
        let total: usize = lengths.iter().product();
        let expanded = keys
            .iter()
            .enumerate()
            .map(|(j, key)| {
                // stride: how many output rows share the same index into this column
                // before it advances — the product of all subsequent column lengths.
                let stride: usize = lengths[j + 1..].iter().product();
                let indices: Vec<usize> = if let Some(corr) = correlations {
                    // If correlations are provided, filter the range to only include rows that are correlated.
                    (0..total)
                        .filter(|i| corr.contains(*i))
                        .map(|i| (i / stride) % lengths[j])
                        .collect()
                } else {
                    (0..total).map(|i| (i / stride) % lengths[j]).collect()
                };
                (key.clone(), data[key].select_indices(&indices))
            })
            .collect();
        ColumnData::Records(expanded)
    }

    /// Construct a ColumnData containing the given string values.
    pub fn strings(values: &[&str]) -> ColumnData {
        ColumnData::Strings(values.iter().map(|s| s.to_string()).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bit_set::BitSet;
    use std::collections::HashMap;

    /// Helper to make a full BitSet covering [0, n).
    fn full_bitset(n: usize) -> BitSet {
        let mut bs = BitSet::new();
        for i in 0..n {
            bs.insert(i);
        }
        bs
    }

    #[test]
    fn test_cartesian_product_no_filter() {
        // {"a": [1,2], "b": [3,4]}, no filter → full 2×2 product.
        // Keys sorted: ["a","b"].  Strides: a=2, b=1.
        // Row 0: a[0]=1, b[0]=3 | Row 1: a[0]=1, b[1]=4
        // Row 2: a[1]=2, b[0]=3 | Row 3: a[1]=2, b[1]=4
        let data = HashMap::from([
            ("a".to_string(), ColumnData::Ints(vec![1, 2])),
            ("b".to_string(), ColumnData::Ints(vec![3, 4])),
        ]);
        let result = ColumnData::cartesian_product_with_correlation(data, &None);
        assert_eq!(
            result,
            ColumnData::Records(HashMap::from([
                ("a".to_string(), ColumnData::Ints(vec![1, 1, 2, 2])),
                ("b".to_string(), ColumnData::Ints(vec![3, 4, 3, 4])),
            ]))
        );
    }

    #[test]
    fn test_cartesian_product_empty_bitset() {
        // Empty correlation set → no rows selected → empty columns.
        let data = HashMap::from([
            ("a".to_string(), ColumnData::Ints(vec![1, 2])),
            ("b".to_string(), ColumnData::Ints(vec![3, 4])),
        ]);
        let result = ColumnData::cartesian_product_with_correlation(data, &Some(BitSet::new()));
        assert_eq!(
            result,
            ColumnData::Records(HashMap::from([
                ("a".to_string(), ColumnData::Ints(vec![])),
                ("b".to_string(), ColumnData::Ints(vec![])),
            ]))
        );
    }

    #[test]
    fn test_cartesian_product_full_bitset() {
        // Full BitSet covering all 4 rows → same output as no filter.
        let data = HashMap::from([
            ("a".to_string(), ColumnData::Ints(vec![1, 2])),
            ("b".to_string(), ColumnData::Ints(vec![3, 4])),
        ]);
        let result = ColumnData::cartesian_product_with_correlation(data, &Some(full_bitset(4)));
        assert_eq!(
            result,
            ColumnData::Records(HashMap::from([
                ("a".to_string(), ColumnData::Ints(vec![1, 1, 2, 2])),
                ("b".to_string(), ColumnData::Ints(vec![3, 4, 3, 4])),
            ]))
        );
    }

    #[test]
    fn test_cartesian_product_sparse_bitset() {
        // BitSet {0, 3} → rows 0 and 3 of the 2×2 product (diagonal).
        // Row 0: a[0]=1, b[0]=3 | Row 3: a[1]=2, b[1]=4
        let data = HashMap::from([
            ("a".to_string(), ColumnData::Ints(vec![1, 2])),
            ("b".to_string(), ColumnData::Ints(vec![3, 4])),
        ]);
        let mut filter = BitSet::new();
        filter.insert(0);
        filter.insert(3);
        let result = ColumnData::cartesian_product_with_correlation(data, &Some(filter));
        assert_eq!(
            result,
            ColumnData::Records(HashMap::from([
                ("a".to_string(), ColumnData::Ints(vec![1, 2])),
                ("b".to_string(), ColumnData::Ints(vec![3, 4])),
            ]))
        );
    }

    #[test]
    fn test_cartesian_product_empty_map() {
        let result = ColumnData::cartesian_product_with_correlation(HashMap::new(), &None);
        assert_eq!(result, ColumnData::Records(HashMap::new()));
    }

    #[test]
    fn test_cartesian_product_single_column() {
        // Single column with a full filter → identity.
        let data = HashMap::from([("a".to_string(), ColumnData::Ints(vec![10, 20, 30]))]);
        let result = ColumnData::cartesian_product_with_correlation(data, &Some(full_bitset(3)));
        assert_eq!(
            result,
            ColumnData::Records(HashMap::from([(
                "a".to_string(),
                ColumnData::Ints(vec![10, 20, 30]),
            )]))
        );
    }
}

/// A columnar value representation for vectorized execution.
/// Contains a batch of values with optional alignment information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ColumnValue {
    /// The batch of values
    pub data: ColumnData,
    /// Indices into the parent level's batch for alignment with outer iterations.
    /// None if this is the outermost level or independent.
    pub parent_indices: ParentIndices,
}

impl ColumnValue {
    /// Create a new ColumnValue with a single value (no parent alignment).
    pub fn single(value: Value) -> Self {
        ColumnValue {
            data: match value {
                Value::Bool(b) => ColumnData::Bools(BitVec::from_elem(1, b)),
                Value::Int(i) => ColumnData::Ints(vec![i]),
                Value::UInt(i) => ColumnData::UInts(vec![i]),
                Value::String(s) => ColumnData::Strings(vec![s]),
                _ => ColumnData::Variants(vec![value]),
            },
            parent_indices: ParentIndices::Scalar,
        }
    }

    pub fn from_values(values: Vec<Value>, extent: &Extent) -> ColumnValue {
        ColumnValue {
            data: ColumnData::from_values(values, extent),
            parent_indices: ParentIndices::TopLevelVector,
        }
    }

    /// Create a new ColumnValue from a vector of values (no parent alignment).
    pub fn from_ints(values: Vec<i64>) -> Self {
        ColumnValue {
            data: ColumnData::Ints(values),
            parent_indices: ParentIndices::TopLevelVector,
        }
    }

    pub fn from_uints(values: Vec<usize>) -> Self {
        ColumnValue {
            data: ColumnData::UInts(values),
            parent_indices: ParentIndices::TopLevelVector,
        }
    }

    pub fn from_column_data(data: ColumnData) -> Self {
        ColumnValue {
            data,
            parent_indices: ParentIndices::TopLevelVector,
        }
    }

    /// Create a new ColumnValue with parent alignment indices.
    pub fn with_parent_indices(data: ColumnData, parent_indices: Vec<usize>) -> Self {
        ColumnValue {
            data,
            parent_indices: ParentIndices::Parent(parent_indices),
        }
    }

    /// Check if this column contains a single value.
    pub fn is_single(&self) -> bool {
        self.len() == 1
    }

    /// Get the single value if this column contains exactly one value.
    pub fn as_single(&self) -> Option<Value> {
        self.data.as_single()
    }

    /// Get the number of values in this column.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Check if this column is empty.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Expand this column's values using the given parent_indices.
    /// Used when an outer variable needs to be aligned with an inner iteration.
    pub fn expand(&self, indices: &[usize]) -> ColumnValue {
        ColumnValue {
            data: self.data.select_indices(indices),
            // The expanded column inherits the indices as its own parent_indices
            parent_indices: ParentIndices::Parent(indices.to_vec()),
        }
    }
}
