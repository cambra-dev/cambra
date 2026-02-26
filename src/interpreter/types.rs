//! Core types for the CCL interpreter: Guard, Extent, BaseType, Value, FuncBinding, ColumnValue.

use std::{cell::RefCell, cmp::Ordering, collections::HashMap, hash::Hash, rc::Rc};

use bit_vec::BitVec;

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
            Guard::Or(guards) => guards.iter().any(|g| g.is_universal()),
            Guard::And(guards) => guards.iter().all(|g| g.is_universal()),
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
#[derive(Clone, PartialEq, Eq)]
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
}

/// The Extent of the domain of a Data Source
pub trait DataSourceDomainExtentImpl {
    fn get_id(&self) -> &str;
    fn check_for_new_data(&mut self) -> bool;
    fn get_yield_guard(&self) -> Guard;
    fn get_elements(&self) -> ColumnData;
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
            Extent::Record(fields) => {
                let field_strs: Vec<String> = fields
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
            _ => todo!("Ordering not implemented yet"),
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
    Tuples(Vec<ColumnData>),
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
            ColumnData::Tuples(_) => todo!("No tuple value yet"),
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
    pub fn from_values(values: Vec<Value>) -> ColumnData {
        let exemplar = if values.is_empty() {
            &Value::Unit
        } else {
            &values[0]
        };
        match exemplar {
            Value::Unit => ColumnData::Units(values.len()),
            Value::Bool(..) => ColumnData::Bools(values.iter().map(Value::as_bool).collect()),
            Value::Int(..) => ColumnData::Ints(values.iter().map(Value::as_int).collect()),
            Value::UInt(..) => ColumnData::UInts(values.iter().map(Value::as_uint).collect()),
            Value::String(..) => {
                ColumnData::Strings(values.iter().map(|v| v.as_string().to_string()).collect())
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
            ColumnData::Tuples(t) => {
                ColumnData::Tuples(t.iter().map(|c| c.select_indices(indices)).collect())
            }
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
            ColumnData::Tuples(t) => t[0].len(),
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
                ColumnData::Tuples(_t) => todo!("No tuple value yet"),
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

    pub fn from_values(values: Vec<Value>) -> ColumnValue {
        ColumnValue {
            data: ColumnData::from_values(values),
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
