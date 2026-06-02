//! Core types for the CCL interpreter: Guard, Extent, BaseType, Value, FuncBinding, ColumnValue.

use std::iter;
use std::mem::take;
use std::{cell::RefCell, cmp::Ordering, collections::HashMap, hash::Hash, rc::Rc};

use bit_vec::BitVec;
use intervalsets::numeric::Domain;
use intervalsets::ops::Difference;
use intervalsets::{Bounding, Interval, IntervalSet, MaybeEmpty, Side};
use smol_str::SmolStr;

use crate::interpreter::{
    BinOpKind, Predicate, Tile, UnaryOpKind, apply_binop_column, apply_unaryop_column, tuple_field,
};
use crate::pretty_graph::fmt_binop;
use crate::util::fmt_record;

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
    /// A finite set of unsigned integer indices, represented as an interval set.
    ///
    /// Created from a CCL `UIntRange(n)` type as the full set `[0, n)`, and
    /// shrunk directly as individual elements or sub-intervals are released.
    UIntRange(IntervalSet<usize>),
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
            (Extent::UIntRange(s1), Extent::UIntRange(s2)) => s1 == s2,
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
            Extent::UIntRange(..) => NotifyOrSubscribeResult {
                notify: true,
                subscribe: false,
            },
            // Record extents are immediately ready if all fields are ready,
            // otherwise we register with the scheduler.
            Extent::Record(fields) => fields
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
            // Union extents iterate each variant in turn; we are ready iff every
            // variant is ready, and we subscribe iff any variant requires it.
            Extent::Union(variants) => variants
                .iter()
                .map(|variant| variant.subscribe_to_iteration_action())
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
            Value::ComputableFunction(_) => todo!(),
            // Union values carry only their inner value; the full union extent requires
            // knowledge of all variant types, which is tracked at the operator level.
            Value::Union { inner, .. } => Self::for_value(inner),
        }
    }

    /// Whether this extent includes all of `other` (i.e. `self` is a supertype of `other`,
    /// or equivalently every value in `other` is also a value in `self`).
    pub fn includes(&self, other: &Extent) -> bool {
        match (self, other) {
            // Base types include only the same base type.
            (Extent::Base(t1), Extent::Base(t2)) => t1 == t2,

            // Function types: self.domain must include other.domain, and the codomains must be equal.
            (
                Extent::Function {
                    domain: d1,
                    codomain: c1,
                },
                Extent::Function {
                    domain: d2,
                    codomain: c2,
                },
            ) => d1.includes(d2) && c1 == c2,

            // Records: same set of field names, each field covariant.
            (Extent::Record(m1), Extent::Record(m2)) => {
                m1.len() == m2.len()
                    && m1
                        .iter()
                        .all(|(k, e1)| m2.get(k).is_some_and(|e2| e1.includes(e2)))
            }

            // Union self vs union other: every variant of `other` must be covered by
            // some variant of `self`.
            (Extent::Union(vs), Extent::Union(ws)) => {
                ws.iter().all(|w| vs.iter().any(|v| v.includes(w)))
            }
            // Union self vs scalar other: `other` must be covered by at least one variant.
            (Extent::Union(variants), _) => variants.iter().any(|v| v.includes(other)),
            // Scalar self vs union other: `self` must include every variant.
            (_, Extent::Union(variants)) => variants.iter().all(|v| self.includes(v)),

            (Extent::Base(BaseType::UInt), Extent::UIntRange(..)) => true,

            // UIntRange: s1 includes s2 iff s2 is a subset of s1.
            (Extent::UIntRange(s1), Extent::UIntRange(s2)) => s2.difference(s1).is_empty(),

            // DataSourceDomain: identity check
            (Extent::DataSourceDomain(d1), Extent::DataSourceDomain(d2)) => d1 == d2,

            // If self is not a DataSourceDomain, then check if it is larger than the inner extent
            // of other.
            (_, Extent::DataSourceDomain(d2)) => self.includes(&d2.borrow().element_extent()),

            // Two restricted extents sharing the same restriction object are subsets
            // of the same predicate; inclusion then reduces to base inclusion.
            (
                Extent::Restricted {
                    base: b1,
                    restriction: r1,
                },
                Extent::Restricted {
                    base: b2,
                    restriction: r2,
                },
            ) => Rc::ptr_eq(r1, r2) && b1.includes(b2),

            // An unrestricted extent includes a restricted one iff it includes the
            // base, because the restricted set is always a subset of the base.
            (_, Extent::Restricted { base, .. }) => self.includes(base),

            // All other combinations are incompatible.
            _ => false,
        }
    }
}

/// Placeholder restriction handle for [`Extent::Restricted`].
///
/// Restriction computation is handled by [`crate::interpreter::tile_operators::Filter`] operators in the tile path.
/// This struct exists only to satisfy the [`Extent::Restricted`] variant's type requirement
/// and will panic if any computation method is called.
#[derive(Debug, Default)]
pub struct Restriction;

impl Restriction {
    /// Create a new empty restriction.
    pub fn new() -> Self {
        Self
    }
}

/// Abstraction for sending computed responses back to waiting clients.
///
/// Implemented by sink types (e.g. [`crate::interpreter::http_server::HttpServerSharedState`])
/// that are paired with a [`DataSourceDomainExtentImpl`].  Sources without an
/// output channel do not implement this trait; sources with a
/// corresponding output channel implement it to dispatch responses.
///
/// Receives a full [`Tile`] so the implementation can apply its own
/// domain/codomain extraction and deduplication logic.
pub trait DataSink: Send + Sync {
    /// Dispatch any not-yet-sent responses contained in `tile`.
    fn process(&self, tile: &Tile);
}

pub trait DataSourceDomainExtentImpl {
    fn get_id(&self) -> &str;
    fn check_for_new_data(&mut self) -> bool;
    /// Returns the current yield predicate: the region of domain values
    /// available to consume.
    fn get_yield_predicate(&self) -> Predicate;
    /// Returns the current set of domain elements as a ColumnValue, according to the stored
    /// obsolete predicate of the producer.
    fn get_elements(&self, producer: &str) -> ColumnValue;
    /// Returns the [`Extent`] of each individual domain element.
    /// Used to construct a typed empty [`ColumnValue`] when the domain is empty.
    fn element_extent(&self) -> Extent;
    /// Returns the output value for a given domain key.
    ///
    /// Used by [`crate::interpreter::tile_operators::MapResultWithSource`] to map each domain
    /// element to its corresponding output value when building a
    /// `SealedFunction { domain, codomain: Scalar(output_values) }` tile.
    fn get(&self, keys: ColumnValue) -> ColumnValue;
    /// Returns the [`Extent`] of each output value produced by this source.
    /// Used to type the codomain of [`crate::interpreter::tile_operators::MapResultWithSource`].
    fn output_value_extent(&self) -> Extent;
    /// Returns the CCL element type produced by this source (the codomain of its
    /// `Fun(DataSource(name), T)` type).  Used by
    /// [`crate::ccl::context::GlobalContext::register_source`] to build the full
    /// inference type without needing to know the concrete source type.
    fn output_type(&self) -> crate::ccl::Type;
    /// Release the region described by `obsolete` for the given producer — those domain values no longer
    /// need to be retained by the source.
    fn release(&mut self, producer: &str, obsolete: Predicate);
}

impl PartialEq for dyn DataSourceDomainExtentImpl {
    fn eq(&self, other: &Self) -> bool {
        self.get_id() == other.get_id()
    }
}
impl Eq for dyn DataSourceDomainExtentImpl {}

impl std::fmt::Display for BaseType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BaseType::Int => write!(f, "Int"),
            BaseType::UInt => write!(f, "UInt"),
            BaseType::String => write!(f, "String"),
            BaseType::Bool => write!(f, "Bool"),
            BaseType::Unit => write!(f, "Unit"),
        }
    }
}

impl std::fmt::Display for Extent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Extent::Base(base) => write!(f, "{base}"),
            Extent::Function { domain, codomain } => write!(f, "({domain} -> {codomain})"),
            Extent::Record(fields) => fmt_record(f, fields),
            Extent::Union(extents) => {
                let extent_strs: Vec<String> = extents.iter().map(|e| format!("{e}")).collect();
                write!(f, "({})", extent_strs.join(" | "))
            }
            Extent::UIntRange(set) => write!(f, "{set}"),
            Extent::DataSourceDomain(source) => write!(f, "Source({})", source.borrow().get_id()),
            Extent::Restricted { base, .. } => write!(f, "Restricted({base})"),
        }
    }
}

impl std::fmt::Debug for Extent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl Extent {
    /// Construct a `UIntRange` extent covering `[0, n)`.
    ///
    /// The resulting interval set contains every unsigned integer in `[0, n)`.
    /// For `n == 0`, the set is empty.
    pub fn uint_range(n: usize) -> Self {
        Self::uint_range_interval(0, n)
    }

    /// Construct a `UIntRange` extent covering `[start, end)`.
    ///
    /// Returns an empty set when `start >= end`.
    pub fn uint_range_interval(start: usize, end: usize) -> Self {
        if start >= end {
            Extent::UIntRange(IntervalSet::from(Interval::<usize>::empty()))
        } else {
            Extent::UIntRange(IntervalSet::from(Interval::closed_open(start, end)))
        }
    }

    /// If this is a `UIntRange` whose remaining set is a single contiguous
    /// range starting at `0` (i.e. `[0, n)`), return `n`.
    ///
    /// Used to convert a compile-time extent back to a CCL `Type::UIntRange(n)`.
    pub fn as_uint_range_size(&self) -> Option<usize> {
        if let Extent::UIntRange(set) = self {
            if set.is_empty() {
                return Some(0);
            }
            let intervals = set.intervals();
            if intervals.len() == 1 {
                let iv = &intervals[0];
                if iv.lval() == Some(&0) {
                    // Discrete intervals are normalized to closed bounds,
                    // so the right bound is n-1 and n = rval + 1.
                    return iv.rval().map(|r| r + 1);
                }
            }
        }
        None
    }

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

    /// Create a restricted record extent: an [`Extent::Restricted`] wrapping an [`Extent::Record`].
    pub fn restricted_record(fields: HashMap<String, Extent>) -> Self {
        Extent::restricted(Extent::Record(fields))
    }

    /// Wrap any extent in an [`Extent::Restricted`] with a fresh [`Restriction`].
    pub fn restricted(base: Extent) -> Self {
        Extent::Restricted {
            base: Box::new(base),
            restriction: Rc::new(RefCell::new(Restriction::new())),
        }
    }

    /// Return the restriction handle if this is an [`Extent::Restricted`] extent.
    pub fn restriction(&mut self) -> Option<Rc<RefCell<Restriction>>> {
        match self {
            Extent::Restricted { restriction, .. } => Some(restriction.clone()),
            _ => None,
        }
    }

    /// Return the field map if this extent is an [`Extent::Record`], or an [`Extent::Restricted`] wrapping one.
    pub fn record_fields(&self) -> Option<&HashMap<String, Extent>> {
        match self {
            Extent::Record(fields) => Some(fields),
            Extent::Restricted { base, .. } => base.record_fields(),
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
}

/// Base types in CCL — re-exported from [`crate::ccl::BaseType`].
///
/// The authoritative definition lives in `ccl/mod.rs`; this re-export keeps
/// all interpreter callsites (`crate::interpreter::BaseType`) working without
/// changes.
pub use crate::ccl::BaseType;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionDef {
    BinOp(BinOpKind),
    /// Unary arithmetic or boolean operation applied element-wise to a single column.
    UnaryOp(UnaryOpKind),
    RecordField(String),
}

impl FunctionDef {
    pub fn apply(&self, input: ColumnValue) -> ColumnValue {
        match (self, input) {
            (FunctionDef::BinOp(op), ColumnValue::Records(mut fields)) => apply_binop_column(
                *op,
                fields.remove(&tuple_field(0)).expect("Not a tuple"),
                &fields[&tuple_field(1)],
            ),
            (FunctionDef::UnaryOp(op), cv) => apply_unaryop_column(*op, cv),
            (FunctionDef::RecordField(f), ColumnValue::Records(mut fields)) => fields
                .remove(f)
                .unwrap_or_else(|| panic!("Missing field {f}")),
            _ => panic!("Invalid function application"),
        }
    }
}

impl std::fmt::Display for FunctionDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FunctionDef::UnaryOp(op) => write!(f, "UnaryOp({op:?})"),
            FunctionDef::BinOp(op) => write!(f, "BinOp({})", fmt_binop(op)),
            FunctionDef::RecordField(field) => write!(f, ".{field}"),
        }
    }
}

/// Values in CCL
#[derive(Clone, PartialEq, Eq)]
pub enum Value {
    Int(i64),
    UInt(usize),
    String(SmolStr),
    Bool(bool),
    Unit,
    /// A function value (collection of bindings)
    Function(Vec<FuncBinding>),
    /// A record value
    Record(HashMap<String, Value>),
    ComputableFunction(FunctionDef),
    /// A tagged union value: `tag` identifies which variant, `inner` is the actual value.
    Union {
        tag: usize,
        inner: Box<Value>,
    },
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
            Value::ComputableFunction(f) => f.hash(state),
            Value::Union { tag, inner } => {
                tag.hash(state);
                inner.hash(state);
            }
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
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
            Value::Record(fields) => {
                if let Value::Record(o_fields) = other {
                    if fields.keys().collect::<std::collections::HashSet<_>>()
                        != o_fields.keys().collect::<std::collections::HashSet<_>>()
                    {
                        return None; // Records with different keys are not comparable
                    }
                    let mut entries: Vec<_> = fields.iter().collect();
                    let mut o_entries: Vec<_> = o_fields.iter().collect();
                    entries.sort_by_key(|(k, _)| *k);
                    o_entries.sort_by_key(|(k, _)| *k);
                    entries.partial_cmp(&o_entries)
                } else {
                    None
                }
            }
            Value::Union { tag, inner } => {
                if let Value::Union {
                    tag: o_tag,
                    inner: o_inner,
                } = other
                {
                    tag.partial_cmp(o_tag).and_then(|o| {
                        if o.is_eq() {
                            inner.partial_cmp(o_inner)
                        } else {
                            Some(o)
                        }
                    })
                } else {
                    None
                }
            }
            _ => todo!("Ordering not implemented yet: {self:?}"),
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{i}"),
            Value::UInt(i) => write!(f, "u{i}"),
            Value::String(s) => write!(f, "\"{s}\""),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Unit => write!(f, "()"),
            Value::Function(bindings) => {
                // If inputs are exactly u0..uN, omit them for readability.
                let is_list = bindings_are_list(bindings);
                let binding_strs: Vec<String> = bindings
                    .iter()
                    .map(|b| {
                        if is_list {
                            format!("{}", b.output)
                        } else {
                            format!("{} -> {}", b.input, b.output)
                        }
                    })
                    .collect();
                write!(f, "Function [ {} ]", binding_strs.join(", "))
            }
            Value::Record(fields) => fmt_record(f, fields),
            Value::ComputableFunction(fun) => write!(f, "{fun}"),
            Value::Union { tag, inner } => write!(f, "Union[{tag}]({inner})"),
        }
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl Domain for Value {
    /// Finds the next smaller or larger element, or None if no such element exists
    /// (like <0 for usize, or anything for strings and floats).
    fn try_adjacent(&self, side: Side) -> Option<Self> {
        match (self, side) {
            (Value::Bool(false), Side::Left) => None,
            (Value::Bool(true), Side::Left) => Some(Value::from(false)),
            (Value::Bool(false), Side::Right) => Some(Value::from(true)),
            (Value::Bool(true), Side::Right) => None,
            (Value::Int(i), Side::Left) => i.checked_sub(1).map(Value::from),
            (Value::Int(i), Side::Right) => i.checked_add(1).map(Value::from),
            (Value::UInt(i), Side::Left) => i.checked_sub(1).map(Value::from),
            (Value::UInt(i), Side::Right) => i.checked_add(1).map(Value::from),
            _ => None,
        }
    }
}

impl From<i64> for Value {
    fn from(v: i64) -> Self {
        Value::Int(v)
    }
}

impl From<usize> for Value {
    fn from(v: usize) -> Self {
        Value::UInt(v)
    }
}

impl From<SmolStr> for Value {
    fn from(v: SmolStr) -> Self {
        Value::String(v)
    }
}

impl From<bool> for Value {
    fn from(v: bool) -> Self {
        Value::Bool(v)
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

    pub fn as_string(&self) -> &SmolStr {
        match self {
            Value::String(s) => s,
            _ => panic!("Not string: {self:?}"),
        }
    }

    pub fn as_function(&self) -> &Vec<FuncBinding> {
        match self {
            Value::Function(v) => v,
            _ => panic!("Not function: {self:?}"),
        }
    }
}

/// Returns whether the given FuncBindings represent a logical list.
pub fn bindings_are_list(bindings: &[FuncBinding]) -> bool {
    bindings
        .iter()
        .enumerate()
        .all(|(i, b)| b.input == Value::UInt(i))
}

/// A function binding represents a single input-output pair for a function
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncBinding {
    pub input: Value,
    pub output: Value,
}

/// Retain elements of `v` where the corresponding `mask` bit is true,
/// preserving the relative order of kept elements.
///
/// Order-stable: walks `v` with a write cursor, swapping each kept element
/// into the next write slot.  A faster two-pointer swap-with-end algorithm
/// (similar to the one used for the `Bools` variant of `ColumnValue::retain`)
/// would not preserve order, which is incompatible with how mutation-loop
/// outputs land in a `Tile::SealedFunction` with a `Union`-domain: the
/// `Union` variants in `ColumnValue::retain` use a stable `select_indices`
/// filter (their order has to match the stably-filtered `tags`), so the
/// codomain — retained via this function — must also stay in source order
/// to keep domain/codomain entries aligned position-by-position.
fn retain_vec<T>(v: &mut Vec<T>, mask: &BitVec) {
    debug_assert_eq!(
        mask.len(),
        v.len(),
        "retain_vec: mask length must match vector length"
    );
    let mut write = 0usize;
    for read in 0..v.len() {
        if mask[read] {
            if write != read {
                v.swap(write, read);
            }
            write += 1;
        }
    }
    v.truncate(write);
}

/// Columnar data for vectorized execution.
/// Each variant holds a typed batch of values produced during interpretation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ColumnValue {
    Units(usize),
    Ints(Vec<i64>),
    UInts(Vec<usize>),
    Strings(Vec<SmolStr>),
    Bools(BitVec),
    Variants(Vec<Value>),
    FunctionBindings {
        inputs: Box<ColumnValue>,
        outputs: Box<ColumnValue>,
    },
    Records(HashMap<String, ColumnValue>),
    /// A tagged union column: each element belongs to one of several typed variants.
    ///
    /// `tags[i]` is the 0-based variant index for element `i`.
    /// `variants[j]` holds only the elements whose tag equals `j`, in the order
    /// they appear in the overall sequence.  The total element count is `tags.len()`.
    Union {
        /// Variant index for each element.
        tags: Vec<usize>,
        /// Per-variant column; `variants[j].len()` equals the count of `j`s in `tags`.
        variants: Vec<ColumnValue>,
    },
}

impl ColumnValue {
    /// Construct a `FunctionBindings` variant from inputs and outputs.
    pub fn function_bindings(inputs: ColumnValue, outputs: ColumnValue) -> ColumnValue {
        Self::FunctionBindings {
            inputs: Box::new(inputs),
            outputs: Box::new(outputs),
        }
    }

    /// Get a value at a specific index.
    pub fn index_at(&self, i: usize) -> Value {
        match self {
            ColumnValue::Units(_) => Value::Unit,
            ColumnValue::Bools(v) => Value::Bool(v[i]),
            ColumnValue::Ints(v) => Value::Int(v[i]),
            ColumnValue::UInts(v) => Value::UInt(v[i]),
            ColumnValue::Strings(v) => Value::String(v[i].clone()),
            ColumnValue::Variants(v) => v[i].clone(),
            ColumnValue::FunctionBindings { inputs, outputs } => {
                Value::Function(vec![FuncBinding {
                    input: inputs.index_at(i),
                    output: outputs.index_at(i),
                }])
            }
            ColumnValue::Records(r) => {
                Value::Record(r.iter().map(|(k, v)| (k.clone(), v.index_at(i))).collect())
            }
            ColumnValue::Union { tags, variants } => {
                let tag = tags[i];
                // Count how many elements before index i belong to the same variant.
                let variant_idx = tags[..i].iter().filter(|&&t| t == tag).count();
                Value::Union {
                    tag,
                    inner: Box::new(variants[tag].index_at(variant_idx)),
                }
            }
        }
    }

    /// Repeat a single-element `ColumnValue` to the given length.
    pub fn repeat(&self, n: usize) -> ColumnValue {
        assert_eq!(self.len(), 1, "repeat requires single-element ColumnValue");
        match self {
            ColumnValue::Units(_) => ColumnValue::Units(n),
            ColumnValue::Bools(v) => ColumnValue::Bools(BitVec::from_elem(n, v[0])),
            ColumnValue::Ints(v) => ColumnValue::Ints(vec![v[0]; n]),
            ColumnValue::UInts(v) => ColumnValue::UInts(vec![v[0]; n]),
            ColumnValue::Strings(v) => ColumnValue::Strings(vec![v[0].clone(); n]),
            ColumnValue::Variants(v) => ColumnValue::Variants(vec![v[0].clone(); n]),
            ColumnValue::Records(r) => {
                ColumnValue::Records(r.iter().map(|(k, v)| (k.clone(), v.repeat(n))).collect())
            }
            _ => panic!("Cannot repeat composite ColumnValue"),
        }
    }

    /// Convert a Vec<Value> into typed ColumnValue.
    pub fn from_values(values: Vec<Value>, extent: &Extent) -> ColumnValue {
        match extent {
            Extent::Base(BaseType::Unit) => ColumnValue::Units(values.len()),
            Extent::Base(BaseType::Bool) => {
                ColumnValue::Bools(values.iter().map(Value::as_bool).collect())
            }
            Extent::Base(BaseType::Int) => {
                ColumnValue::Ints(values.iter().map(Value::as_int).collect())
            }
            Extent::Base(BaseType::UInt) | Extent::UIntRange(..) => {
                ColumnValue::UInts(values.iter().map(Value::as_uint).collect())
            }
            Extent::Base(BaseType::String) => {
                ColumnValue::Strings(values.iter().map(|v| v.as_string().clone()).collect())
            }
            Extent::Record(m) => {
                // Pivot the list of Records into a Record of ColumnValues
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
                            ColumnValue::from_values(
                                field_values,
                                extent
                                    .record_fields()
                                    .and_then(|fields| fields.get(&key))
                                    .unwrap_or_else(|| {
                                        panic!("Record extent missing field '{key}'")
                                    }),
                            ),
                        )
                    })
                    .collect();
                ColumnValue::Records(fields)
            }
            Extent::DataSourceDomain(d) => {
                ColumnValue::from_values(values, &d.borrow().element_extent())
            }
            Extent::Union(sub_extents) => {
                let mut tags: Vec<usize> = Vec::with_capacity(values.len());
                let mut per_variant: Vec<Vec<Value>> = vec![Vec::new(); sub_extents.len()];
                for v in values {
                    let Value::Union { tag, inner } = v else {
                        panic!("Expected Value::Union in from_values for Union extent, got {v:?}");
                    };
                    tags.push(tag);
                    per_variant[tag].push(*inner);
                }
                ColumnValue::Union {
                    tags,
                    variants: per_variant
                        .into_iter()
                        .zip(sub_extents.iter())
                        .map(|(vals, ext)| ColumnValue::from_values(vals, ext))
                        .collect(),
                }
            }
            _ => ColumnValue::Variants(values),
        }
    }

    /// Sort `FunctionBindings` by their input values.
    pub fn sort_by_inputs(&self) -> ColumnValue {
        match self {
            ColumnValue::FunctionBindings { inputs, outputs } => {
                let n = inputs.len();
                let mut indices: Vec<usize> = (0..n).collect();
                indices.sort_by(|&a, &b| {
                    inputs
                        .index_at(a)
                        .partial_cmp(&inputs.index_at(b))
                        .expect("Cannot compare inputs")
                });
                ColumnValue::function_bindings(
                    inputs.select_indices(indices.iter().cloned(), indices.len()),
                    outputs.select_indices(indices.iter().cloned(), indices.len()),
                )
            }
            other => other.clone(),
        }
    }

    /// Select elements at the given indices.
    pub fn select_indices(
        &self,
        indices: impl Iterator<Item = usize>,
        indices_len: usize,
    ) -> ColumnValue {
        match self {
            ColumnValue::Units(_) => ColumnValue::Units(indices_len),
            ColumnValue::Bools(v) => ColumnValue::Bools(indices.map(|i| v[i]).collect()),
            ColumnValue::Ints(v) => ColumnValue::Ints(indices.map(|i| v[i]).collect()),
            ColumnValue::UInts(v) => ColumnValue::UInts(indices.map(|i| v[i]).collect()),
            ColumnValue::Strings(v) => {
                ColumnValue::Strings(indices.map(|i| v[i].clone()).collect())
            }
            ColumnValue::Variants(v) => {
                ColumnValue::Variants(indices.map(|i| v[i].clone()).collect())
            }
            ColumnValue::FunctionBindings { inputs, outputs } => {
                let i: Vec<_> = indices.collect();
                ColumnValue::function_bindings(
                    inputs.select_indices(i.iter().cloned(), i.len()),
                    outputs.select_indices(i.iter().cloned(), i.len()),
                )
            }
            ColumnValue::Records(r) => {
                let i: Vec<_> = indices.collect();
                ColumnValue::Records(
                    r.iter()
                        .map(|(k, v)| (k.clone(), v.select_indices(i.iter().cloned(), indices_len)))
                        .collect(),
                )
            }
            ColumnValue::Union { tags, variants } => {
                let selected_indices: Vec<usize> = indices.collect();
                // Build the new tags for selected elements.
                let new_tags: Vec<usize> = selected_indices.iter().map(|&i| tags[i]).collect();
                // Count per-variant totals in the original so we can map positions.
                let mut variant_counts: Vec<usize> = vec![0; variants.len()];
                for &t in tags.iter() {
                    variant_counts[t] += 1;
                }
                // For each original position, record which variant-local index it is.
                let mut running: Vec<usize> = vec![0; variants.len()];
                let mut per_element_variant_idx: Vec<usize> = Vec::with_capacity(tags.len());
                for &t in tags.iter() {
                    per_element_variant_idx.push(running[t]);
                    running[t] += 1;
                }
                // For each variant, collect the variant-local indices we want to keep.
                let mut per_variant_selection: Vec<Vec<usize>> = vec![Vec::new(); variants.len()];
                for &orig_idx in &selected_indices {
                    let t = tags[orig_idx];
                    per_variant_selection[t].push(per_element_variant_idx[orig_idx]);
                }
                let new_variants: Vec<ColumnValue> = variants
                    .iter()
                    .enumerate()
                    .map(|(j, cv)| {
                        let sel = &per_variant_selection[j];
                        let len = sel.len();
                        cv.select_indices(sel.iter().cloned(), len)
                    })
                    .collect();
                ColumnValue::Union {
                    tags: new_tags,
                    variants: new_variants,
                }
            }
        }
    }

    /// Return the number of elements in this column.
    pub fn len(&self) -> usize {
        match &self {
            ColumnValue::Units(len) => *len,
            ColumnValue::Bools(v) => v.len(),
            ColumnValue::Ints(v) => v.len(),
            ColumnValue::UInts(v) => v.len(),
            ColumnValue::Strings(v) => v.len(),
            ColumnValue::Variants(v) => v.len(),
            ColumnValue::Records(m) => {
                let result = m.values().next().expect("Empty Record").len();
                debug_assert!(
                    m.values().all(|cv| cv.len() == result),
                    "Inconsistent column lengths in Record",
                );
                result
            }
            ColumnValue::FunctionBindings { inputs, .. } => inputs.len(),
            ColumnValue::Union { tags, .. } => tags.len(),
        }
    }

    /// Return `true` if this column contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return `true` if this column contains exactly one element.
    pub fn is_single(&self) -> bool {
        self.len() == 1
    }

    /// Return `true` if this column's element type is consistent with `extent`.
    ///
    /// This is a structural check — it verifies that the `ColumnValue` variant
    /// matches what `from_values(..., extent)` would have produced for the same
    /// data. `DataSourceDomain` extents are resolved to their element extent
    /// before comparison.
    pub fn is_compatible_with_extent(&self, extent: &Extent) -> bool {
        let extent = match extent {
            Extent::DataSourceDomain(source) => source.borrow().element_extent(),
            Extent::Restricted { base, .. } => *base.clone(),
            other => other.clone(),
        };
        match (self, extent) {
            (ColumnValue::Units(_), Extent::Base(BaseType::Unit)) => true,
            (ColumnValue::Bools(_), Extent::Base(BaseType::Bool)) => true,
            (ColumnValue::Ints(_), Extent::Base(BaseType::Int)) => true,
            (ColumnValue::UInts(_), Extent::Base(BaseType::UInt)) => true,
            (ColumnValue::UInts(_), Extent::UIntRange(..)) => true,
            (ColumnValue::Strings(_), Extent::Base(BaseType::String)) => true,
            (ColumnValue::Records(fields), Extent::Record(ext_fields)) => {
                fields.len() == ext_fields.len()
                    && fields.iter().all(|(k, cv)| {
                        ext_fields
                            .get(k)
                            .is_some_and(|e| cv.is_compatible_with_extent(e))
                    })
            }
            (ColumnValue::FunctionBindings { .. }, Extent::Function { .. }) => true,
            (ColumnValue::Union { variants, .. }, Extent::Union(ext_variants)) => {
                variants.len() == ext_variants.len()
                    && variants
                        .iter()
                        .zip(ext_variants.iter())
                        .all(|(cv, e)| cv.is_compatible_with_extent(e))
            }
            // Variants is the fallback used for Union, unknown, etc.
            (ColumnValue::Variants(_), _) => true,
            _ => false,
        }
    }

    /// Return `true` if this column is a single scalar value that can broadcast.
    /// Note: it's a bit unsafe that we are just using length for this, as it
    /// could mask bugs where a vector column of length 1 could be treated as a
    /// scalar.
    /// TODO: consider adding an explicit Scalar variant to ColumnValue to avoid this ambiguity.
    pub fn is_scalar(&self) -> bool {
        self.len() == 1
    }

    /// Get the single value if this column contains exactly one element.
    pub fn as_single(&self) -> Option<Value> {
        if self.len() == 1 {
            match self {
                ColumnValue::Units(len) => {
                    if *len == 1 {
                        Some(Value::Unit)
                    } else {
                        None
                    }
                }
                ColumnValue::Bools(v) => Some(Value::Bool(v[0])),
                ColumnValue::Ints(v) => Some(Value::Int(v[0])),
                ColumnValue::UInts(v) => Some(Value::UInt(v[0])),
                ColumnValue::Strings(v) => Some(Value::String(v[0].clone())),
                ColumnValue::Variants(v) => Some(v[0].clone()),
                ColumnValue::FunctionBindings { inputs, outputs } => {
                    Some(Value::Function(vec![FuncBinding {
                        input: inputs.as_single().expect("Not single").clone(),
                        output: outputs.as_single().expect("Not single").clone(),
                    }]))
                }
                ColumnValue::Records(r) => Some(Value::Record(
                    r.iter()
                        .map(|e| (e.0.clone(), e.1.as_single().expect("Not single").clone()))
                        .collect(),
                )),
                ColumnValue::Union { tags, variants } => {
                    let tag = tags[0];
                    let inner = variants[tag].as_single()?;
                    Some(Value::Union {
                        tag,
                        inner: Box::new(inner),
                    })
                }
            }
        } else {
            None
        }
    }

    /// Create a `ColumnValue` from a single `Value`, wrapping it in a 1-element column.
    pub fn single(value: Value) -> Self {
        match value {
            Value::Bool(b) => ColumnValue::Bools(BitVec::from_elem(1, b)),
            Value::Int(i) => ColumnValue::Ints(vec![i]),
            Value::UInt(i) => ColumnValue::UInts(vec![i]),
            Value::String(s) => ColumnValue::Strings(vec![s]),
            Value::Record(fields) => ColumnValue::Records(
                fields
                    .into_iter()
                    .map(|(k, v)| (k, ColumnValue::single(v)))
                    .collect(),
            ),
            _ => ColumnValue::Variants(vec![value]),
        }
    }

    /// Drain this column into an owned iterator of [`Value`]s, one per row.
    ///
    /// After the call, `self` is left in a valid but empty state.
    /// Note: this is quite expensive and should be used as a last resort.
    pub fn drain_to_value_iter(&mut self) -> Box<dyn Iterator<Item = Value>> {
        match self {
            ColumnValue::Units(n) => {
                let count = *n;
                *n = 0;
                Box::new(iter::repeat_n(Value::Unit, count))
            }
            ColumnValue::Bools(v) => {
                // BitVec::take gives us ownership so we can return a 'static iterator.
                Box::new(take(v).into_iter().map(Value::Bool))
            }
            ColumnValue::Ints(v) => Box::new(take(v).into_iter().map(Value::Int)),
            ColumnValue::UInts(v) => Box::new(take(v).into_iter().map(Value::UInt)),
            ColumnValue::Strings(v) => Box::new(take(v).into_iter().map(Value::String)),
            ColumnValue::Variants(v) => Box::new(take(v).into_iter()),
            ColumnValue::FunctionBindings { inputs, outputs } => Box::new(
                inputs
                    .drain_to_value_iter()
                    .zip(outputs.drain_to_value_iter())
                    .map(|(input, output)| Value::Function(vec![FuncBinding { input, output }])),
            ),
            ColumnValue::Records(m) => {
                let m = take(m);
                let n = m.values().next().map(|v| v.len()).unwrap_or(0);
                Box::new((0..n).map(move |i| {
                    Value::Record(m.iter().map(|(k, v)| (k.clone(), v.index_at(i))).collect())
                }))
            }
            ColumnValue::Union { tags, variants } => {
                let tags = take(tags);
                let n = tags.len();
                // Snapshot the variants so the closure can own them.
                let variants = variants.to_vec();
                // Build per-variant running counts so we can derive variant-local indices.
                let mut running: Vec<usize> = vec![0; variants.len()];
                Box::new((0..n).map(move |i| {
                    let tag = tags[i];
                    let vi = running[tag];
                    running[tag] += 1;
                    Value::Union {
                        tag,
                        inner: Box::new(variants[tag].index_at(vi)),
                    }
                }))
            }
        }
    }

    /// Create a `ColumnValue` from a `Vec<i64>`.
    pub fn from_ints(values: Vec<i64>) -> Self {
        ColumnValue::Ints(values)
    }

    /// Create a `ColumnValue` from a `Vec<usize>`.
    pub fn from_uints(values: Vec<usize>) -> Self {
        ColumnValue::UInts(values)
    }

    /// Compute the cartesian product of a map of named column values.
    ///
    /// Returns a [`ColumnValue::Records`] where each field is expanded so that the fields
    /// together enumerate every combination of rows across all input columns. The total
    /// row count is the product of all input column lengths.
    ///
    /// # Example
    /// Given `{"a": [1, 2], "b": [3, 4]}`, returns
    /// `Records {"a": [1, 1, 2, 2], "b": [3, 4, 3, 4]}`.
    pub fn cartesian_product(data: HashMap<String, ColumnValue>) -> ColumnValue {
        if data.is_empty() {
            return ColumnValue::Records(HashMap::new());
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
                let indices = (0..total).map(|i| (i / stride) % lengths[j]);
                (key.clone(), data[key].select_indices(indices, total))
            })
            .collect();
        ColumnValue::Records(expanded)
    }

    /// Construct a `ColumnValue` containing the given string values.
    pub fn strings(values: &[&str]) -> ColumnValue {
        ColumnValue::Strings(values.iter().map(|s| (*s).into()).collect())
    }

    pub fn append(&mut self, other: ColumnValue) {
        match (self, other) {
            (ColumnValue::Units(s), ColumnValue::Units(o)) => *s += o,
            (ColumnValue::Ints(s), ColumnValue::Ints(mut o)) => s.append(&mut o),
            (ColumnValue::UInts(s), ColumnValue::UInts(mut o)) => s.append(&mut o),
            (ColumnValue::Bools(s), ColumnValue::Bools(mut o)) => s.append(&mut o),
            (ColumnValue::Strings(s), ColumnValue::Strings(mut o)) => s.append(&mut o),
            (ColumnValue::Variants(s), ColumnValue::Variants(mut o)) => s.append(&mut o),
            (
                ColumnValue::FunctionBindings {
                    inputs: si,
                    outputs: so,
                },
                ColumnValue::FunctionBindings {
                    inputs: oi,
                    outputs: oo,
                },
            ) => {
                si.append(*oi);
                so.append(*oo);
            }
            (ColumnValue::Records(s), ColumnValue::Records(o)) => {
                for (k, v) in o {
                    s.get_mut(&k)
                        .unwrap_or_else(|| panic!("Missing field {k} in append"))
                        .append(v);
                }
            }
            (
                ColumnValue::Union {
                    tags: st,
                    variants: sv,
                },
                ColumnValue::Union {
                    tags: ot,
                    variants: ov,
                },
            ) => {
                assert_eq!(sv.len(), ov.len(), "Union append: variant count mismatch");
                st.extend(ot);
                for (s, o) in sv.iter_mut().zip(ov) {
                    s.append(o);
                }
            }
            _ => panic!("Mismatched ColumnValue variants in append"),
        }
    }

    /// Retain only elements where `mask[i]` is true, in-place.
    ///
    /// Not guaranteed to preserve element ordering; when possible, uses swap-remove to avoid shifting data.
    pub fn retain(&mut self, mask: &BitVec) {
        assert_eq!(
            mask.len(),
            self.len(),
            "mask length must match column length"
        );
        match self {
            ColumnValue::Units(_) => {
                *self = ColumnValue::Units(mask.count_ones() as usize);
            }
            ColumnValue::Ints(v) => retain_vec(v, mask),
            ColumnValue::UInts(v) => retain_vec(v, mask),
            ColumnValue::Strings(v) => retain_vec(v, mask),
            ColumnValue::Variants(v) => retain_vec(v, mask),
            ColumnValue::Bools(v) => {
                let n = v.len();
                if n > 0 {
                    let mut left = 0usize;
                    let mut right = n - 1;
                    loop {
                        while left < right && mask[left] {
                            left += 1;
                        }
                        while right > left && !mask[right] {
                            right -= 1;
                        }
                        if left >= right {
                            break;
                        }
                        let lv = v[left];
                        let rv = v[right];
                        v.set(left, rv);
                        v.set(right, lv);
                        left += 1;
                        right -= 1;
                    }
                }
                let count = mask.iter().filter(|b| *b).count();
                v.truncate(count);
            }
            ColumnValue::FunctionBindings { inputs, outputs } => {
                inputs.retain(mask);
                outputs.retain(mask);
            }
            ColumnValue::Records(r) => {
                for v in r.values_mut() {
                    v.retain(mask);
                }
            }
            ColumnValue::Union { tags, variants } => {
                // Build per-variant masks, then retain in each variant.
                let mut per_variant_mask: Vec<BitVec> = variants
                    .iter()
                    .map(|v| BitVec::from_elem(v.len(), false))
                    .collect();
                let mut running: Vec<usize> = vec![0; variants.len()];
                for (i, &t) in tags.iter().enumerate() {
                    let vi = running[t];
                    running[t] += 1;
                    if mask[i] {
                        per_variant_mask[t].set(vi, true);
                    }
                }
                let new_tags: Vec<usize> = tags
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| mask[*i])
                    .map(|(_, &t)| t)
                    .collect();
                *tags = new_tags;
                for (v, m) in variants.iter_mut().zip(per_variant_mask.iter()) {
                    // Use select_indices for a stable retain.  Like `retain_vec`,
                    // this preserves source order — required because `tags` above
                    // is filtered stably, and each variant column has to stay
                    // aligned with the tag occurrences of its variant.
                    let kept: Vec<usize> = m
                        .iter()
                        .enumerate()
                        .filter(|(_, b)| *b)
                        .map(|(i, _)| i)
                        .collect();
                    let len = kept.len();
                    *v = v.select_indices(kept.into_iter(), len);
                }
            }
        }
    }

    /// Map each element of `self` through a lookup table defined by parallel
    /// `(map_keys, map_values)` columns.
    ///
    /// Builds a `HashMap<key_type, position>` from `map_keys`, then uses
    /// [`ColumnValue::select_indices`] to extract the corresponding `map_values`
    /// entries.  Dispatching the value-type through `select_indices` means only
    /// the key type needs an explicit match arm here.
    ///
    /// Drains `self` as a side effect (the column is left empty after the call).
    pub fn transform_by_map(
        &mut self,
        map_keys: ColumnValue,
        map_values: ColumnValue,
    ) -> ColumnValue {
        let indices: Vec<usize> = match (self, map_keys) {
            (ColumnValue::UInts(v), ColumnValue::UInts(mk)) => {
                let pos: HashMap<usize, usize> =
                    mk.into_iter().enumerate().map(|(i, k)| (k, i)).collect();
                take(v).into_iter().map(|k| pos[&k]).collect()
            }
            (ColumnValue::Ints(v), ColumnValue::Ints(mk)) => {
                let pos: HashMap<i64, usize> =
                    mk.into_iter().enumerate().map(|(i, k)| (k, i)).collect();
                take(v).into_iter().map(|k| pos[&k]).collect()
            }
            (ColumnValue::Strings(v), ColumnValue::Strings(mk)) => {
                let pos: HashMap<SmolStr, usize> =
                    mk.into_iter().enumerate().map(|(i, k)| (k, i)).collect();
                take(v).into_iter().map(|k| pos[&k]).collect()
            }
            (ColumnValue::Bools(v), ColumnValue::Bools(mk)) => {
                let pos: HashMap<bool, usize> =
                    mk.into_iter().enumerate().map(|(i, k)| (k, i)).collect();
                take(v).into_iter().map(|k| pos[&k]).collect()
            }
            (ColumnValue::Variants(v), ColumnValue::Variants(mk)) => {
                let pos: HashMap<Value, usize> =
                    mk.into_iter().enumerate().map(|(i, k)| (k, i)).collect();
                take(v).into_iter().map(|k| pos[&k]).collect()
            }
            (s, mk) => panic!(
                "transform_by_map: key type mismatch or unsupported: {:?} vs {:?}",
                s, mk
            ),
        };
        let n = indices.len();
        map_values.select_indices(indices.into_iter(), n)
    }

    /// Map each element of `self` (which must be [`ColumnValue::UInts`] used as
    /// zero-based indices) through `map`, returning the selected entries.
    ///
    /// Delegates entirely to [`ColumnValue::select_indices`], so `map` may be
    /// any `ColumnValue` variant.  Drains `self` as a side effect.
    pub fn transform_by_list(&mut self, map: ColumnValue) -> ColumnValue {
        let ColumnValue::UInts(v) = self else {
            panic!("transform_by_list: input must be UInts, got {self:?}")
        };
        let indices = take(v);
        let n = indices.len();
        map.select_indices(indices.into_iter(), n)
    }

    pub fn for_each_uint(&mut self, f: impl Fn(&mut usize)) {
        match self {
            ColumnValue::UInts(v) => v.iter_mut().for_each(f),
            _ => panic!("Not UInts"),
        }
    }

    /// Returns a reference to the internal bitvec if this ColumnValue is bools.
    pub fn as_bitvec(&self) -> Option<&BitVec> {
        if let ColumnValue::Bools(b) = self {
            Some(b)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_cartesian_product_no_filter() {
        // {"a": [1,2], "b": [3,4]}, no filter → full 2×2 product.
        // Keys sorted: ["a","b"].  Strides: a=2, b=1.
        // Row 0: a[0]=1, b[0]=3 | Row 1: a[0]=1, b[1]=4
        // Row 2: a[1]=2, b[0]=3 | Row 3: a[1]=2, b[1]=4
        let data = HashMap::from([
            ("a".to_string(), ColumnValue::Ints(vec![1, 2])),
            ("b".to_string(), ColumnValue::Ints(vec![3, 4])),
        ]);
        let result = ColumnValue::cartesian_product(data);
        assert_eq!(
            result,
            ColumnValue::Records(HashMap::from([
                ("a".to_string(), ColumnValue::Ints(vec![1, 1, 2, 2])),
                ("b".to_string(), ColumnValue::Ints(vec![3, 4, 3, 4])),
            ]))
        );
    }

    #[test]
    fn test_cartesian_product_empty_map() {
        let result = ColumnValue::cartesian_product(HashMap::new());
        assert_eq!(result, ColumnValue::Records(HashMap::new()));
    }

    // --- retain_vec tests ---

    #[test]
    fn test_retain_vec_keep_some() {
        // mask: keep indices 0 and 2, drop index 1.
        // Order is unspecified; sort to compare.
        let mut v = vec![10, 20, 30];
        let mut mask = BitVec::from_elem(3, false);
        mask.set(0, true);
        mask.set(2, true);
        retain_vec(&mut v, &mask);
        v.sort();
        assert_eq!(v, vec![10, 30]);
    }

    #[test]
    fn test_retain_vec_keep_all() {
        let mut v = vec![1, 2, 3];
        let mask = BitVec::from_elem(3, true);
        retain_vec(&mut v, &mask);
        v.sort();
        assert_eq!(v, vec![1, 2, 3]);
    }

    #[test]
    fn test_retain_vec_keep_none() {
        let mut v = vec![1, 2, 3];
        let mask = BitVec::from_elem(3, false);
        retain_vec(&mut v, &mask);
        assert!(v.is_empty());
    }

    // --- ColumnValue::Union retain tests ---

    /// Helper: build a `ColumnValue::Union` from parallel tag/value slices.
    ///
    /// `rows` is `(tag, value)` in source order.  Values for a given tag must
    /// be `Value::Int`; each variant column is `ColumnValue::Ints`.
    fn make_union_cv(rows: &[(usize, i64)], n_variants: usize) -> ColumnValue {
        let tags: Vec<usize> = rows.iter().map(|(t, _)| *t).collect();
        let mut per_variant: Vec<Vec<i64>> = vec![Vec::new(); n_variants];
        for (t, v) in rows {
            per_variant[*t].push(*v);
        }
        ColumnValue::Union {
            tags,
            variants: per_variant.into_iter().map(ColumnValue::Ints).collect(),
        }
    }

    fn mask(bits: &[bool]) -> BitVec {
        let mut bv = BitVec::from_elem(bits.len(), false);
        for (i, &b) in bits.iter().enumerate() {
            bv.set(i, b);
        }
        bv
    }

    /// Keeping all rows leaves the column unchanged.
    #[test]
    fn retain_union_keep_all() {
        // rows: tag0→1, tag1→10, tag0→2, tag1→20
        let mut cv = make_union_cv(&[(0, 1), (1, 10), (0, 2), (1, 20)], 2);
        cv.retain(&mask(&[true, true, true, true]));
        assert_eq!(cv, make_union_cv(&[(0, 1), (1, 10), (0, 2), (1, 20)], 2));
    }

    /// Dropping all rows yields empty tags and empty variant columns.
    #[test]
    fn retain_union_drop_all() {
        let mut cv = make_union_cv(&[(0, 1), (1, 10), (0, 2)], 2);
        cv.retain(&mask(&[false, false, false]));
        let ColumnValue::Union { tags, variants } = &cv else {
            panic!("expected Union");
        };
        assert!(tags.is_empty());
        assert!(variants.iter().all(|v| v.is_empty()));
    }

    /// Dropping a row from one variant removes only that variant's value,
    /// leaving the other variant's values untouched.
    #[test]
    fn retain_union_drop_one_from_each_variant() {
        // Source order: tag0→1, tag1→10, tag0→2, tag1→20
        // Keep rows 0 and 3 (tag0→1, tag1→20); drop rows 1 and 2.
        let mut cv = make_union_cv(&[(0, 1), (1, 10), (0, 2), (1, 20)], 2);
        cv.retain(&mask(&[true, false, false, true]));
        let ColumnValue::Union { tags, variants } = &cv else {
            panic!("expected Union");
        };
        assert_eq!(tags, &[0, 1]);
        assert_eq!(variants[0], ColumnValue::Ints(vec![1]));
        assert_eq!(variants[1], ColumnValue::Ints(vec![20]));
    }

    /// Keeping only rows from one variant empties the other variant's column.
    #[test]
    fn retain_union_keep_only_one_variant() {
        // Source order: tag0→1, tag1→10, tag0→2
        // Keep only the two tag-0 rows.
        let mut cv = make_union_cv(&[(0, 1), (1, 10), (0, 2)], 2);
        cv.retain(&mask(&[true, false, true]));
        let ColumnValue::Union { tags, variants } = &cv else {
            panic!("expected Union");
        };
        assert_eq!(tags, &[0, 0]);
        assert_eq!(variants[0], ColumnValue::Ints(vec![1, 2]));
        assert_eq!(variants[1], ColumnValue::Ints(vec![]));
    }

    /// Retaining consecutive rows from the middle preserves source order within each variant.
    #[test]
    fn retain_union_preserves_variant_order() {
        // Source order: tag0→10, tag0→20, tag1→100, tag0→30, tag1→200
        // Keep rows 1,2,3 (tag0→20, tag1→100, tag0→30); drop first and last.
        let mut cv = make_union_cv(&[(0, 10), (0, 20), (1, 100), (0, 30), (1, 200)], 2);
        cv.retain(&mask(&[false, true, true, true, false]));
        let ColumnValue::Union { tags, variants } = &cv else {
            panic!("expected Union");
        };
        assert_eq!(tags, &[0, 1, 0]);
        assert_eq!(variants[0], ColumnValue::Ints(vec![20, 30]));
        assert_eq!(variants[1], ColumnValue::Ints(vec![100]));
    }

    // --- Display tests ---

    #[test]
    fn test_value_display_primitives() {
        assert_eq!(Value::Int(42).to_string(), "42");
        assert_eq!(Value::Int(-7).to_string(), "-7");
        assert_eq!(Value::UInt(3).to_string(), "u3");
        assert_eq!(Value::String("hello".into()).to_string(), "\"hello\"");
        assert_eq!(Value::Bool(true).to_string(), "true");
        assert_eq!(Value::Bool(false).to_string(), "false");
        assert_eq!(Value::Unit.to_string(), "()");
    }

    #[test]
    fn test_value_display_function_positional() {
        // Inputs are u0, u1, u2 — should be omitted.
        let f = Value::Function(vec![
            FuncBinding {
                input: Value::UInt(0),
                output: Value::String("a".into()),
            },
            FuncBinding {
                input: Value::UInt(1),
                output: Value::String("b".into()),
            },
        ]);
        assert_eq!(f.to_string(), r#"Function [ "a", "b" ]"#);
    }

    #[test]
    fn test_value_display_function_non_positional() {
        // Inputs are not u0..uN — should be shown explicitly.
        let f = Value::Function(vec![
            FuncBinding {
                input: Value::String("x".into()),
                output: Value::Int(1),
            },
            FuncBinding {
                input: Value::String("y".into()),
                output: Value::Int(2),
            },
        ]);
        assert_eq!(f.to_string(), r#"Function [ "x" -> 1, "y" -> 2 ]"#);
    }

    #[test]
    fn test_value_display_function_gap_in_indices() {
        // u0, u2 — not contiguous, so inputs should be shown.
        let f = Value::Function(vec![
            FuncBinding {
                input: Value::UInt(0),
                output: Value::Int(10),
            },
            FuncBinding {
                input: Value::UInt(2),
                output: Value::Int(20),
            },
        ]);
        assert_eq!(f.to_string(), "Function [ u0 -> 10, u2 -> 20 ]");
    }

    #[test]
    fn test_value_display_record() {
        let mut fields = HashMap::new();
        fields.insert("x".to_string(), Value::Int(1));
        let r = Value::Record(fields);
        assert_eq!(r.to_string(), "{x: 1}");
    }

    #[test]
    fn test_extent_display_base() {
        assert_eq!(Extent::Base(BaseType::Int).to_string(), "Int");
        assert_eq!(Extent::Base(BaseType::UInt).to_string(), "UInt");
        assert_eq!(Extent::Base(BaseType::String).to_string(), "String");
        assert_eq!(Extent::Base(BaseType::Bool).to_string(), "Bool");
        assert_eq!(Extent::Base(BaseType::Unit).to_string(), "Unit");
    }

    #[test]
    fn test_extent_display_function() {
        let e = Extent::function(Extent::Base(BaseType::Int), Extent::Base(BaseType::String));
        assert_eq!(e.to_string(), "(Int -> String)");
    }

    #[test]
    fn test_extent_display_union() {
        let e = Extent::Union(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::Bool),
        ]);
        assert_eq!(e.to_string(), "(Int | Bool)");
    }

    #[test]
    fn test_extent_display_uint_range() {
        // Discrete intervals are normalised to closed form: [2, 5) -> [2, 4].
        let e = Extent::uint_range_interval(2, 5);
        assert_eq!(e.to_string(), "{[2, 4]}");
    }

    #[test]
    fn test_extent_display_nested_function() {
        // (Int -> (Bool -> String))
        let inner = Extent::function(Extent::Base(BaseType::Bool), Extent::Base(BaseType::String));
        let outer = Extent::function(Extent::Base(BaseType::Int), inner);
        assert_eq!(outer.to_string(), "(Int -> (Bool -> String))");
    }

    // -----------------------------------------------------------------------
    // Extent::includes
    // -----------------------------------------------------------------------

    #[test]
    fn test_includes_base_same() {
        assert!(Extent::Base(BaseType::Int).includes(&Extent::Base(BaseType::Int)));
        assert!(Extent::Base(BaseType::Bool).includes(&Extent::Base(BaseType::Bool)));
    }

    #[test]
    fn test_includes_base_different() {
        assert!(!Extent::Base(BaseType::Int).includes(&Extent::Base(BaseType::Bool)));
        assert!(!Extent::Base(BaseType::String).includes(&Extent::Base(BaseType::Int)));
    }

    #[test]
    fn test_includes_uint_range_subset() {
        let wide = Extent::uint_range(10);
        let narrow = Extent::uint_range_interval(2, 7);
        assert!(wide.includes(&narrow));
        assert!(!narrow.includes(&wide));
    }

    #[test]
    fn test_includes_uint_range_equal() {
        let r = Extent::uint_range_interval(3, 6);
        assert!(r.includes(&r));
    }

    #[test]
    fn test_includes_record_same() {
        let r = Extent::Record(HashMap::from([
            ("a".to_string(), Extent::Base(BaseType::Int)),
            ("b".to_string(), Extent::Base(BaseType::Bool)),
        ]));
        assert!(r.includes(&r));
    }

    #[test]
    fn test_includes_record_covariant_field() {
        // Wide has field "a" = Int; narrow has field "a" = Int and "b" = Bool (different size).
        let wide = Extent::Record(HashMap::from([("a".to_string(), Extent::uint_range(10))]));
        let narrow = Extent::Record(HashMap::from([(
            "a".to_string(),
            Extent::uint_range_interval(2, 5),
        )]));
        assert!(wide.includes(&narrow));
        assert!(!narrow.includes(&wide));
    }

    #[test]
    fn test_includes_union_self_includes_member() {
        let u = Extent::Union(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::Bool),
        ]);
        assert!(u.includes(&Extent::Base(BaseType::Int)));
        assert!(u.includes(&Extent::Base(BaseType::Bool)));
        assert!(!u.includes(&Extent::Base(BaseType::String)));
    }

    #[test]
    fn test_includes_union_vs_union() {
        let u = Extent::Union(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::Bool),
        ]);
        assert!(u.includes(&u));
        let subset = Extent::Union(vec![Extent::Base(BaseType::Int)]);
        assert!(u.includes(&subset));
        assert!(!subset.includes(&u));
    }

    #[test]
    fn test_includes_restricted_subset_of_base() {
        let base = Extent::Base(BaseType::Int);
        let restricted = Extent::restricted(base.clone());
        // The base type includes its restriction (restriction is a subset of base).
        assert!(base.includes(&restricted));
        // A restriction cannot include an unrestricted base of the same kind.
        assert!(!restricted.includes(&base));
    }

    #[test]
    fn test_includes_function_codomain_covariant() {
        let codomain = Extent::Base(BaseType::Int);
        let narrow_domain = Extent::uint_range(5);
        let wide_domain = Extent::uint_range(10);
        let wide_fn = Extent::Function {
            domain: Box::new(wide_domain),
            codomain: Box::new(codomain.clone()),
        };
        let narrow_fn = Extent::Function {
            domain: Box::new(narrow_domain),
            codomain: Box::new(codomain),
        };
        assert!(wide_fn.includes(&narrow_fn));
        assert!(!narrow_fn.includes(&wide_fn));
    }
}
