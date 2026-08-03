//! Extent (the runtime type of an operator) and the data-source/sink traits
//! that an [`Extent::DataSourceDomain`] is built around.

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use intervalsets::ops::Difference;
use intervalsets::{Bounding, Interval, IntervalSet, MaybeEmpty};

use crate::ccl::TagMap;
use crate::interpreter::{Predicate, Tile};
use crate::util::fmt_record;

use super::{ColumnValue, Value};

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
    Union(TagMap<Extent>),
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
            Extent::Union(arms) => arms
                .values()
                .map(Extent::subscribe_to_iteration_action)
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

    /// The **join** of two extents describing *alternative values of one
    /// result*: the smallest extent that [`includes`](Self::includes) both.
    ///
    /// This is the value-space counterpart of a `Case`'s arm join. Where the two
    /// alternatives are variants, joining **merges their tag maps** — the result
    /// is one arm or the other, so the space of both is the union of their tags,
    /// with a tag they share joining its payloads. That merged sum is exactly the
    /// column a merged variant stream carries: the inhabited arm holds the rows
    /// that occurred and the other arms are present but empty.
    ///
    /// `None` means the two have no join, which is not automatically an error:
    /// for a genuine concatenation the arm a row came from is part of its
    /// identity, and the caller keeps them separate (an anonymous positional sum)
    /// rather than merging.
    pub fn join(&self, other: &Extent) -> Option<Extent> {
        if self == other {
            return Some(self.clone());
        }
        match (self, other) {
            (Extent::Union(vs), Extent::Union(ws)) => {
                let mut merged = vs.clone();
                for (k, w) in ws.iter() {
                    match merged.get(k) {
                        // A shared tag's payloads must themselves join: the value
                        // at that tag came from one arm or the other.
                        Some(v) => *merged.get_mut(k)? = v.join(w)?,
                        None => {
                            merged.get_or_insert_with(k.clone(), || w.clone());
                        }
                    }
                }
                Some(Extent::Union(merged))
            }
            // Non-variant alternatives join only when one already covers the
            // other (a `UIntRange` inside a wider one, say).
            _ if self.includes(other) => Some(self.clone()),
            _ if other.includes(self) => Some(other.clone()),
            _ => None,
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

            // Union vs union — **this is variant width subtyping**, stated at the
            // runtime boundary. `other` is included iff every tag it carries is a
            // tag `self` carries, with an included payload. A tag `self` has and
            // `other` lacks is fine (that arm simply cannot occur in `other`); a tag
            // `other` has and `self` lacks is not (`self` could not represent it).
            //
            // Matching is by tag, not by position: a tag's position is relative to
            // its own sum's key set, so pairing arms positionally would compare
            // unrelated payloads whenever the two key sets differ.
            (Extent::Union(vs), Extent::Union(ws)) => ws
                .iter()
                .all(|(k, w)| vs.get(k).is_some_and(|v| v.includes(w))),
            // Union self vs scalar other: `other` must be covered by some arm.
            (Extent::Union(arms), _) => arms.values().any(|v| v.includes(other)),
            // Scalar self vs union other: `self` must include every arm.
            (_, Extent::Union(arms)) => arms.values().all(|v| self.includes(v)),

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
        write!(f, "{}", self.keyword())
    }
}

impl std::fmt::Display for Extent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Extent::Base(base) => write!(f, "{base}"),
            Extent::Function { domain, codomain } => write!(f, "({domain} -> {codomain})"),
            Extent::Record(fields) => fmt_record(f, fields),
            Extent::Union(arms) => {
                let arm_strs: Vec<String> =
                    arms.iter().map(|(tag, e)| format!(".{tag}({e})")).collect();
                write!(f, "({})", arm_strs.join(" | "))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::FieldKey;
    use std::collections::HashMap;

    // --- Display tests ---

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

    /// A union renders its arms with their tags: the tag is what identifies an
    /// arm, so a rendering that dropped it could not distinguish two unions with
    /// the same payload types under different tags.
    #[test]
    fn test_extent_display_union() {
        let positional = Extent::Union(TagMap::from_positional(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::Bool),
        ]));
        assert_eq!(positional.to_string(), "(.0(Int) | .1(Bool))");
        let named = Extent::Union(TagMap::from_arms(vec![
            (FieldKey::Name("Commit".into()), Extent::Base(BaseType::Int)),
            (FieldKey::Name("Abort".into()), Extent::Base(BaseType::Unit)),
        ]));
        assert_eq!(named.to_string(), "(.Abort(Unit) | .Commit(Int))");
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
        let u = Extent::Union(TagMap::from_positional(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::Bool),
        ]));
        assert!(u.includes(&Extent::Base(BaseType::Int)));
        assert!(u.includes(&Extent::Base(BaseType::Bool)));
        assert!(!u.includes(&Extent::Base(BaseType::String)));
    }

    #[test]
    fn test_includes_union_vs_union() {
        let u = Extent::Union(TagMap::from_positional(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::Bool),
        ]));
        assert!(u.includes(&u));
        let subset = Extent::Union(TagMap::from_positional(vec![Extent::Base(BaseType::Int)]));
        assert!(u.includes(&subset));
        assert!(!subset.includes(&u));
    }

    // --- join: alternative value spaces ---

    fn named(arms: &[(&str, Extent)]) -> Extent {
        Extent::Union(TagMap::from_arms(
            arms.iter()
                .map(|(t, e)| (FieldKey::Name((*t).into()), e.clone()))
                .collect(),
        ))
    }

    #[test]
    fn join_of_equal_extents_is_that_extent() {
        let int = Extent::Base(BaseType::Int);
        assert_eq!(int.join(&int), Some(int.clone()));
        let v = named(&[("some", int.clone())]);
        assert_eq!(v.join(&v), Some(v));
    }

    /// The case a conditional with differently-tagged arms produces: the join is
    /// the merged tag set, which is the column shape a merged variant stream has.
    #[test]
    fn join_of_disjoint_variants_merges_tags() {
        let pos = named(&[("pos", Extent::Base(BaseType::Int))]);
        let neg = named(&[("neg", Extent::Base(BaseType::Int))]);
        let merged = named(&[
            ("neg", Extent::Base(BaseType::Int)),
            ("pos", Extent::Base(BaseType::Int)),
        ]);
        assert_eq!(pos.join(&neg), Some(merged.clone()));
        // Joining is symmetric in the tags it produces.
        assert_eq!(neg.join(&pos), Some(merged.clone()));
        // And the join includes both inputs, which is what makes each arm's
        // narrower column representable in it.
        assert!(merged.includes(&pos));
        assert!(merged.includes(&neg));
    }

    /// A `Unit` payload is the nullary constructor's, so `.some(Int)` joined with
    /// `.none` is the two-tag sum — the `x if c else .none` shape.
    #[test]
    fn join_keeps_distinct_payloads_per_tag() {
        let some = named(&[("some", Extent::Base(BaseType::Int))]);
        let none = named(&[("none", Extent::Base(BaseType::Unit))]);
        assert_eq!(
            some.join(&none),
            Some(named(&[
                ("none", Extent::Base(BaseType::Unit)),
                ("some", Extent::Base(BaseType::Int)),
            ]))
        );
    }

    /// A tag both sides carry joins its payloads, so an unjoinable payload makes
    /// the whole join fail rather than silently picking one side.
    #[test]
    fn join_fails_on_conflicting_shared_payload() {
        let a = named(&[("t", Extent::Base(BaseType::Int))]);
        let b = named(&[("t", Extent::Base(BaseType::String))]);
        assert_eq!(a.join(&b), None);
    }

    /// Unrelated value spaces have no join. The caller keeps them as an anonymous
    /// positional sum, where which arm a row came from is part of its identity.
    #[test]
    fn join_of_unrelated_scalars_is_none() {
        assert_eq!(
            Extent::Base(BaseType::Int).join(&Extent::Base(BaseType::String)),
            None
        );
    }

    /// Non-variant alternatives join when one already covers the other.
    #[test]
    fn join_of_nested_ranges_is_the_wider() {
        let wide = Extent::Base(BaseType::UInt);
        let narrow = Extent::uint_range(3);
        assert_eq!(wide.join(&narrow), Some(wide.clone()));
        assert_eq!(narrow.join(&wide), Some(wide));
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
