//! Extent (the runtime type of an operator) and the data-source/sink traits
//! that an [`Extent::DataSourceDomain`] is built around.

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use intervalsets::ops::Difference;
use intervalsets::{Bounding, Interval, IntervalSet, MaybeEmpty};

use crate::ccl::TagMap;
use crate::interpreter::{Predicate, Tile};
use crate::util::fmt_record;

use super::ColumnValue;

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
            // A sum and a non-sum are **never** in an inclusion relation, in either
            // direction. A tagged value carries its tag, so no untagged space contains
            // one, and a tagged space contains no untagged value.
            //
            // No compiled program reaches this arm — a mixed pair would have to come
            // from one `Case`, whose codomains are tagged together or not at all — so
            // it is stated rather than inferred. If a path does arrive here, being
            // rejected at a conformance check is the signal.
            (Extent::Union(_), _) | (_, Extent::Union(_)) => false,

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
            // CHL's surface spelling, matching `Type::Variant` — see
            // `fmt_variant_arms`. A `Unit` payload is the nullary constructor
            // and renders bare.
            Extent::Union(arms) => crate::util::fmt_variant_arms(
                f,
                arms.iter().map(|(tag, e)| {
                    let payload = match e {
                        Extent::Base(BaseType::Unit) => None,
                        _ => Some(e.to_string()),
                    };
                    (tag.to_string(), payload)
                }),
                // A runtime extent is never an open demand — openness lives only
                // on the right of a subtyping edge and cannot reach here.
                false,
            ),
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

    /// A union renders in CHL's surface syntax, arms tagged: the tag is what
    /// identifies an arm, so a rendering that dropped it could not distinguish
    /// two unions with the same payload types under different tags.
    ///
    /// A `Unit` payload is the **nullary** constructor and renders bare
    /// (`` `abort ``, not `` `abort{Unit} ``) — the same collapse `Type::Variant`
    /// makes, so the two sides of the compile/runtime boundary spell one sum one
    /// way. That matters most in a tiling-mismatch panic, which prints an
    /// `Extent` beside the `Type` it was built from.
    #[test]
    fn test_extent_display_union() {
        let positional = Extent::Union(TagMap::from_positional(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::Bool),
        ]));
        assert_eq!(positional.to_string(), "{`0{Int} | `1{Bool}}");
        let named = Extent::Union(TagMap::from_arms(vec![
            (FieldKey::Name("commit".into()), Extent::Base(BaseType::Int)),
            (FieldKey::Name("abort".into()), Extent::Base(BaseType::Unit)),
        ]));
        assert_eq!(named.to_string(), "{`abort | `commit{Int}}");
    }

    /// A payload that already renders brace-delimited reuses those braces rather
    /// than doubling them — the surface rule that a nested type inside an arm
    /// omits its own. A payload that does not (a base type, a tuple, a function)
    /// gets the arm's braces around it.
    #[test]
    fn test_extent_display_union_collapses_a_braced_payload() {
        let record = Extent::Record(
            [
                ("a".to_string(), Extent::Base(BaseType::Int)),
                ("b".to_string(), Extent::Base(BaseType::Int)),
            ]
            .into_iter()
            .collect(),
        );
        let with_record = Extent::Union(TagMap::from_arms(vec![(
            FieldKey::Name("pair".into()),
            record,
        )]));
        assert_eq!(with_record.to_string(), "{`pair{a: Int, b: Int}}");

        // A nested sum is brace-delimited too, so it collapses the same way.
        let nested = Extent::Union(TagMap::from_arms(vec![(
            FieldKey::Name("outer".into()),
            Extent::Union(TagMap::from_arms(vec![
                (FieldKey::Name("x".into()), Extent::Base(BaseType::Unit)),
                (FieldKey::Name("y".into()), Extent::Base(BaseType::Int)),
            ])),
        )]));
        assert_eq!(nested.to_string(), "{`outer{`x | `y{Int}}}");

        // A function payload renders parenthesised, so the arm supplies braces.
        let func = Extent::Union(TagMap::from_arms(vec![(
            FieldKey::Name("f".into()),
            Extent::Function {
                domain: Box::new(Extent::Base(BaseType::Int)),
                codomain: Box::new(Extent::Base(BaseType::Bool)),
            },
        )]));
        assert_eq!(func.to_string(), "{`f{(Int -> Bool)}}");
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

    /// A sum does **not** include its arms' payload extents, and this holds for an
    /// anonymous positional sum too.
    ///
    /// A positional sum is the all-`Index` case of the same tagged representation, not
    /// an untagged union: a value in an `Int | Bool` column is `Union { tag: Index(i),
    /// inner }`, never a bare `Int`. So the arm's payload space and the sum's value
    /// space are different spaces, and inclusion relates them in neither direction.
    #[test]
    fn test_union_does_not_include_its_arm_payloads() {
        let u = Extent::Union(TagMap::from_positional(vec![
            Extent::Base(BaseType::Int),
            Extent::Base(BaseType::Bool),
        ]));
        assert!(!u.includes(&Extent::Base(BaseType::Int)));
        assert!(!u.includes(&Extent::Base(BaseType::Bool)));
        assert!(!u.includes(&Extent::Base(BaseType::String)));
        // And the other direction: a payload space does not contain tagged values.
        assert!(!Extent::Base(BaseType::Int).includes(&u));
        // The sum does include itself, and a width-narrower sum.
        assert!(u.includes(&u));
        assert!(
            u.includes(&Extent::Union(TagMap::from_positional(vec![Extent::Base(
                BaseType::Int
            )])))
        );
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

    /// **Variant width subtyping is matched by tag, not by position** — the one
    /// case a positional implementation gets wrong, and the reason `TagMap`
    /// exists.
    ///
    /// ``{`b{Int}} <: {`a{String} | `b{Int}}`` is a legal instance of the width
    /// rule, but `b` sits at position 0 in the subtype and position 1 in the
    /// supertype. Pairing arms positionally would compare `b`'s `Int` against
    /// `a`'s `String` and reject the inclusion (and, for a payload pair that
    /// happened to agree, accept a *wrong* one). The positional cases already
    /// covered above cannot see this: there the shared arms are a prefix, so
    /// tag order and position order agree.
    #[test]
    fn includes_variant_width_subtyping_pairs_arms_by_tag_not_position() {
        let wide = named(&[
            ("a", Extent::Base(BaseType::String)),
            ("b", Extent::Base(BaseType::Int)),
        ]);
        // `b` alone — at position 0 here, position 1 in `wide`.
        let narrow = named(&[("b", Extent::Base(BaseType::Int))]);
        assert!(
            wide.includes(&narrow),
            "a narrower tag set is included regardless of where its arms sit"
        );
        assert!(!narrow.includes(&wide), "and the converse does not hold");

        // The same shape with the payloads swapped is *not* an inclusion: `b`
        // pairs with `b`, so the mismatch is seen. A positional pairing would
        // line `b: String` up against `a: String` and wrongly accept.
        let mistagged = named(&[("b", Extent::Base(BaseType::String))]);
        assert!(
            !wide.includes(&mistagged),
            "arm `b`'s payload must be included by arm `b`'s, not by whichever \
             arm shares its position"
        );
    }

    fn named(arms: &[(&str, Extent)]) -> Extent {
        Extent::Union(TagMap::from_arms(
            arms.iter()
                .map(|(t, e)| (FieldKey::Name((*t).into()), e.clone()))
                .collect(),
        ))
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
