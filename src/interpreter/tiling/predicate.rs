//! The [`Predicate`] type: subset-of-an-extent descriptions used by guards, plus
//! the column-value conversions and the sealed-function domain-sort helper.

use std::collections::HashMap;

use bit_set::BitSet;
use intervalsets::{
    Bounding, Interval, IntervalSet, MaybeEmpty, Side,
    numeric::Domain,
    ops::{Complement, Contains, Difference, Intersection, Union},
};

use crate::{
    ccl::{BaseType, TagMap},
    interpreter::{ColumnValue, Extent, Tile, UnionArm, Value, transform_hashmap_values},
};

/// A predicate that describes a subset of values in an extent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Predicate {
    True,
    False,
    LessThanEq(Value),
    Intervals(IntervalSet<Value>),
    /// Represents the AND of each of the sub-predicates.
    Record(HashMap<String, Predicate>),
    /// The union of multiple predicates — admits any value accepted by any arm.
    ///
    /// Produced when two [`Predicate::Record`] predicates are unioned, since OR
    /// cannot be pushed through the AND semantics of a record predicate.
    ///
    /// Invariant: arms never directly nest another `Or` (always flattened by
    /// [`Predicate::flatten_or`]).
    Or(Vec<Predicate>),
    /// Predicate over a discriminated-union domain.
    ///
    /// `variants[i]` is the predicate for elements whose tag equals `i`.
    /// Admits a value `Union { tag, inner }` iff `variants[tag].contains(inner)`.
    /// Semantically equivalent to `Or` of per-variant predicates, but preserving
    /// the tag structure for efficient dispatch.
    ///
    /// Invariant: `variants.len()` matches the number of variants in the domain.
    Union(TagMap<Predicate>),
}

impl Predicate {
    /// Builds a `Predicate` from a list of arms, flattening any nested `Or`
    /// variants.  Returns the single element directly when `arms` has length
    /// one to avoid gratuitous wrapping.
    pub fn flatten_or(arms: Vec<Predicate>) -> Predicate {
        let flat: Vec<Predicate> = arms
            .into_iter()
            .flat_map(|p| match p {
                Predicate::Or(inner) => inner,
                other => vec![other],
            })
            .collect();
        if flat.is_empty() {
            unreachable!("flatten_or called with no arms");
        }
        // Drop any arm that is subsumed by another arm in the list.
        // When two arms mutually subsume each other (i.e., are semantically
        // equivalent) the one with the lower index is kept, avoiding both
        // being removed.  The condition reads: remove arm[i] if there exists
        // arm[j] (j ≠ i) that subsumes arm[i], unless arm[i] also subsumes
        // arm[j] and i < j (in which case we prefer arm[i]).
        let keep: Vec<bool> = flat
            .iter()
            .enumerate()
            .map(|(i, arm)| {
                !flat.iter().enumerate().any(|(j, other)| {
                    j != i && other.subsumes(arm) && (j < i || !arm.subsumes(other))
                })
            })
            .collect();
        let reduced: Vec<Predicate> = flat
            .into_iter()
            .zip(keep)
            .filter_map(|(p, k)| k.then_some(p))
            .collect();
        match reduced.len() {
            0 => unreachable!("flatten_or: all arms were removed by subsumption"),
            1 => reduced.into_iter().next().unwrap(),
            _ => Predicate::Or(reduced),
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Predicate::False => Some(false),
            Predicate::True => Some(true),
            Predicate::Record(m) if m.iter().all(|(_, p)| p.is_true()) => Some(true),
            Predicate::Record(m) if m.iter().all(|(_, p)| p.is_false()) => Some(false),
            Predicate::Intervals(i) if i.complement().is_empty() => Some(true),
            Predicate::Intervals(i) if i.is_empty() => Some(false),
            // Or is true if any arm is true; false if all arms are false.
            Predicate::Or(arms) => {
                if arms.iter().any(|p| p.as_bool() == Some(true)) {
                    Some(true)
                } else if arms.iter().all(|p| p.as_bool() == Some(false)) {
                    Some(false)
                } else {
                    None
                }
            }
            // Union is true if every variant is true; false if every variant is false.
            Predicate::Union(ps) => {
                if ps.values().all(|p| p.as_bool() == Some(true)) {
                    Some(true)
                } else if ps.values().all(|p| p.as_bool() == Some(false)) {
                    Some(false)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    // Returns whether `self` is equivalent to Predicate::True
    pub fn is_true(&self) -> bool {
        self.as_bool().unwrap_or(false)
    }

    // Returns whether `self` is equivalent to Predicate::False
    pub fn is_false(&self) -> bool {
        !self.as_bool().unwrap_or(true)
    }

    pub fn split_record<V>(&self, fields: &HashMap<String, V>) -> HashMap<String, Predicate> {
        match self {
            p if p.as_bool().is_some() => fields
                .keys()
                .map(|f| {
                    (
                        f.clone(),
                        if p.as_bool().unwrap() {
                            Predicate::True
                        } else {
                            Predicate::False
                        },
                    )
                })
                .collect(),
            Predicate::Record(m) => {
                assert!(fields.len() == m.len() && fields.keys().all(|f| m.contains_key(f)));
                m.clone()
            }
            _ => panic!(
                "Cannot split as record with keys [{:?}]: {:?}",
                fields.keys().collect::<Vec<_>>(),
                self
            ),
        }
    }

    /// Returns the predicate that admits exactly the values accepted by both `self` and `other`.
    pub fn intersect(&self, other: &Predicate) -> Predicate {
        match (self, other) {
            // True is the universal predicate: identity under intersection.
            (Predicate::True, p) | (p, Predicate::True) => p.clone(),
            // False is the empty predicate: annihilator under intersection.
            (Predicate::False, _) | (_, Predicate::False) => Predicate::False,
            // Two upper bounds: keep the tighter (smaller) one.
            (Predicate::LessThanEq(a), Predicate::LessThanEq(b)) => match a.partial_cmp(b) {
                Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal) => {
                    Predicate::LessThanEq(a.clone())
                }
                Some(std::cmp::Ordering::Greater) => Predicate::LessThanEq(b.clone()),
                None => panic!("Cannot compare values in LessThanEq predicates: {a:?} and {b:?}"),
            },
            // Upper bound intersected with an interval set: restrict to (-∞, v].
            (Predicate::LessThanEq(v), Predicate::Intervals(s))
            | (Predicate::Intervals(s), Predicate::LessThanEq(v)) => {
                let upper = IntervalSet::new(vec![Interval::unbound_closed(v.clone())]);
                let result = s.intersection(&upper);
                if result.is_empty() {
                    Predicate::False
                } else {
                    Predicate::Intervals(result)
                }
            }
            // Two interval sets: standard set intersection.
            (Predicate::Intervals(a), Predicate::Intervals(b)) => {
                let result = a.intersection(b);
                if result.is_empty() {
                    Predicate::False
                } else {
                    Predicate::Intervals(result)
                }
            }
            // Records: intersect field-by-field.
            (Predicate::Record(m1), Predicate::Record(m2)) => {
                assert_eq!(
                    m1.len(),
                    m2.len(),
                    "Cannot intersect Record predicates with different schemas"
                );
                Predicate::Record(
                    m1.iter()
                        .map(|(k, p1)| (k.clone(), p1.intersect(&m2[k])))
                        .collect(),
                )
            }
            // Or distributes over intersect: (A | B) & C = (A & C) | (B & C).
            (Predicate::Or(arms), _) => {
                Predicate::flatten_or(arms.iter().map(|a| a.intersect(other)).collect())
            }
            (_, Predicate::Or(arms)) => {
                Predicate::flatten_or(arms.iter().map(|a| self.intersect(a)).collect())
            }
            // Union: intersect per variant.
            (Predicate::Union(ps), Predicate::Union(qs)) => {
                assert!(
                    ps.same_tags(qs),
                    "Union intersect: arm sets differ ({:?} vs {:?})",
                    ps.keys().collect::<Vec<_>>(),
                    qs.keys().collect::<Vec<_>>()
                );
                Predicate::Union(ps.map(|k, p| match qs.get(k) {
                    Some(q) => p.intersect(q),
                    None => Predicate::False,
                }))
            }
            _ => panic!("Cannot intersect incompatible predicates: {self:?} and {other:?}"),
        }
    }

    /// Returns the predicate that admits values in `self` but not in `other` (set difference).
    ///
    /// `self ∖ other = { x | x ∈ self ∧ x ∉ other }`
    pub fn minus(&self, other: &Predicate) -> Predicate {
        match (self, other) {
            // p ∖ ∅ = p
            (s, o) if o.is_false() => s.clone(),
            // p ∖ U = ∅
            (_, o) if o.is_true() => Predicate::False,
            // ∅ ∖ p = ∅
            (s, _) if s.is_false() => Predicate::False,
            // U ∖ Intervals(s): everything not in s — representable as the complement.
            (s, Predicate::Intervals(i)) if s.is_true() => {
                let result = i.complement();
                if result.is_empty() {
                    Predicate::False
                } else {
                    Predicate::Intervals(result)
                }
            }
            // (-∞, v] ∖ Intervals(s): subtract the interval set from the upper-bound half-line.
            (Predicate::LessThanEq(v), Predicate::Intervals(s)) => {
                let lhs = IntervalSet::new(vec![Interval::unbound_closed(v.clone())]);
                let result = lhs.difference(s);
                if result.is_empty() {
                    Predicate::False
                } else {
                    Predicate::Intervals(result)
                }
            }
            (Predicate::LessThanEq(v), Predicate::LessThanEq(s)) => {
                let lhs = IntervalSet::new(vec![Interval::unbound_closed(v.clone())]);
                let rhs = IntervalSet::new(vec![Interval::unbound_closed(s.clone())]);
                let result = lhs.difference(&rhs);
                if result.is_empty() {
                    Predicate::False
                } else {
                    Predicate::Intervals(result)
                }
            }
            // Intervals ∖ Intervals: standard set difference.
            (Predicate::Intervals(a), Predicate::Intervals(b)) => {
                let result = a.difference(b);
                if result.is_empty() {
                    Predicate::False
                } else {
                    Predicate::Intervals(result)
                }
            }
            (Predicate::Intervals(a), Predicate::LessThanEq(b)) => {
                let rhs = IntervalSet::new(vec![Interval::unbound_closed(b.clone())]);
                let result = a.difference(&rhs);
                if result.is_empty() {
                    Predicate::False
                } else {
                    Predicate::Intervals(result)
                }
            }
            // Record ∖ Record: subtract field-by-field.
            (Predicate::Record(m1), Predicate::Record(m2)) => Predicate::Record(
                m1.iter()
                    .map(|(k, p1)| (k.clone(), p1.minus(m2.get(k).unwrap_or(&Predicate::False))))
                    .collect(),
            ),
            // Or ∖ p: distribute the subtraction over each arm.
            (Predicate::Or(arms), _) => {
                Predicate::flatten_or(arms.iter().map(|a| a.minus(other)).collect())
            }
            (s, Predicate::Or(arms)) => {
                let mut res = s.clone();
                for arm in arms {
                    res = res.minus(arm);
                }
                res
            }
            // Union: subtract per variant.
            (Predicate::Union(ps), Predicate::Union(qs)) => {
                assert!(ps.same_tags(qs), "Union minus: arm sets differ");
                Predicate::Union(ps.map(|k, p| match qs.get(k) {
                    Some(q) => p.minus(q),
                    None => p.clone(),
                }))
            }
            _ => panic!("Cannot subtract incompatible predicates: {self:?} minus {other:?}"),
        }
    }

    /// Returns the predicate that admits exactly the values accepted by either `self` or `other`.
    pub fn union(&self, other: &Predicate) -> Predicate {
        match (self, other) {
            // True is the universal predicate: annihilator under union.
            (Predicate::True, _) | (_, Predicate::True) => Predicate::True,
            // False is the empty predicate: identity under union.
            (Predicate::False, p) | (p, Predicate::False) => p.clone(),
            // Two upper bounds: keep the looser (larger) one.
            (Predicate::LessThanEq(a), Predicate::LessThanEq(b)) => match a.partial_cmp(b) {
                Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal) => {
                    Predicate::LessThanEq(a.clone())
                }
                Some(std::cmp::Ordering::Less) => Predicate::LessThanEq(b.clone()),
                None => panic!("Cannot compare values in LessThanEq predicates: {a:?} and {b:?}"),
            },
            // Upper bound unioned with an interval set: merge (-∞, v] into the set.
            (Predicate::LessThanEq(v), Predicate::Intervals(s))
            | (Predicate::Intervals(s), Predicate::LessThanEq(v)) => {
                let upper = IntervalSet::new(vec![Interval::unbound_closed(v.clone())]);
                Predicate::Intervals(s.union(&upper))
            }
            // Two interval sets: standard set union.
            (Predicate::Intervals(a), Predicate::Intervals(b)) => Predicate::Intervals(a.union(b)),
            // Record predicates have AND semantics, so their union cannot be
            // represented as a single Record predicate.  Wrap in Or instead.
            (Predicate::Record(_), Predicate::Record(_)) => {
                Predicate::flatten_or(vec![self.clone(), other.clone()])
            }
            // Or: accumulate all arms, flattening nested Ors.
            (Predicate::Or(arms), _) => {
                let mut new_arms = arms.clone();
                new_arms.push(other.clone());
                Predicate::flatten_or(new_arms)
            }
            (_, Predicate::Or(arms)) => {
                let mut new_arms = vec![self.clone()];
                new_arms.extend(arms.iter().cloned());
                Predicate::flatten_or(new_arms)
            }
            // Union: union per variant.
            (Predicate::Union(ps), Predicate::Union(qs)) => {
                assert!(ps.same_tags(qs), "Union union: arm sets differ");
                Predicate::Union(ps.map(|k, p| match qs.get(k) {
                    Some(q) => p.union(q),
                    None => p.clone(),
                }))
            }
            _ => panic!("Cannot union incompatible predicates: {self:?} and {other:?}"),
        }
    }

    /// Returns `true` if `value` is admitted by this predicate.
    pub fn contains(&self, value: &Value) -> bool {
        match self {
            Predicate::True => true,
            Predicate::False => false,
            Predicate::LessThanEq(v) => value
                .partial_cmp(v)
                .map(|o| o != std::cmp::Ordering::Greater)
                .unwrap_or(false),
            Predicate::Intervals(s) => s.contains(value),
            Predicate::Record(m) => match value {
                Value::Record(fields) => m
                    .iter()
                    .all(|(k, p)| fields.get(k).map(|v| p.contains(v)).unwrap_or(false)),
                _ => false,
            },
            // Or: value is admitted if any arm admits it.
            Predicate::Or(arms) => arms.iter().any(|a| a.contains(value)),
            // Union: value is admitted if the per-variant predicate for its tag admits its inner value.
            Predicate::Union(ps) => match value {
                Value::Union { tag, inner } => ps.get(tag).is_some_and(|p| p.contains(inner)),
                _ => false,
            },
        }
    }

    /// Returns `true` if every value admitted by `other` is also admitted by `self`.
    ///
    /// In set terms: `other ⊆ self`.  Used by [`Predicate::flatten_or`] to
    /// eliminate redundant arms: if arm A subsumes arm B, B adds nothing to the
    /// union and can be dropped.
    pub fn subsumes(&self, other: &Predicate) -> bool {
        match (self, other) {
            // True is the universal set; it subsumes everything.
            (Predicate::True, _) => true,
            // A non-True predicate cannot subsume the universal set.
            (_, Predicate::True) => false,
            // Everything subsumes the empty set.
            (_, Predicate::False) => true,
            // The empty set subsumes nothing non-empty (non-empty handled above).
            (Predicate::False, _) => false,
            // Two upper bounds: (-∞,a] ⊇ (-∞,b] iff a >= b.
            (Predicate::LessThanEq(a), Predicate::LessThanEq(b)) => a
                .partial_cmp(b)
                .map(|o| o != std::cmp::Ordering::Less)
                .unwrap_or(false),
            // (-∞,v] subsumes an interval set iff every interval in s fits within (-∞,v].
            //
            // All interval-vs-interval containment uses `interval_set_covers`
            // rather than `.contains` directly — see that function for why.
            (Predicate::LessThanEq(v), Predicate::Intervals(s)) => {
                let upper = IntervalSet::new(vec![Interval::unbound_closed(v.clone())]);
                s.intervals()
                    .iter()
                    .all(|iv| interval_set_covers(&upper, iv))
            }
            // An interval set subsumes (-∞,v] only if it contains the whole half-line.
            (Predicate::Intervals(s), Predicate::LessThanEq(v)) => {
                interval_set_covers(s, &Interval::unbound_closed(v.clone()))
            }
            // Interval set containment: self ⊇ other iff every interval of other
            // is fully covered by self.
            (Predicate::Intervals(a), Predicate::Intervals(b)) => {
                b.intervals().iter().all(|iv| interval_set_covers(a, iv))
            }
            // Record (AND semantics): self ⊇ other iff every field of self subsumes
            // the corresponding field of other.
            (Predicate::Record(m1), Predicate::Record(m2)) if m1.len() == m2.len() => m1
                .iter()
                .all(|(k, p1)| m2.get(k).is_some_and(|p2| p1.subsumes(p2))),
            // A union subsumes `other` if any of its arms subsumes it.
            (Predicate::Or(arms), _) => arms.iter().any(|a| a.subsumes(other)),
            // self subsumes a union iff it subsumes every arm.
            (_, Predicate::Or(arms)) => arms.iter().all(|a| self.subsumes(a)),
            // Union: self ⊇ other iff every per-variant predicate of self subsumes
            // the corresponding variant of other.
            (Predicate::Union(ps), Predicate::Union(qs)) if ps.same_tags(qs) => {
                ps.zip_matching(qs).all(|(_, p, q)| p.subsumes(q))
            }
            // Incompatible variants (e.g. Record vs LessThanEq): conservative false.
            _ => false,
        }
    }

    /// Converts a batch of concrete domain values into the predicate admitting exactly those values.
    ///
    /// Each scalar value becomes a point interval; records are split field-by-field.
    pub(crate) fn from_column_value(cv: &ColumnValue) -> Predicate {
        match cv {
            // Unit is a single-value type; any Unit value satisfies the predicate.
            ColumnValue::Units(len) => {
                if *len > 0 {
                    Predicate::True
                } else {
                    Predicate::False
                }
            }
            ColumnValue::Ints(v) => vec_to_predicate(v),
            ColumnValue::UInts(v) => vec_to_predicate(v),
            ColumnValue::Bools(v) => {
                let mut vec = Vec::new();
                if v.count_ones() > 0 {
                    vec.push(true)
                }
                if v.count_zeros() > 0 {
                    vec.push(false)
                }
                vec_to_predicate(&vec)
            }
            ColumnValue::Strings(v) => vec_to_predicate(v),
            ColumnValue::Variants(v) => vec_to_predicate(v),
            ColumnValue::Records(fields) => {
                let len = fields.values().next().map_or(0, |cv| cv.len());
                if len == 0 {
                    return Predicate::False;
                }
                // Records have no natural total order, so we cannot represent
                // the set as intervals.  Instead, build one point predicate per
                // row and combine them with Or.
                Predicate::flatten_or(
                    (0..len)
                        .map(|i| {
                            Predicate::Record(
                                fields
                                    .iter()
                                    .map(|(k, cv)| {
                                        let single = cv.select_indices(std::iter::once(i), 1);
                                        (k.clone(), Predicate::from_column_value(&single))
                                    })
                                    .collect(),
                            )
                        })
                        .collect(),
                )
            }
            ColumnValue::FunctionBindings { .. } => {
                panic!("Cannot build predicate from FunctionBindings")
            }
            // Union domains: build one predicate per variant, tracking tags separately.
            ColumnValue::Union(arms) => {
                if arms.values().all(UnionArm::is_empty) {
                    return Predicate::False;
                }
                Predicate::Union(arms.map(|_, arm| Predicate::from_column_value(&arm.values)))
            }
        }
    }

    /// Check whether this predicate is structurally valid for the given [`Extent`].
    ///
    /// A predicate is applicable when it makes sense to use it as a filter over
    /// values drawn from that extent:
    ///
    /// - [`Predicate::True`] and [`Predicate::False`] are applicable to any extent.
    /// - [`Predicate::LessThanEq`] and [`Predicate::Intervals`] are applicable to
    ///   scalar extents ([`Extent::Base`], [`Extent::UIntRange`]) whose element type
    ///   matches the predicate's value type.
    /// - [`Predicate::Record`] is applicable to [`Extent::Record`] when the key sets
    ///   match and each field predicate is applicable to its field extent.
    /// - [`Predicate::Or`] is applicable when every arm is applicable to the extent.
    pub fn is_applicable_to(&self, extent: &Extent) -> bool {
        // Resolve transparent extent wrappers before matching.
        let extent = match extent {
            Extent::DataSourceDomain(src) => src.borrow().element_extent(),
            Extent::Restricted { base, .. } => *base.clone(),
            other => other.clone(),
        };
        match self {
            Predicate::True | Predicate::False => true,
            Predicate::LessThanEq(v) => value_matches_scalar_extent(v, &extent),
            Predicate::Intervals(s) => {
                // An empty interval set is semantically False — applicable everywhere.
                let Some(sample) = s
                    .intervals()
                    .first()
                    .and_then(|iv| iv.lval().or_else(|| iv.rval()))
                else {
                    return true;
                };
                value_matches_scalar_extent(sample, &extent)
            }
            Predicate::Record(pred_fields) => match &extent {
                Extent::Record(ext_fields) => {
                    pred_fields.len() == ext_fields.len()
                        && pred_fields
                            .iter()
                            .all(|(k, p)| ext_fields.get(k).is_some_and(|e| p.is_applicable_to(e)))
                }
                _ => false,
            },
            // Every arm must be applicable to the same extent.
            Predicate::Or(arms) => arms.iter().all(|p| p.is_applicable_to(&extent)),
            // Union: each per-variant predicate must be applicable to its variant extent.
            Predicate::Union(ps) => match &extent {
                // Width subtyping: the predicate may cover fewer arms than the
                // extent declares (the missing ones cannot occur), but every arm it
                // does cover must match that arm's extent.
                Extent::Union(ext_arms) => ps
                    .iter()
                    .all(|(k, p)| ext_arms.get(k).is_some_and(|e| p.is_applicable_to(e))),
                _ => false,
            },
        }
    }
}

/// Returns `true` if `set` fully covers `iv` — i.e., every point in `iv` is also in `set`.
///
/// This is the safe replacement for `set.contains(iv)` / `outer_interval.contains(iv)`.
/// The `intervalsets` crate has a bug in `HalfBounded::contains(&HalfBounded)`:
/// it checks `self.contains(rhs.bound.value())`, which asks whether the bound *point*
/// is inside `self`.  For equal open bounds this is wrong: `(-∞,1).contains((-∞,1))`
/// asks `1 < 1 = false`, but `(-∞,1) ⊆ (-∞,1)` is obviously true.
///
/// Using `iv.difference(set).is_empty()` is equivalent and does not go through
/// the buggy code path.  All interval-vs-interval containment checks must use
/// this helper instead of calling `.contains` directly.
fn interval_set_covers(set: &IntervalSet<Value>, iv: &Interval<Value>) -> bool {
    iv.difference(set).is_empty()
}

/// Returns `true` if `v`'s runtime type is consistent with `extent`'s element type.
///
/// Used by [`Predicate::is_applicable_to`] to verify that scalar predicates
/// ([`Predicate::LessThanEq`], [`Predicate::Intervals`]) are paired with a
/// matching scalar extent.  `Unit` is excluded because predicates over a single-
/// valued type are always `True`/`False` — no scalar predicate is ever created
/// for a Unit column.
fn value_matches_scalar_extent(v: &Value, extent: &Extent) -> bool {
    matches!(
        (v, extent),
        (Value::Int(_), Extent::Base(BaseType::Int))
            | (Value::UInt(_), Extent::Base(BaseType::UInt))
            | (Value::UInt(_), Extent::UIntRange(_))
            | (Value::Bool(_), Extent::Base(BaseType::Bool))
            | (Value::String(_), Extent::Base(BaseType::String))
    )
}

/// Converts a slice of values into a `Predicate::Intervals` with adjacent discrete values merged
/// into contiguous ranges.
///
/// `IntervalSet::new` has a fast-path that skips `merge_sorted` when intervals are already sorted
/// and non-overlapping — which point intervals always are. By sorting the values ourselves and
/// explicitly extending runs of adjacent discrete values, we produce a minimal interval set.
fn vec_to_predicate<T: Clone>(data: &[T]) -> Predicate
where
    Value: From<T>,
{
    if data.is_empty() {
        return Predicate::False;
    }

    // Sort and deduplicate so we can do a single linear scan for adjacent runs.
    let mut vals: Vec<Value> = data.iter().map(|x| Value::from(x.clone())).collect();
    vals.sort_by(|a, b| {
        a.partial_cmp(b)
            .expect("values in a ColumnValue column must be mutually comparable")
    });
    vals.dedup();

    // Walk the sorted values, extending the current interval whenever the next value
    // is the immediate successor of the current end.
    let mut intervals: Vec<Interval<Value>> = Vec::new();
    let mut start = vals[0].clone();
    let mut end = vals[0].clone();
    for v in &vals[1..] {
        if end.try_adjacent(Side::Right).as_ref() == Some(v) {
            end = v.clone();
        } else {
            intervals.push(Interval::closed(start, end));
            start = v.clone();
            end = v.clone();
        }
    }
    intervals.push(Interval::closed(start, end));

    // Intervals are already sorted and merged, so skip the invariant check.
    Predicate::Intervals(IntervalSet::new_unchecked(intervals))
}

/// Sort a `Tile::SealedFunction` by its domain values for deterministic comparison.
///
/// Handles `Ints` and `UInts` domains paired with `Scalar(Ints)` codomains; all
/// other tile forms are returned unchanged.  This is needed wherever key order
/// depends on [`HashMap`] iteration order (e.g. GroupBy, MapSource).
pub fn sort_sealed_function_by_domain(tile: Tile) -> Tile {
    /// Sort parallel `domain` and `cod_ints` vectors together by `domain` key,
    /// then rebuild the tile.
    fn sort_and_rebuild<K: PartialOrd + Clone>(
        domain_vals: Vec<K>,
        cod_ints: Vec<i64>,
        domain_predicate: Predicate,
        mk_domain: impl Fn(Vec<K>) -> ColumnValue,
    ) -> Tile {
        let mut pairs: Vec<(K, i64)> = domain_vals.into_iter().zip(cod_ints).collect();
        pairs.sort_by(|(a, _), (b, _)| a.partial_cmp(b).unwrap());
        let (sorted_d, sorted_c): (Vec<K>, Vec<i64>) = pairs.into_iter().unzip();
        Tile::SealedFunction {
            domain: mk_domain(sorted_d),
            codomain: Box::new(Tile::Scalar(ColumnValue::Ints(sorted_c))),
            domain_predicate,
            deleted: BitSet::new(),
        }
    }

    fn record_cv_to_extent(fields: &HashMap<String, ColumnValue>) -> Extent {
        Extent::Record(transform_hashmap_values(fields, |cv| match cv {
            ColumnValue::UInts(_) => Extent::Base(BaseType::UInt),
            ColumnValue::Records(inner) => record_cv_to_extent(inner),
            _ => todo!(),
        }))
    }

    match tile {
        Tile::SealedFunction {
            domain,
            codomain,
            domain_predicate,
            deleted,
        } => match (*codomain, domain) {
            (Tile::Scalar(ColumnValue::Ints(cod_ints)), ColumnValue::Ints(dom)) => {
                sort_and_rebuild(dom, cod_ints, domain_predicate, ColumnValue::Ints)
            }
            (Tile::Scalar(ColumnValue::Ints(cod_ints)), ColumnValue::UInts(dom)) => {
                sort_and_rebuild(dom, cod_ints, domain_predicate, ColumnValue::UInts)
            }
            (
                Tile::Scalar(ColumnValue::Ints(cod_ints)),
                ref r @ ColumnValue::Records(ref fields),
            ) => sort_and_rebuild(
                r.clone().drain_to_value_iter().collect(),
                cod_ints,
                domain_predicate,
                |v| ColumnValue::from_values(v, &record_cv_to_extent(fields)),
            ),
            // Union domain: canonicalize entries by `(tag, slot)` so two tiles
            // representing the same multiset of `(tag, payload) → cod` entries
            // compare equal regardless of the order the arms happened to be
            // drained in.
            //
            // The arm-keyed column already *stores* that pair — arms are in
            // canonical tag order and each arm's rows ascend by slot — so
            // concatenating the arms in order **is** the canonical sequence, and
            // the codomain just follows the same permutation.
            (Tile::Scalar(ColumnValue::Ints(cod_ints)), ColumnValue::Union(arms)) => {
                let mut sorted_cod: Vec<i64> = Vec::with_capacity(cod_ints.len());
                let mut next_row = 0usize;
                let canonical = arms.map(|_, arm| {
                    for &row in &arm.rows {
                        sorted_cod.push(cod_ints[row]);
                    }
                    let rows: Vec<usize> = (next_row..next_row + arm.len()).collect();
                    next_row += arm.len();
                    UnionArm::new(rows, arm.values.clone())
                });
                let domain = ColumnValue::Union(canonical);
                domain.debug_assert_union_invariants();
                Tile::SealedFunction {
                    domain,
                    codomain: Box::new(Tile::Scalar(ColumnValue::Ints(sorted_cod))),
                    domain_predicate,
                    deleted: BitSet::new(),
                }
            }
            (other_codomain, domain) => Tile::SealedFunction {
                domain,
                codomain: Box::new(other_codomain),
                domain_predicate,
                deleted,
            },
        },
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use crate::ccl::FieldKey;
    use bit_vec::BitVec;
    use intervalsets::ops::Contains;

    use super::*;
    use crate::interpreter::{
        BaseType, ColumnValue, Extent, Value,
        tiling::tests::{bool_ext, int, range},
    };

    // ── helpers ───────────────────────────────────────────────────────────────

    fn record_pred(fields: &[(&str, Predicate)]) -> Predicate {
        Predicate::Record(
            fields
                .iter()
                .map(|(k, v)| (k.to_string(), v.clone()))
                .collect(),
        )
    }

    // ── Predicate::as_bool ────────────────────────────────────────────────────

    #[test]
    fn predicate_as_bool_true() {
        assert_eq!(Predicate::True.as_bool(), Some(true));
    }

    #[test]
    fn predicate_as_bool_false() {
        assert_eq!(Predicate::False.as_bool(), Some(false));
    }

    #[test]
    fn predicate_as_bool_less_than_eq_is_none() {
        assert_eq!(Predicate::LessThanEq(Value::Int(5)).as_bool(), None);
    }

    #[test]
    fn predicate_as_bool_record_all_true() {
        let p = record_pred(&[("a", Predicate::True), ("b", Predicate::True)]);
        assert_eq!(p.as_bool(), Some(true));
    }

    #[test]
    fn predicate_as_bool_record_all_false() {
        let p = record_pred(&[("a", Predicate::False), ("b", Predicate::False)]);
        assert_eq!(p.as_bool(), Some(false));
    }

    #[test]
    fn predicate_as_bool_record_mixed_is_none() {
        let p = record_pred(&[("a", Predicate::True), ("b", Predicate::False)]);
        assert_eq!(p.as_bool(), None);
    }

    #[test]
    fn predicate_as_bool_nonempty_intervals_is_none() {
        // A non-trivial interval set has no boolean representation.
        let p = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3]));
        assert_eq!(p.as_bool(), None);
    }

    #[test]
    fn predicate_as_bool_empty_interval_set_is_false() {
        // Directly constructing Intervals(∅): from_column_value on empty input
        // produces Predicate::False, but interval arithmetic can produce Intervals(∅).
        let empty: IntervalSet<Value> = IntervalSet::new(vec![]);
        assert_eq!(Predicate::Intervals(empty).as_bool(), Some(false));
    }

    // ── Predicate::is_true / is_false ─────────────────────────────────────────

    #[test]
    fn predicate_is_true_for_true_variant() {
        assert!(Predicate::True.is_true());
    }

    #[test]
    fn predicate_is_true_false_for_false_variant() {
        assert!(!Predicate::False.is_true());
    }

    #[test]
    fn predicate_is_true_false_for_none_case() {
        // LessThanEq has no boolean representation — is_true returns false.
        assert!(!Predicate::LessThanEq(Value::Int(5)).is_true());
    }

    #[test]
    fn predicate_is_false_for_false_variant() {
        assert!(Predicate::False.is_false());
    }

    #[test]
    fn predicate_is_false_false_for_true_variant() {
        assert!(!Predicate::True.is_false());
    }

    #[test]
    fn predicate_is_false_false_for_none_case() {
        // LessThanEq has no boolean representation — is_false returns false.
        assert!(!Predicate::LessThanEq(Value::Int(5)).is_false());
    }

    // ── Predicate::intersect ──────────────────────────────────────────────────

    #[test]
    fn predicate_intersect_true_is_identity() {
        assert_eq!(
            Predicate::True.intersect(&Predicate::LessThanEq(Value::Int(3))),
            Predicate::LessThanEq(Value::Int(3))
        );
        assert_eq!(
            Predicate::LessThanEq(Value::Int(3)).intersect(&Predicate::True),
            Predicate::LessThanEq(Value::Int(3))
        );
    }

    #[test]
    fn predicate_intersect_false_is_annihilator() {
        assert_eq!(
            Predicate::False.intersect(&Predicate::True),
            Predicate::False
        );
        assert_eq!(
            Predicate::LessThanEq(Value::Int(3)).intersect(&Predicate::False),
            Predicate::False
        );
    }

    #[test]
    fn predicate_intersect_less_than_eq_picks_tighter() {
        // min(5, 3) → LessThanEq(3)
        assert_eq!(
            Predicate::LessThanEq(Value::Int(5)).intersect(&Predicate::LessThanEq(Value::Int(3))),
            Predicate::LessThanEq(Value::Int(3))
        );
        // min(3, 5) → LessThanEq(3)
        assert_eq!(
            Predicate::LessThanEq(Value::Int(3)).intersect(&Predicate::LessThanEq(Value::Int(5))),
            Predicate::LessThanEq(Value::Int(3))
        );
    }

    #[test]
    fn predicate_intersect_record_field_by_field() {
        let p1 = record_pred(&[("a", Predicate::True), ("b", Predicate::False)]);
        let p2 = record_pred(&[("a", Predicate::False), ("b", Predicate::True)]);
        let result = p1.intersect(&p2);
        let Predicate::Record(m) = result else {
            panic!("expected Record predicate");
        };
        assert_eq!(m["a"], Predicate::False);
        assert_eq!(m["b"], Predicate::False);
    }

    // ── Predicate::from_column_value ─────────────────────────────────────────

    #[test]
    fn from_column_value_empty_ints_is_false() {
        assert_eq!(
            Predicate::from_column_value(&ColumnValue::Ints(vec![])),
            Predicate::False
        );
    }

    #[test]
    fn from_column_value_single_int() {
        let p = Predicate::from_column_value(&ColumnValue::Ints(vec![7]));
        let Predicate::Intervals(s) = p else {
            panic!("expected Intervals");
        };
        // The single point [7, 7] should contain 7 but not 6 or 8.
        assert!(s.contains(&Value::Int(7)));
        assert!(!s.contains(&Value::Int(6)));
        assert!(!s.contains(&Value::Int(8)));
    }

    #[test]
    fn from_column_value_multiple_ints_contains_all() {
        let p = Predicate::from_column_value(&ColumnValue::Ints(vec![1, 3, 5]));
        let Predicate::Intervals(s) = p else {
            panic!("expected Intervals");
        };
        assert!(s.contains(&Value::Int(1)));
        assert!(s.contains(&Value::Int(3)));
        assert!(s.contains(&Value::Int(5)));
        assert!(!s.contains(&Value::Int(2)));
        assert!(!s.contains(&Value::Int(4)));
    }

    #[test]
    fn from_column_value_uints() {
        let p = Predicate::from_column_value(&ColumnValue::UInts(vec![0, 2]));
        let Predicate::Intervals(s) = p else {
            panic!("expected Intervals");
        };
        assert!(s.contains(&Value::UInt(0)));
        assert!(s.contains(&Value::UInt(2)));
        assert!(!s.contains(&Value::UInt(1)));
    }

    #[test]
    fn from_column_value_compact() {
        let p = Predicate::from_column_value(&ColumnValue::UInts(vec![0, 1, 2, 5, 6, 7]));
        let Predicate::Intervals(s) = p else {
            panic!("expected Intervals");
        };
        assert_eq!(s.intervals().len(), 2, "{s:?}");
    }

    #[test]
    fn from_column_value_empty_uints_is_false() {
        assert_eq!(
            Predicate::from_column_value(&ColumnValue::UInts(vec![])),
            Predicate::False
        );
    }

    #[test]
    fn from_column_value_bools_both_values() {
        let mut bv = BitVec::from_elem(2, false);
        bv.set(0, true);
        bv.set(1, false);
        let p = Predicate::from_column_value(&ColumnValue::Bools(bv));
        let Predicate::Intervals(s) = p else {
            panic!("expected Intervals");
        };
        assert!(s.contains(&Value::Bool(true)));
        assert!(s.contains(&Value::Bool(false)));
    }

    #[test]
    fn from_column_value_bools_only_true() {
        let bv = BitVec::from_elem(3, true);
        let p = Predicate::from_column_value(&ColumnValue::Bools(bv));
        let Predicate::Intervals(s) = p else {
            panic!("expected Intervals");
        };
        assert!(s.contains(&Value::Bool(true)));
        assert!(!s.contains(&Value::Bool(false)));
    }

    #[test]
    fn from_column_value_empty_bools_is_false() {
        assert_eq!(
            Predicate::from_column_value(&ColumnValue::Bools(BitVec::new())),
            Predicate::False
        );
    }

    #[test]
    fn from_column_value_units_nonempty_is_true() {
        assert_eq!(
            Predicate::from_column_value(&ColumnValue::Units(3)),
            Predicate::True
        );
    }

    #[test]
    fn from_column_value_units_empty_is_false() {
        assert_eq!(
            Predicate::from_column_value(&ColumnValue::Units(0)),
            Predicate::False
        );
    }

    // ── Predicate::split_record ───────────────────────────────────────────────

    #[test]
    fn split_record_true_broadcasts() {
        let fields: HashMap<String, ()> = [("x", ()), ("y", ())]
            .iter()
            .map(|(k, v)| (k.to_string(), *v))
            .collect();
        let result = Predicate::True.split_record(&fields);
        assert_eq!(result["x"], Predicate::True);
        assert_eq!(result["y"], Predicate::True);
    }

    #[test]
    fn split_record_false_broadcasts() {
        let fields: HashMap<String, ()> = [("a", ())]
            .iter()
            .map(|(k, v)| (k.to_string(), *v))
            .collect();
        let result = Predicate::False.split_record(&fields);
        assert_eq!(result["a"], Predicate::False);
    }

    #[test]
    fn split_record_record_returns_its_own_fields() {
        let fields: HashMap<String, ()> = [("a", ()), ("b", ())]
            .iter()
            .map(|(k, v)| (k.to_string(), *v))
            .collect();
        let p = record_pred(&[("a", Predicate::True), ("b", Predicate::False)]);
        let result = p.split_record(&fields);
        assert_eq!(result["a"], Predicate::True);
        assert_eq!(result["b"], Predicate::False);
    }

    // ── Predicate::union ──────────────────────────────────────────────────────

    /// Helper: assert that a `Predicate::Intervals` contains / does not contain a value.
    fn intervals_contains(p: &Predicate, v: Value) -> bool {
        let Predicate::Intervals(s) = p else {
            panic!("expected Predicate::Intervals, got {p:?}");
        };
        s.contains(&v)
    }

    // True is the annihilator: True ∪ x = True and x ∪ True = True.
    #[test]
    fn union_true_annihilates_lhs() {
        assert_eq!(
            Predicate::True.union(&Predicate::LessThanEq(Value::UInt(5))),
            Predicate::True
        );
    }

    #[test]
    fn union_true_annihilates_rhs() {
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(5)).union(&Predicate::True),
            Predicate::True
        );
    }

    // False is the identity: False ∪ x = x and x ∪ False = x.
    #[test]
    fn union_false_identity_lhs() {
        let p = Predicate::LessThanEq(Value::UInt(3));
        assert_eq!(Predicate::False.union(&p), p);
    }

    #[test]
    fn union_false_identity_rhs() {
        let p = Predicate::LessThanEq(Value::UInt(3));
        assert_eq!(p.union(&Predicate::False), p);
    }

    // LessThanEq ∪ LessThanEq: keep the looser (larger) bound.
    #[test]
    fn union_less_than_eq_keeps_larger() {
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(7)).union(&Predicate::LessThanEq(Value::UInt(3))),
            Predicate::LessThanEq(Value::UInt(7))
        );
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(3)).union(&Predicate::LessThanEq(Value::UInt(7))),
            Predicate::LessThanEq(Value::UInt(7))
        );
    }

    #[test]
    fn union_less_than_eq_equal_bounds() {
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(5)).union(&Predicate::LessThanEq(Value::UInt(5))),
            Predicate::LessThanEq(Value::UInt(5))
        );
    }

    // LessThanEq ∪ Intervals: result is Intervals containing a left-unbounded interval.
    #[test]
    fn union_less_than_eq_with_intervals_lhs() {
        // (-∞, 3] ∪ {7} → Intervals containing both 0, 3, and 7; but not 4 or 6.
        let intervals = Predicate::from_column_value(&ColumnValue::UInts(vec![7]));
        let result = Predicate::LessThanEq(Value::UInt(3)).union(&intervals);
        assert!(intervals_contains(&result, Value::UInt(0)), "0 in (-inf,3]");
        assert!(intervals_contains(&result, Value::UInt(3)), "3 in (-inf,3]");
        assert!(
            !intervals_contains(&result, Value::UInt(4)),
            "4 not in result"
        );
        assert!(
            intervals_contains(&result, Value::UInt(7)),
            "7 in point set"
        );
    }

    #[test]
    fn union_less_than_eq_with_intervals_rhs() {
        // {7} ∪ (-∞, 3] — commutative, same outcome.
        let intervals = Predicate::from_column_value(&ColumnValue::UInts(vec![7]));
        let result = intervals.union(&Predicate::LessThanEq(Value::UInt(3)));
        assert!(intervals_contains(&result, Value::UInt(3)));
        assert!(!intervals_contains(&result, Value::UInt(4)));
        assert!(intervals_contains(&result, Value::UInt(7)));
    }

    // Intervals ∪ Intervals: standard set union.
    #[test]
    fn union_disjoint_interval_sets() {
        // {1, 2} ∪ {5, 6} → values 1, 2, 5, 6 present; 3, 4 absent.
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2]));
        let b = Predicate::from_column_value(&ColumnValue::UInts(vec![5, 6]));
        let result = a.union(&b);
        for v in [1usize, 2, 5, 6] {
            assert!(
                intervals_contains(&result, Value::UInt(v)),
                "{v} should be in union"
            );
        }
        for v in [3usize, 4] {
            assert!(
                !intervals_contains(&result, Value::UInt(v)),
                "{v} should not be in union"
            );
        }
    }

    #[test]
    fn union_overlapping_interval_sets_merges() {
        // {2, 3, 4} ∪ {3, 4, 5} → {2, 3, 4, 5}, all present.
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![2, 3, 4]));
        let b = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 4, 5]));
        let result = a.union(&b);
        for v in [2usize, 3, 4, 5] {
            assert!(intervals_contains(&result, Value::UInt(v)));
        }
    }

    // Record ∪ Record: cannot push OR through AND, result must be Or([r1, r2]).
    #[test]
    fn union_record_predicates_produces_or() {
        // Neither record subsumes the other: r1 is looser on x, r2 is looser on y.
        // r1 admits {x≤5, y≤3}; r2 admits {x≤3, y≤7}.  Each admits records the
        // other does not, so neither is redundant and the union must be an Or.
        let r1 = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(5))),
            ("y", Predicate::LessThanEq(Value::UInt(3))),
        ]);
        let r2 = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(3))),
            ("y", Predicate::LessThanEq(Value::UInt(7))),
        ]);
        let result = r1.union(&r2);
        // Must be an Or — OR cannot be pushed through AND for records.
        assert!(
            matches!(result, Predicate::Or(_)),
            "expected Or, got {result:?}"
        );
        assert_eq!(result.as_bool(), None); // non-trivial
    }

    // Predicate::Or::contains: satisfied when any arm matches, regardless of the others.
    #[test]
    fn or_contains_any_arm_matches() {
        // Or([{a: ≤10}, {b: ≤10}]):
        //   - {a:5, b:20}  → first arm matches (5≤10, b unconstrained in first arm)? No —
        //     Record semantics require ALL fields. So first arm is {a:≤10} only;
        //     use single-field records to keep the test unambiguous.
        // Or([{_0: ≤10}, {_1: ≤10}]):
        //   - {_0:5,  _1:20} → first arm:  5≤10 ✓, _1 absent in arm → only _0 checked → true
        //   - {_0:20, _1:5}  → second arm: 5≤10 ✓                                     → true
        //   - {_0:20, _1:20} → neither arm                                             → false
        let pred = Predicate::Or(vec![
            record_pred(&[("_0", Predicate::LessThanEq(Value::UInt(10)))]),
            record_pred(&[("_1", Predicate::LessThanEq(Value::UInt(10)))]),
        ]);

        let only_first = Value::Record(HashMap::from([
            ("_0".to_string(), Value::UInt(5)),
            ("_1".to_string(), Value::UInt(20)),
        ]));
        let only_second = Value::Record(HashMap::from([
            ("_0".to_string(), Value::UInt(20)),
            ("_1".to_string(), Value::UInt(5)),
        ]));
        let neither = Value::Record(HashMap::from([
            ("_0".to_string(), Value::UInt(20)),
            ("_1".to_string(), Value::UInt(20)),
        ]));

        assert!(
            pred.contains(&only_first),
            "{only_first:?} should match the first arm"
        );
        assert!(
            pred.contains(&only_second),
            "{only_second:?} should match the second arm"
        );
        assert!(!pred.contains(&neither), "{neither:?} should match no arm");
    }

    #[test]
    fn union_record_or_is_empty_when_both_arms_empty() {
        // Both records are all-False, so the Or is effectively empty.
        let r1 = record_pred(&[("a", Predicate::False), ("b", Predicate::False)]);
        let r2 = record_pred(&[("a", Predicate::False), ("b", Predicate::False)]);
        let result = r1.union(&r2);
        assert_eq!(result.as_bool(), Some(false));
    }

    // ── Predicate::subsumes ───────────────────────────────────────────────────

    // True subsumes everything; nothing other than True subsumes True.
    #[test]
    fn subsumes_true_subsumes_all() {
        assert!(Predicate::True.subsumes(&Predicate::True));
        assert!(Predicate::True.subsumes(&Predicate::False));
        assert!(Predicate::True.subsumes(&Predicate::LessThanEq(Value::UInt(5))));
    }

    #[test]
    fn subsumes_non_true_does_not_subsume_true() {
        assert!(!Predicate::False.subsumes(&Predicate::True));
        assert!(!Predicate::LessThanEq(Value::UInt(5)).subsumes(&Predicate::True));
    }

    // False (empty set) is subsumed by everything; it only subsumes itself.
    #[test]
    fn subsumes_everything_subsumes_false() {
        assert!(Predicate::False.subsumes(&Predicate::False));
        assert!(Predicate::True.subsumes(&Predicate::False));
        assert!(Predicate::LessThanEq(Value::UInt(0)).subsumes(&Predicate::False));
    }

    #[test]
    fn subsumes_false_does_not_subsume_nonempty() {
        assert!(!Predicate::False.subsumes(&Predicate::True));
        assert!(!Predicate::False.subsumes(&Predicate::LessThanEq(Value::UInt(3))));
    }

    // LessThanEq: (-∞,a] ⊇ (-∞,b] iff a >= b.
    #[test]
    fn subsumes_less_than_eq_looser_subsumes_tighter() {
        assert!(
            Predicate::LessThanEq(Value::UInt(7)).subsumes(&Predicate::LessThanEq(Value::UInt(3)))
        );
    }

    #[test]
    fn subsumes_less_than_eq_equal_bounds() {
        assert!(
            Predicate::LessThanEq(Value::UInt(5)).subsumes(&Predicate::LessThanEq(Value::UInt(5)))
        );
    }

    #[test]
    fn subsumes_less_than_eq_tighter_does_not_subsume_looser() {
        assert!(
            !Predicate::LessThanEq(Value::UInt(3)).subsumes(&Predicate::LessThanEq(Value::UInt(7)))
        );
    }

    // LessThanEq vs Intervals.
    #[test]
    fn subsumes_less_than_eq_subsumes_contained_interval_set() {
        // (-∞,10] ⊇ {3,7}: both points are <= 10.
        let s = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 7]));
        assert!(Predicate::LessThanEq(Value::UInt(10)).subsumes(&s));
    }

    #[test]
    fn subsumes_less_than_eq_does_not_subsume_escaping_interval_set() {
        // (-∞,5] ⊉ {3,7}: 7 > 5.
        let s = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 7]));
        assert!(!Predicate::LessThanEq(Value::UInt(5)).subsumes(&s));
    }

    #[test]
    fn subsumes_interval_set_does_not_subsume_less_than_eq() {
        // {3,7} ⊉ (-∞,10]: the half-line is unbounded, the set is finite.
        let s = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 7]));
        assert!(!s.subsumes(&Predicate::LessThanEq(Value::UInt(10))));
    }

    // Intervals vs Intervals.
    #[test]
    fn subsumes_interval_superset_subsumes_subset() {
        // {1,2,3,4} ⊇ {2,3}.
        let big = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3, 4]));
        let small = Predicate::from_column_value(&ColumnValue::UInts(vec![2, 3]));
        assert!(big.subsumes(&small));
        assert!(!small.subsumes(&big));
    }

    #[test]
    fn subsumes_equal_interval_sets() {
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3]));
        let b = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3]));
        assert!(a.subsumes(&b));
        assert!(b.subsumes(&a));
    }

    #[test]
    fn subsumes_disjoint_interval_sets_neither_subsumes() {
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2]));
        let b = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 4]));
        assert!(!a.subsumes(&b));
        assert!(!b.subsumes(&a));
    }

    // Record: field-by-field AND semantics.
    #[test]
    fn subsumes_record_field_by_field() {
        // {x: ≤10, y: ≤10} ⊇ {x: ≤5, y: ≤3}: both fields are looser in self.
        let big = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(10))),
            ("y", Predicate::LessThanEq(Value::UInt(10))),
        ]);
        let small = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(5))),
            ("y", Predicate::LessThanEq(Value::UInt(3))),
        ]);
        assert!(big.subsumes(&small));
        assert!(!small.subsumes(&big));
    }

    #[test]
    fn subsumes_record_incomparable_fields() {
        // {x: ≤5, y: ≤10}: x-field is tighter than r2, y-field is looser.
        // Neither record subsumes the other.
        let r1 = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(5))),
            ("y", Predicate::LessThanEq(Value::UInt(10))),
        ]);
        let r2 = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(10))),
            ("y", Predicate::LessThanEq(Value::UInt(5))),
        ]);
        assert!(!r1.subsumes(&r2));
        assert!(!r2.subsumes(&r1));
    }

    #[test]
    fn subsumes_record_with_true_field_subsumes_anything_in_that_field() {
        // {x: True, y: ≤3} ⊇ {x: ≤7, y: ≤3}: True subsumes any x predicate.
        let big = record_pred(&[
            ("x", Predicate::True),
            ("y", Predicate::LessThanEq(Value::UInt(3))),
        ]);
        let small = record_pred(&[
            ("x", Predicate::LessThanEq(Value::UInt(7))),
            ("y", Predicate::LessThanEq(Value::UInt(3))),
        ]);
        assert!(big.subsumes(&small));
        assert!(!small.subsumes(&big));
    }

    // Or: union subsumes `other` if any arm does; self subsumes a union iff it
    // subsumes every arm.
    #[test]
    fn subsumes_or_any_arm_suffices() {
        // Or([≤3, ≤10]) ⊇ ≤5 because the ≤10 arm already covers it.
        let or_pred =
            Predicate::LessThanEq(Value::UInt(3)).union(&Predicate::LessThanEq(Value::UInt(10)));
        // union of two LessThanEqs collapses to just LessThanEq(10), so
        // construct an Or via Record union to exercise the Or path.
        let arm_a = record_pred(&[("x", Predicate::LessThanEq(Value::UInt(10)))]);
        let arm_b = record_pred(&[("x", Predicate::LessThanEq(Value::UInt(3)))]);
        let or_rec = arm_a.union(&arm_b); // Or([arm_a, arm_b]) simplified to [arm_a]
        let target = record_pred(&[("x", Predicate::LessThanEq(Value::UInt(5)))]);
        assert!(or_pred.subsumes(&Predicate::LessThanEq(Value::UInt(5))));
        assert!(or_rec.subsumes(&target));
    }

    #[test]
    fn subsumes_value_must_subsume_all_or_arms() {
        // ≤10 ⊇ Or([≤3, ≤7]) because 10 >= both 3 and 7.
        let or_pred =
            Predicate::LessThanEq(Value::UInt(3)).union(&Predicate::LessThanEq(Value::UInt(7)));
        assert!(Predicate::LessThanEq(Value::UInt(10)).subsumes(&or_pred));
    }

    #[test]
    fn subsumes_value_does_not_subsume_or_if_any_arm_escapes() {
        // ≤5 ⊉ Or([≤3, ≤7]) because the ≤7 arm extends beyond 5.
        let or_pred =
            Predicate::LessThanEq(Value::UInt(3)).union(&Predicate::LessThanEq(Value::UInt(7)));
        assert!(!Predicate::LessThanEq(Value::UInt(5)).subsumes(&or_pred));
    }

    #[test]
    fn subsumes_record_with_interval_and_true_field_subsumes_itself() {
        // Record({"_0": Intervals((-∞,1)), "_1": True}) should subsume itself,
        // and unioning it with itself should collapse back to the original predicate
        // rather than producing Or([pred, pred]).
        let pred = record_pred(&[
            (
                "_0",
                Predicate::Intervals(IntervalSet::new(vec![Interval::unbound_open(Value::UInt(
                    1,
                ))])),
            ),
            ("_1", Predicate::True),
        ]);
        assert!(pred.subsumes(&pred), "a predicate must subsume itself");
        let union_result = pred.union(&pred);
        assert_eq!(
            union_result, pred,
            "unioning a predicate with itself should return the same predicate, got {union_result:?}"
        );
    }

    // ── Predicate::minus ─────────────────────────────────────────────────────

    #[test]
    fn minus_p_minus_false_is_identity() {
        let p = Predicate::LessThanEq(Value::UInt(5));
        assert_eq!(p.minus(&Predicate::False), p.clone());
        assert_eq!(Predicate::True.minus(&Predicate::False), Predicate::True);
        assert_eq!(Predicate::False.minus(&Predicate::False), Predicate::False);
    }

    #[test]
    fn minus_p_minus_true_is_false() {
        assert_eq!(
            Predicate::LessThanEq(Value::UInt(5)).minus(&Predicate::True),
            Predicate::False
        );
        assert_eq!(Predicate::True.minus(&Predicate::True), Predicate::False);
    }

    #[test]
    fn minus_false_minus_anything_is_false() {
        assert_eq!(
            Predicate::False.minus(&Predicate::LessThanEq(Value::UInt(5))),
            Predicate::False
        );
        assert_eq!(Predicate::False.minus(&Predicate::True), Predicate::False);
    }

    #[test]
    fn minus_intervals_minus_overlapping_intervals_removes_overlap() {
        // {[1,5]} ∖ {[2,3]} = {[1,1]} ∪ {[4,5]}
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3, 4, 5]));
        let b = Predicate::from_column_value(&ColumnValue::UInts(vec![2, 3]));
        let result = a.minus(&b);
        assert!(result.contains(&Value::UInt(1)));
        assert!(!result.contains(&Value::UInt(2)));
        assert!(!result.contains(&Value::UInt(3)));
        assert!(result.contains(&Value::UInt(4)));
        assert!(result.contains(&Value::UInt(5)));
    }

    #[test]
    fn minus_intervals_minus_superset_is_false() {
        // {[1,2]} ∖ {[1,3]} = ∅
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2]));
        let b = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3]));
        assert_eq!(a.minus(&b), Predicate::False);
    }

    #[test]
    fn minus_intervals_minus_disjoint_is_unchanged() {
        // {[1,3]} ∖ {[5,7]} = {[1,3]}
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3]));
        let b = Predicate::from_column_value(&ColumnValue::UInts(vec![5, 6, 7]));
        let result = a.minus(&b);
        assert!(result.contains(&Value::UInt(1)));
        assert!(result.contains(&Value::UInt(3)));
        assert!(!result.contains(&Value::UInt(5)));
    }

    #[test]
    fn minus_intervals_minus_less_than_eq() {
        // {[1,5]} ∖ (-∞,3] = {[4,5]}
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3, 4, 5]));
        let result = a.minus(&Predicate::LessThanEq(Value::UInt(3)));
        assert!(!result.contains(&Value::UInt(1)));
        assert!(!result.contains(&Value::UInt(3)));
        assert!(result.contains(&Value::UInt(4)));
        assert!(result.contains(&Value::UInt(5)));
        assert!(!result.contains(&Value::UInt(6)));
    }

    #[test]
    fn minus_less_than_eq_minus_intervals_removes_overlap() {
        // (-∞,10] ∖ {[3,5]} = (-∞,2] ∪ {[6,10]}
        let intervals = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 4, 5]));
        let result = Predicate::LessThanEq(Value::UInt(10)).minus(&intervals);
        assert!(result.contains(&Value::UInt(1)));
        assert!(!result.contains(&Value::UInt(3)));
        assert!(!result.contains(&Value::UInt(5)));
        assert!(result.contains(&Value::UInt(6)));
        assert!(result.contains(&Value::UInt(10)));
        assert!(!result.contains(&Value::UInt(11)));
    }

    #[test]
    fn minus_less_than_eq_minus_same_is_false() {
        // (-∞,5] ∖ (-∞,5] = ∅
        let p = Predicate::LessThanEq(Value::UInt(5));
        assert_eq!(p.minus(&p.clone()), Predicate::False);
    }

    #[test]
    fn minus_less_than_eq_minus_smaller_is_open_interval() {
        // (-∞,5] ∖ (-∞,3] = (3,5] — contains 4, 5 but not 3 or 6.
        let result =
            Predicate::LessThanEq(Value::UInt(5)).minus(&Predicate::LessThanEq(Value::UInt(3)));
        assert!(!result.contains(&Value::UInt(3)));
        assert!(result.contains(&Value::UInt(4)));
        assert!(result.contains(&Value::UInt(5)));
        assert!(!result.contains(&Value::UInt(6)));
    }

    #[test]
    fn minus_less_than_eq_minus_larger_is_false() {
        // (-∞,3] ∖ (-∞,5] = ∅
        let result =
            Predicate::LessThanEq(Value::UInt(3)).minus(&Predicate::LessThanEq(Value::UInt(5)));
        assert_eq!(result, Predicate::False);
    }

    #[test]
    fn minus_true_minus_intervals_is_complement() {
        // U ∖ {[0,5]} = (5,∞)
        let s = Predicate::from_column_value(&ColumnValue::UInts(vec![0, 1, 2, 3, 4, 5]));
        let result = Predicate::True.minus(&s);
        assert!(!result.contains(&Value::UInt(3)));
        assert!(result.contains(&Value::UInt(100)));
    }

    #[test]
    fn minus_record_minus_record_field_by_field() {
        // Record({a:[1,2,3], b:True}) ∖ Record({a:[2], b:False}) = Record({a:[1,3], b:True})
        let a = record_pred(&[
            (
                "a",
                Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3])),
            ),
            ("b", Predicate::True),
        ]);
        let b = record_pred(&[
            (
                "a",
                Predicate::from_column_value(&ColumnValue::UInts(vec![2])),
            ),
            ("b", Predicate::False),
        ]);
        let result = a.minus(&b);
        let Predicate::Record(fields) = result else {
            panic!("expected Record, got {result:?}");
        };
        assert!(fields["a"].contains(&Value::UInt(1)));
        assert!(!fields["a"].contains(&Value::UInt(2)));
        assert!(fields["a"].contains(&Value::UInt(3)));
        assert_eq!(fields["b"], Predicate::True);
    }

    #[test]
    fn minus_or_distributes_over_arms() {
        // Or([{1,2}, {4,5}]) ∖ {2} = Or([{1}, {4,5}])
        let or_pred = Predicate::Or(vec![
            Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2])),
            Predicate::from_column_value(&ColumnValue::UInts(vec![4, 5])),
        ]);
        let result = or_pred.minus(&Predicate::from_column_value(&ColumnValue::UInts(vec![2])));
        assert!(result.contains(&Value::UInt(1)));
        assert!(!result.contains(&Value::UInt(2)));
        assert!(result.contains(&Value::UInt(4)));
        assert!(result.contains(&Value::UInt(5)));
    }

    #[test]
    fn minus_p_minus_or_subtracts_all_arms() {
        // {[1,5]} ∖ Or([{2}, {4}]) = {1,3,5}
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3, 4, 5]));
        let or_b = Predicate::Or(vec![
            Predicate::from_column_value(&ColumnValue::UInts(vec![2])),
            Predicate::from_column_value(&ColumnValue::UInts(vec![4])),
        ]);
        let result = a.minus(&or_b);
        assert!(result.contains(&Value::UInt(1)));
        assert!(!result.contains(&Value::UInt(2)));
        assert!(result.contains(&Value::UInt(3)));
        assert!(!result.contains(&Value::UInt(4)));
        assert!(result.contains(&Value::UInt(5)));
    }

    // ── Predicate::is_applicable_to ───────────────────────────────────────────

    fn uint_ext() -> Extent {
        Extent::Base(BaseType::UInt)
    }

    fn str_ext() -> Extent {
        Extent::Base(BaseType::String)
    }

    fn unit_ext() -> Extent {
        Extent::Base(BaseType::Unit)
    }

    fn record_ext(fields: &[(&str, Extent)]) -> Extent {
        Extent::Record(
            fields
                .iter()
                .map(|(k, e)| (k.to_string(), e.clone()))
                .collect(),
        )
    }

    fn int_intervals(values: &[i64]) -> Predicate {
        Predicate::from_column_value(&ColumnValue::Ints(values.to_vec()))
    }

    fn uint_intervals(values: &[usize]) -> Predicate {
        Predicate::from_column_value(&ColumnValue::UInts(values.to_vec()))
    }

    #[test]
    fn applicable_true_to_any_extent() {
        assert!(Predicate::True.is_applicable_to(&int()));
        assert!(Predicate::True.is_applicable_to(&bool_ext()));
        assert!(Predicate::True.is_applicable_to(&str_ext()));
        assert!(Predicate::True.is_applicable_to(&unit_ext()));
        assert!(Predicate::True.is_applicable_to(&range(4)));
        assert!(Predicate::True.is_applicable_to(&record_ext(&[("x", int())])));
    }

    #[test]
    fn applicable_false_to_any_extent() {
        assert!(Predicate::False.is_applicable_to(&int()));
        assert!(Predicate::False.is_applicable_to(&unit_ext()));
        assert!(Predicate::False.is_applicable_to(&record_ext(&[("x", int())])));
    }

    #[test]
    fn applicable_less_than_eq_int_to_int_extent() {
        assert!(Predicate::LessThanEq(Value::Int(5)).is_applicable_to(&int()));
    }

    #[test]
    fn applicable_less_than_eq_uint_to_uint_extent() {
        assert!(Predicate::LessThanEq(Value::UInt(5)).is_applicable_to(&uint_ext()));
    }

    #[test]
    fn applicable_less_than_eq_uint_to_uint_range_extent() {
        assert!(Predicate::LessThanEq(Value::UInt(3)).is_applicable_to(&range(10)));
    }

    #[test]
    fn applicable_less_than_eq_bool_to_bool_extent() {
        assert!(Predicate::LessThanEq(Value::Bool(true)).is_applicable_to(&bool_ext()));
    }

    #[test]
    fn applicable_less_than_eq_string_to_string_extent() {
        assert!(Predicate::LessThanEq(Value::String("z".into())).is_applicable_to(&str_ext()));
    }

    #[test]
    fn applicable_less_than_eq_int_rejects_bool_extent() {
        assert!(!Predicate::LessThanEq(Value::Int(5)).is_applicable_to(&bool_ext()));
    }

    #[test]
    fn applicable_less_than_eq_int_rejects_uint_extent() {
        assert!(!Predicate::LessThanEq(Value::Int(5)).is_applicable_to(&uint_ext()));
    }

    #[test]
    fn applicable_less_than_eq_int_rejects_record_extent() {
        assert!(
            !Predicate::LessThanEq(Value::Int(5)).is_applicable_to(&record_ext(&[("x", int())]))
        );
    }

    #[test]
    fn applicable_int_intervals_to_int_extent() {
        assert!(int_intervals(&[1, 2, 3]).is_applicable_to(&int()));
    }

    #[test]
    fn applicable_uint_intervals_to_uint_extent() {
        assert!(uint_intervals(&[0, 1]).is_applicable_to(&uint_ext()));
    }

    #[test]
    fn applicable_uint_intervals_to_uint_range_extent() {
        assert!(uint_intervals(&[0, 1]).is_applicable_to(&range(4)));
    }

    #[test]
    fn applicable_int_intervals_rejects_bool_extent() {
        assert!(!int_intervals(&[0, 1]).is_applicable_to(&bool_ext()));
    }

    #[test]
    fn applicable_int_intervals_rejects_record_extent() {
        assert!(!int_intervals(&[1]).is_applicable_to(&record_ext(&[("x", int())])));
    }

    #[test]
    fn applicable_empty_intervals_to_any_extent() {
        // False (empty intervals) is applicable everywhere.
        assert_eq!(uint_intervals(&[]), Predicate::False);
        assert!(Predicate::False.is_applicable_to(&int()));
        assert!(Predicate::False.is_applicable_to(&record_ext(&[("x", int())])));
    }

    #[test]
    fn applicable_record_predicate_to_matching_record_extent() {
        let pred = Predicate::Record(
            [
                ("x".to_string(), Predicate::True),
                ("y".to_string(), Predicate::False),
            ]
            .into(),
        );
        assert!(pred.is_applicable_to(&record_ext(&[("x", int()), ("y", bool_ext())])));
    }

    #[test]
    fn applicable_record_predicate_with_typed_fields() {
        let pred = Predicate::Record([("n".to_string(), int_intervals(&[1, 2]))].into());
        assert!(pred.is_applicable_to(&record_ext(&[("n", int())])));
    }

    #[test]
    fn applicable_record_predicate_rejects_missing_key() {
        let pred = Predicate::Record([("x".to_string(), Predicate::True)].into());
        // Record extent has "x" and "y" but the predicate only covers "x".
        assert!(!pred.is_applicable_to(&record_ext(&[("x", int()), ("y", int())])));
    }

    #[test]
    fn applicable_record_predicate_rejects_wrong_field_type() {
        // "x" field predicate is an Int interval but the extent says Bool.
        let pred = Predicate::Record([("x".to_string(), int_intervals(&[1]))].into());
        assert!(!pred.is_applicable_to(&record_ext(&[("x", bool_ext())])));
    }

    #[test]
    fn applicable_record_predicate_rejects_scalar_extent() {
        let pred = Predicate::Record([("x".to_string(), Predicate::True)].into());
        assert!(!pred.is_applicable_to(&int()));
    }

    #[test]
    fn applicable_or_all_arms_compatible() {
        let pred = Predicate::Or(vec![int_intervals(&[1]), int_intervals(&[3])]);
        assert!(pred.is_applicable_to(&int()));
    }

    #[test]
    fn applicable_or_rejects_when_any_arm_incompatible() {
        // One arm is an Int interval, the other is a UInt interval — mismatch against int().
        let pred = Predicate::Or(vec![int_intervals(&[1]), uint_intervals(&[2])]);
        assert!(!pred.is_applicable_to(&int()));
    }

    // ── Predicate::Union ──────────────────────────────────────────────────────

    fn union_ext() -> Extent {
        Extent::Union(TagMap::from_positional(vec![int(), bool_ext()]))
    }

    fn union_pred(p0: Predicate, p1: Predicate) -> Predicate {
        Predicate::Union(TagMap::from_positional(vec![p0, p1]))
    }

    fn union_val(tag: usize, inner: Value) -> Value {
        Value::Union {
            tag: FieldKey::Index(tag),
            inner: Box::new(inner),
        }
    }

    #[test]
    fn union_from_column_value_empty_tags_is_false() {
        let cv = ColumnValue::positional_union(
            &[],
            vec![ColumnValue::Ints(vec![]), ColumnValue::Bools(BitVec::new())],
        );
        assert_eq!(Predicate::from_column_value(&cv), Predicate::False);
    }

    #[test]
    fn union_from_column_value_builds_per_variant_predicate() {
        let cv = ColumnValue::positional_union(
            &[0, 1, 0],
            vec![ColumnValue::Ints(vec![1, 3]), ColumnValue::Ints(vec![7])],
        );
        let pred = Predicate::from_column_value(&cv);
        assert!(matches!(pred, Predicate::Union(ref ps) if ps.len() == 2));
        // Tag-0 predicate admits 1 and 3 but not 7.
        assert!(pred.contains(&union_val(0, Value::Int(1))));
        assert!(pred.contains(&union_val(0, Value::Int(3))));
        assert!(!pred.contains(&union_val(0, Value::Int(7))));
        // Tag-1 predicate admits 7 but not 1.
        assert!(pred.contains(&union_val(1, Value::Int(7))));
        assert!(!pred.contains(&union_val(1, Value::Int(1))));
    }

    #[test]
    fn union_as_bool_all_true_is_true() {
        assert_eq!(
            union_pred(Predicate::True, Predicate::True).as_bool(),
            Some(true)
        );
    }

    #[test]
    fn union_as_bool_all_false_is_false() {
        assert_eq!(
            union_pred(Predicate::False, Predicate::False).as_bool(),
            Some(false)
        );
    }

    #[test]
    fn union_as_bool_mixed_is_none() {
        assert_eq!(
            union_pred(Predicate::True, Predicate::False).as_bool(),
            None
        );
    }

    #[test]
    fn union_as_bool_interval_variant_is_none() {
        assert_eq!(
            union_pred(Predicate::True, int_intervals(&[1])).as_bool(),
            None
        );
    }

    #[test]
    fn union_contains_matching_tag_and_inner() {
        let pred = union_pred(int_intervals(&[5]), Predicate::True);
        assert!(pred.contains(&union_val(0, Value::Int(5))));
    }

    #[test]
    fn union_contains_rejects_wrong_inner() {
        let pred = union_pred(int_intervals(&[5]), Predicate::True);
        assert!(!pred.contains(&union_val(0, Value::Int(9))));
    }

    #[test]
    fn union_contains_dispatches_by_tag() {
        // Tag 1 is Predicate::True so any inner is accepted; tag 0 is False so nothing is.
        let pred = union_pred(Predicate::False, Predicate::True);
        assert!(!pred.contains(&union_val(0, Value::Int(0))));
        assert!(pred.contains(&union_val(1, Value::Int(99))));
    }

    #[test]
    fn union_contains_rejects_non_union_value() {
        let pred = union_pred(Predicate::True, Predicate::True);
        assert!(!pred.contains(&Value::Int(0)));
    }

    #[test]
    fn union_subsumes_element_wise_both_true() {
        let broad = union_pred(Predicate::True, Predicate::True);
        let narrow = union_pred(int_intervals(&[1, 2]), int_intervals(&[3]));
        assert!(broad.subsumes(&narrow));
        assert!(!narrow.subsumes(&broad));
    }

    #[test]
    fn union_subsumes_identical_predicates() {
        let pred = union_pred(int_intervals(&[1]), int_intervals(&[2]));
        assert!(pred.subsumes(&pred));
    }

    #[test]
    fn union_does_not_subsume_when_one_variant_larger() {
        let a = union_pred(int_intervals(&[1]), Predicate::True);
        let b = union_pred(Predicate::True, Predicate::True);
        // a's tag-0 predicate is narrower than b's, so a does not subsume b.
        assert!(!a.subsumes(&b));
    }

    #[test]
    fn union_intersect_element_wise() {
        let a = union_pred(int_intervals(&[1, 2, 3]), int_intervals(&[10, 20]));
        let b = union_pred(int_intervals(&[2, 3, 4]), int_intervals(&[20, 30]));
        let result = a.intersect(&b);
        // Tag-0: {1,2,3} ∩ {2,3,4} = {2,3}
        assert!(result.contains(&union_val(0, Value::Int(2))));
        assert!(result.contains(&union_val(0, Value::Int(3))));
        assert!(!result.contains(&union_val(0, Value::Int(1))));
        assert!(!result.contains(&union_val(0, Value::Int(4))));
        // Tag-1: {10,20} ∩ {20,30} = {20}
        assert!(result.contains(&union_val(1, Value::Int(20))));
        assert!(!result.contains(&union_val(1, Value::Int(10))));
    }

    #[test]
    fn union_intersect_with_false_variant_yields_false_variant() {
        let a = union_pred(int_intervals(&[1]), Predicate::True);
        let b = union_pred(Predicate::False, Predicate::True);
        let result = a.intersect(&b);
        assert!(!result.contains(&union_val(0, Value::Int(1))));
        assert!(result.contains(&union_val(1, Value::Int(42))));
    }

    #[test]
    fn union_minus_element_wise() {
        let a = union_pred(int_intervals(&[1, 2, 3]), int_intervals(&[10, 20]));
        let b = union_pred(int_intervals(&[2]), int_intervals(&[10]));
        let result = a.minus(&b);
        // Tag-0: {1,2,3} ∖ {2} = {1,3}
        assert!(result.contains(&union_val(0, Value::Int(1))));
        assert!(!result.contains(&union_val(0, Value::Int(2))));
        assert!(result.contains(&union_val(0, Value::Int(3))));
        // Tag-1: {10,20} ∖ {10} = {20}
        assert!(!result.contains(&union_val(1, Value::Int(10))));
        assert!(result.contains(&union_val(1, Value::Int(20))));
    }

    #[test]
    fn union_minus_false_leaves_original() {
        let a = union_pred(int_intervals(&[5]), int_intervals(&[6]));
        let b = union_pred(Predicate::False, Predicate::False);
        let result = a.minus(&b);
        assert!(result.contains(&union_val(0, Value::Int(5))));
        assert!(result.contains(&union_val(1, Value::Int(6))));
    }

    #[test]
    fn union_method_element_wise() {
        let a = union_pred(int_intervals(&[1, 2]), int_intervals(&[10]));
        let b = union_pred(int_intervals(&[3, 4]), int_intervals(&[20]));
        let result = a.union(&b);
        // Tag-0: {1,2} ∪ {3,4} = {1,2,3,4}
        for v in [1, 2, 3, 4] {
            assert!(result.contains(&union_val(0, Value::Int(v))));
        }
        assert!(!result.contains(&union_val(0, Value::Int(5))));
        // Tag-1: {10} ∪ {20} = {10,20}
        assert!(result.contains(&union_val(1, Value::Int(10))));
        assert!(result.contains(&union_val(1, Value::Int(20))));
    }

    #[test]
    fn union_method_with_true_yields_true_per_variant() {
        let a = union_pred(int_intervals(&[1]), Predicate::False);
        let b = union_pred(Predicate::True, Predicate::False);
        let result = a.union(&b);
        assert!(result.contains(&union_val(0, Value::Int(999))));
        assert!(!result.contains(&union_val(1, Value::Int(1))));
    }

    #[test]
    fn applicable_union_predicate_to_matching_union_extent() {
        let pred = union_pred(Predicate::True, Predicate::False);
        assert!(pred.is_applicable_to(&union_ext()));
    }

    #[test]
    fn applicable_union_predicate_with_typed_variants() {
        let pred = union_pred(int_intervals(&[1, 2]), Predicate::True);
        assert!(pred.is_applicable_to(&union_ext()));
    }

    #[test]
    fn applicable_union_predicate_rejects_scalar_extent() {
        let pred = union_pred(Predicate::True, Predicate::True);
        assert!(!pred.is_applicable_to(&int()));
    }

    /// A predicate covering **fewer** arms than the extent is applicable: variant
    /// width subtyping says the uncovered tags simply cannot occur, so there is
    /// nothing to constrain for them. Requiring equal arm counts would reject a
    /// legal subtype.
    #[test]
    fn applicable_union_predicate_accepts_a_subset_of_the_extents_arms() {
        let pred = union_pred(Predicate::True, Predicate::True);
        let three_arm_ext = Extent::Union(TagMap::from_positional(vec![int(), bool_ext(), int()]));
        assert!(pred.is_applicable_to(&three_arm_ext));
    }

    /// The converse is rejected: a predicate constraining a tag the extent does
    /// not carry cannot apply, because that arm has no extent to be checked
    /// against.
    #[test]
    fn applicable_union_predicate_rejects_a_tag_the_extent_lacks() {
        let pred = Predicate::Union(TagMap::from_arms(vec![(
            FieldKey::Name("nope".into()),
            Predicate::True,
        )]));
        let ext = Extent::Union(TagMap::from_positional(vec![int(), bool_ext()]));
        assert!(!pred.is_applicable_to(&ext));
    }

    #[test]
    fn applicable_union_predicate_rejects_wrong_variant_type() {
        // Tag-0 predicate is an Int interval but the extent says Bool for tag 0.
        let pred = union_pred(int_intervals(&[1]), Predicate::True);
        let swapped = Extent::Union(TagMap::from_positional(vec![bool_ext(), int()]));
        assert!(!pred.is_applicable_to(&swapped));
    }
}
