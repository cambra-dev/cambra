//! Operations on [`IntervalSet`] that the `intervalsets` crate lacks: [`HasDifference`], whether
//! one set holds a value that another does not, and [`single_interval_set`], a column of integers
//! as one interval set.
//!
//! `intervalsets` computes `a ∖ b` as `a ∩ complement(b)`, which builds both sets before
//! [`MaybeEmpty::is_empty`] reads one bit of the answer. [`HasDifference`] answers the question
//! that `difference(..).is_empty()` is asked for, stops at the first value of `self` that `rhs`
//! lacks, and builds no [`IntervalSet`].
//!
//! The answer is the one `!a.difference(b).is_empty()` gives for every pair of sets, including
//! sets that hold touching runs unmerged. [`IntervalSet::new`] keeps `[0, 1]` and `[2, 3]` of a
//! discrete domain as two intervals, and `(-∞, 4)` and `[4, 4]` of any domain, so an interval is
//! covered by `rhs` when a chain of touching intervals covers it, not only when one interval
//! does. `Interval::merged` joins the first pair and not the second, so the chain is followed by
//! comparing bounds.

use std::borrow::Cow;

use intervalsets::{
    Bound, BoundType, Bounding, Interval, IntervalSet, MaybeEmpty, Side, numeric::Domain,
};

use crate::interpreter::Value;

/// Whether `self ∖ rhs` is not empty.
///
/// Equivalent to `!self.difference(rhs).is_empty()`, without the set that `difference` builds.
/// The cost is one lookup in `rhs` per interval of `self`, logarithmic in the size of `rhs`.
pub trait HasDifference {
    fn has_difference(&self, rhs: &Self) -> bool;
}

impl<T: Domain> HasDifference for IntervalSet<T> {
    fn has_difference(&self, rhs: &IntervalSet<T>) -> bool {
        let covering = rhs.intervals();
        self.intervals().iter().any(|x| !covered(x, covering))
    }
}

/// Whether the union of `covering` holds every value of `x`.
///
/// `covering` is the intervals of an [`IntervalSet`]: non-empty, ascending, and not
/// intersecting. They may touch, so `x` is covered when a run of touching intervals does.
fn covered<T: Domain>(x: &Interval<T>, covering: &[Interval<T>]) -> bool {
    if x.is_empty() {
        return true;
    }
    // The run holding `x`'s least value starts at one of two intervals. The last interval
    // ordered before `x` starts no later than `x` does, and the first ordered at or after `x`
    // starts where `x` does or later. No interval before either can reach `x`'s least value,
    // since the one after it starts no later than `x` and they do not intersect.
    let at = covering.partition_point(|y| y < x);
    (at > 0 && run_covers(x, &covering[at - 1..]))
        || (at < covering.len() && run_covers(x, &covering[at..]))
}

/// Whether the run of touching intervals that starts at `run[0]` holds every value of `x`.
fn run_covers<T: Domain>(x: &Interval<T>, run: &[Interval<T>]) -> bool {
    if !starts_at_or_before(&run[0], x) {
        return false;
    }
    for (i, y) in run.iter().enumerate() {
        if ends_at_or_after(y, x) {
            return true;
        }
        match run.get(i + 1) {
            Some(next) if touches(y, next) => {}
            _ => return false,
        }
    }
    false
}

/// The bound as the crate normalizes it: an open bound of a discrete domain is the closed bound
/// of the next value inward. The crate leaves the bound of a half-bounded interval open.
fn normalized<T: Domain>(bound: &Bound<T>, side: Side) -> Cow<'_, Bound<T>> {
    match bound.is_open() && bound.value().try_adjacent(side.flip()).is_some() {
        true => Cow::Owned(bound.clone().normalized(side)),
        false => Cow::Borrowed(bound),
    }
}

/// Whether `y` starts at or before the least value of `x`.
fn starts_at_or_before<T: Domain>(y: &Interval<T>, x: &Interval<T>) -> bool {
    match (y.left(), x.left()) {
        (None, _) => true,
        (Some(_), None) => false,
        (Some(by), Some(bx)) => {
            let (by, bx) = (normalized(by, Side::Left), normalized(bx, Side::Left));
            match by.bound_type() {
                BoundType::Closed => by.value() <= bx.value(),
                BoundType::Open => {
                    by.value() < bx.value() || (by.value() == bx.value() && bx.is_open())
                }
            }
        }
    }
}

/// Whether `y` ends at or after the greatest value of `x`.
fn ends_at_or_after<T: Domain>(y: &Interval<T>, x: &Interval<T>) -> bool {
    match (y.right(), x.right()) {
        (None, _) => true,
        (Some(_), None) => false,
        (Some(by), Some(bx)) => {
            let (by, bx) = (normalized(by, Side::Right), normalized(bx, Side::Right));
            match by.bound_type() {
                BoundType::Closed => bx.value() <= by.value(),
                BoundType::Open => {
                    bx.value() < by.value() || (bx.value() == by.value() && bx.is_open())
                }
            }
        }
    }
}

/// Whether no value lies between the right end of `y` and the left end of `z`, where `z`
/// follows `y`.
fn touches<T: Domain>(y: &Interval<T>, z: &Interval<T>) -> bool {
    let (Some(end), Some(start)) = (y.right(), z.left()) else {
        return false;
    };
    let (end, start) = (normalized(end, Side::Right), normalized(start, Side::Left));
    let (v, w) = (end.value(), start.value());
    match (end.bound_type(), start.bound_type()) {
        // The next value after `v`, where the domain has one, is where `z` has to begin.
        (BoundType::Closed, BoundType::Closed) => {
            w <= v || v.try_adjacent(Side::Right).is_some_and(|next| *w <= next)
        }
        // `v` is in one of the two and the values beyond it are in the other.
        (BoundType::Closed, BoundType::Open) | (BoundType::Open, BoundType::Closed) => w <= v,
        // `v` is in neither unless `z` begins below it.
        (BoundType::Open, BoundType::Open) => w < v,
    }
}

/// A primitive integer type whose ranges are sorted and merged as plain numbers, where a
/// [`Value`] comparison would go through [`Value`]'s ordering for every pair.
pub(crate) trait IntegerKey: Copy + Ord {
    /// The next value, or `None` at the type's greatest.
    fn next(self) -> Option<Self>;
    fn value(self) -> Value;
}

impl IntegerKey for u64 {
    fn next(self) -> Option<Self> {
        self.checked_add(1)
    }
    fn value(self) -> Value {
        Value::UInt(self)
    }
}

impl IntegerKey for i64 {
    fn next(self) -> Option<Self> {
        self.checked_add(1)
    }
    fn value(self) -> Value {
        Value::Int(self)
    }
}

/// `ranges` sorted, with overlapping and adjacent ranges merged into one.
///
/// A range is `(least, greatest)`, both included. Equal ranges are interchangeable, so the sort
/// need not be stable.
fn merged_ranges<T: IntegerKey>(mut ranges: Vec<(T, T)>) -> Vec<(T, T)> {
    ranges.sort_unstable();
    let mut merged: Vec<(T, T)> = Vec::with_capacity(ranges.len());
    for (least, greatest) in ranges {
        match merged.last_mut() {
            Some((_, end)) if least <= *end || end.next() == Some(least) => {
                *end = (*end).max(greatest);
            }
            _ => merged.push((least, greatest)),
        }
    }
    merged
}

/// The values of an integer column as one interval set: their sorted runs, with overlapping and
/// adjacent values merged.
///
/// The values are sorted as integers, and `Value`s are built only for the merged ranges.
pub(crate) fn single_interval_set<T: IntegerKey>(data: &[T]) -> IntervalSet<Value> {
    let merged = merged_ranges(data.iter().map(|&v| (v, v)).collect());
    IntervalSet::new_unchecked(range_intervals(merged))
}

/// `ranges` as closed intervals.
fn range_intervals<T: IntegerKey>(ranges: Vec<(T, T)>) -> Vec<Interval<Value>> {
    ranges
        .into_iter()
        .map(|(least, greatest)| Interval::closed(least.value(), greatest.value()))
        .collect()
}

/// Random sets over small integer domains, and the values to enumerate them against. Shared by
/// the `has_difference` tests here and the `Predicate` operation tests in `predicate.rs`.
#[cfg(test)]
pub(crate) mod test_support {
    use super::*;
    use crate::interpreter::Value;

    /// A deterministic pseudo-random sequence.
    pub(crate) struct Lcg(pub u64);

    impl Lcg {
        pub fn next(&mut self, below: u64) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (self.0 >> 33) % below
        }
    }

    /// The integer type a random set is over.
    #[derive(Clone, Copy, Debug)]
    pub(crate) enum Key {
        UInt,
        Int,
    }

    impl Key {
        /// The value at position `i` of the generated range: `i` itself for `UInt`, and `i - 6`
        /// for `Int`, so that a range of 12 straddles zero.
        pub fn value(self, i: u64) -> Value {
            match self {
                Key::UInt => Value::UInt(i),
                Key::Int => Value::Int(i as i64 - 6),
            }
        }

        /// The least value of the type, where it has one.
        pub fn lowest(self) -> Option<Value> {
            matches!(self, Key::UInt).then_some(Value::UInt(0))
        }

        /// The values to ask about for sets generated over `span` positions: the range and a margin
        /// above it, and for `Int` two values below the least bound, which stand for everything
        /// below it.
        pub fn domain(self, span: u64) -> Vec<Value> {
            let mut domain: Vec<Value> = (0..span + 3).map(|i| self.value(i)).collect();
            if matches!(self, Key::Int) {
                domain.extend([Value::Int(-9), Value::Int(-8)]);
            }
            domain
        }

        /// The position of `v` within the generated range.
        fn position(self, v: &Value) -> Option<u64> {
            match (self, v) {
                (Key::UInt, Value::UInt(i)) => Some(*i),
                (Key::Int, Value::Int(i)) => u64::try_from(i + 6).ok(),
                _ => None,
            }
        }
    }

    /// A random closed, half-bounded, unbounded or empty interval over `span` positions.
    ///
    /// A predicate over an unsigned key is clamped to the type's range, so its intervals are never
    /// unbounded below it, and the generator does not make them. `Interval::open` over adjacent
    /// integers is left out: it is an inverted closed interval that `is_empty` does not recognize.
    /// The half-bounded open intervals `Interval::unbound_open` and `Interval::open_unbound` are
    /// in: they carry the open bound that the crate does not normalize.
    pub(crate) fn random_interval(rng: &mut Lcg, span: u64, key: Key) -> Interval<Value> {
        let (lo, hi) = (rng.next(span), rng.next(span));
        let (a, b) = (key.value(lo.min(hi)), key.value(lo.max(hi)));
        match (rng.next(14), key.lowest()) {
            (0, _) => Interval::empty(),
            (10 | 11, None) => Interval::unbound_open(b),
            (12 | 13, _) => Interval::open_unbound(a),
            (1, None) => Interval::unbounded(),
            (1, Some(least)) => Interval::closed_unbound(least),
            (2, None) => Interval::unbound_closed(b),
            (2, Some(least)) => Interval::closed(least, b),
            (3, _) => Interval::closed_unbound(a),
            _ => Interval::closed(a, b),
        }
    }

    /// A random valid set. Half of the sets are what [`IntervalSet::new`] makes of random
    /// intervals; in the other half every finite interval of that set is split at a random inner
    /// value into two touching intervals, which `new` also accepts.
    pub(crate) fn random_set(rng: &mut Lcg, span: u64, key: Key) -> IntervalSet<Value> {
        let count = rng.next(5);
        let set = IntervalSet::new(
            (0..count)
                .map(|_| random_interval(rng, span, key))
                .collect(),
        );
        if rng.next(2) == 0 {
            return set;
        }
        let split: Vec<Interval<Value>> = set
            .intervals()
            .iter()
            .flat_map(|iv| match (iv.lval(), iv.rval()) {
                (Some(l), Some(r)) => match (key.position(l), key.position(r)) {
                    (Some(l), Some(r)) if l < r => {
                        let mid = l + rng.next(r - l);
                        vec![
                            Interval::closed(key.value(l), key.value(mid)),
                            Interval::closed(key.value(mid + 1), key.value(r)),
                        ]
                    }
                    _ => vec![iv.clone()],
                },
                _ => vec![iv.clone()],
            })
            .collect();
        IntervalSet::new_unchecked(split)
    }
}

#[cfg(test)]
mod tests {
    use super::test_support::*;
    use super::*;
    use crate::interpreter::Value;
    use intervalsets::ops::{Contains, Difference};

    fn u(v: u64) -> Value {
        Value::UInt(v)
    }

    /// The set holding just `interval`.
    fn one(interval: Interval<Value>) -> IntervalSet<Value> {
        IntervalSet::new(vec![interval])
    }

    /// Whether `a` holds a value `b` lacks, by asking each value of `domain`.
    ///
    /// `difference(..).is_empty()` is not the oracle: `intervalsets` computes the complement of a set
    /// holding the touching runs `[3, 4]` and `[5, 5]` with an invalid `[5, 4]` piece, and
    /// `[3, 6] ∖ ((-∞, 1] ∪ [3, 4] ∪ [5, 5])` comes out empty where the answer is `{6}`.
    fn by_enumeration(a: &IntervalSet<Value>, b: &IntervalSet<Value>, domain: &[Value]) -> bool {
        domain.iter().any(|v| a.contains(v) && !b.contains(v))
    }

    /// Random pairs of sets agree with enumerating the values.
    ///
    /// Small spans make touching, nested and equal intervals common, which is where a single
    /// containment test and a run of touching intervals can disagree. Signed integers have a
    /// predecessor of their least bound, which `u64` lacks.
    #[test]
    fn agrees_with_enumeration_over_integers() {
        for (key, seed, span) in [
            (Key::UInt, 1, 6),
            (Key::UInt, 2, 12),
            (Key::UInt, 3, 30),
            (Key::Int, 5, 12),
        ] {
            let domain = key.domain(span);
            let mut rng = Lcg(seed);
            for _ in 0..60_000 {
                let a = random_set(&mut rng, span, key);
                let b = random_set(&mut rng, span, key);
                assert_eq!(
                    a.has_difference(&b),
                    by_enumeration(&a, &b, &domain),
                    "{key:?}: {a:?} ∖ {b:?}"
                );
            }
        }
    }

    /// The set the crate gets wrong: `difference` is empty and the answer is `{6}`.
    #[test]
    fn touching_runs_do_not_hide_a_value_beyond_them() {
        let a = IntervalSet::new(vec![Interval::closed(u(3), u(6))]);
        let b = IntervalSet::new_unchecked(vec![
            Interval::unbound_closed(u(1)),
            Interval::closed(u(3), u(4)),
            Interval::closed(u(5), u(5)),
        ]);
        assert!(a.difference(&b).is_empty(), "the crate's answer is wrong");
        assert!(a.has_difference(&b));
        let covered = IntervalSet::new_unchecked(vec![
            Interval::unbound_closed(u(1)),
            Interval::closed(u(3), u(4)),
            Interval::closed(u(5), u(6)),
        ]);
        assert!(!a.has_difference(&covered));
    }

    /// `[1, 2]` straddles two touching runs, so no single interval of the set holds it.
    #[test]
    fn a_value_straddling_two_touching_runs_is_covered() {
        let set = IntervalSet::new(vec![
            Interval::closed(u(0), u(1)),
            Interval::closed(u(2), u(3)),
        ]);
        assert_eq!(set.intervals().len(), 2, "`new` keeps touching runs apart");
        assert!(!one(Interval::closed(u(1), u(2))).has_difference(&set));
        assert!(!set.has_difference(&one(Interval::closed(u(0), u(3)))));
        assert!(one(Interval::closed(u(0), u(4))).has_difference(&set));
    }

    #[test]
    fn a_gap_between_runs_is_a_difference() {
        let set = IntervalSet::new(vec![
            Interval::closed(u(0), u(1)),
            Interval::closed(u(3), u(4)),
        ]);
        assert!(one(Interval::closed(u(1), u(3))).has_difference(&set));
        assert!(!one(Interval::closed(u(3), u(4))).has_difference(&set));
    }

    /// Strings have no adjacent value, so two intervals touch only where one is closed and the
    /// other open at the same bound, and `IntervalSet::new` leaves such a pair apart.
    #[test]
    fn open_and_closed_bounds_at_one_string_touch() {
        let s = |t: &str| Value::String(t.into());
        let set = IntervalSet::new_unchecked(vec![
            Interval::unbound_open(s("d")),
            Interval::closed(s("d"), s("f")),
        ]);
        assert!(!one(Interval::closed(s("b"), s("e"))).has_difference(&set));
        assert!(one(Interval::closed(s("b"), s("g"))).has_difference(&set));
        let apart = IntervalSet::new_unchecked(vec![
            Interval::unbound_open(s("d")),
            Interval::open(s("d"), s("f")),
        ]);
        assert!(
            one(Interval::closed(s("b"), s("e"))).has_difference(&apart),
            "`d` is in neither"
        );
    }

    #[test]
    fn the_empty_set_has_no_difference_and_everything_has_one_against_it() {
        let empty = IntervalSet::<Value>::empty();
        let some = IntervalSet::new(vec![Interval::closed(u(0), u(0))]);
        assert!(!empty.has_difference(&some));
        assert!(!empty.has_difference(&empty));
        assert!(some.has_difference(&empty));
        assert!(!one(Interval::<Value>::empty()).has_difference(&empty));
        assert!(one(Interval::unbounded()).has_difference(&some));
    }

    // ── single_interval_set ───────────────────────────────────────────────────

    /// The closed ranges of a set, as plain pairs.
    fn ranges_of(set: &IntervalSet<Value>) -> Vec<(Value, Value)> {
        set.intervals()
            .iter()
            .map(|interval| {
                (
                    interval.lval().expect("a closed interval").clone(),
                    interval.rval().expect("a closed interval").clone(),
                )
            })
            .collect()
    }

    fn uranges(pairs: &[(u64, u64)]) -> Vec<(Value, Value)> {
        pairs.iter().map(|&(a, b)| (u(a), u(b))).collect()
    }

    #[test]
    fn single_interval_set_of_no_values_is_empty() {
        assert!(single_interval_set::<u64>(&[]).intervals().is_empty());
    }

    #[test]
    fn single_interval_set_merges_adjacent_values_into_one_interval() {
        assert_eq!(
            ranges_of(&single_interval_set(&[1u64, 2, 3])),
            uranges(&[(1, 3)])
        );
        assert_eq!(ranges_of(&single_interval_set(&[5u64])), uranges(&[(5, 5)]));
    }

    #[test]
    fn single_interval_set_keeps_a_gap_between_runs() {
        assert_eq!(
            ranges_of(&single_interval_set(&[1u64, 2, 5, 6, 9])),
            uranges(&[(1, 2), (5, 6), (9, 9)])
        );
    }

    /// Order and repeats of the values do not matter.
    #[test]
    fn single_interval_set_sorts_and_deduplicates() {
        assert_eq!(
            ranges_of(&single_interval_set(&[7u64, 3, 4, 0, 8, 1, 2, 3, 7])),
            uranges(&[(0, 4), (7, 8)])
        );
    }

    /// A run crossing zero is one interval for signed values.
    #[test]
    fn single_interval_set_of_signed_values_runs_through_zero() {
        let signed = |a: i64, b: i64| (Value::Int(a), Value::Int(b));
        assert_eq!(
            ranges_of(&single_interval_set(&[1i64, -2, 0, -1, 5])),
            vec![signed(-2, 1), signed(5, 5)]
        );
    }

    /// The greatest value of a type has no next value, so nothing extends past it, and the
    /// least has no previous one.
    #[test]
    fn single_interval_set_handles_the_extremes_of_each_type() {
        assert_eq!(
            ranges_of(&single_interval_set(&[u64::MAX, 0, u64::MAX - 1, 7])),
            uranges(&[(0, 0), (7, 7), (u64::MAX - 1, u64::MAX)])
        );
        let signed = |a: i64, b: i64| (Value::Int(a), Value::Int(b));
        assert_eq!(
            ranges_of(&single_interval_set(&[i64::MAX, i64::MIN, i64::MIN + 1, 0])),
            vec![
                signed(i64::MIN, i64::MIN + 1),
                signed(0, 0),
                signed(i64::MAX, i64::MAX)
            ]
        );
    }

    /// The set holds exactly the values it was built from, with its intervals ascending and
    /// neither overlapping nor adjacent, for both integer types.
    #[test]
    fn single_interval_set_holds_exactly_its_values() {
        let mut rng = Lcg(41);
        for span in [4u64, 16, 200] {
            for _ in 0..500 {
                let count = rng.next(40) as usize;
                let unsigned: Vec<u64> = (0..count).map(|_| rng.next(span)).collect();
                let signed: Vec<i64> = unsigned
                    .iter()
                    .map(|&v| v as i64 - span as i64 / 2)
                    .collect();
                let from_unsigned = single_interval_set(&unsigned);
                let from_signed = single_interval_set(&signed);
                for v in 0..span + 2 {
                    assert_eq!(from_unsigned.contains(&u(v)), unsigned.contains(&v), "{v}");
                    let v = v as i64 - span as i64 / 2;
                    assert_eq!(
                        from_signed.contains(&Value::Int(v)),
                        signed.contains(&v),
                        "{v}"
                    );
                }
                for set in [ranges_of(&from_unsigned), ranges_of(&from_signed)] {
                    for pair in set.windows(2) {
                        assert!(pair[0].1 < pair[1].0, "ascending and disjoint: {set:?}");
                        let next = match &pair[0].1 {
                            Value::UInt(v) => Value::UInt(v + 1),
                            Value::Int(v) => Value::Int(v + 1),
                            other => panic!("not an integer: {other:?}"),
                        };
                        assert!(next < pair[1].0, "not adjacent: {set:?}");
                    }
                }
            }
        }
    }

    // ── merged_ranges ─────────────────────────────────────────────────────────

    #[test]
    fn merged_ranges_joins_overlapping_nested_and_adjacent_ranges() {
        assert_eq!(
            merged_ranges(vec![
                (10u64, 12),
                (0, 3),
                (2, 5),
                (6, 6),
                (11, 11),
                (20, 30),
                (22, 24)
            ]),
            vec![(0, 6), (10, 12), (20, 30)]
        );
    }

    #[test]
    fn merged_ranges_of_one_range_is_that_range() {
        assert_eq!(merged_ranges(vec![(3i64, 9)]), vec![(3, 9)]);
        assert!(merged_ranges::<u64>(vec![]).is_empty());
    }

    /// A range ending at the type's greatest value has no next value to be adjacent to.
    #[test]
    fn merged_ranges_does_not_join_past_the_greatest_value() {
        assert_eq!(
            merged_ranges(vec![(0u64, u64::MAX), (5, 6)]),
            vec![(0, u64::MAX)]
        );
        assert_eq!(
            merged_ranges(vec![(u64::MAX, u64::MAX), (0, 1)]),
            vec![(0, 1), (u64::MAX, u64::MAX)]
        );
    }
}
