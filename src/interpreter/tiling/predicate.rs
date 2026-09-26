//! The [`Predicate`] type: subset-of-an-extent descriptions used by guards, plus
//! the column-value conversions and the function domain-sort helper.

use std::cmp::Ordering;
use std::collections::HashMap;

use bit_set::BitSet;
use intervalsets::{
    Bounding, Interval, IntervalSet, MaybeEmpty, Side,
    numeric::Domain,
    ops::{Complement, Contains, Difference, Intersection, Union},
};

use crate::{
    ccl::{BaseType, FieldKey, TagMap},
    interpreter::{ColumnValue, Extent, Tile, UnionArm, Value, transform_hashmap_values},
};

/// Whether two predicates admit the same values, whatever each is spelled as.
fn same_region(a: &Predicate, b: &Predicate) -> bool {
    a == b || (a.subsumes(b) && b.subsumes(a))
}

/// The two predicate shapes that are **boxes**: products of one predicate per component,
/// admitting a key when every component admits its part.
///
/// A [`Record`](Predicate::Record) is a box over one record key's fields, taken in name
/// order, which is the order [`Value`]'s comparison takes them in. A
/// [`Qualified`](Predicate::Qualified) predicate is a box over two components, the
/// enclosing path and the key under it; an unqualified predicate is the box
/// `(True, itself)` ([`split_qualification`](Predicate::split_qualification)).
///
/// Both shapes take one algebra, written once over the components: boxes meet component
/// by component, join where they differ in at most one component, and one box less another
/// is a staircase of boxes. Containment is componentwise too, which is exact for products:
/// a nonempty box lies inside another exactly when each of its components does.
enum BoxShape {
    Record(Vec<String>),
    Qualified,
}

impl BoxShape {
    /// `a` and `b` read as boxes of one shape, component by component, or `None` where
    /// neither is a box.
    fn of<'a>(
        a: &'a Predicate,
        b: &'a Predicate,
    ) -> Option<(BoxShape, Vec<&'a Predicate>, Vec<&'a Predicate>)> {
        match (a, b) {
            (Predicate::Qualified { .. }, _) | (_, Predicate::Qualified { .. }) => {
                let ((q1, k1), (q2, k2)) = (a.split_qualification(), b.split_qualification());
                Some((BoxShape::Qualified, vec![q1, k1], vec![q2, k2]))
            }
            (Predicate::Record(m1), Predicate::Record(m2)) => {
                assert!(
                    m1.len() == m2.len() && m2.keys().all(|k| m1.contains_key(k)),
                    "records over one domain have one schema: {a:?} and {b:?}"
                );
                let mut names: Vec<String> = m1.keys().cloned().collect();
                names.sort();
                let first = names.iter().map(|n| &m1[n]).collect();
                let second = names.iter().map(|n| &m2[n]).collect();
                Some((BoxShape::Record(names), first, second))
            }
            _ => None,
        }
    }

    /// The box with these components, in canonical form: a box with an empty component
    /// admits nothing, and is [`Predicate::False`].
    fn build(&self, components: Vec<Predicate>) -> Predicate {
        if components.iter().any(Predicate::is_false) {
            return Predicate::False;
        }
        match self {
            BoxShape::Record(names) => {
                Predicate::Record(names.iter().cloned().zip(components).collect())
            }
            BoxShape::Qualified => {
                let [enclosing, here]: [Predicate; 2] = components
                    .try_into()
                    .unwrap_or_else(|_| unreachable!("a qualified box has two components"));
                Predicate::qualified(enclosing, here)
            }
        }
    }

    fn meet(&self, a: &[&Predicate], b: &[&Predicate]) -> Predicate {
        self.build(a.iter().zip(b).map(|(p, q)| p.intersect(q)).collect())
    }

    /// The one box `a ∪ b` is, where there is one: the boxes agree on every component but
    /// at most one, which takes the union of the two. Differing in two components, their
    /// union has a corner neither box has, so no single box is it.
    fn join(&self, a: &[&Predicate], b: &[&Predicate]) -> Option<Predicate> {
        let differing: Vec<usize> = (0..a.len()).filter(|&i| !same_region(a[i], b[i])).collect();
        let mut components: Vec<Predicate> = a.iter().map(|p| (*p).clone()).collect();
        match differing.as_slice() {
            [] => {}
            [i] => components[*i] = a[*i].union(b[*i]),
            _ => return None,
        }
        Some(self.build(components))
    }

    /// `a ∖ b` as a staircase: the box at step `i` keeps what component `i` alone leaves,
    /// over the components before it that `b` does hold and the components after it
    /// untouched. The steps are disjoint and cover `a ∖ b` exactly. Subtracting component
    /// by component into one box instead drops every key agreeing with `b` in any
    /// component, so `(1, 0) ∖ ({1} × {1})` would come back empty.
    fn minus(&self, a: &[&Predicate], b: &[&Predicate]) -> Predicate {
        let steps: Vec<Predicate> = (0..a.len())
            .map(|i| {
                self.build(
                    (0..a.len())
                        .map(|j| match j.cmp(&i) {
                            Ordering::Less => a[j].intersect(b[j]),
                            Ordering::Equal => a[j].minus(b[j]),
                            Ordering::Greater => a[j].clone(),
                        })
                        .collect(),
                )
            })
            .filter(|step| !step.is_false())
            .collect();
        match steps.is_empty() {
            true => Predicate::False,
            false => Predicate::flatten_or(steps),
        }
    }

    /// Whether box `a` contains box `b`, for a nonempty `b`.
    fn contains(a: &[&Predicate], b: &[&Predicate]) -> bool {
        a.iter().zip(b).all(|(p, q)| p.subsumes(q))
    }
}

/// The one box two predicates' union is, where both are boxes and one box is their union.
fn join(a: &Predicate, b: &Predicate) -> Option<Predicate> {
    let (shape, first, second) = BoxShape::of(a, b)?;
    shape.join(&first, &second)
}

/// The first of `arms` that `arm` joins with, and the box they join into.
fn join_with_any(arm: &Predicate, arms: &[Predicate]) -> Option<(usize, Predicate)> {
    arms.iter()
        .enumerate()
        .find_map(|(at, other)| join(arm, other).map(|joined| (at, joined)))
}

/// A predicate that describes a subset of values in an extent.
///
/// **One region has one spelling** wherever the representation allows it, because the
/// derived `PartialEq` is what release accumulation tests to decide whether a release added
/// anything ([`TileProducer::release`](crate::interpreter::tile_operators::TileProducer)):
/// an ordered set is an [`Intervals`](Self::Intervals) clamped to its type's range
/// ([`intervals`](Self::intervals)), an empty region is [`False`](Self::False), and a
/// region covering the whole type is [`True`](Self::True). A union of boxes has more than
/// one spelling in general; [`flatten_or`](Self::flatten_or) joins boxes that share all
/// but one component, and [`subsumes`](Self::subsumes) compares regions rather than
/// spellings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Predicate {
    True,
    False,
    /// An ordered scalar key's admitted values. Never built over records: a record key is
    /// described field by field, as a [`Record`](Self::Record) or a union of them.
    Intervals(IntervalSet<Value>),
    /// A box over a record key: the AND of each field's predicate.
    Record(HashMap<String, Predicate>),
    /// The union of multiple predicates — admits any value accepted by any arm.
    ///
    /// A union of boxes as [`Predicate::flatten_or`] leaves it: no two arms join into one box
    /// ([`BoxShape`]). Three or more arms can still cover one box that no two of them make,
    /// so an `Or` is not proof the region is no single box. Invariant: arms never directly
    /// nest another `Or`.
    Or(Vec<Predicate>),
    /// Predicate over a discriminated-union domain: one predicate per **named tag**, and
    /// `rest` for every tag it does not name.
    ///
    /// Admits a value `Union { tag, inner }` iff the predicate for `tag` — its own, or
    /// `rest` — admits `inner`.
    ///
    /// A predicate need not name every tag of its domain, and cannot always: a column
    /// carries only the tags it holds, which width subtyping makes fewer than its extent's
    /// (see [`TagMap`], "Why keyed rather than positional"), and a point names one. `rest`
    /// is what makes that exact. A point or a column's keys leave `rest` false, and a
    /// complement flips it, so `True ∖ 𝑝` needs no list of the tags `𝑝` leaves out.
    ///
    /// Canonical form, kept by [`Predicate::tagged`]: no named tag's predicate is `rest`'s
    /// value, and a union naming no tag is `True` or `False`. Universality is therefore
    /// spelled `True`: a union naming every tag of its domain `True` over a `false` rest is
    /// not recognized as everything, so a constructor that knows the whole tag set spells it
    /// through [`Predicate::over_every_tag`].
    Union {
        tags: TagMap<Predicate>,
        rest: bool,
    },
    /// A key of an inner level **qualified by the enclosing path that reaches it**:
    /// admits `(k₀ … k_d)` when `(k₀ … k_{d-1})` satisfies `enclosing` and `k_d`
    /// satisfies `here`.
    ///
    /// Every other arm is **unqualified**: read against the last component of a path
    /// alone, it admits the same key value under every enclosing path. That is the whole
    /// of what a curried collection's levels could say before this arm, and it is why a
    /// statement about one parent's keys had to be widened to cover every parent's.
    /// `enclosing` is itself a predicate over the level above's paths, `Qualified` again
    /// where the nest is deeper, so depth costs nesting rather than a concept per level.
    ///
    /// A box over `(enclosing, here)`, so it takes the same algebra as a record
    /// ([`BoxShape`]).
    ///
    /// Built through [`qualified`](Predicate::qualified), which drops the arm where
    /// `enclosing` admits everything: admitting the same keys everywhere is what the
    /// predicate says without it, so one region keeps one spelling. A predicate over the
    /// outermost level is never qualified — there is no enclosing path to name.
    Qualified {
        enclosing: Box<Predicate>,
        here: Box<Predicate>,
    },
}

impl Predicate {
    /// The largest position this predicate covers, for a prefix-style release of
    /// a monotone `UInt` domain — a commit clock or an iteration's positions.
    ///
    /// `None` for a predicate with no concrete upper bound (`True`, `False`,
    /// non-`UInt`). `True` is the terminal release, after which the consumer
    /// pulls no more, so there is no position to advance past.
    pub fn max_released_position(&self) -> Option<usize> {
        match self {
            Predicate::Intervals(iset) => iset
                .intervals()
                .iter()
                .filter_map(|iv| match iv.rval() {
                    Some(&Value::UInt(k)) => Some(k),
                    _ => None,
                })
                .max(),
            Predicate::Or(arms) => arms
                .iter()
                .filter_map(Predicate::max_released_position)
                .max(),
            // A union's arms are tag-keyed, so they are walked by value rather
            // than sharing the `Or` arm's positional vector.
            Predicate::Union { tags, rest: false } => tags
                .values()
                .filter_map(Predicate::max_released_position)
                .max(),
            // Every tag it does not name is whole, so there is no watermark to read.
            Predicate::Union { rest: true, .. } => None,
            // A qualified predicate names a position under one enclosing path, and the
            // caller wants a watermark over a flat domain, so there is nothing to answer.
            Predicate::Qualified { .. } => None,
            // A record key is not a position, and `True` and `False` bound nothing.
            Predicate::Record(_) | Predicate::True | Predicate::False => None,
        }
    }

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
        // Boxes that agree on every component but one are one box ([`BoxShape`]). A column
        // of records arrives as one point per row, and a drive states each enclosing row's
        // progress as a box of its own, so without this a region is one arm per row however
        // regular it is, and every later union compares all of them. A joined arm goes
        // round again, since one join can enable the next, and takes the earliest place it
        // came from.
        let mut joined: Vec<Predicate> = Vec::with_capacity(flat.len());
        for mut arm in flat {
            let mut slot = joined.len();
            while let Some((at, merged)) = join_with_any(&arm, &joined) {
                joined.remove(at);
                slot = slot.min(at);
                arm = merged;
            }
            joined.insert(slot.min(joined.len()), arm);
        }
        let flat = joined;
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

    /// [`Qualified`](Self::Qualified) in canonical form.
    ///
    /// An `enclosing` that admits everything says nothing, so the arm is dropped and
    /// `here` alone spells the same region. Either side empty admits nothing.
    pub fn qualified(enclosing: Predicate, here: Predicate) -> Predicate {
        if enclosing.is_false() || here.is_false() {
            return Predicate::False;
        }
        if enclosing.is_true() {
            return here;
        }
        Predicate::Qualified {
            enclosing: Box::new(enclosing),
            here: Box::new(here),
        }
    }

    /// A union predicate in canonical form: `tags` for the tags named, `rest` for every other.
    /// A tag stating what `rest` does is dropped, and one naming nothing collapses to `rest`.
    pub fn tagged(tags: TagMap<Predicate>, rest: bool) -> Predicate {
        let kept: Vec<(FieldKey, Predicate)> = tags
            .iter()
            .filter(|(_, p)| p.as_bool() != Some(rest))
            .map(|(tag, p)| (tag.clone(), p.clone()))
            .collect();
        match (kept.is_empty(), rest) {
            (true, true) => Predicate::True,
            (true, false) => Predicate::False,
            (false, _) => Predicate::Union {
                tags: TagMap::from_arms(kept),
                rest,
            },
        }
    }

    /// A union predicate over `tags`, which name every tag of the domain: `rest` is vacuous,
    /// so every tag `True` is `True` and every tag `False` is `False`.
    pub fn over_every_tag(tags: TagMap<Predicate>) -> Predicate {
        let rest = tags.values().all(Predicate::is_true);
        Predicate::tagged(tags, rest)
    }

    /// `True` or `False`.
    fn of_bool(b: bool) -> Predicate {
        match b {
            true => Predicate::True,
            false => Predicate::False,
        }
    }

    /// What this predicate over a union domain admits under `tag`, over that tag's payload.
    /// `None` for a predicate of another shape.
    pub(crate) fn under_tag(&self, tag: &FieldKey) -> Option<Predicate> {
        match self {
            Predicate::True | Predicate::False => Some(self.clone()),
            Predicate::Union { tags, rest } => Some(Predicate::at_tag(tags, *rest, tag)),
            _ => None,
        }
    }

    /// What a union predicate admits under `tag`: its own predicate, or `rest`.
    fn at_tag(tags: &TagMap<Predicate>, rest: bool, tag: &FieldKey) -> Predicate {
        match tags.get(tag) {
            Some(p) => p.clone(),
            None => Predicate::of_bool(rest),
        }
    }

    /// Two union predicates combined tag by tag, over every tag either names, with `rest`
    /// combined the same way.
    fn zip_tags(
        (ps, pr): (&TagMap<Predicate>, bool),
        (qs, qr): (&TagMap<Predicate>, bool),
        f: impl Fn(&Predicate, &Predicate) -> Predicate,
    ) -> Predicate {
        let mut named: Vec<&FieldKey> = ps.keys().chain(qs.keys()).collect();
        named.sort();
        named.dedup();
        let tags = named
            .into_iter()
            .map(|tag| {
                let combined = f(
                    &Predicate::at_tag(ps, pr, tag),
                    &Predicate::at_tag(qs, qr, tag),
                );
                (tag.clone(), combined)
            })
            .collect();
        let rest = f(&Predicate::of_bool(pr), &Predicate::of_bool(qr))
            .as_bool()
            .unwrap_or_else(|| unreachable!("True and False combine to True or False"));
        Predicate::tagged(TagMap::from_arms(tags), rest)
    }

    /// Whether this predicate names an enclosing path anywhere in it.
    ///
    /// What [`contains`](Self::contains) checks before reading a bare key: a qualified
    /// predicate cannot answer for one, and a caller that has not been converted to pass
    /// the whole path would silently get the answer for every enclosing path at once.
    pub fn qualifies(&self) -> bool {
        match self {
            Predicate::Qualified { .. } => true,
            Predicate::Or(arms) => arms.iter().any(Predicate::qualifies),
            _ => false,
        }
    }

    /// This predicate split into the enclosing paths it is qualified by and the keys it
    /// admits under them.
    ///
    /// An unqualified predicate splits as `(True, self)`, admitting its keys under every
    /// enclosing path. Reading both shapes this way is what lets one rule serve them: the
    /// lattice operations below combine the two halves rather than carrying a mixed arm.
    pub(crate) fn split_qualification(&self) -> (&Predicate, &Predicate) {
        match self {
            Predicate::Qualified { enclosing, here } => (enclosing, here),
            unqualified => (&Predicate::True, unqualified),
        }
    }

    /// `Some(true)` where this admits every value, `Some(false)` where it admits none.
    ///
    /// Exact for emptiness, given canonical interval sets ([`intervals`](Self::intervals),
    /// which every operation answers through): every constructor that can produce an empty
    /// region reports it through one of the arms below, so `Some(false)` is returned for
    /// every predicate admitting nothing. Universality is answered only
    /// where the spelling shows it — a union of arms that together cover everything but
    /// none alone answers `None` — so a caller needing the exact answer asks
    /// [`subsumes`](Self::subsumes).
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Predicate::False => Some(false),
            Predicate::True => Some(true),
            Predicate::Record(m) if m.iter().all(|(_, p)| p.is_true()) => Some(true),
            // A record's fields are an AND, so one empty field admits nothing however
            // much the others admit. Reading only an all-empty record as empty leaves a
            // predicate admitting nothing looking like one that admits something, and
            // every simplification that tests for emptiness then declines to make itself.
            Predicate::Record(m) if m.iter().any(|(_, p)| p.is_false()) => Some(false),
            Predicate::Intervals(i) if i.is_empty() => Some(false),
            Predicate::Intervals(i) if is_whole(i, sample(i).and_then(type_range).as_ref()) => {
                Some(true)
            }
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
            // True or false where every named tag says what `rest` does, which the canonical
            // form collapses; a union naming a tag that differs from `rest` is neither.
            Predicate::Union { tags, rest } => {
                match tags.values().all(|p| p.as_bool() == Some(*rest)) {
                    true => Some(*rest),
                    false => None,
                }
            }
            // A box, so one empty side empties it, as for a record.
            Predicate::Qualified { enclosing, here } if enclosing.is_false() || here.is_false() => {
                Some(false)
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
            (Predicate::Intervals(a), Predicate::Intervals(b)) => {
                Predicate::intervals(a.intersection(b))
            }
            // Or distributes over intersect: (A | B) & C = (A & C) | (B & C).
            (Predicate::Or(arms), _) => {
                Predicate::flatten_or(arms.iter().map(|a| a.intersect(other)).collect())
            }
            (_, Predicate::Or(arms)) => {
                Predicate::flatten_or(arms.iter().map(|a| self.intersect(a)).collect())
            }
            // Union: intersect per arm. Pointwise over one arm set — see
            // `TagMap::zip_same_tags`.
            (Predicate::Union { tags: ps, rest: pr }, Predicate::Union { tags: qs, rest: qr }) => {
                Predicate::zip_tags((ps, *pr), (qs, *qr), Predicate::intersect)
            }
            (a, b) => match BoxShape::of(a, b) {
                Some((shape, first, second)) => shape.meet(&first, &second),
                None => panic!("Cannot intersect incompatible predicates: {self:?} and {other:?}"),
            },
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
            (Predicate::Intervals(a), Predicate::Intervals(b)) => {
                Predicate::intervals(a.difference(b))
            }
            // U ∖ Intervals(s): everything not in s — representable as the complement.
            (s, Predicate::Intervals(i)) if s.is_true() => Predicate::intervals(i.complement()),
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
            // Union: subtract per arm. Pointwise over one arm set — see
            // `TagMap::zip_same_tags`.
            (Predicate::Union { tags: ps, rest: pr }, Predicate::Union { tags: qs, rest: qr }) => {
                Predicate::zip_tags((ps, *pr), (qs, *qr), Predicate::minus)
            }
            // `True` has no arms or fields of its own to subtract from, so it takes those of
            // the predicate it loses, each admitting everything. Only the bare `True`: a
            // record or union that admits everything already has its own, and expanding it
            // again would expand forever.
            (Predicate::True, Predicate::Union { tags, rest }) => {
                Predicate::tagged(tags.map(|_, q| Predicate::True.minus(q)), !rest)
            }
            (Predicate::True, Predicate::Record(m)) => {
                let whole = m.keys().map(|k| (k.clone(), Predicate::True)).collect();
                Predicate::Record(whole).minus(other)
            }
            (a, b) => match BoxShape::of(a, b) {
                Some((shape, first, second)) => shape.minus(&first, &second),
                None => panic!("Cannot subtract incompatible predicates: {self:?} minus {other:?}"),
            },
        }
    }

    /// Returns the predicate that admits exactly the values accepted by either `self` or `other`.
    pub fn union(&self, other: &Predicate) -> Predicate {
        match (self, other) {
            // True is the universal predicate: annihilator under union.
            (Predicate::True, _) | (_, Predicate::True) => Predicate::True,
            // False is the empty predicate: identity under union.
            (Predicate::False, p) | (p, Predicate::False) => p.clone(),
            (Predicate::Intervals(a), Predicate::Intervals(b)) => Predicate::intervals(a.union(b)),
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
            // Union: union per arm. Pointwise over one arm set — see
            // `TagMap::zip_same_tags`.
            (Predicate::Union { tags: ps, rest: pr }, Predicate::Union { tags: qs, rest: qr }) => {
                Predicate::zip_tags((ps, *pr), (qs, *qr), Predicate::union)
            }
            // Two boxes join into one where they agree on every component but one;
            // otherwise the join is the two of them, which is what `Or` is for.
            (a, b) => match BoxShape::of(a, b) {
                Some((shape, first, second)) => shape
                    .join(&first, &second)
                    .unwrap_or_else(|| Predicate::flatten_or(vec![a.clone(), b.clone()])),
                None => panic!("Cannot union incompatible predicates: {self:?} and {other:?}"),
            },
        }
    }

    /// Returns `true` if the node at `path` is admitted by this predicate.
    ///
    /// `path` names the node from the outermost level down, one component per level.
    /// Only [`Qualified`](Self::Qualified) reads more than its last component: every
    /// other arm describes a key value under every enclosing path, so an unqualified
    /// predicate answers for the key alone.
    pub fn contains_path(&self, path: &[Value]) -> bool {
        match self {
            Predicate::True => true,
            Predicate::False => false,
            Predicate::Qualified { enclosing, here } => {
                let Some((key, above)) = path.split_last() else {
                    return false;
                };
                enclosing.contains_path(above) && here.contains(key)
            }
            // An arm may be qualified, so the whole path goes down rather than the key.
            Predicate::Or(arms) => arms.iter().any(|a| a.contains_path(path)),
            unqualified => path.last().is_some_and(|key| unqualified.contains(key)),
        }
    }

    /// Returns `true` if `value` is admitted by this predicate.
    ///
    /// The key alone, which answers only for an unqualified predicate. A predicate naming an
    /// enclosing path needs [`contains_path`](Self::contains_path) and is refused here
    /// rather than answered approximately: the key does not say which enclosing path it
    /// sits under, and a conservative `false` would make a release build disagree with a
    /// debug one about a value the caller acts on.
    pub fn contains(&self, value: &Value) -> bool {
        match self {
            Predicate::True => true,
            Predicate::False => false,
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
            Predicate::Union { tags, rest } => match value {
                Value::Union { tag, inner } => match tags.get(tag) {
                    Some(p) => p.contains(inner),
                    None => *rest,
                },
                _ => false,
            },
            // Refused rather than approximated: the caller holds a key where the
            // predicate asks about a path, so there is no answer to give.
            Predicate::Qualified { .. } => panic!(
                "a predicate naming an enclosing path is read against the whole path, not \
                 the key {value:?} alone: {self:?}"
            ),
        }
    }

    /// Returns `true` if every value admitted by `other` is also admitted by `self`:
    /// `other ⊆ self`, exactly.
    ///
    /// Two boxes compare component by component, and a union on the right is contained
    /// when each of its arms is; both rules are exact. A union on the left may cover a
    /// region no single arm covers, so where no arm answers alone the question becomes
    /// whether `other ∖ self` is empty. Two predicates over different domains have no
    /// answer, and [`minus`](Self::minus) refuses them.
    pub fn subsumes(&self, other: &Predicate) -> bool {
        match (self, other) {
            // Everything subsumes the empty set, and the universal set subsumes everything.
            (_, o) if o.is_false() => true,
            (s, _) if s.is_true() => true,
            // Both canonical, so `b ∖ a` lies inside the type's range with normalized bounds,
            // and the crate's emptiness is the set's.
            (Predicate::Intervals(a), Predicate::Intervals(b)) => b.difference(a).is_empty(),
            // self subsumes a union iff it subsumes every arm.
            (_, Predicate::Or(arms)) => arms.iter().all(|a| self.subsumes(a)),
            (Predicate::Or(arms), _) => {
                arms.iter().any(|a| a.subsumes(other)) || other.minus(self).is_false()
            }
            // Tag by tag over every tag either names, and over the tags neither names.
            (Predicate::Union { tags: ps, rest: pr }, Predicate::Union { tags: qs, rest: qr }) => {
                (*pr || !*qr)
                    && ps.keys().chain(qs.keys()).all(|tag| {
                        Predicate::at_tag(ps, *pr, tag).subsumes(&Predicate::at_tag(qs, *qr, tag))
                    })
            }
            (a, b) => match BoxShape::of(a, b) {
                // `other` is nonempty, having passed the first arm.
                Some((_, first, second)) => BoxShape::contains(&first, &second),
                None => other.minus(self).is_false(),
            },
        }
    }

    /// Exactly `v`, and nothing else. A record is the box of its fields' points, and `Unit`,
    /// the one value of its type, is everything, as [`from_column_value`](Self::from_column_value)
    /// spells a column of it.
    pub(crate) fn point(v: Value) -> Predicate {
        match v {
            Value::Unit => Predicate::True,
            // One tag, with nothing under the others.
            Value::Union { tag, inner } => Predicate::tagged(
                TagMap::from_arms(vec![(tag, Predicate::point(*inner))]),
                false,
            ),
            Value::Record(fields) => Predicate::Record(
                fields
                    .into_iter()
                    .map(|(name, field)| (name, Predicate::point(field)))
                    .collect(),
            ),
            scalar => Predicate::intervals(IntervalSet::new(vec![Interval::closed(
                scalar.clone(),
                scalar,
            )])),
        }
    }

    /// Exactly the node at `path`, and nothing else — one qualified component per level.
    ///
    /// What a drive names when it says which enclosing row it is inside: the levels above
    /// pinned to the keys the path reaches, so a statement about that row's keys says
    /// nothing about the same keys under a sibling. The empty path is every node, there
    /// being no level to pin.
    pub(crate) fn exactly(path: &[Value]) -> Predicate {
        path.iter().fold(Predicate::True, |above, key| {
            Predicate::qualified(above, Predicate::point(key.clone()))
        })
    }

    /// This predicate, over the keys `depth` levels beneath the row at path `row`, restated
    /// over the paths of that row's group taken out on its own: restricted to paths under
    /// `row`, with `row`'s components removed. The inverse of [`beneath`](Self::beneath).
    ///
    /// A row's group is a collection in its own right, so an operator acting on one reads
    /// and writes its completeness over the group's own paths; a statement read over the
    /// whole tile's paths would be about other rows too.
    pub(crate) fn within(&self, row: &[Value], depth: usize) -> Predicate {
        match self {
            Predicate::Or(arms) => arms
                .iter()
                .map(|arm| arm.within(row, depth))
                .fold(Predicate::False, |all, one| all.union(&one)),
            Predicate::Qualified { enclosing, here } => match depth {
                0 => match enclosing.contains_path(row) {
                    true => (**here).clone(),
                    false => Predicate::False,
                },
                _ => Predicate::qualified(enclosing.within(row, depth - 1), (**here).clone()),
            },
            unqualified => unqualified.clone(),
        }
    }

    /// This predicate, stated over the paths of the group of the row at path `row`, `depth`
    /// levels beneath it, restated over whole paths: qualified by `row`, so it says nothing
    /// of any other row's group. The inverse of [`within`](Self::within).
    pub(crate) fn beneath(&self, row: &[Value], depth: usize) -> Predicate {
        self.qualified_by(&Predicate::exactly(row), depth)
    }

    /// This predicate, stated over the paths of a column of groups `depth` levels beneath its
    /// rows, restated over whole paths: qualified by `rows`, a predicate over the paths
    /// that reach those rows. A statement a column makes of every group can only be about
    /// the rows it is attached to, so it says nothing of any other row.
    /// [`beneath`](Self::beneath) is the case of one row.
    pub(crate) fn qualified_by(&self, rows: &Predicate, depth: usize) -> Predicate {
        match self {
            Predicate::False => Predicate::False,
            Predicate::Or(arms) => arms
                .iter()
                .map(|arm| arm.qualified_by(rows, depth))
                .fold(Predicate::False, |all, one| all.union(&one)),
            Predicate::Qualified { enclosing, here } => {
                assert!(
                    depth > 0,
                    "a group's own level names no enclosing path within the group: {self:?}"
                );
                Predicate::qualified(enclosing.qualified_by(rows, depth - 1), (**here).clone())
            }
            unqualified => {
                let enclosing = match depth {
                    0 => rows.clone(),
                    _ => Predicate::True.qualified_by(rows, depth - 1),
                };
                Predicate::qualified(enclosing, unqualified.clone())
            }
        }
    }

    /// The `v` this is [`at_or_below`](Self::at_or_below), where it is one — the watermark
    /// a prefix release or a store's frontier names.
    pub fn as_at_or_below(&self) -> Option<Value> {
        let Predicate::Intervals(iset) = self else {
            return None;
        };
        let [only] = iset.intervals().as_slice() else {
            return None;
        };
        let top = only.rval()?.clone();
        (Predicate::at_or_below(top.clone()) == *self).then_some(top)
    }

    /// This predicate, over the keys of level `above.len()`, without the regions the
    /// levels `above` already name whole, or `None` where it keeps all of them. `above[d]` is
    /// a predicate over the paths reaching level `d`, outermost first.
    ///
    /// A level names a key whole when it says the key is complete, or releases it, at every
    /// depth beneath, so a path running through that key says nothing the level has not.
    /// Each arm loses those paths from the enclosing paths it is qualified by, which is
    /// exact ([`minus`](Self::minus)) however the arm's paths are spelled, and an arm left
    /// qualified by none is dropped. An unqualified arm stands under every enclosing path,
    /// so it goes only where every path is covered: removing some would qualify an arm that
    /// said nothing about paths, a longer spelling of the same statement.
    pub(crate) fn without_covered(&self, above: &[Predicate]) -> Option<Predicate> {
        // The covered paths reaching this level's keys: `above[d]` read `depth - 1 - d`
        // levels further in, qualified by `True` once per level between.
        let depth = above.len();
        let covered = above
            .iter()
            .enumerate()
            .map(|(level, whole)| {
                (level + 1..depth).fold(whole.clone(), |region, _| {
                    Predicate::qualified(region, Predicate::True)
                })
            })
            .fold(Predicate::False, |all, region| all.union(&region));
        if covered.is_false() {
            return None;
        }
        let arms: Vec<&Predicate> = match self {
            Predicate::Or(arms) => arms.iter().collect(),
            one => vec![one],
        };
        let kept: Vec<Predicate> = arms
            .iter()
            .map(|arm| match arm {
                Predicate::Qualified { enclosing, here } => {
                    Predicate::qualified(enclosing.minus(&covered), (**here).clone())
                }
                _ if covered.subsumes(&Predicate::True) => Predicate::False,
                unqualified => (*unqualified).clone(),
            })
            .filter(|arm| !arm.is_false())
            .collect();
        let kept = match kept.is_empty() {
            true => Predicate::False,
            false => Predicate::flatten_or(kept),
        };
        (kept != *self).then_some(kept)
    }

    /// The predicate admitting exactly `set`, in canonical form.
    ///
    /// Every operation that yields an interval set answers through here, so one region has
    /// one spelling. The set is clamped to its type's range ([`type_range`]): the crate
    /// does not know that a `UInt` stops at 0, and `(-∞, 3]` and `[0, 3]` spell one set of
    /// positions. Each bound is normalized, which the crate does for a finite interval and
    /// not for a half-bounded one, so a complement's `(4, ∞)` reads as `[5, ∞)`. Then the
    /// empty set is [`Predicate::False`], a set covering its type is [`Predicate::True`],
    /// and intervals meeting at a shared value are merged.
    pub(crate) fn intervals(set: IntervalSet<Value>) -> Predicate {
        let range = sample(&set).and_then(type_range);
        let set = match &range {
            Some(range) => set.intersection(range),
            None => set,
        };
        let set = coalesce_abutting(IntervalSet::new(
            set.intervals().iter().map(normalized).collect(),
        ));
        if set.is_empty() {
            return Predicate::False;
        }
        if is_whole(&set, range.as_ref()) {
            return Predicate::True;
        }
        Predicate::Intervals(set)
    }

    /// Everything ordered at or below `v`: the watermark a prefix release names.
    ///
    /// A record key is ordered lexicographically over its fields in name order, as
    /// [`Value`]'s comparison orders it, and a prefix of that order is a staircase of boxes
    /// ([`BoxShape`]), one per field: `≤ (𝑎, 𝑏)` is `{_0 < 𝑎} ∪ {_0 = 𝑎, _1 ≤ 𝑏}`. That is
    /// the construction [`domain_prefix`](super::domain_prefix) takes across levels, taken
    /// across fields.
    pub fn at_or_below(v: Value) -> Predicate {
        Predicate::up_to(v, true)
    }

    /// Everything ordered strictly below `v`.
    ///
    /// What the keys before a path prefix's head are: the head's own key is only partly
    /// covered, so it is excluded rather than taken whole. A record is a staircase, as in
    /// [`at_or_below`](Self::at_or_below).
    pub(crate) fn below(v: Value) -> Predicate {
        Predicate::up_to(v, false)
    }

    fn up_to(v: Value, inclusive: bool) -> Predicate {
        // A prefix of a union domain is the tags ordered before the bound's whole, part of its
        // own, and none after, which one `rest` for every unnamed tag cannot spell.
        assert!(
            !matches!(v, Value::Union { .. }),
            "a union key has no prefix spelling without its domain's tags: {v:?}"
        );
        // `Unit` is the one value of its type: `≤ ()` is everything and `< ()` nothing.
        if v == Value::Unit {
            return match inclusive {
                true => Predicate::True,
                false => Predicate::False,
            };
        }
        let Value::Record(fields) = v else {
            let bound = match inclusive {
                true => Interval::unbound_closed(v),
                false => Interval::unbound_open(v),
            };
            return Predicate::intervals(IntervalSet::new(vec![bound]));
        };
        let mut names: Vec<&String> = fields.keys().collect();
        names.sort();
        // Step `i` agrees with `v` on the fields before `i`, lies below it on field `i`,
        // and admits anything after. The last step's field takes `v`'s own value too where
        // the bound is inclusive, which is what puts `v` itself in the region.
        let steps: Vec<Predicate> = (0..names.len())
            .map(|i| {
                let last = i + 1 == names.len();
                Predicate::Record(
                    names
                        .iter()
                        .enumerate()
                        .map(|(j, name)| {
                            let field = fields[*name].clone();
                            let p = match j.cmp(&i) {
                                Ordering::Less => Predicate::point(field),
                                Ordering::Equal => Predicate::up_to(field, inclusive && last),
                                Ordering::Greater => Predicate::True,
                            };
                            ((*name).clone(), p)
                        })
                        .collect(),
                )
            })
            .filter(|step| !step.is_false())
            .collect();
        match steps.is_empty() {
            // A record with no fields has one value, so `≤` admits it and `<` does not.
            true if names.is_empty() && inclusive => Predicate::True,
            true => Predicate::False,
            false => Predicate::flatten_or(steps),
        }
    }

    /// Converts a batch of concrete domain values into the predicate admitting exactly those values.
    ///
    /// Each scalar value becomes a point interval; records are split field-by-field.
    pub fn from_column_value(cv: &ColumnValue) -> Predicate {
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
                // Records have no interval spelling, so the set is one point box per row,
                // which `flatten_or` joins where the rows fill a box.
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
                // A column names only the tags it holds; the rest admit nothing.
                Predicate::tagged(
                    arms.map(|_, arm| Predicate::from_column_value(arm.values())),
                    false,
                )
            }
        }
    }

    /// Check whether this predicate is structurally valid for the given [`Extent`].
    ///
    /// A predicate is applicable when it makes sense to use it as a filter over
    /// values drawn from that extent:
    ///
    /// - [`Predicate::True`] and [`Predicate::False`] are applicable to any extent.
    /// - [`Predicate::Intervals`] is applicable to a **scalar** ordered extent
    ///   ([`Extent::Base`], [`Extent::UIntRange`]) whose element type matches the
    ///   predicate's value type.
    /// - [`Predicate::Record`] is applicable to [`Extent::Record`] when the key sets
    ///   match and each field predicate is applicable to its field extent.
    /// - [`Predicate::Or`] is applicable when every arm is applicable to the extent.
    ///
    /// A record extent therefore takes only per-field boxes. A prefix of its lexicographic
    /// order is one of those too, a staircase ([`at_or_below`](Self::at_or_below)), so an
    /// interval over record values is refused here rather than left to meet a box it has
    /// no rule against.
    ///
    /// One extent, so a predicate naming an enclosing path is **not** applicable: the
    /// domain it claims has levels this one does not.
    /// [`is_applicable_over`](Self::is_applicable_over) is the form that carries them.
    pub fn is_applicable_to(&self, extent: &Extent) -> bool {
        self.is_applicable_over(std::slice::from_ref(extent))
    }

    /// [`is_applicable_to`](Self::is_applicable_to) over the levels a path runs through,
    /// outermost first.
    ///
    /// The mirror of [`contains_path`](Self::contains_path): a predicate that names an
    /// enclosing path is checked against that path's extents, so a component read
    /// against the wrong level is refused here rather than at the value that trips over
    /// it. Every other arm describes the innermost level alone.
    pub fn is_applicable_over(&self, extents: &[Extent]) -> bool {
        match self {
            Predicate::Qualified { enclosing, here } => {
                let Some((own, above)) = extents.split_last() else {
                    return false;
                };
                !above.is_empty()
                    && enclosing.is_applicable_over(above)
                    && here.is_applicable_over(std::slice::from_ref(own))
            }
            // An arm may name an enclosing path, so the levels go down whole.
            Predicate::Or(arms) => arms.iter().all(|p| p.is_applicable_over(extents)),
            innermost => extents
                .last()
                .is_some_and(|extent| innermost.applies_to_level(extent)),
        }
    }

    fn applies_to_level(&self, extent: &Extent) -> bool {
        // Resolve transparent extent wrappers before matching.
        let extent = match extent {
            Extent::DataSourceDomain(src) => src.borrow().element_extent(),
            Extent::Restricted { base, .. } => *base.clone(),
            other => other.clone(),
        };
        match self {
            Predicate::True | Predicate::False => true,
            Predicate::Intervals(s) => {
                // An empty interval set is semantically False — applicable everywhere.
                let Some(sample) = s
                    .intervals()
                    .first()
                    .and_then(|iv| iv.lval().or_else(|| iv.rval()))
                else {
                    return true;
                };
                value_is_of_extent(sample, &extent)
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
            // Handled by `is_applicable_over`, which carries the levels these two need.
            Predicate::Qualified { .. } | Predicate::Or(_) => {
                unreachable!("a path-shaped predicate is checked over its levels")
            }
            // Union: each per-variant predicate must be applicable to its variant extent.
            Predicate::Union { tags, .. } => match &extent {
                // Width subtyping: the predicate may name fewer tags than the extent
                // declares, and `rest` covers the others, but every tag it does name must
                // match that tag's extent.
                Extent::Union(ext_arms) => tags
                    .iter()
                    .all(|(k, p)| ext_arms.get(k).is_some_and(|e| p.is_applicable_to(e))),
                _ => false,
            },
        }
    }
}

/// The whole of `sample`'s type as an interval, where the type has a least or greatest
/// value; `None` for a type unbounded on both sides.
///
/// `Value`'s discrete [`Domain`] knows each value's neighbours but not where a type ends,
/// so the crate reads `(-∞, 0)` over `UInt` as nonempty. Clamping every set to this range
/// is what makes emptiness, universality, and containment exact.
fn type_range(sample: &Value) -> Option<IntervalSet<Value>> {
    let range = match sample {
        Value::UInt(_) => Interval::closed_unbound(Value::UInt(0)),
        Value::Int(_) => Interval::closed(Value::Int(i64::MIN), Value::Int(i64::MAX)),
        Value::Bool(_) => Interval::closed(Value::Bool(false), Value::Bool(true)),
        Value::String(_) => Interval::closed_unbound(Value::String("".into())),
        _ => return None,
    };
    Some(IntervalSet::from(range))
}

/// A value `set` names, from which its type is read.
fn sample(set: &IntervalSet<Value>) -> Option<&Value> {
    set.intervals()
        .iter()
        .find_map(|iv| iv.lval().or_else(|| iv.rval()))
}

/// `interval` with each bound normalized, closed where the domain names the neighbouring
/// value ([`Bound::normalized`](intervalsets::Bound::normalized)).
fn normalized(interval: &Interval<Value>) -> Interval<Value> {
    match (interval.left(), interval.right()) {
        (None, None) => interval.clone(),
        (Some(left), None) => {
            Interval::new_half_bounded(Side::Left, left.clone().normalized(Side::Left))
        }
        (None, Some(right)) => {
            Interval::new_half_bounded(Side::Right, right.clone().normalized(Side::Right))
        }
        (Some(left), Some(right)) => Interval::new_finite(left.clone(), right.clone()),
    }
}

/// Whether canonical `set` holds every value of its type, whose range is `range`: the
/// range itself once clamped and normalized, or the unbounded interval for a type with no
/// least or greatest value.
fn is_whole(set: &IntervalSet<Value>, range: Option<&IntervalSet<Value>>) -> bool {
    match range {
        Some(range) => set == range,
        None => {
            matches!(set.intervals().as_slice(), [only] if only.left().is_none() && only.right().is_none())
        }
    }
}

/// Returns `true` if `v`'s runtime type is consistent with `extent`'s element type.
///
/// Used by [`Predicate::is_applicable_to`] to verify that an [`Predicate::Intervals`] is
/// paired with a scalar extent whose values it can be compared against. `Unit` is excluded
/// because predicates over a single-valued type are always `True`/`False` — no interval
/// set is ever created for a Unit column.
fn value_is_of_extent(v: &Value, extent: &Extent) -> bool {
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
    Predicate::intervals(IntervalSet::new_unchecked(intervals))
}

/// Merge intervals that meet at a shared value with no gap between them.
///
/// `intervalsets` merges intervals that overlap, and over a discrete domain those that are
/// adjacent, but leaves `(-∞, 𝑥)` beside `[𝑥, 𝑦]` as two — neither holds a value the other
/// does, and `𝑥` has no predecessor to make them adjacent. Together they are `(-∞, 𝑦]`.
/// Where the shared value is open on both sides it belongs to neither, which is a real gap
/// and stays.
fn coalesce_abutting(set: IntervalSet<Value>) -> IntervalSet<Value> {
    let mut merged: Vec<Interval<Value>> = Vec::with_capacity(set.intervals().len());
    for next in set.intervals() {
        match merged.pop() {
            None => merged.push(next.clone()),
            Some(prev) => match joined(&prev, next) {
                Some(one) => merged.push(one),
                None => merged.extend([prev, next.clone()]),
            },
        }
    }
    // The walk preserves the crate's ordering and disjointness, having only replaced
    // neighbours by their union.
    IntervalSet::new_unchecked(merged)
}

/// `a` and `b` as one interval where they meet at a single value with no gap, else `None`.
fn joined(a: &Interval<Value>, b: &Interval<Value>) -> Option<Interval<Value>> {
    let (end, start) = (a.right()?, b.left()?);
    if end.value() != start.value() || (end.is_open() && start.is_open()) {
        return None;
    }
    Some(match (a.left(), b.right()) {
        (None, None) => Interval::unbounded(),
        (None, Some(right)) => Interval::new_half_bounded(Side::Right, right.clone()),
        (Some(left), None) => Interval::new_half_bounded(Side::Left, left.clone()),
        (Some(left), Some(right)) => Interval::new_finite(left.clone(), right.clone()),
    })
}

/// Sort a one-level `Tile::DataFunction` by its domain values for deterministic comparison.
///
/// Handles `Ints` and `UInts` domains paired with `Scalar(Ints)` codomains; all other tile
/// forms are returned unchanged, a deeper function among them — reordering its outermost
/// level would have to carry every group with it. This is needed wherever key order depends
/// on [`HashMap`] iteration order (e.g. GroupBy, MapSource).
pub fn sort_function_by_domain(tile: Tile) -> Tile {
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
        Tile::data_function(
            mk_domain(sorted_d),
            Box::new(Tile::Scalar(ColumnValue::Ints(sorted_c))),
            domain_predicate,
            BitSet::new(),
        )
    }

    fn record_cv_to_extent(fields: &HashMap<String, ColumnValue>) -> Extent {
        Extent::Record(transform_hashmap_values(fields, |cv| match cv {
            ColumnValue::UInts(_) => Extent::Base(BaseType::UInt),
            ColumnValue::Records(inner) => record_cv_to_extent(inner),
            _ => todo!(),
        }))
    }

    match tile {
        Tile::DataFunction {
            row_starts,
            domain,
            codomain,
            domain_predicate,
            deleted,
        } if row_starts.len() == 1 && !codomain.is_data_function() => {
            match (*codomain, domain) {
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
                        for &row in arm.rows() {
                            sorted_cod.push(cod_ints[row]);
                        }
                        let rows: Vec<usize> = (next_row..next_row + arm.len()).collect();
                        next_row += arm.len();
                        UnionArm::new(rows, arm.values().clone())
                    });
                    let domain = ColumnValue::Union(canonical);
                    domain.debug_assert_union_invariants();
                    Tile::data_function(
                        domain,
                        Box::new(Tile::Scalar(ColumnValue::Ints(sorted_cod))),
                        domain_predicate,
                        BitSet::new(),
                    )
                }
                (other_codomain, domain) => {
                    Tile::data_function(domain, Box::new(other_codomain), domain_predicate, deleted)
                }
            }
        }
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
    fn predicate_as_bool_at_or_below_is_none() {
        assert_eq!(Predicate::at_or_below(Value::Int(5)).as_bool(), None);
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
    fn predicate_as_bool_record_partial_field_is_none() {
        let p = record_pred(&[
            ("a", Predicate::True),
            ("b", Predicate::at_or_below(Value::UInt(3))),
        ]);
        assert_eq!(p.as_bool(), None);
    }

    /// A record's fields are an AND, so it admits nothing as soon as one of them does —
    /// whatever the others admit.
    #[test]
    fn predicate_as_bool_record_with_one_empty_field_is_false() {
        let p = record_pred(&[("a", Predicate::True), ("b", Predicate::False)]);
        assert_eq!(p.as_bool(), Some(false));
        assert!(p.is_false());
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
        // A proper prefix is neither empty nor whole.
        assert!(!Predicate::at_or_below(Value::Int(5)).is_true());
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
        // A proper prefix is neither empty nor whole.
        assert!(!Predicate::at_or_below(Value::Int(5)).is_false());
    }

    // ── Predicate::Qualified ──────────────────────────────────────────────────

    /// A key of a level, as a path of one component.
    fn at(key: usize) -> Vec<Value> {
        vec![Value::UInt(key)]
    }

    /// A node of the second level, as the path that reaches it.
    fn under(outer: usize, key: usize) -> Vec<Value> {
        vec![Value::UInt(outer), Value::UInt(key)]
    }

    fn u(v: usize) -> Value {
        Value::UInt(v)
    }

    /// Exactly `{k}`.
    fn only(k: usize) -> Predicate {
        Predicate::point(u(k))
    }

    /// The nodes of a 2×2 grid's second level that a statement per level calls complete.
    ///
    /// A level naming a node makes every node beneath it complete, so a depth-1 node is
    /// answered by either level — which is what lets a statement about the running
    /// enclosing row describe that row alone.
    fn complete_pairs(levels: &[Predicate]) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        for outer in 0..2 {
            for key in 0..2 {
                let path = under(outer, key);
                if levels[0].contains_path(&path[..1]) || levels[1].contains_path(&path) {
                    out.push((outer, key));
                }
            }
        }
        out
    }

    /// `beneath` and `within` are inverse, at the group's own level and deeper.
    #[test]
    fn beneath_and_within_are_inverse() {
        let row = [u(3)];
        let flat = Predicate::at_or_below(u(1));
        let placed = flat.beneath(&row, 0);
        assert!(placed.contains_path(&under(3, 1)) && !placed.contains_path(&under(2, 1)));
        assert_eq!(placed.within(&row, 0), flat);
        assert_eq!(flat.beneath(&[u(2)], 0).within(&row, 0), Predicate::False);

        let deep = Predicate::qualified(only(0), Predicate::at_or_below(u(4)));
        let placed = deep.beneath(&row, 1);
        assert!(placed.contains_path(&[u(3), u(0), u(4)]));
        assert!(!placed.contains_path(&[u(2), u(0), u(4)]));
        assert!(!placed.contains_path(&[u(3), u(1), u(4)]));
        assert_eq!(placed.within(&row, 1), deep);
    }

    /// `qualified_by` states a column's groups beneath its rows and nowhere else.
    #[test]
    fn qualified_by_states_a_column_only_under_its_rows() {
        let rows = uint_intervals(&[0, 1]);
        let q = Predicate::True.qualified_by(&rows, 0);
        assert!(q.contains_path(&under(1, 7)));
        assert!(!q.contains_path(&under(2, 7)));
        let deeper = Predicate::at_or_below(u(0)).qualified_by(&rows, 1);
        assert!(deeper.contains_path(&[u(1), u(9), u(0)]));
        assert!(!deeper.contains_path(&[u(2), u(9), u(0)]));
        assert!(!deeper.contains_path(&[u(1), u(9), u(1)]));
    }

    /// `as_at_or_below` reads back the watermark `at_or_below` was built from, and nothing
    /// else is one.
    #[test]
    fn as_at_or_below_reads_back_its_watermark() {
        for w in [0usize, 3, 100] {
            assert_eq!(Predicate::at_or_below(u(w)).as_at_or_below(), Some(u(w)));
        }
        assert_eq!(uint_intervals(&[0, 1, 2]).as_at_or_below(), Some(u(2)));
        assert_eq!(uint_intervals(&[1, 2]).as_at_or_below(), None);
        assert_eq!(Predicate::True.as_at_or_below(), None);
    }

    /// `Unit` has one value, so its point and `≤ ()` are everything and `< ()` is nothing,
    /// as `from_column_value` spells a column of units: taking a unit key out of a statement
    /// leaves one that still applies to a `Unit` domain.
    #[test]
    fn a_unit_key_is_the_whole_unit_domain() {
        let unit = Extent::Base(BaseType::Unit);
        assert_eq!(Predicate::point(Value::Unit), Predicate::True);
        assert_eq!(Predicate::at_or_below(Value::Unit), Predicate::True);
        assert_eq!(Predicate::below(Value::Unit), Predicate::False);
        assert_eq!(
            Predicate::point(Value::Unit),
            Predicate::from_column_value(&ColumnValue::Units(1))
        );
        let rest = Predicate::True.minus(&Predicate::exactly(&[Value::Unit]));
        assert_eq!(rest, Predicate::False);
        assert!(rest.is_applicable_to(&unit));
    }

    #[test]
    fn qualified_by_everything_is_the_rectangle_itself() {
        let here = Predicate::at_or_below(u(1));
        assert_eq!(Predicate::qualified(Predicate::True, here.clone()), here);
    }

    #[test]
    fn qualified_with_an_empty_side_is_empty() {
        assert_eq!(
            Predicate::qualified(Predicate::False, Predicate::at_or_below(u(1))),
            Predicate::False
        );
        assert_eq!(
            Predicate::qualified(only(1), Predicate::False),
            Predicate::False
        );
    }

    #[test]
    fn a_rectangle_answers_for_the_key_under_every_enclosing_path() {
        let rect = Predicate::at_or_below(u(1));
        assert!(rect.contains_path(&under(0, 1)));
        assert!(
            rect.contains_path(&under(7, 1)),
            "including a row not yet seen"
        );
        assert!(!rect.contains_path(&under(0, 2)));
    }

    #[test]
    fn a_qualified_box_answers_only_under_its_enclosing_path() {
        let box_ = Predicate::qualified(only(1), Predicate::at_or_below(u(0)));
        assert!(box_.contains_path(&under(1, 0)));
        assert!(!box_.contains_path(&under(1, 1)), "past the keys it names");
        assert!(
            !box_.contains_path(&under(0, 0)),
            "under another enclosing row"
        );
        assert!(
            !box_.contains_path(&at(1)),
            "the enclosing node is not itself whole"
        );
    }

    /// The case the arm exists for: a sequential drive through `(1, 0)` of a 2×2 nest.
    ///
    /// Without it the second level can only name key *values*, so the nearest statement
    /// it can make is `{0, 1}`, which claims `(1, 1)` — a position the drive has not run.
    #[test]
    fn a_drive_prefix_is_one_statement_per_level() {
        let prefix = [
            Predicate::below(u(1)),
            Predicate::qualified(only(1), Predicate::at_or_below(u(0))),
        ];
        assert_eq!(complete_pairs(&prefix), vec![(0, 0), (0, 1), (1, 0)]);

        let unqualified = [
            Predicate::below(u(1)),
            Predicate::from_column_value(&ColumnValue::UInts(vec![0, 1])),
        ];
        assert_eq!(
            complete_pairs(&unqualified),
            vec![(0, 0), (0, 1), (1, 0), (1, 1)],
            "read under every enclosing row, which is all the level could state before \
             this arm, (1, 1) is over-claimed"
        );
    }

    /// Completeness that really does hold under every enclosing row stays the cheapest
    /// thing to say, including under rows not yet seen.
    #[test]
    fn a_slice_across_every_enclosing_row_needs_no_enclosing_path() {
        let slice = Predicate::at_or_below(u(1));
        assert!(!slice.qualifies());
        for outer in [0usize, 1, 99] {
            assert!(slice.contains_path(&under(outer, 0)));
            assert!(slice.contains_path(&under(outer, 1)));
            assert!(!slice.contains_path(&under(outer, 2)));
        }
    }

    #[test]
    fn boxes_sharing_a_component_join_into_one() {
        let (a, b) = (
            Predicate::qualified(only(1), only(0)),
            Predicate::qualified(only(1), only(1)),
        );
        assert_eq!(
            a.union(&b),
            Predicate::qualified(only(1), only(0).union(&only(1))),
            "the same enclosing path gains keys"
        );

        let (c, d) = (
            Predicate::qualified(only(0), only(1)),
            Predicate::qualified(only(1), only(1)),
        );
        assert_eq!(
            c.union(&d),
            Predicate::qualified(only(0).union(&only(1)), only(1)),
            "the same keys gain enclosing paths"
        );
    }

    #[test]
    fn boxes_sharing_no_component_join_as_a_union() {
        let (a, b) = (
            Predicate::qualified(only(0), only(0)),
            Predicate::qualified(only(1), only(1)),
        );
        let joined = a.union(&b);
        assert!(joined.contains_path(&under(0, 0)));
        assert!(joined.contains_path(&under(1, 1)));
        assert!(!joined.contains_path(&under(0, 1)));
        assert!(!joined.contains_path(&under(1, 0)));
    }

    #[test]
    fn boxes_meet_componentwise() {
        let a = Predicate::qualified(Predicate::at_or_below(u(1)), Predicate::at_or_below(u(1)));
        let b = Predicate::qualified(only(1), Predicate::at_or_below(u(0)));
        assert_eq!(
            a.intersect(&b),
            b,
            "the tighter component wins on each side"
        );
    }

    #[test]
    fn a_rectangle_meets_a_box_by_narrowing_its_keys() {
        let box_ = Predicate::qualified(only(1), Predicate::at_or_below(u(1)));
        let rect = Predicate::at_or_below(u(0));
        assert_eq!(
            box_.intersect(&rect),
            Predicate::qualified(only(1), Predicate::at_or_below(u(0))),
            "the enclosing path it already named, over the keys both admit"
        );
    }

    #[test]
    fn one_box_less_another_leaves_the_rows_it_did_not_name() {
        // Everything of the 2×2 grid, less the keys `≤ 0` under enclosing row 1.
        let all = Predicate::True;
        let taken = Predicate::qualified(only(1), Predicate::at_or_below(u(0)));
        let left = all.minus(&taken);
        let held: Vec<(usize, usize)> = (0..2)
            .flat_map(|o| (0..2).map(move |k| (o, k)))
            .filter(|(o, k)| left.contains_path(&under(*o, *k)))
            .collect();
        assert_eq!(held, vec![(0, 0), (0, 1), (1, 1)]);
    }

    #[test]
    fn an_unqualified_predicate_subsumes_a_qualified_one_over_the_same_keys() {
        let everywhere = Predicate::at_or_below(u(1));
        let under_one = Predicate::qualified(only(1), only(0));
        assert!(everywhere.subsumes(&under_one));
        assert!(
            !under_one.subsumes(&everywhere),
            "a qualified region covers no row it does not name"
        );
    }

    #[test]
    fn a_union_drops_the_box_a_rectangle_already_covers() {
        let rect = Predicate::at_or_below(u(1));
        let box_ = Predicate::qualified(only(1), only(0));
        assert_eq!(rect.union(&box_), rect);
    }

    #[test]
    fn exactly_a_path_admits_that_node_and_no_sibling() {
        let node = Predicate::exactly(&[u(1), u(0)]);
        assert!(node.contains_path(&under(1, 0)));
        assert!(!node.contains_path(&under(1, 1)));
        assert!(!node.contains_path(&under(0, 0)));
    }

    #[test]
    fn exactly_the_empty_path_pins_no_level() {
        assert_eq!(Predicate::exactly(&[]), Predicate::True);
    }

    #[test]
    fn a_qualified_predicate_is_not_applicable_to_a_single_level() {
        let box_ = Predicate::qualified(only(1), only(0));
        assert!(
            !box_.is_applicable_to(&range(2)),
            "it names an enclosing level the domain does not have"
        );
        assert!(box_.is_applicable_over(&[range(2), range(2)]));
    }

    /// The half of the check that a predicate over one level cannot make: whether the
    /// enclosing component belongs to the level above.
    #[test]
    fn a_qualified_predicates_enclosing_is_checked_against_the_level_above() {
        let box_ = Predicate::qualified(only(1), only(0));
        assert!(
            !box_.is_applicable_over(&[bool_ext(), range(2)]),
            "the enclosing component is a key, not a boolean"
        );
    }

    #[test]
    #[should_panic(expected = "read against the whole path")]
    fn reading_a_qualified_predicate_by_key_alone_is_refused() {
        let box_ = Predicate::qualified(only(1), only(0));
        box_.contains(&u(0));
    }

    // ── Predicate::intersect ──────────────────────────────────────────────────

    #[test]
    fn predicate_intersect_true_is_identity() {
        assert_eq!(
            Predicate::True.intersect(&Predicate::at_or_below(Value::Int(3))),
            Predicate::at_or_below(Value::Int(3))
        );
        assert_eq!(
            Predicate::at_or_below(Value::Int(3)).intersect(&Predicate::True),
            Predicate::at_or_below(Value::Int(3))
        );
    }

    #[test]
    fn predicate_intersect_false_is_annihilator() {
        assert_eq!(
            Predicate::False.intersect(&Predicate::True),
            Predicate::False
        );
        assert_eq!(
            Predicate::at_or_below(Value::Int(3)).intersect(&Predicate::False),
            Predicate::False
        );
    }

    #[test]
    fn predicate_intersect_at_or_below_picks_tighter() {
        // min(5, 3) → at_or_below(3)
        assert_eq!(
            Predicate::at_or_below(Value::Int(5)).intersect(&Predicate::at_or_below(Value::Int(3))),
            Predicate::at_or_below(Value::Int(3))
        );
        // min(3, 5) → at_or_below(3)
        assert_eq!(
            Predicate::at_or_below(Value::Int(3)).intersect(&Predicate::at_or_below(Value::Int(5))),
            Predicate::at_or_below(Value::Int(3))
        );
    }

    #[test]
    fn predicate_intersect_record_field_by_field() {
        let p1 = record_pred(&[("a", Predicate::True), ("b", uint_intervals(&[1, 2]))]);
        let p2 = record_pred(&[("a", uint_intervals(&[0])), ("b", Predicate::True)]);
        assert_eq!(
            p1.intersect(&p2),
            record_pred(&[("a", uint_intervals(&[0])), ("b", uint_intervals(&[1, 2]))])
        );
    }

    /// A box with an empty component admits nothing, and its meet says so rather than
    /// keeping a record that reads as nonempty.
    #[test]
    fn a_record_meet_with_an_empty_field_is_empty() {
        let p1 = record_pred(&[("a", Predicate::True), ("b", uint_intervals(&[1]))]);
        let p2 = record_pred(&[("a", Predicate::True), ("b", uint_intervals(&[2]))]);
        assert_eq!(p1.intersect(&p2), Predicate::False);
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
        // Both values are the whole of `Bool`, which has one spelling.
        assert_eq!(
            Predicate::from_column_value(&ColumnValue::Bools(bv)),
            Predicate::True
        );
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

    fn pair(a: usize, b: usize) -> Value {
        Value::Record(HashMap::from([
            ("_0".to_string(), Value::UInt(a)),
            ("_1".to_string(), Value::UInt(b)),
        ]))
    }

    /// A prefix of a record key's lexicographic order is a staircase of records, one per
    /// field: `≤ (1, 0)` is `{_0 < 1} ∪ {_0 = 1, _1 ≤ 0}`, a per-field region like any other.
    #[test]
    fn a_prefix_of_a_record_key_is_a_staircase_of_records() {
        let prefix = Predicate::at_or_below(pair(1, 0));
        assert_eq!(
            prefix,
            Predicate::Or(vec![
                record_pred(&[("_0", uint_intervals(&[0])), ("_1", Predicate::True)]),
                record_pred(&[("_0", uint_intervals(&[1])), ("_1", uint_intervals(&[0]))]),
            ])
        );
        assert!(
            prefix.contains(&pair(0, 9)),
            "a prefix reaches past a field's bound"
        );
        assert!(prefix.contains(&pair(1, 0)));
        assert!(!prefix.contains(&pair(1, 1)));
        assert!(!Predicate::below(pair(1, 0)).contains(&pair(1, 0)));
        let extent = Extent::Record(HashMap::from([
            ("_0".to_string(), Extent::Base(BaseType::UInt)),
            ("_1".to_string(), Extent::Base(BaseType::UInt)),
        ]));
        assert!(prefix.is_applicable_to(&extent));
    }

    /// A prefix and a region per field meet under the box algebra, where two readings of
    /// one record key would have no rule between them.
    #[test]
    fn a_record_prefix_meets_a_per_field_region() {
        let prefix = Predicate::at_or_below(pair(1, 0));
        let column = Predicate::from_column_value(&pairs(&[0, 1], &[0, 0]));
        assert!(prefix.subsumes(&column));
        assert!(!column.subsumes(&prefix));
        let rest = prefix.minus(&column);
        assert!(rest.contains(&pair(0, 9)));
        assert!(!rest.contains(&pair(0, 0)) && !rest.contains(&pair(1, 0)));
        // The same region, though a union of boxes may spell it with different boxes.
        let joined = prefix.union(&column);
        assert!(
            joined.subsumes(&prefix) && prefix.subsumes(&joined),
            "{joined:?}"
        );
    }

    /// An interval over record values has no rule against a per-field region, so it is
    /// refused where a guard is checked rather than built.
    #[test]
    fn an_interval_over_record_values_is_not_applicable() {
        let extent = Extent::Record(HashMap::from([
            ("_0".to_string(), Extent::Base(BaseType::UInt)),
            ("_1".to_string(), Extent::Base(BaseType::UInt)),
        ]));
        let over_records =
            Predicate::Intervals(IntervalSet::new(vec![Interval::unbound_closed(pair(1, 0))]));
        assert!(!over_records.is_applicable_to(&extent));
    }

    // ── Exact containment and one spelling per region ─────────────────────────

    /// A union can cover a box that none of its arms covers alone. Here the arms differ in
    /// both fields, so they do not join, and each holds half of the box's `_1` range.
    #[test]
    fn a_union_subsumes_a_box_its_arms_cover_only_together() {
        let low = record_pred(&[
            ("_0", uint_intervals(&[0, 1])),
            ("_1", uint_intervals(&[0, 1, 2])),
        ]);
        let high = record_pred(&[
            ("_0", uint_intervals(&[0, 1, 2])),
            ("_1", uint_intervals(&[3, 4])),
        ]);
        let both = low.union(&high);
        assert_eq!(arm_count(&both), 2, "{both:?}");
        let box_ = record_pred(&[
            ("_0", uint_intervals(&[0, 1])),
            ("_1", uint_intervals(&[0, 1, 2, 3, 4])),
        ]);
        assert!(!low.subsumes(&box_) && !high.subsumes(&box_));
        assert!(both.subsumes(&box_));
        assert!(
            !box_.subsumes(&both),
            "the union holds (2, 3), the box does not"
        );
    }

    /// The interval crate does not know that a `UInt` stops at 0, so `(-∞, 3]` and `[0, 3]`
    /// would be two spellings of one set of positions. `Predicate::intervals` makes them
    /// one, and a set covering the type is `True`.
    #[test]
    fn a_uint_set_has_one_spelling() {
        let half_line = Predicate::intervals(IntervalSet::new(vec![Interval::unbound_closed(
            Value::UInt(3),
        )]));
        assert_eq!(half_line, uint_intervals(&[0, 1, 2, 3]));
        assert_eq!(half_line, Predicate::at_or_below(Value::UInt(3)));
        assert_eq!(
            Predicate::True.minus(&half_line),
            Predicate::intervals(IntervalSet::new(vec![Interval::closed_unbound(
                Value::UInt(4)
            )]))
        );
        assert_eq!(
            half_line.union(&Predicate::True.minus(&half_line)),
            Predicate::True
        );
        assert!(Predicate::below(Value::UInt(0)).is_false());
    }

    /// Two predicates over different domains have no containment to answer.
    #[test]
    #[should_panic(expected = "incompatible predicates")]
    fn subsumes_refuses_predicates_over_different_domains() {
        uint_intervals(&[1]).subsumes(&record_pred(&[("_0", uint_intervals(&[1]))]));
    }

    /// Rows stated one at a time, each a box qualified by its own enclosing row, join into
    /// one box where their keys agree, not one arm per row.
    #[test]
    fn rows_stated_one_at_a_time_join_into_one_box() {
        let row = |r: usize| Predicate::qualified(Predicate::point(u(r)), uint_intervals(&[0, 1]));
        let rows = (1..4).fold(row(0), |acc, r| acc.union(&row(r)));
        assert_eq!(
            rows,
            Predicate::qualified(uint_intervals(&[0, 1, 2, 3]), uint_intervals(&[0, 1]))
        );
    }

    // ── Joining record arms ───────────────────────────────────────────────────

    fn pairs(outer: &[usize], inner: &[usize]) -> ColumnValue {
        ColumnValue::Records(HashMap::from([
            ("_0".to_string(), ColumnValue::UInts(outer.to_vec())),
            ("_1".to_string(), ColumnValue::UInts(inner.to_vec())),
        ]))
    }

    fn arm_count(p: &Predicate) -> usize {
        match p {
            Predicate::Or(arms) => arms.len(),
            _ => 1,
        }
    }

    /// A column of pairs filling a rectangle is one record, whichever way it is assembled:
    /// read whole, or unioned in one point at a time.
    #[test]
    fn pairs_filling_a_rectangle_join_into_one_record() {
        let square = pairs(&[0, 0, 1, 1], &[0, 1, 0, 1]);
        let whole = Predicate::from_column_value(&square);
        assert_eq!(arm_count(&whole), 1, "{whole:?}");
        let point = |a: usize, b: usize| Predicate::from_column_value(&pairs(&[a], &[b]));
        let one_by_one = [(0, 1), (1, 0), (1, 1)]
            .into_iter()
            .fold(point(0, 0), |acc, (a, b)| acc.union(&point(a, b)));
        assert_eq!(one_by_one, whole);
        for (a, b) in [(0, 0), (0, 1), (1, 0), (1, 1)] {
            assert!(whole.contains(&Value::Record(HashMap::from([
                ("_0".to_string(), Value::UInt(a)),
                ("_1".to_string(), Value::UInt(b)),
            ]))));
        }
    }

    /// Rows of different lengths have no single record, and the join is greedy: arms join
    /// in the order they arrive, so the result is exact and at most one arm per row rather
    /// than the fewest records covering the set.
    #[test]
    fn rows_of_different_lengths_stay_exact_within_an_arm_per_row() {
        let jagged = pairs(&[0, 0, 1, 2, 2], &[0, 1, 0, 0, 1]);
        let p = Predicate::from_column_value(&jagged);
        assert!(arm_count(&p) <= 3, "one arm per row at most: {p:?}");
        let pair = |a: usize, b: usize| {
            Value::Record(HashMap::from([
                ("_0".to_string(), Value::UInt(a)),
                ("_1".to_string(), Value::UInt(b)),
            ]))
        };
        for (a, b) in [(0, 0), (0, 1), (1, 0), (2, 0), (2, 1)] {
            assert!(p.contains(&pair(a, b)), "({a}, {b}) is in the column");
        }
        assert!(!p.contains(&pair(1, 1)), "(1, 1) is not");
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
        let p = record_pred(&[
            ("a", Predicate::True),
            ("b", Predicate::at_or_below(Value::UInt(3))),
        ]);
        let result = p.split_record(&fields);
        assert_eq!(result["a"], Predicate::True);
        assert_eq!(result["b"], Predicate::at_or_below(Value::UInt(3)));
    }

    /// A record that admits nothing gives every field nothing, rather than handing one of
    /// them a share of a row it never held.
    #[test]
    fn split_record_of_an_empty_record_gives_every_field_nothing() {
        let fields: HashMap<String, ()> = [("a", ()), ("b", ())]
            .iter()
            .map(|(k, v)| (k.to_string(), *v))
            .collect();
        let p = record_pred(&[("a", Predicate::True), ("b", Predicate::False)]);
        let result = p.split_record(&fields);
        assert_eq!(result["a"], Predicate::False);
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
            Predicate::True.union(&Predicate::at_or_below(Value::UInt(5))),
            Predicate::True
        );
    }

    #[test]
    fn union_true_annihilates_rhs() {
        assert_eq!(
            Predicate::at_or_below(Value::UInt(5)).union(&Predicate::True),
            Predicate::True
        );
    }

    // False is the identity: False ∪ x = x and x ∪ False = x.
    #[test]
    fn union_false_identity_lhs() {
        let p = Predicate::at_or_below(Value::UInt(3));
        assert_eq!(Predicate::False.union(&p), p);
    }

    #[test]
    fn union_false_identity_rhs() {
        let p = Predicate::at_or_below(Value::UInt(3));
        assert_eq!(p.union(&Predicate::False), p);
    }

    // at_or_below ∪ at_or_below: keep the looser (larger) bound.
    #[test]
    fn union_at_or_below_keeps_larger() {
        assert_eq!(
            Predicate::at_or_below(Value::UInt(7)).union(&Predicate::at_or_below(Value::UInt(3))),
            Predicate::at_or_below(Value::UInt(7))
        );
        assert_eq!(
            Predicate::at_or_below(Value::UInt(3)).union(&Predicate::at_or_below(Value::UInt(7))),
            Predicate::at_or_below(Value::UInt(7))
        );
    }

    #[test]
    fn union_at_or_below_equal_bounds() {
        assert_eq!(
            Predicate::at_or_below(Value::UInt(5)).union(&Predicate::at_or_below(Value::UInt(5))),
            Predicate::at_or_below(Value::UInt(5))
        );
    }

    // A prefix ∪ a point beyond it: one interval set holding both.
    #[test]
    fn union_at_or_below_with_intervals_lhs() {
        // [0, 3] ∪ {7} → Intervals containing both 0, 3, and 7; but not 4 or 6.
        let intervals = Predicate::from_column_value(&ColumnValue::UInts(vec![7]));
        let result = Predicate::at_or_below(Value::UInt(3)).union(&intervals);
        assert!(intervals_contains(&result, Value::UInt(0)), "0 in [0,3]");
        assert!(intervals_contains(&result, Value::UInt(3)), "3 in [0,3]");
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
    fn union_at_or_below_with_intervals_rhs() {
        // {7} ∪ [0, 3] — commutative, same outcome.
        let intervals = Predicate::from_column_value(&ColumnValue::UInts(vec![7]));
        let result = intervals.union(&Predicate::at_or_below(Value::UInt(3)));
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

    /// The set below a value, joined with that value on its own, is the set up to it.
    /// `intervalsets` leaves the two apart — neither holds a value the other does, and
    /// `u0` has no predecessor to make them adjacent — so [`coalesce_abutting`] merges
    /// them. Two spellings of one region compare unequal, which is what release
    /// accumulation reads as a change.
    #[test]
    fn union_below_a_value_with_that_value_is_the_bound() {
        let u0 = Value::UInt(0);
        let point = Predicate::from_column_value(&ColumnValue::UInts(vec![0]));
        let joined = Predicate::below(u0.clone()).union(&point);
        assert_eq!(
            joined,
            Predicate::intervals(IntervalSet::new(vec![Interval::unbound_closed(u0)]))
        );
    }

    /// Only the value shared by two bounds closes the gap. Open on both sides it belongs
    /// to neither interval, so they stay apart.
    #[test]
    fn union_keeps_intervals_open_on_both_sides_of_the_shared_value_apart() {
        let u5 = Value::UInt(5);
        let below = Predicate::below(u5.clone());
        let above = Predicate::intervals(IntervalSet::new(vec![Interval::open_closed(
            u5,
            Value::UInt(9),
        )]));
        let Predicate::Intervals(joined) = below.union(&above) else {
            panic!("two interval sets union to one")
        };
        assert_eq!(joined.intervals().len(), 2, "got {joined:?}");
        assert!(
            !joined.contains(&Value::UInt(5)),
            "the gap holds: {joined:?}"
        );
    }

    /// Merging a pair exposes the next one, so a run of abutting intervals collapses to a
    /// single interval rather than to a shorter run. The keys are strings, which have no
    /// adjacent value: the crate merges neither, so what collapses the run is
    /// [`coalesce_abutting`] alone.
    #[test]
    fn a_run_of_abutting_intervals_collapses_to_one() {
        let key = |v: &str| Value::String(v.into());
        let run = Predicate::intervals(IntervalSet::new(vec![
            Interval::unbound_open(key("b")),
            Interval::closed_open(key("b"), key("d")),
            Interval::closed(key("d"), key("f")),
        ]));
        assert_eq!(
            run,
            Predicate::intervals(IntervalSet::new(vec![Interval::unbound_closed(key("f"))]))
        );
    }

    // Record ∪ Record: cannot push OR through AND, result must be Or([r1, r2]).
    #[test]
    fn union_record_predicates_produces_or() {
        // Neither record subsumes the other: r1 is looser on x, r2 is looser on y.
        // r1 admits {x≤5, y≤3}; r2 admits {x≤3, y≤7}.  Each admits records the
        // other does not, so neither is redundant and the union must be an Or.
        let r1 = record_pred(&[
            ("x", Predicate::at_or_below(Value::UInt(5))),
            ("y", Predicate::at_or_below(Value::UInt(3))),
        ]);
        let r2 = record_pred(&[
            ("x", Predicate::at_or_below(Value::UInt(3))),
            ("y", Predicate::at_or_below(Value::UInt(7))),
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
            record_pred(&[("_0", Predicate::at_or_below(Value::UInt(10)))]),
            record_pred(&[("_1", Predicate::at_or_below(Value::UInt(10)))]),
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
        assert!(Predicate::True.subsumes(&Predicate::at_or_below(Value::UInt(5))));
    }

    #[test]
    fn subsumes_non_true_does_not_subsume_true() {
        assert!(!Predicate::False.subsumes(&Predicate::True));
        assert!(!Predicate::at_or_below(Value::UInt(5)).subsumes(&Predicate::True));
    }

    // False (empty set) is subsumed by everything; it only subsumes itself.
    #[test]
    fn subsumes_everything_subsumes_false() {
        assert!(Predicate::False.subsumes(&Predicate::False));
        assert!(Predicate::True.subsumes(&Predicate::False));
        assert!(Predicate::at_or_below(Value::UInt(0)).subsumes(&Predicate::False));
    }

    #[test]
    fn subsumes_false_does_not_subsume_nonempty() {
        assert!(!Predicate::False.subsumes(&Predicate::True));
        assert!(!Predicate::False.subsumes(&Predicate::at_or_below(Value::UInt(3))));
    }

    // Prefixes: ≤ a ⊇ ≤ b iff a >= b.
    #[test]
    fn subsumes_at_or_below_looser_subsumes_tighter() {
        assert!(
            Predicate::at_or_below(Value::UInt(7))
                .subsumes(&Predicate::at_or_below(Value::UInt(3)))
        );
    }

    #[test]
    fn subsumes_at_or_below_equal_bounds() {
        assert!(
            Predicate::at_or_below(Value::UInt(5))
                .subsumes(&Predicate::at_or_below(Value::UInt(5)))
        );
    }

    #[test]
    fn subsumes_at_or_below_tighter_does_not_subsume_looser() {
        assert!(
            !Predicate::at_or_below(Value::UInt(3))
                .subsumes(&Predicate::at_or_below(Value::UInt(7)))
        );
    }

    // A prefix vs a point set.
    #[test]
    fn subsumes_at_or_below_subsumes_contained_interval_set() {
        // [0,10] ⊇ {3,7}: both points are <= 10.
        let s = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 7]));
        assert!(Predicate::at_or_below(Value::UInt(10)).subsumes(&s));
    }

    #[test]
    fn subsumes_at_or_below_does_not_subsume_escaping_interval_set() {
        // [0,5] ⊉ {3,7}: 7 > 5.
        let s = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 7]));
        assert!(!Predicate::at_or_below(Value::UInt(5)).subsumes(&s));
    }

    #[test]
    fn subsumes_interval_set_does_not_subsume_at_or_below() {
        // {3,7} ⊉ [0,10]: the prefix holds 0, which the set does not.
        let s = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 7]));
        assert!(!s.subsumes(&Predicate::at_or_below(Value::UInt(10))));
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
            ("x", Predicate::at_or_below(Value::UInt(10))),
            ("y", Predicate::at_or_below(Value::UInt(10))),
        ]);
        let small = record_pred(&[
            ("x", Predicate::at_or_below(Value::UInt(5))),
            ("y", Predicate::at_or_below(Value::UInt(3))),
        ]);
        assert!(big.subsumes(&small));
        assert!(!small.subsumes(&big));
    }

    #[test]
    fn subsumes_record_incomparable_fields() {
        // {x: ≤5, y: ≤10}: x-field is tighter than r2, y-field is looser.
        // Neither record subsumes the other.
        let r1 = record_pred(&[
            ("x", Predicate::at_or_below(Value::UInt(5))),
            ("y", Predicate::at_or_below(Value::UInt(10))),
        ]);
        let r2 = record_pred(&[
            ("x", Predicate::at_or_below(Value::UInt(10))),
            ("y", Predicate::at_or_below(Value::UInt(5))),
        ]);
        assert!(!r1.subsumes(&r2));
        assert!(!r2.subsumes(&r1));
    }

    #[test]
    fn subsumes_record_with_true_field_subsumes_anything_in_that_field() {
        // {x: True, y: ≤3} ⊇ {x: ≤7, y: ≤3}: True subsumes any x predicate.
        let big = record_pred(&[
            ("x", Predicate::True),
            ("y", Predicate::at_or_below(Value::UInt(3))),
        ]);
        let small = record_pred(&[
            ("x", Predicate::at_or_below(Value::UInt(7))),
            ("y", Predicate::at_or_below(Value::UInt(3))),
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
            Predicate::at_or_below(Value::UInt(3)).union(&Predicate::at_or_below(Value::UInt(10)));
        // union of two at_or_below bounds collapses to just at_or_below(10), so
        // construct an Or via Record union to exercise the Or path.
        let arm_a = record_pred(&[("x", Predicate::at_or_below(Value::UInt(10)))]);
        let arm_b = record_pred(&[("x", Predicate::at_or_below(Value::UInt(3)))]);
        let or_rec = arm_a.union(&arm_b); // Or([arm_a, arm_b]) simplified to [arm_a]
        let target = record_pred(&[("x", Predicate::at_or_below(Value::UInt(5)))]);
        assert!(or_pred.subsumes(&Predicate::at_or_below(Value::UInt(5))));
        assert!(or_rec.subsumes(&target));
    }

    #[test]
    fn subsumes_value_must_subsume_all_or_arms() {
        // ≤10 ⊇ Or([≤3, ≤7]) because 10 >= both 3 and 7.
        let or_pred =
            Predicate::at_or_below(Value::UInt(3)).union(&Predicate::at_or_below(Value::UInt(7)));
        assert!(Predicate::at_or_below(Value::UInt(10)).subsumes(&or_pred));
    }

    #[test]
    fn subsumes_value_does_not_subsume_or_if_any_arm_escapes() {
        // ≤5 ⊉ Or([≤3, ≤7]) because the ≤7 arm extends beyond 5.
        let or_pred =
            Predicate::at_or_below(Value::UInt(3)).union(&Predicate::at_or_below(Value::UInt(7)));
        assert!(!Predicate::at_or_below(Value::UInt(5)).subsumes(&or_pred));
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
        let p = Predicate::at_or_below(Value::UInt(5));
        assert_eq!(p.minus(&Predicate::False), p.clone());
        assert_eq!(Predicate::True.minus(&Predicate::False), Predicate::True);
        assert_eq!(Predicate::False.minus(&Predicate::False), Predicate::False);
    }

    #[test]
    fn minus_p_minus_true_is_false() {
        assert_eq!(
            Predicate::at_or_below(Value::UInt(5)).minus(&Predicate::True),
            Predicate::False
        );
        assert_eq!(Predicate::True.minus(&Predicate::True), Predicate::False);
    }

    #[test]
    fn minus_false_minus_anything_is_false() {
        assert_eq!(
            Predicate::False.minus(&Predicate::at_or_below(Value::UInt(5))),
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
    fn minus_intervals_minus_at_or_below() {
        // {[1,5]} ∖ (-∞,3] = {[4,5]}
        let a = Predicate::from_column_value(&ColumnValue::UInts(vec![1, 2, 3, 4, 5]));
        let result = a.minus(&Predicate::at_or_below(Value::UInt(3)));
        assert!(!result.contains(&Value::UInt(1)));
        assert!(!result.contains(&Value::UInt(3)));
        assert!(result.contains(&Value::UInt(4)));
        assert!(result.contains(&Value::UInt(5)));
        assert!(!result.contains(&Value::UInt(6)));
    }

    #[test]
    fn minus_at_or_below_minus_intervals_removes_overlap() {
        // (-∞,10] ∖ {[3,5]} = (-∞,2] ∪ {[6,10]}
        let intervals = Predicate::from_column_value(&ColumnValue::UInts(vec![3, 4, 5]));
        let result = Predicate::at_or_below(Value::UInt(10)).minus(&intervals);
        assert!(result.contains(&Value::UInt(1)));
        assert!(!result.contains(&Value::UInt(3)));
        assert!(!result.contains(&Value::UInt(5)));
        assert!(result.contains(&Value::UInt(6)));
        assert!(result.contains(&Value::UInt(10)));
        assert!(!result.contains(&Value::UInt(11)));
    }

    #[test]
    fn minus_at_or_below_minus_same_is_false() {
        // (-∞,5] ∖ (-∞,5] = ∅
        let p = Predicate::at_or_below(Value::UInt(5));
        assert_eq!(p.minus(&p.clone()), Predicate::False);
    }

    #[test]
    fn minus_at_or_below_minus_smaller_is_open_interval() {
        // (-∞,5] ∖ (-∞,3] = (3,5] — contains 4, 5 but not 3 or 6.
        let result =
            Predicate::at_or_below(Value::UInt(5)).minus(&Predicate::at_or_below(Value::UInt(3)));
        assert!(!result.contains(&Value::UInt(3)));
        assert!(result.contains(&Value::UInt(4)));
        assert!(result.contains(&Value::UInt(5)));
        assert!(!result.contains(&Value::UInt(6)));
    }

    #[test]
    fn minus_at_or_below_minus_larger_is_false() {
        // (-∞,3] ∖ (-∞,5] = ∅
        let result =
            Predicate::at_or_below(Value::UInt(3)).minus(&Predicate::at_or_below(Value::UInt(5)));
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

    /// Subtracting a record that admits nothing removes nothing.
    ///
    /// A record's fields are an AND, so `{a: [2], b: False}` admits nothing however much
    /// its `a` field admits. Subtracting field by field into a single record instead takes
    /// `a = 2` out of the minuend, which no row of the subtrahend ever held.
    #[test]
    fn minus_record_minus_an_empty_record_keeps_every_row() {
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
        assert_eq!(a.minus(&b), a);
    }

    /// A record less a record is one record per field, and each row the subtrahend does
    /// not hold survives — including a row that agrees with it in some fields but not all.
    #[test]
    fn minus_record_minus_record_keeps_the_rows_the_subtrahend_never_held() {
        let pt = |k: usize| Predicate::from_column_value(&ColumnValue::UInts(vec![k]));
        let pair = |x: usize, y: usize| {
            Value::Record(
                [
                    ("a".to_string(), Value::UInt(x)),
                    ("b".to_string(), Value::UInt(y)),
                ]
                .into_iter()
                .collect(),
            )
        };
        let all = record_pred(&[("a", pt(0).union(&pt(1))), ("b", pt(0).union(&pt(1)))]);
        let taken = record_pred(&[("a", pt(1)), ("b", pt(1))]);
        let left = all.minus(&taken);
        let held: Vec<(usize, usize)> = (0..2)
            .flat_map(|x| (0..2).map(move |y| (x, y)))
            .filter(|(x, y)| left.contains(&pair(*x, *y)))
            .collect();
        assert_eq!(held, vec![(0, 0), (0, 1), (1, 0)]);
    }

    /// Two records differing in one field are one record, so a difference that fragments
    /// into several does not stay fragmented where it need not.
    #[test]
    fn union_of_two_records_differing_in_one_field_is_one_record() {
        let pt = |k: usize| Predicate::from_column_value(&ColumnValue::UInts(vec![k]));
        let left = record_pred(&[("a", pt(0)), ("b", Predicate::True)]);
        let right = record_pred(&[("a", pt(1)), ("b", Predicate::True)]);
        assert_eq!(
            left.union(&right),
            record_pred(&[("a", pt(0).union(&pt(1))), ("b", Predicate::True)])
        );
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
    fn applicable_at_or_below_int_to_int_extent() {
        assert!(Predicate::at_or_below(Value::Int(5)).is_applicable_to(&int()));
    }

    #[test]
    fn applicable_at_or_below_uint_to_uint_extent() {
        assert!(Predicate::at_or_below(Value::UInt(5)).is_applicable_to(&uint_ext()));
    }

    #[test]
    fn applicable_at_or_below_uint_to_uint_range_extent() {
        assert!(Predicate::at_or_below(Value::UInt(3)).is_applicable_to(&range(10)));
    }

    #[test]
    fn applicable_at_or_below_bool_to_bool_extent() {
        assert!(Predicate::at_or_below(Value::Bool(true)).is_applicable_to(&bool_ext()));
    }

    #[test]
    fn applicable_at_or_below_string_to_string_extent() {
        assert!(Predicate::at_or_below(Value::String("z".into())).is_applicable_to(&str_ext()));
    }

    #[test]
    fn applicable_at_or_below_int_rejects_bool_extent() {
        assert!(!Predicate::at_or_below(Value::Int(5)).is_applicable_to(&bool_ext()));
    }

    #[test]
    fn applicable_at_or_below_int_rejects_uint_extent() {
        assert!(!Predicate::at_or_below(Value::Int(5)).is_applicable_to(&uint_ext()));
    }

    #[test]
    fn applicable_at_or_below_int_rejects_record_extent() {
        assert!(
            !Predicate::at_or_below(Value::Int(5)).is_applicable_to(&record_ext(&[("x", int())]))
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
        Predicate::over_every_tag(TagMap::from_positional(vec![p0, p1]))
    }

    fn union_val(tag: usize, inner: Value) -> Value {
        Value::Union {
            tag: FieldKey::Index(tag),
            inner: Box::new(inner),
        }
    }

    /// A union predicate names some tags and says with `rest` what every other admits, so a
    /// point, its complement and their combination are exact without the domain's tag list.
    #[test]
    fn a_union_predicate_is_exact_over_tags_it_does_not_name() {
        let one = Predicate::point(union_val(0, Value::Int(1)));
        assert!(one.contains(&union_val(0, Value::Int(1))));
        assert!(!one.contains(&union_val(0, Value::Int(2))));
        assert!(!one.contains(&union_val(1, Value::Int(1))));
        let rest = Predicate::True.minus(&one);
        assert!(!rest.contains(&union_val(0, Value::Int(1))));
        assert!(rest.contains(&union_val(0, Value::Int(2))));
        assert!(rest.contains(&union_val(1, Value::Int(1))));
        assert!(
            rest.contains(&union_val(7, Value::Int(1))),
            "a tag neither names: {rest:?}"
        );
        assert_eq!(rest.union(&one), Predicate::True);
        assert_eq!(rest.intersect(&one), Predicate::False);
        assert!(rest.is_applicable_to(&union_ext()));
        // A column naming one tag and a statement over both combine without a tag-set match.
        let column = Predicate::from_column_value(&ColumnValue::positional_union(
            &[0],
            vec![ColumnValue::Ints(vec![1])],
        ));
        let statement = union_pred(int_intervals(&[1, 2]), Predicate::True);
        assert!(statement.subsumes(&column));
        assert!(!column.subsumes(&statement));
        assert_eq!(
            statement.minus(&column),
            union_pred(int_intervals(&[2]), Predicate::True)
        );
    }

    /// A path through a union-typed level is spelled the way that level's own statements
    /// are, so it applies to the level and meets its statements.
    #[test]
    fn a_union_key_path_is_spelled_as_its_levels_statements() {
        let row = Predicate::exactly(&[union_val(0, Value::Int(1))]);
        assert!(row.is_applicable_to(&union_ext()), "{row:?}");
        let stated = union_pred(Predicate::True, Predicate::False);
        assert!(row.minus(&stated).is_false(), "{:?}", row.minus(&stated));
    }

    /// A predicate built over every tag of its domain is `True` when every tag is.
    #[test]
    fn a_union_over_every_tag_all_true_is_true() {
        assert_eq!(
            union_pred(Predicate::True, Predicate::True),
            Predicate::True
        );
        assert_eq!(
            union_pred(Predicate::False, Predicate::False),
            Predicate::False
        );
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
        assert!(matches!(pred, Predicate::Union { ref tags, .. } if tags.len() == 2));
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
        let pred = union_pred(int_intervals(&[0]), Predicate::True);
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
        let pred = union_pred(int_intervals(&[1]), Predicate::True);
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
        let pred = Predicate::tagged(
            TagMap::from_arms(vec![(FieldKey::Name("nope".into()), Predicate::True)]),
            false,
        );
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
