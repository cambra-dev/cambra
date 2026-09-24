//! Release/intent guards: [`TileGuard`] (per-[`Tile`](crate::interpreter::Tile) region
//! descriptor) and [`FunctionGuard`] (its function-shaped arm).

use std::collections::HashMap;

use crate::interpreter::{Extent, Predicate, Tiling, Value};

/// Specifies a sub-region of interest within a [`Tile`](crate::interpreter::Tile), used for
/// demand-driven computation and incremental release.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TileGuard {
    Scalar(bool),
    Record(HashMap<String, TileGuard>),
    Function(FunctionGuard),
    Aggregation(bool),
    /// The union of multiple guards — matches anything admitted by any arm.
    ///
    /// Built where no single variant holds the union. A collection of collections is
    /// covered partly by its own keys and partly by the inner ones, so
    /// [`Tile::to_guard`](crate::interpreter::Tile::to_guard) names both and
    /// [`FunctionGuard::union`] has no `Domain`-with-`Codomain` arm to merge them.
    /// Every other shape represents its own union directly — a record's union is its
    /// fields'.
    ///
    /// Invariant: arms never directly nest another `Or` (always flattened by
    /// [`TileGuard::flatten_or`]).
    Or(Vec<TileGuard>),
}

impl TileGuard {
    /// Whether this guard names `path`, one component per level from the outermost.
    ///
    /// A guard is a region of paths, and this is the region read at one of them — what a
    /// consumer holding its own state by path asks before dropping an entry. Reading the
    /// arms by hand instead gives every such consumer its own partial answer, and each one
    /// then has to be taught every guard shape.
    pub fn covers_path(&self, path: &[Value]) -> bool {
        self.covers_at(path, 0)
    }

    /// [`covers_path`](Self::covers_path) at the level this guard has stepped down to.
    ///
    /// The **whole** path goes down, not the part below the steps taken: a predicate
    /// naming an enclosing path is read against that path ([`Predicate::contains_path`]),
    /// so handing it only its own key reads it as unqualified and answers no.
    fn covers_at(&self, path: &[Value], level: usize) -> bool {
        match self {
            TileGuard::Or(arms) => arms.iter().any(|arm| arm.covers_at(path, level)),
            // A domain guard names whole keys, so the key it names covers every path
            // running through it, however much deeper that path goes.
            TileGuard::Function(FunctionGuard::Domain(pred)) => {
                level < path.len() && pred.contains_path(&path[..=level])
            }
            TileGuard::Function(FunctionGuard::Codomain(inner)) => inner.covers_at(path, level + 1),
            TileGuard::Record(fields) => fields.values().any(|g| g.covers_at(path, level)),
            TileGuard::Scalar(taken) | TileGuard::Aggregation(taken) => *taken,
        }
    }

    /// Whether any predicate in this guard names an enclosing path.
    ///
    /// What [`Tile::remove_guarded`](crate::interpreter::Tile::remove_guarded) asks before
    /// walking a level's key paths: a guard that names none is read against the key alone,
    /// and building the paths for it would allocate on every release.
    pub fn names_a_path(&self) -> bool {
        match self {
            TileGuard::Function(FunctionGuard::Domain(pred)) => pred.qualifies(),
            TileGuard::Function(FunctionGuard::Codomain(inner)) => inner.names_a_path(),
            TileGuard::Record(fields) => fields.values().any(TileGuard::names_a_path),
            TileGuard::Or(arms) => arms.iter().any(TileGuard::names_a_path),
            _ => false,
        }
    }
}

/// Whether two guards name the same place — the same nesting, down to the predicate.
fn same_place(a: &TileGuard, b: &TileGuard) -> bool {
    match (a, b) {
        (
            TileGuard::Function(FunctionGuard::Domain(_)),
            TileGuard::Function(FunctionGuard::Domain(_)),
        ) => true,
        (
            TileGuard::Function(FunctionGuard::Codomain(x)),
            TileGuard::Function(FunctionGuard::Codomain(y)),
        ) => same_place(x, y),
        // A record's fields are cells of their own, so two record guards union field by
        // field ([`TileGuard::union`]) whatever each field names.
        (TileGuard::Record(_), TileGuard::Record(_)) => true,
        _ => false,
    }
}

/// The union of two guards naming the same place, which [`same_place`] has established.
fn union_in_place(a: &TileGuard, b: &TileGuard) -> TileGuard {
    match (a, b) {
        (
            TileGuard::Function(FunctionGuard::Domain(p)),
            TileGuard::Function(FunctionGuard::Domain(q)),
        ) => TileGuard::Function(FunctionGuard::Domain(p.union(q))),
        (
            TileGuard::Function(FunctionGuard::Codomain(x)),
            TileGuard::Function(FunctionGuard::Codomain(y)),
        ) => TileGuard::Function(FunctionGuard::Codomain(Box::new(union_in_place(x, y)))),
        (TileGuard::Record(_), TileGuard::Record(_)) => a.union(b),
        _ => unreachable!("only two guards naming one place are unioned this way"),
    }
}

/// The domain predicate `arm` names, with how many codomain steps in it sits, where `arm`
/// is a chain of codomain steps ending in a domain guard.
fn domain_at(arm: &TileGuard) -> Option<(usize, &Predicate)> {
    match arm {
        TileGuard::Function(FunctionGuard::Domain(pred)) => Some((0, pred)),
        TileGuard::Function(FunctionGuard::Codomain(inner)) => {
            domain_at(inner).map(|(depth, pred)| (depth + 1, pred))
        }
        _ => None,
    }
}

/// `arm`, a chain [`domain_at`] reads, naming `pred` at its end instead.
fn with_domain(arm: &TileGuard, pred: Predicate) -> TileGuard {
    match arm {
        TileGuard::Function(FunctionGuard::Domain(_)) => {
            TileGuard::Function(FunctionGuard::Domain(pred))
        }
        TileGuard::Function(FunctionGuard::Codomain(inner)) => {
            TileGuard::Function(FunctionGuard::Codomain(Box::new(with_domain(inner, pred))))
        }
        other => unreachable!("only a chain ending in a domain guard is rewritten: {other:?}"),
    }
}

/// `arms`, each at most one per place, without what a shallower domain arm names whole
/// ([`Predicate::without_covered`]). An arm left naming nothing is dropped, unless every
/// arm is.
fn without_covered_arms(arms: Vec<TileGuard>) -> Vec<TileGuard> {
    let depths: Vec<(usize, Predicate)> = arms
        .iter()
        .filter_map(|arm| domain_at(arm).map(|(depth, pred)| (depth, pred.clone())))
        .collect();
    let Some(deepest) = depths.iter().map(|(depth, _)| *depth).max() else {
        return arms;
    };
    let mut above = vec![Predicate::False; deepest + 1];
    for (depth, pred) in depths {
        above[depth] = pred;
    }
    let pruned: Vec<TileGuard> = arms
        .into_iter()
        .map(|arm| match domain_at(&arm) {
            Some((depth, pred)) if depth > 0 => match pred.without_covered(&above[..depth]) {
                Some(kept) => with_domain(&arm, kept),
                None => arm,
            },
            _ => arm,
        })
        .collect();
    match pruned.iter().any(|arm| !arm.is_empty()) {
        true => pruned.into_iter().filter(|arm| !arm.is_empty()).collect(),
        false => pruned.into_iter().take(1).collect(),
    }
}

/// Combine two record guards field by field.
///
/// Both guards describe the same `Tiling::Record`, so they name the same fields;
/// a mismatch means two guards for different tilings met, which no producer can
/// act on.
fn zip_fields(
    m1: &HashMap<String, TileGuard>,
    m2: &HashMap<String, TileGuard>,
    combine: impl Fn(&TileGuard, &TileGuard) -> TileGuard,
) -> HashMap<String, TileGuard> {
    assert_eq!(
        m1.len(),
        m2.len(),
        "Incompatible record guards: {m1:?} vs {m2:?}"
    );
    m1.iter()
        .map(|(k, g)| {
            let other = m2.get(k).unwrap_or_else(|| {
                panic!("Incompatible record guards: {m1:?} vs {m2:?}");
            });
            (k.clone(), combine(g, other))
        })
        .collect()
}

impl TileGuard {
    /// Builds a `TileGuard` from a list of arms, flattening any nested `Or`
    /// variants.  Returns the single element directly when `arms` has length
    /// one to avoid gratuitous wrapping.
    pub(crate) fn flatten_or(arms: Vec<TileGuard>) -> TileGuard {
        // Every arm is a chain of codomain steps ending in one guard, so arms naming the same
        // place merge and the covered ones are found. A codomain step over an `Or` is
        // the `Or` of that step over each arm, which is how it becomes chains.
        fn chains(guard: TileGuard) -> Vec<TileGuard> {
            match guard {
                TileGuard::Or(arms) => arms.into_iter().flat_map(chains).collect(),
                TileGuard::Function(FunctionGuard::Codomain(inner)) => chains(*inner)
                    .into_iter()
                    .map(|arm| TileGuard::Function(FunctionGuard::Codomain(Box::new(arm))))
                    .collect(),
                other => vec![other],
            }
        }
        let mut flat: Vec<TileGuard> = arms.into_iter().flat_map(chains).collect();
        if let Some(everything) = flat.iter().find(|arm| arm.is_universal()) {
            return everything.clone();
        }
        // Filter empty guards; if all are empty, keep the first as a canonical empty sentinel.
        if flat.iter().any(|g| !g.is_empty()) {
            flat.retain(|g| !g.is_empty());
        } else {
            flat.truncate(1);
        }
        // Two arms naming the same place are one arm over the union of what they name.
        // Leaving them apart would make a guard's shape depend on how it was assembled,
        // and a consumer that matches on the shape reads that as a different guard.
        let mut merged: Vec<TileGuard> = Vec::with_capacity(flat.len());
        for arm in flat {
            match merged.iter().position(|g| same_place(g, &arm)) {
                Some(i) => {
                    merged[i] = union_in_place(&merged[i], &arm);
                }
                None => merged.push(arm),
            }
        }
        // A region beneath a key a shallower arm names whole is already named. A sequential
        // drive releases the rows before the running one whole and the running one's
        // positions beneath, so without this every row it finishes leaves an arm behind and
        // the guard — and every union into it — grows with the number of rows run.
        let merged = without_covered_arms(merged);
        match merged.len() {
            0 => unreachable!("flatten_or called with no arms"),
            1 => merged.into_iter().next().unwrap(),
            _ => TileGuard::Or(merged),
        }
    }

    pub fn intersect(&self, other: &TileGuard) -> TileGuard {
        self.intersect_at(other, 0)
    }

    /// [`intersect`](Self::intersect) at the level these two guards sit at.
    ///
    /// A predicate names its level by where it sits in the chain, so a meet that has to
    /// write one — a domain guard against a codomain guard — needs to know which level
    /// that is. `covers_at` and `check_from_under` thread it for the same reason.
    fn intersect_at(&self, other: &TileGuard, level: usize) -> TileGuard {
        match (self, other) {
            (TileGuard::Scalar(u1), TileGuard::Scalar(u2)) => TileGuard::Scalar(*u1 && *u2),
            (TileGuard::Aggregation(u1), TileGuard::Aggregation(u2)) => {
                TileGuard::Aggregation(*u1 && *u2)
            }
            (TileGuard::Function(f1), TileGuard::Function(f2)) => {
                TileGuard::Function(f1.intersect_at(f2, level))
            }
            (TileGuard::Record(m1), TileGuard::Record(m2)) => {
                TileGuard::Record(zip_fields(m1, m2, |a, b| a.intersect_at(b, level)))
            }
            // Or distributes over intersect: (A | B) & C = (A & C) | (B & C).
            (TileGuard::Or(arms), g) | (g, TileGuard::Or(arms)) => {
                TileGuard::flatten_or(arms.iter().map(|a| a.intersect_at(g, level)).collect())
            }
            _ => panic!("Intersect on incompatible guards {self:?} and {other:?}"),
        }
    }

    /// Returns the union of two guards — the set of data covered by either guard.
    ///
    /// Used to accumulate release guards across multiple incremental deliveries: a
    /// consumer that has released `[0,1]` and then `[2,3]` has collectively seen
    /// `[0,3]`, so the stored guard must grow via union rather than replacement.
    ///
    /// Note for future implementation: All TileGuards we currently have are compatible with
    /// union, but future stuff like conditional function guards (e.g. constraints like
    /// "positive inputs produce positive outputs") are *not* closed under union and need to
    /// throw an error.
    pub fn union(&self, other: &TileGuard) -> TileGuard {
        match (self, other) {
            (TileGuard::Scalar(u1), TileGuard::Scalar(u2)) => TileGuard::Scalar(*u1 || *u2),
            (TileGuard::Aggregation(u1), TileGuard::Aggregation(u2)) => {
                TileGuard::Aggregation(*u1 || *u2)
            }
            // Two function guards whose shapes have no common arm stay side by side: an
            // `Or` names the union exactly, where an arm invented to hold the pair would
            // have to over- or under-approximate it.
            (TileGuard::Function(f1), TileGuard::Function(f2)) => match f1.union(f2) {
                Some(merged) => TileGuard::Function(merged),
                None => TileGuard::flatten_or(vec![self.clone(), other.clone()]),
            },
            // A record guard covers the cells of each field its map names, so two of
            // them union field by field, as `intersect` above combines them.
            //
            // [`Predicate::Record`](crate::interpreter::Predicate::Record) reads
            // alike and does not union alike: it admits a record *value* only when
            // every field admits its component, so it is a product and two products
            // do not union to one. That is why `Predicate` keeps an `Or` arm for this
            // and a guard does not need one. Reaching for `TileGuard::Or` here leaves
            // a guard no record-tiled producer can act on: a consumer releasing one
            // field twice hands `MakeRecord` two arms naming that field, and the
            // operand that owns it hears about neither.
            (TileGuard::Record(m1), TileGuard::Record(m2)) => {
                TileGuard::Record(zip_fields(m1, m2, TileGuard::union))
            }
            // Or: accumulate all arms, flattening nested Ors.
            (TileGuard::Or(arms), g) | (g, TileGuard::Or(arms)) => {
                let mut new_arms = arms.clone();
                new_arms.push(g.clone());
                TileGuard::flatten_or(new_arms)
            }
            _ => panic!("Union on incompatible guards {self:?} and {other:?}"),
        }
    }

    pub fn is_universal(&self) -> bool {
        match self {
            TileGuard::Scalar(universal) | TileGuard::Aggregation(universal) => *universal,
            TileGuard::Record(m) => m.values().all(TileGuard::is_universal),
            TileGuard::Function(g) => g.is_universal(),
            // Or is universal if any arm covers everything.
            TileGuard::Or(arms) => arms.iter().any(TileGuard::is_universal),
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            TileGuard::Scalar(universal) | TileGuard::Aggregation(universal) => !*universal,
            // Record: empty only when every field guard is empty — i.e., there
            // is nothing to release from any field.  (Fields are managed
            // independently, so a guard with one empty field is still meaningful
            // for the non-empty fields.)
            TileGuard::Record(m) => m.values().all(TileGuard::is_empty),
            TileGuard::Function(g) => g.is_empty(),
            // Or is empty only when every arm is empty.
            TileGuard::Or(arms) => arms.iter().all(TileGuard::is_empty),
        }
    }

    /// Returns whether this guard is universal, panicking unless it is universal
    /// or empty — for producers that can only reclaim all or nothing. Quietly
    /// dropping a partial guard would leave them free to re-emit the released
    /// region, since a producer records the guard either way. `context` names the
    /// producer in the panic message.
    pub fn expect_universal_or_empty(&self, context: &str) -> bool {
        if self.is_empty() {
            false
        } else if self.is_universal() {
            true
        } else {
            panic!("{context} cannot honor the partial release guard {self:?}")
        }
    }

    /// Check whether this guard is structurally compatible with `tiling`.
    ///
    /// A guard is compatible when its variant matches the shape of the tiling
    /// it was derived from — e.g., a [`TileGuard::Scalar`] guard belongs to a
    /// [`Tiling::Scalar`] tiling.  Used to assert that a guard passed to
    /// [`crate::interpreter::tile_operators::TileProducer::release`] is well-formed.
    pub fn check_from(&self, tiling: &Tiling) -> bool {
        self.check_from_under(tiling, &[])
    }

    /// [`check_from`](Self::check_from), carrying the extents of the levels this guard
    /// already stepped through.
    ///
    /// A predicate naming an enclosing path is checked against that path's extents
    /// ([`Predicate::is_applicable_over`]), so a `Codomain` step has to hand the level it
    /// came from down with it. Checking a qualified predicate against its own level alone
    /// reads it as unqualified and refuses it.
    fn check_from_under(&self, tiling: &Tiling, above: &[Extent]) -> bool {
        match (self, tiling) {
            (TileGuard::Scalar(_), Tiling::Scalar(_)) => true,
            (TileGuard::Aggregation(_), Tiling::Aggregation { .. }) => true,

            // DataFunction tilings can have domain guards which are always allowed, or
            // codomain guards which match their codomain tiling. A Store shares the
            // function shape: consumers release a prefix of its position domain
            // (a `Domain` guard) — that is its only release form (a store's
            // `to_guard` is `Function(Domain(_))`), so no `Codomain` arm.
            //
            // Its positions are a level like any other, so the levels it was reached
            // through go down with it: a carrier holds one store per row, and a release
            // naming the positions of *one* of them qualifies its predicate by that row.
            // Checked against the store's own domain alone, such a predicate reads as
            // unqualified and is refused.
            (TileGuard::Function(FunctionGuard::Domain(pred)), Tiling::Store { domain, .. }) => {
                let mut levels = above.to_vec();
                levels.push(domain.clone());
                pred.is_applicable_over(&levels)
            }

            // A collection supports a `Domain` guard naming its own keys and a `Codomain`
            // guard naming what sits under them. The guard nests exactly as the tiling does,
            // so stepping in is one recursion with nothing to translate.
            (
                TileGuard::Function(FunctionGuard::Domain(pred)),
                Tiling::DataFunction { domain, .. },
            ) => {
                let mut levels = above.to_vec();
                levels.push(domain.clone());
                pred.is_applicable_over(&levels)
            }
            (
                TileGuard::Function(FunctionGuard::Codomain(g)),
                Tiling::DataFunction { domain, codomain },
            ) => {
                let mut levels = above.to_vec();
                levels.push(domain.clone());
                g.check_from_under(codomain, &levels)
            }

            // Record guards must have the same key set, with each field guard
            // compatible with the corresponding field tiling.
            (TileGuard::Record(guard_fields), Tiling::Record(tiling_fields)) => {
                guard_fields.len() == tiling_fields.len()
                    && guard_fields.iter().all(|(k, g)| {
                        tiling_fields
                            .get(k)
                            .is_some_and(|t| g.check_from_under(t, above))
                    })
            }
            // All arms of an Or must be compatible with the same tiling.
            (TileGuard::Or(arms), _) => arms.iter().all(|g| g.check_from_under(tiling, above)),
            _ => false,
        }
    }
}

/// A guard on a [`Tile::DataFunction`](crate::interpreter::Tile::DataFunction), naming which
/// part of it is of interest: its own keys, or what those keys hold.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionGuard {
    Domain(Predicate),
    Codomain(Box<TileGuard>),
}

/// The guard naming everything at or below `path` in the nesting order: the keys before
/// its head entirely, and within that head key, everything up to the tail.
///
/// A **spelling**, not a shape. One arm per level, each naming that level's keys under the
/// path that reaches it: a domain guard names whole keys, a codomain guard steps one level
/// in, and [`Predicate::exactly`] pins the levels above so the arm speaks about one row
/// rather than about every row a codomain read would name. Giving the prefix an arm of its
/// own would owe the algebra a rule against every other shape.
///
/// The path is **non-empty**. A path with no components has two readings that disagree —
/// nothing, since it names no key, or everything, since a path's end reads as "and all of
/// this key" — so it is rejected rather than given one of them.
pub fn domain_prefix(path: Vec<Value>) -> TileGuard {
    assert!(
        !path.is_empty(),
        "a path prefix names at least one key; an empty path is neither the empty guard \
         nor the universal one"
    );
    let last = path.len() - 1;
    let arms = path
        .iter()
        .enumerate()
        .map(|(level, key)| {
            // Every level but the last is bounded below its key, that key's own row being
            // only partly done; the last takes its key whole.
            let bound = match level == last {
                true => Predicate::at_or_below(key.clone()),
                false => Predicate::below(key.clone()),
            };
            let at = Predicate::qualified(Predicate::exactly(&path[..level]), bound);
            (0..level).fold(
                TileGuard::Function(FunctionGuard::Domain(at)),
                |inner, _| TileGuard::Function(FunctionGuard::Codomain(Box::new(inner))),
            )
        })
        .collect();
    TileGuard::flatten_or(arms)
}

/// `guard`, sitting at `level`, with `p` additionally required of the key at level `at`.
fn require_at(guard: TileGuard, p: &Predicate, at: usize, level: usize) -> TileGuard {
    match guard {
        TileGuard::Function(FunctionGuard::Domain(pred)) => {
            TileGuard::Function(FunctionGuard::Domain(require_level(&pred, p, at, level)))
        }
        TileGuard::Function(FunctionGuard::Codomain(inner)) => TileGuard::Function(
            FunctionGuard::Codomain(Box::new(require_at(*inner, p, at, level + 1))),
        ),
        TileGuard::Or(arms) => TileGuard::flatten_or(
            arms.into_iter()
                .map(|arm| require_at(arm, p, at, level))
                .collect(),
        ),
        // A record stands over the same rows, so a collection in one of its fields is a
        // level at the record's own depth.
        TileGuard::Record(fields) => TileGuard::Record(
            fields
                .into_iter()
                .map(|(name, field)| (name, require_at(field, p, at, level)))
                .collect(),
        ),
        // A whole value under every key cannot be narrowed to the keys `p` admits: a scalar
        // guard names no keys. Naming none of it releases less than the meet, which the
        // consumer answers by delivering again rather than by losing data.
        TileGuard::Scalar(_) => TileGuard::Scalar(false),
        TileGuard::Aggregation(_) => TileGuard::Aggregation(false),
    }
}

/// `pred`, which describes the keys of level `own`, with `p` also required of level `at`.
///
/// A qualification chain runs outermost-first, so the level a component speaks about is
/// its depth in the chain: the requirement is conjoined where the chain reaches `at`,
/// rather than around the whole predicate, which would read `p` against the wrong level.
fn require_level(pred: &Predicate, p: &Predicate, at: usize, own: usize) -> Predicate {
    if let Predicate::Or(arms) = pred {
        return Predicate::flatten_or(
            arms.iter()
                .map(|arm| require_level(arm, p, at, own))
                .collect(),
        );
    }
    let (enclosing, here) = pred.split_qualification();
    // `enclosing` describes the path up to `own - 1`, whose last component is that level.
    match own == at + 1 {
        true => Predicate::qualified(enclosing.intersect(p), here.clone()),
        false => Predicate::qualified(require_level(enclosing, p, at, own - 1), here.clone()),
    }
}

impl FunctionGuard {
    pub fn intersect(&self, other: &FunctionGuard) -> FunctionGuard {
        self.intersect_at(other, 0)
    }

    /// [`intersect`](Self::intersect) at the level these guards sit at.
    fn intersect_at(&self, other: &FunctionGuard, level: usize) -> FunctionGuard {
        match (self, other) {
            (a, _b) | (_b, a) if a.is_empty() => a.clone(),
            (a, b) | (b, a) if a.is_universal() => b.clone(),
            (FunctionGuard::Domain(p1), FunctionGuard::Domain(p2)) => {
                FunctionGuard::Domain(p1.intersect(p2))
            }
            (FunctionGuard::Codomain(p1), FunctionGuard::Codomain(p2)) => {
                FunctionGuard::Codomain(Box::new(p1.intersect_at(p2, level + 1)))
            }
            // A domain guard names whole keys of this level and a codomain guard a region
            // one level in, so their meet is that region with those keys additionally
            // required of it. The requirement goes into the codomain's predicates at this
            // level's place in their qualification chain — which is what a predicate about
            // an enclosing path already is, so there is no shape to invent.
            (FunctionGuard::Domain(p), FunctionGuard::Codomain(g))
            | (FunctionGuard::Codomain(g), FunctionGuard::Domain(p)) => {
                FunctionGuard::Codomain(Box::new(require_at((**g).clone(), p, level, level + 1)))
            }
        }
    }

    /// The union of two function guards, or `None` where no single arm holds it.
    ///
    /// The two arms name two shapes of region — whole keys of this level, and a region one
    /// level in — and a union across them is neither. Declining is what [`TileGuard::Or`]
    /// exists for, rather than an arm invented to hold the pair.
    pub fn union(&self, other: &FunctionGuard) -> Option<FunctionGuard> {
        Some(match (self, other) {
            (a, b) | (b, a) if a.is_empty() => b.clone(),
            (a, _b) | (_b, a) if a.is_universal() => a.clone(),
            (FunctionGuard::Domain(p1), FunctionGuard::Domain(p2)) => {
                FunctionGuard::Domain(p1.union(p2))
            }
            (FunctionGuard::Codomain(p1), FunctionGuard::Codomain(p2)) => {
                FunctionGuard::Codomain(Box::new(p1.union(p2)))
            }
            // A domain guard and a codomain guard name two different places, so no
            // single arm holds their union — `TileGuard::Or` does, and declining is how
            // the caller is told to build one.
            _ => return None,
        })
    }

    pub fn is_universal(&self) -> bool {
        match self {
            FunctionGuard::Domain(p) => p.as_bool() == Some(true),
            FunctionGuard::Codomain(g) => g.is_universal(),
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            FunctionGuard::Domain(p) => p.as_bool() == Some(false),
            FunctionGuard::Codomain(g) => g.is_empty(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::AggregateKind;
    use crate::interpreter::tiling::tests::*;

    // ── TileGuard::union: absorbing what a shallower arm names whole ─────────

    fn at(row: usize, positions: Predicate) -> Predicate {
        Predicate::qualified(Predicate::point(Value::UInt(row)), positions)
    }

    fn domain(pred: Predicate) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(pred))
    }

    fn codomain(inner: TileGuard) -> TileGuard {
        TileGuard::Function(FunctionGuard::Codomain(Box::new(inner)))
    }

    /// What a sequential drive releases: the rows before the running one whole, and the
    /// running one's positions. Once row 0 is named whole, its positions add nothing, and a
    /// row not yet named whole keeps its own.
    #[test]
    fn union_drops_a_region_beneath_a_key_named_whole() {
        let rows_done = domain(Predicate::at_or_below(Value::UInt(1)));
        let positions = codomain(domain(Predicate::flatten_or(vec![
            at(0, Predicate::at_or_below(Value::UInt(1))),
            at(2, Predicate::at_or_below(Value::UInt(0))),
        ])));
        let expected = TileGuard::Or(vec![
            domain(Predicate::at_or_below(Value::UInt(1))),
            codomain(domain(at(2, Predicate::at_or_below(Value::UInt(0))))),
        ]);
        assert_eq!(rows_done.union(&positions), expected);
        // An `Or` keeps its arms in the order they arrived, so the other order is the same
        // two arms reversed.
        let TileGuard::Or(arms) = expected else {
            unreachable!()
        };
        assert_eq!(
            positions.union(&rows_done),
            TileGuard::Or(arms.into_iter().rev().collect())
        );
    }

    /// The region beneath a covered key goes however deep it sits: a key named whole at
    /// the outermost level covers the paths two levels in that run through it.
    #[test]
    fn union_drops_a_covered_region_two_levels_in() {
        let path = |outer: usize, middle: usize| {
            Predicate::qualified(
                Predicate::qualified(
                    Predicate::point(Value::UInt(outer)),
                    Predicate::point(Value::UInt(middle)),
                ),
                Predicate::at_or_below(Value::UInt(1)),
            )
        };
        let rows_done = domain(Predicate::at_or_below(Value::UInt(0)));
        let deep = codomain(codomain(domain(Predicate::flatten_or(vec![
            path(0, 1),
            path(1, 0),
        ]))));
        assert_eq!(
            rows_done.union(&deep),
            TileGuard::Or(vec![
                domain(Predicate::at_or_below(Value::UInt(0))),
                codomain(codomain(domain(path(1, 0)))),
            ])
        );
    }

    /// Nothing named whole, nothing dropped.
    #[test]
    fn union_keeps_regions_no_key_covers() {
        let positions = codomain(domain(at(0, Predicate::at_or_below(Value::UInt(1)))));
        let other = codomain(domain(at(1, Predicate::at_or_below(Value::UInt(0)))));
        let union = positions.union(&other);
        assert!(union.covers_path(&[Value::UInt(0), Value::UInt(1)]));
        assert!(union.covers_path(&[Value::UInt(1), Value::UInt(0)]));
    }

    // ── TileGuard::intersect ──────────────────────────────────────────────────

    #[test]
    fn guard_intersect_scalar_universal_universal() {
        let g = TileGuard::Scalar(true).intersect(&TileGuard::Scalar(true));
        assert!(g.is_universal());
    }

    #[test]
    fn guard_intersect_scalar_universal_empty() {
        let g = TileGuard::Scalar(true).intersect(&TileGuard::Scalar(false));
        assert!(g.is_empty());
    }

    #[test]
    fn guard_intersect_aggregation() {
        let g = TileGuard::Aggregation(true).intersect(&TileGuard::Aggregation(true));
        assert!(g.is_universal());
    }

    #[test]
    fn guard_intersect_one_level_universal_universal() {
        let g = TileGuard::Function(FunctionGuard::Domain(Predicate::True))
            .intersect(&TileGuard::Function(FunctionGuard::Domain(Predicate::True)));
        assert!(g.is_universal());
    }

    #[test]
    fn guard_intersect_one_level_empty_dominates() {
        let g = TileGuard::Function(FunctionGuard::Domain(Predicate::True)).intersect(
            &TileGuard::Function(FunctionGuard::Domain(Predicate::False)),
        );
        assert!(g.is_empty());
    }

    // ── A domain guard meeting a codomain guard ───────────────────────────────
    //
    // The two name regions of different shapes: whole keys of one level, and a region one
    // level in read against every row of it. Their meet is that region with those keys
    // additionally required of it, which is a **qualified** predicate, the arm that makes
    // this expressible.

    /// The meet keeps the codomain's region and qualifies it by the domain's keys, so it
    /// admits a path exactly where both halves do. Read against the key alone it would be
    /// the codomain's region unchanged, which is the over-claim the qualification prevents.
    #[test]
    fn guard_intersect_domain_with_codomain_qualifies_the_inner_region() {
        let rows = upto(0);
        let inner = inner_upto(1);
        let met = rows.intersect(&inner);

        // Under row 0 the inner bound stands.
        assert!(met.covers_path(&[Value::UInt(0), Value::UInt(0)]));
        assert!(met.covers_path(&[Value::UInt(0), Value::UInt(1)]));
        // The inner bound alone would admit these; the domain half does not.
        assert!(!met.covers_path(&[Value::UInt(1), Value::UInt(0)]));
        // Neither half admits this one.
        assert!(!met.covers_path(&[Value::UInt(1), Value::UInt(2)]));
        // Nor does the inner half, under any row.
        assert!(!met.covers_path(&[Value::UInt(0), Value::UInt(2)]));
    }

    /// The meet is symmetric, however the two are written.
    #[test]
    fn guard_intersect_domain_with_codomain_is_symmetric() {
        let rows = upto(0);
        let inner = inner_upto(1);
        for path in [
            [Value::UInt(0), Value::UInt(1)],
            [Value::UInt(1), Value::UInt(1)],
            [Value::UInt(0), Value::UInt(2)],
        ] {
            assert_eq!(
                rows.intersect(&inner).covers_path(&path),
                inner.intersect(&rows).covers_path(&path),
                "the meet is symmetric at {path:?}"
            );
        }
    }

    /// An empty half empties the meet, and a universal one leaves the other standing —
    /// the two arms that run before the shapes are compared at all.
    #[test]
    fn guard_intersect_domain_with_codomain_respects_the_trivial_guards() {
        let inner = inner_upto(1);
        assert!(
            domain_guard(Predicate::False).intersect(&inner).is_empty(),
            "an empty domain guard empties the meet"
        );
        assert_eq!(
            domain_guard(Predicate::True).intersect(&inner),
            inner,
            "a universal domain guard leaves the codomain's region standing"
        );
    }

    /// A meet **beneath a standing level** qualifies at that level's place in the chain
    /// rather than at the top. The guards sit one level in, so the keys the domain half
    /// names are the second component of a path and not the first.
    #[test]
    fn guard_intersect_domain_with_codomain_under_a_standing_level() {
        let rows = codomain_guard(upto(0));
        let inner = codomain_guard(inner_upto(1));
        let met = rows.intersect(&inner);

        // Standing row 9 is named by neither half, so it constrains nothing: what the meet
        // says is about the two levels beneath it.
        assert!(met.covers_path(&[Value::UInt(9), Value::UInt(0), Value::UInt(1)]));
        assert!(!met.covers_path(&[Value::UInt(9), Value::UInt(1), Value::UInt(1)]));
        assert!(!met.covers_path(&[Value::UInt(9), Value::UInt(0), Value::UInt(2)]));
    }

    /// A meet is well formed against the tiling it was built for — the check a release
    /// makes before it is honoured, and the one a qualified predicate read against a
    /// single level would fail.
    #[test]
    fn guard_intersect_domain_with_codomain_checks_from_its_tiling() {
        let met = upto(0).intersect(&inner_upto(1));
        let tiling = Tiling::data_function(
            Extent::Base(crate::ccl::BaseType::UInt),
            Tiling::data_function(
                Extent::Base(crate::ccl::BaseType::UInt),
                Tiling::Scalar(Extent::Base(crate::ccl::BaseType::Int)),
            ),
        );
        assert!(met.check_from(&tiling), "{met:?} against {tiling}");
    }

    // ── TileGuard::union (Record / Or) ────────────────────────────────────────

    /// Helper: build a Record TileGuard from a slice of (field, guard) pairs.
    fn record_guard(fields: &[(&str, TileGuard)]) -> TileGuard {
        TileGuard::Record(
            fields
                .iter()
                .map(|(k, g)| (k.to_string(), g.clone()))
                .collect(),
        )
    }

    /// A domain guard over the positions up to and including `bound`.
    fn upto(bound: usize) -> TileGuard {
        domain_guard(Predicate::at_or_below(Value::UInt(bound)))
    }

    /// `upto` one level in, so an `Or` of the two has an arm per level.
    fn inner_upto(bound: usize) -> TileGuard {
        codomain_guard(upto(bound))
    }

    /// Two record guards union field by field, to a record guard.
    #[test]
    fn guard_union_record_is_field_wise() {
        let g1 = record_guard(&[
            ("a", TileGuard::Scalar(true)),
            ("b", TileGuard::Scalar(false)),
        ]);
        let g2 = record_guard(&[
            ("a", TileGuard::Scalar(false)),
            ("b", TileGuard::Scalar(true)),
        ]);
        assert_eq!(
            g1.union(&g2),
            record_guard(&[
                ("a", TileGuard::Scalar(true)),
                ("b", TileGuard::Scalar(true)),
            ]),
        );
    }

    /// A field unions as that field's own shape does. A collection field released
    /// in pieces therefore accumulates the positions it has handed over, which is
    /// what a consumer reading one field of a growing product does every pull.
    #[test]
    fn guard_union_record_accumulates_a_function_field() {
        let first = record_guard(&[("n", TileGuard::Scalar(false)), ("xs", upto(0))]);
        let second = record_guard(&[("n", TileGuard::Scalar(false)), ("xs", upto(2))]);
        assert_eq!(
            first.union(&second),
            record_guard(&[("n", TileGuard::Scalar(false)), ("xs", upto(2))]),
        );
    }

    #[test]
    fn guard_union_record_identical_is_that_record() {
        let g = record_guard(&[
            ("x", TileGuard::Scalar(true)),
            ("y", TileGuard::Scalar(true)),
        ]);
        assert_eq!(g.union(&g), g);
    }

    #[test]
    fn guard_union_record_is_universal_when_every_field_is() {
        let universal = record_guard(&[
            ("a", TileGuard::Scalar(true)),
            ("b", TileGuard::Scalar(true)),
        ]);
        let empty = record_guard(&[
            ("a", TileGuard::Scalar(false)),
            ("b", TileGuard::Scalar(false)),
        ]);
        assert!(empty.union(&universal).is_universal());
    }

    #[test]
    fn guard_union_record_is_empty_when_every_field_is() {
        let empty = record_guard(&[
            ("a", TileGuard::Scalar(false)),
            ("b", TileGuard::Scalar(false)),
        ]);
        assert!(empty.union(&empty).is_empty());
    }

    // ── TileGuard::Or ─────────────────────────────────────────────────────────
    //
    // Arms are built here rather than taken from a producer: what is under test is
    // the algebra, and the one production shape that needs it (`Tile::to_guard` on a
    // nested collection) mixes a `Domain` arm with a `Codomain` one, whose intersect is
    // unimplemented.

    /// Arms stay flat: a union against an existing `Or` appends rather than nests.
    #[test]
    fn guard_or_accumulates_arms() {
        let or = TileGuard::Or(vec![upto(0), inner_upto(1)]);
        let result = or.union(&codomain_guard(inner_upto(2)));
        let TileGuard::Or(arms) = &result else {
            panic!("expected Or, got {result:?}");
        };
        assert_eq!(arms.len(), 3, "should be flat, not nested");
    }

    /// Arms naming one level are one arm: the `Or` carries a predicate per level, so two
    /// at the same level are that level's union. Without this a guard's shape would depend
    /// on how it was assembled, and a consumer that matches on the shape would read two
    /// spellings of one region as different guards.
    #[test]
    fn guard_or_merges_arms_at_one_level() {
        let result = TileGuard::Or(vec![upto(0), upto(1)]).union(&upto(2));
        assert_eq!(result, upto(2));
    }

    /// `Or` distributes through `intersect`: `(A | B) & C = (A & C) | (B & C)`, which for
    /// arms at one level is that level's union — here `upto(1) | upto(3)`.
    #[test]
    fn guard_or_intersect_distributes() {
        let or = TileGuard::Or(vec![upto(1), upto(5)]);
        assert_eq!(or.intersect(&upto(3)), upto(3));
    }

    /// An `Or` is universal when any arm is, and empty only when every arm is.
    #[test]
    fn guard_or_is_universal_when_any_arm_is() {
        let with_universal = TileGuard::Or(vec![
            upto(1),
            TileGuard::Function(FunctionGuard::Domain(Predicate::True)),
        ]);
        assert!(with_universal.is_universal());
        assert!(!TileGuard::Or(vec![upto(1), upto(2)]).is_universal());
    }

    // ── FunctionGuard::intersect ───────────────────────────────────

    #[test]
    fn function_guard_intersect_empty_dominates() {
        let result = FunctionGuard::Domain(Predicate::True)
            .intersect(&FunctionGuard::Domain(Predicate::False));
        assert!(matches!(result, FunctionGuard::Domain(Predicate::False)));
    }

    #[test]
    fn function_guard_intersect_universal_is_identity() {
        let result = FunctionGuard::Domain(Predicate::True)
            .intersect(&FunctionGuard::Domain(Predicate::True));
        assert!(matches!(result, FunctionGuard::Domain(Predicate::True)));
    }

    #[test]
    fn function_guard_intersect_domain_domain() {
        let result = FunctionGuard::Domain(Predicate::True)
            .intersect(&FunctionGuard::Domain(Predicate::False));
        assert!(matches!(result, FunctionGuard::Domain(Predicate::False)));
    }

    #[test]
    fn function_guard_intersect_codomain_codomain() {
        let result = FunctionGuard::Codomain(Box::new(TileGuard::Scalar(true)))
            .intersect(&FunctionGuard::Codomain(Box::new(TileGuard::Scalar(false))));
        assert_eq!(
            result,
            FunctionGuard::Codomain(Box::new(TileGuard::Scalar(false)))
        );
    }

    // ── TileGuard::check_from ─────────────────────────────────────────────────

    fn domain_guard(p: Predicate) -> TileGuard {
        TileGuard::Function(FunctionGuard::Domain(p))
    }

    fn codomain_guard(inner: TileGuard) -> TileGuard {
        TileGuard::Function(FunctionGuard::Codomain(Box::new(inner)))
    }

    fn agg_tiling() -> Tiling {
        Tiling::Aggregation {
            kind: AggregateKind::Sum,
            accumulator: Box::new(Tiling::Scalar(int())),
        }
    }

    #[test]
    fn check_from_scalar_matches_scalar_tiling() {
        assert!(TileGuard::Scalar(true).check_from(&Tiling::Scalar(int())));
        assert!(TileGuard::Scalar(false).check_from(&Tiling::Scalar(int())));
    }

    #[test]
    fn check_from_scalar_rejects_non_scalar_tiling() {
        assert!(!TileGuard::Scalar(true).check_from(&scalar_function(int(), bool_ext())));
        assert!(!TileGuard::Scalar(true).check_from(&agg_tiling()));
    }

    #[test]
    fn check_from_aggregation_matches_aggregation_tiling() {
        assert!(TileGuard::Aggregation(true).check_from(&agg_tiling()));
        assert!(TileGuard::Aggregation(false).check_from(&agg_tiling()));
    }

    #[test]
    fn check_from_aggregation_rejects_non_aggregation_tiling() {
        assert!(!TileGuard::Aggregation(true).check_from(&Tiling::Scalar(int())));
        assert!(!TileGuard::Aggregation(true).check_from(&scalar_function(int(), bool_ext())));
    }

    #[test]
    fn check_from_function_domain_matches_a_one_level_tiling() {
        assert!(domain_guard(Predicate::True).check_from(&scalar_function(int(), bool_ext())));
        assert!(domain_guard(Predicate::False).check_from(&scalar_function(int(), bool_ext())));
    }

    #[test]
    fn check_from_function_codomain_matches_a_one_level_tiling() {
        // A Codomain(Domain(_)) guard is valid against a Function whose
        // codomain is itself a function tiling.
        let nested = scalar_function(int(), bool_ext());
        let outer = Tiling::data_function(int(), nested);
        let g = codomain_guard(domain_guard(Predicate::True));
        assert!(g.check_from(&outer));
    }

    #[test]
    fn check_from_function_codomain_scalar_against_a_one_level_tiling() {
        // Codomain(Scalar) is valid when the function's codomain is a scalar.
        let g = codomain_guard(TileGuard::Scalar(true));
        assert!(g.check_from(&scalar_function(int(), bool_ext())));
    }

    #[test]
    fn check_from_function_codomain_wrong_shape_against_a_one_level_tiling() {
        // Codomain(Aggregation) against a function with scalar codomain must fail.
        let g = codomain_guard(TileGuard::Aggregation(true));
        assert!(!g.check_from(&scalar_function(int(), bool_ext())));
    }

    #[test]
    fn check_from_function_domain_matches_a_two_level_tiling() {
        assert!(domain_guard(Predicate::True).check_from(&two_level(range(4), int(), int())));
    }

    #[test]
    fn check_from_function_codomain_domain_matches_a_two_level_tiling() {
        // Codomain(Domain(_)) is the canonical way to address the inner domain of
        // a Function.
        let g = codomain_guard(domain_guard(Predicate::True));
        assert!(g.check_from(&two_level(range(4), int(), int())));
    }

    #[test]
    fn check_from_function_codomain_scalar_rejects_a_two_level_tiling() {
        // Codomain(Scalar) is not a valid guard shape for a Function.
        let g = codomain_guard(TileGuard::Scalar(true));
        assert!(!g.check_from(&two_level(range(4), int(), int())));
    }

    #[test]
    fn check_from_function_guard_rejects_scalar_tiling() {
        assert!(!domain_guard(Predicate::True).check_from(&Tiling::Scalar(int())));
        assert!(!codomain_guard(domain_guard(Predicate::True)).check_from(&Tiling::Scalar(int())));
    }

    #[test]
    fn check_from_record_matches_record_tiling_with_same_keys() {
        let tiling = record_tiling(&[("x", Tiling::Scalar(int())), ("y", agg_tiling())]);
        let guard = TileGuard::Record(
            [
                ("x".to_string(), TileGuard::Scalar(true)),
                ("y".to_string(), TileGuard::Aggregation(false)),
            ]
            .into(),
        );
        assert!(guard.check_from(&tiling));
    }

    #[test]
    fn check_from_record_rejects_missing_key() {
        let tiling = record_tiling(&[("x", Tiling::Scalar(int())), ("y", Tiling::Scalar(int()))]);
        // Guard only has "x", not "y".
        let guard = TileGuard::Record([("x".to_string(), TileGuard::Scalar(true))].into());
        assert!(!guard.check_from(&tiling));
    }

    #[test]
    fn check_from_record_rejects_wrong_field_shape() {
        let tiling = record_tiling(&[("x", Tiling::Scalar(int()))]);
        // "x" field guard is Aggregation but tiling says Scalar.
        let guard = TileGuard::Record([("x".to_string(), TileGuard::Aggregation(true))].into());
        assert!(!guard.check_from(&tiling));
    }

    #[test]
    fn check_from_record_rejects_extra_key() {
        let tiling = record_tiling(&[("x", Tiling::Scalar(int()))]);
        let guard = TileGuard::Record(
            [
                ("x".to_string(), TileGuard::Scalar(true)),
                ("y".to_string(), TileGuard::Scalar(true)),
            ]
            .into(),
        );
        assert!(!guard.check_from(&tiling));
    }

    #[test]
    fn check_from_or_all_arms_compatible() {
        let tiling = Tiling::Scalar(int());
        let guard = TileGuard::Or(vec![TileGuard::Scalar(true), TileGuard::Scalar(false)]);
        assert!(guard.check_from(&tiling));
    }

    #[test]
    fn check_from_or_rejects_when_any_arm_incompatible() {
        let tiling = Tiling::Scalar(int());
        // Second arm is an Aggregation guard, which does not match a Scalar tiling.
        let guard = TileGuard::Or(vec![TileGuard::Scalar(true), TileGuard::Aggregation(true)]);
        assert!(!guard.check_from(&tiling));
    }
}
