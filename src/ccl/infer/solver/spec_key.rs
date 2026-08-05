//! The **specialization key**: a canonical, polarity-complete fingerprint of a
//! monomorphization use's instantiation type.
//!
//! # Why this is not a `Type`
//!
//! A resolved [`Type`] answers "what should be stamped on this node". That answer
//! is *deliberately* lossy: a domain is a negative position, so it resolves from
//! upper bounds — from what the definition body demands — and a position the body
//! never touches is narrowed away entirely, while a refinement sitting on the
//! argument's *lower* bounds is invisible unless
//! [`compact_type`](super::compact_type)'s opposite-polarity fallback happens to
//! fire at that exact position.
//!
//! A specialization key answers a different question: "would two uses' clones be
//! the same code?" That answer must be **complete**, because it decides whether
//! one use is served by a clone whose interior was resolved against a *different*
//! use's argument. The clone's interior reads its parameter at a *positive*
//! position, so it sees exactly the lower-bound refinements a polarity-correct
//! rendering of the domain drops. Keying on a rendering therefore compares one
//! polarity's view against a clone built from the other's.
//!
//! # Both directed views, not an undirected closure
//!
//! The temptation is to "saturate": follow *both* bound lists at every variable.
//! That is wrong, and instructively so — the bound graph is connected across
//! unrelated uses (two calls' arguments meet at the shared variable of an
//! operator's scheme), so an undirected closure walks out of one use and into
//! every other. Every use of a definition then keys on the union of the whole
//! program's literals, and they all compare equal: the exact defect this key
//! exists to remove, arrived at from the other side.
//!
//! Polarity has to direct the *traversal*. What the key needs is **both directed
//! reads** of the use's instantiation type — the root taken once at each polarity:
//!
//! - The [`positive`](SpecKey::positive) read is the stamping view: a domain is
//!   negative, so it follows upper bounds — what the definition body demands —
//!   while the codomain follows lower bounds, what the definition supplies.
//! - The [`negative`](SpecKey::negative) read is the **clone's** view: the domain
//!   flips to positive and follows *lower* bounds — the argument that flowed in —
//!   while the codomain follows upper bounds, the consumer's demand on the result.
//!
//! The negative read is the load-bearing half, because it is the polarity the
//! clone's interior reads its parameter at. And the pair covers the channels
//! through which a use's own information enters: the emit-time `arg <: domain`
//! edge (a *lower* bound of a negative position) and a consumer's
//! `codomain <: demand` edge (an *upper* bound of a positive position). Both
//! reads stay directed, so neither leaves the use's own cone.
//!
//! **What "covers" does and does not mean.** The two reads flip in lockstep, so
//! at the *root's* immediate positions they are exact opposites and every bound
//! list is consulted by one of them. Deeper in, they diverge: a variable `?e`
//! reached only through `?d`'s lower bounds is visited only by the negative read,
//! at whatever polarity the traversal arrived with — so `?e`'s other bound list is
//! read by neither. That is not a hole, because it is precisely the direction the
//! *clone* reads that position at too: the clone's own resolution walks the same
//! edges from the same side, so a bound the key cannot see is one the clone cannot
//! see either, and the two stay in agreement. The guarantee is agreement with the
//! pin, not omniscience about the graph.
//!
//! **The two are kept apart, not merged.** Merging them into one view per position
//! loses which *direction* a contribution arrived from, and the pin the key is
//! standing in for is direction-sensitive: a use whose domain must accept a plain
//! `Int` cannot be served by a specialization whose parameter is refined, even
//! though the union of both reads is `{Int | …}` on both sides. (This is not
//! hypothetical — it is what a merged key got wrong for a definition used both
//! directly and through a generalized wrapper.) Comparing the views separately is
//! also strictly more discriminating, and over-splitting is a wasted clone while
//! under-splitting is a miscompile.
//!
//! # The remaining rules
//!
//! - **Union, never narrow.** Polarity picks which bounds to follow; merging is
//!   always union. A polarity-correct merge *intersects* record fields and refinement
//!   sets at one of the two polarities, which is what makes a rendering forget an
//!   argument's unused fields. A key that narrows can only under-split, and
//!   under-splitting is a miscompile while over-splitting is a wasted clone.
//! - **Canonical when under-determined.** A position nothing concrete reached is
//!   the [`Default`] key, not a freshly-minted `Infer` placeholder. Placeholder
//!   ids are fresh per resolution, so a key carrying them could never match a
//!   second time.
//! - **Conflict-tolerant.** Two atoms, or two history kinds, at one position are
//!   both recorded. A key is a fingerprint, not a type that has to typecheck —
//!   the real resolution is what reports the conflict, and a key that raised an
//!   error would have to pick a specialization anyway.
//!
//! The property this buys: *if two uses' keys are equal then the clone coalesced
//! under either use's pin is the same code*, because every edge the clone's own
//! resolution can follow is followed, from the same side, by one of the two reads.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, btree_map::Entry};
use std::fmt;
use std::rc::Rc;

use smol_str::SmolStr;

use crate::ccl::subst::Subst;
use crate::ccl::{FieldKey, HistoryKind, InferVarId, Refinement, Type};

use super::compact::{AtomKey, KindMerge};

/// The identity of a use's instantiation, for deciding which uses may share one
/// monomorphization specialization: its two directed reads, kept apart (see the
/// module docs for why merging them is wrong).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SpecKey {
    /// The stamping view — a domain resolved from the definition's demands.
    positive: KeyView,
    /// The clone's view — a domain resolved from the argument that flowed in.
    /// This is the half that sees a use's refinements.
    negative: KeyView,
}

/// A canonical fingerprint of one position, under one directed read.
///
/// Every field accumulates by **union** ([`KeyView::union`]); the all-empty value
/// ([`Default`]) is both the "nothing concrete here" view and the merge identity.
/// Equality is structural, with refinement sets compared as *sets* (they accumulate
/// in first-insertion order, which is not canonical) — see the [`PartialEq`] impl.
#[derive(Debug, Clone, Default)]
struct KeyView {
    /// Leaf contributions (bases, ranges, sources, `Txn`, channel domains).
    atoms: BTreeSet<AtomKey>,
    /// Refinements at this position, deduplicated by [`Refinement`]'s
    /// type-blind structural equality. Order is insertion order, so equality
    /// compares these as a set.
    refinements: Vec<Refinement>,
    /// Function contributions, **keyed by kind** so a compute arrow and a data
    /// collection at one position stay distinguishable rather than one shadowing
    /// the other — exactly as [`history`](Self::history) is keyed by
    /// [`HistoryKind`]. Each maps to `(domain, codomain)`.
    ///
    /// The kind belongs in the key because it is what a clone *compiles to*: a
    /// specialization pinned at `⤇` iterates a domain that a `⇒` use does not
    /// supply. It is read through [`KindMerge::of`], the same resolved-from-bounds
    /// view compaction uses, rather than off the [`FunKind`](crate::ccl::ty::FunKind)
    /// itself — an inferred kind is a variable here, and keying on its *identity*
    /// (fresh per instantiation) would split every use into its own key while
    /// telling us nothing.
    ///
    /// Like every other field this reads the live graph mid-solve, so a kind may
    /// still be accumulating; that is the same bargain the `Infer` bounds make, and
    /// the same guarantee holds — agreement with the pin, not omniscience.
    ///
    /// The Pi binder name is deliberately **not** part of the key. It is either
    /// cosmetic (stripped at materialization when no predicate references it) or
    /// it is referenced by a refinement predicate — and the predicate itself is in
    /// `refinements`, compared structurally. Keeping the name would also make the
    /// key sensitive to the solver's per-site fresh dependent-application binders
    /// (`Name::solver_arg`), which would split every use into its own key.
    fun: BTreeMap<KindMerge, (Box<KeyView>, Box<KeyView>)>,
    /// Record/tuple fields, unioned. Tuples and records share this representation
    /// keyed by `Index` / `Name`, exactly as `compact_type` normalizes them.
    rec: BTreeMap<FieldKey, KeyView>,
    /// Variant tags, unioned.
    var: BTreeMap<FieldKey, KeyView>,
    /// History contributions, keyed by kind so an `Overwrite` and an `Append`
    /// handle at one position stay distinguishable rather than one shadowing the
    /// other. Each maps to `(value, domain)`.
    history: BTreeMap<HistoryKind, (Box<KeyView>, Box<KeyView>)>,
}

/// Structural equality, with `refinements` compared as a set.
///
/// Refinements accumulate in first-insertion order, which depends on the order the
/// walk happened to reach a variable's bounds — not on the position's meaning. A
/// positional comparison would therefore split two identical instantiations whose
/// bound lists were built in different orders. Both sides are deduplicated on
/// insertion, so equal lengths plus containment is set equality.
impl PartialEq for KeyView {
    fn eq(&self, other: &Self) -> bool {
        fn same_refinements(a: &[Refinement], b: &[Refinement]) -> bool {
            a.len() == b.len() && a.iter().all(|w| b.contains(w))
        }
        self.atoms == other.atoms
            && same_refinements(&self.refinements, &other.refinements)
            && self.fun == other.fun
            && self.rec == other.rec
            && self.var == other.var
            && self.history == other.history
    }
}

impl Eq for KeyView {}

impl KeyView {
    /// Fold `other` into `self` positionwise. Union everywhere: sets union, maps
    /// union by key with matching entries merged recursively, and a shape present
    /// on one side only passes through.
    fn union(&mut self, other: KeyView) {
        self.atoms.extend(other.atoms);
        for w in other.refinements {
            if !self.refinements.contains(&w) {
                self.refinements.push(w);
            }
        }
        for (kind, (domain, codomain)) in other.fun {
            match self.fun.entry(kind) {
                Entry::Vacant(e) => {
                    e.insert((domain, codomain));
                }
                Entry::Occupied(mut e) => {
                    let (d0, c0) = e.get_mut();
                    d0.union(*domain);
                    c0.union(*codomain);
                }
            }
        }
        union_map(&mut self.rec, other.rec);
        union_map(&mut self.var, other.var);
        for (kind, (value, domain)) in other.history {
            match self.history.entry(kind) {
                Entry::Vacant(e) => {
                    e.insert((value, domain));
                }
                Entry::Occupied(mut e) => {
                    let (v0, d0) = e.get_mut();
                    v0.union(*value);
                    d0.union(*domain);
                }
            }
        }
    }

    fn from_atom(a: AtomKey) -> KeyView {
        KeyView {
            atoms: BTreeSet::from([a]),
            ..Default::default()
        }
    }
}

fn union_map(into: &mut BTreeMap<FieldKey, KeyView>, from: BTreeMap<FieldKey, KeyView>) {
    for (k, v) in from {
        match into.entry(k) {
            Entry::Vacant(e) => {
                e.insert(v);
            }
            Entry::Occupied(mut e) => e.get_mut().union(v),
        }
    }
}

/// A terse, type-like rendering, for assertion messages and traces. An empty view
/// is `_`; a position with several contributions joins them with `&`.
impl fmt::Display for KeyView {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts: Vec<String> = self.atoms.iter().map(|a| a.to_type().to_string()).collect();
        for (kind, (d, c)) in &self.fun {
            let arrow = match kind {
                KindMerge::Data => "⤇",
                KindMerge::Compute => "⇒",
                KindMerge::Conflict => "⇒!",
            };
            parts.push(format!("({d} {arrow} {c})"));
        }
        if !self.rec.is_empty() {
            let fields: Vec<String> = self.rec.iter().map(|(k, v)| format!("{k}: {v}")).collect();
            parts.push(format!("({})", fields.join(", ")));
        }
        if !self.var.is_empty() {
            let tags: Vec<String> = self.var.iter().map(|(k, v)| format!(".{k}: {v}")).collect();
            parts.push(format!("[{}]", tags.join(" | ")));
        }
        for (kind, (value, domain)) in &self.history {
            let name = match kind {
                HistoryKind::Overwrite => "Mut",
                HistoryKind::Append => "Feed",
            };
            parts.push(format!("{name}({value}, {domain})"));
        }
        let base = if parts.is_empty() {
            "_".to_string()
        } else {
            parts.join(" & ")
        };
        if self.refinements.is_empty() {
            write!(f, "{base}")
        } else {
            let preds: Vec<String> = self
                .refinements
                .iter()
                .map(|w| crate::ccl::symbolic::symbolic(&w.predicate))
                .collect();
            write!(f, "{{{base} | {}}}", preds.join(", "))
        }
    }
}

/// Renders the two views, or just one when they agree (the common case for a
/// fully-determined instantiation).
impl fmt::Display for SpecKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.positive == self.negative {
            write!(f, "{}", self.positive)
        } else {
            write!(f, "{} ⊣ {}", self.positive, self.negative)
        }
    }
}

/// Walk-wide state: the cycle guard, the per-variable memo, and the truncation
/// counter that decides what may be memoized.
struct KeyCtx {
    /// Variables whose bounds are currently being walked, per polarity — the same
    /// key `compact_type`'s cycle guard uses, and for the same reason: a variable
    /// legitimately appears at both polarities in one type.
    visiting: HashSet<(InferVarId, bool)>,
    /// Completed keys per `(variable, polarity)`, for variables reached under the
    /// identity substitution.
    ///
    /// Sound because a variable's directed key depends only on the variable and
    /// the direction — not on the position it was reached from. A variable reached
    /// under a *non-identity* substitution bypasses the memo: the substitution
    /// rewrites the predicates the walk materializes, so that result *is*
    /// position-dependent.
    memo: HashMap<(InferVarId, bool), KeyView>,
    /// How many cycle back-edges the walk has dropped. A key computed while a
    /// truncation occurred inside it is *incomplete* — it is missing whatever the
    /// back-edge would have contributed — so it must not be memoized. Comparing
    /// the counter before and after a variable's expansion is what detects that.
    truncations: usize,
}

/// The specialization key of `ty`: its two directed reads (see the module docs).
///
/// Reads the live bound graph, so it must be called with the graph in the state
/// the use's pin will see — i.e. *before* the pin, matching every other use's
/// key, so that both sides of a memo comparison are computed by one procedure at
/// one point in the pin's lifecycle.
pub fn spec_key(ty: &Type) -> SpecKey {
    let mut ctx = KeyCtx {
        visiting: HashSet::new(),
        memo: HashMap::new(),
        truncations: 0,
    };
    // One walk-wide `ctx` for both reads: its memo is keyed by polarity, so the
    // two reads share it without contaminating each other.
    SpecKey {
        positive: key_go(ty, true, &Subst::id(), &mut ctx),
        negative: key_go(ty, false, &Subst::id(), &mut ctx),
    }
}

fn key_go(ty: &Type, pol: bool, subst_acc: &Subst, ctx: &mut KeyCtx) -> KeyView {
    match ty {
        // `Below` is a *pre-inference* annotation marker: `normalize_annotation`
        // erases it into a bounded variable before any constraint is emitted, so
        // the solver never sees one.
        Type::Below(_) => {
            unreachable!("Type::Below reached the solver; `normalize_annotation` must erase it")
        }
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::ChanDom(..)
        | Type::Txn => KeyView::from_atom(
            AtomKey::from_type(ty).expect("every atomic type classifies as an AtomKey"),
        ),
        // A `Hole` contributes nothing — the same "no information here" the
        // default key denotes, so a `Hole` keys identically to an
        // under-determined `Infer`. That collision cannot merge two uses that
        // actually differ, because emission normalizes every annotation
        // (`normalize_annotation` turns a `Hole` into a fresh `Type::Infer`), so
        // no `Hole` reaches a use's instantiation type in the first place. The
        // arm is for exhaustiveness, and "no information here" is the honest
        // reading if one ever did.
        Type::Hole | Type::SharedHole(_) => KeyView::default(),
        // A refinement rides the position it refines. The accumulated substitution
        // is forced on it exactly as `compact_go` does, so a suspended
        // dependent-application discharge lands in the key as the predicate the
        // clone will actually carry — that is use-specific information, and two
        // uses discharging different arguments *should* key apart.
        Type::Refinement(inner, r) => {
            let mut k = key_go(inner, pol, subst_acc, ctx);
            let r = subst_acc.force_refinement(r);
            if !k.refinements.contains(&r) {
                k.refinements.push(r);
            }
            k
        }
        Type::Fun {
            name,
            domain,
            codomain,
            kind,
        } => {
            // The domain is contravariant — the flip that makes the dual read
            // follow an argument's *lower* bounds.
            let dom = key_go(domain, !pol, subst_acc, ctx);
            // A Pi binder shadows the accumulated substitution inside the
            // codomain, as in `compact_go`. The binder *name* itself is not part
            // of the key — see `SpecKey::fun`.
            let cod_acc = match name {
                Some(b) => subst_acc.shadow(b),
                None => subst_acc.clone(),
            };
            let cod = key_go(codomain, pol, &cod_acc, ctx);
            // Resolved through `KindMerge::of`, not off the `FunKind` itself: an
            // inferred kind is a variable whose identity is fresh per instantiation,
            // so keying on it would split every use; its *bounds* are the answer, and
            // reading them here is what compaction does at the same point in the solve.
            KeyView {
                fun: BTreeMap::from([(KindMerge::of(kind), (Box::new(dom), Box::new(cod)))]),
                ..Default::default()
            }
        }
        Type::Tuple(ts) => KeyView {
            rec: ts
                .iter()
                .enumerate()
                .map(|(i, t)| (FieldKey::Index(i), key_go(t, pol, subst_acc, ctx)))
                .collect(),
            ..Default::default()
        },
        Type::Record(fs) => KeyView {
            rec: fs
                .iter()
                .map(|(n, t)| {
                    (
                        FieldKey::Name(SmolStr::from(n.as_str())),
                        key_go(t, pol, subst_acc, ctx),
                    )
                })
                .collect(),
            ..Default::default()
        },
        Type::Variant(tags) => KeyView {
            var: tags
                .iter()
                .map(|(k, t)| (k.clone(), key_go(t, pol, subst_acc, ctx)))
                .collect(),
            ..Default::default()
        },
        // A history's children are invariant, so they recurse at the reference's
        // own polarity — no flip, matching `compact_go`.
        Type::History {
            value,
            domain,
            kind,
        } => {
            let value = key_go(value, pol, subst_acc, ctx);
            let domain = key_go(domain, pol, subst_acc, ctx);
            KeyView {
                history: BTreeMap::from([(*kind, (Box::new(value), Box::new(domain)))]),
                ..Default::default()
            }
        }
        // A variable contributes its **polarity-correct** bounds only. Following
        // both here instead is what leaks out of this use's cone and into every
        // other use's arguments; the two root reads are what cover both
        // directions without ever mixing them at one variable. There is no
        // opposite-polarity fallback either — the dual read subsumes it.
        Type::Infer(state) => {
            let memo_key = (state.uid, pol);
            let memoizable = subst_acc.is_id();
            if memoizable && let Some(k) = ctx.memo.get(&memo_key) {
                return k.clone();
            }
            if !ctx.visiting.insert(memo_key) {
                // A cycle in the bound graph (`?a <: ?b` and `?b <: ?a` is
                // ordinary). Drop the back-edge: whatever it would contribute is
                // already on the path that reached it. Recorded so the partial
                // result this produces is never cached.
                ctx.truncations += 1;
                return KeyView::default();
            }
            let bounds = {
                let b = state.bounds.borrow();
                Rc::clone(if pol { b.lower() } else { b.upper() })
            };
            let truncations_before = ctx.truncations;
            let mut acc = KeyView::default();
            for b in bounds.iter() {
                // Compose the edge's morphism before descending, as `compact_go`
                // does: a bound reached transitively arrives with every edge's
                // substitution composed.
                let inner_acc = Subst::then(&b.render_subst(), subst_acc);
                acc.union(key_go(&b.ty, pol, &inner_acc, ctx));
            }
            ctx.visiting.remove(&memo_key);
            if memoizable && ctx.truncations == truncations_before {
                ctx.memo.insert(memo_key, acc.clone());
            }
            acc
        }
    }
}

#[cfg(test)]
mod tests {
    // `ConstrainCache` keys on `(Type, Type)`; its interior mutability is
    // identity-by-`uid` and never inspected by `Hash`/`Eq`, so the lint's hazard
    // does not apply (see `constrain`'s module-level note).
    #![allow(clippy::mutable_key_type)]

    use std::rc::Rc;

    use super::*;
    use crate::ccl::infer::solver::{ConstrainCache, constrain_subtype, fresh_var};
    use crate::ccl::infer_var::Bound;
    use crate::ccl::{BaseType, Lit, TypedExpr};

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }

    /// `{Int | __elem == n}` — a literal's singleton, the refinement every literal
    /// carries and therefore the one this key exists to see.
    fn singleton(n: i64) -> Type {
        crate::ccl::infer::lit_singleton(&Lit::Int(n))
    }

    fn refined(marker: i64) -> Refinement {
        Refinement::born(Rc::new(TypedExpr::lit(Lit::Int(marker))))
    }

    #[test]
    fn atoms_and_shapes_are_structural() {
        assert_eq!(spec_key(&int()), spec_key(&int()));
        assert_ne!(spec_key(&int()), spec_key(&Type::Base(BaseType::String)));
        assert_eq!(
            spec_key(&Type::Tuple(vec![int(), int()])),
            spec_key(&Type::Tuple(vec![int(), int()]))
        );
        // Width matters: a key must not equate a 1-tuple with a 2-tuple, or a
        // narrowed domain would share a clone with an unnarrowed one.
        assert_ne!(
            spec_key(&Type::Tuple(vec![int()])),
            spec_key(&Type::Tuple(vec![int(), int()]))
        );
    }

    #[test]
    fn refinements_participate_and_distinguish() {
        assert_ne!(spec_key(&int()), spec_key(&singleton(1)));
        assert_ne!(spec_key(&singleton(1)), spec_key(&singleton(2)));
        assert_eq!(spec_key(&singleton(1)), spec_key(&singleton(1)));
    }

    #[test]
    fn refinement_sets_compare_order_insensitively() {
        let a = Type::Refinement(
            Box::new(Type::Refinement(Box::new(int()), refined(1))),
            refined(2),
        );
        let b = Type::Refinement(
            Box::new(Type::Refinement(Box::new(int()), refined(2))),
            refined(1),
        );
        assert_eq!(spec_key(&a), spec_key(&b));
    }

    /// An under-determined position is one canonical value, not a fresh
    /// placeholder — two such uses must be able to share.
    #[test]
    fn under_determined_positions_are_canonical() {
        assert_eq!(spec_key(&fresh_var(0)), spec_key(&fresh_var(0)));
        assert_eq!(spec_key(&fresh_var(0)), SpecKey::default());
    }

    /// The defect the key exists to fix: an argument's refinement reaches a domain
    /// variable as a **lower** bound, where a negative-position materialization
    /// cannot see it. The saturated key sees it, so two calls differing only
    /// there key apart.
    #[test]
    fn lower_bound_refinement_is_visible_where_a_materialization_narrows() {
        let mut keys = Vec::new();
        for n in [2, 5] {
            let dom = fresh_var(0);
            let mut cache = ConstrainCache::new();
            // The emit-time `arg <: domain` edge, for an argument carrying its
            // literal's singleton.
            constrain_subtype(&singleton(n), &dom, &mut cache).expect("arg flows into domain");
            // And the definition's demand, which is all a negative resolution of
            // `dom` would consult.
            constrain_subtype(&dom, &int(), &mut cache).expect("domain meets the body's demand");
            keys.push(spec_key(&Type::fun(dom, int())));
        }
        assert_ne!(
            keys[0], keys[1],
            "two calls whose only difference is an argument refinement on the \
             domain's lower bounds must not share a specialization"
        );
    }

    /// A cycle between two variables terminates, and the walk still collects what
    /// is reachable on the way rather than bailing out to the empty key. (`?a <:
    /// ?b` with `?b <: ?a` is the ordinary spurious cycle, not a recursive type.)
    #[test]
    fn mutually_constrained_vars_terminate() {
        let a = fresh_var(0);
        let b = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&a, &b, &mut cache).expect("a <: b");
        constrain_subtype(&b, &a, &mut cache).expect("b <: a");
        constrain_subtype(&singleton(7), &a, &mut cache).expect("7 <: a");
        let k = spec_key(&a);
        assert_ne!(k, SpecKey::default(), "the lower bound must be collected");
        assert_eq!(k, spec_key(&a), "and the walk must be deterministic");
        // The refinement is on `a`'s lower bounds, so it is the *positive* read that
        // carries it — the same asymmetry a domain position exploits in reverse.
        assert_eq!(k.positive, spec_key(&singleton(7)).positive);
    }

    /// A key computed while a cycle back-edge was dropped is **incomplete**, so it
    /// must not enter the memo — otherwise a later position that reaches the same
    /// variable from outside the cycle is served the truncated view.
    ///
    /// The shape: `?a` and `?b` are mutually constrained and each carries a
    /// refinement of its own, so each one's *complete* view is both refinements.
    /// Reached from position 0, `?b` expands with `?a` already on the stack — the
    /// back-edge is dropped and `?b` sees only its own `2`. Position 1 then asks for
    /// `?b` directly, where nothing is on the stack and the answer is `{1, 2}`.
    /// Without [`KeyCtx::truncations`] guarding the insert, the truncated `{2}` is
    /// cached at position 0 and returned at position 1, and one type has two
    /// different keys depending on where the walk met it.
    ///
    /// The cycle is built by **writing the bound lists directly** rather than
    /// through [`constrain_subtype`], and that is the point: `constrain_go` keeps
    /// the bound graph transitively closed, so a back-edge it recorded really does
    /// contribute nothing new and the guard never fires. This walk must not depend
    /// on that invariant — bounds also arrive carrying an edge substitution
    /// (`Bound::render_subst`), where the transitive copy and the direct one are not
    /// the same contribution.
    #[test]
    fn a_truncated_expansion_is_not_memoized() {
        fn push_lower(var: &Type, ty: Type) {
            let Type::Infer(v) = var else {
                unreachable!("fresh_var yields Type::Infer");
            };
            v.bounds.borrow_mut().lower_mut().push(Bound::conc(ty));
        }
        let a = fresh_var(0);
        let b = fresh_var(0);
        push_lower(&a, singleton(1));
        push_lower(&a, b.clone());
        push_lower(&b, singleton(2));
        push_lower(&b, a.clone());

        // Both variables reach both refinements, so both positions see both — no
        // matter which one the walk expands first.
        let both = spec_key(&Type::Tuple(vec![a.clone(), b.clone()]));
        let (pos0, pos1) = (
            &both.positive.rec[&FieldKey::Index(0)],
            &both.positive.rec[&FieldKey::Index(1)],
        );
        assert_eq!(
            pos0, pos1,
            "the second position was served a view truncated while computing the \
             first: {pos0} vs {pos1}"
        );
        assert_eq!(
            pos0.refinements.len(),
            2,
            "both refinements, at both positions: {pos0}"
        );

        // And the whole key is independent of the order the walk meets them.
        assert_eq!(both, spec_key(&Type::Tuple(vec![b, a])));
    }

    /// [`KeyView::union`]'s structural merges: two bounds contributing *different*
    /// shapes at one position must merge positionwise rather than one winning.
    ///
    /// Only the variable arm ever calls `union` with two non-empty views, so these
    /// merges are unreachable except through a variable carrying several bounds —
    /// which is exactly the ordinary case for a use whose argument and whose
    /// definition-side demand both say something.
    #[test]
    fn several_bounds_at_one_position_merge_positionwise() {
        // `?v` bounded below by two function types that differ only in their
        // codomain: the merged view must carry both codomain atoms, not the first.
        let v = fresh_var(0);
        let mut cache = ConstrainCache::new();
        for cod in [int(), Type::Base(BaseType::String)] {
            let f = Type::fun(singleton(1), cod);
            constrain_subtype(&f, &v, &mut cache).expect("bound flows into v");
        }
        let k = spec_key(&v);
        let (dom, cod) = k
            .positive
            .fun
            .values()
            .next()
            .expect("both bounds are functions, so the merged view has a function shape");
        assert_eq!(
            cod.atoms.len(),
            2,
            "a conflict at one position is recorded, not resolved: {cod}"
        );
        assert_eq!(
            dom.refinements.len(),
            1,
            "the shared domain refinement is deduplicated, not doubled: {dom}"
        );
    }

    /// A function's **kind** is part of its identity for the same reason a history's
    /// flavour is: `𝐷 ⇒ 𝑉` and `𝐷 ⤇ 𝑉` are one shape and compile to different code —
    /// a specialization pinned at `⤇` iterates a domain a `⇒` use does not supply — so
    /// a clone keyed on one must not serve a use of the other.
    ///
    /// The kind reaches the key through `KindMerge::of`, so a concrete arrow keys by
    /// what it *is*. An unresolved `FunKind::Var` resolves from its bounds like any
    /// other position, which is what keeps two uses of one generic binding sharing a
    /// clone instead of splitting on a per-instantiation variable identity.
    #[test]
    fn fun_kind_is_part_of_the_key() {
        assert_ne!(
            spec_key(&Type::fun(int(), int())),
            spec_key(&Type::data_fun(int(), int())),
            "a capability and a collection of the same shape must not share a clone"
        );
        // An *unresolved* kind does not split: both uses read the same unbounded var
        // through `KindMerge::of`, which answers `Compute` (the capability default).
        let unresolved = || Type::Fun {
            name: None,
            kind: crate::ccl::ty::FunKind::fresh_var(),
            domain: Box::new(int()),
            codomain: Box::new(int()),
        };
        assert_eq!(
            spec_key(&unresolved()),
            spec_key(&unresolved()),
            "two fresh kind vars are the same unresolved answer, not two identities"
        );
        // And the merge keeps two concrete kinds apart rather than one shadowing the
        // other — what keying `fun` by `KindMerge` buys, and why it needs `Ord`.
        let mut merged = key_go(
            &Type::fun(int(), int()),
            true,
            &Subst::id(),
            &mut fresh_ctx(),
        );
        merged.union(key_go(
            &Type::data_fun(int(), int()),
            true,
            &Subst::id(),
            &mut fresh_ctx(),
        ));
        assert_eq!(
            merged.fun.len(),
            2,
            "a compute and a data arrow at one position are distinct contributions: {merged}"
        );
    }

    /// A history's flavour is part of its identity: a `Mut(Int, Txn)` mutable variable and
    /// a `Feed(Int, Txn)` channel are the same `domain ⇒ value` shape and must not
    /// key alike, or a clone pinned to one would serve a use of the other.
    #[test]
    fn history_kind_is_part_of_the_key() {
        let history = |kind| Type::History {
            value: Box::new(int()),
            domain: Box::new(Type::Txn),
            kind,
        };
        assert_ne!(
            spec_key(&history(HistoryKind::Overwrite)),
            spec_key(&history(HistoryKind::Append))
        );
        // And the merge keeps them apart rather than one shadowing the other —
        // which is what the `history` map being keyed by kind buys, and why
        // `HistoryKind` needs `Ord`. Driven through `union` directly: `constrain`
        // reads an `Overwrite` handle *through* to its value type, so the two kinds
        // never reach one variable's bound list by way of a subtyping edge.
        let mut merged = key_go(
            &history(HistoryKind::Overwrite),
            true,
            &Subst::id(),
            &mut fresh_ctx(),
        );
        merged.union(key_go(
            &history(HistoryKind::Append),
            true,
            &Subst::id(),
            &mut fresh_ctx(),
        ));
        assert_eq!(
            merged.history.len(),
            2,
            "an Overwrite and an Append at one position are distinct contributions: {merged}"
        );
    }

    fn fresh_ctx() -> KeyCtx {
        KeyCtx {
            visiting: HashSet::new(),
            memo: HashMap::new(),
            truncations: 0,
        }
    }
}
