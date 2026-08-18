//! The constraint solver at the core of Cambra's inference algorithm.
//!
//! The solver operates **directly on [`crate::ccl::Type`]** — there is no
//! separate internal type representation. An inference variable is a
//! [`Type::Infer`] carrying a mutable [`crate::ccl::InferVar`] (lower/upper
//! bound lists); `constrain_subtype` mutates those bounds in place, and the
//! `compact`/`simplify`/`coalesce` pipeline resolves a bound graph back into
//! a concrete `Type`. The only intermediate is the internal `CompactType`
//! used by simplification.
//!
//! # Refinements
//!
//! Refinements ride the lattice natively, as a **set** per position. A
//! refined type `{T | S}` carries a set `S` of [`Refinement`](crate::ccl::Refinement)
//! refinements (matched by structural predicate equality — see
//! [`Refinement`](crate::ccl::Refinement)'s
//! `PartialEq` — but never by predicate implication). Subtyping is
//! superset-on-refinements, structurally identical to record width-subtyping
//! (`{T | p, q} <: {T | p}`, and `{T | p} <: T`); a refinement set therefore
//! merges with the same polarity rule as `rec` (positive ⇒ intersect,
//! negative ⇒ union) and is preserved verbatim through simplification
//! (refinements are positional, never folded into a variable's identity, so
//! co-occurrence merging cannot move or drop them). A refinement is
//! *required*, so `constrain_subtype` is strict in the other
//! direction: an unrefined value does **not** flow into a refined position
//! (`T ⊀ {T | p}`). Acquiring a refinement is an explicit operation — the
//! interpreter compiles a refinement on a *collection domain* to a runtime
//! `Restrict`/`Filter` at the iteration boundary (the `Iterate`/`Restrict`
//! arms of [`crate::interpreter::operator_conversion`], where `extent_of`
//! strips the domain refinement into a `Restrict`); it is not modelled as
//! subsumption here. The predicate `Expr` of each refinement lives in
//! [`crate::ccl::Refinement`] and is inferred/coalesced like any other
//! sub-tree.
//!
//! # Reference
//!
//! Cambra's solver is originally based on Parreaux, "The Simple Essence of
//! Algebraic Subtyping" (ICFP 2020), extended here with Pi types and
//! refinements.

use crate::ccl::{BaseType, InferVar, Level, Type};

pub mod coalesce;
pub mod compact;
pub mod constrain;
pub mod scheme;
pub mod simplify_type;
pub mod spec_key;
pub mod traits;

// Re-export every symbol that external modules reach through the
// `crate::ccl::infer::solver::…` path (chiefly the inference engine), so the
// directory split is path-transparent.
pub use coalesce::{CoalesceError, coalesce_compact};
pub use compact::{CompactGraph, CompactType, compact_type, compact_type_polarity_only};
pub use constrain::{ConstrainCache, ConstrainError, ExtrudeCache, constrain_subtype, extrude};
pub use scheme::{
    FreshenCache, FreshenLevel, PolyScheme, freshen_above, freshen_expr_type_slots,
    seed_chan_dom_pairings,
};
pub use simplify_type::simplify_type;
pub use spec_key::{SpecKey, spec_key};

/// The level of `ty` — the maximum scope level of any inference variable
/// occurring inside it. Leaves and `Hole` are level 0; `Refinement` defers
/// to its inner type (refinements are lattice-blind). Used by `extrude` and by
/// let-generalization (`infer::context::should_generalize`, which generalizes
/// a binding when its type's level exceeds the binding level).
pub fn type_level(ty: &Type) -> Level {
    match ty {
        Type::Infer(v) => v.level,
        // A bounded annotation's level is its bound's: the variable it becomes is
        // minted at the *use* level by `normalize_annotation`, so the bound is all
        // there is to report here.
        Type::BoundedHole(t) => type_level(t),
        Type::Fun {
            domain: d,
            codomain: c,
            ..
        } => type_level(d).max(type_level(c)),
        Type::Tuple(ts) => ts.iter().map(type_level).max().unwrap_or(0),
        Type::Record(fs) => fs.iter().map(|(_, t)| type_level(t)).max().unwrap_or(0),
        Type::Variant(tags, _) => tags.iter().map(|(_, t)| type_level(t)).max().unwrap_or(0),
        Type::Refinement(inner, _) => type_level(inner),
        // Combine both children like `Fun` (domain + codomain): a later
        // increment's per-call-site domain generalization depends on the
        // `domain`'s level surfacing here, so a fresh domain var pins the
        // level of the enclosing `Mut`.
        Type::History { value, domain, .. } => type_level(value).max(type_level(domain)),
        // A channel domain stores its introduction level, but deliberately
        // reports 0 here: `type_level` drives extrusion and bound-recording
        // level scoping, and a rigid atom must flow through bounds to
        // lower-level consumers *unchanged* — that flow is exactly how a
        // channel's readers come to reference it. The stored level's one
        // consumer is `freshen_above`'s `ChanDom` arm (quantification at
        // instantiation), which reads it directly and is exempted from the
        // `type_level` short-circuit.
        Type::ChanDom(..) => 0,
        Type::Base(_)
        | Type::UIntRange(_)
        | Type::DataSource(_)
        | Type::Txn
        | Type::Hole
        | Type::SharedHole(_) => 0,
    }
}

/// Construct a fresh inference variable at the given level, as a [`Type`]
/// for direct use in constraint emission.
pub fn fresh_var(level: Level) -> Type {
    Type::Infer(InferVar::fresh(level))
}

/// Wrap a [`BaseType`] as a primitive [`Type`].
pub fn prim(b: BaseType) -> Type {
    Type::Base(b)
}

/// Build a function [`Type`] from domain and codomain.
pub fn fun(d: Type, c: Type) -> Type {
    Type::Fun {
        name: None,
        kind: crate::ccl::ty::FunKind::Compute,
        domain: Box::new(d),
        codomain: Box::new(c),
    }
}

/// Shared test-only constructors used by more than one submodule's tests.
#[cfg(test)]
pub(crate) mod test_helpers {
    use std::rc::Rc;

    use smol_str::SmolStr;

    use crate::ccl::{FieldKey, Refinement, Type};

    /// The dependent refinement `__elem == <name>` — a predicate referencing an
    /// enclosing Pi binder by (raw) name, the mid-solve coordinate.
    pub(crate) fn dep_pred(name: &str) -> Rc<crate::ccl::TypedExpr> {
        use crate::ccl::{BinOpKind, CompareKind, Name, TypedExpr};
        Rc::new(TypedExpr::binop(
            TypedExpr::var(Name::elem()),
            BinOpKind::Compare(CompareKind::Equals),
            TypedExpr::var(Name::raw(name)),
        ))
    }

    /// Build a `Type` from `FieldKey`-keyed fields: all-`Name` → `Record`,
    /// otherwise a dense `Tuple` (the only product shapes `ccl::Type` has).
    /// Sparse-`Index` inputs have no `Type` form — tests that need them
    /// build the `CompactType` directly.
    ///
    /// No fields → `Unit`, matching the real `product` constructor: the empty
    /// product has one representation and it is not `Tuple([])`.
    pub(crate) fn record(fields: &[(FieldKey, Type)]) -> Type {
        if fields.is_empty() {
            return Type::Base(crate::ccl::BaseType::Unit);
        }
        if fields.iter().all(|(k, _)| matches!(k, FieldKey::Name(_))) {
            Type::Record(
                fields
                    .iter()
                    .map(|(k, t)| match k {
                        FieldKey::Name(n) => (n.to_string(), t.clone()),
                        _ => unreachable!(),
                    })
                    .collect(),
            )
        } else {
            Type::Tuple(fields.iter().map(|(_, t)| t.clone()).collect())
        }
    }

    /// Build `{base | marker}` — a `Type::Refinement` whose refinement's predicate
    /// encodes `marker` (an `Int(marker)` literal). Refinements compare by
    /// structural predicate equality (see [`Refinement`]'s `PartialEq`), so
    /// equal markers match and distinct markers stay distinct.
    pub(crate) fn refined(base: Type, marker: i64) -> Type {
        use crate::ccl::{Lit, TypedExpr};
        let r = Refinement::born(Rc::new(TypedExpr::lit(Lit::Int(marker))));
        Type::Refinement(Box::new(base), r)
    }

    /// Helper: build a `Type::Variant({tag: payload, ...})` with named
    /// (`FieldKey::Name`) tags.
    pub(crate) fn variant<const N: usize>(tags: [(&str, Type); N]) -> Type {
        Type::variant(
            tags.into_iter()
                .map(|(k, v)| (FieldKey::Name(SmolStr::from(k)), v))
                .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    // `ConstrainCache` keys on `(Type, Type)`; its interior mutability is
    // identity-by-`uid` and never inspected by `Hash`/`Eq`, so the lint's
    // hazard does not apply (see `constrain`'s module-level note).
    #![allow(clippy::mutable_key_type)]

    use std::rc::Rc;

    use super::*;
    use crate::ccl::{BaseType, InferVar, Type};

    #[test]
    fn fresh_var_has_no_bounds() {
        let v = InferVar::fresh(0);
        let s = v.bounds.borrow();
        assert!(s.lower().is_empty());
        assert!(s.upper().is_empty());
        assert_eq!(v.level, 0);
    }

    /// Regression: mutually-constrained inference variables form an `Rc`
    /// cycle through their bounds (`?a <: ?b` stores `?b` in `?a`'s upper
    /// bounds and vice versa). Reference counting alone never rerefinements it;
    /// the owning [`InferArena`](crate::ccl::infer::InferArena)'s `Drop` is
    /// what clears the bounds and breaks the cycle.
    /// If this fails, the cycle is leaking again.
    #[test]
    fn mutually_constrained_vars_leak_via_rc_cycle() {
        use crate::ccl::infer::InferArena;
        use std::rc::Weak;

        // Activate an arena so the two `fresh_var` mints below are owned by
        // it; its `Drop` is what clears the bounds and breaks the cycle.
        let arena = InferArena::new();

        let a = fresh_var(0);
        let b = fresh_var(0);
        let mut cache = ConstrainCache::new();
        // ?a <: ?b and ?b <: ?a — the ordinary "spurious cycle" the solver
        // tolerates; nothing recursive or exotic is required.
        constrain_subtype(&a, &b, &mut cache).unwrap();
        constrain_subtype(&b, &a, &mut cache).unwrap();

        let (wa, wb): (Weak<InferVar>, Weak<InferVar>) = match (&a, &b) {
            (Type::Infer(va), Type::Infer(vb)) => (Rc::downgrade(va), Rc::downgrade(vb)),
            _ => unreachable!("fresh_var yields Type::Infer"),
        };

        // Drop every external strong handle. The cache also holds `Type`
        // clones (its keys are `(Type, Type)`), so it must go too — it is
        // dropped at the end of a real constraint-emission pass anyway.
        drop(cache);
        drop(a);
        drop(b);

        // Tearing down the arena clears both cells' bounds, severing the
        // mutual `Rc` edges. Only after this can the refcounts reach zero.
        drop(arena);

        assert!(
            wa.upgrade().is_none() && wb.upgrade().is_none(),
            "expected the Rc cycle to be reclaimed; both inference vars leaked"
        );
    }

    #[test]
    fn level_of_compound_is_max_of_components() {
        let v0 = fresh_var(0);
        let v1 = fresh_var(1);
        let f = fun(v0, v1);
        assert_eq!(type_level(&f), 1);
    }

    #[test]
    fn primitives_have_level_zero() {
        let p = prim(BaseType::Int);
        assert_eq!(type_level(&p), 0);
    }
}
