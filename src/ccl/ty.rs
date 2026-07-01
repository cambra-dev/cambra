//! The CCL [`Type`] lattice, its [`Refinement`] subset-type carrier, and the
//! type-blind structural equality / hashing on refinement predicate terms.

use std::fmt;
use std::rc::Rc;

use crate::ccl::simple_sub::FieldKey;
use crate::ccl::{BaseType, InferVar, Lit, ProjKey, TypedExpr, TypedExprNode, ccl_utils, symbolic};

/// A CCL type annotation.
///
/// Appears on [`TypedExpr`] nodes and as the output of type inference.
///
/// The two pre-/post-inference variants divide ownership cleanly:
///
/// | Variant | Owner | Meaning | Must be eliminated by |
/// |---|---|---|---|
/// | `Hole` | Lowering | "This slot needs a type; not yet known" | End of inference (compiler bug if survives — flagged as `UnresolvedHole`) |
/// | `Infer(id)` | Type checker only | "Inference variable N from simple-sub coalesce" | End of inference for any type reachable from the program's root output (flagged as `UnresolvedInfer` by `collect_type_errors`) |
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// A primitive base type.
    Base(BaseType),
    /// A finite index range `[0, n)`, used as the domain of list types.
    ///
    /// Emitted by `lower_list_comp` to annotate the outer lambda's parameter
    /// with the exact length of the source list. `compile_ccl::extent_of` maps
    /// it directly to `Extent::UIntRange { start: 0, end: n }`.
    UIntRange(usize),
    /// A function type. When `name` is `None` it is the ordinary
    /// non-dependent arrow `domain ⇒ codomain`. When `name` is `Some(x)` it
    /// is a **Pi type** `(x: domain) ⇒ codomain`: the binder `x` is in scope
    /// in `codomain` and may be referenced by refinement predicates nested
    /// anywhere within it.
    ///
    /// Inference always populates `name` when it introduces a function type
    /// from a lambda's parameter (see `emit_lambda`); whether the codomain
    /// actually references the binder is a *property* of the resulting type,
    /// not a structural decision made up front. A `Some`-named function whose
    /// codomain does not mention the binder is observationally identical to
    /// the same function with `name: None` — the binder is only load-bearing
    /// once a nested refinement closes over it (dependent application).
    Fun {
        /// The Pi binder, if this function type is dependent. Bound in
        /// `codomain`. The derived [`PartialEq`] *does* compare it, but the
        /// α-aware comparisons that matter for dependent refinements strip it
        /// first (`without_pi_names`), so two function types equal up to
        /// renaming their Pi binder reconcile there (see the substitution
        /// machinery).
        name: Option<crate::ccl::Name>,
        /// The parameter (argument) type. Contravariant position.
        domain: Box<Type>,
        /// The result type. Covariant position; may reference `name`.
        codomain: Box<Type>,
    },
    /// An ordered product type with unnamed fields (tuple).
    Tuple(Vec<Type>),
    /// A named product type (record).
    Record(Vec<(String, Type)>),
    /// A tagged sum type — each tag has its own payload type.
    ///
    /// Tags are [`FieldKey`]s, the dual of `Record`/`Tuple` keys: `Name`
    /// for source-level `.Tag(...)` variants, `Index` for anonymous
    /// positional sums. This is the single sum representation — the
    /// formerly-separate untagged `Union` is just the all-`Index` case
    /// (`a ++ b` is `Variant([(Index(0), A), (Index(1), B)])`), so
    /// positional and named sums share one constructor, one coalesce
    /// path, and one width-subtyping rule. `Vec` order is preserved for
    /// display.
    Variant(Vec<(FieldKey, Type)>),
    /// A refinement of another type
    Refinement(Box<Type>, Refinement),
    /// Pre-inference placeholder stamped by lowering on every new node.
    ///
    /// Invariant: every `Hole` must be eliminated by the end of inference.
    /// `Hole` carries no identity — it's a structural "fill this in later"
    /// marker. The simple-sub pass replaces it either with a concrete type
    /// or with a `Type::Infer` variable. A surviving `Hole` means inference
    /// never visited the node, and is reported by `collect_type_errors` as
    /// `UnresolvedHole` (treat as a compiler bug, not a user-facing error).
    /// Created exclusively by [`TypedExpr::new`] and [`crate::ccl::TypedBinding::new_unannotated`].
    Hole,
    /// Unresolved type variable, identified by a unique [`crate::ccl::InferVarId`].
    ///
    /// Created during inference by the simple-sub pass
    /// ([`crate::ccl::infer_simple_sub`]) when coalescing a constraint
    /// variable whose bounds left it genuinely unconstrained (e.g. an
    /// identity lambda's parameter with no call-site usage).
    ///
    /// Invariant: any `Infer` reachable from the program's root output
    /// type is an *ambiguous-type* error, reported by `collect_type_errors`
    /// as `UnresolvedInfer`. `Infer` survivals are permitted only inside
    /// sub-expressions whose output type is not exercised (e.g. a top-level
    /// `f = lambda x: x` that is never applied).
    ///
    /// Carries the mutable [`InferVar`] (id + level + bounds) that the
    /// simple-sub solver constrains in place. A *coalesced* `Infer` (one
    /// surviving inference) has empty bounds and matters only for its
    /// `uid`; the solver guarantees no still-mutating variable escapes
    /// into a downstream pass.
    Infer(Rc<InferVar>),
    /// The opaque domain type of an externally-registered data source.
    ///
    /// Used as the domain in `Fun(DataSource(name), output_type)` types emitted
    /// by the source registry.  [`crate::interpreter::operator_conversion::OpConversionContext`]
    /// resolves this to a concrete `Extent::DataSourceDomain(rc)` at compilation time
    /// by looking the name up in its source-domain-extent registry.
    DataSource(String),
    // Planned:
    // Pi { param: String, param_ty: Box<Type>, body_ty: Box<Type> }
    // Refinement { base: Box<Type>, predicate: Box<Expr> }
}

/// If every tag in `tags` is an anonymous positional [`FieldKey::Index`]
/// tag (as produced by `++`/CollectionUnion and other unnamed sums),
/// return the payloads in order — recursively flattening nested
/// all-positional variants so chained `a ++ b ++ c` renders flat as
/// `A | B | C` rather than as nested `[._0: … | ._1: …]`. Returns `None`
/// for any variant containing a `Name` tag (a source-level `.Tag(...)`),
/// which is rendered with its tags shown.
///
/// Because positional (`Index`) and named (`Name`) tags are distinct
/// `FieldKey` cases, there is no ambiguity here: a user-written named tag
/// can never be mistaken for a synthetic positional one.
fn synthetic_payloads(tags: &[(FieldKey, Type)]) -> Option<Vec<Type>> {
    if tags.iter().any(|(k, _)| !matches!(k, FieldKey::Index(_))) {
        return None;
    }
    let mut out = Vec::with_capacity(tags.len());
    for (_, t) in tags {
        match t {
            Type::Variant(inner) => match synthetic_payloads(inner) {
                Some(mut flat) => out.append(&mut flat),
                None => out.push(t.clone()),
            },
            _ => out.push(t.clone()),
        }
    }
    Some(out)
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Base(b) => write!(
                f,
                "{}",
                match b {
                    BaseType::Int => "Int",
                    BaseType::UInt => "UInt",
                    BaseType::String => "String",
                    BaseType::Bool => "Bool",
                    BaseType::Unit => "Unit",
                }
            ),
            // `n == 0` means an empty range (e.g. the domain of `[]`); render
            // it as `∅` instead of computing `n - 1` and underflowing.
            Type::UIntRange(0) => write!(f, "∅"),
            Type::UIntRange(n) => write!(f, "[0, {}]", n - 1),
            Type::Fun {
                name: Some(x),
                domain,
                codomain,
            } => write!(f, "(({x}: {domain}) ⇒ {codomain})"),
            Type::Fun {
                name: None,
                domain,
                codomain,
            } => write!(f, "({domain} ⇒ {codomain})"),
            Type::Tuple(ts) => {
                let parts: Vec<_> = ts.iter().map(|t| t.to_string()).collect();
                write!(f, "({})", parts.join(", "))
            }
            Type::Record(fields) => {
                let parts: Vec<_> = fields.iter().map(|(n, t)| format!("{n}: {t}")).collect();
                write!(f, "{{{}}}", parts.join(", "))
            }
            Type::Variant(tags) => {
                // Anonymous positional variants (all tags are
                // `FieldKey::Index`, as `++`/CollectionUnion produces) are
                // rendered as a flat `A | B` join — the positional tags
                // carry no user-meaningful information. Nested
                // all-positional variants flatten recursively so
                // `a ++ b ++ c` prints as `A | B | C` rather than
                // `[._0: [._0: A | ._1: B] | ._1: C]`.
                if let Some(payloads) = synthetic_payloads(tags) {
                    let parts: Vec<_> = payloads.iter().map(|t| t.to_string()).collect();
                    write!(f, "{}", parts.join(" | "))
                } else {
                    let parts: Vec<_> = tags
                        .iter()
                        .map(|(n, t)| {
                            if matches!(t, Type::Base(BaseType::Unit)) {
                                format!(".{n}")
                            } else {
                                format!(".{n}({t})")
                            }
                        })
                        .collect();
                    write!(f, "[{}]", parts.join(" | "))
                }
            }
            Type::Refinement(t, r) => {
                write!(f, "{{{t} | {}}}", symbolic::symbolic(&r.predicate))
            }
            Type::Hole => write!(f, "_"),
            Type::Infer(var) => write!(f, "?{}", var.uid),
            Type::DataSource(name) => write!(f, "source({name})"),
        }
    }
}

impl Type {
    /// Helper for creating a non-dependent function type (`name: None`).
    pub fn fun(domain: Self, codomain: Self) -> Self {
        Type::Fun {
            name: None,
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// Helper for creating a dependent (Pi) function type `(name: domain) ⇒ codomain`.
    pub fn pi(name: impl Into<crate::ccl::Name>, domain: Self, codomain: Self) -> Self {
        Type::Fun {
            name: Some(name.into()),
            domain: Box::new(domain),
            codomain: Box::new(codomain),
        }
    }

    /// If this is a function type, return the domain type, otherwise None.
    pub fn domain(&self) -> Option<Type> {
        if let Type::Fun { domain, .. } = &self {
            Some(domain.as_ref().clone())
        } else {
            None
        }
    }

    /// If this is a function type, return the codomain type, otherwise None.
    pub fn codomain(&self) -> Option<Type> {
        if let Type::Fun { codomain, .. } = &self {
            Some(codomain.as_ref().clone())
        } else {
            None
        }
    }

    /// A structural copy with every Pi binder name erased (`Fun.name → None`).
    ///
    /// The binder is load-bearing only inside the type solver (it carries
    /// dependent-refinement correspondences); downstream passes treat function
    /// types structurally and a `Some`/`None` binder is the same arrow to them.
    /// Use this when comparing types for structural equality across a pass that
    /// does not preserve the cosmetic binder.
    ///
    /// Under the Barendregt convention the blindness needed at the remaining
    /// call sites (lambda elimination's type-preservation asserts) is exactly
    /// `Some` vs `None`: both compared types descend from one derivation, so
    /// when both carry a binder it is the *same* [`crate::ccl::Name`] (uids are preserved
    /// by every copy along the lineage). What elimination does not preserve is
    /// the binder's presence — rebuilt combinator arrows (`fun_ty_or_hole`,
    /// [`Type::fun`]) are constructed with `name: None`. If those sites ever
    /// preserve binders on rebuilt arrows, this helper can retire.
    pub fn without_pi_names(&self) -> Type {
        match self {
            Type::Fun {
                domain, codomain, ..
            } => Type::Fun {
                name: None,
                domain: Box::new(domain.without_pi_names()),
                codomain: Box::new(codomain.without_pi_names()),
            },
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| t.without_pi_names()).collect()),
            Type::Record(fs) => Type::Record(
                fs.iter()
                    .map(|(n, t)| (n.clone(), t.without_pi_names()))
                    .collect(),
            ),
            Type::Variant(tags) => Type::Variant(
                tags.iter()
                    .map(|(k, t)| (k.clone(), t.without_pi_names()))
                    .collect(),
            ),
            Type::Refinement(base, r) => {
                Type::Refinement(Box::new(base.without_pi_names()), r.clone())
            }
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::Hole
            | Type::Infer(_)
            | Type::DataSource(_) => self.clone(),
        }
    }

    /// Create a fresh [`Type::Infer`] variable for use in tests.
    ///
    /// Use this only when constructing expressions in tests that will not be
    /// run through inference (e.g. to exercise pretty-printing or symbolic
    /// output), or to provide an unannotated parameter type that inference
    /// will fill in.
    #[cfg(test)]
    pub fn infer() -> Self {
        Type::Infer(InferVar::fresh(0))
    }

    /// Invoke `f` on each direct child [`Type`] of this type.
    ///
    /// "Direct child" means a `Type` reachable through this type's value
    /// fields — the domain and codomain of a `Fun`, the elements of a
    /// `Tuple` / `Record`, the payloads of a `Variant`, and the base of a
    /// `Refinement`.
    ///
    /// Does **not** descend into the refinement *predicate* (which is a
    /// [`TypedExpr`], not a `Type`).  Callers that need to walk a
    /// refinement's predicate must handle [`Type::Refinement`] explicitly
    /// — e.g. by matching on it before calling this helper.
    pub fn walk_children(&self, mut f: impl FnMut(&Type)) {
        match self {
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::Hole
            | Type::Infer(_)
            | Type::DataSource(_) => {}
            Type::Fun {
                domain, codomain, ..
            } => {
                f(domain);
                f(codomain);
            }
            Type::Tuple(ts) => {
                for t in ts {
                    f(t);
                }
            }
            Type::Record(fields) => {
                for (_, t) in fields {
                    f(t);
                }
            }
            Type::Refinement(base, _) => f(base),
            Type::Variant(tags) => {
                for (_, t) in tags {
                    f(t);
                }
            }
        }
    }

    /// Mutable analog of [`walk_children`](Self::walk_children).
    ///
    /// Same caveats apply: does not descend into the refinement predicate.
    pub fn walk_children_mut(&mut self, mut f: impl FnMut(&mut Type)) {
        match self {
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::Hole
            | Type::Infer(_)
            | Type::DataSource(_) => {}
            Type::Fun {
                domain, codomain, ..
            } => {
                f(domain);
                f(codomain);
            }
            Type::Tuple(ts) => {
                for t in ts {
                    f(t);
                }
            }
            Type::Record(fields) => {
                for (_, t) in fields {
                    f(t);
                }
            }
            Type::Refinement(base, _) => f(base),
            Type::Variant(tags) => {
                for (_, t) in tags {
                    f(t);
                }
            }
        }
    }

    /// Fold `f` left-to-right over the direct child [`Type`]s, starting
    /// from `init`.  Mirrors [`TypedExpr::fold_children`].
    pub fn fold_children<T>(&self, init: T, mut f: impl FnMut(T, &Type) -> T) -> T {
        let mut acc = Some(init);
        self.walk_children(|t| {
            let v = acc
                .take()
                .expect("Type::fold_children: closure invoked re-entrantly");
            acc = Some(f(v, t));
        });
        acc.expect("Type::fold_children: walk_children dropped accumulator")
    }
}

/// Represents a type refinement: a base type narrowed by a boolean predicate.
///
/// The refinement *is a binding form*. Rather than carry a per-refinement
/// binder name, every refinement implicitly binds the single reserved
/// [`REFINEMENT_BINDER`], which ranges over the refined base type and is free
/// in [`predicate`]. A predicate references its own element through that one
/// name; nested refinements simply shadow it, which is the correct lexical
/// scoping (a predicate never refers to an *outer* refinement's element, only
/// to its own plus enclosing `Fun`-binders, which have their own distinct
/// names). A fixed binder means refinement equality is plain structural
/// equality of the bare predicate — no α-renaming needed.
///
/// [`predicate`]: Refinement::predicate
#[derive(Debug, Clone)]
pub struct Refinement {
    /// A **bare**, *immutable* boolean expression (not a lambda) in which
    /// [`REFINEMENT_BINDER`] is free. Compiled as an element-wise loop join
    /// when its type is iterated. A rewrite produces a *new* term (structural
    /// `Rc` sharing keeps that cheap); nothing mutates a predicate in place,
    /// so a predicate that flows around is never resolved out from under a
    /// hash key.
    pub predicate: Rc<TypedExpr>,
}

/// Pointer identity of a refinement's predicate term.
///
/// Traversals that descend into refinement predicates use this as a
/// visited-set key to avoid re-walking a predicate term shared by `Rc` across
/// several occurrences (the term graph is a DAG — immutable `Rc<TypedExpr>`
/// cannot form a cycle). It identifies *this very `Rc`*, unlike
/// [`Refinement`]'s structural `PartialEq`, and costs nothing to compute.
/// Only meaningful while the `Rc` is alive — hold it no longer than a
/// traversal over a tree that owns the `Rc`s (a freed address can be reused).
pub type PredicateId = *const TypedExpr;

/// The single reserved binder every [`Refinement`] implicitly introduces. It
/// is free in a refinement's predicate and ranges over the refined base type.
/// Disjoint from user identifiers by construction (lowering never produces
/// it); nested refinements share it and shadow positionally.
pub const REFINEMENT_BINDER: &str = "__elem";

impl Refinement {
    /// The [`PredicateId`] of this refinement's predicate term.
    pub fn predicate_id(&self) -> PredicateId {
        Rc::as_ptr(&self.predicate)
    }
}

impl PartialEq for Refinement {
    /// Two refinements match iff they carry structurally equal predicate
    /// *terms* ([`eq_refinement_predicate`]). Structural equality makes
    /// refinement-bearing `Type`/`Expr` equality agnostic to *where* a
    /// predicate was constructed, so a `{D | p}` that join planning
    /// re-minted at a marker (`make_iterate` / `make_restrict` /
    /// `refine_with`) compares equal to its structural twin — which is what
    /// lets the post-planning `typecheck` chain the re-minted witnesses. This
    /// is *equality*, not implication — `{T | p}` and `{T | q}` with
    /// structurally-distinct predicates remain unequal.
    ///
    /// The comparison is **type-blind**: a predicate's embedded `Type`s are
    /// inference metadata, so copies of one predicate — freshened for a
    /// specialization, rebuilt by a discharge, pinned at different use types —
    /// denote the same refinement while their type slots differ. Comparing the
    /// term and skipping the types keeps those copies equal, exactly as the
    /// [`Hash`](std::hash::Hash) impl keeps them hash-equal.
    ///
    /// Every refinement binds the same reserved [`REFINEMENT_BINDER`], so
    /// equality is plain structural equality of the bare predicate — the
    /// binder appears identically on both sides, with no α-renaming to do.
    ///
    /// Pointer-equal predicates short-circuit: a refinement that merely flows
    /// around (a vacuous substitution) keeps sharing its predicate `Rc`, so
    /// the common case never compares structure.
    fn eq(&self, other: &Self) -> bool {
        if Rc::ptr_eq(&self.predicate, &other.predicate) {
            return true;
        }

        eq_refinement_predicate(&self.predicate, &other.predicate)
    }
}

impl Eq for Refinement {}

/// The **"same-restriction" relation** on refinement predicate terms: the
/// equality that backs [`Refinement`] and the counterpart of
/// [`hash_refinement_predicate`]. It is *deliberately* type-blind — it compares
/// node shape, scalar leaves (operators, builtins, literals, names, tags),
/// binder names, and child `Expr`s pairwise, but never the embedded `Type`s
/// (`ty` slots, annotations, binding types). Those are inference metadata, not
/// part of what restriction a refinement imposes, and copies of one predicate
/// legitimately differ in them (freshened for a specialization, rebuilt by a
/// discharge, pinned at different use types). So this is a structural relation
/// chosen for its context, not an approximation of a finer one — there is no
/// plan to make it a derived `==` (which would wrongly compare those slots).
///
/// Binder names compare by equality, which coincides with α-equivalence under
/// the Barendregt convention (uniquified, globally-distinct binders; copies
/// preserve uids). Should a future pass need to compare predicates whose bound
/// binders were independently minted, this is the site to make α-aware (thread
/// a binder correspondence) rather than chase global name determinism.
///
/// One type-anchored slot **is** compared: a [`TypedExprNode::Cast`]'s
/// `target` carries the cast's domain-refinement *predicate term*
/// ([`ccl_utils::cast_target_refinement`]) — a semantic filter, not inference
/// metadata. Two predicates that each contain a cast and differ only in the
/// nested filter (e.g. embedded comprehensions filtering `> 0` vs `< 0`)
/// denote different refinements; conflating them would let witness-deficit
/// matching accept an unsatisfied demand and refinement dedup drop a runtime
/// `Restrict`. The target's *base* types are still skipped. The recursion
/// terminates on tree shape alone: a predicate is an immutable `Rc<TypedExpr>`,
/// which is acyclic, so cast targets cannot cycle back into a term under
/// comparison — no coinduction guard is needed.
///
/// Everything this distinguishes beyond [`hash_refinement_predicate`]'s
/// stream (binder names, `Source` names, record field names, pattern tags,
/// cast-target predicates) makes eq finer than hash, preserving the
/// `Eq`/`Hash` contract.
pub(crate) fn eq_refinement_predicate(a: &TypedExpr, b: &TypedExpr) -> bool {
    eq_refinement_predicate_go(a, b)
}

/// Compare two cast targets' domain-refinement predicates term-wise (see
/// [`eq_refinement_predicate`]). Pointer-equal predicates short-circuit;
/// otherwise the comparison recurses structurally (acyclic terms, so it
/// terminates without a cycle guard).
fn eq_cast_target_predicates(t1: &Type, t2: &Type) -> bool {
    match (
        ccl_utils::cast_target_refinement(t1),
        ccl_utils::cast_target_refinement(t2),
    ) {
        (None, None) => true,
        (Some(r1), Some(r2)) => {
            if Rc::ptr_eq(&r1.predicate, &r2.predicate) {
                return true;
            }
            eq_refinement_predicate_go(&r1.predicate, &r2.predicate)
        }
        _ => false,
    }
}

/// Recursive worker for [`eq_refinement_predicate`].
fn eq_refinement_predicate_go(a: &TypedExpr, b: &TypedExpr) -> bool {
    use TypedExprNode as N;
    fn all_eq(xs: &[TypedExpr], ys: &[TypedExpr]) -> bool {
        xs.len() == ys.len()
            && xs
                .iter()
                .zip(ys)
                .all(|(x, y)| eq_refinement_predicate_go(x, y))
    }
    match (&a.node, &b.node) {
        (N::Lit(x), N::Lit(y)) => x == y,
        (N::Var(x), N::Var(y)) => x == y,
        (N::Builtin(x), N::Builtin(y)) => x == y,
        (N::Proj(x), N::Proj(y)) => x == y,
        (N::Source(x), N::Source(y)) => x == y,
        (N::Defer, N::Defer) | (N::Error, N::Error) => true,
        (
            N::Apply {
                function: f1,
                argument: a1,
            },
            N::Apply {
                function: f2,
                argument: a2,
            },
        ) => eq_refinement_predicate_go(f1, f2) && eq_refinement_predicate_go(a1, a2),
        (
            N::Cast {
                value: v1,
                target: t1,
            },
            N::Cast {
                value: v2,
                target: t2,
            },
        ) => eq_refinement_predicate_go(v1, v2) && eq_cast_target_predicates(t1, t2),
        (
            N::BinOp {
                left: l1,
                op: o1,
                right: r1,
            },
            N::BinOp {
                left: l2,
                op: o2,
                right: r2,
            },
        ) => o1 == o2 && eq_refinement_predicate_go(l1, l2) && eq_refinement_predicate_go(r1, r2),
        (N::UnaryOp(k1, e1), N::UnaryOp(k2, e2)) => k1 == k2 && eq_refinement_predicate_go(e1, e2),
        (
            N::Lambda {
                param: p1,
                body: b1,
                ..
            },
            N::Lambda {
                param: p2,
                body: b2,
                ..
            },
        ) => p1.name == p2.name && eq_refinement_predicate_go(b1, b2),
        (
            N::Aggregate {
                input: i1,
                kind: k1,
            },
            N::Aggregate {
                input: i2,
                kind: k2,
            },
        ) => k1 == k2 && eq_refinement_predicate_go(i1, i2),
        (
            N::Let {
                binding: bd1,
                bound_expr: e1,
                body: b1,
            },
            N::Let {
                binding: bd2,
                bound_expr: e2,
                body: b2,
            },
        ) => {
            bd1.name == bd2.name
                && eq_refinement_predicate_go(e1, e2)
                && eq_refinement_predicate_go(b1, b2)
        }
        (N::List(x), N::List(y))
        | (N::Tuple(x), N::Tuple(y))
        | (N::Compose(x), N::Compose(y))
        | (N::CollectionUnion(x), N::CollectionUnion(y)) => all_eq(x, y),
        (
            N::Case {
                scrutinee: s1,
                branches: br1,
            },
            N::Case {
                scrutinee: s2,
                branches: br2,
            },
        ) => {
            let scrutinee_eq = match (s1, s2) {
                (None, None) => true,
                (Some(x), Some(y)) => eq_refinement_predicate_go(x, y),
                _ => false,
            };
            scrutinee_eq
                && br1.len() == br2.len()
                && br1.iter().zip(br2).all(|(x, y)| {
                    let pattern_eq = match (&x.pattern, &y.pattern) {
                        (None, None) => true,
                        (Some(p), Some(q)) => p.tag == q.tag && p.binding.name == q.binding.name,
                        _ => false,
                    };
                    pattern_eq
                        && eq_refinement_predicate_go(&x.guard, &y.guard)
                        && eq_refinement_predicate_go(&x.body, &y.body)
                })
        }
        (
            N::VariantCtor {
                tag: t1,
                payload: p1,
            },
            N::VariantCtor {
                tag: t2,
                payload: p2,
            },
        ) => t1 == t2 && eq_refinement_predicate_go(p1, p2),
        (N::Record(f1), N::Record(f2)) => {
            f1.len() == f2.len()
                && f1
                    .iter()
                    .zip(f2)
                    .all(|((n1, e1), (n2, e2))| n1 == n2 && eq_refinement_predicate_go(e1, e2))
        }
        (
            N::Loop {
                params: p1,
                init_args: i1,
                source: s1,
                loop_body: b1,
            },
            N::Loop {
                params: p2,
                init_args: i2,
                source: s2,
                loop_body: b2,
            },
        ) => {
            p1.len() == p2.len()
                && p1.iter().zip(p2).all(|(x, y)| x.name == y.name)
                && all_eq(i1, i2)
                && eq_refinement_predicate_go(s1, s2)
                && eq_refinement_predicate_go(b1, b2)
        }
        (N::ExprStmt { expr: e1, body: b1 }, N::ExprStmt { expr: e2, body: b2 }) => {
            eq_refinement_predicate_go(e1, e2) && eq_refinement_predicate_go(b1, b2)
        }
        (
            N::Feed {
                name: n1,
                value: v1,
            },
            N::Feed {
                name: n2,
                value: v2,
            },
        )
        | (
            N::Define {
                name: n1,
                value: v1,
            },
            N::Define {
                name: n2,
                value: v2,
            },
        ) => n1 == n2 && eq_refinement_predicate_go(v1, v2),
        _ => false,
    }
}

/// Structural hash of a refinement predicate, the hashing counterpart of
/// [`eq_refinement_predicate`]: it hashes the predicate's node discriminant
/// and scalar leaves (operators, builtins, literals, names) and recurses
/// into child `Expr`s, but never hashes the embedded `Type`s. Skipping
/// types keeps the hash stable while inference resolves the predicate's
/// type slots in place, and keeps it non-recursive through refinements (so
/// it always terminates and adds no extra borrows).
fn hash_refinement_predicate<H: std::hash::Hasher>(e: &TypedExpr, state: &mut H) {
    use std::hash::Hash;
    std::mem::discriminant(&e.node).hash(state);
    match &e.node {
        TypedExprNode::Lit(Lit::Int(n)) => n.hash(state),
        TypedExprNode::Lit(Lit::String(s)) => s.hash(state),
        TypedExprNode::Lit(Lit::Bool(b)) => b.hash(state),
        TypedExprNode::Lit(Lit::Unit) => {}
        TypedExprNode::Var(name) => name.hash(state),
        TypedExprNode::Builtin(b) => b.hash(state),
        TypedExprNode::BinOp { op, .. } => op.hash(state),
        TypedExprNode::UnaryOp(kind, _) => kind.hash(state),
        TypedExprNode::Aggregate { kind, .. } => kind.hash(state),
        TypedExprNode::VariantCtor { tag, .. } => tag.hash(state),
        TypedExprNode::Proj(ProjKey::Index(i)) => i.hash(state),
        TypedExprNode::Proj(ProjKey::Field(f)) => f.hash(state),
        _ => {}
    }
    e.walk_children(|child| hash_refinement_predicate(child, state));
}

impl std::hash::Hash for Refinement {
    /// Hashes the predicate's *structure* (refined `Type`s are hashed as
    /// `ConstrainCache` keys). [`hash_refinement_predicate`] hashes the
    /// predicate's node shape and scalar leaves but skips embedded `Type`s,
    /// so the hash is stable even though a refinement's twin may carry
    /// differently-resolved type slots; `==` ([`eq_refinement_predicate`]) is
    /// the matching type-blind relation, finer only by leaves the hash skips,
    /// which keeps the `Eq`/`Hash` contract. The predicate is immutable, so a
    /// `Type` used as a `ConstrainCache` key never re-hashes differently.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        hash_refinement_predicate(&self.predicate, state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{BinOpKind, CompareKind};

    /// Two predicates that each contain a [`TypedExprNode::Cast`] and differ
    /// only in the *target's* domain-refinement predicate denote different
    /// refinements: the nested filter is semantic, not inference metadata, so
    /// [`eq_refinement_predicate`] must compare cast targets rather than skip
    /// them as type slots (conflating them could drop a runtime `Restrict`).
    #[test]
    fn refinement_eq_distinguishes_cast_target_predicates() {
        let filter = |op: CompareKind| {
            TypedExpr::binop(
                TypedExpr::var("x"),
                BinOpKind::Compare(op),
                TypedExpr::lit(Lit::Int(0)),
            )
        };
        let cast_pred = |op: CompareKind| {
            TypedExpr::cast(
                TypedExpr::var("xs"),
                ccl_utils::refined_fn_type(Type::Hole, filter(op), Type::Hole),
            )
        };
        let refinement = |pred: TypedExpr| Refinement {
            predicate: Rc::new(pred),
        };

        let gt = refinement(cast_pred(CompareKind::Greater));
        let gt_twin = refinement(cast_pred(CompareKind::Greater));
        let lt = refinement(cast_pred(CompareKind::Less));

        assert_eq!(
            gt, gt_twin,
            "casts with structurally equal target predicates are one refinement"
        );
        assert_ne!(
            gt, lt,
            "casts differing only in the target's nested filter are distinct refinements"
        );
    }
}
