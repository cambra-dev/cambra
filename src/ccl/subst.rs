//! Capture-avoiding substitutions over term binders — the context-morphism
//! machinery for dependent refinements (Pi types).
//!
//! This is the load-bearing distinction from the design proposal
//! (`brainstorm/2026-06-02-dependent-refinements-via-pi-types.md`, §3.5) and its
//! executable model
//! (`brainstorm/2026-06-02-dependent-refinements-substitution-prototype.rs`):
//!
//! * A **context** annotates a type or metavariable — the binders it may
//!   legitimately mention. It is a *checking* device only (free vars ⊆ context);
//!   it transforms nothing. See [`well_formed`].
//! * A **substitution** ([`Subst`]) is a context morphism `Γ_src → Γ_dst` that
//!   rides on a constraint edge and *rewrites* a term/type as it propagates.
//!   Two flavours:
//!     - a **rename** `[k ↦ x]` (a bijection on binders) is **invertible**;
//!     - a **discharge** `[x ↦ arg]` (plug an argument in for a binder) is
//!       **one-way** (no inverse).
//!
//! A [`Subst`] maps *term* binders — `TypedExprNode::Var(name)` references — to
//! replacement [`TypedExpr`]s. It is deliberately **not** a type-variable
//! substitution: it never rewrites a [`Type::Infer`] / type slot (those are
//! relabelled by freshening, a separate mechanism). Applying a substitution
//! descends into refinement *predicates* (which are terms) and shadows the
//! binder of any enclosing lambda / `let` / Pi it passes under, α-renaming to
//! avoid capture.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::ccl::ccl_utils::{is_free, is_free_in_value};
use crate::ccl::{Branch, PredicateCellId, REFINEMENT_BINDER, Type, TypedExpr, TypedExprNode};

/// A term binder name.
pub type Binder = String;

/// A simultaneous substitution `{binder ↦ term, …}`. An absent binder maps to
/// itself (the identity). The empty map is [`Subst::id`].
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Subst(BTreeMap<Binder, TypedExpr>);

/// Monotonic source of fresh binder suffixes for capture-avoiding α-renaming.
/// Renaming is rare (only when a substitution's range mentions a binder it is
/// passing under), so a process-global counter is fine — uniqueness is all that
/// matters, not determinism across runs.
static FRESH_BINDER: AtomicU64 = AtomicU64::new(0);

pub fn fresh_binder(base: &str) -> Binder {
    let n = FRESH_BINDER.fetch_add(1, Ordering::Relaxed);
    format!("{base}#{n}")
}

impl Subst {
    /// The identity substitution — a perfect no-op. `apply_*` on it returns the
    /// input structurally unchanged.
    pub fn id() -> Self {
        Subst(BTreeMap::new())
    }

    /// Is this the identity? Callers fast-path the common (non-dependent) case
    /// on this so that ordinary code paths are byte-identical to a world
    /// without substitutions.
    pub fn is_id(&self) -> bool {
        self.0.is_empty()
    }

    /// A rename `[from ↦ to]` — a bijection on binders, hence invertible.
    pub fn rename(from: &str, to: &str) -> Self {
        let mut m = BTreeMap::new();
        m.insert(from.to_string(), TypedExpr::var(to));
        Subst(m)
    }

    /// A discharge `[binder ↦ term]` — plug `term` in for `binder`. One-way.
    pub fn discharge(binder: &str, term: TypedExpr) -> Self {
        let mut m = BTreeMap::new();
        m.insert(binder.to_string(), term);
        Subst(m)
    }

    /// The binders this substitution acts on (its source domain).
    pub fn binders(&self) -> impl Iterator<Item = &Binder> {
        self.0.keys()
    }

    /// True if any binder of `self`'s *range* (the replacement terms) contains a
    /// free `name` — i.e. substituting under a binder `name` would capture.
    fn range_mentions(&self, name: &str) -> bool {
        self.0.values().any(|t| is_free(name, t))
    }

    /// Compose two morphisms: `then(a, b)` is "apply `a`, then `b`" — the
    /// function `(a;b)(t) = b(a(t))`. The composite records its action on every
    /// binder either map touches (so intermediate correspondence binders are
    /// faithfully carried; design §3.6 "force before combine").
    pub fn then(a: &Subst, b: &Subst) -> Subst {
        if a.is_id() {
            return b.clone();
        }
        if b.is_id() {
            return a.clone();
        }
        let mut keys: BTreeSet<Binder> = a.0.keys().cloned().collect();
        keys.extend(b.0.keys().cloned());
        let mut m = BTreeMap::new();
        for k in keys {
            let from_a =
                a.0.get(&k)
                    .cloned()
                    .unwrap_or_else(|| TypedExpr::var(k.clone()));
            let composed = b.apply_expr(&from_a);
            // Drop entries that resolve back to the identity on `k`.
            if !is_var_named(&composed, &k) {
                m.insert(k, composed);
            }
        }
        Subst(m)
    }

    /// Invert, requiring this be a rename (identity inverts to identity). Used
    /// on the contravariant domain edge and when recording an upper bound,
    /// where the discipline guarantees only renames ride the edge — a discharge
    /// here is a solver bug, so this panics loudly rather than silently
    /// corrupting the edge.
    pub fn invert_rename(&self) -> Subst {
        self.invert()
            .expect("correspondence / upper edge must be a rename (invertible)")
    }

    /// Invert if possible, otherwise the identity. Used when recording the
    /// *reverse* of a constraint edge whose forward morphism may be a discharge
    /// (a non-invertible projection). A discharge `[x ↦ arg]` only rewrites
    /// predicate binders, which `constrain` treats opaquely, and the bound
    /// being recorded on the reverse edge lives in the *post*-discharge context
    /// — it never mentions the discharged binder — so the discharge's action on
    /// it is the identity. Falling back to `id` is therefore exact for that
    /// bound (it is *not* a general inverse of the discharge).
    pub fn invert_or_id(&self) -> Subst {
        self.invert().unwrap_or_else(Subst::id)
    }

    /// Extend this substitution with a fresh binder correspondence `k ↦ x`
    /// (the Pi-vs-Pi binder alignment derived in the codomain edge). `k` is a
    /// newly-scoped binder, so this is an insert, not a composition.
    pub fn extended_rename(&self, k: &str, x: &str) -> Subst {
        let mut m = self.0.clone();
        m.insert(k.to_string(), TypedExpr::var(x));
        Subst(m)
    }

    /// Invert a **rename** (every range term is a distinct bare variable).
    /// Returns `None` if any frame is a discharge or the map is not injective —
    /// the discipline that keeps only renames on bidirectional edges (§3.6).
    pub fn invert(&self) -> Option<Subst> {
        let mut m = BTreeMap::new();
        let mut seen = BTreeSet::new();
        for (k, v) in &self.0 {
            let to = as_var_name(v)?;
            if !seen.insert(to.to_string()) {
                return None; // not injective
            }
            m.insert(to.to_string(), TypedExpr::var(k.clone()));
        }
        Some(Subst(m))
    }

    /// Apply this substitution to a **term**. Capture-avoiding: it shadows the
    /// binder of any lambda / `let` / loop / match-arm it descends under and
    /// α-renames when its range would otherwise capture. Type slots
    /// (`expr.ty`) are *not* touched — a term substitution never rewrites a
    /// type variable, and an occurrence of a substituted binder buried inside
    /// a type slot's refinement predicate is **out of contract**: it is
    /// neither rewritten nor counted by the freeness checks below (which use
    /// the value-only [`is_free_in_value`], agreeing with the rewriter). The
    /// end-of-inference scope-validity check (`check_scope_valid`, design
    /// §6.2) is what guards a type-slot occurrence left dangling — it runs
    /// unconditionally, surfacing the residual as an `InferError` in release
    /// builds too.
    pub fn apply_expr(&self, e: &TypedExpr) -> TypedExpr {
        if self.is_id() {
            return e.clone();
        }
        // No-op short-circuit: if none of the substituted binders occur free in
        // `e`'s value, the substitution does nothing here. This is not merely
        // an optimization — without it, descending under a binder whose name
        // collides with the substitution's *range* (but where the substitution
        // never actually acts) would trigger a spurious capture-avoiding
        // α-rename, copying the term with a fresh binder for no reason. The
        // common case (a vacuous discharge `[x ↦ arg]` from a non-dependent
        // application, `x` not occurring in `e`) takes this path. Value-only:
        // a binder free solely in a type-slot predicate would otherwise fail
        // this check, walk the term, and change nothing — the type slot is
        // out of contract (see above).
        if !self.0.keys().any(|k| is_free_in_value(k, e)) {
            return e.clone();
        }
        self.apply_expr_inner(e)
    }

    fn apply_expr_inner(&self, e: &TypedExpr) -> TypedExpr {
        use TypedExprNode::*;
        let node = match &e.node {
            Var(n) => match self.0.get(n) {
                // The replacement carries its own type/annotation, so return it
                // wholesale rather than rebuilding `e`.
                Some(repl) => return repl.clone(),
                None => Var(n.clone()),
            },

            Lambda { param, body } => {
                // Domain refinements ride the param's *type* (a
                // `Type::Refinement`); those predicates are substituted by
                // `apply_type`, not here.
                let (param_name, inner) = self.under_binder(&param.name, body);
                let body = Box::new(inner.apply_expr(body));
                let mut param = param.clone();
                param.name = param_name;
                Lambda { param, body }
            }

            Let {
                binding,
                bound_expr,
                body,
            } => {
                let bound_expr = Box::new(self.apply_expr(bound_expr));
                let (bind_name, inner) = self.under_binder(&binding.name, body);
                let body = Box::new(inner.apply_expr(body));
                let mut binding = binding.clone();
                binding.name = bind_name;
                Let {
                    binding,
                    bound_expr,
                    body,
                }
            }

            Loop {
                params,
                init_args,
                source,
                loop_body,
            } => {
                // `init_args` / `source` sit outside the loop-param scope.
                let init_args = init_args.iter().map(|a| self.apply_expr(a)).collect();
                let source = Box::new(self.apply_expr(source));
                // Shadow every loop param inside the body.
                let inner = params.iter().fold(self.clone(), |s, p| s.shadow(&p.name));
                let loop_body = Box::new(inner.apply_expr(loop_body));
                Loop {
                    params: params.clone(),
                    init_args,
                    source,
                    loop_body,
                }
            }

            Case {
                scrutinee,
                branches,
            } => {
                let scrutinee = scrutinee.as_ref().map(|s| Box::new(self.apply_expr(s)));
                let branches = branches
                    .iter()
                    .map(|b| {
                        // A structural pattern binds its payload name inside the
                        // branch's guard and body.
                        let inner = match &b.pattern {
                            Some(p) => self.shadow(&p.binding.name),
                            None => self.clone(),
                        };
                        Branch {
                            pattern: b.pattern.clone(),
                            guard: inner.apply_expr(&b.guard),
                            body: inner.apply_expr(&b.body),
                        }
                    })
                    .collect();
                Case {
                    scrutinee,
                    branches,
                }
            }

            // No binders introduced: recurse structurally into child terms.
            _ => {
                let mut child = e.clone();
                child.map_children(|c| self.apply_expr(&c));
                return child;
            }
        };
        TypedExpr {
            node,
            ty: e.ty.clone(),
            user_annotation: e.user_annotation.clone(),
        }
    }

    /// Restrict this substitution so it does not act on `binder`, and α-rename
    /// `binder` to a fresh name if the (restricted) range would capture it.
    /// Returns the (possibly fresh) binder name to install and the substitution
    /// to use inside its scope.
    fn under_binder(&self, binder: &str, body: &TypedExpr) -> (Binder, Subst) {
        let restricted = self.shadow(binder);
        // If no substituted binder occurs free in the body, the substitution is
        // inert there — return the identity so the body is left untouched and no
        // spurious capture-avoiding rename is triggered.
        if !restricted.0.keys().any(|k| is_free_in_value(k, body)) {
            return (binder.to_string(), Subst::id());
        }
        if restricted.range_mentions(binder) {
            let fresh = fresh_binder(binder);
            // Compose the α-rename into the restricted substitution so the body
            // both renames the binder and applies the outer map.
            let renamed = Subst::then(&Subst::rename(binder, &fresh), &restricted);
            (fresh, renamed)
        } else {
            (binder.to_string(), restricted)
        }
    }

    /// Rewrite a refinement's predicate by this substitution. A no-op clone
    /// under the identity.
    ///
    /// Refinements compare by *structural predicate equality*, so the same
    /// discharge applied in two places — the solver's coalesce walk and the
    /// post-inference check's reconstruction — rewrites the predicate to the
    /// same term and the resulting refinements compare equal, letting the
    /// check's reconcile pass. Two *different* discharges of one polymorphic
    /// refinement — `g(0)` vs `g(1)` — rewrite to structurally distinct
    /// predicates and stay distinguished for the same reason (O4).
    pub fn force_refinement(&self, r: &crate::ccl::Refinement) -> crate::ccl::Refinement {
        if self.is_id() {
            return r.clone();
        }
        // The refinement is a binding form for the implicit REFINEMENT_BINDER,
        // so the substitution acts *under* that binder: shadow it (drop it from
        // the domain) before rewriting the predicate. Unlike an ordinary binder
        // it is never α-renamed — every refinement shares the one global name,
        // and a predicate only ever references its *own* element through it, so
        // there is no capture to avoid.
        let restricted = self.shadow(REFINEMENT_BINDER);
        let new_pred = {
            let pred = r.predicate.borrow();
            // Vacuous here (no substituted binder occurs free in the
            // predicate's *value* — type-slot occurrences are out of
            // contract, see `apply_expr`): keep the original refinement,
            // *sharing its predicate cell*. Downstream passes rewrite
            // predicates in place through that `Rc` (e.g. planning compiles
            // the predicate to point-free when its type is iterated);
            // re-celling on a vacuous substitution would split the copies so
            // one side misses the rewrite and the structural comparison breaks.
            if !restricted.0.keys().any(|k| is_free_in_value(k, &pred)) {
                return r.clone();
            }
            restricted.apply_expr(&pred)
        };
        // Scope-validity (design §6.2): a discharged binder must not survive in
        // the rewritten predicate's value — once `[x ↦ arg]` fires, no free `x`
        // may remain, or a downstream pass would observe a dangling reference.
        // (A rename `[k ↦ x]` maps its binder to a bare variable; only
        // non-variable range terms — discharges — are checked, since a rename
        // legitimately *introduces* its target. Value-only, agreeing with what
        // `apply_expr` rewrites: a binder buried in a sub-expression's
        // type-slot predicate is out of the substitution contract and would
        // fire this spuriously on a correct program.) In a correct
        // implementation this never fires; it is the debug-build fast-path
        // regression guard for substitution-descent bugs — the release-build
        // guard is the unconditional end-of-inference scope-validity check
        // (`check_scope_valid`).
        #[cfg(debug_assertions)]
        for (b, t) in &self.0 {
            if !matches!(t.node, TypedExprNode::Var(_)) {
                debug_assert!(
                    !is_free_in_value(b, &new_pred),
                    "discharged binder `{b}` still free after substitution into predicate",
                );
            }
        }
        let mut r2 = r.clone();
        r2.predicate = std::rc::Rc::new(std::cell::RefCell::new(new_pred));
        r2
    }

    /// This substitution with `binder` removed from its source domain (the
    /// binder shadows the outer mapping inside its scope).
    pub fn shadow(&self, binder: &str) -> Subst {
        if !self.0.contains_key(binder) {
            return self.clone();
        }
        let mut m = self.0.clone();
        m.remove(binder);
        Subst(m)
    }

    /// Apply this substitution to a **type**, rewriting the term binders that
    /// appear inside refinement predicates. Descends into `Fun` codomains
    /// (shadowing the Pi binder, α-renaming to avoid capture) and refinement
    /// predicates. Leaves atoms and type variables untouched — a term
    /// substitution never rewrites a type slot.
    pub fn apply_type(&self, ty: &Type) -> Type {
        if self.is_id() {
            return ty.clone();
        }
        self.apply_type_inner(ty)
    }

    fn apply_type_inner(&self, ty: &Type) -> Type {
        match ty {
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::DataSource(_)
            | Type::Hole
            | Type::Infer(_) => ty.clone(),

            Type::Fun {
                name: None,
                domain,
                codomain,
            } => Type::Fun {
                name: None,
                domain: Box::new(self.apply_type(domain)),
                codomain: Box::new(self.apply_type(codomain)),
            },

            Type::Fun {
                name: Some(b),
                domain,
                codomain,
            } => {
                let domain = Box::new(self.apply_type(domain));
                let (b2, inner) = self.under_binder_ty(b, codomain);
                Type::Fun {
                    name: Some(b2),
                    domain,
                    codomain: Box::new(inner),
                }
            }

            Type::Refinement(base, r) => {
                // The refinement implicitly binds REFINEMENT_BINDER in its bare
                // predicate; `force_refinement` shadows it before rewriting.
                // Substituting the predicate changes its meaning, so it mints a
                // fresh refinement identity rather than aliasing the original.
                Type::Refinement(Box::new(self.apply_type(base)), self.force_refinement(r))
            }

            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|t| self.apply_type(t)).collect()),
            Type::Record(fs) => Type::Record(
                fs.iter()
                    .map(|(n, t)| (n.clone(), self.apply_type(t)))
                    .collect(),
            ),
            Type::Variant(tags) => Type::Variant(
                tags.iter()
                    .map(|(k, t)| (k.clone(), self.apply_type(t)))
                    .collect(),
            ),
        }
    }

    /// `Fun`-codomain analogue of [`under_binder`](Self::under_binder): shadow
    /// the Pi binder in `codomain`, α-renaming it if the range would capture.
    fn under_binder_ty(&self, binder: &str, codomain: &Type) -> (Binder, Type) {
        let restricted = self.shadow(binder);
        if restricted.range_mentions(binder) {
            let fresh = fresh_binder(binder);
            let renamed = Subst::rename(binder, &fresh).apply_type(codomain);
            (fresh, restricted.apply_type(&renamed))
        } else {
            (binder.to_string(), restricted.apply_type(codomain))
        }
    }
}

/// Is `e` exactly the variable `name` (a bare `Var(name)`)?
fn is_var_named(e: &TypedExpr, name: &str) -> bool {
    matches!(&e.node, TypedExprNode::Var(n) if n == name)
}

/// If `e` is a bare variable reference, its name.
fn as_var_name(e: &TypedExpr) -> Option<&str> {
    match &e.node {
        TypedExprNode::Var(n) => Some(n.as_str()),
        _ => None,
    }
}

// ---- contexts: the *checking* device (free vars ⊆ context) ----

/// Collect the free term-variable names of `ty` — the term binders its
/// refinement predicates reference, minus any bound by an enclosing Pi binder
/// or by a binder inside the predicates themselves.
///
/// One scope-aware accumulating walk: it threads the set of in-scope binders
/// (so it subtracts shadowing binders as it descends) and a visited-set of
/// [`PredicateCellId`]s (so self-referential predicate type slots terminate),
/// gathering every free variable in a single pass. This is the accumulating
/// dual of [`crate::ccl::ccl_utils::count_free`]'s by-name query — O(n) in the
/// type/predicate size, where the old "collect every name, then re-run a
/// by-name occurrence walk per name" was O(n²).
pub fn type_free_vars(ty: &Type) -> BTreeSet<Binder> {
    let mut out = BTreeSet::new();
    let mut bound = BTreeSet::new();
    let mut visited = BTreeSet::new();
    collect_type_fv(ty, &mut bound, &mut visited, &mut out);
    out
}

/// Insert each of `names` into `bound` for the duration of `f`, restoring the
/// set afterward. Only names that were *newly* inserted are removed, so a
/// binder that shadows an already-in-scope name of the same spelling does not
/// spuriously un-bind the outer one on the way back up.
fn with_binders<R>(
    bound: &mut BTreeSet<Binder>,
    names: impl IntoIterator<Item = Binder>,
    f: impl FnOnce(&mut BTreeSet<Binder>) -> R,
) -> R {
    let added: Vec<Binder> = names
        .into_iter()
        .filter(|n| bound.insert(n.clone()))
        .collect();
    let r = f(bound);
    for n in added {
        bound.remove(&n);
    }
    r
}

fn collect_type_fv(
    ty: &Type,
    bound: &mut BTreeSet<Binder>,
    visited: &mut BTreeSet<PredicateCellId>,
    out: &mut BTreeSet<Binder>,
) {
    match ty {
        Type::Base(_) | Type::UIntRange(_) | Type::DataSource(_) | Type::Hole | Type::Infer(_) => {}
        Type::Fun {
            name,
            domain,
            codomain,
        } => {
            collect_type_fv(domain, bound, visited, out);
            // A `Some` name is the Pi binder, bound in the codomain.
            with_binders(bound, name.clone(), |bnd| {
                collect_type_fv(codomain, bnd, visited, out)
            });
        }
        Type::Refinement(base, r) => {
            // Walk each refinement's predicate at most once (cycle guard). The
            // refinement binds the implicit REFINEMENT_BINDER over `base`, so it
            // is bound — not free — inside the predicate.
            if visited.insert(r.cell_id())
                && let Ok(pred) = r.predicate.try_borrow()
            {
                with_binders(bound, [REFINEMENT_BINDER.to_string()], |bnd| {
                    collect_expr_fv(&pred, bnd, visited, out)
                });
            }
            collect_type_fv(base, bound, visited, out);
        }
        Type::Tuple(ts) => ts
            .iter()
            .for_each(|t| collect_type_fv(t, bound, visited, out)),
        Type::Record(fs) => fs
            .iter()
            .for_each(|(_, t)| collect_type_fv(t, bound, visited, out)),
        Type::Variant(tags) => tags
            .iter()
            .for_each(|(_, t)| collect_type_fv(t, bound, visited, out)),
    }
}

/// Collect the free term-variable names of an expression, respecting the
/// binders introduced by lambdas / `let`s / loops / match arms (mirrors the
/// shadowing rules of [`crate::ccl::ccl_utils::count_free`]). Also descends
/// into each sub-expression's type slot, since predicate sub-terms may carry
/// further refinements.
fn collect_expr_fv(
    e: &TypedExpr,
    bound: &mut BTreeSet<Binder>,
    visited: &mut BTreeSet<PredicateCellId>,
    out: &mut BTreeSet<Binder>,
) {
    collect_type_fv(&e.ty, bound, visited, out);
    match &e.node {
        TypedExprNode::Var(n) => {
            if !bound.contains(n) {
                out.insert(n.clone());
            }
        }
        TypedExprNode::Lambda { param, body } => {
            with_binders(bound, [param.name.clone()], |bnd| {
                collect_expr_fv(body, bnd, visited, out)
            });
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            collect_expr_fv(bound_expr, bound, visited, out);
            with_binders(bound, [binding.name.clone()], |bnd| {
                collect_expr_fv(body, bnd, visited, out)
            });
        }
        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
        } => {
            init_args
                .iter()
                .for_each(|a| collect_expr_fv(a, bound, visited, out));
            collect_expr_fv(source, bound, visited, out);
            with_binders(bound, params.iter().map(|p| p.name.clone()), |bnd| {
                collect_expr_fv(loop_body, bnd, visited, out)
            });
        }
        // The `name` of Feed/Define is a *use* of the defer handle variable.
        TypedExprNode::Feed { name, value } | TypedExprNode::Define { name, value } => {
            if !bound.contains(name) {
                out.insert(name.clone());
            }
            collect_expr_fv(value, bound, visited, out);
        }
        TypedExprNode::Case {
            scrutinee,
            branches,
        } => {
            if let Some(s) = scrutinee {
                collect_expr_fv(s, bound, visited, out);
            }
            for b in branches {
                let payload = b.pattern.iter().map(|p| p.binding.name.clone());
                with_binders(bound, payload, |bnd| {
                    collect_expr_fv(&b.guard, bnd, visited, out);
                    collect_expr_fv(&b.body, bnd, visited, out);
                });
            }
        }
        // No binders introduced: recurse structurally into child terms.
        _ => e.walk_children(|c| collect_expr_fv(c, bound, visited, out)),
    }
}

/// A type is well-formed in context `ctx` iff every free term variable of its
/// refinement predicates is bound there. The scope-validity assertion of the
/// proposal (§6.2) is exactly this check.
pub fn well_formed(ty: &Type, ctx: &BTreeSet<Binder>) -> bool {
    type_free_vars(ty).is_subset(ctx)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{BinOpKind, CompareKind, Lit, Refinement};

    fn var(s: &str) -> TypedExpr {
        TypedExpr::var(s)
    }
    fn int(n: i64) -> TypedExpr {
        TypedExpr::lit(Lit::Int(n))
    }
    /// `l > r`
    fn gt(l: TypedExpr, r: TypedExpr) -> TypedExpr {
        TypedExpr::binop(l, BinOpKind::Compare(CompareKind::Greater), r)
    }

    // A — identity laws + associativity + action on the source context.
    #[test]
    fn scenario_a_laws() {
        let sigma = Subst::rename("k", "x");
        assert_eq!(Subst::then(&Subst::id(), &sigma), sigma);
        assert_eq!(Subst::then(&sigma, &Subst::id()), sigma);

        let a = Subst::rename("k", "x");
        let b = Subst::rename("x", "z");
        let c = Subst::discharge("z", int(5));
        let abc = Subst::then(&Subst::then(&a, &b), &c);
        let abc2 = Subst::then(&a, &Subst::then(&b, &c));
        assert_eq!(abc, abc2); // associative
        // [k↦x];[x↦z];[z↦5] sends k ↦ 5
        assert_eq!(abc.apply_expr(&var("k")), int(5));
    }

    // The identity substitution is a perfect structural no-op.
    #[test]
    fn identity_is_noop() {
        let id = Subst::id();
        let exprs = [var("k"), int(3), gt(var("y"), var("k"))];
        for e in &exprs {
            assert_eq!(&id.apply_expr(e), e);
        }
        let tys = [
            Type::fun(Type::infer(), Type::infer()),
            Type::pi("k", Type::infer(), Type::infer()),
        ];
        for t in &tys {
            assert_eq!(&id.apply_type(t), t);
        }
    }

    // B — invert a rename and round-trip on a source-context term.
    #[test]
    fn scenario_b_invert() {
        let sigma = Subst::rename("k", "x");
        let sinv = sigma.invert().expect("rename invertible");
        assert_eq!(sinv, Subst::rename("x", "k"));
        let pred = gt(var("y"), var("k"));
        let there = sigma.apply_expr(&pred);
        assert_eq!(sinv.apply_expr(&there), pred); // round-trip
    }

    // E — discharges (and composites containing one) are not invertible.
    #[test]
    fn scenario_e_discharge_not_invertible() {
        let dis = Subst::discharge("x", int(5));
        assert!(dis.invert().is_none());
        let sigma = Subst::rename("k", "x");
        assert!(Subst::then(&sigma, &dis).invert().is_none());
    }

    // A binder occurring only in a *type slot's* refinement predicate is out
    // of the substitution contract: the rewriter never touches type slots, so
    // the freeness checks must not see it either (value-only). The discharge
    // takes the vacuous fast path — term and predicate cell shared untouched —
    // instead of walking the term and tripping the dangling-binder guard on a
    // correct program.
    #[test]
    fn type_slot_only_occurrence_is_vacuous() {
        use std::cell::RefCell;
        use std::rc::Rc;
        // y : {_ | k > 0} — `k` appears only in the type slot's predicate.
        let slot_ref = Refinement {
            predicate: Rc::new(RefCell::new(gt(var("k"), int(0)))),
        };
        let e = var("y").with_ty(Type::Refinement(Box::new(Type::Hole), slot_ref.clone()));
        let dis = Subst::discharge("k", int(5));

        let out = dis.apply_expr(&e);
        let Type::Refinement(_, out_ref) = &out.ty else {
            panic!("type slot preserved");
        };
        assert!(
            Rc::ptr_eq(&out_ref.predicate, &slot_ref.predicate),
            "vacuous apply_expr must share the type slot's predicate cell"
        );

        // force_refinement on a predicate whose *sub-expression type* mentions
        // `k`: vacuous at the value level — cell shared, no dangling-binder
        // panic.
        let outer = Refinement {
            predicate: Rc::new(RefCell::new(e)),
        };
        let forced = dis.force_refinement(&outer);
        assert!(
            Rc::ptr_eq(&forced.predicate, &outer.predicate),
            "value-vacuous force_refinement must share the predicate cell"
        );
    }

    // D — compose-into-then-apply equals apply-then-discharge.
    #[test]
    fn scenario_d_compose_equals_apply() {
        // predicate {y | y > k}, here just the bare body `y > k`.
        let pred = gt(var("y"), var("k"));
        let rename = Subst::rename("k", "x"); // [k↦x]: y>k ⇒ y>x
        let renamed = rename.apply_expr(&pred);
        assert_eq!(renamed, gt(var("y"), var("x")));
        let dis = Subst::discharge("x", int(5)); // [x↦5]: y>x ⇒ y>5
        let eager = dis.apply_expr(&renamed);
        let composed = Subst::then(&rename, &dis).apply_expr(&pred);
        assert_eq!(eager, gt(var("y"), int(5)));
        assert_eq!(eager, composed);
    }

    // F — the context check rejects a free `k` in [x], accepts it in [k].
    // The refinement's element binder `y` is bound by the predicate lambda
    // (as real refinement predicates are shaped), so only the outer `k` is
    // free.
    #[test]
    fn scenario_f_context_check() {
        let pred = TypedExpr::lambda("y", Type::Hole, gt(var("y"), var("k")));
        let bad = Type::Refinement(
            Box::new(Type::infer()),
            Refinement {
                predicate: std::rc::Rc::new(std::cell::RefCell::new(pred)),
            },
        );
        let only_x: BTreeSet<Binder> = ["x".to_string()].into_iter().collect();
        let only_k: BTreeSet<Binder> = ["k".to_string()].into_iter().collect();
        assert!(!well_formed(&bad, &only_x));
        assert!(well_formed(&bad, &only_k));
    }

    // G — capture avoidance: [k↦x] under a binder `x` α-renames the binder.
    #[test]
    fn scenario_g_capture_avoidance() {
        // body: λ x → (x > k); apply [k ↦ x]. The free x in the range must not
        // be captured by the lambda's own x.
        let lam = TypedExpr::lambda("x", Type::Hole, gt(var("x"), var("k")));
        let out = Subst::rename("k", "x").apply_expr(&lam);
        let TypedExprNode::Lambda { param, body, .. } = &out.node else {
            panic!("expected lambda");
        };
        assert_ne!(param.name, "x", "binder must have been α-renamed");
        // The body's original `x` now refers to the fresh binder, and the
        // substituted `k` became the *outer* `x`.
        assert!(is_free("x", &out), "outer x is free after substitution");
        // Exactly one free `x` (the substituted k), not the bound occurrence.
        let inner_binder = param.name.clone();
        assert!(is_free(&inner_binder, body));
    }

    // apply_type descends into a refinement predicate and discharges a free
    // outer binder — the dependent-application shape `g(5)`.
    #[test]
    fn apply_type_discharges_refinement_predicate() {
        let r = Refinement {
            predicate: std::rc::Rc::new(std::cell::RefCell::new(gt(var("i"), var("k")))),
        };
        let ty = Type::fun(Type::Refinement(Box::new(Type::infer()), r), Type::infer());
        let out = Subst::discharge("k", int(5)).apply_type(&ty);
        let Type::Fun { domain, .. } = &out else {
            panic!("expected fun");
        };
        let Type::Refinement(_, r2) = domain.as_ref() else {
            panic!("expected refinement domain");
        };
        assert_eq!(*r2.predicate.borrow(), gt(var("i"), int(5)));
    }

    // apply_type shadows a Pi binder: [k↦5] does not touch a codomain that
    // rebinds k.
    #[test]
    fn apply_type_shadows_pi_binder() {
        let r = Refinement {
            predicate: std::rc::Rc::new(std::cell::RefCell::new(gt(var("i"), var("k")))),
        };
        // (k: _) ⇒ {i | i > k} ⇒ _  — the inner k is bound by the Pi.
        let inner = Type::fun(Type::Refinement(Box::new(Type::infer()), r), Type::infer());
        let ty = Type::pi("k", Type::infer(), inner);
        let out = Subst::discharge("k", int(5)).apply_type(&ty);
        // The Pi binder shadows the discharge: predicate is unchanged.
        let Type::Fun { codomain, .. } = &out else {
            panic!()
        };
        let Type::Fun { domain, .. } = codomain.as_ref() else {
            panic!()
        };
        let Type::Refinement(_, r2) = domain.as_ref() else {
            panic!()
        };
        assert_eq!(*r2.predicate.borrow(), gt(var("i"), var("k")));
    }
}
