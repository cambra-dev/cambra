//! α-uniquification at lowering: the minting pass of the Barendregt
//! convention.
//!
//! Lowering builds the tree with **raw** names — spellings straight from the
//! source program, where two distinct binders can share one spelling (Python
//! reassignment lowers to a shadowing `let`). This pass walks the lowered
//! tree once, mints a fresh [`Name`] uid at every binding site, and rewrites
//! each bound variable reference to the name of the binder that lexically
//! binds it. After it runs, two binders are equal iff they are the *same*
//! binder — plain structural equality on terms coincides with α-equivalence,
//! which is what lets every downstream equality-mediated decision (refinement
//! dedup, demand satisfaction, structural reconciles) compare names without a
//! scope analysis.
//!
//! The convention this establishes (see `src/ccl/names.rs`): **unique binding
//! sites at lowering; copying preserves uids; no pass mints fresh uids on an
//! equality-mediated path.** Downstream passes that duplicate terms
//! (discharges, `let`-closing, monomorphization splices) copy minted names
//! verbatim, so copies compare equal by construction.
//!
//! Scope rules are the ones declared in [`crate::ccl::scope`]: lambda params,
//! `let` bindings (non-recursive: the bound expression sees the outer scope),
//! loop accumulators, `letrec` groups, and case-pattern payloads bind;
//! `Feed`/`Define`/`MutWrite` target names are *uses* of the binder they name.
//!
//! This is the one scope-aware pass that does **not** fold over
//! [`crate::ccl::scope::for_each_scoped_item`], and the reason is that it does
//! not merely *observe* binders — it mints them. A scoped walk hands out the
//! binders covering each child; this pass needs `&mut` access to the binding
//! *slot* in order to rewrite the name, has to mint before descending anywhere
//! it scopes over (`LetRec` must mint the whole group before walking any
//! definition), and must unwind its environment stack in step. What it can and
//! does share is the binder *enumeration*: [`assert_all_binders_minted`] checks
//! its output through [`crate::ccl::TypedExpr::walk_binders`], which is
//! exhaustive over [`crate::ccl::TypedExprNode`] for exactly this reason — so a
//! binding form this pass forgets to mint cannot be invisible to the post-pass
//! assertion, and fails it rather than passing silently. (That the enumeration
//! and the scoping rules agree on the declaration set is a test in
//! `crate::ccl::scope`.)
//!
//! Type-borne refinement predicates are full terms and are walked under the
//! environment of their syntactic origin (a `Cast` target or a user
//! annotation — pre-inference, predicates exist nowhere else): their free
//! variables resolve against that origin's lexical scope, and binders *inside*
//! a predicate mint like any other. The reserved [`crate::ccl::REFINEMENT_BINDER`] is
//! bound by the refinement itself, never enters the environment, and stays
//! raw — it is deliberately one shared name (see [`crate::ccl::Refinement`]).
//! Predicates are immutable `Rc<TypedExpr>`, so uniquifying one **rebuilds**
//! it. A predicate term shared by `Rc` across occurrences (lowering's clones
//! share predicate terms deliberately) is rebuilt **once** — keyed by
//! [`crate::ccl::PredicateId`] in `memo` — and every occurrence is re-pointed at the same
//! rebuilt `Rc`, preserving the sharing.
//!
//! A variable that resolves to no binder is left raw — it is either a
//! reference inference will reject as unbound, or a reserved name resolved
//! by other means.
//!
//! **Mint before copy.** Lowering duplicates a few already-lowered subtrees
//! (a comprehension's generator sources are cloned into its loop-join
//! predicate; chained comparisons clone the shared middle operand). A copy
//! made of *raw* trees would mint distinct uids per copy here, making
//! α-equivalent copies structurally unequal — and the loop-join shape relies
//! on the copies comparing equal (refinement dedup collapses the
//! predicate's source against the body's). So lowering runs this pass on a
//! subtree *before* cloning it (see `lower_list_comp` Phase 1), and the
//! whole-program run treats minted names as settled: minted binding sites
//! are not re-minted and push nothing on the environment (their bound
//! variables are already resolved; their free variables are still raw and
//! resolve against the environment at the position of each copy). The same
//! contract makes the pass idempotent. A consequence: after lowering a uid
//! may legitimately occur at several binding sites — copies preserve uids —
//! so the checked invariant is "every binding site is minted", not global
//! binder uniqueness.

use std::collections::HashMap;

use crate::ccl::ccl_utils::PredMemo;
use crate::ccl::{Expr, Name, Type, TypedBinding, TypedExprNode};

/// Every **distinct** refinement-predicate term reachable from `expr`, as a
/// multiset of their id-sets, deduped by `Rc` pointer.
///
/// One predicate term riding many type slots is one term; two entries here mean
/// two genuinely different `Rc`s. Used to assert uniquify's predicate handling is
/// **1:1** — see the tripwire in [`run`].
#[cfg(debug_assertions)]
fn distinct_predicate_terms(expr: &Expr) -> Vec<Vec<crate::ccl::provenance::NodeId>> {
    use crate::ccl::provenance::NodeId;
    use std::collections::{HashMap, HashSet};

    fn ids_of(e: &Expr, out: &mut Vec<NodeId>) {
        out.push(e.node_id());
        e.walk_children(|c| ids_of(c, out));
    }
    fn from_ty(t: &Type, acc: &mut HashMap<usize, Vec<NodeId>>, seen: &mut HashSet<usize>) {
        if let Type::Refinement(_, rs) = t {
            for r in rs.iter() {
                let key = std::rc::Rc::as_ptr(&r.predicate) as usize;
                if seen.insert(key) {
                    let mut v = Vec::new();
                    ids_of(&r.predicate, &mut v);
                    v.sort_unstable();
                    acc.insert(key, v);
                    from_expr(&r.predicate, acc, seen);
                }
            }
        }
        t.walk_children(|c| from_ty(c, acc, seen));
    }
    fn from_expr(e: &Expr, acc: &mut HashMap<usize, Vec<NodeId>>, seen: &mut HashSet<usize>) {
        from_ty(&e.ty, acc, seen);
        if let Some(a) = &e.user_annotation {
            from_ty(a, acc, seen);
        }
        if let TypedExprNode::Cast { target, .. } = &e.node {
            from_ty(target, acc, seen);
        }
        e.walk_children(|c| from_expr(c, acc, seen));
    }
    let mut acc = HashMap::new();
    let mut seen = HashSet::new();
    from_expr(expr, &mut acc, &mut seen);
    let mut out: Vec<Vec<NodeId>> = acc.into_values().collect();
    out.sort();
    out
}

/// α-uniquify every binder in `expr` (see module docs). Runs once per
/// program, immediately after lowering and before channelization.
pub fn run(mut expr: Expr) -> Expr {
    // Snapshot every node's `NodeId` before the rename so we can assert
    // it survives unchanged (collected only under debug_assertions).
    #[cfg(debug_assertions)]
    let before_ids = collect_node_ids(&expr);
    // The **1:1 predicate** precondition. Uniquify cannot mutate through a
    // predicate's `Rc`, so it rebuilds each one and repoints the refinement it
    // was handed. That is only a *replacement* — and preserving the ids only
    // honest — if the walk reaches every occurrence, so that no original term
    // survives beside its rebuild. Asserted rather than assumed: N distinct
    // predicate terms in, N distinct terms out, carrying the same ids.
    #[cfg(debug_assertions)]
    let before_preds = distinct_predicate_terms(&expr);

    let mut u = Uniquifier {
        env: HashMap::new(),
        // Replacing, not deriving: this walk reaches every occurrence of every
        // predicate it rebuilds, so no original survives beside its rebuild. The
        // tripwire below asserts that 1:1 correspondence on every compile.
        memo: PredMemo::replacing(),
    };
    u.expr(&mut expr);
    debug_assert!(
        u.env.values().all(|stack| stack.is_empty()),
        "uniquify: environment must be fully unwound after the walk"
    );
    #[cfg(debug_assertions)]
    assert_all_binders_minted(&expr);
    #[cfg(debug_assertions)]
    {
        let after_ids = collect_node_ids(&expr);
        debug_assert_eq!(
            before_ids, after_ids,
            "uniquify must preserve every NodeId (1:1 in-place rename); \
             provenance ids are stable across this pass"
        );
        let after_preds = distinct_predicate_terms(&expr);
        debug_assert_eq!(
            before_preds.len(),
            after_preds.len(),
            "uniquify must be 1:1 on predicate terms: {} distinct terms in, {} out. \
             A mismatch means the walk missed an occurrence, so an original term \
             survives beside its rebuild — and then preserving their ids puts one \
             id-set on two live terms.",
            before_preds.len(),
            after_preds.len(),
        );
        debug_assert_eq!(
            before_preds, after_preds,
            "uniquify's rebuilt predicate terms must carry the same ids as the \
             terms they replace",
        );
    }
    expr
}

struct Uniquifier {
    /// Lexical environment: source spelling → stack of minted names, the
    /// innermost binder last. Raw `Var`s resolve to the top of their
    /// spelling's stack.
    env: HashMap<String, Vec<Name>>,
    /// Predicates already rewritten in this run, mapped to a `(keepalive,
    /// rebuilt)` pair. A predicate term shared across occurrences is
    /// uniquified once, and every occurrence is re-pointed at the same
    /// rebuilt term.
    ///
    /// Uniquification is a predicate-*rebuilding* pass like every other, so it
    /// memoizes with the shared [`PredMemo`] — including its keepalive
    /// discipline, without which overwriting `r.predicate` could free an address
    /// a later `Rc::new` in the same walk reclaims, colliding an unrelated
    /// predicate with this entry.
    ///
    /// **Why reusing an entry is sound here**, given that the transform resolves
    /// free variables against `env` — context the memo key does not name (see
    /// [`PredMemo`]'s note on key-determined transforms). Lowering shares a
    /// predicate `Rc` across slots only by *copying one refinement*, and where it
    /// copies an already-lowered subtree it runs this pass on that subtree
    /// **before** cloning (see the module docs' "mint before copy"). So every
    /// occurrence sharing an `Rc` either sits in one scope, or is a copy whose
    /// binders are already minted and whose free variables therefore resolve the
    /// same way wherever the copy lands. Two occurrences that *should* uniquify
    /// differently — the same predicate spelling under two different bindings —
    /// arrive as distinct `Rc`s, which is what the scope-blind-equality test at the
    /// bottom of this file pins.
    memo: PredMemo,
}

impl Uniquifier {
    fn expr(&mut self, e: &mut Expr) {
        // Anchor-borne types first: `ty` is a lowering `Hole` almost
        // everywhere, but user annotations (and a few stamped types) can
        // carry refinement predicates whose free variables live in the
        // *enclosing* scope — the scope as of this node, before any binder
        // this node introduces.
        //
        // **A lambda's own arrow is the exception, by the same rule.**
        // [`crate::ccl::TypedExpr::lambda`] sets the node's type to
        // `param_ty ⇒ body_ty`, so its codomain is a copy of the body's type and belongs
        // to the *binder's* scope rather than this one. Its arm walks the two halves each
        // at its own scope.
        let lambda = matches!(&e.node, TypedExprNode::Lambda { .. });
        // Taken out and put back: the arm below matches `e.node` mutably, and the two
        // halves are walked around the mint that sits between them.
        let mut e_ty = if lambda {
            std::mem::replace(&mut e.ty, Type::Hole)
        } else {
            self.ty(&mut e.ty);
            Type::Hole
        };
        if let Some(ann) = &mut e.user_annotation {
            self.ty(ann);
        }
        match &mut e.node {
            TypedExprNode::Var(n) => {
                if let Some(m) = self.resolve(n) {
                    *n = m;
                }
            }

            // The target name is a use of the defer-handle binder
            // (Feed/Define) or of the mutable variable's `let` (MutWrite).
            TypedExprNode::Feed { name, value }
            | TypedExprNode::Define { name, value }
            | TypedExprNode::MutWrite { name, value } => {
                if let Some(m) = self.resolve(name) {
                    *name = m;
                }
                self.expr(value);
            }

            TypedExprNode::Lambda { param, body } => {
                // The domain half is the param's declared type, so it resolves against the
                // enclosing scope, alongside `binding_tys`. The codomain half is the body's
                // type and resolves under the binder. Walking the whole arrow before the
                // mint decides the codomain's names in the wrong scope — and a predicate is
                // rebuilt **once**, with every occurrence re-pointed at that rebuild, so a
                // decision made here is the one the copies visited later under the binder
                // get too.
                if let Type::Fun { domain, .. } = &mut e_ty {
                    self.ty(domain);
                }
                self.binding_tys(param);
                let base = self.bind(param);
                if let Type::Fun { codomain, .. } = &mut e_ty {
                    self.ty(codomain);
                }
                self.expr(body);
                self.unbind(base);
            }

            // The loop target binds only in the body; the source sees the
            // outer scope.
            TypedExprNode::For { target, iter, body } => {
                self.expr(iter);
                self.binding_tys(target);
                let base = self.bind(target);
                self.expr(body);
                self.unbind(base);
            }

            // Non-recursive `let`: the bound expression sees the outer scope.
            TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            } => {
                self.expr(bound_expr);
                self.binding_tys(binding);
                let base = self.bind(binding);
                self.expr(body);
                self.unbind(base);
            }

            // A mutable variable introduction binds exactly like a `let`: the seed is
            // walked *outside* the binder's scope (a seed cannot reference the
            // register it seeds), then the name is minted over the body — which is
            // where its `MutWrite`s and reads live, and they must resolve to this
            // binder's α-unique name for the write-target map to key on.
            TypedExprNode::MutDecl {
                binding,
                init,
                body,
            } => {
                self.expr(init);
                self.binding_tys(binding);
                let base = self.bind(binding);
                self.expr(body);
                self.unbind(base);
            }

            // Mutual recursion: mint *all* group binders before walking any
            // binding body, so a reference to any group name — in any body or
            // in the letrec body — resolves to its group binder.
            TypedExprNode::LetRec { bindings, body } => {
                let bases: Vec<Option<String>> = bindings
                    .iter_mut()
                    .map(|(b, _)| {
                        self.binding_tys(b);
                        self.bind(b)
                    })
                    .collect();
                for (_, def) in bindings.iter_mut() {
                    self.expr(def);
                }
                self.expr(body);
                for base in bases.into_iter().rev() {
                    self.unbind(base);
                }
            }

            TypedExprNode::Case {
                scrutinee,
                branches,
            } => {
                if let Some(s) = scrutinee {
                    self.expr(s);
                }
                for b in branches {
                    match &mut b.pattern {
                        Some(p) => {
                            self.binding_tys(&mut p.binding);
                            let base = self.bind(&mut p.binding);
                            self.expr(&mut b.guard);
                            self.expr(&mut b.body);
                            self.unbind(base);
                        }
                        None => {
                            self.expr(&mut b.guard);
                            self.expr(&mut b.body);
                        }
                    }
                }
            }

            // The cast target is a type slot `walk_children_mut` skips; its
            // refinement predicate is the main anchor lowering emits.
            TypedExprNode::Cast { value, target } => {
                self.ty(target);
                self.expr(value);
            }

            // Everything else introduces no binders and no type anchors of
            // its own: plain structural recursion.
            _ => e.walk_children_mut(|c| self.expr(c)),
        }
        if lambda {
            e.ty = e_ty;
        }
    }

    /// Walk a refinement-bearing type, uniquifying each predicate under the
    /// current environment by rebuilding it — once per shared predicate term
    /// (see module docs), with every occurrence re-pointed at the rebuilt `Rc`
    /// via `memo`.
    fn ty(&mut self, t: &mut Type) {
        if let Type::Refinement(_, refinements) = t {
            // A handle clone, so `self` stays freely borrowable for the rebuild —
            // which re-enters this same memo through `self.expr` → `self.ty`.
            let memo = self.memo.clone();
            refinements.rewrite_each(|_, r| {
                memo.rebuild(r, &(), |pred| {
                    self.expr(pred);
                    true
                });
            });
        }
        t.walk_children_mut(|c| self.ty(c));
    }

    /// Walk the type slots riding a binding site itself. These are in the
    /// scope *outside* the binder (a binding's annotation cannot reference
    /// the binding).
    fn binding_tys(&mut self, b: &mut TypedBinding) {
        self.ty(&mut b.ty);
        if let Some(ann) = &mut b.user_annotation {
            self.ty(ann);
        }
    }

    /// Mint a fresh uid for this binding site and push it on its spelling's
    /// scope stack. Returns the spelling for the matching [`Self::unbind`].
    /// An already-minted binder (a pre-minted, lowering-copied subtree — see
    /// module docs) is left as-is and binds nothing: its bound variables were
    /// resolved when it was minted.
    fn bind(&mut self, b: &mut TypedBinding) -> Option<String> {
        if !b.name.is_raw() {
            return None;
        }
        let base = b.name.base().to_string();
        let fresh = Name::fresh(&base);
        self.env
            .entry(base.clone())
            .or_default()
            .push(fresh.clone());
        b.name = fresh;
        Some(base)
    }

    fn unbind(&mut self, base: Option<String>) {
        let Some(base) = base else { return };
        self.env
            .get_mut(&base)
            .expect("uniquify: unbind of never-bound spelling")
            .pop()
            .expect("uniquify: scope stack underflow");
    }

    /// The minted name a raw variable reference resolves to, if any. Minted
    /// names pass through untouched; unresolved raw names stay raw.
    fn resolve(&self, n: &Name) -> Option<Name> {
        if !n.is_raw() {
            return None;
        }
        self.env.get(n.base()).and_then(|s| s.last()).cloned()
    }
}

/// Collect the sorted multiset of every node's [`NodeId`] reachable from
/// `expr`, mirroring the exact set of nodes [`Uniquifier::expr`] visits —
/// the main expression tree *and* the [`TypedExpr`]s living inside type-borne
/// refinement predicates (which uniquify rebuilds in place). Sorting makes the
/// result order-independent so the before/after comparison checks set identity
/// with 1:1 multiplicity, not traversal order.
///
/// This domain is **broader than the uniqueness walk**'s `walk_children` node-set
/// (see `design/provenance.md`, "Walking the ids"): the
/// property checked here is not uniqueness but preservation, and predicate
/// interiors are in scope precisely because uniquify rebuilds those terms through
/// a [`PredMemo`], which is where a rebuild could drop or re-mint an id. Do not
/// narrow it to match the freshen walks — they are checking different things.
/// (Likewise no [`PredicateId`](crate::ccl::PredicateId) dedup: a term shared by
/// `Rc` across N slots contributes its ids N times, on both sides of the
/// comparison.)
///
/// Compiled under `debug_assertions`
/// (where `run` asserts with it) or `test` (where the preservation tests call
/// it); a release build with neither pays nothing.
#[cfg(any(debug_assertions, test))]
fn collect_node_ids(expr: &Expr) -> Vec<crate::ccl::provenance::NodeId> {
    use crate::ccl::provenance::NodeId;

    fn from_ty(t: &Type, out: &mut Vec<NodeId>) {
        for r in t.refinements() {
            from_expr(&r.predicate, out);
        }
        t.walk_children(|c| from_ty(c, out));
    }

    fn from_expr(e: &Expr, out: &mut Vec<NodeId>) {
        out.push(e.node_id());
        from_ty(&e.ty, out);
        if let Some(ann) = &e.user_annotation {
            from_ty(ann, out);
        }
        // `Cast`'s target is a type slot `walk_children` skips; its refinement
        // predicate is an anchor uniquify rebuilds, so walk it explicitly.
        if let TypedExprNode::Cast { target, .. } = &e.node {
            from_ty(target, out);
        }
        e.walk_children(|c| from_expr(c, out));
    }

    let mut out = Vec::new();
    from_expr(expr, &mut out);
    out.sort_unstable();
    out
}

/// The checked Barendregt invariant at the minting boundary: right after
/// uniquification every binding site is a [`Name::Unique`]. `Synthetic`
/// binders don't exist yet (later passes mint them) and the element binder is
/// never a binding site, so `Unique` is exact here — which is the whole point
/// of keeping the variants distinct. Global binder *uniqueness* is deliberately
/// not asserted — lowering copies pre-minted subtrees (see module docs), so a
/// uid may occur at several binding sites; the convention is "distinct
/// derivations get distinct uids, copies share," which is not a tree-checkable
/// property.
#[cfg(debug_assertions)]
fn assert_all_binders_minted(expr: &Expr) {
    fn go(e: &Expr) {
        // `walk_binders` is the exhaustive enumeration of binding *slots* (kept
        // in step with `crate::ccl::scope`'s scoping rules by that module's
        // corpus test), so this check covers a newly-added binding form for
        // free — it cannot fall through a wildcard arm.
        e.walk_binders(|b| {
            assert!(
                matches!(b.name, Name::Unique { .. }),
                "uniquify must mint every binding site to a Unique name; `{:?}` is not",
                b.name
            );
        });
        e.walk_children(go);
    }
    go(expr);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::lower::{LoweringContext, lower_stmts};
    use crate::ccl::{Expr, Lit, Refinement};

    /// Parse and lower a CHL program, *without* uniquifying.
    fn lower_only(code: &str) -> Expr {
        let mut ctx = LoweringContext::default();
        let stmts = crate::chl_parser::parse_module(code)
            .into_result()
            .expect("parse failed")
            .body;
        let lowered = lower_stmts(&stmts, &mut ctx);
        assert!(lowered.errors.is_empty(), "{:?}", lowered.errors);
        lowered.value.expect("lowering produced no value")
    }

    /// Parse, lower, and uniquify a CHL program.
    fn pipeline_front(code: &str) -> Expr {
        run(lower_only(code))
    }

    /// Every refinement reachable from `e`'s types (Cast targets,
    /// annotations, ty slots), in walk order — including refinements nested
    /// inside other refinements' predicate expressions.
    fn collect_refinements(e: &Expr, out: &mut Vec<Refinement>) {
        fn from_ty(t: &Type, out: &mut Vec<Refinement>) {
            for r in t.refinements() {
                out.push(r.clone());
                collect_refinements(&r.predicate, out);
            }
            t.walk_children(|c| from_ty(c, out));
        }
        from_ty(&e.ty, out);
        if let Some(ann) = &e.user_annotation {
            from_ty(ann, out);
        }
        if let TypedExprNode::Cast { target, .. } = &e.node {
            from_ty(target, out);
        }
        e.walk_children(|c| collect_refinements(c, out));
    }

    /// All `Let` binders named (by base) `base`, in walk order.
    fn let_binders(e: &Expr, base: &str, out: &mut Vec<Name>) {
        if let TypedExprNode::Let { binding, .. } = &e.node
            && binding.name.base() == base
        {
            out.push(binding.name.clone());
        }
        e.walk_children(|c| let_binders(c, base, out));
    }

    // The scope-blind-equality hazard, closed: the same predicate spelling
    // under two different `k` bindings (Python reassignment lowers to a
    // shadowing `let`) yields *distinct* refinements.
    #[test]
    fn shadowed_scope_twins_are_distinct_refinements() {
        let expr = pipeline_front(
            "k = 1\n\
             a = [x for x in [1, 2, 3] if x > k]\n\
             k = 2\n\
             b = [x for x in [1, 2, 3] if x > k]\n\
             (a, b)\n",
        );
        let mut ks = Vec::new();
        let_binders(&expr, "k", &mut ks);
        assert_eq!(ks.len(), 2, "two shadowing k bindings");
        assert_ne!(ks[0], ks[1], "shadowing binders must mint distinct uids");

        let mut refinements = Vec::new();
        collect_refinements(&expr, &mut refinements);
        assert_eq!(refinements.len(), 2, "one refinement per filter");
        assert_ne!(
            refinements[0], refinements[1],
            "`x > k` under different k bindings must be distinct refinements"
        );
    }

    // Control for the twins test: *copies of one derivation* still compare
    // equal. A filtered outer comprehension clones its (filtered) generator
    // source into the loop-join predicate — mint-before-copy makes the
    // body-side and predicate-side copies of the inner refinement share
    // uids, so the tag dedup that collapses them keeps working. (Two
    // *separately written* identical comprehensions are independent
    // derivations and deliberately do NOT compare equal under uid naming.)
    #[test]
    fn copies_of_one_derivation_compare_equal() {
        let expr = pipeline_front("[x for x in [y for y in [1, 2, 3] if y < 3] if x < 2]\n");
        let mut refinements = Vec::new();
        collect_refinements(&expr, &mut refinements);
        // The inner `y < 3` refinement appears at several anchors (the inner
        // comprehension's cast in the body chain and its clone in the
        // loop-join predicate). Those copies must land in one equality
        // class — partition the collected refinements by `==` and check a
        // multi-member class exists.
        let mut classes: Vec<(Refinement, usize)> = Vec::new();
        for r in refinements {
            match classes.iter_mut().find(|(rep, _)| *rep == r) {
                Some((_, n)) => *n += 1,
                None => classes.push((r, 1)),
            }
        }
        assert!(
            classes.iter().any(|(_, n)| *n >= 2),
            "expected a refinement anchored at multiple copies to compare \
             equal across them; classes: {:?}",
            classes.iter().map(|(_, n)| *n).collect::<Vec<_>>()
        );
    }

    #[test]
    fn shadowing_resolves_to_innermost_binder() {
        let expr = pipeline_front("k = 1\nk = 2\nk\n");
        let mut ks = Vec::new();
        let_binders(&expr, "k", &mut ks);
        assert_eq!(ks.len(), 2);
        // The terminal `k` reference resolves to the inner (second) binder.
        fn find_var(e: &Expr, base: &str, out: &mut Vec<Name>) {
            if let TypedExprNode::Var(n) = &e.node
                && n.base() == base
            {
                out.push(n.clone());
            }
            e.walk_children(|c| find_var(c, base, out));
        }
        let mut uses = Vec::new();
        find_var(&expr, "k", &mut uses);
        assert!(!uses.is_empty());
        assert!(
            uses.iter().all(|u| *u == ks[1]),
            "every free k use sits under the inner binder"
        );
    }

    // The refinement's reserved element binder is never minted; the
    // predicate's free program variables resolve to the enclosing binder.
    #[test]
    fn predicate_vars_resolve_at_their_anchor() {
        let expr = pipeline_front("k = 1\n[x for x in [1, 2, 3] if x > k]\n");
        let mut ks = Vec::new();
        let_binders(&expr, "k", &mut ks);
        assert_eq!(ks.len(), 1);
        let mut refinements = Vec::new();
        collect_refinements(&expr, &mut refinements);
        assert_eq!(refinements.len(), 1);
        let pred = &*refinements[0].predicate;
        fn vars(e: &Expr, out: &mut Vec<Name>) {
            if let TypedExprNode::Var(n) = &e.node {
                out.push(n.clone());
            }
            e.walk_children(|c| vars(c, out));
        }
        let mut vs = Vec::new();
        vars(pred, &mut vs);
        assert!(
            vs.iter().any(|v| v.is_elem()),
            "the element binder stays the raw reserved name"
        );
        assert!(
            vs.iter().any(|v| *v == ks[0]),
            "the predicate's k resolves to the enclosing binder"
        );
    }

    // Feed/Define target names are uses of the defer-handle binder.
    #[test]
    fn feed_target_resolves_to_defer_binder() {
        let inner = Expr::expr_stmt(Expr::feed("d", Expr::lit(Lit::Int(1))), Expr::var("d"));
        let expr = run(Expr::let_bind("d", Expr::new(TypedExprNode::Defer), inner));
        let TypedExprNode::Let { binding, body, .. } = &expr.node else {
            panic!("expected let");
        };
        assert!(!binding.name.is_raw());
        let TypedExprNode::ExprStmt { expr: fed, body } = &body.node else {
            panic!("expected expr_stmt");
        };
        let TypedExprNode::Feed { name, .. } = &fed.node else {
            panic!("expected feed");
        };
        assert_eq!(name, &binding.name, "feed target follows the binder");
        let TypedExprNode::Var(v) = &body.node else {
            panic!("expected var");
        };
        assert_eq!(v, &binding.name);
    }

    // Mint-before-copy: a second run leaves a minted tree untouched.
    #[test]
    fn idempotent_on_minted_trees() {
        let expr = pipeline_front("k = 1\n[x for x in [1, 2, 3] if x > k]\n");
        // The second run must see the same nodes, not a freshened copy of them.
        let again = run(expr.clone_preserving_ids());
        assert_eq!(expr, again, "uniquify must be idempotent");
    }

    // uniquify is a 1:1 in-place rename, so it must preserve every node's
    // provenance `NodeId` — none added, dropped, or changed. Mirrors the
    // before/after set checked by the in-pass debug_assert in `run`.
    #[test]
    fn uniquify_preserves_every_node_id() {
        use crate::ccl::provenance::NodeId;
        use std::collections::HashSet;

        // `let x = 1 in let x = x in x` — two shadowing `x` binders plus uses,
        // so the rename actually rewrites `Var` names. Lower *without*
        // uniquifying so we capture ids before the rename.
        let expr = lower_only("x = 1\nx = x\nx\n");

        let before: HashSet<NodeId> = collect_node_ids(&expr).into_iter().collect();
        // Pin a known structural position: the id of the root `Let` node.
        assert!(
            matches!(expr.node, TypedExprNode::Let { .. }),
            "expected a root Let"
        );
        let root_id = expr.node_id();

        let after_expr = run(expr);
        let after: HashSet<NodeId> = collect_node_ids(&after_expr).into_iter().collect();

        assert_eq!(
            before, after,
            "uniquify must preserve the exact set of NodeIds (none added, dropped, or changed)"
        );
        assert_eq!(
            after_expr.node_id(),
            root_id,
            "the root Let's NodeId is unchanged across the rename"
        );
    }

    #[test]
    fn unbound_references_stay_raw() {
        let expr = run(Expr::var("never_bound"));
        let TypedExprNode::Var(n) = &expr.node else {
            panic!("expected var")
        };
        assert!(n.is_raw());
        assert_eq!(n.base(), "never_bound");
    }

    // LetRec α-renames without capture: the group binders shadow an outer
    // same-spelling binder across every binding body and the letrec body,
    // and mutual references resolve to the *group* binders (all minted
    // before any body is walked). Constructed directly — nothing lowers to
    // LetRec yet.
    #[test]
    fn letrec_group_binders_shadow_and_resolve_mutually() {
        use crate::ccl::TypedBinding;
        // let f = 1 in
        // letrec f = g ▷ f; g = λ x → f in f
        let expr = run(Expr::let_bind(
            "f",
            Expr::lit(Lit::Int(1)),
            Expr::letrec(
                vec![
                    (
                        TypedBinding::new_unannotated("f"),
                        Expr::apply(Expr::var("g"), Expr::var("f")),
                    ),
                    (
                        TypedBinding::new_unannotated("g"),
                        Expr::lambda("x", Type::Hole, Expr::var("f")),
                    ),
                ],
                Expr::var("f"),
            ),
        ));
        let TypedExprNode::Let { binding, body, .. } = &expr.node else {
            panic!("expected outer let");
        };
        let outer_f = binding.name.clone();
        let TypedExprNode::LetRec {
            bindings,
            body: rec_body,
        } = &body.node
        else {
            panic!("expected letrec");
        };
        let (f_rec, g_rec) = (&bindings[0].0.name, &bindings[1].0.name);
        assert!(!f_rec.is_raw() && !g_rec.is_raw(), "group binders minted");
        assert_ne!(
            *f_rec, outer_f,
            "letrec's f is a fresh binder, not the outer let's"
        );
        // f's def `g ▷ f`: both references resolve to *group* binders — g
        // forward-references the later binding, f self-references, and
        // neither is captured by the outer let's f.
        let TypedExprNode::Apply { function, argument } = &bindings[0].1.node else {
            panic!("expected apply in f's def");
        };
        assert_eq!(function.node, TypedExprNode::Var(f_rec.clone()));
        assert_eq!(argument.node, TypedExprNode::Var(g_rec.clone()));
        // g's def `λ x → f`: the reference under an inner binder still
        // resolves to the group's f.
        let TypedExprNode::Lambda {
            body: lambda_body, ..
        } = &bindings[1].1.node
        else {
            panic!("expected lambda in g's def");
        };
        assert_eq!(lambda_body.node, TypedExprNode::Var(f_rec.clone()));
        // The letrec body's f is the group's, shadowing the outer let.
        assert_eq!(rec_body.node, TypedExprNode::Var(f_rec.clone()));
    }
}
