//! Refinement-predicate compilation (design §6.3 / §6.5).
//!
//! Predicates ride the pipeline as bare expressions over the implicit
//! `REFINEMENT_BINDER`; planning compiles each to point-free form by running
//! the lambda-elim → simplify sub-pipeline on it. [`compile_refinement_predicates`]
//! is the whole-tree pass; [`fn_of_bare_predicate`] is the inverse of
//! [`crate::ccl::ccl_utils::bare_predicate_of_fn`] that the iterate/restrict and
//! op-conversion lowering consume.

use crate::ccl::Occurrence;
use crate::ccl::infer::solver::Solver;
use std::collections::HashSet;

use super::*;
use crate::ccl::Duplicate;
use crate::ccl::RefinementSet;
use crate::ccl::ty::TypeLet;

// Predicate compilation is a predicate-*rebuilding* pass like any other, so it
// memoizes with the shared [`ccl_utils::PredMemo`] — including its keepalive
// discipline, which is load-bearing rather than incidental here: overwriting
// `refinement.predicate` with the compiled result drops the *original* `Rc` if
// that was its last strong reference, and the freed address can be handed
// straight back to an unrelated `Rc::new` later in the same walk — including one
// of `compile_predicates_in_type`'s own allocations — so an unrelated predicate
// starting life at that address would collide and inherit this entry's compiled
// form. Observed in practice: two structurally unrelated join predicates from
// different call sites landed on the same freed address and the second silently
// inherited the first's compiled form.
//
// Dedup itself is a **performance / structural-sharing optimization, not a
// correctness requirement** — verified: the full suite passes with dedup
// disabled (i.e. recompiling every occurrence independently). Compilation is
// effectively a value function for comparison purposes: `lambda_elim` mints a
// fresh `__pair` `Uid` in its nested-lambda rule, but that binder is
// *eliminated* within the same run, so the compiled output is point-free and
// carries no minted binder — two independent compilations of one predicate yield
// structurally-equal terms. (The convention this rests on — no pass leaves a
// re-minted bound binder in a term that equality later compares — is what makes
// by-name equality coincide with α-equivalence; `lambda_elim` upholds it by
// eliminating `__pair` rather than the equality having to be α-aware.)
//
// Keying on the `Rc` address rather than a refinement id is deliberate: a
// substituted/discharged refinement keeps its id but holds an independently
// rebuilt predicate that must be compiled on its own, so keying by id would skip
// it and leave it in lambda form.

// The refinement's **base** is the memo's context ([`PredicateContext`]), because
// compilation reads it: `fn_of_bare_predicate` eta-expands `λ 𝑒 : base →
// bare[__elem ↦ 𝑒]`, and `bare_predicate_of_fn` stamps it on the element var. An entry is
// therefore reused only for an occurrence over an equal base. That holds in
// practice — a shared `Rc` is only ever created by copying one refinement — but
// nothing enforces it, and keying on the base means a mismatch *recompiles*
// rather than silently borrowing another occurrence's element type.
//
// Cost of a `Type` context: a lookup compares bases structurally, and `PartialEq`
// for a refined `Type` descends into predicate terms. Two things keep that cheap.
// The base is the type being *refined*, so it sits below the refinement rather
// than containing it — comparing `{Int | p}`'s base compares `Int`, never `p` —
// and the entry list for one key is a singleton in every shape measured, so a hit
// is one compare of a small type. The clone per refinement node is the same
// shallow value. Measured against the pre-context memo the difference is in the
// noise; a base that ever became large enough to matter would be a signal about
// the types, not about this key.

/// What compiling a refinement reads besides its predicate, which keys the pass's memo: the
/// element type the predicate is applied at, and the type `let`s around the refinement that the
/// predicate or the element type reads, each as its binder, its definition, and the binders
/// between the `let` and the refinement ([`TypeLetScope`]). Two occurrences of one predicate under
/// different definitions compile apart.
#[derive(Clone, PartialEq)]
pub(crate) struct PredicateContext {
    element: Type,
    lets: Vec<(Name, Rc<crate::ccl::ty::HeldTerm>, u32)>,
}

/// The type `let`s ([`TypeLet`]) around the position a predicate walk has reached, outermost
/// first, each with the walk's binder depth at the `let`; `depth` counts the binders an index
/// counts at the position. The ones left after the program's root binds what it can
/// ([`super::held`]) hold a value per position, and a compiled refinement has the ones it reads
/// discharged ([`Self::compiled_form`]). They key the memo ([`PredicateContext`]).
#[derive(Clone, Default)]
pub(crate) struct TypeLetScope {
    lets: Vec<(Rc<TypeLet>, u32)>,
    depth: u32,
    /// What planning does with each type `let`'s definition ([`super::PlanningCtx::held`]).
    held: Rc<held::TypeLetRoles>,
    /// The compiled definitions of the type `let`s the walk has met, by binder
    /// ([`Self::share_definition`]).
    compiled: Rc<std::cell::RefCell<std::collections::HashMap<Name, ccl_utils::SharedTerms>>>,
}

impl TypeLetScope {
    /// Point the definition of the type `let` `l` at an equal compiled definition of a `let` of
    /// the same binder, or record it as one. Each position holding a `let` compiles its
    /// definition under the `let`s around it, so one definition held at many positions compiles
    /// to many equal copies ([`ccl_utils::SharedTerms`]).
    fn share_definition(&self, l: &mut TypeLet) {
        if let Some(kept) = self
            .compiled
            .borrow_mut()
            .entry(l.name.clone())
            .or_default()
            .share(&l.definition, || ccl_utils::term_reads(&l.definition))
        {
            l.definition = kept;
        }
    }

    /// `predicate` reading each type `let`'s definition the program's root binds by the root's binder,
    /// with every other type `let`'s definition it reads discharged, directly or through another's,
    /// each raised by the binders between its `let` and the predicate. Copies the definitions,
    /// so the caller holds a recording open.
    fn compiled_form(&self, predicate: Expr) -> Expr {
        // A root `let` of the predicate is the type's: dropped where the program's root binds
        // its binder, and discharged into the predicate otherwise.
        let mut term = predicate;
        while let TypedExprNode::Let {
            binding,
            bound_expr,
            ..
        } = &term.node
            && binding.transparency == crate::ccl::BindingTransparency::Transparent
            && crate::ccl::subst::free_elem_indices(bound_expr).is_empty()
        {
            let bound = self
                .held
                .role_of(&binding.name, bound_expr)
                .filter(|role| self.held.bound.contains(role));
            let TypedExprNode::Let {
                binding,
                bound_expr,
                body,
            } = term.node
            else {
                unreachable!("matched a `let` above")
            };
            term = match bound {
                None => lambda_elim::substitute(*body, &binding.name, &bound_expr),
                // A copy's own name for the binder the root binds.
                Some(role) if role != binding.name => {
                    crate::ccl::subst::Subst::rename(binding.name, role).apply_expr(&body)
                }
                Some(_) => *body,
            };
        }
        let mut term = self.with_unbound_discharged(term);
        held::list_elements_discharged(&mut term, &|n| {
            self.held.definitions.get(n).map(|d| d.term())
        });
        term
    }

    /// `term`, standing under every `let` of the scope, with each definition the program's root
    /// does not bind discharged, raised by the binders between its `let` and `term`. A
    /// definition can read another, so each round writes in an outer one.
    fn with_unbound_discharged(&self, mut term: Expr) -> Expr {
        loop {
            let reads = ccl_utils::free_names(&term);
            let definitions: std::collections::HashMap<Name, Expr> = self
                .lets
                .iter()
                .filter(|(l, _)| !self.held.bound.contains(&l.name) && reads.contains(&l.name))
                .map(|(l, at)| {
                    (
                        l.name.clone(),
                        crate::ccl::subst::raised_term(&l.definition, self.depth - at),
                    )
                })
                .collect();
            if definitions.is_empty() {
                break;
            }
            term = crate::ccl::subst::Subst::discharge_env_in_place_in(
                &mut Solver::none(),
                term,
                &definitions,
                crate::ccl::Ids::Fresh,
            );
        }
        term
    }

    /// The `let`s that a term or type reading `reads` reads, directly or through another's
    /// definition.
    fn read_by(&self, reads: impl IntoIterator<Item = Name>) -> Vec<&(Rc<TypeLet>, u32)> {
        let lets: Vec<&TypeLet> = self.lets.iter().map(|(l, _)| &**l).collect();
        TypeLet::read_by(&lets, reads)
            .into_iter()
            .zip(&self.lets)
            .filter_map(|(read, l)| read.then_some(l))
            .collect()
    }
}

/// True if a `__pair` binder ([`Name::is_synthetic_pair`]) other than one of
/// `referenced` appears anywhere in the **term** `e` — its node and child
/// *expressions*, never its type slots.
///
/// Type slots are skipped on purpose: lambda elimination leaves `__pair` in a
/// type slot as a `Fun.name` Pi binder, which every equality path ignores
/// (`eq_term_modulo_ty_slots` is type-blind; the structural reconcile strips Pi
/// names via `without_pi_names`). The invariant this backs is purely about the
/// compared term.
///
/// `referenced` is the pair binders the predicate read before it was compiled. A
/// predicate under a correlated site reads its row through the pair the site's
/// function takes, and its reference to that binder is a free name like any
/// other: compilation keeps it, and it is the same name in every compilation.
fn term_mentions_pair_binder(e: &Expr, referenced: &HashSet<Name>) -> bool {
    let here = match &e.node {
        TypedExprNode::Var(n) => n.is_synthetic_pair() && !referenced.contains(n),
        TypedExprNode::Lambda { params, .. } => params.iter().any(|p| p.name.is_synthetic_pair()),
        TypedExprNode::Let { binding, .. } => binding.name.is_synthetic_pair(),
        TypedExprNode::LetRec { bindings, .. } => {
            bindings.iter().any(|(b, _)| b.name.is_synthetic_pair())
        }
        TypedExprNode::For { target, .. } => target.name.is_synthetic_pair(),
        TypedExprNode::MutWrite { name, .. } => name.is_synthetic_pair(),
        TypedExprNode::Case { branches, .. } => branches.iter().any(|b| {
            b.pattern
                .as_ref()
                .is_some_and(|p| p.binding.name.is_synthetic_pair())
        }),
        _ => false,
    };
    here || e.any_child(|c| term_mentions_pair_binder(c, referenced))
}

/// Compile every refinement predicate reachable from `expr` by running the
/// lambda-elim → simplify sub-pipeline on it (design §6.3/§6.5).
///
/// Refinement predicates ride the pipeline as bare expressions over the implicit
/// `REFINEMENT_BINDER`; this normalizes each to `__elem ▷ p` with a point-free
/// `p`, the form the recognizers and op-conversion's `Restrict` consume (it
/// recovers `p` via `fn_of_bare_predicate` and re-wraps). Each distinct predicate
/// `Rc` is compiled once.
///
/// Every type slot a node carries is compiled, not just `expr.ty`
/// ([`Expr::walk_type_slots_mut`]): a `Cast`'s `target` and the binder-declared
/// types (lambda param, `let` binding, etc.) carry their own predicate `Rc`s.
/// They are independent (immutable) terms, so each must be normalized. For the
/// common predicate (no nested lambdas) compilation is deterministic, so a
/// `target` and its parallel `expr.ty` normalize to structurally-equal point-free
/// predicates and still match under refinement equality; for the nested-lambda
/// case the per-`Rc` memo keeps shared occurrences equal despite `lambda_elim`'s
/// `__pair` minting (see [`PredMemo`]).
pub(crate) fn compile_refinement_predicates(
    expr: &mut Expr,
    memo: &PredMemo<PredicateContext>,
    held: &Rc<held::TypeLetRoles>,
) {
    compile_refinement_predicates_under(
        expr,
        memo,
        &mut TypeLetScope {
            held: Rc::clone(held),
            ..TypeLetScope::default()
        },
    );
}

/// [`compile_refinement_predicates`] in a term at `scope`: a type `let`'s definition, under the
/// `let`s around it.
fn compile_refinement_predicates_under(
    expr: &mut Expr,
    memo: &PredMemo<PredicateContext>,
    scope: &mut TypeLetScope,
) {
    // A `Cast`'s target refinements are assertions on the cast's *value*: the
    // checker types them with `__elem` bound at the value's domain (see
    // `emit_cast`), which carries the value's own refinements. Compile them against
    // that same base — a target holds only the cast's *born* refinements, so
    // deriving the element type from the target alone would stamp `__elem`
    // bare and fail the checker's argument edge against a predicate function
    // whose domain the value's refinements narrow.
    if let TypedExprNode::Cast { value, target } = &mut expr.node {
        let value_dom = value.ty.domain();
        compile_cast_target(target, value_dom, memo, scope);
        compile_predicates_in_type(&mut expr.ty, memo, &[], scope);
        compile_refinement_predicates_under(value, memo, scope);
        return;
    }
    expr.walk_type_slots_mut(|ty| compile_predicates_in_type(ty, memo, &[], scope));
    expr.walk_children_mut(|child| compile_refinement_predicates_under(child, memo, scope));
}

/// Compile a cast target's domain refinements against the value's domain (the
/// assertion base — see [`compile_refinement_predicates`]), then the rest of
/// the target generically. The top-level domain refinement must not be
/// revisited by the generic walk: recompiling it against the target's bare
/// base would re-stamp `__elem` with the narrower context lost.
fn compile_cast_target(
    target: &mut Type,
    value_dom: Option<Type>,
    memo: &PredMemo<PredicateContext>,
    scope: &mut TypeLetScope,
) {
    if let Type::Fun {
        binder,
        domain,
        codomain,
        ..
    } = target
    {
        // The type `let`s over the domain are in scope at its refinements.
        let outside = scope.lets.len();
        let mut at = domain.as_mut();
        while let Type::Let(l) = at {
            scope.lets.push((Rc::clone(l), scope.depth));
            at = &mut Rc::make_mut(l).body;
        }
        if let Type::Refinement(base, refinements) = at {
            // The base an assertion *filters*: the value's domain with the assertion itself
            // taken back out. A target holds only the cast's born refinements, so its own
            // set cannot say what precedes them, and the value's domain says it once the
            // born ones stop counting as their own predecessors. The two readings of this
            // base were wrong in opposite directions — the target's bare base drops the
            // narrowing the restrict pipeline gives this predicate, and the value's domain
            // hands the predicate a domain its own assertion already narrowed — which only
            // reconciled while a predicate was a compute function and contravariance absorbed it.
            let assert_base = match value_dom.as_ref().map(TypeLet::peel) {
                Some((value_lets, Type::Refinement(value_base, value_set))) => {
                    let preceding = value_set
                        .as_slice()
                        .iter()
                        .filter(|r| !refinements.as_slice().contains(r))
                        .cloned()
                        .fold(RefinementSet::default(), |mut acc, r| {
                            acc.insert(r);
                            acc
                        });
                    TypeLet::rewrap(
                        &value_lets,
                        Type::refined((**value_base).clone(), preceding),
                    )
                }
                Some(_) => value_dom.clone().expect("matched `Some`"),
                None => (**base).clone(),
            };
            compile_refinements(refinements, &assert_base, memo, &[], scope);
            compile_predicates_in_type(base, memo, &[], scope);
        } else {
            compile_predicates_in_type(at, memo, &[], scope);
        }
        scope.lets.truncate(outside);
        settle_lets(domain);
        compile_codomain(binder, domain, codomain, memo, &[], scope);
    } else {
        compile_predicates_in_type(target, memo, &[], scope);
    }
}

/// `ty` with each type `let` at its root that compilation left unread dropped, or its
/// definition discharged where that is a variable or a literal: a compiled predicate has the
/// definitions it reads discharged.
fn settle_lets(ty: &mut Type) {
    if let Type::Let(l) = ty {
        settle_lets(&mut Rc::make_mut(l).body);
        ccl_utils::inline_rewritten_let(ty);
    }
}

/// The refinements of `ty` under the type `let`s at its root, each in the form a compiled
/// predicate takes ([`TypeLetScope::compiled_form`]): reading the binders the program's root binds,
/// with every other definition it reads discharged.
pub(crate) fn refinements_under_lets(
    ty: &Type,
    held: &held::TypeLetRoles,
) -> Vec<crate::ccl::Refinement> {
    let (lets, under) = TypeLet::peel(ty);
    let scope = TypeLetScope {
        lets: lets.iter().map(|l| (Rc::new((*l).clone()), 0)).collect(),
        depth: 0,
        held: Rc::new(held.clone()),
        compiled: Default::default(),
    };
    under
        .own_refinements()
        .iter()
        .map(|r| {
            let reads = ccl_utils::free_names(&r.predicate);
            let root_let = matches!(&r.predicate.node, TypedExprNode::Let { .. });
            if !root_let && scope.read_by(reads).is_empty() {
                return r.clone();
            }
            let _g = provenance::enter(
                r.predicate.node_id(),
                "planning.predicate_under_lets",
                provenance::Nature::Machinery,
            );
            crate::ccl::Refinement::born(Rc::new(scope.compiled_form(r.predicate.duplicate())))
        })
        .collect()
}

/// The witness projection `ty` is under the type `let`s at its root, its term in the form a
/// compiled predicate takes ([`refinements_under_lets`]). `None` where `ty` is no projection
/// under its `let`s.
pub(crate) fn projection_under_lets(
    ty: &Type,
    held: &held::TypeLetRoles,
) -> Option<crate::ccl::ty::WitnessProjection> {
    let (lets, under) = TypeLet::peel(ty);
    let Type::WitnessProjection(projection) = under else {
        return None;
    };
    let scope = TypeLetScope {
        lets: lets.iter().map(|l| (Rc::new((*l).clone()), 0)).collect(),
        depth: 0,
        held: Rc::new(held.clone()),
        compiled: Default::default(),
    };
    let reads = ccl_utils::free_names(&projection.term);
    if scope.read_by(reads).is_empty() {
        return Some(projection.clone());
    }
    let _g = provenance::enter(
        projection.term.node_id(),
        "planning.projection_under_lets",
        provenance::Nature::Machinery,
    );
    Some(crate::ccl::ty::WitnessProjection::new(
        Rc::new(scope.compiled_form(projection.term.duplicate())),
        projection.position,
    ))
}

/// `ty`'s refined shape under the type `let`s at its root: the base, holding the `let`s it reads
/// where it reads them ([`TypeLet::innermost`]), which keeps its structure, and the refinements
/// ([`refinements_under_lets`]). `None` where `ty` is no refinement under its `let`s.
pub(crate) fn refined_under_lets(
    ty: &Type,
    held: &held::TypeLetRoles,
) -> Option<(Type, Vec<crate::ccl::Refinement>)> {
    let (lets, under) = TypeLet::peel(ty);
    match under {
        Type::Refinement(base, _) => Some((
            TypeLet::innermost_each(&lets, (**base).clone()),
            refinements_under_lets(ty, held),
        )),
        _ => None,
    }
}

/// Compile a function type's codomain. A codomain under a binder that names the input is
/// compiled in its opened form: a predicate there may hold a subterm whose type reads the
/// binder, and compiled closed, that index is carried under the crossings the compiled morphisms
/// add, where it names another function. An unnamed binder's codomain stands one binder deeper.
fn compile_codomain(
    binder: &crate::ccl::FunBinder,
    domain: &Type,
    codomain: &mut Type,
    memo: &PredMemo<PredicateContext>,
    slot: &[crate::ccl::ty::Witness],
    scope: &mut TypeLetScope,
) {
    if binder.is_none() {
        scope.depth += 1;
        compile_predicates_in_type(codomain, memo, slot, scope);
        scope.depth -= 1;
    } else {
        crate::ccl::subst::map_opened_codomain(
            &mut Solver::none(),
            binder,
            domain,
            codomain,
            |opened| compile_predicates_in_type(opened, memo, slot, scope),
        )
    }
}

/// The point-free predicate function `p : base ⇒ Bool` underlying a refinement's
/// bare predicate `__elem ▷ p` (the inverse of [`ccl_utils::bare_predicate_of_fn`]).
/// Join-condition sides use the same operation with any codomain.
/// Fast-pathed when the bare predicate is already that single application; otherwise
/// η-expands to `λ 𝑒 → bare[__elem ↦ 𝑒]`, `𝑒` fresh, and lambda-eliminates to point-free.
///
/// Lambda elimination leaves predicates alone, so `p` can still hold a lambda. A comprehension's
/// filter predicate is the filter's nest read at the element, `__elem ▷ (𝑛𝑒𝑠𝑡 ▷ uncurry(𝑛))`
/// (`src/ccl/design/ir.md`, "Several generators"), and the fast path eliminates its `p`
/// ([`eliminate_lifted`]). A membership refinement, a group-by's key domain
/// `__elem ▷ ((c ≫ λ 𝑒 → key) ▷ collection_contains)`, is carried and never executed: an
/// iteration site enumerates the collection's image instead (`iterate::membership_keys`), so its
/// `p` stays as it stands unless it holds a `defer`, from a generator called in the key, which
/// [`eliminate_lifted`] channelizes.
///
/// For a refinement, the function is a **collection**: it yields one `Bool` per element of what it
/// refines, and the runtime `Restrict` evaluates it over the extent
/// (`src/ccl/design/type-inference.md`, "A refinement predicate is a data function"). The
/// η-expanded form is where that is said, the binder being the one place a kind is written,
/// and it is said for every predicate — nothing declares the kind of a function synthesized
/// here, so `Expr::lambda`'s `Compute` would otherwise stand as the answer by default and
/// [`crate::ccl::lambda_elim`] would thread it onto every fan-out it mints. A predicate
/// reading its own source then meets that source at the incomparable kind.
///
/// `slot` is the binder telescope `base` is written under — the Σ of the collection this
/// refinement refines. It decides which data kind, not whether: a predicate under binders
/// carries them, so a witness in `base` is bound by the predicate's own type rather than
/// supplied from outside.
pub(crate) fn fn_of_bare_predicate(
    base: &Type,
    bare: &Expr,
    slot: &[crate::ccl::ty::Witness],
) -> Expr {
    if let TypedExprNode::Apply { argument, function } = &bare.node
        && matches!(&argument.node, TypedExprNode::Var(n) if n.is_elem())
        && crate::ccl::subst::free_elem_indices(function).is_empty()
    {
        let membership = matches!(
            &function.node,
            TypedExprNode::Apply { function: contains, .. }
                if is_builtin(contains, Builtin::CollectionContains)
        );
        if crate::ccl::channelize::holds_defer(function) || (!membership && holds_lambda(function))
        {
            return eliminate_lifted((**function).duplicate())
                .expect("lambda-elim of a refinement predicate");
        }
        return (**function).duplicate();
    }
    // A plain collection carries no binders; a sum carries the telescope `base` is written
    // under, since a reference names no kind and the binder is the one place a kind is
    // written (`src/ccl/design/type-inference.md`, "The witness context").
    let fun_kind = if slot.is_empty() {
        crate::ccl::ty::FunKind::Data(None)
    } else {
        crate::ccl::ty::FunKind::Data(Some(Rc::new(slot.to_vec())))
    };
    // The kind is the only part of the type chosen here. The domain is `base` and the codomain is
    // the body's own type, so a bare predicate that is already function-valued keeps the codomain
    // it has.
    //
    // The parameter is a fresh name: element references are bound by refinements alone, and
    // no lambda binds one. The rename reaches a nested refinement's `__elem^1` too
    // (`src/ccl/design/type-inference.md`, "A refinement's element is referenced by index").
    let param = Name::fresh("elem");
    let body = crate::ccl::subst::Subst::rename(Name::elem(), param.clone()).apply_expr(bare);
    // A refined operator's result type records its operands, so the body's type can read
    // `param`, and the function is then a Pi over it.
    let ty = Type::fun_over(param.clone(), base.clone(), body.ty.clone(), fun_kind);
    let lam = Expr::lambda(param, Occurrence::mint(), base.clone(), body).with_ty(ty);
    eliminate_lifted(lam).expect("lambda-elim of refinement predicate")
}

/// Point-free `term`, a term lifted out of a refinement predicate, by the passes between
/// inference and planning that it skipped while it sat in a type
/// (`src/ccl/design/optimization.md`, "Planning a lifted term").
///
/// Of those passes:
///
/// - `inline` reaches a predicate: its substitution rewrites type slots too.
/// - `transact_phase::run` and `mut_elim` find nothing to rewrite there: a predicate holds no
///   mutability statement ([`crate::ccl::ty::debug_assert_predicate_shape`]).
/// - `channelize` skips a predicate holding a `defer` block, which a generator called in a
///   filter or a key leaves there. This runs it on such a term, then letrec recognition
///   (`plan_loops`), which reads the loop channelize builds as the collection it feeds.
/// - `erase_refinements` skips predicates. This erases the lifted term's value facts before
///   `lambda_elim`, retaining the data-domain refinements that planning executes.
/// - `lambda_elim` skips predicates, and this runs it.
///
/// Debug builds assert that the result holds none of these passes' source forms.
pub(crate) fn eliminate_lifted(term: Expr) -> Result<Expr, lambda_elim::LambdaElimError> {
    let eliminated = if crate::ccl::channelize::holds_defer(&term) {
        // Channelize reported every error in a `defer` block a predicate holds
        // (`channelize::check_predicate_defers`), so this one channelizes.
        let channelized = crate::ccl::channelize::run(term)
            .unwrap_or_else(|e| panic!("channelizing a term lifted out of a predicate: {e:?}"));
        plan_loops(lambda_elim::run(crate::ccl::erase_refinements::run(
            channelized,
        ))?)
    } else {
        lambda_elim::run(crate::ccl::erase_refinements::run(term))?
    };
    #[cfg(debug_assertions)]
    if let Some(form) = pre_planning_source_form(&eliminated) {
        panic!(
            "a term lifted out of a predicate still holds a `{form}`, which a pass before \
             planning rewrites: {}",
            symbolic(&eliminated)
        );
    }
    Ok(eliminated)
}

/// Whether `e`'s term holds a lambda.
fn holds_lambda(e: &Expr) -> bool {
    let mut found = matches!(e.node, TypedExprNode::Lambda { .. });
    e.walk_children(|c| found |= !found && holds_lambda(c));
    found
}

/// The first node in `e`'s term that a pass between inference and planning rewrites
/// ([`eliminate_lifted`] lists them).
#[cfg(debug_assertions)]
fn pre_planning_source_form(e: &Expr) -> Option<&'static str> {
    use TypedExprNode as N;
    let here = match &e.node {
        N::Lambda { .. } => Some("Lambda"),
        N::Defer => Some("Defer"),
        N::Feed { .. } => Some("Feed"),
        N::Define { .. } => Some("Define"),
        N::MutDecl { .. } => Some("MutDecl"),
        N::MutWrite { .. } => Some("MutWrite"),
        N::For { .. } => Some("For"),
        N::Begin { .. } => Some("Begin"),
        N::LetRec { .. } => Some("LetRec"),
        _ => None,
    };
    let mut found = here;
    e.walk_children(|c| {
        if found.is_none() {
            found = pre_planning_source_form(c);
        }
    });
    found
}

fn compile_predicates_in_type(
    ty: &mut Type,
    memo: &PredMemo<PredicateContext>,
    slot: &[crate::ccl::ty::Witness],
    scope: &mut TypeLetScope,
) {
    // A type `let` is in scope over its body, whose refinements take its definition discharged
    // ([`TypeLetScope`]). Afterwards only a read outside the refinements keeps it, and its
    // definition compiles as a term under the `let`s around it.
    if let Type::Let(l) = ty {
        scope.lets.push((Rc::clone(l), scope.depth));
        compile_predicates_in_type(&mut Rc::make_mut(l).body, memo, slot, scope);
        scope.lets.pop();
        if !ccl_utils::inline_rewritten_let(ty)
            && let Type::Let(_) = ty
        {
            let context = PredicateContext {
                element: Type::Hole,
                lets: scope
                    .lets
                    .iter()
                    .map(|(l, at)| (l.name.clone(), Rc::clone(&l.definition), scope.depth - at))
                    .collect(),
            };
            for quoted in ty.held_terms_mut() {
                memo.rebuild(quoted, &context, |definition| {
                    compile_refinement_predicates_under(definition, memo, scope);
                    true
                });
            }
            if let Type::Let(l) = ty {
                scope.share_definition(Rc::make_mut(l));
            }
        }
        return;
    }
    let here = ty.sum().unwrap_or(&[]).to_vec();
    let extended: Vec<crate::ccl::ty::Witness> = if here.is_empty() {
        slot.to_vec()
    } else {
        slot.iter().cloned().chain(here).collect()
    };
    let slot = extended.as_slice();
    if let Type::Refinement(base, refinements) = ty {
        let base = base.clone();
        compile_refinements(refinements, &base, memo, slot, scope);
    }
    // Recurse into structural type children (refinement base, function
    // domain/codomain, tuple/record/variant elements).
    // Not `walk_children_mut`: it descends into a `FunKind`'s witness candidates, and a
    // predicate typed as a collection over a witness carries the source's candidate types in
    // its own kind — walking them re-enters the refinements this predicate came out of.
    // A binder's candidates are compiled where the binder's own type is.
    //
    // A dependent tuple's components are compiled **under the names** of the components
    // before them, then closed again. A component's predicate can hold a subterm whose type
    // reads an earlier component — a projection out of the tuple has one — and compiled
    // closed, that index is carried under the crossings the compiled morphisms add, where it
    // names another function.
    match ty {
        // A codomain is compiled in its opened form: a predicate there may hold a subterm
        // whose type reads the binder, and compiled closed, that index is carried under the
        // crossings the compiled morphisms add, where it names another function.
        Type::Fun {
            binder,
            domain,
            codomain,
            ..
        } => {
            compile_predicates_in_type(domain, memo, slot, scope);
            compile_codomain(binder, domain, codomain, memo, slot, scope);
        }
        Type::DepTuple(components) => {
            let names = crate::ccl::subst::tuple_component_names(components);
            let mut opened: Vec<(Option<Name>, Type)> = crate::ccl::subst::open_tuple_components(
                &mut Solver::none(),
                components,
                |j, _| crate::ccl::subst::Mapping::Rename(names[j].clone()),
                crate::ccl::Ids::Fresh,
            )
            .into_iter()
            .zip(&names)
            .map(|(mut t, name)| {
                compile_predicates_in_type(&mut t, memo, slot, scope);
                (Some(name.clone()), t)
            })
            .collect();
            crate::ccl::subst::close_tuple_components(
                &mut Solver::none(),
                &mut opened,
                crate::ccl::Ids::Fresh,
            );
            for ((_, component), (_, t)) in components.iter_mut().zip(opened) {
                *component = t;
            }
        }
        // A family's body is compiled under its binders' names, as a codomain is.
        Type::Family { binders, body } => {
            for (_, t) in binders.iter_mut() {
                compile_predicates_in_type(t, memo, slot, scope);
            }
            crate::ccl::subst::map_opened_family_body(
                &mut Solver::none(),
                binders,
                body,
                |opened| compile_predicates_in_type(opened, memo, slot, scope),
            );
        }
        _ => ty.walk_children_mut(|child| compile_predicates_in_type(child, memo, slot, scope)),
    }
}

/// Compile each refinement of a set against the element type it sees in the restrict
/// pipeline planning will build for this domain — `base` narrowed by the refinements
/// applied before it. `wrap_with_iterate` builds that pipeline from the same
/// application order, so the compiled predicates and the pipeline's types
/// agree. For a cast target's refinements, `base` is the cast value's domain (the
/// assertion base — see [`compile_refinement_predicates`]).
fn compile_refinements(
    refinements: &mut RefinementSet,
    base: &Type,
    memo: &PredMemo<PredicateContext>,
    slot: &[crate::ccl::ty::Witness],
    scope: &TypeLetScope,
) {
    // Indexed by physical position (`application_elem_types`), because the
    // rewrite below walks the set in place and the application order is a
    // *permutation* of the physical one.
    let elem_tys = crate::ccl::application_elem_types(refinements.as_slice(), base);
    refinements.rewrite_each(|i, refinement| {
        let base_ctx = &elem_tys[i];
        let context = PredicateContext {
            element: base_ctx.clone(),
            lets: scope
                .read_by(
                    ccl_utils::free_names(&refinement.predicate)
                        .into_iter()
                        .chain(crate::ccl::subst::type_free_vars(base_ctx)),
                )
                .into_iter()
                .map(|(l, at)| (l.name.clone(), Rc::clone(&l.definition), scope.depth - at))
                .collect(),
        };
        memo.rebuild(refinement, &context, |bare| {
            // The predicate takes the form a compiled predicate takes under the type `let`s. A
            // membership is carried rather than compiled ([`fn_of_bare_predicate`]), so it keeps
            // reading the definitions by the names the type holds them under.
            let carried = matches!(
                &bare.node,
                TypedExprNode::Apply { function, .. }
                    if matches!(&function.node, TypedExprNode::Apply { function: contains, .. }
                        if is_builtin(contains, Builtin::CollectionContains))
                        && !crate::ccl::channelize::holds_defer(function)
            );
            if !carried {
                *bare = scope.compiled_form(std::mem::take(bare));
            }
            // Normalize the bare predicate to `__elem ▷ p` with `p` point-free:
            // recover the predicate function and re-wrap it. This keeps the stored
            // predicate in the single bare form while pinning a point-free core, so
            // the iterate/restrict producers (built from the same `p`) carry a
            // structurally-identical refinement to the cast demand they satisfy.
            let referenced: HashSet<Name> = ccl_utils::free_names_in_value(bare)
                .into_iter()
                .filter(Name::is_synthetic_pair)
                .collect();
            let p = fn_of_bare_predicate(base_ctx, bare, slot);
            let mut compiled = ccl_utils::bare_predicate_of_fn(base_ctx, p);
            // The compiled predicate's own sub-expressions can carry *nested*
            // refinements (a filter over an already-filtered source: the inner
            // refinement rides a sub-expression's type slot inside this predicate).
            // `Type::walk_children_mut` below does not descend into a predicate term,
            // so compile those here, sharing the memo, under the type `let`s around this one:
            // a type `let`'s definition reads no element, so the predicate stands where its type does.
            compile_refinement_predicates_under(&mut compiled, memo, &mut scope.clone());
            // The producer/consumer refinement match (`sum`'s domain vs. its feed, a
            // compose adjacency) compares *distinct* predicate `Rc`s — the memo only
            // dedups occurrences sharing one `Rc`. That match rests on compilation
            // being a deterministic value function, which requires that lambda
            // elimination's freshly-minted `__pair` (`Uid::fresh()`) never survive
            // into the compared *term*. It legitimately survives as a `Fun.name` Pi
            // binder in a type slot (which `eq_term_modulo_ty_slots` is type-blind
            // to), so the check is term-only. A `__pair` the predicate read before
            // compiling is not one this compilation minted: it is the binder of an
            // enclosing correlated site, which a type under that site's function
            // names as it would a user binder, so the check exempts exactly those.
            // Enforced in every build: a predicate this skipped in release is one whose
            // producer/consumer match compares terms that are not value functions, and
            // that mismatch surfaces later as an unrelated operator-conversion failure.
            assert!(
                !term_mentions_pair_binder(&compiled, &referenced),
                "a `__pair` binder survived into a compiled predicate term, \
                 breaking the value-function property the structural \
                 producer/consumer match relies on: {}",
                symbolic(&compiled)
            );
            *bare = compiled;
            true
        });
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::ccl_utils::trivially_true_predicate;
    use crate::ccl::context::Phase;
    use crate::ccl::provenance::{NodeId, PhaseScope, ProvenanceTable, TableSession};
    use crate::ccl::{BaseType, Lit, Name};
    use std::collections::HashSet;

    /// Every id reachable from `e`, main tree only.
    fn ids_of(e: &Expr) -> HashSet<NodeId> {
        let mut out = HashSet::new();
        fn go(e: &Expr, out: &mut HashSet<NodeId>) {
            out.insert(e.node_id());
            e.walk_children(&mut |c| go(c, out));
        }
        go(e, &mut out);
        out
    }

    /// Whether walking `parents` back from `id` reaches an id in `roots` before
    /// running out of rows.
    fn resolves_into(table: &ProvenanceTable, id: NodeId, roots: &HashSet<NodeId>) -> bool {
        let mut frontier = vec![id];
        let mut seen = HashSet::new();
        while let Some(n) = frontier.pop() {
            if roots.contains(&n) {
                return true;
            }
            if !seen.insert(n) {
                continue;
            }
            frontier.extend_from_slice(table.parents(n));
        }
        false
    }

    /// Raise `bare` out of a predicate under a recording naming `site`, and
    /// report which of the result's nodes reach the predicate and which reach
    /// the site.
    fn raise(bare: &Expr, site: NodeId) -> (ProvenanceTable, Expr, HashSet<NodeId>) {
        let pred_ids = ids_of(bare);
        let session = TableSession::install();
        let raised = {
            let _scope = PhaseScope::enter(Phase::Planning);
            let _g = provenance::enter(site, "test.raise", provenance::Nature::Machinery);
            // No witness slot: the base is a scalar, so the raised function is over no
            // index a Σ named.
            fn_of_bare_predicate(&Type::Base(BaseType::Int), bare, &[])
        };
        (session.into_table(), raised, pred_ids)
    }

    /// **Both paths of `fn_of_bare_predicate` attribute the raised predicate to
    /// the predicate**, never to the term-tree site the recording names.
    ///
    /// The fast path clones, and a clone's copy names the node it was freshened
    /// from, so the predicate's parentage rides along by construction. The slow
    /// path η-expands and lambda-eliminates, minting a `Lambda` that descends
    /// from the site — but that wrapper is consumed by the elimination rather
    /// than placed, so it composes away as a transient and every node that
    /// reaches the output still resolves into the predicate.
    ///
    /// This is what makes the two agree. Before `lambda_elim` recorded, the
    /// slow path's whole product landed on the site, because the sub-run's
    /// mints fell through to the enclosing recording.
    #[test]
    fn both_raising_paths_attribute_the_predicate_to_the_predicate() {
        let int_ty = Type::Base(BaseType::Int);
        let bool_ty = Type::Base(BaseType::Bool);
        let elem = || Expr::var(Name::elem()).with_ty(int_ty.clone());
        // A real `𝐷 ⇒ Bool`, so the η-expansion the slow path builds is
        // well-typed.
        let pred_fn = |domain: Type| trivially_true_predicate(domain);

        // Fast path: already `__elem ▷ p`, so the raise is a single clone of `p`.
        let fast = Expr::apply(elem(), pred_fn(int_ty.clone())).with_ty(bool_ty.clone());
        // Slow path, constant: `__elem` is not free, so elimination emits
        // `const(e)` and the η-wrapper never reaches the output.
        let slow_const = Expr::lit(Lit::Bool(false)).with_ty(bool_ty.clone());
        // Slow path, `__elem` free: `__elem ▷ p ▷ q`, whose outer argument is an
        // application rather than the bare `__elem`, so the fast path declines.
        let slow_free = Expr::apply(
            Expr::apply(elem(), pred_fn(int_ty.clone())).with_ty(bool_ty.clone()),
            pred_fn(bool_ty.clone()),
        )
        .with_ty(bool_ty.clone());

        for (name, bare) in [
            ("fast", fast),
            ("slow/constant", slow_const),
            ("slow/free", slow_free),
        ] {
            let site = NodeId::fresh();
            let (table, raised, pred_ids) = raise(&bare, site);
            let site_only = HashSet::from([site]);
            for id in ids_of(&raised) {
                assert!(
                    resolves_into(&table, id, &pred_ids),
                    "{name}: {id:?} does not resolve into the predicate",
                );
                assert!(
                    !resolves_into(&table, id, &site_only),
                    "{name}: {id:?} resolves to the term-tree site instead",
                );
            }
        }
    }
}
