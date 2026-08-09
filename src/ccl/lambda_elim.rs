//! Lambda elimination pass for CCL.
//!
//! Rewrites all [`TypedExprNode::Lambda`] nodes in a CCL expression into a point-free
//! composition of primitive combinators, following the Cartesian Closed Category
//! (CCC) structure described in `docs/operational-semantics/lowering.md`.
//!
//! # Entry point
//!
//! [`run`] eliminates all lambdas and then simplifies to a fixed point.
//!
//! # Outside-in ordering
//!
//! Lambda elimination is applied **outside-in**: the outermost lambda is
//! handled before inner ones. This ordering is mandatory — an inner lambda
//! that captures a free variable of an outer lambda must be combined with it
//! via the nested-lambda rule. Eliminating inside-out would
//! treat a captured variable as a constant, which is incorrect.
//!
//! # Primitive combinators
//!
//! The output uses [`TypedExprNode::Builtin`] for primitive functions and
//! [`TypedExprNode::Proj`] for tuple/record projections:
//!
//! | Symbol | AST shape | Meaning |
//! |--------|-----------|---------|
//! | `id` | `Builtin(Id)` | identity morphism |
//! | `.0`, `.1`, … | `Proj(Index(n))` | tuple projection |
//! | `.field` | `Proj(Field(s))` | record field projection |
//! | `f ≫ g` | `Compose([f, g])` | left-to-right composition |
//! | `⟨f, g⟩` | `Apply(Tuple([f, g]), Builtin(Zip))` | product/fanout |
//! | `curry(f)` | `Apply(f, Builtin(Curry))` | curry |
//! | `const(c)` | `Apply(c, Builtin(Const))` | constant lift |
//! | `restrict` | `Builtin(Restrict)` | domain restriction |
//! | `apply` | `Builtin(Apply)` | function application as morphism |
//! | `map` | `Builtin(Map)` | post-composition |
//! | `sum`, `max` | `Builtin(Sum)`, `Builtin(Max)` | fold/reduce |
//! | `converse` | `Builtin(Converse)` | grouping by key |
//! | `uncurry` | `Builtin(Uncurry)` | uncurry |
//! | `compose` | `Builtin(Compose)` | composition as first-class morphism |
//! | `add`/`sub`/… (and compares / logic) | `Builtin(BinOp(op))` for `op: BinOpKind` | binary scalar ops |
//! | `neg`, `not_fn` | `Builtin(Neg)`, `Builtin(NotFn)` | unary scalar ops |

use std::rc::Rc;

use crate::ccl::ccl_utils::{
    apply_primitive, cast_target_refinement, flatten_trailing_value_case, is_free,
    is_free_in_value, refine_with, strip_refinements, synthesize_arm_predicate, typed_compose,
};
use crate::ccl::infer::{dbg_typecheck_mv, debug_typecheck};
use crate::ccl::simplify::simplify;
use crate::ccl::{BaseType, Branch, Builtin, FieldKey, Lit, Name, Refinement};
use crate::ccl::{Expr, Type, TypedExpr, TypedExprNode, symbolic::symbolic};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors that can occur during lambda elimination.
#[derive(Debug, Clone, PartialEq)]
pub enum LambdaElimError {
    /// A node kind inside a lambda body is not yet handled by the elimination
    /// rules.  Currently: `Case`, `Loop`, and `HashJoin` refinements.
    Unsupported(String),
}

impl std::fmt::Display for LambdaElimError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(msg) => write!(f, "lambda elimination: unsupported: {msg}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Eliminate all [`TypedExprNode::Lambda`] nodes and simplify the result to a fixed point.
///
/// The input must be a well-formed, fully type-inferred CCL expression
/// (as produced by [`crate::ccl::infer::infer`]).
///
/// Returns `Ok(point_free_expr)` where the result contains no `Lambda` nodes.
pub fn run(expr: Expr) -> Result<Expr, LambdaElimError> {
    let mut ctx = ElimContext::new();
    let point_free = elim_lambdas(&mut ctx, expr)?;
    // Per design §6.3, lambda elimination **does not descend into refinement
    // predicates** — they stay as bare boolean expressions (over the implicit
    // `REFINEMENT_BINDER`) in their type slots. Compiling them is deferred to
    // planning, which wraps each in `λ __elem → …` and runs the full lambda-elim
    // → simplify (→ planning) sub-pipeline when a refined type is iterated
    // (`planning::compile_refinement_predicates`).
    let mut simplified = simplify(point_free);
    // Predicate rewrites during elimination/simplification rebuild the
    // immutable predicate on each node's `expr.ty`; re-sync every `Cast`'s
    // `target` slot to its `expr.ty` so the post-pass typecheck's
    // reconstruction matches the recorded type.
    crate::ccl::ccl_utils::sync_cast_targets(&mut simplified);
    Ok(simplified)
}

// ---------------------------------------------------------------------------
// Elimination context
// ---------------------------------------------------------------------------

/// Mutable state threaded through lambda elimination.
///
/// Currently stateless — the nested-lambda rule mints its `__pair` binder
/// straight from [`Name::pair`] (uid-identified, no counter to carry) — but
/// kept as the threaded context the elimination walk already expects.
struct ElimContext {}

impl ElimContext {
    fn new() -> Self {
        Self {}
    }

    /// A fresh `__pair` binder for the nested-lambda rule.
    fn fresh_pair_name(&mut self) -> Name {
        Name::pair()
    }
}

// ---------------------------------------------------------------------------
// Primitive combinator constructors
// ---------------------------------------------------------------------------

/// Build [`Builtin::Id`]: the identity morphism.
pub(crate) fn id() -> Expr {
    Expr::builtin(Builtin::Id)
}

/// Build `f ≫ g`: left-to-right function composition.
pub(crate) fn compose(f: Expr, g: Expr) -> Expr {
    Expr::compose(vec![f, g])
}

/// Build a [`TypedExprNode::Tuple`] whose type is inferred from its elements.
///
/// Sets the node's type to `Type::Tuple([e.ty for e in elts])`, using
/// [`Type::Hole`] for any element whose type is not yet known.
pub(crate) fn typed_tuple(elts: Vec<Expr>) -> Expr {
    let ty = Type::Tuple(elts.iter().map(|e| e.ty.clone()).collect());
    dbg_typecheck_mv(Expr::tuple(elts).with_ty(ty))
}

/// Build `⟨f, g⟩`: the product/fanout `zip(f, g)` using the [`Builtin::Zip`]
/// combinator.
///
/// Represented as `Apply { argument: Tuple([f, g]), function: Builtin(Zip) }`,
/// i.e. `(f, g) ▷ zip`.  Annotates all nodes with concrete types when available.
pub(crate) fn zip_pair(f: Expr, g: Expr) -> Expr {
    let result_ty = zip_pair_ty(&f, &g);
    let inner_tuple = typed_tuple(vec![f, g]);
    let zip_fn_ty = fun_ty_or_hole(&inner_tuple.ty, &result_ty);
    let zip_var = Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty);
    dbg_typecheck_mv(Expr::apply(inner_tuple, zip_var).with_ty(result_ty))
}

/// Build `curry(f)`: `f ▷ curry` = `Apply { argument: f, function: Builtin(Curry) }`.
///
/// Annotates the curry built-in with its type when `f` has a concrete function type.
pub(crate) fn curry(f: Expr) -> Expr {
    // If f: Tuple([A, B]) → C, then curry(f): A → (B → C)
    let curry_result = match &f.ty {
        Type::Fun {
            domain, codomain, ..
        } => match domain.as_ref() {
            Type::Tuple(elts) if elts.len() >= 2 => Type::fun(
                elts[0].clone(),
                Type::fun(elts[1].clone(), *codomain.clone()),
            ),
            _ => Type::Hole,
        },
        _ => Type::Hole,
    };
    let curry_fn_ty = fun_ty_or_hole(&f.ty, &curry_result);
    let curry_var = Expr::builtin(Builtin::Curry).with_ty(curry_fn_ty);
    Expr::apply(f, curry_var).with_ty(curry_result)
}

/// Build `const(c)`: `c ▷ const` = `Apply { argument: c, function: Builtin(Const) }`.
///
/// Leaves the const built-in untyped; use the typed inline form in `elim_lambda`
/// when the result type (param domain) is known.
pub fn const_(c: Expr) -> Expr {
    Expr::apply(c, Expr::builtin(Builtin::Const))
}

// Free-variable check lives in [`crate::ccl::ccl_utils`]: `is_free` is a
// thin wrapper around `count_free`, which counts occurrences across the
// AST and inside refinement predicates carried by types.  Imported at the
// top of this module.

// ---------------------------------------------------------------------------
// Substitution
// ---------------------------------------------------------------------------

/// Replace every free occurrence of `Var(name)` in `expr` with `replacement`.
///
/// A thin wrapper over the uniform engine's in-place mode
/// ([`crate::ccl::subst::Subst::discharge_in_place`]): one traversal over terms
/// *and* type slots, each predicate rebuilt as a fresh `Rc` with the engine's
/// memo re-pointing occurrences that shared one term so the rewrite is observed
/// uniformly, `Compose` types recomputed from the rewritten elements. Shadowing
/// stops the descent exactly as before (an inlined copy of a lambda can rebind
/// the same `Name`, so the discipline is still load-bearing); capture is
/// impossible under the Barendregt convention and the engine asserts it.
pub(crate) fn substitute(expr: Expr, name: &Name, replacement: &Expr) -> Expr {
    debug_typecheck(&expr);
    let mut expr = expr;
    crate::ccl::subst::Subst::discharge_in_place(&mut expr, name, replacement);
    debug_typecheck(&expr);
    expr
}

// ---------------------------------------------------------------------------
// BinOp desugaring
// ---------------------------------------------------------------------------

// `BinOpKind` and `UnaryOpKind` are mapped to the corresponding [`Builtin`]
// variant via [`Builtin::for_binop`] / [`Builtin::for_unaryop`].

/// Compute `Fun(domain, codomain)`, returning [`Type::Hole`] if either
/// component is [`Type::Hole`] or [`Type::Infer`].
///
/// Used throughout lambda elimination to set result types only when concrete
/// type information is available, leaving [`Type::Hole`] otherwise so the
/// post-elimination inference pass can fill in the gaps without conflict.
pub(crate) fn fun_ty_or_hole(domain: &Type, codomain: &Type) -> Type {
    if matches!(domain, Type::Hole | Type::Infer(_))
        || matches!(codomain, Type::Hole | Type::Infer(_))
    {
        Type::Hole
    } else {
        Type::fun(domain.clone(), codomain.clone())
    }
}

/// Compute the type of `zip(f, g): A → (B, C)` from `f: A → B` and `g: A → C`.
///
/// Returns [`Type::Hole`] if either argument does not have a concrete function
/// type; inference will fill in the gaps in that case.
pub(crate) fn zip_pair_ty(f: &Expr, g: &Expr) -> Type {
    match (&f.ty, &g.ty) {
        (
            Type::Fun {
                domain: a,
                codomain: b,
                ..
            },
            Type::Fun {
                domain: _,
                codomain: c,
                ..
            },
        ) => Type::fun(*a.clone(), Type::Tuple(vec![*b.clone(), *c.clone()])),
        _ => Type::Hole,
    }
}

// ---------------------------------------------------------------------------
// Filter-pattern helpers
// ---------------------------------------------------------------------------

/// Return `true` if `body` is a two-branch Case matching the filter pattern:
/// `{ [guard → action, true → unit] }`.
///
/// Used by [`elim_lambdas_impl`] to detect `Compose([src, Lambda(x, filter_body)])`
/// and lower it to a restricted source composition instead of a plain lambda elimination.
///
/// **Shape constraint**: the body must be exactly a `Case` at the top level.
/// If the loop body has leading `Let` bindings (`let y = f(x) in Case { … }`),
/// the Case is nested under a `Let` and this function returns `false`, so the
/// loop compiles via the general path (correct but no `Restrict` operator).
/// A follow-up could peel leading `Let` nodes before the pattern check.
fn is_filter_case_body(body: &Expr) -> bool {
    if let TypedExprNode::Case {
        scrutinee: None,
        branches,
    } = &body.node
    {
        branches.len() == 2
            && branches.iter().all(|b| b.pattern.is_none())
            && matches!(&branches[1].guard.node, TypedExprNode::Lit(Lit::Bool(true)))
            && matches!(&branches[1].body.node, TypedExprNode::Lit(Lit::Unit))
    } else {
        false
    }
}

/// Extract `(guard, action)` from a two-branch filter-pattern Case body.
///
/// Panics if `body` is not a filter-pattern Case; call [`is_filter_case_body`] first.
fn extract_filter_case(body: Expr) -> (Expr, Expr) {
    if let TypedExprNode::Case { mut branches, .. } = body.node {
        let first = branches.remove(0);
        (first.guard, first.body)
    } else {
        panic!("extract_filter_case: expected a filter-pattern Case body")
    }
}

// ---------------------------------------------------------------------------
// Value-selecting Case compilation (the scalar C-form)
// ---------------------------------------------------------------------------

/// Returns `true` if `ty` (peeling outer refinements) is a *collection* — a
/// data or compute function. A value-selecting `Case` whose arms are collections
/// takes the data-typed gate fan-out; a `Case` returning a scalar / compute value
/// takes the C-form below.
fn is_collection_result(ty: &Type) -> bool {
    matches!(strip_refinements(ty), Type::Fun { .. })
}

/// Compile a guard-based **value-selecting** `Case` (a ternary or `if`/`elif`/
/// `else` that returns a scalar / compute value) to the **C-form**: a union of
/// gated one-shot lifts over the `UIntRange(1)` driver, extracted by
/// `final_or_default`.
///
/// ```text
/// Case{scrutinee: None, [g₀ → e₀; …; gₙ → eₙ]}   (gₙ is the exhaustive trailing `true`)
///   ⟹  (⧺ᵢ const(eᵢ) : {UIntRange(1) | π̂ᵢ} ⤇ V,  eₙ) ▷ final_or_default
/// ```
///
/// where `π̂ᵢ = gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ` ([`synthesize_arm_predicate`]). Each arm is a
/// constant lift of its value over a one-position driver whose domain is
/// *refined by the arm's first-match gate*. The gate is **constant in the
/// driver element** (see `src/interpreter/design-operators.md`): it does not
/// vary with the driver position, so the whole one-element domain survives (gate
/// holds) or is emptied (gate fails). The partition is exhaustive (the trailing
/// `true` guard), so exactly one arm survives and the union has one element;
/// `final_or_default`'s default `eₙ` is a type anchor for the empty case that
/// cannot occur. The outer type is the `Case`'s own value type `V`, unchanged,
/// so lambda_elim's type-preservation assertion holds.
fn build_value_case_cform(
    ctx: &mut ElimContext,
    branches: Vec<Branch>,
    result_ty: Type,
) -> Result<Expr, LambdaElimError> {
    // Exhaustiveness invariant: a value-selecting `Case` must be total (a
    // trailing `true` guard). `default_body` below becomes `final_or_default`'s
    // default, and the whole first-match/`final_or_default` argument is sound only
    // if the last arm is that unconditional fallback — a non-exhaustive `Case`
    // reaching here would silently return the last arm's value with its gate
    // false (an empty union → the wrong default). Lowering always appends the
    // `true` complement (a ternary's `else`); assert it at this boundary.
    debug_assert!(
        branches
            .last()
            .is_some_and(|b| matches!(&b.guard.node, TypedExprNode::Lit(Lit::Bool(true)))),
        "value-selecting Case must be exhaustive (trailing `true` guard)"
    );
    let bool_ty = Type::Base(BaseType::Bool);
    let driver_dom = Type::UIntRange(1);

    let mut prior_guards: Vec<Expr> = Vec::new();
    let mut arms: Vec<Expr> = Vec::new();
    let mut arm_domains: Vec<Type> = Vec::new();
    let mut default_body: Option<Expr> = None;

    for b in branches {
        let guard = elim_lambdas(ctx, b.guard)?;
        let body = elim_lambdas(ctx, b.body)?;
        // First-match gate π̂ᵢ, lifted to a constant-in-element predicate
        // `const(π̂ᵢ) : UIntRange(1) ⇒ Bool` over the driver. `synthesize_arm_predicate`
        // combines the (already point-free) guards with raw `and`/`not` nodes, so
        // eliminate once more to desugar those into applied-combinator form.
        let gate_value = elim_lambdas(ctx, synthesize_arm_predicate(&guard, &prior_guards))?;
        prior_guards.push(guard);
        let gate_fn = apply_primitive(
            gate_value,
            Builtin::Const,
            Type::fun(driver_dom.clone(), bool_ty.clone()),
        );
        // {UIntRange(1) | π̂ᵢ} — the gated one-shot driver domain. A trivially-true
        // gate (a leading `if True`) leaves the driver unrefined (always fires).
        let refined_dom = refine_with(driver_dom.clone(), &gate_fn);
        arm_domains.push(refined_dom.clone());
        // const(eᵢ) : {UIntRange(1) | π̂ᵢ} ⤇ V — lift the value over the gated driver.
        let arm = apply_primitive(
            body.clone(),
            Builtin::Const,
            Type::data_fun(refined_dom, result_ty.clone()),
        );
        arms.push(arm);
        default_body = Some(body);
    }

    // A one-branch value `Case` denotes just that branch's value.
    let default_body = default_body.expect("value-selecting Case has at least one branch");
    if arms.len() == 1 {
        return Ok(default_body);
    }

    // Union domain = Variant({Index(i): {UIntRange(1)|π̂ᵢ}}) — the same tagged
    // union `emit_collection_union` produces, so op-conversion's `UnionOperator`
    // dispatches to the surviving arm.
    let union_dom = Type::Variant(
        arm_domains
            .into_iter()
            .enumerate()
            .map(|(i, d)| (FieldKey::Index(i), d))
            .collect(),
    );
    let union_ty = Type::data_fun(union_dom, result_ty.clone());
    let union = Expr::collection_union(arms).with_ty(union_ty.clone());

    // (union, eₙ) ▷ final_or_default : V
    let tuple_ty = Type::Tuple(vec![union_ty, result_ty.clone()]);
    let arg = Expr::tuple(vec![union, default_body]).with_ty(tuple_ty);
    Ok(apply_primitive(arg, Builtin::FinalOrDefault, result_ty))
}

/// The element (codomain) type a collection-valued `Case` produces — the codomain
/// of the arms' joined data function. The arms share one domain (a join at distinct
/// domains is rejected at inference), so they share one codomain. Peels outer
/// refinements first.
fn collection_value_ty(ty: &Type) -> Type {
    match strip_refinements(ty) {
        Type::Fun { codomain, .. } => *codomain,
        other => other,
    }
}

/// Compile a guard-based **value-selecting** `Case` whose arms are *collections*
/// (data-typed) to the **gate fan-out**: each arm's whole collection,
/// restricted by its constant first-match gate, unioned.
///
/// ```text
/// Case{scrutinee: None, [g₀ → xs₀; …; gₙ → xsₙ]}   ⟹   ⧺ᵢ (xsᵢ | π̂ᵢ)
/// ```
///
/// where `π̂ᵢ = gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ` ([`synthesize_arm_predicate`]). Each gate is
/// **constant in the element** (see the C-form above), so an arm's collection
/// survives whole (gate holds) or is emptied (gate fails); the partition is
/// exhaustive, so exactly one arm is non-empty and the union is that arm's
/// collection. The union's type is the tagged `Variant`-domain data function —
/// the same shape `emit_collection_union` gives a `++`, which the strict wall
/// reconciles against the arms' joined data function by `is_index_partition_of`
/// (`src/ccl/design/type-inference.md`, "The domain join is a Σ"). The arms all share
/// one domain — a join at distinct domains is rejected at inference — so every leg's
/// payload is that one domain under its own gate.
fn build_value_case_fanout(
    ctx: &mut ElimContext,
    branches: Vec<Branch>,
    result_ty: Type,
) -> Result<Expr, LambdaElimError> {
    // Exhaustiveness invariant (as in [`build_value_case_cform`]): a total value
    // selection has a trailing `true` guard, so exactly one arm survives the
    // first-match partition and the union is that arm's whole collection. A
    // non-exhaustive `Case` here would leave the union empty on the uncovered
    // path (e.g. `sum` = 0) — a silent miscompile, not a rejection.
    debug_assert!(
        branches
            .last()
            .is_some_and(|b| matches!(&b.guard.node, TypedExprNode::Lit(Lit::Bool(true)))),
        "value-selecting Case (fan-out) must be exhaustive (trailing `true` guard)"
    );
    let bool_ty = Type::Base(BaseType::Bool);
    let value_ty = collection_value_ty(&result_ty);

    let mut prior_guards: Vec<Expr> = Vec::new();
    let mut arms: Vec<Expr> = Vec::new();

    for b in branches {
        let guard = elim_lambdas(ctx, b.guard)?;
        let coll = elim_lambdas(ctx, b.body)?;
        let arm_dom = coll.ty.domain().ok_or_else(|| {
            LambdaElimError::Unsupported(format!(
                "value-selecting Case arm is not a plain collection (nested conditional \
                 collections are not yet supported): {}",
                coll.ty
            ))
        })?;
        // First-match gate, lifted to a constant-in-element predicate over the
        // arm's own domain, then attached as a domain refinement (planning
        // materializes it as the arm's `restrict`).
        let gate_value = elim_lambdas(ctx, synthesize_arm_predicate(&guard, &prior_guards))?;
        prior_guards.push(guard);
        let gate_fn = apply_primitive(
            gate_value,
            Builtin::Const,
            Type::fun(arm_dom.clone(), bool_ty.clone()),
        );
        let refined_dom = refine_with(arm_dom, &gate_fn);
        arms.push(coll.with_ty(Type::data_fun(refined_dom, value_ty.clone())));
    }

    // A one-branch collection `Case` denotes just that arm's collection — no union
    // needed, and nothing for the partition rule to reconcile.
    if arms.len() == 1 {
        return Ok(arms.pop().unwrap());
    }

    // The node keeps the `Case`'s own type — the arms' joined data function `D ⤇ V`
    // — so lambda_elim stays type-preserving. The strict `typecheck` then reconciles
    // the union's structural `Variant([{D | π̂ᵢ}])` domain against that `D` via
    // `is_index_partition_of` (`src/ccl/design/type-inference.md`, "The domain join
    // is a Σ"). Op-conversion compiles the union straight to a `UnionOperator`
    // from its operands, whose domains are concrete domains.
    Ok(Expr::collection_union(arms).with_ty(result_ty))
}

// ---------------------------------------------------------------------------
// Core: elim_lambda
// ---------------------------------------------------------------------------

/// Eliminate `param` from `body`, eliminating any lambdas that use `param` as
/// a free variable along the way. Lambdas that are constant in `param` are not
/// eliminated.
///
/// `param_ty` is the type of the lambda parameter being eliminated. It is used
/// to set [`TypedExpr::ty`] on every new expression created, so that the
/// post-elimination type-inference pass has concrete type anchors to work from.
///
/// **Precondition**: `body` must not itself be the lambda being eliminated —
/// i.e. this function is called on the body of a `Lambda { param, body, .. }`.
fn elim_lambda(
    ctx: &mut ElimContext,
    param: &Name,
    param_ty: &Type,
    body: Expr,
) -> Result<Expr, LambdaElimError> {
    stacker::maybe_grow(512 * 1024, 1024 * 1024, || {
        elim_lambda_impl(ctx, param, param_ty, body)
    })
}

fn elim_lambda_impl(
    ctx: &mut ElimContext,
    param: &Name,
    param_ty: &Type,
    body: Expr,
) -> Result<Expr, LambdaElimError> {
    log::trace!("elim_lambda: eliminating λ {param}: {}", symbolic(&body));
    debug_typecheck(&body);
    // Capture the body's type before consuming it; the result of eliminating
    // `λ param → body` is a morphism `param_ty → body_ty`. When `param` is
    // still free in `body_ty` (a refinement predicate closes over it — the
    // dependent-application shape), the morphism's type must bind it as a Pi:
    // the eliminated binder no longer exists as a term binder, so without the
    // Pi the occurrences dangle and the checker's α-alignment has nothing to
    // bind them against.
    let body_ty = body.ty.clone();
    let result_ty = match fun_ty_or_hole(param_ty, &body_ty) {
        Type::Fun {
            domain,
            codomain,
            kind,
            ..
        } if crate::ccl::subst::type_free_vars(&body_ty).contains(param) => Type::Fun {
            name: Some(param.clone()),
            kind,
            domain,
            codomain,
        },
        t => t,
    };
    assert_ne!(Type::Hole, result_ty);

    // Constant: λ x → e  ⟹  const(e)  when x ∉ fv(e)
    // Checked before pattern-matching because a nested lambda that does not
    // reference param should also be treated as a constant.
    if !is_free(param, &body) {
        // const: T → (A → T) where T = body.ty and result_ty = A → T
        let const_fn_ty = fun_ty_or_hole(&body.ty, &result_ty);
        let const_var = Expr::builtin(Builtin::Const).with_ty(const_fn_ty);
        let result = Expr::apply(body, const_var).with_ty(result_ty);
        debug_typecheck(&result);
        return Ok(result);
    }

    // Pi-const: λ x → e  ⟹  const(e) : (x: param_ty) ⇒ e.ty  when `x` is free
    // only in `e`'s **type** (a refinement closes over it) and not in its value.
    // The value is a `const`; the binder rides the type as a Pi binder — a
    // dependent refinement. This generalizes the cast-wrapped-lambda arm below
    // (which the comment there flags as a special case to subsume): after the
    // pairing rule rewrites a captured partition predicate onto a pair domain,
    // the residual `λ __pair → <point-free value>` has its binder free only in
    // that refinement. The cast-wrapped-lambda shape keeps its dedicated arm
    // (it also point-frees the cast's inner lambda), so exclude it here.
    let body_is_cast_lambda = matches!(
        &body.node,
        TypedExprNode::Cast { value, .. } if matches!(value.node, TypedExprNode::Lambda { .. })
    );
    if !body_is_cast_lambda && !is_free_in_value(param, &body) {
        let result_pi = Type::pi(param, param_ty.clone(), body.ty.clone());
        let const_fn =
            Expr::builtin(Builtin::Const).with_ty(Type::fun(body.ty.clone(), result_pi.clone()));
        let result = Expr::apply(body, const_fn).with_ty(result_pi);
        debug_typecheck(&result);
        return Ok(result);
    }

    let TypedExpr {
        node: body_node, ..
    } = body;
    let result = match body_node {
        // Identity: λ x → x  ⟹  id
        TypedExprNode::Var(ref name) if name == param => Ok(id().with_ty(result_ty)),

        // Nested lambda: λ x → λ y → body  ⟹  curry(λ(x,y) → body)
        TypedExprNode::Lambda {
            param: y_binding,
            body: inner_body,
        } => {
            let y = y_binding.name;
            let y_ty = y_binding.ty.clone();

            // Merge λ x → λ y into λ __pair where x = pair[0], y = pair[1].
            // The pair variable has type (param_ty, y_ty).
            let pair = ctx.fresh_pair_name();
            let pair_ty = Type::Tuple(vec![param_ty.clone(), y_ty.clone()]);
            // Annotate the projection morphisms with their concrete types so that
            // downstream type computations (e.g. zip_pair_ty) can see the domain.
            // Also annotate the pair variable itself so that the identity rule in
            // the recursive call can produce a typed `id` morphism.
            let proj0_ty = Type::fun(pair_ty.clone(), param_ty.clone());
            let proj1_ty = Type::fun(pair_ty.clone(), y_ty.clone());
            let sub_x = Expr::apply(
                Expr::var(&pair).with_ty(pair_ty.clone()),
                Expr::proj_index(0).with_ty(proj0_ty.clone()),
            )
            .with_ty(param_ty.clone());
            let sub_y = Expr::apply(
                Expr::var(&pair).with_ty(pair_ty.clone()),
                Expr::proj_index(1).with_ty(proj1_ty.clone()),
            )
            .with_ty(y_ty.clone());
            let merged = substitute(substitute(*inner_body, &y, &sub_y), param, &sub_x);

            let inner_elim = elim_lambda(ctx, &pair, &pair_ty, merged)?;
            Ok(dbg_typecheck_mv(curry(inner_elim)))
        }

        // Cast-wrapped lambda: `λ param → cast(λ y → body, {𝐷 | 𝑝} ⇒ 𝑉)` — the
        // group-by / for-filter shape lowering emits (see
        // [`crate::ccl::ccl_utils::make_cast`]), where the cast's refinement `𝑝`
        // may reference the outer binder `param` (correlated, the groupby
        // shape) or only local binders (uncorrelated, the for-filter shape).
        // Handled by the Pi-const path below.
        TypedExprNode::Cast { value, target }
            if matches!(value.node, TypedExprNode::Lambda { .. }) =>
        {
            // Pi-aware path: the outer binder `param` is dependent solely
            // through the cast's *refinement* (the group-by shape — the binder
            // appears in the refinement predicate, not in the cast's value).
            // Emit `const(cast(<point-free inner>))` with the Pi type
            // `(param) ⇒ {D | p} ⇒ V`: the param-dependence rides the
            // refinement and is materialized as a `Restrict` at the iteration
            // boundary (the dependent-application model), and planning's
            // pointful group-by recognizer reads the binder off the predicate.
            // This replaces the former correlated-refinement uncurrying.
            //
            // A binder referenced in the cast's *value* (a value-dependent
            // dependent function) is not produced by any current lowering; the
            // assertion rejects it loudly rather than silently mishandle.
            debug_assert!(
                cast_target_refinement(&target).is_some(),
                "cast-wrapped lambda must carry a Fun(Refinement(_, _), _) target; got {target:?}"
            );
            assert!(
                !is_free(param, &value),
                "value-dependent dependent function unsupported: `{param}` occurs in the cast value of {}",
                symbolic(&value)
            );
            let inner_pf = elim_lambdas(ctx, *value)?;
            let cast_val = Expr::new(TypedExprNode::Cast {
                value: Box::new(inner_pf),
                target,
            })
            .with_ty(body_ty.clone());
            let result_pi = Type::pi(param, param_ty.clone(), body_ty.clone());
            let const_fn = Expr::builtin(Builtin::Const)
                .with_ty(Type::fun(body_ty.clone(), result_pi.clone()));
            return Ok(Expr::apply(cast_val, const_fn).with_ty(result_pi));
        }

        // Application: λ x → e ▷ f  ⟹  ⟨λx→e, λx→f⟩ ≫ apply
        TypedExprNode::Apply { argument, function } => {
            let elim_arg = elim_lambda(ctx, param, param_ty, *argument)?;
            let elim_fn = elim_lambda(ctx, param, param_ty, *function)?;
            let pair = zip_pair(elim_arg, elim_fn);
            // apply: Tuple([B, B→C]) → C; its domain is the codomain of pair
            let apply_ty = match &pair.ty {
                Type::Fun {
                    domain: _,
                    codomain: cod,
                    ..
                } => fun_ty_or_hole(cod, &body_ty),
                _ => Type::Hole,
            };
            let apply_var = Expr::builtin(Builtin::Apply).with_ty(apply_ty);
            Ok(compose(pair, apply_var).with_ty(result_ty))
        }

        // Compose in body: λ x → f ≫ g  ⟹  ⟨λx→f, λx→g⟩ ≫ compose
        //
        // For an n-ary Compose([f₀, f₁, …]), eliminate the lambda through each
        // element and re-build a pairwise chain: ⟨λx→f₀, λx→f₁⟩ ≫ compose ≫ …
        TypedExprNode::Compose(elts) => {
            let mut elim_elts = elts
                .into_iter()
                .map(|e| elim_lambda(ctx, param, param_ty, e))
                .collect::<Result<Vec<_>, _>>()?;
            // Fold pairwise from the left: ⟨e0, e1⟩ ≫ compose, then compose
            // the result with e2, etc.
            let mut acc = elim_elts.remove(0);
            for next in elim_elts {
                let pair = zip_pair(acc, next);
                // compose: Tuple([A→B, B→C]) → (A→C); domain = codomain of pair
                let compose_ty = match &pair.ty {
                    Type::Fun {
                        domain: _,
                        codomain: cod,
                        ..
                    } => match cod.as_ref() {
                        Type::Tuple(elts) if elts.len() == 2 => match (&elts[0], &elts[1]) {
                            (
                                Type::Fun { domain: a, .. },
                                Type::Fun {
                                    domain: _,
                                    codomain: c,
                                    ..
                                },
                            ) => fun_ty_or_hole(cod, &Type::fun(*a.clone(), *c.clone())),
                            _ => Type::Hole,
                        },
                        _ => Type::Hole,
                    },
                    _ => Type::Hole,
                };
                let compose_var = Expr::builtin(Builtin::Compose).with_ty(compose_ty);
                acc = compose(pair, compose_var);
            }
            Ok(acc.with_ty(result_ty))
        }

        // BinOp — desugar to Apply + Tuple, then apply the application rule.
        // a op b  ≡  (a, b) ▷ op_fn
        //
        // The `String + String → Concat` rewrite is handled by
        // [`crate::ccl::simplify::try_string_add_to_concat`] (which runs after
        // lambda elimination), so it's not duplicated here.
        TypedExprNode::BinOp { left, op, right } => {
            let left = *left;
            let right = *right;
            let tuple = typed_tuple(vec![left, right]);
            let fn_ty = fun_ty_or_hole(&tuple.ty, &body_ty);
            let fn_var = Expr::builtin(Builtin::BinOp(op)).with_ty(fn_ty);
            let desugared = Expr::apply(tuple, fn_var).with_ty(body_ty);
            elim_lambda(ctx, param, param_ty, desugared)
        }

        // CollectionUnion inside a lambda body: lift via the
        // `Apply(Tuple(ops), Builtin::CollectionUnion)` point-free form.
        // This mirrors the BinOp rule — the tuple of operands gets zipped
        // through the lambda parameter and the binary `CollectionUnion`
        // builtin closes the loop.  At the top level (outside any
        // lambda being eliminated) the dedicated arm in [`elim_lambdas`]
        // keeps the N-ary value-form intact.
        TypedExprNode::CollectionUnion(ops) => {
            let tuple = typed_tuple(ops);
            let fn_ty = fun_ty_or_hole(&tuple.ty, &body_ty);
            let fn_var = Expr::builtin(Builtin::CollectionUnion).with_ty(fn_ty);
            let desugared = Expr::apply(tuple, fn_var).with_ty(body_ty);
            elim_lambda(ctx, param, param_ty, desugared)
        }

        // UnaryOp — desugar to Apply, then apply the application rule.
        TypedExprNode::UnaryOp(op, inner) => {
            let op_builtin = Builtin::for_unaryop(op);
            let inner = *inner;
            let fn_ty = fun_ty_or_hole(&inner.ty, &body_ty);
            let fn_var = Expr::builtin(op_builtin).with_ty(fn_ty);
            let desugared = Expr::apply(inner, fn_var).with_ty(body_ty);
            elim_lambda(ctx, param, param_ty, desugared)
        }

        // Tuple: λ x → (e1, ..., en)  ⟹  zip(λx→e1, ..., λx→en)
        // In CCC, a tuple of morphisms is a product morphism ⟨f1, ..., fn⟩ = zip(f1, ..., fn).
        TypedExprNode::Tuple(elts) => {
            let elim_elts: Vec<Expr> = elts
                .into_iter()
                .map(|e| elim_lambda(ctx, param, param_ty, e))
                .collect::<Result<_, _>>()?;
            let inner_tuple = typed_tuple(elim_elts);
            let zip_fn_ty = fun_ty_or_hole(&inner_tuple.ty, &result_ty);
            let zip_var = Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty);
            Ok(Expr::apply(inner_tuple, zip_var).with_ty(result_ty))
        }

        // Record: λ x → {f1: e1, ..., fn: en}  ⟹  zip({f1: λx→e1, ..., fn: λx→en})
        // Mirrors the Tuple rule: build an inner Record of morphisms, then apply Zip.
        // This keeps the same structural invariant: the Record node always has type
        // Record([..., Fun(D, Ti), ...]) and the Fun wrapper lives on the Apply/Zip node.
        TypedExprNode::Record(fields) => {
            let elim_fields: Vec<(String, Expr)> = fields
                .into_iter()
                .map(|(k, e)| elim_lambda(ctx, param, param_ty, e).map(|r| (k, r)))
                .collect::<Result<_, _>>()?;
            let inner_ty = Type::Record(
                elim_fields
                    .iter()
                    .map(|(k, e)| (k.clone(), e.ty.clone()))
                    .collect(),
            );
            let inner_record = TypedExpr::new(TypedExprNode::Record(elim_fields)).with_ty(inner_ty);
            let zip_fn_ty = fun_ty_or_hole(&inner_record.ty, &result_ty);
            let zip_var = Expr::builtin(Builtin::Zip).with_ty(zip_fn_ty);
            Ok(Expr::apply(inner_record, zip_var).with_ty(result_ty))
        }

        // Let binding:
        // λ x → let v = def in body  ⟹
        //   let v = (λx→def) in (λx→body[v ↦ x ▷ v])
        //
        // Op-conversion's `Let` arm handles the resulting let-in-Compose
        // shape generically by fanning the surrounding input out to both
        // `bound_expr` and `body`.  For 0/1-use `v` this materialises the
        // input twice instead of inlining — a runtime cost that we accept
        // for simplicity.  A future optimization could inline `def` directly
        // when `v` appears at most once in `body` and keep the lift only
        // when sharing actually matters.
        TypedExprNode::Let {
            binding,
            bound_expr: def,
            body: let_body,
        } => {
            let v = binding.name;
            let new_def = elim_lambda(ctx, param, param_ty, *def)?;
            // In the let body, each free occurrence of v is replaced by x ▷ v
            // (i.e. the renamed function v applied to the current argument x).
            // Type `call_v` using the types already computed for `new_def` and
            // `param_ty`, so that `elim_lambda` on the substituted body can
            // propagate types into the combinator arguments it builds.
            let call_v_result_ty = match &new_def.ty {
                Type::Fun {
                    domain: _,
                    codomain: cod,
                    ..
                } => *cod.clone(),
                _ => Type::Hole,
            };
            let call_v = Expr::apply(
                Expr::var(param).with_ty(param_ty.clone()),
                Expr::var(&v).with_ty(new_def.ty.clone()),
            )
            .with_ty(call_v_result_ty);
            let substituted_body = substitute(*let_body, &v, &call_v);
            let new_body = elim_lambda(ctx, param, param_ty, substituted_body)?;
            // The let's type is its body's type lifted out of `v`'s scope, so
            // any refinement predicate mentioning `v` must have it discharged
            // to the bound expression (design §6.2 move-site rule) — the same
            // substitution inference's let-closing and `emit_let` apply, so
            // the post-elim check's reconstruction reconciles structurally.
            let let_ty =
                crate::ccl::subst::Subst::discharge(&v, new_def.clone()).apply_type(&result_ty);
            Ok(Expr::let_bind(v, new_def, new_body).with_ty(let_ty))
        }

        // List — treat like Tuple: eliminate param element-wise.
        TypedExprNode::List(elts) => {
            let elim_elts: Result<Vec<_>, _> = elts
                .into_iter()
                .map(|e| elim_lambda(ctx, param, param_ty, e))
                .collect();
            Ok(Expr::list(elim_elts?).with_ty(result_ty))
        }

        // Desugar to input ▷ agg(kind), then elim_lambda the result
        TypedExprNode::Aggregate { input, kind } => {
            let agg_builtin = Builtin::for_aggregate(kind);
            let input = *input;
            let agg_ty = fun_ty_or_hole(&input.ty, &body_ty);
            let agg_var = Expr::builtin(agg_builtin).with_ty(agg_ty);
            let desugared = Expr::apply(input, agg_var).with_ty(body_ty);
            elim_lambda(ctx, param, param_ty, desugared)
        }

        // `Defer`, `Feed`, `Define`, and `ExprStmt` are eliminated by
        // `channelize`, which runs before lambda-elim; by the time
        // `lambda_elim` runs they cannot appear.
        TypedExprNode::Feed { .. }
        | TypedExprNode::Define { .. }
        | TypedExprNode::Defer
        | TypedExprNode::ExprStmt { .. } => {
            unreachable!(
                "Defer/Feed/Define/ExprStmt eliminated by channelize, which runs before lambda-elim"
            )
        }

        // `Transact` is born by recognition, which runs *after* this pass —
        // none can reach lambda elimination.
        TypedExprNode::Transact { .. } => {
            unreachable!("lambda_elim: Transact is born by recognition, after this pass")
        }

        // A value-selecting `Case` inside a bare lambda body (`λ x → Case{[gᵢ → eᵢ]}`),
        // where the gate `gᵢ(x)` varies with the element. A *comprehension* element
        // conditional (`[a if g(x) else b for x in xs]`) is fanned out at
        // comprehension lowering (`lower::comprehension::fan_out_element_case`) into
        // `⧺ᵢ src|π̂ᵢ ≫ eᵢ`, so it never reaches here. This arm handles the residual
        // shapes — a per-element conditional in a lambda whose *iteration source is not
        // visible at lowering* (a writer decision body: `if 𝑝: a := … else: b := …`, a
        // per-key carry-forward merge, an `if/else`-both-write accumulator).
        //
        // It desugars to the same **union of domain-restricts** as every other
        // value-`Case` — `⧺ᵢ (filter_values(π̂ᵢ) ≫ eᵢ)` — but over the *lambda
        // parameter's* fed element stream (the writer body's runtime input) rather
        // than a visible comprehension source or the `UIntRange(1)` C-form driver.
        // Each arm filters the fed stream to the sub-domain its first-match gate
        // `π̂ᵢ = gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ` admits (`filter_values` keeps the element value, unlike
        // the position-domain `Restrict`), then maps by `eᵢ`. So a **partial op**
        // (`//`, `%`) in `eᵢ` is evaluated only where its guard holds — never eagerly
        // at a rejected position. The partition is exhaustive (a trailing `true` arm —
        // the carry in a writer decision), so the arms reassemble the full
        // `param_ty ⇒ V` column by position (op-conversion fans the fed input to each
        // union operand).
        TypedExprNode::Case {
            scrutinee: None,
            branches,
        } if branches.iter().all(|b| b.pattern.is_none()) => {
            let value_ty = body_ty.clone();
            let mut prior_guards: Vec<Expr> = Vec::new();
            let mut arms: Vec<Expr> = Vec::with_capacity(branches.len());
            for br in branches {
                // First-match gate π̂ᵢ as a scalar bool in `param` (the nesting the
                // old `select` encoded, made explicit), eliminated to the
                // element-varying predicate morphism `param_ty ⇒ Bool`.
                let pi_hat = synthesize_arm_predicate(&br.guard, &prior_guards);
                prior_guards.push(br.guard);
                let gate_fn = elim_lambda(ctx, param, param_ty, pi_hat)?;
                let value_fn = elim_lambda(ctx, param, param_ty, br.body)?;
                // `filter_values(π̂ᵢ) ≫ eᵢ`: filter the fed element stream to the gate
                // (keeping the element value), then map by `eᵢ`. The filtered stream
                // is typed by the plain `param` domain, **not** a `{param | π̂ᵢ}`
                // refinement: the `filter_values` op *is* the runtime filter, and a
                // refinement type would make planning inject its own (value-dropping,
                // position-domain) `restrict` at this site. The arms' runtime domains
                // are disjoint by first-match, so the `UnionOperator` merges them
                // without overlap despite the identical static type.
                let filter = apply_primitive(
                    gate_fn,
                    Builtin::FilterValues,
                    Type::data_fun(param_ty.clone(), param_ty.clone()),
                );
                arms.push(
                    typed_compose(vec![filter, value_fn])
                        .with_ty(Type::data_fun(param_ty.clone(), value_ty.clone())),
                );
            }
            match arms.len() {
                0 => unreachable!("a value-selecting Case has at least one branch"),
                1 => Ok(arms.pop().expect("len == 1")),
                _ => Ok(Expr::collection_union(arms)
                    .with_ty(Type::data_fun(param_ty.clone(), value_ty))),
            }
        }

        // Unsupported constructs.
        body => Err(LambdaElimError::Unsupported(format!(
            "unsupported body kind in lambda elimination for param '{param}' in body {body:?}"
        ))),
    };
    if let Ok(e) = &result {
        debug_typecheck(e);
    }
    result
}

// ---------------------------------------------------------------------------
// Top-level traversal
// ---------------------------------------------------------------------------

/// Traverse `expr` and eliminate all [`TypedExprNode::Lambda`] nodes, outside-in.
///
/// Applies [`elim_lambda`] to each lambda encountered.  After elimination
/// the result is recursed to handle any lambdas in sub-expressions.  Non-lambda
/// nodes are recursed into to reach nested lambdas.
fn elim_lambdas(ctx: &mut ElimContext, expr: Expr) -> Result<Expr, LambdaElimError> {
    stacker::maybe_grow(512 * 1024, 1024 * 1024, || elim_lambdas_impl(ctx, expr))
}

fn elim_lambdas_impl(ctx: &mut ElimContext, expr: Expr) -> Result<Expr, LambdaElimError> {
    log::trace!("elim_lambdas: eliminating {}", symbolic(&expr));
    debug_typecheck(&expr);
    let TypedExpr {
        node,
        ty,
        user_annotation,
        ..
    } = expr;
    // Only the debug-build invariant asserts below read `original_ty`.
    #[cfg(debug_assertions)]
    let original_ty = ty.clone();
    let result = match node {
        // Lambda: eliminate then continue. (Domain refinements ride the type
        // lattice via `cast`; the cast-wrapped-lambda arm below handles the
        // dependent case.)
        TypedExprNode::Lambda { param, body } => {
            // Render the pre-elimination lambda only in debug builds — the
            // string (and its `*body` clone) feeds just the assert below.
            #[cfg(debug_assertions)]
            let original = symbolic(&Expr::lambda(&param.name, param.ty.clone(), *body.clone()));
            let result = elim_lambda(ctx, &param.name, &param.ty, *body)?;
            // Compare modulo Pi binder *identity and presence*: the
            // coalesced original carries canonical (`__pi{n}`) binders while
            // the point-free construction rebuilds from the term's own
            // binder names (and combinator arrows with `name: None`) — so
            // α-normalize both sides first, then erase binder presence; see
            // `Type::alpha_normalized` / `Type::without_pi_names`.
            #[cfg(debug_assertions)]
            assert!(
                original_ty.alpha_normalized().without_pi_names()
                    == result.ty.alpha_normalized().without_pi_names(),
                "{}\nto\n{}\nwith {} vs {}",
                original,
                symbolic(&result),
                original_ty,
                result.ty
            );
            elim_lambdas(ctx, result)
        }

        // Filter pattern: Compose([..src.., Lambda(x, Case([guard→action, true→unit]))])
        // ⟹ src_restricted ≫ elim(x, action)
        //
        // Recognised here rather than inside the Lambda arm because the refinement
        // must be attached to the source (the preceding compose elements), which is
        // only visible at the Compose level.
        // TODO once refinements are properly propagated everywhere, we should be able to remove
        // this special case.
        //
        // Early return bypasses the original_ty == e.ty assertion because the
        // Refinement added to the domain is not present in the inferred compose type.
        TypedExprNode::Compose(mut terms)
            if terms.len() >= 2
                && matches!(
                    terms.last(),
                    Some(Expr {
                        node: TypedExprNode::Lambda { body, .. },
                        ..
                    }) if is_filter_case_body(body)
                ) =>
        {
            let lambda = terms.pop().unwrap();
            let (param, filter_body) = match lambda.node {
                TypedExprNode::Lambda { param, body, .. } => (param, *body),
                _ => unreachable!(),
            };
            let (guard, true_body) = extract_filter_case(filter_body);
            let raw_target = if terms.len() == 1 {
                terms.remove(0)
            } else {
                Expr::compose(terms)
            };
            let target_elim = elim_lambdas(ctx, raw_target)?;
            let pred_elem = elim_lambda(ctx, &param.name, &param.ty, guard)?;
            let pred_elem = elim_lambdas(ctx, pred_elem)?;
            let pred_on_source = typed_compose(vec![target_elim.clone(), pred_elem]);
            let source_domain = target_elim.ty.domain().unwrap();
            let source_codomain = target_elim.ty.codomain().unwrap();
            let refinement = Refinement::born(Rc::new(pred_on_source));
            let refined_domain = Type::Refinement(Box::new(source_domain), refinement);
            let refined_source = target_elim.with_ty(Type::fun(refined_domain, source_codomain));
            let body_elim = elim_lambda(ctx, &param.name, &param.ty, true_body)?;
            let result = typed_compose(vec![refined_source, elim_lambdas(ctx, body_elim)?]);
            debug_typecheck(&result);
            return Ok(result);
        }

        // BinOp (non-Compose): desugar to function application form.
        // `a op b` ≡ `(a, b) ▷ op_fn` — mirrors what `elim_lambda` does for
        // the same pattern inside a lambda body, making the CCL uniform.
        TypedExprNode::BinOp { left, op, right } => {
            let left_elim = elim_lambdas(ctx, *left)?;
            let right_elim = elim_lambdas(ctx, *right)?;
            let tuple_ty = Type::Tuple(vec![left_elim.ty.clone(), right_elim.ty.clone()]);
            let fn_ty = fun_ty_or_hole(&tuple_ty, &ty);
            let tuple = Expr::tuple(vec![left_elim, right_elim]).with_ty(tuple_ty);
            let fn_var = Expr::builtin(Builtin::BinOp(op)).with_ty(fn_ty);
            let mut desugared = Expr::apply(tuple, fn_var);
            desugared.ty = ty;
            debug_typecheck(&desugared);
            Ok(desugared)
        }

        // CollectionUnion at top level: an N-ary value-form node that
        // represents the eager merge of N collections.  Recurse into each
        // operand (each may itself contain lambdas to eliminate) and keep
        // the node — operator conversion compiles it directly to a
        // `UnionOperator`.  No need to lift through `Apply`/`Tuple`/`Builtin`
        // since there is no surrounding lambda parameter to thread through.
        TypedExprNode::CollectionUnion(ops) => {
            let elim_ops: Vec<Expr> = ops
                .into_iter()
                .map(|o| elim_lambdas(ctx, o))
                .collect::<Result<_, _>>()?;
            let mut result = Expr::collection_union(elim_ops);
            result.ty = ty;
            debug_typecheck(&result);
            Ok(result)
        }

        // UnaryOp: desugar to function application form.
        // `op(x)` ≡ `x ▷ op_fn` — mirrors `elim_lambda`'s treatment.
        TypedExprNode::UnaryOp(op, inner) => {
            let op_builtin = Builtin::for_unaryop(op);
            let inner_elim = elim_lambdas(ctx, *inner)?;
            let fn_ty = fun_ty_or_hole(&inner_elim.ty, &ty);
            let fn_var = Expr::builtin(op_builtin).with_ty(fn_ty);
            let mut desugared = Expr::apply(inner_elim, fn_var);
            desugared.ty = ty;
            debug_typecheck(&desugared);
            Ok(desugared)
        }

        TypedExprNode::Aggregate { input, kind } => {
            let input2 = elim_lambdas(ctx, *input)?;
            let agg_builtin = Builtin::for_aggregate(kind);
            let agg_ty = fun_ty_or_hole(&input2.ty, &ty);
            Ok(dbg_typecheck_mv(
                Expr::apply(input2, Expr::builtin(agg_builtin).with_ty(agg_ty)).with_ty(ty),
            ))
        }

        TypedExprNode::Error => crate::unexpected_error_node!(),

        // Value-selecting guard `Case`: the literal union-of-restricts. A
        // scalar / compute result takes the C-form (gated one-shot lifts +
        // `final_or_default`); a data-collection result takes the gate fan-out
        // (each whole arm restricted then unioned). A pattern-matching
        // `Case` (`scrutinee: Some`) is not handled here yet.
        TypedExprNode::Case {
            scrutinee: None,
            branches,
        } if branches.iter().all(|b| b.pattern.is_none()) => {
            // Flatten `elif` chains to one partition first, so a nested
            // conditional collection collapses into a single N-choice fan-out.
            let branches = flatten_trailing_value_case(branches);
            let result = if is_collection_result(&ty) {
                build_value_case_fanout(ctx, branches, ty)?
            } else {
                build_value_case_cform(ctx, branches, ty)?
            };
            debug_typecheck(&result);
            Ok(result)
        }

        // Control-flow constructs not yet supported.
        node @ TypedExprNode::Case { .. } => Err(LambdaElimError::Unsupported(format!(
            "unsupported node kind in lambda elimination: {node:?}"
        ))),

        // Pure structural recursion: Apply, plain Compose, Let, Tuple, Record,
        // List, ExprStmt, Feed, Define, and the atoms (no children to walk).
        node => {
            // TODO(preserve): a pure structural recursion rebuilds the same
            // logical node, so this is arguably `Expr::preserve(node_id, node)`
            // carrying the input's id rather than a mint. Minting here is at
            // least *recorded* (via `Expr::new`); settling mint-vs-preserve for
            // the catch-all arm wants its own change.
            let mut expr = Expr::new(node).with_ty(ty);
            expr.user_annotation = user_annotation;
            expr.try_map_children(|child| elim_lambdas(ctx, child))?;
            Ok(dbg_typecheck_mv(expr))
        }
    };
    if let Ok(e) = &result {
        debug_typecheck(e);
        #[cfg(debug_assertions)]
        assert!(
            original_ty.alpha_normalized().without_pi_names()
                == e.ty.alpha_normalized().without_pi_names(),
            "{} vs {}",
            original_ty,
            e.ty
        );
    }
    result
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{
        ArithmeticKind, BaseType, BinOpKind, CompareKind, Expr, Lit, Type, symbolic::symbolic,
    };
    use test_log::test;

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    fn var(s: &str) -> Expr {
        Expr::var(s)
    }

    fn app(arg: Expr, func: Expr) -> Expr {
        Expr::apply(arg, func)
    }

    fn lit(n: i64) -> Expr {
        Expr::lit(Lit::Int(n))
    }

    /// `Int` base type, used to give test expressions concrete types for the
    /// typechecker.
    fn int_ty() -> Type {
        Type::Base(BaseType::Int)
    }

    /// Build a `Fun(a, b)` type.
    fn fun_ty(a: Type, b: Type) -> Type {
        Type::Fun {
            name: None,
            kind: crate::ccl::ty::FunKind::Compute,
            domain: Box::new(a),
            codomain: Box::new(b),
        }
    }

    /// `Bool` base type, for predicate bodies and other boolean-typed nodes.
    fn bool_ty() -> Type {
        Type::Base(BaseType::Bool)
    }

    /// Compare two expressions structurally, ignoring type annotations.
    ///
    /// The lambda-elimination unit tests care about combinator structure, not
    /// about the exact types that inference fills in.  Comparing via
    /// [`symbolic`] strips types and gives a clean structural diff.
    fn assert_expr_eq(result: Expr, expected: Expr) {
        assert_eq!(
            symbolic(&result),
            symbolic(&expected),
            "left: {} vs expected: {}",
            symbolic(&result),
            symbolic(&expected)
        );
    }

    // -----------------------------------------------------------------------
    // Unit tests for elim_lambda (one rule each)
    // -----------------------------------------------------------------------

    /// Identity: λ x → x  ⟹  id
    #[test]
    fn identity() {
        let param_ty = int_ty();
        let result = elim_lambda(
            &mut ElimContext::new(),
            &Name::raw("x"),
            &param_ty,
            var("x").with_ty(int_ty()),
        )
        .unwrap();
        assert_eq!(result, id().with_ty(fun_ty(int_ty(), int_ty())));
    }

    /// λ x → x.0  ⟹  .0  (via application rule + simplification)
    #[test]
    fn proj0_via_apply() {
        // Typed: x: (Int, Int), .0: (Int, Int) → Int, body: Int
        let param_ty = Type::Tuple(vec![int_ty(), int_ty()]);
        let body = Expr::apply(
            var("x").with_ty(param_ty.clone()),
            Expr::proj_index(0).with_ty(fun_ty(param_ty.clone(), int_ty())),
        )
        .with_ty(int_ty());
        let expr = Expr::lambda("x", param_ty, body);
        let result = run(expr).unwrap();
        assert_expr_eq(result, Expr::proj_index(0));
    }

    /// Constant (literal): λ x → 42  ⟹  const(42)
    #[test]
    fn literal_constant() {
        let param_ty = int_ty();
        let result = elim_lambda(
            &mut ElimContext::new(),
            &Name::raw("x"),
            &param_ty,
            lit(42).with_ty(int_ty()),
        )
        .unwrap();
        assert_expr_eq(result, const_(lit(42)));
    }

    /// Constant (free var): λ x → y  ⟹  const(y)  (y ≠ x, free in outer scope)
    #[test]
    fn var_constant() {
        let param_ty = int_ty();
        let result = elim_lambda(
            &mut ElimContext::new(),
            &Name::raw("x"),
            &param_ty,
            var("y").with_ty(int_ty()),
        )
        .unwrap();
        assert_expr_eq(result, const_(var("y")));
    }

    /// Application: λ x → x ▷ f  ⟹  ⟨id, const(f)⟩ ≫ apply  (pre-simplification)
    #[test]
    fn apply_pre_simplification() {
        // Typed: x: Int, f: Int → Int, body: Int
        let param_ty = int_ty();
        let body = app(
            var("x").with_ty(param_ty.clone()),
            var("f").with_ty(fun_ty(int_ty(), int_ty())),
        )
        .with_ty(int_ty());
        let result =
            elim_lambda(&mut ElimContext::new(), &Name::raw("x"), &param_ty, body).unwrap();
        let f_ty = fun_ty(int_ty(), int_ty());
        let apply_ty = fun_ty(Type::Tuple(vec![int_ty(), f_ty.clone()]), int_ty());
        // const(f) where f: Int → Int has type Int -> ((Int → Int) -> (Int → Int))
        let const_f_ty = fun_ty(f_ty.clone(), fun_ty(f_ty.clone(), f_ty.clone()));
        let const_var = Expr::builtin(Builtin::Const).with_ty(const_f_ty);
        let const_f = Expr::apply(var("f").with_ty(f_ty.clone()), const_var)
            .with_ty(fun_ty(f_ty.clone(), f_ty.clone()));
        let expected = compose(
            zip_pair(id().with_ty(fun_ty(int_ty(), int_ty())), const_f),
            Expr::builtin(Builtin::Apply).with_ty(apply_ty),
        );
        assert_expr_eq(result, expected);
    }

    /// Tuple: λ x → (x, f)  ⟹  zip(id, const(f))  (pre-simplification)
    #[test]
    fn tuple() {
        // Typed: x: Int, f: Int, body: (Int, Int)
        let param_ty = int_ty();
        let body = Expr::tuple(vec![
            var("x").with_ty(param_ty.clone()),
            var("f").with_ty(int_ty()),
        ])
        .with_ty(Type::Tuple(vec![int_ty(), int_ty()]));
        let result =
            elim_lambda(&mut ElimContext::new(), &Name::raw("x"), &param_ty, body).unwrap();
        // const(f) where f: Int has type Int -> (Int -> Int)
        let const_f_ty = fun_ty(int_ty(), fun_ty(int_ty(), int_ty()));
        let const_var = Expr::builtin(Builtin::Const).with_ty(const_f_ty);
        let const_f =
            Expr::apply(var("f").with_ty(int_ty()), const_var).with_ty(fun_ty(int_ty(), int_ty()));
        let expected = zip_pair(id().with_ty(fun_ty(int_ty(), int_ty())), const_f);
        assert_expr_eq(result, expected);
    }

    /// Nested lambda: λ x → λ y → x  ⟹  curry(.0)
    #[test]
    fn nested_lambda_uses_first() {
        // Typed: x: Int, y: Int; inner lambda type Int → Int
        let inner = Expr::lambda("y", int_ty(), var("x").with_ty(int_ty()))
            .with_ty(fun_ty(int_ty(), int_ty()));
        let expr = Expr::lambda("x", int_ty(), inner);
        let result = run(expr).unwrap();
        assert_expr_eq(result, curry(Expr::proj_index(0)));
    }

    /// Let binding: λ x → let v = x in v  ⟹  let v = id in v.
    ///
    /// elim_lambda produces `let v = id in ⟨id, const(v)⟩ ≫ apply`,
    /// which simplifies to `let v = id in v` via const-apply.
    #[test]
    fn let_binding() {
        // Typed: x: Int, v: Int
        let param_ty = int_ty();
        let let_expr = Expr::let_bind(
            "v",
            var("x").with_ty(param_ty.clone()),
            var("v").with_ty(int_ty()),
        )
        .with_ty(int_ty());
        let expr = Expr::lambda("x", param_ty, let_expr);
        let result = run(expr).unwrap();
        let expected = Expr::let_bind(
            "v",
            id().with_ty(fun_ty(int_ty(), int_ty())),
            var("v").with_ty(fun_ty(int_ty(), int_ty())),
        )
        .with_ty(fun_ty(int_ty(), int_ty()));
        assert_expr_eq(result, expected);
    }

    #[test]
    fn substitute_in_refinement() {
        // A refinement predicate is a bare `Bool` over the implicit element
        // binder. Build one whose body uses the free variable `y` in a Bool
        // position: `y > 0`. We substitute `y` and confirm the replacement
        // reached into the predicate body.
        let pred_of = |y_expr: Expr| {
            Expr::binop(
                y_expr,
                BinOpKind::Compare(CompareKind::Greater),
                lit(0).with_ty(int_ty()),
            )
            .with_ty(bool_ty())
        };
        let refinement_pred = pred_of(var("y").with_ty(int_ty()));

        // Refinements ride the type lattice (introduced by `cast`), so the
        // predicate lives in the lambda's *domain type* `{Int | y > 0}`, not on
        // a dedicated AST field. `substitute` must descend through the type
        // (via `substitute_in_type`) into the predicate body.
        let refinement = Refinement::born(Rc::new(refinement_pred));
        let refined_param = Type::Refinement(Box::new(int_ty()), refinement);
        let expr = Expr::lambda("x", int_ty(), Expr::var("x").with_ty(int_ty()))
            .with_ty(fun_ty(refined_param, int_ty()));

        // Substitute "y" with a literal value in the expression
        let replacement = Expr::lit(Lit::Int(42)).with_ty(int_ty());
        let result = substitute(expr, &Name::raw("y"), &replacement);

        // Extract the refinement predicate from the result's domain type to
        // verify substitution descended into it.
        let pred_after_subst = match &result.ty {
            Type::Fun { domain, .. } => match domain.as_ref() {
                Type::Refinement(_, r) => (*r.predicate).clone(),
                other => panic!("expected refined domain, got {other}"),
            },
            other => panic!("expected function type, got {other}"),
        };

        // The predicate's `y` should now be `42`: `λ _p : Int → 42 > 0`.
        assert_expr_eq(pred_after_subst, pred_of(replacement.clone()));
    }

    // -----------------------------------------------------------------------
    // Integration tests — worked examples from docs/operational-semantics/lowering.md
    // -----------------------------------------------------------------------

    /// λ i → i ▷ f ▷ g  ⟹  f ≫ g
    #[test]
    fn example_basic_compose() {
        // Typed: i: Int, f: Int → Int, g: Int → Int
        let param_ty = int_ty();
        let f_ty = fun_ty(int_ty(), int_ty());
        let g_ty = fun_ty(int_ty(), int_ty());
        let if_ = app(var("i").with_ty(param_ty.clone()), var("f").with_ty(f_ty)).with_ty(int_ty());
        let body = app(if_, var("g").with_ty(g_ty)).with_ty(int_ty());
        let expr = Expr::lambda("i", param_ty, body);
        let result = run(expr).unwrap();
        assert_expr_eq(result, compose(var("f"), var("g")));
    }

    /// λ r → r.0 ▷ c1 + r.1 ▷ c2  ⟹  ⟨.0 ≫ c1, .1 ≫ c2⟩ ≫ add
    #[test]
    fn example_lambda_of_tuple() {
        // Typed: r: (Int, Int), .0/.1: (Int,Int)→Int, c1/c2: Int→Int,
        //        add: (Int,Int)→Int
        let r_ty = Type::Tuple(vec![int_ty(), int_ty()]);
        let proj_ty = fun_ty(r_ty.clone(), int_ty());
        let c_ty = fun_ty(int_ty(), int_ty());
        let add_ty = fun_ty(Type::Tuple(vec![int_ty(), int_ty()]), int_ty());

        let r0 = Expr::apply(
            var("r").with_ty(r_ty.clone()),
            Expr::proj_index(0).with_ty(proj_ty.clone()),
        )
        .with_ty(int_ty());
        let r1 = Expr::apply(
            var("r").with_ty(r_ty.clone()),
            Expr::proj_index(1).with_ty(proj_ty.clone()),
        )
        .with_ty(int_ty());
        let r0c1 = app(r0, var("c1").with_ty(c_ty.clone())).with_ty(int_ty());
        let r1c2 = app(r1, var("c2").with_ty(c_ty.clone())).with_ty(int_ty());
        let tuple_result =
            Expr::tuple(vec![r0c1, r1c2]).with_ty(Type::Tuple(vec![int_ty(), int_ty()]));
        let body = app(
            tuple_result,
            Expr::builtin(Builtin::BinOp(BinOpKind::Arithmetic(ArithmeticKind::Add)))
                .with_ty(add_ty.clone()),
        )
        .with_ty(int_ty());
        let expr = Expr::lambda("r", r_ty.clone(), body);
        let result = run(expr).unwrap();
        // Expected: zip(.0 ≫ c1, .1 ≫ c2) ≫ add
        let r_to_int = fun_ty(r_ty.clone(), int_ty());
        let proj0_c1 = compose(
            Expr::proj_index(0).with_ty(proj_ty.clone()),
            var("c1").with_ty(c_ty.clone()),
        )
        .with_ty(r_to_int.clone());
        let proj1_c2 = compose(
            Expr::proj_index(1).with_ty(proj_ty.clone()),
            var("c2").with_ty(c_ty.clone()),
        )
        .with_ty(r_to_int.clone());
        let expected = compose(
            zip_pair(proj0_c1, proj1_c2),
            Expr::builtin(Builtin::BinOp(BinOpKind::Arithmetic(ArithmeticKind::Add)))
                .with_ty(add_ty),
        );
        assert_expr_eq(result, expected);
    }

    /// λ i → (i, c) ▷ f  ⟹  ⟨id, const(c)⟩ ≫ f
    #[test]
    fn example_free_var_capture() {
        // Typed: i: Int, c: Int, f: (Int, Int) → Int
        let param_ty = int_ty();
        let f_ty = fun_ty(Type::Tuple(vec![int_ty(), int_ty()]), int_ty());
        let tuple_body = Expr::tuple(vec![
            var("i").with_ty(param_ty.clone()),
            var("c").with_ty(int_ty()),
        ])
        .with_ty(Type::Tuple(vec![int_ty(), int_ty()]));
        let body = app(tuple_body, var("f").with_ty(f_ty.clone())).with_ty(int_ty());
        let expr = Expr::lambda("i", param_ty, body);
        let result = run(expr).unwrap();
        let int_to_int = fun_ty(int_ty(), int_ty());
        let tuple_ty = Type::Tuple(vec![int_ty(), int_ty()]);
        let zip_result_ty = fun_ty(tuple_ty.clone(), int_ty());
        // const(c) where c: Int has type Int -> (Int -> Int)
        let const_c_ty = fun_ty(int_ty(), int_to_int.clone());
        let const_var = Expr::builtin(Builtin::Const).with_ty(const_c_ty);
        let const_c =
            Expr::apply(var("c").with_ty(int_ty()), const_var).with_ty(int_to_int.clone());
        let expected = compose(
            zip_pair(id().with_ty(int_to_int.clone()), const_c).with_ty(zip_result_ty),
            var("f").with_ty(f_ty),
        );
        assert_expr_eq(result, expected);
    }

    /// Test direct elimination of a lambda whose parameter has a refined type
    ///
    /// Refinements ride the type lattice (introduced by `cast`), so a refined
    /// parameter shows up as a `Type::Refinement` domain. Eliminating `λ y → y`
    /// over such a domain should yield `id` with the refinement preserved.
    #[test]
    fn lambda_with_refined_param_type() {
        let bool_ty = Type::Base(BaseType::Bool);

        // Uncorrelated refinement (a Bool constant predicate) on the param.
        let refinement = Refinement::born(Rc::new(Expr::lit(Lit::Bool(true)).with_ty(bool_ty)));
        let refined_y_ty = Type::Refinement(Box::new(int_ty()), refinement);
        let body = var("y").with_ty(int_ty());

        // Eliminate λ y → y over the refined domain.
        let mut ctx = ElimContext::new();
        let result = elim_lambda(&mut ctx, &Name::raw("y"), &refined_y_ty, body);

        assert!(result.is_ok(), "Lambda elimination should succeed");
        let eliminated = result.unwrap();

        // Eliminating λ y → y is `id`; the refined domain is preserved and the
        // codomain is the body's type (`Int`, the type recorded on `Var(y)`).
        assert_eq!(
            eliminated.ty,
            fun_ty(refined_y_ty, int_ty()),
            "Result of eliminating λ y → y should be id with the refined domain"
        );
    }

    // -----------------------------------------------------------------------
    // is_free / is_free_in_type
    // -----------------------------------------------------------------------

    /// Two properties of `is_free_in_type`, on one fixture so they contrast:
    ///
    /// 1. A name is free in a tuple type if it appears in **any** component. The
    ///    original bug here used `.all()`, so a variable appearing in only one
    ///    component of a multi-element tuple went undetected and `substitute`
    ///    silently skipped it.
    /// 2. `REFINEMENT_BINDER` is **never** free in a type: a refinement is a
    ///    binding form, and every `__elem` occurrence sits under the refinement
    ///    that binds it. Reporting it free tripped the "value-dependent dependent
    ///    function" guard below on any nested filter, whose predicate carries a
    ///    refinement over `__elem`.
    ///
    /// One predicate exercises both — `__elem > x` mentions the bound element
    /// binder and a free reference to the enclosing scope — so an implementation
    /// that answered uniformly (everything free, or nothing free) fails one half.
    #[test]
    fn is_free_in_type_sees_free_names_but_not_the_bound_element_binder() {
        use crate::ccl::Refinement;
        use std::rc::Rc;

        // pred = `__elem > x`: `__elem` is bound by the enclosing refinement,
        // `x` is a free reference to whatever scope the type sits in.
        let pred = Rc::new(Expr::binop(
            Expr::var(Name::elem()),
            BinOpKind::Compare(CompareKind::Greater),
            Expr::var("x"),
        ));
        // A predicate this call site is creating, so `born` — see `Refinement`.
        let refinement = Refinement::born(pred);

        // Tuple([Int, {Int | __elem > x}]): the predicate rides only the second
        // component, so `any`-vs-`all` is observable.
        let tuple_ty = Type::Tuple(vec![
            int_ty(),
            Type::Refinement(Box::new(int_ty()), refinement),
        ]);

        // Lit(42) typed with the tuple above — the expression node itself has no
        // free vars, so both answers come entirely from `is_free_in_type`.
        let expr = Expr::lit(Lit::Int(42)).with_ty(tuple_ty);

        assert!(
            is_free(&Name::raw("x"), &expr),
            "x should be free: it appears in the refinement of the second tuple component"
        );
        assert!(
            !is_free(&Name::elem(), &expr),
            "the refinement element binder is bound by its refinement, so it is never \
             free in a type — reporting it free is what falsely tripped the \
             value-dependent-dependent-function guard on nested filters"
        );
    }
}
