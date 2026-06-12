//! CCC simplification pass for CCL.
//!
//! Applies algebraic rewrite rules to a point-free CCL expression until no
//! further changes occur (fixed-point iteration).  All rules are
//! equationally valid in any Cartesian Closed Category.
//!
//! # Entry point
//!
//! [`simplify`] runs the rule set to a fixed point and is safe at any point
//! in the pipeline.  There is no mode: the structural-discard rules
//! self-guard on [`is_iteration`], so they fire on pure CCC morphisms but
//! never drop an `Apply(_, Iterate)` iteration source.  Before
//! `crate::ccl::planning::insert_iterate_markers` no `iterate` exists (every
//! rule fires); afterwards the always-safe rules still absorb the `id` /
//! nested-`Compose` leftovers from the hash-join rewrite.
//!
//! # Rule summary
//!
//! Rules that match a compose pattern operate *pairwise*: they scan every
//! consecutive `(elts[i], elts[i+1])` pair inside an n-ary
//! [`TypedExprNode::Compose`] and fire on the first matching pair.
//!
//! The **Iteration-guarded?** column flags whether a rule is gated on
//! [`is_iteration`].  A rule is *unguarded* (✓ — always safe) iff it
//! preserves every sub-expression of the input (and therefore every
//! `iterate` inside any of them).  A *guarded* rule (✗) drops or relocates a
//! sub-expression whose purity it cannot verify; it must not fire on a
//! sub-tree containing an `iterate`, because an `Apply(_, Iterate)` at a
//! chain head *is* the iteration source for everything downstream — dropping
//! it strands the chain (op-conversion then errors).  A `restrict` filter is
//! always applied to an iterate-bearing upstream, so this single guard
//! protects it transitively; it needs no check of its own.
//!
//! | Rule | Pattern | Reduction | Iteration-guarded? |
//! |------|---------|-----------|-----------------|
//! | Compose identity | `… ≫ id ≫ …` / `… ≫ id ≫ …` | remove `id` | ✓ |
//! | Const reduce | `f ≫ g ▷ const` | `g ▷ const` | ✗ (drops `f`) |
//! | Product beta (fst) | `⟨f, g⟩ ≫ .0` | `f` | ✗ (drops `g`) |
//! | Product beta (snd) | `⟨f, g⟩ ≫ .1` | `g` | ✗ (drops `f`) |
//! | Literal tuple projection | `(e₀, …, eₙ).i` | `eᵢ` | ✗ (drops siblings) |
//! | CCC universal | `⟨.1, .0 ≫ curry(f)⟩ ≫ apply` | `f` | ✗ (drops structure) |
//! | Exponential beta | `⟨g, curry(h)⟩ ≫ apply` | `⟨id, g⟩ ≫ h` | ✗ (restructures) |
//! | Exponential eta | `curry(⟨.1, .0 ≫ f⟩ ≫ apply)` | `f` | ✗ (drops structure) |
//! | Const-apply | `⟨f, const(g)⟩ ≫ apply` | `f ≫ g` | ✗ (drops `const` wrap) |
//! | Product eta | `⟨f ≫ .0, f ≫ .1⟩` | `f` | ✗ (collapses) |
//! | Flatten compose | `Compose([…, Compose([…]), …])` | `Compose([…flat…])` | ✓ |
//! | Zip distribute | `⟨f0, f1⟩ ≫ ⟨g, h⟩` (if g,h will simplify) | `⟨⟨f0, f1⟩ ≫ g, ⟨f0, f1⟩ ≫ h⟩` | ✗ (restructures) |
//! | String add-to-concat | `Arithmetic(Add) : (String,String)→String` | `Concat` | ✓ |

use crate::ccl::infer::debug_typecheck;
use crate::ccl::lambda_elim::{fun_ty_or_hole, id, zip_pair};
use crate::ccl::{
    ArithmeticKind, BaseType, BinOpKind, Builtin, Expr, Lit, ProjKey, Type, TypedExpr,
    TypedExprNode,
};

/// Returns `true` if `expr` directly references the given built-in primitive.
fn is_builtin(expr: &Expr, b: Builtin) -> bool {
    matches!(&expr.node, TypedExprNode::Builtin(x) if *x == b)
}

// ---------------------------------------------------------------------------
// Simplification pass
// ---------------------------------------------------------------------------

/// Returns `true` if `expr` is *itself* an iteration source — an
/// `Apply(_, Iterate)` chain head.  This is the per-node test only; the
/// subtree-wide "contains an iteration" property is accumulated bottom-up in
/// [`simplify_once`] (OR-ing this node's result with its children's) and
/// threaded to the discard-rule guard in [`apply_simplification_rules`], so
/// the subtree is never re-scanned at every node.
///
/// `iterate`, emitted by `crate::ccl::planning::insert_iterate_markers`, is
/// *not* a pure CCC morphism: it is the iteration source for everything
/// downstream, so dropping it strands the chain (op-conversion errors).  The
/// structural-discard / restructure rewrite rules are equationally valid only
/// on pure morphisms, so they consult the accumulated guard and refuse to fire
/// on any sub-tree that contains an `iterate`.  That makes the rule set correct
/// at any point in the pipeline — before *or* after iterate insertion — which
/// is why [`simplify`] needs no mode parameter.
///
/// **Only `iterate` needs guarding.**  A `restrict` filter
/// (`Apply(upstream, Apply(p, Restrict))`) is always emitted *applied to* an
/// iterate-bearing upstream (see `crate::ccl::planning`), so it is never
/// separable from its iteration source: any discard rule that would drop a
/// `restrict` also drops the `iterate` in its upstream, which this guard
/// already catches.  Guarding `iterate` therefore protects `restrict`
/// transitively — there is no need to flag `restrict` (or any other filter)
/// directly.
///
/// **Why `cast` is deliberately *not* guarded here.** A
/// [`TypedExprNode::Cast`] carries a domain refinement (a filter) on its type,
/// so it is tempting to protect it the same way — dropping a cast looks like a
/// "filter silently dropped" hazard.  It is not, and adding the guard
/// regresses real reductions (witness: `test_new_compile::case_27` in
/// `tests/compilation_pipeline.rs`).  No rule matches a `Cast` node (the
/// simplify rules operate on `Apply`/`Compose`), so none collapses `cast(v)`
/// to `v` directly; a rule only *drops a sub-tree containing a cast* when that
/// sub-tree is extensionally dead — a tuple arm a later `Proj` discards
/// (`⟨a, b ▷ cast⟩ ≫ .0 ⟹ a`), or the input of a `const` that ignores it.  A
/// dead cast carries a dead filter, so pruning it is sound; a cast feeding a
/// *consumed* collection (the `filter_and_aggregate` case) sits in a live
/// position no discard rule touches, and casts are freely duplicated, so a
/// live occurrence survives even when a dead duplicate is pruned.  The one
/// drop rule that keeps a refinement-bearing position alive,
/// `try_const_reduce`, re-stamps the dropped operand's *domain* — refinement
/// included — onto the rewritten `const`, so planning still sees the filter.
fn is_iteration(expr: &Expr) -> bool {
    matches!(
        &expr.node,
        TypedExprNode::Apply { function, .. }
            if matches!(&function.node, TypedExprNode::Builtin(Builtin::Iterate))
    )
}

/// Apply the CCC simplification rule set to `expr` until no further changes
/// occur (bottom-up fixed-point iteration).
///
/// Safe to run at any point in the pipeline.  The structural-discard rules
/// self-guard on [`is_iteration`], so they fire on pure CCC morphisms —
/// pre-iterate-insertion CCL, or iteration-free sub-trees of post-insertion
/// CCL — but never drop an `iterate` source.  (Before
/// `crate::ccl::planning::insert_iterate_markers` no `iterate` exists, so
/// every rule fires; afterwards the always-safe rules still absorb the `id` /
/// nested-`Compose` leftovers from the hash-join rewrite's
/// `replace_tuple_project_with_id`.)
pub fn simplify(mut expr: Expr) -> Expr {
    while simplify_once(&mut expr).0 {}
    expr
}

/// One bottom-up simplification pass over the subtree at `expr`.
///
/// Returns `(changed, contains_iteration)`:
/// - `changed` — whether any rule fired anywhere in the subtree.
/// - `contains_iteration` — whether the subtree contains an `iterate` source
///   ([`is_iteration`]).  Computed bottom-up: OR the children's results (from
///   [`recurse_simplify`]) with whether this node is itself an `iterate`.
///   Passing it to [`apply_simplification_rules`] lets the discard-rule guard
///   read it in O(1) instead of re-scanning the whole subtree at every node —
///   the re-scan was O(n²) over the long compose chains planning emits.
fn simplify_once(expr: &mut Expr) -> (bool, bool) {
    let mut changed = false;
    if let Type::Fun {
        domain,
        codomain: _,
        ..
    } = &mut expr.ty
        && let Type::Refinement(_, refinment) = &mut **domain
    {
        let pred = &refinment.predicate;
        // A refinement's predicate is itself an `Expr` whose own
        // subexpressions may carry the same refinement on their `ty`
        // (inference shares the `Rc<RefCell<Expr>>` across all places
        // the refined type surfaces).  If we're already simplifying
        // this predicate higher up the call stack, `borrow_mut` would
        // panic.  Skipping the inner attempt is sound: the outer
        // recursion is already simplifying this predicate, and we
        // walk to a fixed point in [`simplify`], so any rule that
        // could fire will fire on a later pass.
        //
        // This try_borrow_mut fallback is the same cycle-handling
        // mechanism used by [`crate::ccl::infer_simple_sub::coalesce_node`].
        // A related visited-set variant lives in
        // [`crate::ccl::ccl_utils::walk_refined_predicates`] and is
        // used by [`crate::ccl::ccl_utils::count_free`],
        // [`crate::ccl::infer::check_fully_typed`], and
        // [`crate::ccl::lambda_elim::elim_lambdas_in_type`].  This
        // site doesn't use the helper because it only targets the
        // domain refinement on `Fun(...)` (Lambda's refinement slot
        // shape) rather than every refinement reachable from the type.
        if let Ok(mut p) = pred.try_borrow_mut() {
            // A refinement predicate's own iteration-containment is irrelevant
            // to the term-tree guard: `iterate` sources are inserted into the
            // term tree, never inside predicates.  Discard the iteration bit
            // here — matching the original recursive scan, which never
            // descended into `expr.ty`.
            changed = simplify_once(&mut p).0;
        }
    }
    let (children_changed, children_have_iteration) = recurse_simplify(expr);
    changed |= children_changed;
    let contains_iteration = children_have_iteration || is_iteration(expr);
    changed |= apply_simplification_rules(expr, contains_iteration);
    (changed, contains_iteration)
}

/// Recursively apply [`simplify_once`] to all child expressions (bottom-up).
///
/// Returns `(changed, contains_iteration)`: whether any child was modified,
/// and whether any child's subtree contains an `iterate` source (OR-ed up so
/// the parent need not re-scan its descendants).
fn recurse_simplify(expr: &mut Expr) -> (bool, bool) {
    let (mut changed, has_iteration) = expr.fold_children_mut((false, false), |(c, it), e| {
        let (child_changed, child_has_iteration) = simplify_once(e);
        (c | child_changed, it | child_has_iteration)
    });
    // After simplifying children, propagate the Let body's type up to the Let
    // itself. Simplification can change the body's type (e.g., union flattening
    // rewrites Fun(Union(Union(A,B),C), D) → Fun(Union(A,B,C), D)); the Let
    // must stay in sync so downstream passes see a consistent representation.
    // Lifting the body's type out of the binder's scope must discharge
    // `[v ↦ bound]` into its refinement predicates (design §6.2 move-site
    // rule), matching inference's let-closing so the recorded type stays
    // well-formed (closed over `v`) and the post-pass check reconciles.
    if let TypedExprNode::Let {
        binding,
        bound_expr,
        body,
    } = &expr.node
    {
        let body_ty = crate::ccl::subst::Subst::discharge(&binding.name, (**bound_expr).clone())
            .apply_type(&body.ty);
        if expr.ty != body_ty {
            expr.ty = body_ty;
            changed = true;
        }
    }
    (changed, has_iteration)
}

/// Temporarily take ownership of `expr`, leaving a cheap placeholder.
///
/// The caller **must** write a valid expression back to `*expr` before
/// returning; the placeholder is never externally observable.
fn take(expr: &mut Expr) -> Expr {
    std::mem::replace(expr, Expr::lit(Lit::Int(0)))
}

/// Rewrite `String + String` from `Arithmetic(Add)` to `Concat`.
///
/// Inference intentionally leaves the operator as `Add` (see
/// [`crate::ccl::infer`]); this pass retargets the runtime dispatch.  Doing it
/// here — rather than in [`crate::ccl::lambda_elim`] — guarantees every BinOp
/// is visited regardless of how it ended up wrapped: a constant-body lambda
/// lifted to `Apply(BinOp(...), Const)` no longer hides the operator from
/// rewriting, and a BinOp inside a lambda body that has been desugared to
/// `Apply(Tuple, Builtin(BinOp(Add)))` is rewritten via its `Builtin` head.
fn try_string_add_to_concat(expr: &mut Expr) -> bool {
    match &mut expr.node {
        // Pre-lambda-elim form: a raw BinOp node still in the tree.
        TypedExprNode::BinOp { left, op, .. }
            if *op == BinOpKind::Arithmetic(ArithmeticKind::Add)
                && left.ty == Type::Base(BaseType::String) =>
        {
            *op = BinOpKind::Concat;
            true
        }
        // Post-lambda-elim form: `BinOp(Add, ...)` was desugared to
        // `Apply(Tuple, Builtin(BinOp(Add)))`.  The function's type captures
        // the operand types: `Fun(Tuple([String, String]), String)`.
        TypedExprNode::Builtin(Builtin::BinOp(op))
            if *op == BinOpKind::Arithmetic(ArithmeticKind::Add) =>
        {
            if let Type::Fun {
                domain: arg_ty,
                codomain: _,
                ..
            } = &expr.ty
                && let Type::Tuple(elts) = arg_ty.as_ref()
                && elts.first() == Some(&Type::Base(BaseType::String))
            {
                *op = BinOpKind::Concat;
                return true;
            }
            false
        }
        _ => false,
    }
}

/// Apply all simplification rules at the root of `expr`.
///
/// Rules are tried in a fixed order; each pass may enable earlier rules in the
/// next fixed-point iteration. Key ordering constraints:
/// - Product beta before product eta (eta needs reduced arms).
/// - Exponential eta before zip-beta (beta patterns may expose eta redexes).
///
/// Note: `curry_compose` (`curry(f ≫ g) ⟹ curry(f) ≫ map(g)`) is intentionally
/// omitted. Splitting a curry prevents `exponential_beta` from recognising the
/// `curry(h)` right-arm of a zip in multi-generator comprehension contexts.
///
/// Returns `true` if any rule fired.
fn apply_simplification_rules(expr: &mut Expr, contains_iteration: bool) -> bool {
    let mut changed = false;
    // Always-safe rules — neither discard sub-expressions nor relocate
    // iteration sources, so they fire regardless of any `iterate` present.
    // (They also preserve the subtree's iteration set, so `contains_iteration`
    // — computed before they run — is still accurate at the guard below.)
    changed |= check(try_compose_identity(expr), expr);
    changed |= check(try_flatten_compose(expr), expr);
    changed |= check(try_string_add_to_concat(expr), expr);

    // Rules that may discard or restructure sub-expressions.  Equationally
    // valid only on pure CCC morphisms, so they must not touch a sub-tree
    // containing an `iterate` source (dropping it strands the iteration — a
    // correctness bug; see [`is_iteration`]).  `contains_iteration` is
    // accumulated bottom-up by [`simplify_once`], so this guard is O(1) here
    // rather than a fresh subtree scan.  Guarding on iteration-freeness is
    // what lets the rule set run correctly at any point in the pipeline — the
    // invariant is a property of the *nodes*, not of pass timing.
    if !contains_iteration {
        changed |= check(try_const_reduce(expr), expr);
        changed |= check(try_product_beta_fst(expr), expr);
        changed |= check(try_product_beta_snd(expr), expr);
        changed |= check(try_literal_tuple_projection(expr), expr);
        changed |= check(try_ccc_universal(expr), expr);
        changed |= check(try_exponential_beta(expr), expr);
        changed |= check(try_exponential_eta(expr), expr);
        changed |= check(try_const_apply(expr), expr);
        changed |= check(try_product_eta(expr), expr);
        changed |= check(try_zip_distribute_compose(expr), expr);
    }

    changed
}

fn check(changed: bool, expr: &Expr) -> bool {
    // Only re-typecheck when a rewrite actually fired: the assertion validates
    // that a *transformation* preserved typing, so an untouched expression
    // (already valid on the way in) needs no re-check. Skipping the no-op case
    // avoids re-typechecking every subexpression after every rewrite *attempt*
    // (10 per node per fixpoint pass), which otherwise dominates simplify in
    // debug builds.
    if changed {
        debug_typecheck(expr);
    }
    changed
}

// ---------------------------------------------------------------------------
// Flatten-compose helpers
// ---------------------------------------------------------------------------

/// Expand `expr` into its flat compose constituents.
///
/// If `expr` is an n-ary [`TypedExprNode::Compose`], return its elements;
/// otherwise return a single-element `vec![expr]`.  Used by
/// [`try_flatten_compose`] to merge already-flattened child compose nodes.
fn flatten_compose_arm(expr: Expr) -> Vec<Expr> {
    match expr.node {
        TypedExprNode::Compose(elts) => elts,
        _ => vec![expr],
    }
}

// ---------------------------------------------------------------------------
// Pattern-matching helpers for zip / curry / const
// ---------------------------------------------------------------------------

/// Returns `(f, g)` if `expr` is `zip_pair(f, g)` i.e.
/// `Apply { argument: Tuple([f, g]), function: Builtin(Zip) }`.
fn as_zip(expr: &Expr) -> Option<(&Expr, &Expr)> {
    if let TypedExprNode::Apply { argument, function } = &expr.node
        && is_builtin(function, Builtin::Zip)
        && let TypedExprNode::Tuple(elts) = &argument.node
        && elts.len() == 2
    {
        return Some((&elts[0], &elts[1]));
    }
    None
}

/// Returns the inner `f` if `expr` is `curry(f)` i.e.
/// `Apply { argument: f, function: Builtin(Curry) }`.
fn as_curry(expr: &Expr) -> Option<&Expr> {
    if let TypedExprNode::Apply { argument, function } = &expr.node
        && is_builtin(function, Builtin::Curry)
    {
        return Some(argument);
    }
    None
}

/// Returns the inner `c` if `expr` is `const_(c)` i.e.
/// `Apply { argument: c, function: Builtin(Const) }`.
fn as_const(expr: &Expr) -> Option<&Expr> {
    if let TypedExprNode::Apply { argument, function } = &expr.node
        && is_builtin(function, Builtin::Const)
    {
        return Some(argument);
    }
    None
}

/// Returns `(left, right)` if `expr` is a two-element [`TypedExprNode::Compose`].
///
/// Used for inner sub-composes that are always binary (e.g. `.0 ≫ curry(f)`).
/// Top-level compose patterns use [`try_pairwise_in_compose`] instead.
fn as_compose(expr: &Expr) -> Option<(&Expr, &Expr)> {
    if let TypedExprNode::Compose(elts) = &expr.node
        && let [left, right] = elts.as_slice()
    {
        return Some((left, right));
    }
    None
}

/// Returns `true` if `expr` is the `id` built-in.
fn is_id(expr: &Expr) -> bool {
    is_builtin(expr, Builtin::Id)
}

/// Returns `true` if `expr` is `Proj(Index(n))` for the given `n`.
fn is_proj_idx(expr: &Expr, n: usize) -> bool {
    matches!(&expr.node, TypedExprNode::Proj(ProjKey::Index(m)) if *m == n)
}

/// Split a [`TypedExprNode::Compose`] into `(prefix, last)` if it has ≥ 2 elements.
///
/// Used by [`try_product_eta`] to match n-ary compose arms like `[f, .0]`.
fn compose_split_last(expr: &Expr) -> Option<(&[Expr], &Expr)> {
    if let TypedExprNode::Compose(elts) = &expr.node
        && let Some((last, prefix)) = elts.split_last()
        && !prefix.is_empty()
    {
        return Some((prefix, last));
    }
    None
}

// ---------------------------------------------------------------------------
// Pairwise compose helper
// ---------------------------------------------------------------------------

/// Try a pairwise rewrite rule on consecutive elements of an n-ary [`TypedExprNode::Compose`].
///
/// Iterates over consecutive pairs `(elts[i], elts[i+1])` calling `detect`.
/// On the first match, takes ownership of the compose, removes those two
/// elements, calls `apply(left, right)` to produce replacement elements, and
/// splices them back.  A single-element result is unwrapped to a bare
/// expression. Returns `true` if a rule fired.
fn try_pairwise_in_compose(
    expr: &mut Expr,
    detect: impl Fn(&Expr, &Expr) -> bool,
    apply: impl FnOnce(Expr, Expr) -> Vec<Expr>,
) -> bool {
    let TypedExprNode::Compose(elts) = &expr.node else {
        return false;
    };
    let Some(i) = elts.windows(2).position(|w| detect(&w[0], &w[1])) else {
        return false;
    };
    let TypedExpr {
        node: TypedExprNode::Compose(mut elts),
        ty,
        user_annotation,
    } = take(expr)
    else {
        unreachable!()
    };
    let right = elts.remove(i + 1);
    let left = elts.remove(i);
    let mut replacements = apply(left, right);
    for (j, r) in replacements.drain(..).enumerate() {
        elts.insert(i + j, r);
    }
    *expr = if elts.len() == 1 {
        elts.pop().unwrap()
    } else {
        Expr::compose(elts)
    };
    expr.ty = ty;
    expr.user_annotation = user_annotation;
    true
}

// ---------------------------------------------------------------------------
// Individual simplification rules
// ---------------------------------------------------------------------------

/// Compose identity: `… ≫ id ≫ …  ⟹  …` (removes `id` from any position in a compose chain)
fn try_compose_identity(expr: &mut Expr) -> bool {
    try_pairwise_in_compose(
        expr,
        |left, right| is_id(left) || is_id(right),
        |left, right| {
            if is_id(&left) {
                vec![right]
            } else {
                vec![left]
            }
        },
    )
}

/// Const reduce: `f ≫ g ▷ const  ⟹  g ▷ const` (with updated type)
///
/// When composing with a lifted constant, the constant discards its input and
/// returns the constant value. Therefore, any preceding function `f` has no effect.
/// The type of the resulting `g ▷ const` changes from `codomain(f) → codomain(g)`
/// to `domain(f) → codomain(g)`.
///
/// Operates pairwise in an n-ary compose; trailing elements are preserved.
fn try_const_reduce(expr: &mut Expr) -> bool {
    try_pairwise_in_compose(
        expr,
        |_left, right| as_const(right).is_some(),
        |left, right| {
            let Some(g) = as_const(&right) else {
                unreachable!()
            };
            let new_const_ty = match (left.ty.domain(), right.ty.codomain()) {
                (Some(dom), Some(cod)) => Type::fun(dom, cod),
                _ => Type::Hole,
            };
            let const_var_ty = fun_ty_or_hole(&g.ty, &new_const_ty);
            let const_var = Expr::builtin(Builtin::Const).with_ty(const_var_ty);
            let new_const = Expr::apply(g.clone(), const_var).with_ty(new_const_ty);
            vec![new_const]
        },
    )
}

/// Product beta (first): `⟨f, g⟩ ≫ .0  ⟹  f`
fn try_product_beta_fst(expr: &mut Expr) -> bool {
    try_pairwise_in_compose(
        expr,
        |left, right| is_proj_idx(right, 0) && as_zip(left).is_some(),
        |left, _proj| {
            let TypedExpr {
                node: TypedExprNode::Apply { argument, .. },
                ..
            } = left
            else {
                unreachable!()
            };
            let TypedExpr {
                node: TypedExprNode::Tuple(mut elts),
                ..
            } = *argument
            else {
                unreachable!()
            };
            vec![elts.swap_remove(0)]
        },
    )
}

/// Literal tuple projection: `(e₀, …, eₙ).i  ⟹  eᵢ`
///
/// Sister rule to product-beta: where product-beta reduces a *zip* of
/// morphisms followed by a projection, this reduces a *literal tuple value*
/// followed by a projection.  The rewrite is pure constant folding —
/// equationally sound anywhere the pattern appears.
///
/// In practice this fires on uncurried multi-arg UDF call sites: after
/// `inline_non_iterable_lambdas` beta-reduces the outer user-parameter lambda,
/// references like `__arg_pair.0` are left as `Apply(Tuple([list, n]),
/// Proj(0))`.  Operator conversion's list-element path needs the projection
/// folded, so this rule must fire before `operator_conversion` runs.
///
/// Out-of-range indices are intentionally a no-op: a later pass will surface
/// the real error rather than silently dropping the access here.
fn try_literal_tuple_projection(expr: &mut Expr) -> bool {
    // Look-only check first; if it matches, take ownership and rewrite.
    let matches = matches!(
        &expr.node,
        TypedExprNode::Apply { argument, function }
            if matches!(&function.node, TypedExprNode::Proj(ProjKey::Index(i))
                if matches!(&argument.node, TypedExprNode::Tuple(elts) if *i < elts.len()))
    );
    if !matches {
        return false;
    }
    let TypedExpr {
        node: TypedExprNode::Apply { argument, function },
        ..
    } = take(expr)
    else {
        unreachable!()
    };
    let TypedExprNode::Proj(ProjKey::Index(i)) = function.node else {
        unreachable!()
    };
    let TypedExpr {
        node: TypedExprNode::Tuple(mut elts),
        ..
    } = *argument
    else {
        unreachable!()
    };
    *expr = elts.swap_remove(i);
    true
}

/// Product beta (second): `⟨f, g⟩ ≫ .1  ⟹  g`
fn try_product_beta_snd(expr: &mut Expr) -> bool {
    try_pairwise_in_compose(
        expr,
        |left, right| is_proj_idx(right, 1) && as_zip(left).is_some(),
        |left, _proj| {
            let TypedExpr {
                node: TypedExprNode::Apply { argument, .. },
                ..
            } = left
            else {
                unreachable!()
            };
            let TypedExpr {
                node: TypedExprNode::Tuple(mut elts),
                ..
            } = *argument
            else {
                unreachable!()
            };
            vec![elts.swap_remove(1)]
        },
    )
}

/// CCC universal property: `⟨.1, .0 ≫ curry(f)⟩ ≫ apply  ⟹  f`
fn try_ccc_universal(expr: &mut Expr) -> bool {
    try_pairwise_in_compose(
        expr,
        |left, right| {
            is_builtin(right, Builtin::Apply)
                && as_zip(left).is_some_and(|(l, r)| {
                    is_proj_idx(l, 1)
                        && as_compose(r)
                            .is_some_and(|(cl, cr)| is_proj_idx(cl, 0) && as_curry(cr).is_some())
                })
        },
        |left, _apply| {
            let TypedExpr {
                node: TypedExprNode::Apply { argument, .. },
                ..
            } = left
            else {
                unreachable!()
            };
            let TypedExpr {
                node: TypedExprNode::Tuple(mut elts),
                ..
            } = *argument
            else {
                unreachable!()
            };
            let r = elts.swap_remove(1);
            let TypedExpr {
                node: TypedExprNode::Compose(mut r_elts),
                ..
            } = r
            else {
                unreachable!()
            };
            let curry_f = r_elts.pop().unwrap();
            let TypedExpr {
                node: TypedExprNode::Apply { argument: f, .. },
                ..
            } = curry_f
            else {
                unreachable!()
            };
            vec![*f]
        },
    )
}

/// Exponential beta: `⟨g, curry(h)⟩ ≫ apply  ⟹  ⟨id, g⟩ ≫ h`
fn try_exponential_beta(expr: &mut Expr) -> bool {
    try_pairwise_in_compose(
        expr,
        |left, right| {
            is_builtin(right, Builtin::Apply)
                && as_zip(left).is_some_and(|(_, r)| as_curry(r).is_some())
        },
        |left, _apply| {
            let TypedExpr {
                node: TypedExprNode::Apply { argument, .. },
                ..
            } = left
            else {
                unreachable!()
            };
            let TypedExpr {
                node: TypedExprNode::Tuple(mut elts),
                ..
            } = *argument
            else {
                unreachable!()
            };
            let curry_h = elts.swap_remove(1);
            let g = elts.swap_remove(0);
            let TypedExpr {
                node: TypedExprNode::Apply { argument: h, .. },
                ..
            } = curry_h
            else {
                unreachable!()
            };
            // Type id: A → A where A = domain(g).  Type zip(id, g): A → (A, B)
            // where g: A → B.  Both fall back to Hole if g has no concrete type.
            let g_dom = g.ty.domain();
            let g_cod = g.ty.codomain();
            let id_ty = g_dom
                .as_ref()
                .map(|a| Type::fun(a.clone(), a.clone()))
                .unwrap_or(Type::Hole);
            let zip_ty = match (g_dom.as_ref(), g_cod.as_ref()) {
                (Some(a), Some(c)) => Type::fun(a.clone(), Type::Tuple(vec![a.clone(), c.clone()])),
                _ => Type::Hole,
            };
            let id_node = id().with_ty(id_ty);
            let zip_node = zip_pair(id_node, g).with_ty(zip_ty);
            vec![zip_node, *h]
        },
    )
}

/// Const-apply: `⟨f, const(g)⟩ ≫ apply  ⟹  f ≫ g`
fn try_const_apply(expr: &mut Expr) -> bool {
    try_pairwise_in_compose(
        expr,
        |left, right| {
            is_builtin(right, Builtin::Apply)
                && as_zip(left).is_some_and(|(_, r)| as_const(r).is_some())
        },
        |left, _apply| {
            let TypedExpr {
                node: TypedExprNode::Apply { argument, .. },
                ..
            } = left
            else {
                unreachable!()
            };
            let TypedExpr {
                node: TypedExprNode::Tuple(mut elts),
                ..
            } = *argument
            else {
                unreachable!()
            };
            let const_g = elts.swap_remove(1);
            let f = elts.swap_remove(0);
            let TypedExpr {
                node: TypedExprNode::Apply { argument: g, .. },
                ..
            } = const_g
            else {
                unreachable!()
            };
            vec![f, *g]
        },
    )
}

/// Product eta: `⟨f ≫ .0, f ≫ .1⟩  ⟹  f`
///
/// Works for n-ary compose arms: matches when both arms end in `.0`/`.1`
/// respectively and share the same prefix (which becomes `f`).
/// Collapses a singleton prefix to a bare expression.
///
/// Analogous to the function-type eta rule `λ x → f x  ⟹  f`.
///
/// Only sound when `f`'s codomain is a 2-tuple: `⟨.0, .1⟩` is the identity on a
/// pair, but on a wider tuple it is a lossy projection that drops components
/// `≥ 2`. The guard consults `lp.ty.domain()` (the tuple being projected from,
/// i.e. the prefix's codomain) and bails out for non-pair codomains.
fn try_product_eta(expr: &mut Expr) -> bool {
    let matched = as_zip(expr).is_some_and(|(left, right)| {
        compose_split_last(left).is_some_and(|(lpfx, lp)| {
            is_proj_idx(lp, 0)
                && compose_split_last(right)
                    .is_some_and(|(rpfx, rp)| is_proj_idx(rp, 1) && lpfx == rpfx)
                && matches!(lp.ty.domain(), Some(Type::Tuple(ts)) if ts.len() == 2)
        })
    });
    if matched {
        let TypedExpr {
            node: TypedExprNode::Apply { argument, .. },
            ty,
            ..
        } = take(expr)
        else {
            unreachable!()
        };
        let TypedExpr {
            node: TypedExprNode::Tuple(mut elts),
            ..
        } = *argument
        else {
            unreachable!()
        };
        let left_compose = elts.swap_remove(0);
        let TypedExpr {
            node: TypedExprNode::Compose(mut compose_elts),
            ..
        } = left_compose
        else {
            unreachable!()
        };
        let _proj = compose_elts.pop().unwrap();
        let f = if compose_elts.len() == 1 {
            compose_elts.pop().unwrap()
        } else {
            Expr::compose(compose_elts)
        };
        *expr = f.with_ty(ty.clone());
        return true;
    }
    false
}

// ---------------------------------------------------------------------------
// Zip distribute rule
// ---------------------------------------------------------------------------

/// Zip distribute: `⟨f0, f1⟩ ≫ ⟨g, h⟩  ⟹  ⟨⟨f0, f1⟩ ≫ g, ⟨f0, f1⟩ ≫ h⟩`
///
/// Distributes a zip composition across another zip, but only when the left side
/// is itself a zip and the right-side arms will simplify nicely after the composition.
/// This latter property is called "simplifying" here and is defined in the `arm_is_simplifying` helper.
///
/// After this rule is applied, product_beta will be able to perform further simplification.
///
/// Operates pairwise in an n-ary compose; trailing elements are preserved.
fn try_zip_distribute_compose(expr: &mut Expr) -> bool {
    // Returns true if both arms are simplifying, but not both are id.
    fn is_simplifying_zip(expr: &Expr) -> bool {
        as_zip(expr)
            .is_some_and(|(a, b)| is_simplifying(a) && is_simplifying(b) && !(is_id(a) && is_id(b)))
    }

    /// Returns true if the arm is simplifying: id, projection, lifted const, or a zip with simplifying arms.
    fn is_simplifying(expr: &Expr) -> bool {
        if is_id(expr) {
            return true;
        }
        if let TypedExprNode::Proj(ProjKey::Index(_)) = &expr.node {
            return true;
        }
        // Lifted constant: <expr> ▷ const
        if let TypedExprNode::Apply {
            function,
            argument: _,
        } = &expr.node
            && is_builtin(function, Builtin::Const)
        {
            return true;
        }
        // Zip where both arms are simplifying
        if is_simplifying_zip(expr) {
            return true;
        }
        // Compose starting with projection (original behavior)
        if let TypedExprNode::Compose(elts) = &expr.node
            && let Some(first) = elts.first()
            && is_simplifying(first)
        {
            return true;
        }
        false
    }

    try_pairwise_in_compose(
        expr,
        |left, right| {
            // Match: left is a zip, right is a zip with simplifying arms
            // But don't match if both arms are just id (which would create unnecessary complexity)
            as_zip(left).is_some() && is_simplifying_zip(right)
        },
        |left, right| {
            let Some((g, h)) = as_zip(&right) else {
                unreachable!()
            };

            // Compute types for the composed expressions
            let g_ty = match (&left.ty, &g.ty) {
                (
                    Type::Fun {
                        domain: dom,
                        codomain: _,
                        ..
                    },
                    Type::Fun {
                        domain: _,
                        codomain: cod,
                        ..
                    },
                ) => Type::fun(dom.as_ref().clone(), cod.as_ref().clone()),
                _ => Type::Hole,
            };
            let h_ty = match (&left.ty, &h.ty) {
                (
                    Type::Fun {
                        domain: dom,
                        codomain: _,
                        ..
                    },
                    Type::Fun {
                        domain: _,
                        codomain: cod,
                        ..
                    },
                ) => Type::fun(dom.as_ref().clone(), cod.as_ref().clone()),
                _ => Type::Hole,
            };

            let g_compose = Expr::compose(vec![left.clone(), g.clone()]).with_ty(g_ty);
            let h_compose = Expr::compose(vec![left.clone(), h.clone()]).with_ty(h_ty);
            vec![zip_pair(g_compose, h_compose)]
        },
    )
}

/// Exponential eta: `curry(⟨.1, .0 ≫ f⟩ ≫ apply)  ⟹  f`
///
/// Matches when the inner compose ends with `⟨.1, .0 ≫ f⟩` then `apply`
/// (i.e. those are the last two elements of an n-ary inner compose).
/// Any prefix elements before the matched pair disqualify the rule, since
/// the full inner compose must be exactly `zip ≫ apply`.
fn try_exponential_eta(expr: &mut Expr) -> bool {
    let matched = as_curry(expr).is_some_and(|uncurried| {
        as_compose(uncurried).is_some_and(|(zip, ap)| {
            is_builtin(ap, Builtin::Apply)
                && as_zip(zip).is_some_and(|(proj1, proj0f)| {
                    is_proj_idx(proj1, 1)
                        && as_compose(proj0f).is_some_and(|(proj0, _)| is_proj_idx(proj0, 0))
                })
        })
    });
    if matched {
        let TypedExpr {
            node: TypedExprNode::Apply {
                argument: inner, ..
            },
            ..
        } = take(expr)
        else {
            unreachable!()
        };
        let TypedExpr {
            node: TypedExprNode::Compose(mut inner_elts),
            ..
        } = *inner
        else {
            unreachable!()
        };
        let _apply = inner_elts.pop().unwrap();
        let zip_node = inner_elts.pop().unwrap();
        let TypedExpr {
            node: TypedExprNode::Apply { argument, .. },
            ..
        } = zip_node
        else {
            unreachable!()
        };
        let TypedExpr {
            node: TypedExprNode::Tuple(mut elts),
            ..
        } = *argument
        else {
            unreachable!()
        };
        let TypedExpr {
            node: TypedExprNode::Compose(mut compose_elts),
            ..
        } = elts.swap_remove(1)
        else {
            unreachable!()
        };
        let f = compose_elts.pop().unwrap();
        *expr = f;
        return true;
    }
    false
}

/// Flatten a [`TypedExprNode::Compose`] whose elements contain nested
/// `Compose` nodes, expanding them into a single flat list.
///
/// Called bottom-up by [`flatten_all`] after CCC simplification. The CCC
/// rules produce new two-element `Compose` nodes via [`compose`]; if any of
/// their arguments were already `Compose` nodes, the result is a nested
/// `Compose` that this function normalizes.
fn try_flatten_compose(expr: &mut Expr) -> bool {
    let TypedExprNode::Compose(elts) = &expr.node else {
        return false;
    };
    if !elts
        .iter()
        .any(|e| matches!(&e.node, TypedExprNode::Compose(_)))
    {
        return false;
    }
    let TypedExpr {
        node: TypedExprNode::Compose(elts),
        ty,
        user_annotation,
    } = take(expr)
    else {
        unreachable!()
    };
    let flat: Vec<Expr> = elts.into_iter().flat_map(flatten_compose_arm).collect();
    *expr = Expr::compose(flat);
    expr.ty = ty;
    expr.user_annotation = user_annotation;
    true
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::ccl_utils::{
        apply_primitive, make_iterate, make_restrict, trivially_true_predicate,
    };
    use crate::ccl::lambda_elim::{curry, zip_pair};
    use crate::ccl::{BaseType, Expr};

    fn var(s: &str) -> Expr {
        Expr::var(s)
    }

    fn id() -> Expr {
        Expr::builtin(Builtin::Id)
    }

    fn proj_idx(n: usize) -> Expr {
        Expr::proj_index(n)
    }

    fn typed_const(c: Expr, param_ty: Type) -> Expr {
        let result_ty = fun_ty(param_ty.clone(), c.ty.clone());
        let const_var_ty = fun_ty(c.ty.clone(), result_ty.clone());
        Expr::apply(c, Expr::builtin(Builtin::Const).with_ty(const_var_ty)).with_ty(result_ty)
    }

    fn int_ty() -> Type {
        Type::Base(BaseType::Int)
    }

    fn fun_ty(a: Type, b: Type) -> Type {
        Type::Fun {
            name: None,
            domain: Box::new(a),
            codomain: Box::new(b),
        }
    }

    fn typed_compose(elts: Vec<Expr>) -> Expr {
        let mut fun_tys = Vec::new();
        for e in &elts {
            if let Type::Fun {
                domain: d,
                codomain: c,
                ..
            } = &e.ty
            {
                fun_tys.push(((*d).clone(), (*c).clone()));
            } else {
                panic!("compose element not a function: {e:?}");
            }
        }
        let ty = Type::Fun {
            name: None,
            domain: fun_tys.first().unwrap().0.clone(),
            codomain: fun_tys.last().unwrap().1.clone(),
        };
        Expr::compose(elts).with_ty(ty)
    }

    fn typed_compose2(f: Expr, g: Expr) -> Expr {
        typed_compose(vec![f, g])
    }

    /// Compose identity (left): id ≫ f  ⟹  f
    #[test]
    fn simplify_compose_identity_left() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let expr = typed_compose2(id().with_ty(f_ty.clone()), var("f").with_ty(f_ty.clone()));
        let simplified = simplify(expr);
        assert_eq!(simplified, var("f").with_ty(f_ty));
    }

    /// Compose identity (right): f ≫ id  ⟹  f
    #[test]
    fn simplify_compose_identity_right() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let expr = typed_compose2(var("f").with_ty(f_ty.clone()), id().with_ty(f_ty.clone()));
        assert_eq!(simplify(expr), var("f").with_ty(f_ty));
    }

    /// Compose identity (middle of n-ary): f ≫ id ≫ g  ⟹  f ≫ g
    #[test]
    fn simplify_compose_identity_middle() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let expr = typed_compose(vec![
            var("f").with_ty(f_ty.clone()),
            id().with_ty(f_ty.clone()),
            var("g").with_ty(f_ty.clone()),
        ]);
        let expected = typed_compose2(
            var("f").with_ty(f_ty.clone()),
            var("g").with_ty(f_ty.clone()),
        );
        assert_eq!(simplify(expr), expected);
    }

    /// Product beta (first): ⟨f, g⟩ ≫ .0  ⟹  f
    #[test]
    fn simplify_product_beta_fst() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let g_ty = fun_ty(int_ty(), int_ty());
        let f = var("f").with_ty(f_ty.clone());
        let g = var("g").with_ty(g_ty.clone());
        let zip = zip_pair(f.clone(), g); // A -> (B, C)
        let proj_ty = fun_ty(Type::Tuple(vec![int_ty(), int_ty()]), int_ty());
        let expr = typed_compose2(zip, proj_idx(0).with_ty(proj_ty));
        assert_eq!(simplify(expr), f);
    }

    /// Product beta (first) inside a longer compose: a ≫ ⟨f, g⟩ ≫ .0 ≫ b  ⟹  a ≫ f ≫ b
    #[test]
    fn simplify_product_beta_fst_pairwise() {
        let ty = fun_ty(int_ty(), int_ty());
        let a = var("a").with_ty(ty.clone());
        let f = var("f").with_ty(ty.clone());
        let g = var("g").with_ty(ty.clone());
        let b = var("b").with_ty(ty.clone());

        let zip = zip_pair(f.clone(), g);
        let proj_ty = fun_ty(Type::Tuple(vec![int_ty(), int_ty()]), int_ty());
        let proj = proj_idx(0).with_ty(proj_ty);

        let expr = typed_compose(vec![a.clone(), zip, proj, b.clone()]);
        let expected = typed_compose(vec![a, f, b]);
        assert_eq!(simplify(expr), expected);
    }

    /// Literal tuple projection: `Apply(Tuple([1, 2]), Proj(.1))  ⟹  2`
    #[test]
    fn simplify_literal_tuple_projection_in_range() {
        let lit1 = Expr::lit(Lit::Int(1)).with_ty(int_ty());
        let lit2 = Expr::lit(Lit::Int(2)).with_ty(int_ty());
        let tup_ty = Type::Tuple(vec![int_ty(), int_ty()]);
        let tuple = Expr::tuple(vec![lit1, lit2.clone()]).with_ty(tup_ty.clone());
        let proj = proj_idx(1).with_ty(fun_ty(tup_ty, int_ty()));
        let expr = Expr::apply(tuple, proj).with_ty(int_ty());
        assert_eq!(simplify(expr), lit2);
    }

    /// Non-literal argument: `Apply(Var("xs"), Proj(.0))` is *not* a literal-tuple
    /// projection — the rule must leave it alone.
    ///
    /// (Out-of-range and non-product projections can't reach `simplify`:
    /// inference rejects them, and the unified `typecheck` — run by
    /// `debug_typecheck` inside `simplify` — now enforces the `Proj` input shape.
    /// So the scaffolding here is kept well-typed; the only thing under test is
    /// that a non-literal argument leaves the rewrite untriggered.)
    #[test]
    fn simplify_literal_tuple_projection_non_literal_argument_is_noop() {
        let xs_ty = Type::Tuple(vec![int_ty()]);
        let xs = var("xs").with_ty(xs_ty.clone());
        let proj = proj_idx(0).with_ty(fun_ty(xs_ty, int_ty()));
        let expr = Expr::apply(xs, proj).with_ty(int_ty());
        assert_eq!(simplify(expr.clone()), expr);
    }

    /// Recurses through composition: a `Tuple(…).0` nested inside a Compose
    /// arm gets folded just like any other simplifiable subterm.
    #[test]
    fn simplify_literal_tuple_projection_recurses_into_compose() {
        let lit1 = Expr::lit(Lit::Int(1)).with_ty(int_ty());
        let lit2 = Expr::lit(Lit::Int(2)).with_ty(int_ty());
        let tup_ty = Type::Tuple(vec![int_ty(), int_ty()]);
        let tuple = Expr::tuple(vec![lit1.clone(), lit2]).with_ty(tup_ty.clone());
        let proj = proj_idx(0).with_ty(fun_ty(tup_ty, int_ty()));
        let projection = Expr::apply(tuple, proj).with_ty(int_ty());
        // Wrap the projection inside a const(...) so it appears as a sub-expression.
        let wrapped = typed_const(projection, int_ty());
        let simplified = simplify(wrapped);
        let expected = typed_const(lit1, int_ty());
        assert_eq!(simplified, expected);
    }

    /// Product beta (second): ⟨f, g⟩ ≫ .1  ⟹  g
    #[test]
    fn simplify_product_beta_snd() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let g_ty = fun_ty(int_ty(), int_ty());
        let f = var("f").with_ty(f_ty.clone());
        let g = var("g").with_ty(g_ty.clone());
        let zip = zip_pair(f, g.clone()); // A -> (B, C)
        let proj_ty = fun_ty(Type::Tuple(vec![int_ty(), int_ty()]), int_ty());
        let expr = typed_compose2(zip, proj_idx(1).with_ty(proj_ty));
        assert_eq!(simplify(expr), g);
    }

    /// Product beta (second) inside a longer compose: a ≫ ⟨f, g⟩ ≫ .1 ≫ b  ⟹  a ≫ g ≫ b
    #[test]
    fn simplify_product_beta_snd_pairwise() {
        let ty = fun_ty(int_ty(), int_ty());
        let a = var("a").with_ty(ty.clone());
        let f = var("f").with_ty(ty.clone());
        let g = var("g").with_ty(ty.clone());
        let b = var("b").with_ty(ty.clone());

        let zip = zip_pair(f, g.clone());
        let proj_ty = fun_ty(Type::Tuple(vec![int_ty(), int_ty()]), int_ty());
        let proj = proj_idx(1).with_ty(proj_ty);

        let expr = typed_compose(vec![a.clone(), zip, proj, b.clone()]);
        let expected = typed_compose(vec![a, g, b]);
        assert_eq!(simplify(expr), expected);
    }

    /// Product eta: ⟨f ≫ .0, f ≫ .1⟩  ⟹  f
    #[test]
    fn simplify_product_eta() {
        let f_ty = fun_ty(int_ty(), Type::Tuple(vec![int_ty(), int_ty()]));
        let f = var("f").with_ty(f_ty.clone());
        let proj0_ty = fun_ty(Type::Tuple(vec![int_ty(), int_ty()]), int_ty());
        let proj1_ty = fun_ty(Type::Tuple(vec![int_ty(), int_ty()]), int_ty());

        let expr = zip_pair(
            typed_compose2(f.clone(), proj_idx(0).with_ty(proj0_ty)),
            typed_compose2(f.clone(), proj_idx(1).with_ty(proj1_ty)),
        );
        assert_eq!(simplify(expr), f);
    }

    /// Product eta with n-ary arms: ⟨f ≫ g ≫ .0, f ≫ g ≫ .1⟩  ⟹  f ≫ g
    #[test_log::test]
    fn simplify_product_eta_nary_arms() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let g_ty = fun_ty(int_ty(), Type::Tuple(vec![int_ty(), int_ty()]));
        let f = var("f").with_ty(f_ty.clone());
        let g = var("g").with_ty(g_ty.clone());
        let proj_ty = fun_ty(Type::Tuple(vec![int_ty(), int_ty()]), int_ty());

        let expr = zip_pair(
            typed_compose(vec![
                f.clone(),
                g.clone(),
                proj_idx(0).with_ty(proj_ty.clone()),
            ]),
            typed_compose(vec![f.clone(), g.clone(), proj_idx(1).with_ty(proj_ty)]),
        );
        let expected = typed_compose2(f, g);
        assert_eq!(simplify(expr), expected);
    }

    /// Product eta must not fire when the shared prefix's codomain is wider
    /// than a pair: `⟨f ≫ .0, f ≫ .1⟩` on `f: (Int,Int,Int) → (Int,Int,Int)`
    /// is a genuine projection (it drops component 2), not the identity, so
    /// reducing to `f` would stamp an incoherent `(Int,Int,Int) → (Int,Int)`
    /// type onto `f`.
    ///
    /// Uses a non-`id` prefix so that [`try_compose_identity`] does not
    /// pre-reduce the inner composes and hide the eta redex from the rule
    /// under test.
    #[test]
    fn product_eta_rejects_non_pair_codomain() {
        let triple_ty = Type::Tuple(vec![int_ty(), int_ty(), int_ty()]);
        let f_ty = fun_ty(triple_ty.clone(), triple_ty.clone());
        let f = var("f").with_ty(f_ty);
        let proj0_ty = fun_ty(triple_ty.clone(), int_ty());
        let proj1_ty = fun_ty(triple_ty.clone(), int_ty());
        let expr = zip_pair(
            typed_compose2(f.clone(), proj_idx(0).with_ty(proj0_ty)),
            typed_compose2(f, proj_idx(1).with_ty(proj1_ty)),
        );
        let before = expr.clone();
        assert_eq!(simplify(expr), before);
    }

    /// Exponential beta: ⟨g, curry(h)⟩ ≫ apply  ⟹  ⟨id, g⟩ ≫ h  (flattened to n-ary Compose)
    #[test]
    fn simplify_exponential_beta() {
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();

        let g_ty = fun_ty(a_ty.clone(), b_ty.clone());
        let h_ty = fun_ty(Type::Tuple(vec![a_ty.clone(), b_ty.clone()]), c_ty.clone());
        let curry_h_ty = fun_ty(a_ty.clone(), fun_ty(b_ty.clone(), c_ty.clone()));

        let g = var("g").with_ty(g_ty.clone());
        let h = var("h").with_ty(h_ty.clone());
        let curry_h = curry(h.clone()).with_ty(curry_h_ty.clone());

        let zip = zip_pair(g.clone(), curry_h);
        let apply_ty = fun_ty(
            Type::Tuple(vec![b_ty.clone(), fun_ty(b_ty.clone(), c_ty.clone())]),
            c_ty.clone(),
        );
        let apply = Expr::builtin(Builtin::Apply).with_ty(apply_ty);

        let expr = typed_compose2(zip, apply);

        let id_ty = fun_ty(a_ty.clone(), a_ty.clone());
        let expected = typed_compose2(zip_pair(id().with_ty(id_ty), g), h);

        assert_eq!(simplify(expr), expected);
    }

    /// Exponential beta inside a longer compose: a ≫ ⟨g, curry(h)⟩ ≫ apply ≫ b
    #[test]
    fn simplify_exponential_beta_pairwise() {
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();

        let g_ty = fun_ty(a_ty.clone(), b_ty.clone());
        let h_ty = fun_ty(Type::Tuple(vec![a_ty.clone(), b_ty.clone()]), c_ty.clone());
        let curry_h_ty = fun_ty(a_ty.clone(), fun_ty(b_ty.clone(), c_ty.clone()));

        let aa_ty = fun_ty(a_ty.clone(), a_ty.clone());
        let bb_ty = fun_ty(c_ty.clone(), c_ty.clone());

        let aa = var("a").with_ty(aa_ty.clone());
        let bb = var("b").with_ty(bb_ty.clone());

        let g = var("g").with_ty(g_ty.clone());
        let h = var("h").with_ty(h_ty.clone());
        let curry_h = curry(h.clone()).with_ty(curry_h_ty.clone());

        let zip = zip_pair(g.clone(), curry_h);
        let apply_ty = fun_ty(
            Type::Tuple(vec![b_ty.clone(), fun_ty(b_ty.clone(), c_ty.clone())]),
            c_ty.clone(),
        );
        let apply = Expr::builtin(Builtin::Apply).with_ty(apply_ty);

        let expr = typed_compose(vec![aa.clone(), zip, apply, bb.clone()]);

        let id_ty = fun_ty(a_ty.clone(), a_ty.clone());
        let expected = typed_compose(vec![aa, zip_pair(id().with_ty(id_ty), g), h, bb]);

        assert_eq!(simplify(expr), expected);
    }

    /// Const-apply: ⟨f, const(g)⟩ ≫ apply  ⟹  f ≫ g  (flattened to n-ary Compose)
    #[test]
    fn simplify_const_apply() {
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();

        let f_ty = fun_ty(a_ty.clone(), b_ty.clone());
        let g_ty = fun_ty(b_ty.clone(), c_ty.clone());

        let f = var("f").with_ty(f_ty.clone());
        let g = var("g").with_ty(g_ty.clone());
        let const_g = typed_const(g.clone(), a_ty.clone());

        let zip = zip_pair(f.clone(), const_g);
        let apply_ty = fun_ty(
            Type::Tuple(vec![b_ty.clone(), fun_ty(b_ty.clone(), c_ty.clone())]),
            c_ty.clone(),
        );
        let apply = Expr::builtin(Builtin::Apply).with_ty(apply_ty);

        let expr = typed_compose2(zip, apply);
        let expected = typed_compose2(f, g);

        assert_eq!(simplify(expr), expected);
    }

    /// Const-apply inside a longer compose: a ≫ ⟨f, const(g)⟩ ≫ apply ≫ b  ⟹  a ≫ f ≫ g ≫ b
    #[test]
    fn simplify_const_apply_pairwise() {
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();

        let f_ty = fun_ty(a_ty.clone(), b_ty.clone());
        let g_ty = fun_ty(b_ty.clone(), c_ty.clone());

        let aa_ty = fun_ty(a_ty.clone(), a_ty.clone());
        let bb_ty = fun_ty(c_ty.clone(), c_ty.clone());

        let aa = var("a").with_ty(aa_ty.clone());
        let bb = var("b").with_ty(bb_ty.clone());

        let f = var("f").with_ty(f_ty.clone());
        let g = var("g").with_ty(g_ty.clone());
        let const_g = typed_const(g.clone(), a_ty.clone());

        let zip = zip_pair(f.clone(), const_g);
        let apply_ty = fun_ty(
            Type::Tuple(vec![b_ty.clone(), fun_ty(b_ty.clone(), c_ty.clone())]),
            c_ty.clone(),
        );
        let apply = Expr::builtin(Builtin::Apply).with_ty(apply_ty);

        let expr = typed_compose(vec![aa.clone(), zip, apply, bb.clone()]);
        let expected = typed_compose(vec![aa, f, g, bb]);

        assert_eq!(simplify(expr), expected);
    }

    // -----------------------------------------------------------------
    // Iteration guard
    //
    // The discard rules are equationally valid only on pure morphisms;
    // they must never drop an `iterate` source.  These tests pin that
    // guard: a discard-rule-shaped term *containing* an `iterate` must be
    // left intact, even though the identical iteration-free shape reduces.
    // -----------------------------------------------------------------

    /// `iterate ≫ (k ▷ const)` is a textbook `try_const_reduce` candidate
    /// (`f ≫ g ▷ const ⟹ g ▷ const`, which would drop `f` = the iterate
    /// source).  The iteration guard must skip the rule so the iterate
    /// survives.
    #[test]
    fn simplify_preserves_iteration_under_const_reduce() {
        let const_k = typed_const(Expr::lit(Lit::Int(7)).with_ty(int_ty()), int_ty());

        // Sanity: with a plain morphism in the lead, the same shape *does*
        // reduce — so the rule genuinely fires here and the guard below is
        // meaningful, not vacuous.
        let unguarded = typed_compose2(
            var("f").with_ty(fun_ty(int_ty(), int_ty())),
            const_k.clone(),
        );
        assert!(
            !matches!(simplify(unguarded).node, TypedExprNode::Compose(_)),
            "const-reduce should have collapsed the iteration-free compose"
        );

        // With an `iterate` at the head, the compose is intact.
        let guarded = typed_compose2(make_iterate(trivially_true_predicate(int_ty())), const_k);
        assert_eq!(
            simplify(guarded.clone()),
            guarded,
            "const-reduce must not drop the iterate source"
        );
    }

    /// A `restrict` filter is protected *transitively*: it is always applied
    /// to an iterate-bearing upstream (`Apply(upstream, Apply(p, Restrict))`),
    /// so the subtree contains an `iterate` and the iteration guard skips the
    /// discard rule — a `restrict`-led filter in a const-reduce position
    /// survives without `is_iteration` flagging `restrict` itself.
    #[test]
    fn simplify_preserves_restrict_over_iteration_under_const_reduce() {
        // `restrict(p)` applied to an iterate source: `{Int | p} ⇒ Int`.
        let pred = apply_primitive(
            Expr::lit(Lit::Bool(false)).with_ty(Type::Base(BaseType::Bool)),
            Builtin::Const,
            fun_ty(int_ty(), Type::Base(BaseType::Bool)),
        );
        let restricted = make_restrict(pred, make_iterate(trivially_true_predicate(int_ty())));
        let const_k = typed_const(Expr::lit(Lit::Int(7)).with_ty(int_ty()), int_ty());

        let guarded = typed_compose2(restricted, const_k);
        assert_eq!(
            simplify(guarded.clone()),
            guarded,
            "const-reduce must not drop the restrict (its upstream iterate guards it)"
        );
    }

    /// Exponential eta: curry(⟨.1, .0 ≫ f⟩ ≫ apply)  ⟹  f
    #[test]
    fn simplify_exponential_eta() {
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();
        let bc_ty = fun_ty(b_ty.clone(), c_ty.clone());
        let f_ty = fun_ty(a_ty.clone(), bc_ty.clone());
        let f = var("f").with_ty(f_ty.clone());

        let ab_tup_ty = Type::Tuple(vec![a_ty.clone(), b_ty.clone()]);
        let p1 = proj_idx(1).with_ty(fun_ty(ab_tup_ty.clone(), b_ty.clone()));
        let p0 = proj_idx(0).with_ty(fun_ty(ab_tup_ty.clone(), a_ty.clone()));

        let p0_f = typed_compose2(p0, f.clone());
        let zip = zip_pair(p1, p0_f);
        let apply = Expr::builtin(Builtin::Apply).with_ty(fun_ty(
            Type::Tuple(vec![b_ty.clone(), bc_ty.clone()]),
            c_ty.clone(),
        ));
        let inner_compose = typed_compose2(zip, apply);

        let curry_var =
            Expr::builtin(Builtin::Curry).with_ty(fun_ty(inner_compose.ty.clone(), f_ty.clone()));
        let expr = Expr::apply(inner_compose, curry_var).with_ty(f_ty.clone());

        assert_eq!(simplify(expr), f);
    }

    /// CCC universal: `⟨.1, .0 ≫ curry(f)⟩ ≫ apply  ⟹  f`
    #[test]
    fn simplify_ccc_universal() {
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();

        let f_ty = fun_ty(Type::Tuple(vec![a_ty.clone(), b_ty.clone()]), c_ty.clone());
        let f = var("f").with_ty(f_ty.clone());

        let curry_f_ty = fun_ty(a_ty.clone(), fun_ty(b_ty.clone(), c_ty.clone()));
        let curry_var =
            Expr::builtin(Builtin::Curry).with_ty(fun_ty(f_ty.clone(), curry_f_ty.clone()));
        let curry_f = Expr::apply(f.clone(), curry_var).with_ty(curry_f_ty.clone());

        let ab_tup_ty = Type::Tuple(vec![a_ty.clone(), b_ty.clone()]);
        let p1 = proj_idx(1).with_ty(fun_ty(ab_tup_ty.clone(), b_ty.clone()));
        let p0 = proj_idx(0).with_ty(fun_ty(ab_tup_ty.clone(), a_ty.clone()));

        let p0_curry_f = typed_compose2(p0, curry_f);
        let zip = zip_pair(p1, p0_curry_f);
        let apply = Expr::builtin(Builtin::Apply).with_ty(fun_ty(
            Type::Tuple(vec![b_ty.clone(), fun_ty(b_ty.clone(), c_ty.clone())]),
            c_ty.clone(),
        ));

        let expr = typed_compose2(zip, apply);
        assert_eq!(simplify(expr), f);
    }

    /// CCC universal inside a longer compose: a ≫ ⟨.1, .0 ≫ curry(f)⟩ ≫ apply ≫ b  ⟹  a ≫ f ≫ b
    #[test]
    fn simplify_ccc_universal_pairwise() {
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();

        let f_ty = fun_ty(Type::Tuple(vec![a_ty.clone(), b_ty.clone()]), c_ty.clone());
        let f = var("f").with_ty(f_ty.clone());

        let aa_ty = fun_ty(a_ty.clone(), Type::Tuple(vec![a_ty.clone(), b_ty.clone()]));
        let bb_ty = fun_ty(c_ty.clone(), c_ty.clone());
        let aa = var("a").with_ty(aa_ty.clone());
        let bb = var("b").with_ty(bb_ty.clone());

        let curry_f_ty = fun_ty(a_ty.clone(), fun_ty(b_ty.clone(), c_ty.clone()));
        let curry_var =
            Expr::builtin(Builtin::Curry).with_ty(fun_ty(f_ty.clone(), curry_f_ty.clone()));
        let curry_f = Expr::apply(f.clone(), curry_var).with_ty(curry_f_ty.clone());

        let ab_tup_ty = Type::Tuple(vec![a_ty.clone(), b_ty.clone()]);
        let p1 = proj_idx(1).with_ty(fun_ty(ab_tup_ty.clone(), b_ty.clone()));
        let p0 = proj_idx(0).with_ty(fun_ty(ab_tup_ty.clone(), a_ty.clone()));

        let p0_curry_f = typed_compose2(p0, curry_f);
        let zip = zip_pair(p1, p0_curry_f);
        let apply = Expr::builtin(Builtin::Apply).with_ty(fun_ty(
            Type::Tuple(vec![b_ty.clone(), fun_ty(b_ty.clone(), c_ty.clone())]),
            c_ty.clone(),
        ));

        let expr = typed_compose(vec![aa.clone(), zip, apply, bb.clone()]);
        let expected = typed_compose(vec![aa, f, bb]);
        assert_eq!(simplify(expr), expected);
    }

    /// Flatten: f ≫ g ≫ h (binary tree)  ⟹  Compose([f, g, h])
    #[test]
    fn simplify_flatten_compose() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let f = var("f").with_ty(f_ty.clone());
        let g = var("g").with_ty(f_ty.clone());
        let h = var("h").with_ty(f_ty.clone());

        let expr = typed_compose2(f.clone(), typed_compose2(g.clone(), h.clone()));
        let expected = typed_compose(vec![f, g, h]);
        assert_eq!(simplify(expr), expected);
    }

    /// Flatten left-associative: (f ≫ g) ≫ h  ⟹  Compose([f, g, h])
    #[test]
    fn simplify_flatten_compose_left_assoc() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let f = var("f").with_ty(f_ty.clone());
        let g = var("g").with_ty(f_ty.clone());
        let h = var("h").with_ty(f_ty.clone());

        let expr = typed_compose2(typed_compose2(f.clone(), g.clone()), h.clone());
        let expected = typed_compose(vec![f, g, h]);
        assert_eq!(simplify(expr), expected);
    }

    /// Zip beta, n1=0 (id left): ⟨id, f⟩ ≫ ⟨.0 ≫ g, .1⟩  ⟹  ⟨g, f⟩
    #[test]
    fn simplify_zip_beta_n1_0_id() {
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();

        let id_val = id().with_ty(fun_ty(a_ty.clone(), a_ty.clone()));
        let f = var("f").with_ty(fun_ty(a_ty.clone(), b_ty.clone()));
        let zip1 = zip_pair(id_val, f.clone());

        let g = var("g").with_ty(fun_ty(a_ty.clone(), c_ty.clone()));
        let tup_ty = Type::Tuple(vec![a_ty.clone(), b_ty.clone()]);
        let p0 = proj_idx(0).with_ty(fun_ty(tup_ty.clone(), a_ty.clone()));
        let p1 = proj_idx(1).with_ty(fun_ty(tup_ty.clone(), b_ty.clone()));

        let p0_g = typed_compose2(p0, g.clone());
        let zip2 = zip_pair(p0_g, p1);

        let expr = typed_compose2(zip1, zip2);
        let expected = zip_pair(g, f);
        assert_eq!(simplify(expr), expected);
    }

    /// Zip beta, n1=0 (general h): ⟨h, f⟩ ≫ ⟨.0 ≫ g, .1⟩  ⟹  ⟨h ≫ g, f⟩
    #[test]
    fn simplify_zip_beta_n1_0_general() {
        let x_ty = int_ty();
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();

        let h = var("h").with_ty(fun_ty(x_ty.clone(), a_ty.clone()));
        let f = var("f").with_ty(fun_ty(x_ty.clone(), b_ty.clone()));
        let zip1 = zip_pair(h.clone(), f.clone());

        let g = var("g").with_ty(fun_ty(a_ty.clone(), c_ty.clone()));
        let tup_ty = Type::Tuple(vec![a_ty.clone(), b_ty.clone()]);
        let p0 = proj_idx(0).with_ty(fun_ty(tup_ty.clone(), a_ty.clone()));
        let p1 = proj_idx(1).with_ty(fun_ty(tup_ty.clone(), b_ty.clone()));

        let p0_g = typed_compose2(p0, g.clone());
        let zip2 = zip_pair(p0_g, p1);

        let expr = typed_compose2(zip1, zip2);
        let expected = zip_pair(typed_compose2(h, g), f);
        assert_eq!(simplify(expr), expected);
    }

    /// Zip beta, n1=1 (id left): ⟨id, f⟩ ≫ ⟨.1, .0 ≫ g⟩  ⟹  ⟨f, g⟩
    #[test]
    fn simplify_zip_beta_n1_1_id() {
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();

        let id_val = id().with_ty(fun_ty(a_ty.clone(), a_ty.clone()));
        let f = var("f").with_ty(fun_ty(a_ty.clone(), b_ty.clone()));
        let zip1 = zip_pair(id_val, f.clone());

        let g = var("g").with_ty(fun_ty(a_ty.clone(), c_ty.clone()));
        let tup_ty = Type::Tuple(vec![a_ty.clone(), b_ty.clone()]);
        let p0 = proj_idx(0).with_ty(fun_ty(tup_ty.clone(), a_ty.clone()));
        let p1 = proj_idx(1).with_ty(fun_ty(tup_ty.clone(), b_ty.clone()));

        let p0_g = typed_compose2(p0, g.clone());
        let zip2 = zip_pair(p1, p0_g);

        let expr = typed_compose2(zip1, zip2);
        let expected = zip_pair(f, g);
        assert_eq!(simplify(expr), expected);
    }

    /// Zip beta, n1=1 (general h): ⟨h, f⟩ ≫ ⟨.1, .0 ≫ g⟩  ⟹  ⟨f, h ≫ g⟩
    #[test]
    fn simplify_zip_beta_n1_1_general() {
        let x_ty = int_ty();
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();

        let h = var("h").with_ty(fun_ty(x_ty.clone(), a_ty.clone()));
        let f = var("f").with_ty(fun_ty(x_ty.clone(), b_ty.clone()));
        let zip1 = zip_pair(h.clone(), f.clone());

        let g = var("g").with_ty(fun_ty(a_ty.clone(), c_ty.clone()));
        let tup_ty = Type::Tuple(vec![a_ty.clone(), b_ty.clone()]);
        let p0 = proj_idx(0).with_ty(fun_ty(tup_ty.clone(), a_ty.clone()));
        let p1 = proj_idx(1).with_ty(fun_ty(tup_ty.clone(), b_ty.clone()));

        let p0_g = typed_compose2(p0, g.clone());
        let zip2 = zip_pair(p1, p0_g);

        let expr = typed_compose2(zip1, zip2);
        let expected = zip_pair(f, typed_compose2(h, g));
        assert_eq!(simplify(expr), expected);
    }

    /// Zip beta, both arms suffixed: ⟨h, f⟩ ≫ ⟨.0 ≫ g, .1 ≫ i⟩  ⟹  ⟨h ≫ g, f ≫ i⟩
    #[test]
    fn simplify_zip_beta_both_arms() {
        let x_ty = int_ty();
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();
        let d_ty = int_ty();

        let h = var("h").with_ty(fun_ty(x_ty.clone(), a_ty.clone()));
        let f = var("f").with_ty(fun_ty(x_ty.clone(), b_ty.clone()));
        let zip1 = zip_pair(h.clone(), f.clone());

        let g = var("g").with_ty(fun_ty(a_ty.clone(), c_ty.clone()));
        let i = var("i").with_ty(fun_ty(b_ty.clone(), d_ty.clone()));

        let tup_ty = Type::Tuple(vec![a_ty.clone(), b_ty.clone()]);
        let p0 = proj_idx(0).with_ty(fun_ty(tup_ty.clone(), a_ty.clone()));
        let p1 = proj_idx(1).with_ty(fun_ty(tup_ty.clone(), b_ty.clone()));

        let p0_g = typed_compose2(p0, g.clone());
        let p1_i = typed_compose2(p1, i.clone());
        let zip2 = zip_pair(p0_g, p1_i);

        let expr = typed_compose2(zip1, zip2);
        let expected = zip_pair(typed_compose2(h, g), typed_compose2(f, i));
        assert_eq!(simplify(expr), expected);
    }

    /// Zip beta in n-ary compose: a ≫ ⟨h, f⟩ ≫ ⟨.0 ≫ g, .1⟩ ≫ b  ⟹  a ≫ ⟨h ≫ g, f⟩ ≫ b
    #[test]
    fn simplify_zip_beta_pairwise() {
        let x_ty = int_ty();
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();

        let aa = var("a").with_ty(fun_ty(x_ty.clone(), x_ty.clone()));
        let h = var("h").with_ty(fun_ty(x_ty.clone(), a_ty.clone()));
        let f = var("f").with_ty(fun_ty(x_ty.clone(), b_ty.clone()));
        let zip1 = zip_pair(h.clone(), f.clone());

        let g = var("g").with_ty(fun_ty(a_ty.clone(), c_ty.clone()));
        let tup_ty = Type::Tuple(vec![a_ty.clone(), b_ty.clone()]);
        let p0 = proj_idx(0).with_ty(fun_ty(tup_ty.clone(), a_ty.clone()));
        let p1 = proj_idx(1).with_ty(fun_ty(tup_ty.clone(), b_ty.clone()));

        let p0_g = typed_compose2(p0, g.clone());
        let zip2 = zip_pair(p0_g, p1);

        let bb = var("b").with_ty(fun_ty(
            Type::Tuple(vec![c_ty.clone(), b_ty.clone()]),
            x_ty.clone(),
        ));

        let expr = typed_compose(vec![aa.clone(), zip1, zip2, bb.clone()]);
        let expected = typed_compose(vec![aa, zip_pair(typed_compose2(h, g), f), bb]);
        assert_eq!(simplify(expr), expected);
    }

    /// Zip beta with n-ary arm: ⟨h, f⟩ ≫ ⟨.0 ≫ g ≫ k, .1⟩  ⟹  ⟨h ≫ g ≫ k, f⟩
    #[test]
    fn simplify_zip_beta_nary_arm() {
        let x_ty = int_ty();
        let a_ty = int_ty();
        let b_ty = int_ty();
        let c_ty = int_ty();
        let d_ty = int_ty();

        let h = var("h").with_ty(fun_ty(x_ty.clone(), a_ty.clone()));
        let f = var("f").with_ty(fun_ty(x_ty.clone(), b_ty.clone()));
        let zip1 = zip_pair(h.clone(), f.clone());

        let g = var("g").with_ty(fun_ty(a_ty.clone(), c_ty.clone()));
        let k = var("k").with_ty(fun_ty(c_ty.clone(), d_ty.clone()));

        let tup_ty = Type::Tuple(vec![a_ty.clone(), b_ty.clone()]);
        let p0 = proj_idx(0).with_ty(fun_ty(tup_ty.clone(), a_ty.clone()));
        let p1 = proj_idx(1).with_ty(fun_ty(tup_ty.clone(), b_ty.clone()));

        let p0_g_k = typed_compose(vec![p0, g.clone(), k.clone()]);
        let zip2 = zip_pair(p0_g_k, p1);

        let expr = typed_compose2(zip1, zip2);
        let expected = zip_pair(typed_compose(vec![h, g, k]), f);
        assert_eq!(simplify(expr), expected);
    }

    /// Idempotency: simplify(simplify(e)) == simplify(e)
    #[test]
    fn simplify_idempotent() {
        let f_ty = fun_ty(int_ty(), int_ty());
        let f = var("f").with_ty(f_ty.clone());
        let g = var("g").with_ty(f_ty.clone());

        let expr = typed_compose2(
            id().with_ty(f_ty.clone()),
            typed_compose2(f.clone(), g.clone()),
        );
        let once = simplify(expr);
        let twice = simplify(once.clone());
        assert_eq!(once, twice);
    }

    /// Zip distribute doesn't match when left is not a zip
    /// f ≫ ⟨.0, .1⟩ where f is not a zip
    /// Should not distribute
    #[test]
    fn simplify_zip_no_distribute_when_left_not_zip() {
        // Left is NOT a zip: just a function
        let f = var("f").with_ty(fun_ty(int_ty(), Type::Tuple(vec![int_ty(), int_ty()])));

        // Right is a zip with simplifying arms
        let tup_ty = Type::Tuple(vec![int_ty(), int_ty()]);
        let p0 = proj_idx(0).with_ty(fun_ty(tup_ty.clone(), int_ty()));
        let p1 = proj_idx(1).with_ty(fun_ty(tup_ty.clone(), int_ty()));
        let zip = zip_pair(p0, p1);

        let expr = typed_compose2(f.clone(), zip.clone());
        let simplified = simplify(expr);

        // Should NOT distribute because left is not a zip
        assert_eq!(simplified, typed_compose2(f, zip));
    }

    /// Zip distribute with projection arms: ⟨f0, f1⟩ ≫ ⟨.0, .1⟩
    /// Both arms are projections (simplifying), but not both id
    #[test]
    fn simplify_zip_distribute_projection_arms() {
        let int_fun = fun_ty(int_ty(), int_ty());
        let int_pair = Type::Tuple(vec![int_ty(), int_ty()]);

        let f0 = var("f0").with_ty(int_fun.clone());
        let f1 = var("f1").with_ty(int_fun.clone());
        let zip1 = zip_pair(f0.clone(), f1.clone());

        // Both .0 and .1 are simplifying projections
        let p0 = proj_idx(0).with_ty(fun_ty(int_pair.clone(), int_ty()));
        let p1 = proj_idx(1).with_ty(fun_ty(int_pair, int_ty()));

        let zip2 = zip_pair(p0, p1);

        let expr = typed_compose2(zip1.clone(), zip2);
        let simplified = simplify(expr);

        // Should distribute: ⟨f0 ≫ .0, f1 ≫ .1⟩
        // Then further simplify via product_beta: ⟨f0, f1⟩
        assert_eq!(simplified, zip1);
    }

    /// Zip distribute with composed arms: ⟨f0, f1⟩ ≫ ⟨.0 ≫ g, .1 ≫ h⟩
    /// where both arms are composes starting with projections (simplifying)
    #[test]
    fn simplify_zip_distribute_composed_arms() {
        let int_fun = fun_ty(int_ty(), int_ty());
        let int_pair = Type::Tuple(vec![int_ty(), int_ty()]);

        let f0 = var("f0").with_ty(int_fun.clone());
        let f1 = var("f1").with_ty(int_fun.clone());
        let zip1 = zip_pair(f0.clone(), f1.clone());

        // .0 ≫ g and .1 ≫ h are composes starting with projections (simplifying)
        let p0 = proj_idx(0).with_ty(fun_ty(int_pair.clone(), int_ty()));
        let p1 = proj_idx(1).with_ty(fun_ty(int_pair, int_ty()));

        let g = var("g").with_ty(int_fun.clone());
        let h = var("h").with_ty(int_fun.clone());

        let p0_g = typed_compose2(p0, g.clone());
        let p1_h = typed_compose2(p1, h.clone());
        let zip2 = zip_pair(p0_g, p1_h);

        let expr = typed_compose2(zip1.clone(), zip2);
        let simplified = simplify(expr);

        // Should distribute: ⟨f0 ≫ (.0 ≫ g), f1 ≫ (.1 ≫ h)⟩
        // Which flattens to: ⟨f0 ≫ .0 ≫ g, f1 ≫ .1 ≫ h⟩
        // Then product_beta simplifies: ⟨f0 ≫ g, f1 ≫ h⟩
        let expected = zip_pair(typed_compose2(f0.clone(), g), typed_compose2(f1.clone(), h));
        assert_eq!(simplified, expected);
    }

    /// Zip distribute in n-ary compose: a ≫ ⟨f0, f1⟩ ≫ ⟨.0, .1⟩ ≫ b
    /// where right zip has simplifying arms (both projections)
    #[test]
    fn simplify_zip_distribute_nary_compose() {
        let int_fun = fun_ty(int_ty(), int_ty());
        let int_pair = Type::Tuple(vec![int_ty(), int_ty()]);

        let aa = var("a").with_ty(int_fun.clone());
        let f0 = var("f0").with_ty(int_fun.clone());
        let f1 = var("f1").with_ty(int_fun.clone());
        let zip1 = zip_pair(f0.clone(), f1.clone());

        // Both .0 and .1 are simplifying projections
        let p0 = proj_idx(0).with_ty(fun_ty(int_pair.clone(), int_ty()));
        let p1 = proj_idx(1).with_ty(fun_ty(int_pair.clone(), int_ty()));
        let zip2 = zip_pair(p0, p1);

        let bb = var("b").with_ty(fun_ty(int_pair, int_ty()));

        let expr = typed_compose(vec![aa.clone(), zip1.clone(), zip2, bb.clone()]);
        let simplified = simplify(expr);

        // Should distribute: ⟨f0 ≫ .0, f1 ≫ .1⟩ then simplify via product_beta to ⟨f0, f1⟩
        let expected = typed_compose(vec![aa, zip1, bb]);
        assert_eq!(simplified, expected);
    }

    /// Zip distribute with composed/projected arms: ⟨f0, f1⟩ ≫ ⟨.0 ≫ id, .1 ≫ id⟩
    /// Both arms are composes starting with projections (simplifying)
    #[test]
    fn simplify_zip_distribute_project_compose_arms() {
        let int_fun = fun_ty(int_ty(), int_ty());
        let int_pair = Type::Tuple(vec![int_ty(), int_ty()]);

        let f0 = var("f0").with_ty(int_fun.clone());
        let f1 = var("f1").with_ty(int_fun.clone());
        let zip1 = zip_pair(f0.clone(), f1.clone());

        // Both arms are composes: projection followed by identity
        let p0 = proj_idx(0).with_ty(fun_ty(int_pair.clone(), int_ty()));
        let p1 = proj_idx(1).with_ty(fun_ty(int_pair, int_ty()));
        let id_fn = id().with_ty(int_fun.clone());

        let p0_id = typed_compose2(p0, id_fn.clone());
        let p1_id = typed_compose2(p1, id_fn);
        let zip2 = zip_pair(p0_id, p1_id);

        let expr = typed_compose2(zip1.clone(), zip2);
        let simplified = simplify(expr);

        // Should distribute and simplify back to zip1 via product_beta
        assert_eq!(simplified, zip1);
    }

    /// Zip distribute with composed projection arms (matching full behavior)
    /// ⟨f0, f1⟩ ≫ ⟨.0 ≫ id, .1 ≫ id⟩ (simplifying arms)
    #[test]
    fn simplify_zip_distribute_complex_arms() {
        let int_fun = fun_ty(int_ty(), int_ty());
        let int_pair = Type::Tuple(vec![int_ty(), int_ty()]);

        let f0 = var("f0").with_ty(int_fun.clone());
        let f1 = var("f1").with_ty(int_fun.clone());
        let zip1 = zip_pair(f0.clone(), f1.clone());

        // .0 ≫ id and .1 ≫ id are projections composed with identity (simplifying)
        let p0 = proj_idx(0).with_ty(fun_ty(int_pair.clone(), int_ty()));
        let p1 = proj_idx(1).with_ty(fun_ty(int_pair, int_ty()));
        let id_fn = id().with_ty(int_fun.clone());

        let p0_id = typed_compose2(p0, id_fn.clone());
        let p1_id = typed_compose2(p1, id_fn);
        let zip2 = zip_pair(p0_id, p1_id);

        let expr = typed_compose2(zip1.clone(), zip2);
        let simplified = simplify(expr);

        // After distribution: ⟨f0 ≫ (.0 ≫ id), f1 ≫ (.1 ≫ id)⟩
        // After flattening: ⟨f0 ≫ .0 ≫ id, f1 ≫ .1 ≫ id⟩
        // After product_beta: ⟨f0 ≫ id, f1 ≫ id⟩
        // After compose identity: ⟨f0, f1⟩
        assert_eq!(simplified, zip1);
    }

    /// `String + String` as a raw `BinOp` is rewritten to `Concat`.  This is
    /// the form left behind by lambda elimination's constant short-circuit
    /// when the lambda body doesn't reference its parameter.
    #[test]
    fn simplify_string_add_to_concat_binop_form() {
        let s_ty = Type::Base(BaseType::String);
        let lhs = Expr::lit(Lit::String("a".into())).with_ty(s_ty.clone());
        let rhs = Expr::lit(Lit::String("b".into())).with_ty(s_ty.clone());
        let expr =
            Expr::binop(lhs, BinOpKind::Arithmetic(ArithmeticKind::Add), rhs).with_ty(s_ty.clone());
        let simplified = simplify(expr);
        let TypedExprNode::BinOp { op, .. } = simplified.node else {
            panic!("expected BinOp, got {:?}", simplified.node);
        };
        assert_eq!(op, BinOpKind::Concat);
    }

    /// `String + String` desugared to `Builtin(BinOp(Add))` (the form lambda
    /// elimination produces inside lambda bodies that reference their
    /// parameter) is also rewritten to `Concat`.
    #[test]
    fn simplify_string_add_to_concat_builtin_form() {
        let s_ty = Type::Base(BaseType::String);
        let arg_ty = Type::Tuple(vec![s_ty.clone(), s_ty.clone()]);
        let fn_ty = fun_ty(arg_ty, s_ty);
        let mut expr = Expr::builtin(Builtin::BinOp(BinOpKind::Arithmetic(ArithmeticKind::Add)))
            .with_ty(fn_ty);
        // simplify rewrites the inner op in place; call directly to avoid
        // packing it into an enclosing Apply just for the test.
        assert!(try_string_add_to_concat(&mut expr));
        let TypedExprNode::Builtin(Builtin::BinOp(op)) = &expr.node else {
            panic!("expected Builtin(BinOp), got {:?}", expr.node);
        };
        assert_eq!(*op, BinOpKind::Concat);
    }

    /// `Int + Int` as a `Builtin(BinOp(Add))` is left untouched.
    #[test]
    fn simplify_int_add_builtin_unchanged() {
        let arg_ty = Type::Tuple(vec![int_ty(), int_ty()]);
        let fn_ty = fun_ty(arg_ty, int_ty());
        let mut expr = Expr::builtin(Builtin::BinOp(BinOpKind::Arithmetic(ArithmeticKind::Add)))
            .with_ty(fn_ty);
        assert!(!try_string_add_to_concat(&mut expr));
    }
}
