//! CCC simplification pass for CCL.
//!
//! Applies algebraic rewrite rules to a point-free CCL expression until no
//! further changes occur (fixed-point iteration).  All rules are
//! equationally valid in any Cartesian Closed Category.
//!
//! # Entry point
//!
//! [`simplify`] runs all rules to a fixed point.
//!
//! # Rule summary
//!
//! Rules that match a compose pattern operate *pairwise*: they scan every
//! consecutive `(elts[i], elts[i+1])` pair inside an n-ary
//! [`TypedExprNode::Compose`] and fire on the first matching pair.
//!
//! | Rule | Pattern | Reduction |
//! |------|---------|-----------|
//! | Compose identity | `… ≫ id ≫ …` / `… ≫ id ≫ …` | remove `id` |
//! | Const reduce | `f ≫ g ▷ const` | `g ▷ const` |
//! | Product beta (fst) | `⟨f, g⟩ ≫ .0` | `f` |
//! | Product beta (snd) | `⟨f, g⟩ ≫ .1` | `g` |
//! | Literal tuple projection | `(e₀, …, eₙ).i` | `eᵢ` |
//! | CCC universal | `⟨.1, .0 ≫ curry(f)⟩ ≫ apply` | `f` |
//! | Exponential beta | `⟨g, curry(h)⟩ ≫ apply` | `⟨id, g⟩ ≫ h` |
//! | Exponential eta | `curry(⟨.1, .0 ≫ f⟩ ≫ apply)` | `f` |
//! | Const-apply | `⟨f, const(g)⟩ ≫ apply` | `f ≫ g` |
//! | Product eta | `⟨f ≫ .0, f ≫ .1⟩` | `f` |
//! | Flatten compose | `Compose([…, Compose([…]), …])` | `Compose([…flat…])` |
//! | Flatten union | `(a @ b) @ c` | `CollectionUnion(a, b, c)` |
//! | Zip distribute | `⟨f0, f1⟩ ≫ ⟨g, h⟩` (if g,h will simplify) | `⟨⟨f0, f1⟩ ≫ g, ⟨f0, f1⟩ ≫ h⟩` |
//! | Drop pure ExprStmt | `ExprStmt { expr, body }` (if `expr` has no `Feed`) | `body` |

use crate::ccl::infer::debug_typecheck;
use crate::ccl::lambda_elim::{fun_ty_or_hole, id, zip_pair};
use crate::ccl::{Builtin, Expr, Lit, ProjKey, RefinementKind, Type, TypedExpr, TypedExprNode};

/// Returns `true` if `expr` directly references the given built-in primitive.
fn is_builtin(expr: &Expr, b: Builtin) -> bool {
    matches!(&expr.node, TypedExprNode::Builtin(x) if *x == b)
}

// ---------------------------------------------------------------------------
// Simplification pass
// ---------------------------------------------------------------------------

/// Apply the CCC simplification rules to `expr` until no further changes occur.
///
/// Runs [`simplify_once`] bottom-up passes until no rule fires.
pub fn simplify(mut expr: Expr) -> Expr {
    while simplify_once(&mut expr) {}
    expr
}

/// One bottom-up simplification pass. Returns `true` if any rule fired.
fn simplify_once(expr: &mut Expr) -> bool {
    let mut changed = false;
    if let Type::Fun(domain, _) = &mut expr.ty {
        if let Type::Refinement(_, refinment) = &mut **domain {
            let RefinementKind::Predicate(pred) = &refinment.kind;
            changed = simplify_once(&mut pred.borrow_mut())
        }
    }
    changed |= recurse_simplify(expr);
    changed |= apply_simplification_rules(expr);
    changed
}

/// Recursively apply [`simplify_once`] to all child expressions (bottom-up).
///
/// Returns `true` if any child was modified.
fn recurse_simplify(expr: &mut Expr) -> bool {
    let mut changed = match &mut expr.node {
        TypedExprNode::Apply { function, argument } => {
            simplify_once(function) | simplify_once(argument)
        }
        TypedExprNode::BinOp { left, right, .. } => simplify_once(left) | simplify_once(right),
        TypedExprNode::UnaryOp(_, inner) => simplify_once(inner),
        TypedExprNode::Lambda { body, .. } => simplify_once(body),
        TypedExprNode::Let {
            bound_expr, body, ..
        } => simplify_once(bound_expr) | simplify_once(body),
        TypedExprNode::Tuple(elts) | TypedExprNode::List(elts) | TypedExprNode::Compose(elts) => {
            elts.iter_mut().fold(false, |c, e| c | simplify_once(e))
        }
        TypedExprNode::Record(fields) => fields
            .iter_mut()
            .fold(false, |c, (_, e)| c | simplify_once(e)),
        TypedExprNode::Case { branches } => branches.iter_mut().fold(false, |c, b| {
            c | simplify_once(&mut b.guard) | simplify_once(&mut b.body)
        }),
        TypedExprNode::Join {
            loop_body,
            outer_body,
            ..
        } => simplify_once(loop_body) | simplify_once(outer_body),
        TypedExprNode::Jump { args, .. } => {
            args.iter_mut().fold(false, |c, a| c | simplify_once(a))
        }
        TypedExprNode::Aggregate { input, .. } => simplify_once(input),
        TypedExprNode::ExprStmt { expr, body } => simplify_once(expr) | simplify_once(body),
        TypedExprNode::Feed { value, .. } | TypedExprNode::Define { value, .. } => {
            simplify_once(value)
        }
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Defer => false,
    };
    // After simplifying children, propagate the Let body's type up to the Let
    // itself. Simplification can change the body's type (e.g., union flattening
    // rewrites Fun(Union(Union(A,B),C), D) → Fun(Union(A,B,C), D)); the Let
    // must stay in sync so downstream passes see a consistent representation.
    if let TypedExprNode::Let { body, .. } = &expr.node {
        let body_ty = body.ty.clone();
        if expr.ty != body_ty {
            expr.ty = body_ty;
            changed = true;
        }
    }
    changed
}

/// Temporarily take ownership of `expr`, leaving a cheap placeholder.
///
/// The caller **must** write a valid expression back to `*expr` before
/// returning; the placeholder is never externally observable.
fn take(expr: &mut Expr) -> Expr {
    std::mem::replace(expr, Expr::lit(Lit::Int(0)))
}

/// Returns `true` if `expr` or any of its sub-expressions is a [`TypedExprNode::Feed`].
fn contains_feed(expr: &Expr) -> bool {
    match &expr.node {
        TypedExprNode::Feed { .. } | TypedExprNode::Define { .. } => true,
        TypedExprNode::Let {
            bound_expr, body, ..
        } => contains_feed(bound_expr) || contains_feed(body),
        TypedExprNode::Apply { function, argument } => {
            contains_feed(function) || contains_feed(argument)
        }
        TypedExprNode::BinOp { left, right, .. } => contains_feed(left) || contains_feed(right),
        TypedExprNode::UnaryOp(_, inner) => contains_feed(inner),
        TypedExprNode::Lambda { body, .. } => contains_feed(body),
        TypedExprNode::Aggregate { input, .. } => contains_feed(input),
        TypedExprNode::Tuple(elts) | TypedExprNode::List(elts) | TypedExprNode::Compose(elts) => {
            elts.iter().any(contains_feed)
        }
        TypedExprNode::Record(fields) => fields.iter().any(|(_, e)| contains_feed(e)),
        TypedExprNode::Case { branches } => branches
            .iter()
            .any(|b| contains_feed(&b.guard) || contains_feed(&b.body)),
        TypedExprNode::Join {
            loop_body,
            outer_body,
            ..
        } => contains_feed(loop_body) || contains_feed(outer_body),
        TypedExprNode::Jump { args, .. } => args.iter().any(contains_feed),
        TypedExprNode::ExprStmt { expr, body } => contains_feed(expr) || contains_feed(body),
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Defer => false,
    }
}

/// Drop pure `ExprStmt`: `ExprStmt { expr, body }  ⟹  body` when `expr` contains no `Feed`.
///
/// An `ExprStmt` whose statement sub-expression has no side-effectful handle
/// binding is a no-op: the expression is evaluated and discarded. Replacing the
/// whole node with `body` is safe because nothing in the body depends on the
/// discarded value.
fn try_drop_pure_expr_stmt(expr: &mut Expr) -> bool {
    let TypedExprNode::ExprStmt { expr: inner, .. } = &expr.node else {
        return false;
    };
    if contains_feed(inner) {
        return false;
    }
    let TypedExprNode::ExprStmt { body, .. } = take(expr).node else {
        unreachable!()
    };
    *expr = *body;
    true
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
fn apply_simplification_rules(expr: &mut Expr) -> bool {
    let mut changed = false;
    changed |= check(try_compose_identity(expr), expr);
    changed |= check(try_const_reduce(expr), expr);
    changed |= check(try_product_beta_fst(expr), expr);
    changed |= check(try_product_beta_snd(expr), expr);
    changed |= check(try_literal_tuple_projection(expr), expr);
    changed |= check(try_ccc_universal(expr), expr);
    changed |= check(try_exponential_beta(expr), expr);
    changed |= check(try_exponential_eta(expr), expr);
    changed |= check(try_const_apply(expr), expr);
    changed |= check(try_product_eta(expr), expr);
    changed |= check(try_flatten_compose(expr), expr);
    changed |= check(try_flatten_collection_union(expr), expr);
    changed |= check(try_zip_distribute_compose(expr), expr);
    changed |= check(try_drop_pure_expr_stmt(expr), expr);

    changed
}

fn check(changed: bool, expr: &Expr) -> bool {
    debug_typecheck(expr);
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
    if let TypedExprNode::Apply { argument, function } = &expr.node {
        if is_builtin(function, Builtin::Zip) {
            if let TypedExprNode::Tuple(elts) = &argument.node {
                if elts.len() == 2 {
                    return Some((&elts[0], &elts[1]));
                }
            }
        }
    }
    None
}

/// Returns the inner `f` if `expr` is `curry(f)` i.e.
/// `Apply { argument: f, function: Builtin(Curry) }`.
fn as_curry(expr: &Expr) -> Option<&Expr> {
    if let TypedExprNode::Apply { argument, function } = &expr.node {
        if is_builtin(function, Builtin::Curry) {
            return Some(argument);
        }
    }
    None
}

/// Returns the inner `c` if `expr` is `const_(c)` i.e.
/// `Apply { argument: c, function: Builtin(Const) }`.
fn as_const(expr: &Expr) -> Option<&Expr> {
    if let TypedExprNode::Apply { argument, function } = &expr.node {
        if is_builtin(function, Builtin::Const) {
            return Some(argument);
        }
    }
    None
}

/// Returns `(left, right)` if `expr` is a two-element [`TypedExprNode::Compose`].
///
/// Used for inner sub-composes that are always binary (e.g. `.0 ≫ curry(f)`).
/// Top-level compose patterns use [`try_pairwise_in_compose`] instead.
fn as_compose(expr: &Expr) -> Option<(&Expr, &Expr)> {
    if let TypedExprNode::Compose(elts) = &expr.node {
        if let [left, right] = elts.as_slice() {
            return Some((left, right));
        }
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
    if let TypedExprNode::Compose(elts) = &expr.node {
        if let Some((last, prefix)) = elts.split_last() {
            if !prefix.is_empty() {
                return Some((prefix, last));
            }
        }
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

            // Compute the new type for g ▷ const
            // Original: g ▷ const has type codomain(f) → codomain(g)
            // New: should be domain(f) → codomain(g)
            let new_const_ty = match (&left.ty, &right.ty) {
                (Type::Fun(left_dom, _), Type::Fun(_, right_cod)) => {
                    Type::fun(left_dom.as_ref().clone(), right_cod.as_ref().clone())
                }
                _ => Type::Hole,
            };

            // Reconstruct g ▷ const with the new type
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
        {
            if is_builtin(function, Builtin::Const) {
                return true;
            }
        }
        // Zip where both arms are simplifying
        if is_simplifying_zip(expr) {
            return true;
        }
        // Compose starting with projection (original behavior)
        if let TypedExprNode::Compose(elts) = &expr.node {
            if let Some(first) = elts.first() {
                if is_simplifying(first) {
                    return true;
                }
            }
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
                (Type::Fun(dom, _), Type::Fun(_, cod)) => {
                    Type::fun(dom.as_ref().clone(), cod.as_ref().clone())
                }
                _ => Type::Hole,
            };
            let h_ty = match (&left.ty, &h.ty) {
                (Type::Fun(dom, _), Type::Fun(_, cod)) => {
                    Type::fun(dom.as_ref().clone(), cod.as_ref().clone())
                }
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
// Collection-union flatten rule
// ---------------------------------------------------------------------------

/// Recursively collect operands from nested `CollectionUnion` applications.
///
/// If `e` is `Apply(CollectionUnion, Tuple([a, b]))`, returns the flat
/// concatenation of `collect_union_operands(a)` and `collect_union_operands(b)`.
/// Otherwise returns `vec![e]`.
fn collect_union_operands(e: Expr) -> Vec<Expr> {
    let is_cu = matches!(&e.node, TypedExprNode::Apply { function, .. }
        if is_builtin(function, Builtin::CollectionUnion));
    if !is_cu {
        return vec![e];
    }
    let Expr {
        node,
        ty,
        user_annotation,
    } = e;
    let TypedExprNode::Apply { function, argument } = node else {
        unreachable!()
    };
    let Expr {
        node: arg_node,
        ty: arg_ty,
        user_annotation: arg_ua,
    } = *argument;
    match arg_node {
        TypedExprNode::Tuple(elts) => elts.into_iter().flat_map(collect_union_operands).collect(),
        other_arg_node => {
            // Non-tuple argument: reconstruct as-is.
            vec![Expr {
                node: TypedExprNode::Apply {
                    function,
                    argument: Box::new(Expr {
                        node: other_arg_node,
                        ty: arg_ty,
                        user_annotation: arg_ua,
                    }),
                },
                ty,
                user_annotation,
            }]
        }
    }
}

/// Flatten `Type::Union([…, Type::Union([…]), …])` to a single level.
fn flatten_union_variants(ty: Type) -> Type {
    match ty {
        Type::Union(variants) => {
            let mut flat = Vec::new();
            for v in variants {
                match flatten_union_variants(v) {
                    Type::Union(sub) => flat.extend(sub),
                    other => flat.push(other),
                }
            }
            Type::Union(flat)
        }
        other => other,
    }
}

/// Flatten union: `(a @ b) @ c  ⟹  CollectionUnion(a, b, c)`.
///
/// When a `CollectionUnion` application has a tuple argument where any element
/// is itself a `CollectionUnion`, collect all operands into a single flat tuple.
/// Also flattens the nested `Type::Union` in the expression's domain type.
fn try_flatten_collection_union(expr: &mut Expr) -> bool {
    let should_flatten = matches!(&expr.node,
        TypedExprNode::Apply { function, argument }
        if is_builtin(function, Builtin::CollectionUnion)
            && matches!(&argument.node, TypedExprNode::Tuple(elts)
                if elts.iter().any(|e| matches!(&e.node,
                    TypedExprNode::Apply { function: f, .. } if is_builtin(f, Builtin::CollectionUnion)))));
    if !should_flatten {
        return false;
    }

    let Expr {
        node,
        ty,
        user_annotation,
    } = take(expr);
    let TypedExprNode::Apply { function, argument } = node else {
        unreachable!()
    };
    let TypedExpr {
        node: TypedExprNode::Tuple(elts),
        ..
    } = *argument
    else {
        unreachable!()
    };

    let flat_elts: Vec<Expr> = elts.into_iter().flat_map(collect_union_operands).collect();
    let tuple_ty = Type::Tuple(flat_elts.iter().map(|e| e.ty.clone()).collect());
    let new_ty = match ty {
        Type::Fun(dom, cod) => Type::fun(flatten_union_variants(*dom), *cod),
        other => other,
    };

    // Update the builtin's function type to match the new N-ary argument type.
    let mut builtin_expr = *function;
    builtin_expr.ty = Type::fun(tuple_ty.clone(), new_ty.clone());

    *expr = Expr {
        node: TypedExprNode::Apply {
            function: Box::new(builtin_expr),
            argument: Box::new(Expr {
                node: TypedExprNode::Tuple(flat_elts),
                ty: tuple_ty,
                user_annotation: None,
            }),
        },
        ty: new_ty,
        user_annotation,
    };
    true
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
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
        Type::Fun(Box::new(a), Box::new(b))
    }

    fn typed_compose(elts: Vec<Expr>) -> Expr {
        let mut fun_tys = Vec::new();
        for e in &elts {
            if let Type::Fun(d, c) = &e.ty {
                fun_tys.push(((*d).clone(), (*c).clone()));
            } else {
                panic!("compose element not a function: {e:?}");
            }
        }
        let ty = Type::Fun(
            fun_tys.first().unwrap().0.clone(),
            fun_tys.last().unwrap().1.clone(),
        );
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

    /// Out-of-range index is left alone — let a later pass surface the real error.
    #[test]
    fn simplify_literal_tuple_projection_out_of_range_is_noop() {
        let lit1 = Expr::lit(Lit::Int(1)).with_ty(int_ty());
        let tup_ty = Type::Tuple(vec![int_ty()]);
        let tuple = Expr::tuple(vec![lit1]).with_ty(tup_ty.clone());
        let proj = proj_idx(5).with_ty(fun_ty(tup_ty, int_ty()));
        let expr = Expr::apply(tuple, proj).with_ty(int_ty());
        assert_eq!(simplify(expr.clone()), expr);
    }

    /// Non-tuple argument: `Apply(Var("xs"), Proj(.0))` is *not* a literal-tuple
    /// projection — the rule must leave it alone.
    #[test]
    fn simplify_literal_tuple_projection_non_tuple_argument_is_noop() {
        let xs_ty = fun_ty(Type::UIntRange(3), int_ty());
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

    // ── try_flatten_collection_union ──────────────────────────────────────────

    /// Build `CollectionUnion(tuple)` with the given elements and result type.
    ///
    /// This mirrors the shape the lowering pass produces:
    ///   `Apply { function: CollectionUnion, argument: Tuple([...]) }`.
    fn cu(elts: Vec<Expr>, result_ty: Type) -> Expr {
        let tuple_ty = Type::Tuple(elts.iter().map(|e| e.ty.clone()).collect());
        let builtin_ty = fun_ty(tuple_ty.clone(), result_ty.clone());
        let argument = Expr::tuple(elts).with_ty(tuple_ty);
        Expr::apply(
            argument,
            Expr::builtin(Builtin::CollectionUnion).with_ty(builtin_ty),
        )
        .with_ty(result_ty)
    }

    fn union_ty(variants: Vec<Type>) -> Type {
        Type::Union(variants)
    }

    /// A typed var standing in for a `Fun(domain, int)` leaf.
    fn fun_leaf(name: &str, domain: Type) -> Expr {
        var(name).with_ty(fun_ty(domain, int_ty()))
    }

    /// `(a @ b)` — binary union, right-associative nesting as the lowerer produces.
    fn binary_cu(a: Expr, b: Expr) -> Expr {
        let a_dom = match &a.ty {
            Type::Fun(d, _) => *d.clone(),
            other => panic!("binary_cu: expected Fun, got {other:?}"),
        };
        let b_dom = match &b.ty {
            Type::Fun(d, _) => *d.clone(),
            other => panic!("binary_cu: expected Fun, got {other:?}"),
        };
        let result_ty = fun_ty(union_ty(vec![a_dom, b_dom]), int_ty());
        cu(vec![a, b], result_ty)
    }

    /// `(a @ b) @ c` — left-nested: outer CU wraps inner CU and `c`.
    fn left_nested_cu(a: Expr, b: Expr, c: Expr) -> Expr {
        let ab = binary_cu(a, b);
        let c_dom = match &c.ty {
            Type::Fun(d, _) => *d.clone(),
            other => panic!("left_nested_cu: expected Fun, got {other:?}"),
        };
        let ab_dom = match &ab.ty {
            Type::Fun(d, _) => *d.clone(),
            other => panic!("left_nested_cu: expected Fun, got {other:?}"),
        };
        let result_ty = fun_ty(union_ty(vec![ab_dom, c_dom]), int_ty());
        cu(vec![ab, c], result_ty)
    }

    /// `a @ (b @ c)` — right-nested: outer CU wraps `a` and inner CU.
    fn right_nested_cu(a: Expr, b: Expr, c: Expr) -> Expr {
        let bc = binary_cu(b, c);
        let a_dom = match &a.ty {
            Type::Fun(d, _) => *d.clone(),
            other => panic!("right_nested_cu: expected Fun, got {other:?}"),
        };
        let bc_dom = match &bc.ty {
            Type::Fun(d, _) => *d.clone(),
            other => panic!("right_nested_cu: expected Fun, got {other:?}"),
        };
        let result_ty = fun_ty(union_ty(vec![a_dom, bc_dom]), int_ty());
        cu(vec![a, bc], result_ty)
    }

    /// Returns `true` if `expr` is a flat `CollectionUnion` with exactly `n` operands.
    fn is_flat_cu(expr: &Expr, n: usize) -> bool {
        let TypedExprNode::Apply { function, argument } = &expr.node else {
            return false;
        };
        if !is_builtin(function, Builtin::CollectionUnion) {
            return false;
        }
        let TypedExprNode::Tuple(elts) = &argument.node else {
            return false;
        };
        // No element may itself be a CollectionUnion application.
        elts.len() == n
            && !elts.iter().any(|e| {
                matches!(&e.node, TypedExprNode::Apply { function: f, .. }
                    if is_builtin(f, Builtin::CollectionUnion))
            })
    }

    /// A binary `a @ b` is already flat — `try_flatten_collection_union` must not
    /// change it.
    #[test]
    fn flatten_cu_binary_is_noop() {
        let a = fun_leaf("a", int_ty());
        let b = fun_leaf("b", int_ty());
        let expr = binary_cu(a, b);
        let before = expr.clone();
        let result = simplify(expr);
        assert_eq!(result, before);
    }

    /// `(a @ b) @ c`  ⟹  flat `CollectionUnion(a, b, c)` (left-nested).
    #[test]
    fn flatten_cu_left_nested_three_way() {
        let a = fun_leaf("a", int_ty());
        let b = fun_leaf("b", int_ty());
        let c = fun_leaf("c", int_ty());
        let expr = left_nested_cu(a, b, c);
        let result = simplify(expr);
        assert!(
            is_flat_cu(&result, 3),
            "expected flat 3-ary CU, got {result:?}"
        );
    }

    /// `a @ (b @ c)` ⟹  flat `CollectionUnion(a, b, c)` (right-nested).
    #[test]
    fn flatten_cu_right_nested_three_way() {
        let a = fun_leaf("a", int_ty());
        let b = fun_leaf("b", int_ty());
        let c = fun_leaf("c", int_ty());
        let expr = right_nested_cu(a, b, c);
        let result = simplify(expr);
        assert!(
            is_flat_cu(&result, 3),
            "expected flat 3-ary CU, got {result:?}"
        );
    }

    /// `((a @ b) @ c) @ d` — two levels of nesting flatten to 4 operands.
    #[test]
    fn flatten_cu_double_nested_four_way() {
        let a = fun_leaf("a", int_ty());
        let b = fun_leaf("b", int_ty());
        let c = fun_leaf("c", int_ty());
        let d = fun_leaf("d", int_ty());
        let abc = left_nested_cu(a, b, c);
        let d_dom = int_ty();
        let abc_dom = match &abc.ty {
            Type::Fun(dom, _) => *dom.clone(),
            other => panic!("{other:?}"),
        };
        let result_ty = fun_ty(union_ty(vec![abc_dom, d_dom]), int_ty());
        let expr = cu(vec![abc, d], result_ty);
        let result = simplify(expr);
        assert!(
            is_flat_cu(&result, 4),
            "expected flat 4-ary CU, got {result:?}"
        );
    }

    /// The flattened result type must be `Fun(Union(A,B,C), cod)` — not
    /// `Fun(Union(Union(A,B),C), cod)`.
    #[test]
    fn flatten_cu_result_type_is_flat_union() {
        let a = fun_leaf("a", int_ty());
        let b = fun_leaf("b", int_ty());
        let c = fun_leaf("c", int_ty());
        let expr = left_nested_cu(a, b, c);
        let result = simplify(expr);
        let Type::Fun(dom, _) = &result.ty else {
            panic!("expected Fun type, got {:?}", result.ty);
        };
        let Type::Union(variants) = dom.as_ref() else {
            panic!("expected Union domain, got {dom:?}");
        };
        // Must be flat: no variant should itself be a Union.
        for v in variants {
            assert!(
                !matches!(v, Type::Union(_)),
                "domain union must be flat, but found nested Union in {variants:?}"
            );
        }
        assert_eq!(variants.len(), 3);
    }
}
