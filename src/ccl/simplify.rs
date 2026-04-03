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
//! | Product beta (fst) | `⟨f, g⟩ ≫ .0` | `f` |
//! | Product beta (snd) | `⟨f, g⟩ ≫ .1` | `g` |
//! | CCC universal | `⟨.1, .0 ≫ curry(f)⟩ ≫ apply` | `f` |
//! | Exponential beta | `⟨g, curry(h)⟩ ≫ apply` | `⟨id, g⟩ ≫ h` |
//! | Exponential eta | `curry(⟨.1, .0 ≫ f⟩ ≫ apply)` | `f` |
//! | Const-apply | `⟨f, const(g)⟩ ≫ apply` | `f ≫ g` |
//! | Product eta | `⟨f ≫ .0, f ≫ .1⟩` | `f` |
//! | Flatten compose | `Compose([…, Compose([…]), …])` | `Compose([…flat…])` |
//! | Zip beta | `⟨f0, f1⟩ ≫ ⟨.n ≫ g, .m ≫ h⟩` | `⟨f_n ≫ g, f_m ≫ h⟩` |

use crate::ccl::infer::debug_typecheck;
use crate::ccl::lambda_elim::{id, zip_pair};
use crate::ccl::{Expr, Lit, ProjKey, RefinementKind, Type, TypedExpr, TypedExprNode};

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
            if let RefinementKind::Predicate(pred) = &refinment.kind {
                changed = simplify_once(&mut pred.borrow_mut())
            }
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
    match &mut expr.node {
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
        TypedExprNode::GroupBy { collection, key } => {
            simplify_once(collection) | simplify_once(key)
        }
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_) => false,
    }
}

/// Temporarily take ownership of `expr`, leaving a cheap placeholder.
///
/// The caller **must** write a valid expression back to `*expr` before
/// returning; the placeholder is never externally observable.
fn take(expr: &mut Expr) -> Expr {
    std::mem::replace(expr, Expr::lit(Lit::Int(0)))
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
    changed |= check(try_product_beta_fst(expr), expr);
    changed |= check(try_product_beta_snd(expr), expr);
    changed |= check(try_ccc_universal(expr), expr);
    changed |= check(try_exponential_beta(expr), expr);
    changed |= check(try_exponential_eta(expr), expr);
    changed |= check(try_zip_beta(expr), expr);
    changed |= check(try_const_apply(expr), expr);
    changed |= check(try_product_eta(expr), expr);
    changed |= check(try_flatten_compose(expr), expr);
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
/// `Apply { argument: Tuple([f, g]), function: Var("zip") }`.
fn as_zip(expr: &Expr) -> Option<(&Expr, &Expr)> {
    if let TypedExprNode::Apply { argument, function } = &expr.node {
        if matches!(&function.node, TypedExprNode::Var(n) if n == "zip") {
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
/// `Apply { argument: f, function: Var("curry") }`.
fn as_curry(expr: &Expr) -> Option<&Expr> {
    if let TypedExprNode::Apply { argument, function } = &expr.node {
        if matches!(&function.node, TypedExprNode::Var(n) if n == "curry") {
            return Some(argument);
        }
    }
    None
}

/// Returns the inner `c` if `expr` is `const_(c)` i.e.
/// `Apply { argument: c, function: Var("const") }`.
fn as_const(expr: &Expr) -> Option<&Expr> {
    if let TypedExprNode::Apply { argument, function } = &expr.node {
        if matches!(&function.node, TypedExprNode::Var(n) if n == "const") {
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

/// Returns `true` if `expr` is `Var("id")`.
fn is_id(expr: &Expr) -> bool {
    matches!(&expr.node, TypedExprNode::Var(n) if n == "id")
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
            matches!(&right.node, TypedExprNode::Var(n) if n == "apply")
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
            matches!(&right.node, TypedExprNode::Var(n) if n == "apply")
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
            matches!(&right.node, TypedExprNode::Var(n) if n == "apply")
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
fn try_product_eta(expr: &mut Expr) -> bool {
    let matched = as_zip(expr).is_some_and(|(left, right)| {
        compose_split_last(left).is_some_and(|(lpfx, lp)| {
            is_proj_idx(lp, 0)
                && compose_split_last(right)
                    .is_some_and(|(rpfx, rp)| is_proj_idx(rp, 1) && lpfx == rpfx)
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
// Zip beta rule
// ---------------------------------------------------------------------------

/// Zip beta: `⟨f0, f1⟩ ≫ ⟨.n ≫ g, .m ≫ i⟩  ⟹  ⟨f_n ≫ g, f_m ≫ i⟩`
///
/// Each arm of the right zip must start with a projection (`n, m ∈ {0,1}`);
/// each arm routes to whichever component of the left zip it selects, then
/// applies its optional suffix.  Bare projections (no suffix)
/// leave the component unchanged; compose identity subsequently reduces any
/// `id ≫ …` that appears.
///
/// Covers all combinations of arm order and suffix presence:
/// - `⟨h, f⟩ ≫ ⟨.0 ≫ g, .1⟩  ⟹  ⟨h ≫ g, f⟩`   (n=0, m=1, bare .1)
/// - `⟨h, f⟩ ≫ ⟨.1, .0 ≫ g⟩  ⟹  ⟨f, h ≫ g⟩`   (n=1, m=0, bare .1)
/// - `⟨h, f⟩ ≫ ⟨.0 ≫ g, .1 ≫ i⟩  ⟹  ⟨h ≫ g, f ≫ i⟩`  (both suffixed)
///
/// Operates pairwise in an n-ary compose; trailing elements are preserved.
fn try_zip_beta(expr: &mut Expr) -> bool {
    /// Returns the leading projection index of a zip arm.
    ///
    /// A zip arm may be a bare `Proj(Index(n))` or a compose whose first element
    /// is `Proj(Index(n))`.  Returns `Some(n)` in both cases, `None` otherwise.
    fn arm_leading_proj(expr: &Expr) -> Option<usize> {
        match &expr.node {
            TypedExprNode::Proj(ProjKey::Index(n)) => Some(*n),
            TypedExprNode::Compose(elts) => {
                if let Some(TypedExprNode::Proj(ProjKey::Index(n))) = elts.first().map(|e| &e.node)
                {
                    Some(*n)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Apply a zip arm to a base component.
    ///
    /// Given `base` (a left-zip component `f_n`) and an `arm` of the form `.n`
    /// or `.n ≫ g ≫ …`, replaces the leading projection in `arm` with `base`,
    /// yielding `base ≫ g ≫ …`.  Returns `base` unchanged when `arm` is a bare
    /// projection (equivalent to `base ≫ id`, reduced by compose identity).
    ///
    /// The result type is `Fun(domain_of_base, codomain_of_arm)` when both are
    /// concrete, falling back to [`Type::Hole`] otherwise.
    fn apply_arm_suffix(base: Expr, arm: Expr) -> Expr {
        // Result type: domain from base, codomain from arm (the arm carries the
        // full type A→C where A is the tuple domain and C is the output type;
        // substituting base for the leading proj gives domain(base)→C).
        let result_ty = match (&base.ty, &arm.ty) {
            (Type::Fun(dom, _), Type::Fun(_, cod)) => Type::fun(*dom.clone(), *cod.clone()),
            _ => Type::Hole,
        };
        match arm.node {
            TypedExprNode::Proj(_) => base,
            TypedExprNode::Compose(mut elts) => {
                elts[0] = base; // replace leading proj with base component
                let result = if elts.len() == 1 {
                    elts.pop().unwrap()
                } else {
                    Expr::compose(elts)
                };
                result.with_ty(result_ty)
            }
            _ => unreachable!(),
        }
    }

    try_pairwise_in_compose(
        expr,
        |left, right| {
            as_zip(left).is_some()
                && as_zip(right).is_some_and(|(a, b)| {
                    let n1 = arm_leading_proj(a);
                    let n2 = arm_leading_proj(b);
                    n1.is_some() && n2.is_some()
                })
        },
        |left, right| {
            // Peek at projection indices before consuming `right`
            let (n1, n2) = {
                let TypedExprNode::Apply { argument, .. } = &right.node else {
                    unreachable!()
                };
                let TypedExprNode::Tuple(elts) = &argument.node else {
                    unreachable!()
                };
                (
                    arm_leading_proj(&elts[0]).unwrap(),
                    arm_leading_proj(&elts[1]).unwrap(),
                )
            };
            // Extract (f0, f1) from ⟨f0, f1⟩
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
            let f1 = elts.swap_remove(1);
            let f0 = elts.pop().unwrap();
            // Extract (a, b) from ⟨a, b⟩
            let TypedExpr {
                node: TypedExprNode::Apply { argument, .. },
                ..
            } = right
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
            let b = elts.swap_remove(1);
            let a = elts.pop().unwrap();
            // Route each arm to the component it selects; clone when both arms
            // pick the same component (n1 == n2).
            let base_a = if n1 == 0 { f0.clone() } else { f1.clone() };
            let base_b = if n2 == 0 { f0 } else { f1 };
            let new_f = apply_arm_suffix(base_a, a);
            let new_g = apply_arm_suffix(base_b, b);
            vec![zip_pair(new_f, new_g)]
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
            matches!(&ap.node, TypedExprNode::Var(n) if n == "apply")
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
    use crate::ccl::lambda_elim::{curry, zip_pair};
    use crate::ccl::{BaseType, Expr};

    fn var(s: &str) -> Expr {
        Expr::var(s)
    }

    fn id() -> Expr {
        Expr::var("id")
    }

    fn proj_idx(n: usize) -> Expr {
        Expr::proj_index(n)
    }

    fn typed_const(c: Expr, param_ty: Type) -> Expr {
        let result_ty = fun_ty(param_ty.clone(), c.ty.clone());
        let const_var_ty = fun_ty(c.ty.clone(), result_ty.clone());
        Expr::apply(c, var("const").with_ty(const_var_ty)).with_ty(result_ty)
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
        let apply = var("apply").with_ty(apply_ty);

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
        let apply = var("apply").with_ty(apply_ty);

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
        let apply = var("apply").with_ty(apply_ty);

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
        let apply = var("apply").with_ty(apply_ty);

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
        let apply = var("apply").with_ty(fun_ty(
            Type::Tuple(vec![b_ty.clone(), bc_ty.clone()]),
            c_ty.clone(),
        ));
        let inner_compose = typed_compose2(zip, apply);

        let curry_var = var("curry").with_ty(fun_ty(inner_compose.ty.clone(), f_ty.clone()));
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
        let curry_var = var("curry").with_ty(fun_ty(f_ty.clone(), curry_f_ty.clone()));
        let curry_f = Expr::apply(f.clone(), curry_var).with_ty(curry_f_ty.clone());

        let ab_tup_ty = Type::Tuple(vec![a_ty.clone(), b_ty.clone()]);
        let p1 = proj_idx(1).with_ty(fun_ty(ab_tup_ty.clone(), b_ty.clone()));
        let p0 = proj_idx(0).with_ty(fun_ty(ab_tup_ty.clone(), a_ty.clone()));

        let p0_curry_f = typed_compose2(p0, curry_f);
        let zip = zip_pair(p1, p0_curry_f);
        let apply = var("apply").with_ty(fun_ty(
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
        let curry_var = var("curry").with_ty(fun_ty(f_ty.clone(), curry_f_ty.clone()));
        let curry_f = Expr::apply(f.clone(), curry_var).with_ty(curry_f_ty.clone());

        let ab_tup_ty = Type::Tuple(vec![a_ty.clone(), b_ty.clone()]);
        let p1 = proj_idx(1).with_ty(fun_ty(ab_tup_ty.clone(), b_ty.clone()));
        let p0 = proj_idx(0).with_ty(fun_ty(ab_tup_ty.clone(), a_ty.clone()));

        let p0_curry_f = typed_compose2(p0, curry_f);
        let zip = zip_pair(p1, p0_curry_f);
        let apply = var("apply").with_ty(fun_ty(
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
}
