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
//! | Rule | Pattern | Reduction |
//! |------|---------|-----------|
//! | Compose identity | `id ≫ f` / `f ≫ id` | `f` |
//! | Product beta (fst) | `⟨f, g⟩ ≫ .0` | `f` |
//! | Product beta (snd) | `⟨f, g⟩ ≫ .1` | `g` |
//! | CCC universal | `⟨.1, .0 ≫ curry(f)⟩ ≫ apply` | `f` |
//! | Exponential beta | `⟨g, curry(h)⟩ ≫ apply` | `⟨id, g⟩ ≫ h` |
//! | Exponential eta | `curry(⟨.1, f⟩ ≫ apply)` | `f` |
//! | Curry-compose | `curry(f ≫ g)` | `curry(f) ≫ map(g)` |
//! | Const-apply | `⟨f, const(g)⟩ ≫ apply` | `f ≫ g` |
//! | Product eta | `⟨f ≫ .0, f ≫ .1⟩` | `f` |

use crate::ccl::lambda_elim::{compose, curry, id, zip_pair};
use crate::ccl::{BinOpKind, Expr, Lit, ProjKey, TypedExpr, TypedExprNode};

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
    let changed = recurse_simplify(expr);
    changed | apply_simplification_rules(expr)
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
        TypedExprNode::Tuple(elts) | TypedExprNode::List(elts) => {
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
/// - Exponential eta before curry-compose (curry-compose splits the pattern
///   exponential eta needs).
///
/// Returns `true` if any rule fired.
fn apply_simplification_rules(expr: &mut Expr) -> bool {
    let mut changed = false;
    changed |= try_compose_identity(expr);
    changed |= try_product_beta_fst(expr);
    changed |= try_product_beta_snd(expr);
    changed |= try_ccc_universal(expr);
    changed |= try_exponential_beta(expr);
    changed |= try_exponential_eta(expr);
    changed |= try_curry_compose(expr);
    changed |= try_const_apply(expr);
    changed |= try_product_eta(expr);
    changed
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

/// Returns `(left, right)` if `expr` is `compose(left, right)`.
fn as_compose(expr: &Expr) -> Option<(&Expr, &Expr)> {
    if let TypedExprNode::BinOp {
        left,
        op: BinOpKind::Compose,
        right,
    } = &expr.node
    {
        return Some((left, right));
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

// ---------------------------------------------------------------------------
// Individual simplification rules
// ---------------------------------------------------------------------------

/// Compose identity: `id ≫ f  ⟹  f` and `f ≫ id  ⟹  f`
fn try_compose_identity(expr: &mut Expr) -> bool {
    let side = match as_compose(expr) {
        Some((left, _)) if is_id(left) => Some(true),
        Some((_, right)) if is_id(right) => Some(false),
        _ => None,
    };
    if let Some(take_right) = side {
        let TypedExpr {
            node: TypedExprNode::BinOp { left, right, .. },
            ..
        } = take(expr)
        else {
            unreachable!()
        };
        *expr = if take_right { *right } else { *left };
        return true;
    }
    false
}

/// Product beta (first): `⟨f, g⟩ ≫ .0  ⟹  f`
fn try_product_beta_fst(expr: &mut Expr) -> bool {
    let matched = matches!(as_compose(expr), Some((left, right))
        if is_proj_idx(right, 0) && as_zip(left).is_some());
    if matched {
        let TypedExpr {
            node: TypedExprNode::BinOp { left, .. },
            ..
        } = take(expr)
        else {
            unreachable!()
        };
        let TypedExpr {
            node: TypedExprNode::Apply { argument, .. },
            ..
        } = *left
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
        *expr = elts.swap_remove(0);
        return true;
    }
    false
}

/// Product beta (second): `⟨f, g⟩ ≫ .1  ⟹  g`
fn try_product_beta_snd(expr: &mut Expr) -> bool {
    let matched = matches!(as_compose(expr), Some((left, right))
        if is_proj_idx(right, 1) && as_zip(left).is_some());
    if matched {
        let TypedExpr {
            node: TypedExprNode::BinOp { left, .. },
            ..
        } = take(expr)
        else {
            unreachable!()
        };
        let TypedExpr {
            node: TypedExprNode::Apply { argument, .. },
            ..
        } = *left
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
        *expr = elts.swap_remove(1);
        return true;
    }
    false
}

/// CCC universal property: `⟨.1, .0 ≫ curry(f)⟩ ≫ apply  ⟹  f`
fn try_ccc_universal(expr: &mut Expr) -> bool {
    let matched = as_compose(expr).is_some_and(|(left, right)| {
        matches!(&right.node, TypedExprNode::Var(n) if n == "apply")
            && as_zip(left).is_some_and(|(l, r)| {
                is_proj_idx(l, 1)
                    && as_compose(r)
                        .is_some_and(|(cl, cr)| is_proj_idx(cl, 0) && as_curry(cr).is_some())
            })
    });
    if matched {
        // Path: expr.left.argument.elts[1].right.argument
        let TypedExpr {
            node: TypedExprNode::BinOp { left, .. },
            ..
        } = take(expr)
        else {
            unreachable!()
        };
        let TypedExpr {
            node: TypedExprNode::Apply { argument, .. },
            ..
        } = *left
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
            node: TypedExprNode::BinOp { right, .. },
            ..
        } = r
        else {
            unreachable!()
        };
        let TypedExpr {
            node: TypedExprNode::Apply { argument: f, .. },
            ..
        } = *right
        else {
            unreachable!()
        };
        *expr = *f;
        return true;
    }
    false
}

/// Exponential beta: `⟨g, curry(h)⟩ ≫ apply  ⟹  ⟨id, g⟩ ≫ h`
fn try_exponential_beta(expr: &mut Expr) -> bool {
    let matched = as_compose(expr).is_some_and(|(left, right)| {
        matches!(&right.node, TypedExprNode::Var(n) if n == "apply")
            && as_zip(left).is_some_and(|(_, r)| as_curry(r).is_some())
    });
    if matched {
        let TypedExpr {
            node: TypedExprNode::BinOp { left, .. },
            ..
        } = take(expr)
        else {
            unreachable!()
        };
        let TypedExpr {
            node: TypedExprNode::Apply { argument, .. },
            ..
        } = *left
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
        *expr = compose(zip_pair(id(), g), *h);
        return true;
    }
    false
}

/// Curry-compose: `curry(f ≫ g)  ⟹  curry(f) ≫ map(g)`
///
/// Skips when either side of the inner compose is `id`, since
/// compose-identity reduction (`id ≫ g → g`) should simplify first.
fn try_curry_compose(expr: &mut Expr) -> bool {
    let matched = as_curry(expr)
        .is_some_and(|inner| as_compose(inner).is_some_and(|(f, g)| !is_id(f) && !is_id(g)));
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
            node: TypedExprNode::BinOp {
                left: f, right: g, ..
            },
            ..
        } = *inner
        else {
            unreachable!()
        };
        *expr = compose(curry(*f), Expr::apply(*g, Expr::var("map")));
        return true;
    }
    false
}

/// Const-apply: `⟨f, const(g)⟩ ≫ apply  ⟹  f ≫ g`
fn try_const_apply(expr: &mut Expr) -> bool {
    let matched = as_compose(expr).is_some_and(|(left, right)| {
        matches!(&right.node, TypedExprNode::Var(n) if n == "apply")
            && as_zip(left).is_some_and(|(_, r)| as_const(r).is_some())
    });
    if matched {
        let TypedExpr {
            node: TypedExprNode::BinOp { left, .. },
            ..
        } = take(expr)
        else {
            unreachable!()
        };
        let TypedExpr {
            node: TypedExprNode::Apply { argument, .. },
            ..
        } = *left
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
        *expr = compose(f, *g);
        return true;
    }
    false
}

/// Product eta: `⟨f ≫ .0, f ≫ .1⟩  ⟹  f`
///
/// Collapses a zip that merely destructs and re-pairs the same source morphism.
/// Analogous to the function-type eta rule `λ x → f x  ⟹  f`.
fn try_product_eta(expr: &mut Expr) -> bool {
    let matched = as_zip(expr).is_some_and(|(left, right)| {
        as_compose(left).is_some_and(|(lf, lp)| {
            is_proj_idx(lp, 0)
                && as_compose(right).is_some_and(|(rf, rp)| is_proj_idx(rp, 1) && lf == rf)
        })
    });
    if matched {
        // Path: expr.argument.elts[0].left
        let TypedExpr {
            node: TypedExprNode::Apply { argument, .. },
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
            node: TypedExprNode::BinOp { left: f, .. },
            ..
        } = left_compose
        else {
            unreachable!()
        };
        *expr = *f;
        return true;
    }
    false
}

/// Exponential eta: `curry(⟨.1, .0 ≫ f⟩ ≫ apply)  ⟹  f`
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
        // Path: expr.argument.left.argument.elts[1].right
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
            node: TypedExprNode::BinOp { left, .. },
            ..
        } = *inner
        else {
            unreachable!()
        };
        let TypedExpr {
            node: TypedExprNode::Apply { argument, .. },
            ..
        } = *left
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
            node: TypedExprNode::BinOp { right, .. },
            ..
        } = elts.swap_remove(1)
        else {
            unreachable!()
        };
        *expr = *right;
        return true;
    }
    false
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::lambda_elim::{compose, const_, curry, id, proj_idx, zip_pair};
    use crate::ccl::Expr;

    fn var(s: &str) -> Expr {
        Expr::var(s)
    }

    fn app(arg: Expr, func: Expr) -> Expr {
        Expr::apply(arg, func)
    }

    /// Compose identity (left): id ≫ f  ⟹  f
    #[test]
    fn simplify_compose_identity_left() {
        let expr = compose(id(), var("f"));
        assert_eq!(simplify(expr), var("f"));
    }

    /// Compose identity (right): f ≫ id  ⟹  f
    #[test]
    fn simplify_compose_identity_right() {
        let expr = compose(var("f"), id());
        assert_eq!(simplify(expr), var("f"));
    }

    /// Product beta (first): ⟨f, g⟩ ≫ .0  ⟹  f
    #[test]
    fn simplify_product_beta_fst() {
        let expr = compose(zip_pair(var("f"), var("g")), proj_idx(0));
        assert_eq!(simplify(expr), var("f"));
    }

    /// Product beta (second): ⟨f, g⟩ ≫ .1  ⟹  g
    #[test]
    fn simplify_product_beta_snd() {
        let expr = compose(zip_pair(var("f"), var("g")), proj_idx(1));
        assert_eq!(simplify(expr), var("g"));
    }

    /// Product eta: ⟨f ≫ .0, f ≫ .1⟩  ⟹  f
    #[test]
    fn simplify_product_eta() {
        let expr = zip_pair(
            compose(var("f"), proj_idx(0)),
            compose(var("f"), proj_idx(1)),
        );
        assert_eq!(simplify(expr), var("f"));
    }

    /// Exponential beta: ⟨g, curry(h)⟩ ≫ apply  ⟹  ⟨id, g⟩ ≫ h
    #[test]
    fn simplify_exponential_beta() {
        let expr = compose(zip_pair(var("g"), curry(var("h"))), var("apply"));
        let expected = compose(zip_pair(id(), var("g")), var("h"));
        assert_eq!(simplify(expr), expected);
    }

    /// Curry-compose: curry(f ≫ g)  ⟹  curry(f) ≫ map(g)
    #[test]
    fn simplify_curry_compose() {
        let expr = curry(compose(var("f"), var("g")));
        let expected = compose(curry(var("f")), app(var("g"), var("map")));
        assert_eq!(simplify(expr), expected);
    }

    /// Const-apply: ⟨f, const(g)⟩ ≫ apply  ⟹  f ≫ g
    #[test]
    fn simplify_const_apply() {
        let expr = compose(zip_pair(var("f"), const_(var("g"))), var("apply"));
        let expected = compose(var("f"), var("g"));
        assert_eq!(simplify(expr), expected);
    }

    /// Exponential eta: curry(⟨.1, .0 ≫ f⟩ ≫ apply)  ⟹  f
    #[test]
    fn simplify_exponential_eta() {
        let expr = curry(compose(
            zip_pair(proj_idx(1), compose(proj_idx(0), var("f"))),
            var("apply"),
        ));
        assert_eq!(simplify(expr), var("f"));
    }

    /// CCC universal: `⟨.1, .0 ≫ curry(f)⟩ ≫ apply  ⟹  f`
    #[test]
    fn simplify_ccc_universal() {
        let expr = compose(
            zip_pair(proj_idx(1), compose(proj_idx(0), curry(var("f")))),
            var("apply"),
        );
        assert_eq!(simplify(expr), var("f"));
    }

    /// Idempotency: simplify(simplify(e)) == simplify(e)
    #[test]
    fn simplify_idempotent() {
        let expr = compose(id(), compose(var("f"), var("g")));
        let once = simplify(expr);
        let twice = simplify(once.clone());
        assert_eq!(once, twice);
    }
}
