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
//! | Curry-compose | `curry(f ≫ g)` | `curry(f) ≫ map(g)` |
//! | Const-apply | `⟨f, const(g)⟩ ≫ apply` | `f ≫ g` |
//! | Product eta | `⟨f ≫ .0, f ≫ .1⟩` | `f` |
//! | Flatten compose | `Compose([…, Compose([…]), …])` | `Compose([…flat…])` |

use crate::ccl::lambda_elim::{compose, curry, id, zip_pair};
use crate::ccl::{Expr, Lit, ProjKey, TypedExpr, TypedExprNode};

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
    changed |= try_flatten_compose(expr);
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
/// expression (preserving `ty` and `user_annotation` only for multi-element
/// results).  Returns `true` if a rule fired.
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
        let mut e = Expr::compose(elts);
        e.ty = ty;
        e.user_annotation = user_annotation;
        e
    };
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
            vec![zip_pair(id(), g), *h]
        },
    )
}

/// Curry-compose: `curry(f ≫ g)  ⟹  curry(f) ≫ map(g)`
///
/// For n-ary inner composes, peels the last element: `curry([e0,…,en-1]) ⟹
/// curry([e0,…,en-2]) ≫ map(en-1)`.  Skips when the first or last element of
/// the inner compose is `id`, since compose-identity reduction
/// (`id ≫ g → g`) should simplify first.
fn try_curry_compose(expr: &mut Expr) -> bool {
    let matched = as_curry(expr).is_some_and(|inner| {
        if let TypedExprNode::Compose(elts) = &inner.node {
            elts.len() >= 2 && !is_id(elts.first().unwrap()) && !is_id(elts.last().unwrap())
        } else {
            false
        }
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
        let g = inner_elts.pop().unwrap();
        let f = if inner_elts.len() == 1 {
            inner_elts.pop().unwrap()
        } else {
            Expr::compose(inner_elts)
        };
        *expr = compose(curry(f), Expr::apply(g, Expr::var("map")));
        return true;
    }
    false
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
        *expr = f;
        return true;
    }
    false
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

    /// Compose identity (middle of n-ary): f ≫ id ≫ g  ⟹  f ≫ g
    #[test]
    fn simplify_compose_identity_middle() {
        let expr = Expr::compose(vec![var("f"), id(), var("g")]);
        let expected = Expr::compose(vec![var("f"), var("g")]);
        assert_eq!(simplify(expr), expected);
    }

    /// Product beta (first): ⟨f, g⟩ ≫ .0  ⟹  f
    #[test]
    fn simplify_product_beta_fst() {
        let expr = compose(zip_pair(var("f"), var("g")), proj_idx(0));
        assert_eq!(simplify(expr), var("f"));
    }

    /// Product beta (first) inside a longer compose: a ≫ ⟨f, g⟩ ≫ .0 ≫ b  ⟹  a ≫ f ≫ b
    #[test]
    fn simplify_product_beta_fst_pairwise() {
        let expr = Expr::compose(vec![
            var("a"),
            zip_pair(var("f"), var("g")),
            proj_idx(0),
            var("b"),
        ]);
        let expected = Expr::compose(vec![var("a"), var("f"), var("b")]);
        assert_eq!(simplify(expr), expected);
    }

    /// Product beta (second): ⟨f, g⟩ ≫ .1  ⟹  g
    #[test]
    fn simplify_product_beta_snd() {
        let expr = compose(zip_pair(var("f"), var("g")), proj_idx(1));
        assert_eq!(simplify(expr), var("g"));
    }

    /// Product beta (second) inside a longer compose: a ≫ ⟨f, g⟩ ≫ .1 ≫ b  ⟹  a ≫ g ≫ b
    #[test]
    fn simplify_product_beta_snd_pairwise() {
        let expr = Expr::compose(vec![
            var("a"),
            zip_pair(var("f"), var("g")),
            proj_idx(1),
            var("b"),
        ]);
        let expected = Expr::compose(vec![var("a"), var("g"), var("b")]);
        assert_eq!(simplify(expr), expected);
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

    /// Product eta with n-ary arms: ⟨f ≫ g ≫ .0, f ≫ g ≫ .1⟩  ⟹  f ≫ g
    #[test]
    fn simplify_product_eta_nary_arms() {
        let expr = zip_pair(
            Expr::compose(vec![var("f"), var("g"), proj_idx(0)]),
            Expr::compose(vec![var("f"), var("g"), proj_idx(1)]),
        );
        let expected = Expr::compose(vec![var("f"), var("g")]);
        assert_eq!(simplify(expr), expected);
    }

    /// Exponential beta: ⟨g, curry(h)⟩ ≫ apply  ⟹  ⟨id, g⟩ ≫ h  (flattened to n-ary Compose)
    #[test]
    fn simplify_exponential_beta() {
        let expr = compose(zip_pair(var("g"), curry(var("h"))), var("apply"));
        let expected = Expr::compose(vec![zip_pair(id(), var("g")), var("h")]);
        assert_eq!(simplify(expr), expected);
    }

    /// Exponential beta inside a longer compose: a ≫ ⟨g, curry(h)⟩ ≫ apply ≫ b
    #[test]
    fn simplify_exponential_beta_pairwise() {
        let expr = Expr::compose(vec![
            var("a"),
            zip_pair(var("g"), curry(var("h"))),
            var("apply"),
            var("b"),
        ]);
        let expected = Expr::compose(vec![var("a"), zip_pair(id(), var("g")), var("h"), var("b")]);
        assert_eq!(simplify(expr), expected);
    }

    /// Curry-compose: curry(f ≫ g)  ⟹  curry(f) ≫ map(g)  (flattened to n-ary Compose)
    #[test]
    fn simplify_curry_compose() {
        let expr = curry(compose(var("f"), var("g")));
        let expected = Expr::compose(vec![curry(var("f")), app(var("g"), var("map"))]);
        assert_eq!(simplify(expr), expected);
    }

    /// Curry-compose with n-ary inner: curry(f ≫ g ≫ h)  ⟹  curry(f) ≫ map(g) ≫ map(h)
    #[test]
    fn simplify_curry_compose_nary() {
        let expr = curry(Expr::compose(vec![var("f"), var("g"), var("h")]));
        let expected = Expr::compose(vec![
            curry(var("f")),
            app(var("g"), var("map")),
            app(var("h"), var("map")),
        ]);
        assert_eq!(simplify(expr), expected);
    }

    /// Const-apply: ⟨f, const(g)⟩ ≫ apply  ⟹  f ≫ g  (flattened to n-ary Compose)
    #[test]
    fn simplify_const_apply() {
        let expr = compose(zip_pair(var("f"), const_(var("g"))), var("apply"));
        let expected = Expr::compose(vec![var("f"), var("g")]);
        assert_eq!(simplify(expr), expected);
    }

    /// Const-apply inside a longer compose: a ≫ ⟨f, const(g)⟩ ≫ apply ≫ b  ⟹  a ≫ f ≫ g ≫ b
    #[test]
    fn simplify_const_apply_pairwise() {
        let expr = Expr::compose(vec![
            var("a"),
            zip_pair(var("f"), const_(var("g"))),
            var("apply"),
            var("b"),
        ]);
        let expected = Expr::compose(vec![var("a"), var("f"), var("g"), var("b")]);
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

    /// CCC universal inside a longer compose: a ≫ ⟨.1, .0 ≫ curry(f)⟩ ≫ apply ≫ b  ⟹  a ≫ f ≫ b
    #[test]
    fn simplify_ccc_universal_pairwise() {
        let expr = Expr::compose(vec![
            var("a"),
            zip_pair(proj_idx(1), compose(proj_idx(0), curry(var("f")))),
            var("apply"),
            var("b"),
        ]);
        let expected = Expr::compose(vec![var("a"), var("f"), var("b")]);
        assert_eq!(simplify(expr), expected);
    }

    /// Flatten: f ≫ g ≫ h (binary tree)  ⟹  Compose([f, g, h])
    #[test]
    fn simplify_flatten_compose() {
        // Binary tree: f ≫ (g ≫ h)
        let expr = compose(var("f"), compose(var("g"), var("h")));
        let expected = Expr::compose(vec![var("f"), var("g"), var("h")]);
        assert_eq!(simplify(expr), expected);
    }

    /// Flatten left-associative: (f ≫ g) ≫ h  ⟹  Compose([f, g, h])
    #[test]
    fn simplify_flatten_compose_left_assoc() {
        let expr = compose(compose(var("f"), var("g")), var("h"));
        let expected = Expr::compose(vec![var("f"), var("g"), var("h")]);
        assert_eq!(simplify(expr), expected);
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
