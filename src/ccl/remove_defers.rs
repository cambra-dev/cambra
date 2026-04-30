//! Elimination pass for [`TypedExprNode::Defer`], [`TypedExprNode::Feed`], and
//! [`TypedExprNode::Define`] — the output operators introduced by `x = defer()`,
//! `x << value`, and `x <<= value` in Python source.
//!
//! After type inference, a deferred output looks like:
//!
//! ```text
//! let x = Defer
//! in ExprStmt(Feed(x, v), x)   # x << v; x
//! ```
//!
//! This pass rewrites every such `Let`/`Defer` binding to replace `Defer` with the
//! actual value that was fed or defined, then drops the now-vacuous `ExprStmt` shells
//! via the simplification pass. After [`run`] returns, no `Defer`, `Feed`, `Define`,
//! or `ExprStmt` nodes remain in the tree.
//!
//! # Pipeline position
//!
//! Runs after [`crate::ccl::inline`] and before [`crate::ccl::join_plan`].

use std::fmt;

use log::trace;

use crate::ccl::{
    ccl_utils::{apply_primitive, typed_compose},
    lambda_elim::{is_free, substitute},
    simplify::simplify,
    symbolic::symbolic,
    BaseType, Branch, Expr, RefinementKind, Type, TypedExprNode,
};

/// Errors that can arise while eliminating `Defer`/`Feed`/`Define` nodes.
#[derive(Debug, PartialEq)]
pub enum DeferError {
    /// A deferred binding had no corresponding `Feed` or `Define` in its scope.
    NoFeedOrDefine(String),
    /// A deferred binding had more than one `Define` in its scope.
    MultipleDefinitions(String),
    /// Both `Feed` and `Define` were found for the same deferred binding.
    FeedsAndDefinesMixed(String),
    /// A `Define` appeared inside a context where it is not top-level
    NestedDefinition,
}

impl fmt::Display for DeferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DeferError::NoFeedOrDefine(name) => {
                write!(f, "deferred binding '{name}' has no feed or define")
            }
            DeferError::MultipleDefinitions(name) => {
                write!(f, "deferred binding '{name}' has multiple definitions")
            }
            DeferError::FeedsAndDefinesMixed(name) => {
                write!(f, "deferred binding '{name}' has both feeds and a define")
            }
            DeferError::NestedDefinition => {
                write!(f, "<<= must occur as a top-level statement")
            }
        }
    }
}

/// Eliminate all `Defer`/`Feed`/`Define` nodes from `expr`.
///
/// Runs three sequential sub-passes:
/// 1. [`inline_defers`] — replace each `let x = Defer` with the feed/define value.
/// 2. [`substitute_types_in_expr`] — propagate `HandleDomain` type mappings collected
///    during inlining (the feed case maps the old synthetic domain to the result domain).
/// 3. [`simplify`] — drop the `ExprStmt` sentinel shells left behind at feed/define sites.
pub fn run(mut expr: Expr) -> Result<Expr, DeferError> {
    let mut type_substitutions = Vec::new();
    inline_defers(&mut expr, &mut type_substitutions)?;
    substitute_types_in_expr(&mut expr, &type_substitutions);
    Ok(simplify(expr))
}

/// Walk `expr` top-down, replacing each `let x = Defer` binding with the value
/// that was fed or defined into `x`.
///
/// For each `Let { bound_expr: Defer, binding, body }`:
/// - Calls [`inline_defer`] to search `body` for the single `Feed(x, …)` or
///   `Define(x, …)` associated with `x`.
/// - **Define path**: replaces `Defer` with the define value directly.
/// - **Feed path**: wraps a scalar feed value in `value ▷ const` (since the defer
///   has a function type), records the `HandleDomain → result_domain` mapping in
///   `type_substitutions`, then replaces `Defer` with the result.
///
/// Recurses into both the (now-updated) `bound_expr` and `body` for nested defers.
fn inline_defers(
    expr: &mut Expr,
    type_substitutions: &mut Vec<(Type, Type)>,
) -> Result<(), DeferError> {
    match &mut expr.node {
        TypedExprNode::Let {
            bound_expr,
            body,
            binding,
        } => {
            // Bottom-up: recurse into body first so that any nested defers are
            // resolved before we search body for this let's feed/define value.
            // This ensures that extracted values reference concrete expressions
            // rather than still-deferred placeholders.
            inline_defers(body, type_substitutions)?;

            if bound_expr.node == TypedExprNode::Defer {
                trace!("Inlining defer {} in {}", binding.name, symbolic(body));
                let (feed_values, define_value) = inline_defer(body, &binding.name)?;
                let name = &binding.name;
                match (feed_values.len(), define_value) {
                    (0, None) => return Err(DeferError::NoFeedOrDefine(name.clone())),
                    (n, None) if n > 1 => {
                        todo!("multiple feeds for defer '{}' not yet supported", name)
                    }
                    (0, Some(define_value)) => {
                        **bound_expr = define_value;
                    }
                    (1, None) => {
                        let feed_result = construct_feed_result(feed_values);
                        let feed_result_domain_ty = feed_result
                            .ty
                            .domain()
                            .unwrap_or(Type::Base(BaseType::Unit));
                        type_substitutions.push((
                            bound_expr.ty.domain().unwrap().clone(),
                            feed_result_domain_ty,
                        ));
                        **bound_expr = feed_result;
                    }
                    _ => unreachable!("FeedsAndDefinesMixed is caught inside inline_defer"),
                }
            }
            inline_defers(bound_expr, type_substitutions)?;
            // Note: body was already processed above; don't recurse into it again.
        }
        TypedExprNode::Apply { function, argument } => {
            inline_defers(function, type_substitutions)?;
            inline_defers(argument, type_substitutions)?;
        }
        TypedExprNode::BinOp { left, right, .. } => {
            inline_defers(left, type_substitutions)?;
            inline_defers(right, type_substitutions)?;
        }
        TypedExprNode::UnaryOp(_, inner) => {
            inline_defers(inner, type_substitutions)?;
        }
        TypedExprNode::Lambda { body, .. } => {
            inline_defers(body, type_substitutions)?;
        }
        TypedExprNode::Aggregate { input, .. } => {
            inline_defers(input, type_substitutions)?;
        }
        TypedExprNode::Tuple(elts) | TypedExprNode::List(elts) | TypedExprNode::Compose(elts) => {
            for e in elts {
                inline_defers(e, type_substitutions)?;
            }
        }
        TypedExprNode::Record(fields) => {
            for (_, e) in fields {
                inline_defers(e, type_substitutions)?;
            }
        }
        TypedExprNode::Case { branches } => {
            for Branch { guard, body } in branches {
                inline_defers(guard, type_substitutions)?;
                inline_defers(body, type_substitutions)?;
            }
        }
        TypedExprNode::Join {
            loop_body,
            outer_body,
            ..
        } => {
            inline_defers(loop_body, type_substitutions)?;
            inline_defers(outer_body, type_substitutions)?;
        }
        TypedExprNode::Jump { args, .. } => {
            for a in args {
                inline_defers(a, type_substitutions)?;
            }
        }
        TypedExprNode::GroupBy { collection, key } => {
            inline_defers(collection, type_substitutions)?;
            inline_defers(key, type_substitutions)?;
        }
        TypedExprNode::ExprStmt { expr: inner, body } => {
            inline_defers(inner, type_substitutions)?;
            inline_defers(body, type_substitutions)?;
        }
        TypedExprNode::Feed { value, .. } | TypedExprNode::Define { value, .. } => {
            inline_defers(value, type_substitutions)?;
        }
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Defer => {}
    }
    Ok(())
}

/// Merge the feed values collected for a single defer into one expression.
///
/// Currently only a single feed per defer is supported; the caller guarantees
/// exactly one value. Multiple feeds would require unioning together the
/// individual feed values, which is future work.
fn construct_feed_result(mut feed_values: Vec<Expr>) -> Expr {
    debug_assert_eq!(feed_values.len(), 1);
    feed_values.remove(0)
}

/// Apply `type_substitutions` to every type slot in `expr`.
///
/// After [`inline_defers`] replaces a `Defer` with a feed result, the surrounding
/// expression still contains `HandleDomain(id)` placeholders in type annotations
/// that were inferred against the original `Defer` type. This pass rewrites those
/// occurrences to the concrete domain type recorded by [`inline_defers`].
fn substitute_types_in_expr(expr: &mut Expr, type_substitutions: &[(Type, Type)]) {
    substitute_types(&mut expr.ty, type_substitutions);
    match &mut expr.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            substitute_types(&mut binding.ty, type_substitutions);
            substitute_types_in_expr(bound_expr, type_substitutions);
            substitute_types_in_expr(body, type_substitutions);
        }
        TypedExprNode::Apply { function, argument } => {
            substitute_types_in_expr(function, type_substitutions);
            substitute_types_in_expr(argument, type_substitutions);
        }
        TypedExprNode::BinOp { left, right, .. } => {
            substitute_types_in_expr(left, type_substitutions);
            substitute_types_in_expr(right, type_substitutions);
        }
        TypedExprNode::UnaryOp(_, inner) => {
            substitute_types_in_expr(inner, type_substitutions);
        }
        TypedExprNode::Lambda {
            body,
            param,
            refinement,
        } => {
            substitute_types(&mut param.ty, type_substitutions);
            if let Some(refinement) = refinement {
                if let RefinementKind::Predicate(pred) = &mut refinement.kind {
                    substitute_types_in_expr(&mut pred.borrow_mut(), type_substitutions);
                }
            }
            substitute_types_in_expr(body, type_substitutions);
        }
        TypedExprNode::Aggregate { input, .. } => {
            substitute_types_in_expr(input, type_substitutions);
        }
        TypedExprNode::Tuple(elts) | TypedExprNode::List(elts) | TypedExprNode::Compose(elts) => {
            for e in elts {
                substitute_types_in_expr(e, type_substitutions);
            }
        }
        TypedExprNode::Record(fields) => {
            for (_, e) in fields {
                substitute_types_in_expr(e, type_substitutions);
            }
        }
        TypedExprNode::Case { branches } => {
            for Branch { guard, body } in branches {
                substitute_types_in_expr(guard, type_substitutions);
                substitute_types_in_expr(body, type_substitutions);
            }
        }
        TypedExprNode::Join {
            loop_body,
            outer_body,
            ..
        } => {
            substitute_types_in_expr(loop_body, type_substitutions);
            substitute_types_in_expr(outer_body, type_substitutions);
        }
        TypedExprNode::Jump { args, .. } => {
            for a in args {
                substitute_types_in_expr(a, type_substitutions);
            }
        }
        TypedExprNode::GroupBy { collection, key } => {
            substitute_types_in_expr(collection, type_substitutions);
            substitute_types_in_expr(key, type_substitutions);
        }
        TypedExprNode::ExprStmt { expr: inner, body } => {
            substitute_types_in_expr(inner, type_substitutions);
            substitute_types_in_expr(body, type_substitutions);
        }
        TypedExprNode::Feed { value, .. } | TypedExprNode::Define { value, .. } => {
            substitute_types_in_expr(value, type_substitutions);
        }
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Defer => {}
    }
}

/// Recursively replace types in `ty` according to `type_substitutions`.
///
/// Each entry `(from, to)` replaces an exact match of `from` at any position in the
/// type tree. Structural types (`Fun`, `Tuple`, `Record`) are walked recursively;
/// all other variants are left unchanged if they don't match any substitution.
fn substitute_types(ty: &mut Type, type_substitutions: &[(Type, Type)]) {
    for (from, to) in type_substitutions {
        if *ty == *from {
            *ty = to.clone();
            return;
        }
    }
    match ty {
        Type::Fun(arg, func) => {
            substitute_types(arg, type_substitutions);
            substitute_types(func, type_substitutions);
        }
        Type::Tuple(elts) => {
            for e in elts {
                substitute_types(e, type_substitutions);
            }
        }
        Type::Record(fields) => {
            for (_, ty) in fields {
                substitute_types(ty, type_substitutions);
            }
        }
        Type::Refinement(base, pred) => {
            substitute_types(base, type_substitutions);
            if let RefinementKind::Predicate(pred) = &mut pred.kind {
                substitute_types_in_expr(&mut pred.borrow_mut(), type_substitutions);
            }
        }
        _ => {}
    }
}

/// Search `expr` for all `Feed` and `Define` nodes that reference `name_to_bind`,
/// extract their values, and replace each site with a `__replaced` sentinel.
///
/// Returns `(feed_values, define_value)`:
/// - `feed_values`: one entry per `Feed(name_to_bind, v)` found. Scalar values are
///   wrapped in `v ▷ const` so the result is always a function type.
/// - `define_value`: the value from the single `Define(name_to_bind, v)` found, if any.
///
/// Exactly one of `feed_values.len() == 1` or `define_value.is_some()` must hold by
/// the time the caller (i.e. [`inline_defers`]) asserts — mixing both or providing
/// multiple defines is an error.
///
/// Recurses through `ExprStmt`, `Compose`, `Apply`, `Tuple`, and `Let` nodes.
/// `Let` bindings that re-introduce `name_to_bind` stop the search in their body
/// (shadowing semantics). `Feed` and `Define` nodes for *other* names are leaves
/// unless `name_to_bind` appears free in their value expression.
fn inline_defer(
    expr: &mut Expr,
    name_to_bind: &str,
) -> Result<(Vec<Expr>, Option<Expr>), DeferError> {
    let ty = expr.ty.clone();
    let (replacement, feed_result, define_result) = match &mut expr.node {
        TypedExprNode::Feed { name, value } if name == name_to_bind => {
            let result = if value.ty.domain().is_some() {
                *value.clone()
            } else {
                apply_primitive(
                    *value.clone(),
                    super::Builtin::Const,
                    Type::fun(Type::Base(BaseType::Unit), value.ty.clone()),
                )
            };
            (
                Some(Expr::var("__replaced").with_ty(ty)),
                vec![result],
                None,
            )
        }

        TypedExprNode::Define { name, value } if name == name_to_bind => (
            Some(Expr::var("__replaced").with_ty(ty)),
            Vec::new(),
            Some(*value.clone()),
        ),

        TypedExprNode::ExprStmt { expr, body } => {
            let mut result_feeds = Vec::new();
            let (expr_feeds, expr_define) = inline_defer(expr.as_mut(), name_to_bind)?;
            let (body_feeds, body_define) = inline_defer(body.as_mut(), name_to_bind)?;
            result_feeds.extend(expr_feeds);
            result_feeds.extend(body_feeds);
            if expr_define.is_some() && body_define.is_some() {
                return Err(DeferError::MultipleDefinitions(name_to_bind.into()));
            }
            if (expr_define.is_some() || body_define.is_some()) && !result_feeds.is_empty() {
                return Err(DeferError::FeedsAndDefinesMixed(name_to_bind.into()));
            }
            (None, result_feeds, expr_define.or(body_define))
        }

        TypedExprNode::Compose(elts) => {
            let mut result = Vec::new();
            for i in 0..elts.len() {
                let (mut feed_value, define_value) = inline_defer(&mut elts[i], name_to_bind)?;
                if define_value.is_some() {
                    return Err(DeferError::NestedDefinition);
                }
                for v in feed_value.drain(..) {
                    let mut feed_value_with_ctx = elts[0..i].to_vec();
                    feed_value_with_ctx.push(v);
                    let mut composed = typed_compose(feed_value_with_ctx);
                    // TODO we shouldn't have to do this once refinements are correctly
                    // propagated to all types.
                    composed.ty = Type::fun(ty.domain().unwrap(), composed.ty.codomain().unwrap());
                    result.push(composed);
                }
            }
            (None, result, None)
        }

        TypedExprNode::Apply { function, argument } => {
            let (mut func_feeds, func_define) = inline_defer(function.as_mut(), name_to_bind)?;
            let (mut arg_feeds, arg_define) = inline_defer(argument.as_mut(), name_to_bind)?;
            if func_define.is_some() && arg_define.is_some() {
                return Err(DeferError::MultipleDefinitions(name_to_bind.into()));
            }
            if (func_define.is_some() || arg_define.is_some())
                && !(func_feeds.is_empty() && arg_feeds.is_empty())
            {
                return Err(DeferError::FeedsAndDefinesMixed(name_to_bind.into()));
            }
            func_feeds.append(&mut arg_feeds);
            (None, func_feeds, func_define.or(arg_define))
        }

        TypedExprNode::Tuple(elts) => {
            let mut result = Vec::new();
            for e in elts {
                let (mut feeds, define) = inline_defer(e, name_to_bind)?;
                if define.is_some() {
                    return Err(DeferError::NestedDefinition);
                }
                result.append(&mut feeds);
            }
            (None, result, None)
        }

        // Recurse through a nested Let binding. If the binding shadows name_to_bind
        // (i.e. an inner defer reuses the same name), stop searching in the body.
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let (be_feeds, be_define) = inline_defer(bound_expr.as_mut(), name_to_bind)?;
            let (body_feeds, body_define) = if binding.name == name_to_bind {
                // The inner let shadows the name; don't search deeper.
                (vec![], None)
            } else {
                inline_defer(body.as_mut(), name_to_bind)?
            };

            // Values extracted from the body may reference binding.name as a free
            // variable, since they were written in its scope.  Substitute it out now
            // so the lifted value is self-contained.  `inline_defers` processes lets
            // bottom-up, so bound_expr is already a concrete value by the time we get
            // here.
            let bound_val = &**bound_expr;
            let body_feeds: Vec<Expr> = body_feeds
                .into_iter()
                .map(|val| substitute(val, &binding.name, bound_val))
                .collect();
            let body_define = body_define.map(|val| substitute(val, &binding.name, bound_val));

            // After substitution, if name_to_bind is still free in any extracted
            // value, the two defers are mutually recursive (x depends on y which
            // depends on x).  We detect this here so we fail with a clear message
            // rather than producing an invalid operator plan downstream.
            // TODO handle this properly once we have support for letrec
            let still_free = body_feeds.iter().any(|v| is_free(name_to_bind, v))
                || body_define
                    .as_ref()
                    .is_some_and(|v| is_free(name_to_bind, v));
            if still_free {
                todo!(
                    "mutually recursive defers ('{name_to_bind}' ↔ '{}') are not yet supported",
                    binding.name
                );
            }

            let mut result_feeds = be_feeds;
            result_feeds.extend(body_feeds);
            if be_define.is_some() && body_define.is_some() {
                return Err(DeferError::MultipleDefinitions(name_to_bind.into()));
            }
            if (be_define.is_some() || body_define.is_some()) && !result_feeds.is_empty() {
                return Err(DeferError::FeedsAndDefinesMixed(name_to_bind.into()));
            }
            (None, result_feeds, be_define.or(body_define))
        }

        // Recurse into the value to collect any nested feed/define nodes.
        TypedExprNode::Feed { value, .. } | TypedExprNode::Define { value, .. } => {
            let (feeds, define) = inline_defer(value.as_mut(), name_to_bind)?;
            (None, feeds, define)
        }

        TypedExprNode::Defer
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Lit(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::List(_) => (None, vec![], None),

        e => todo!("inline_defer: unhandled node type {:?}", e),
    };
    if let Some(replacement) = replacement {
        *expr = replacement;
    }
    Ok((feed_result, define_result))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{symbolic::symbolic, BaseType, Lit};
    use test_log::test;

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    fn int_ty() -> Type {
        Type::Base(BaseType::Int)
    }

    fn lit(n: i64) -> Expr {
        Expr::lit(Lit::Int(n)).with_ty(Type::Base(BaseType::Int))
    }

    fn var(s: &str) -> Expr {
        Expr::var(s)
    }

    // -----------------------------------------------------------------------
    // inline_defer: direct unit tests for the core search/replace logic
    // -----------------------------------------------------------------------

    /// Define node for the target name is extracted and the site replaced.
    #[test]
    fn inline_defer_define_extracts_value() {
        // ExprStmt(Define("x", 42), Var("x"))
        let mut expr = Expr::expr_stmt(Expr::define("x".into(), lit(42)), var("x"));
        let (feeds, define) = inline_defer(&mut expr, "x").unwrap();
        assert!(feeds.is_empty());
        assert_eq!(symbolic(define.as_ref().unwrap()), "42");
        // The Define site must be replaced with the sentinel.
        assert_eq!(
            symbolic(&expr),
            "__replaced; x",
            "define site should be replaced"
        );
    }

    /// Define node for a *different* name is left untouched.
    #[test]
    fn inline_defer_define_wrong_name_unchanged() {
        let mut expr = Expr::expr_stmt(Expr::define("y".into(), lit(42)), var("x"));
        let original = symbolic(&expr);
        let (feeds, define) = inline_defer(&mut expr, "x").unwrap();
        assert!(feeds.is_empty());
        assert!(define.is_none());
        assert_eq!(
            symbolic(&expr),
            original,
            "unrelated define must not change"
        );
    }

    /// Scalar feed value (no domain type) is wrapped in `const`.
    #[test]
    fn inline_defer_feed_scalar_wrapped_in_const() {
        let mut expr = Expr::feed("x".into(), lit(7));
        let (feeds, define) = inline_defer(&mut expr, "x").unwrap();
        assert!(define.is_none());
        assert_eq!(feeds.len(), 1);
        assert_eq!(
            symbolic(&feeds[0]),
            "7 ▷ const",
            "scalar must be lifted via const"
        );
        assert_eq!(symbolic(&expr), "__replaced");
    }

    /// Feed value that is already a function (has a domain type) is passed through as-is.
    #[test]
    fn inline_defer_feed_function_passed_through() {
        let fn_ty = Type::fun(int_ty(), int_ty());
        let mut expr = Expr::feed("x".into(), var("f").with_ty(fn_ty));
        let (feeds, define) = inline_defer(&mut expr, "x").unwrap();
        assert!(define.is_none());
        assert_eq!(feeds.len(), 1);
        assert_eq!(
            symbolic(&feeds[0]),
            "f",
            "function value must not be re-wrapped"
        );
    }

    /// Feed for a different name is not extracted.
    #[test]
    fn inline_defer_feed_wrong_name_unchanged() {
        let mut expr = Expr::expr_stmt(Expr::feed("y".into(), lit(1)), var("x"));
        let original = symbolic(&expr);
        let (feeds, define) = inline_defer(&mut expr, "x").unwrap();
        assert!(feeds.is_empty());
        assert!(define.is_none());
        assert_eq!(symbolic(&expr), original);
    }

    /// An inner Let that re-binds the target name shadows the outer defer; feeds
    /// inside the inner let body are not extracted for the outer name.
    #[test]
    fn inline_defer_let_shadowing_stops_search() {
        // let x = 0 in Feed("x", 1) — the inner let shadows the outer defer for "x".
        let inner_body = Expr::feed("x".into(), lit(1));
        let mut expr = Expr::let_bind("x", lit(0), inner_body);
        let (feeds, define) = inline_defer(&mut expr, "x").unwrap();
        assert!(
            feeds.is_empty(),
            "feed inside shadowing let must not be extracted"
        );
        assert!(define.is_none());
    }

    // -----------------------------------------------------------------------
    // Error cases
    // -----------------------------------------------------------------------

    /// Multiple definitions for the same defer name is an error.
    #[test]
    fn inline_defer_multiple_definitions_is_error() {
        let mut expr = Expr::expr_stmt(
            Expr::define("x".into(), lit(1)),
            Expr::expr_stmt(Expr::define("x".into(), lit(2)), var("x")),
        );
        let err = inline_defer(&mut expr, "x").unwrap_err();
        assert_eq!(err, DeferError::MultipleDefinitions("x".into()));
    }

    /// Mixing feeds and a define for the same defer name is an error.
    #[test]
    fn inline_defer_feeds_and_define_mixed_is_error() {
        let mut expr = Expr::expr_stmt(
            Expr::feed("x".into(), lit(1)),
            Expr::expr_stmt(Expr::define("x".into(), lit(2)), var("x")),
        );
        let err = inline_defer(&mut expr, "x").unwrap_err();
        assert_eq!(err, DeferError::FeedsAndDefinesMixed("x".into()));
    }

    // -----------------------------------------------------------------------
    // run(): scoping correctness for nested defers
    // -----------------------------------------------------------------------

    /// Two mutually-ordered defers: `x <<= y; y <<= 42`.
    ///
    /// The define value for `x` is `Var("y")`, which is only in scope inside
    /// the `let y = Defer` binding.  The pass must substitute `y → 42` before
    /// lifting the value out to `x`'s binding site.
    #[test]
    fn run_nested_define_scoping() {
        // Construct: let x = Defer in
        //              let y = Defer in
        //                ExprStmt(Define("x", y), ExprStmt(Define("y", 42), x))
        let body = Expr::expr_stmt(
            Expr::define("x".into(), var("y")),
            Expr::expr_stmt(Expr::define("y".into(), lit(42)), var("x")),
        );
        let inner = Expr::let_bind("y", Expr::new(TypedExprNode::Defer).with_ty(int_ty()), body);
        let expr = Expr::let_bind(
            "x",
            Expr::new(TypedExprNode::Defer).with_ty(int_ty()),
            inner,
        );

        let result = run(expr).expect("run should succeed");
        // After elimination and simplification, x should be bound to 42 (the
        // value of y, substituted in-place) and the result expression should
        // evaluate x.
        let s = symbolic(&result);
        assert!(
            s.contains("42"),
            "expected 42 to appear in result, got: {s}"
        );
        assert!(
            !s.contains("Defer") && !s.contains("defer"),
            "no Defer should remain: {s}"
        );
    }
}
