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
//!
//! # Invariants on entry
//!
//! By the time this pass runs, [`crate::ccl::inline`] has already:
//! - Eliminated all `let y = x` aliases (α-renaming: Feed/Define targets follow).
//! - Applied the defer-returning lift, merging any `let y = (let x = Defer in …) in …`
//!   scope into `let y = Defer in …` with all Feed/Define targets consistently
//!   naming `y`.
//!
//! As a result, every `Feed`/`Define` node for a given defer handle uses exactly
//! the binding name of that handle — no alias tracking is required here.

use std::fmt;

use log::trace;

use crate::ccl::{
    BaseType, Branch, Builtin, Expr, RefinementKind, Type, TypedBinding, TypedExprNode,
    ccl_utils::{apply_primitive, count_free, is_free, typed_compose},
    infer::dedup_union_type,
    lambda_elim::substitute,
    simplify::simplify,
    symbolic::symbolic,
};

/// A let-binding lifted out of inline_defer's body recursion because it is
/// referenced by more than one extracted feed/define value.  These bindings
/// are wrapped around `construct_feed_result` at the top so the shared
/// expression compiles to a single operator instead of being substituted
/// (and duplicated) into every feed.
///
/// The motivating case is the Record-bodied mutation-loop encoding:
/// lowering binds the loop's body stream via `let __acc_stream_N = Loop {…} in …`,
/// and every per-feed `ExprStmt(Feed(d_k, __acc_stream_N ▷ Proj("tap_<k>_<d_k>")), …)`
/// references it.  Substituting the binding away into each projection
/// would compile N copies of the underlying `Recurse` op; preserving it
/// here keeps the single shared `Recurse` in the operator graph.
#[derive(Debug)]
struct PendingLet {
    binding: TypedBinding,
    bound_expr: Expr,
}

/// Convenience type alias for the inline_defer return shape.
type InlineDeferResult = (Vec<Expr>, Option<Expr>, Vec<PendingLet>);

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
///
/// By the time this runs, [`crate::ccl::inline`] has already merged any
/// defer-returning let scopes and α-renamed all `Feed`/`Define` targets, so
/// every feed/define node for a given handle already carries its binding name
/// and no alias tracking is needed.
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
                let (feed_values, define_value, pending_lets) = inline_defer(body, &binding.name)?;
                let name = &binding.name;
                let extracted = match (feed_values.len(), define_value) {
                    (0, None) => return Err(DeferError::NoFeedOrDefine(name.clone())),
                    (0, Some(define_value)) => define_value,
                    (_, None) => {
                        let feed_result = construct_feed_result(feed_values);
                        let feed_result_domain_ty = feed_result
                            .ty
                            .domain()
                            .unwrap_or(Type::Base(BaseType::Unit));
                        type_substitutions.push((
                            bound_expr.ty.domain().unwrap().clone(),
                            feed_result_domain_ty,
                        ));
                        feed_result
                    }
                    // inline_defer returns Err(FeedsAndDefinesMixed) when both feeds
                    // and a define are present, so Ok(...) with non-empty feeds and
                    // Some(define) cannot reach here.
                    _ => unreachable!(),
                };
                // Wrap the extracted result in any preserved let-bindings
                // that the body referenced.  `pending_lets` was pushed
                // bottom-up during recursion (inner lets first, outer
                // lets last), and each wrap iteration makes the current
                // plet the new outer.  So iterating *in order* preserves
                // the original lexical nesting: an inner pending_let's
                // bound_expr that references an outer pending_let's
                // binding stays correctly bound.
                let mut wrapped = extracted;
                for plet in pending_lets.into_iter() {
                    let wrapped_ty = wrapped.ty.clone();
                    wrapped = Expr::new(TypedExprNode::Let {
                        binding: plet.binding,
                        bound_expr: Box::new(plet.bound_expr),
                        body: Box::new(wrapped),
                    })
                    .with_ty(wrapped_ty);
                }
                **bound_expr = wrapped;
            }
            // body was already recursed above; only recurse into bound_expr here so
            // we process any defers nested inside the newly-substituted value.
            inline_defers(bound_expr, type_substitutions)?;
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
        TypedExprNode::Loop {
            init_args,
            source,
            loop_body,
            ..
        } => {
            for a in init_args {
                inline_defers(a, type_substitutions)?;
            }
            inline_defers(source, type_substitutions)?;
            inline_defers(loop_body, type_substitutions)?;
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

/// Merge feed values collected for a single defer into one expression.
///
/// A single feed is returned as-is. Multiple feeds are merged into a single
/// `Apply(Tuple([v0, v1, ...]), Builtin(CollectionUnion))` — the same shape
/// `operator_conversion` consumes for `a @ b`, so it lowers directly to a
/// `UnionOperator` without seeing a raw `BinOp`.
///
/// TODO(diffing): the i-th feed site implicitly becomes the i-th variant of
/// the resulting union, relying on `inline_defer`'s deterministic visit
/// order to assign tags. Program diffing / cross-program state sharing will
/// need an explicit tagged union keyed on a stable feed-site identity rather
/// than visit order.
fn construct_feed_result(feed_values: Vec<Expr>) -> Expr {
    debug_assert!(!feed_values.is_empty());
    // Const-wrap any scalar feed values that weren't inside a Compose context
    // (where the domain would already have been fixed).
    let feed_values: Vec<Expr> = feed_values
        .into_iter()
        .map(|v| {
            if v.ty.domain().is_none() {
                apply_primitive(
                    v.clone(),
                    Builtin::Const,
                    Type::fun(Type::Base(BaseType::Unit), v.ty.clone()),
                )
            } else {
                v
            }
        })
        .collect();
    if feed_values.len() == 1 {
        return feed_values.into_iter().next().unwrap();
    }
    // Compute the union result type: Fun(Union(dom0, dom1, ...), dedup(cod0, cod1, ...)).
    let mut domains = Vec::with_capacity(feed_values.len());
    let mut codomain_acc: Option<Type> = None;
    for v in &feed_values {
        let (dom, cod) = match &v.ty {
            Type::Fun(d, c) => (*d.clone(), *c.clone()),
            _ => unreachable!("feed value must have function type, got {:?}", v.ty),
        };
        domains.push(dom);
        codomain_acc = Some(match codomain_acc {
            None => cod,
            Some(prev) => dedup_union_type(prev, cod),
        });
    }
    let result_ty = Type::fun(Type::Union(domains), codomain_acc.unwrap());
    // Build Apply(Tuple([v0, v1, ...]), Builtin(CollectionUnion)) with correct types.
    // This is the post-lambda-elim form that operator_conversion expects.
    let tuple_tys: Vec<Type> = feed_values.iter().map(|v| v.ty.clone()).collect();
    let tuple = Expr::tuple(feed_values).with_ty(Type::Tuple(tuple_tys));
    apply_primitive(tuple, Builtin::CollectionUnion, result_ty)
}

/// Apply `type_substitutions` to every type slot in `expr`.
///
/// After [`inline_defers`] replaces a `Defer` with a feed result, the surrounding
/// expression still contains `HandleDomain(id)` placeholders in type annotations
/// that were inferred against the original `Defer` type. This pass rewrites those
/// occurrences to the concrete domain type recorded by [`inline_defers`].
fn substitute_types_in_expr(expr: &mut Expr, type_substitutions: &[(Type, Type)]) {
    substitute_types(&mut expr.ty, type_substitutions);

    // Binder-bearing variants carry types in fields that `walk_children_mut`
    // doesn't visit; rewrite those (and the Lambda's refinement predicate)
    // here before descending into the structural children.
    match &mut expr.node {
        TypedExprNode::Let { binding, .. } => {
            substitute_types(&mut binding.ty, type_substitutions);
        }
        TypedExprNode::Lambda {
            param, refinement, ..
        } => {
            substitute_types(&mut param.ty, type_substitutions);
            if let Some(refinement) = refinement {
                let RefinementKind::Predicate(pred) = &mut refinement.kind;
                substitute_types_in_expr(&mut pred.borrow_mut(), type_substitutions);
            }
        }
        _ => {}
    }

    expr.walk_children_mut(|e| substitute_types_in_expr(e, type_substitutions));
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
    // Refinement predicates are sub-expressions, not sub-types — recurse
    // into the predicate before falling through to the structural walk.
    if let Type::Refinement(_, refinement) = ty {
        let RefinementKind::Predicate(pred) = &mut refinement.kind;
        substitute_types_in_expr(&mut pred.borrow_mut(), type_substitutions);
    }
    ty.walk_children_mut(|child| substitute_types(child, type_substitutions));
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
/// Other node types (`Lambda`, `Join`, `BinOp`, etc.) are not yet supported and
/// will panic if encountered.
///
/// By the time this runs all aliases have been resolved by [`crate::ccl::inline`],
/// so exact name equality is sufficient for matching.
fn inline_defer(expr: &mut Expr, name_to_bind: &str) -> Result<InlineDeferResult, DeferError> {
    let ty = expr.ty.clone();
    let (replacement, feed_result, define_result, pending_lets): (
        Option<Expr>,
        Vec<Expr>,
        Option<Expr>,
        Vec<PendingLet>,
    ) = match &mut expr.node {
        TypedExprNode::Feed { name, value } if name == name_to_bind => (
            Some(Expr::var("__replaced").with_ty(ty)),
            vec![*value.clone()],
            None,
            Vec::new(),
        ),

        TypedExprNode::Define { name, value } if name == name_to_bind => (
            Some(Expr::var("__replaced").with_ty(ty)),
            Vec::new(),
            Some(*value.clone()),
            Vec::new(),
        ),

        TypedExprNode::ExprStmt { expr, body } => {
            let mut result_feeds = Vec::new();
            let mut result_pending = Vec::new();
            let (expr_feeds, expr_define, mut expr_pending) =
                inline_defer(expr.as_mut(), name_to_bind)?;
            let (body_feeds, body_define, mut body_pending) =
                inline_defer(body.as_mut(), name_to_bind)?;
            result_feeds.extend(expr_feeds);
            result_feeds.extend(body_feeds);
            result_pending.append(&mut expr_pending);
            result_pending.append(&mut body_pending);
            if expr_define.is_some() && body_define.is_some() {
                return Err(DeferError::MultipleDefinitions(name_to_bind.into()));
            }
            if (expr_define.is_some() || body_define.is_some()) && !result_feeds.is_empty() {
                return Err(DeferError::FeedsAndDefinesMixed(name_to_bind.into()));
            }
            (
                None,
                result_feeds,
                expr_define.or(body_define),
                result_pending,
            )
        }

        TypedExprNode::Compose(elts) => {
            let mut result = Vec::new();
            let mut result_pending = Vec::new();
            for i in 0..elts.len() {
                let (mut feed_value, define_value, mut pending) =
                    inline_defer(&mut elts[i], name_to_bind)?;
                if define_value.is_some() {
                    return Err(DeferError::NestedDefinition);
                }
                result_pending.append(&mut pending);
                // Scalar feed values have no domain; wrap them in `const` with the
                // expected domain taken from the compose-element's type here, where
                // that domain is known.  Function-typed values are used as-is.
                let expected_domain = elts[i].ty.domain();
                for v in feed_value.drain(..) {
                    let v = if v.ty.domain().is_none() {
                        let dom = expected_domain
                            .clone()
                            .unwrap_or(Type::Base(BaseType::Unit));
                        apply_primitive(v.clone(), Builtin::Const, Type::fun(dom, v.ty.clone()))
                    } else {
                        v
                    };
                    let mut feed_value_with_ctx = elts[0..i].to_vec();
                    feed_value_with_ctx.push(v);
                    let mut composed = typed_compose(feed_value_with_ctx);
                    // TODO we shouldn't have to do this once refinements are correctly
                    // propagated to all types.
                    composed.ty = Type::fun(ty.domain().unwrap(), composed.ty.codomain().unwrap());
                    result.push(composed);
                }
            }
            (None, result, None, result_pending)
        }

        TypedExprNode::Apply { function, argument } => {
            let (mut func_feeds, func_define, mut func_pending) =
                inline_defer(function.as_mut(), name_to_bind)?;
            let (mut arg_feeds, arg_define, mut arg_pending) =
                inline_defer(argument.as_mut(), name_to_bind)?;
            if func_define.is_some() && arg_define.is_some() {
                return Err(DeferError::MultipleDefinitions(name_to_bind.into()));
            }
            if (func_define.is_some() || arg_define.is_some())
                && !(func_feeds.is_empty() && arg_feeds.is_empty())
            {
                return Err(DeferError::FeedsAndDefinesMixed(name_to_bind.into()));
            }
            func_feeds.append(&mut arg_feeds);
            func_pending.append(&mut arg_pending);
            (None, func_feeds, func_define.or(arg_define), func_pending)
        }

        TypedExprNode::Tuple(elts) => {
            let mut result = Vec::new();
            let mut result_pending = Vec::new();
            for e in elts {
                let (mut feeds, define, mut pending) = inline_defer(e, name_to_bind)?;
                if define.is_some() {
                    return Err(DeferError::NestedDefinition);
                }
                result.append(&mut feeds);
                result_pending.append(&mut pending);
            }
            (None, result, None, result_pending)
        }

        // Recurse through a nested Let binding.  If the binding shadows name_to_bind
        // (an inner defer reuses the same name), stop searching in the body.
        //
        // When the binding is *referenced* by extracted feed/define values, we
        // defer the let to wrap the eventual feed-result instead of substituting
        // it away — this preserves sharing for bindings like the mutation-loop
        // acc-stream Join that are intentionally shared across multiple feeds.
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let (be_feeds, be_define, mut be_pending) =
                inline_defer(bound_expr.as_mut(), name_to_bind)?;

            let (body_feeds, body_define, mut body_pending) = if binding.name == name_to_bind {
                // The inner let shadows the name; don't search deeper.
                (vec![], None, vec![])
            } else {
                inline_defer(body.as_mut(), name_to_bind)?
            };

            // Count free references to binding.name across every extracted
            // value (feeds + define).  When there are ≥2 references the
            // substitute path would duplicate the bound expression, so we
            // preserve the let-binding as a `PendingLet` and let the
            // caller wrap the combined feed result with it once — sharing
            // a single op-graph subexpression across all references (used
            // by the multi-feed acc-stream Join binding).
            //
            // For 0 references the let is irrelevant.  For exactly 1
            // reference there is no duplication to avoid, and substituting
            // also keeps the bound expression's *type* information flowing
            // into the extracted value (the substituted value gets
            // `bound_expr.ty`, whereas a still-Hole `Var` in the body
            // wouldn't have that type filled in).
            let ref_count: usize = body_feeds
                .iter()
                .map(|v| count_free(&binding.name, v))
                .sum::<usize>()
                + body_define
                    .as_ref()
                    .map(|v| count_free(&binding.name, v))
                    .unwrap_or(0);

            let (body_feeds, body_define) = if ref_count >= 2 {
                // Hoist: leave the binding in place by pushing it onto
                // pending_lets so the caller can wrap it around the
                // feed-result at the defer site.
                body_pending.push(PendingLet {
                    binding: binding.clone(),
                    bound_expr: (**bound_expr).clone(),
                });
                (body_feeds, body_define)
            } else {
                let bound_val = &**bound_expr;
                let body_feeds: Vec<Expr> = body_feeds
                    .into_iter()
                    .map(|val| substitute(val, &binding.name, bound_val))
                    .collect();
                let body_define = body_define.map(|val| substitute(val, &binding.name, bound_val));
                (body_feeds, body_define)
            };

            // After the above, if name_to_bind is still free in any extracted
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
            be_pending.append(&mut body_pending);
            if be_define.is_some() && body_define.is_some() {
                return Err(DeferError::MultipleDefinitions(name_to_bind.into()));
            }
            if (be_define.is_some() || body_define.is_some()) && !result_feeds.is_empty() {
                return Err(DeferError::FeedsAndDefinesMixed(name_to_bind.into()));
            }
            (None, result_feeds, be_define.or(body_define), be_pending)
        }

        // Recurse into the value to collect any nested feed/define nodes.
        TypedExprNode::Feed { value, .. } | TypedExprNode::Define { value, .. } => {
            let (feeds, define, pending) = inline_defer(value.as_mut(), name_to_bind)?;
            (None, feeds, define, pending)
        }

        // Record: recurse into each field value, same policy as Tuple.
        TypedExprNode::Record(fields) => {
            let mut result = Vec::new();
            let mut result_pending = Vec::new();
            for (_, e) in fields.iter_mut() {
                let (feeds, define, mut pending) = inline_defer(e, name_to_bind)?;
                if define.is_some() {
                    return Err(DeferError::NestedDefinition);
                }
                result.extend(feeds);
                result_pending.append(&mut pending);
            }
            (None, result, None, result_pending)
        }

        TypedExprNode::Defer
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Lit(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::List(_) => (None, vec![], None, Vec::new()),

        // Loop (mutation loop) — by the time this pass runs, the
        // lowering in [`crate::ccl::lower::lower_mutation_loop`] has
        // already absorbed every `<<` feed from the loop body into the
        // Loop's body Record (one `tap_<k>_<defer>` field per feed) and
        // emitted an outer
        // `ExprStmt(Feed(defer_k, acc_stream ▷ Proj("tap_<k>_<defer>")), …)`
        // for each tap.  So a Loop's `loop_body` should never contain a
        // `Feed` for our `name_to_bind`; the recursion is purely a
        // safety walk, asserted via `debug_assert!` below.
        //
        // `init_args` sit outside the loop and *can* legitimately
        // contain feeds — the surrounding lowering threads pre-loop
        // defer-fed expressions in here.
        TypedExprNode::Loop {
            init_args,
            source,
            loop_body,
            ..
        } => {
            let (loop_feeds, loop_define, loop_pending) =
                inline_defer(loop_body.as_mut(), name_to_bind)?;
            if loop_define.is_some() {
                return Err(DeferError::NestedDefinition);
            }
            debug_assert!(
                loop_feeds.is_empty(),
                "Loop's loop_body should not contain feeds for `{name_to_bind}`; \
                 lower_mutation_loop is supposed to hoist them outside the loop"
            );
            debug_assert!(
                loop_pending.is_empty(),
                "Loop's loop_body should not contain pending lets for `{name_to_bind}`"
            );
            let (source_feeds, source_define, source_pending) =
                inline_defer(source.as_mut(), name_to_bind)?;
            if source_define.is_some() {
                return Err(DeferError::NestedDefinition);
            }
            debug_assert!(
                source_feeds.is_empty(),
                "Loop's source should not contain feeds for `{name_to_bind}`"
            );
            debug_assert!(
                source_pending.is_empty(),
                "Loop's source should not contain pending lets for `{name_to_bind}`"
            );
            let mut result = Vec::new();
            let mut result_pending = Vec::new();
            for init in init_args.iter_mut() {
                let (feeds, define, mut pending) = inline_defer(init, name_to_bind)?;
                if define.is_some() {
                    return Err(DeferError::NestedDefinition);
                }
                result.extend(feeds);
                result_pending.append(&mut pending);
            }
            (None, result, None, result_pending)
        }

        e => todo!("inline_defer: unhandled node type {:?}", e),
    };
    if let Some(replacement) = replacement {
        *expr = replacement;
    }
    Ok((feed_result, define_result, pending_lets))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{BaseType, Builtin, Lit, TypedExprNode, symbolic::symbolic};
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
        let (feeds, define, _) = inline_defer(&mut expr, "x").unwrap();
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
        let (feeds, define, _) = inline_defer(&mut expr, "x").unwrap();
        assert!(feeds.is_empty());
        assert!(define.is_none());
        assert_eq!(
            symbolic(&expr),
            original,
            "unrelated define must not change"
        );
    }

    /// Scalar feed value (no domain type) is returned as-is; const-wrapping is
    /// deferred to the Compose context or `construct_feed_result`.
    #[test]
    fn inline_defer_feed_scalar_wrapped_in_const() {
        let mut expr = Expr::feed("x".into(), lit(7));
        let (feeds, define, _) = inline_defer(&mut expr, "x").unwrap();
        assert!(define.is_none());
        assert_eq!(feeds.len(), 1);
        assert_eq!(
            symbolic(&feeds[0]),
            "7",
            "scalar must be returned as-is; const-wrapping happens downstream"
        );
        assert_eq!(symbolic(&expr), "__replaced");
    }

    /// Feed value that is already a function (has a domain type) is passed through as-is.
    #[test]
    fn inline_defer_feed_function_passed_through() {
        let fn_ty = Type::fun(int_ty(), int_ty());
        let mut expr = Expr::feed("x".into(), var("f").with_ty(fn_ty));
        let (feeds, define, _) = inline_defer(&mut expr, "x").unwrap();
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
        let (feeds, define, _) = inline_defer(&mut expr, "x").unwrap();
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
        let (feeds, define, _) = inline_defer(&mut expr, "x").unwrap();
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

    // -----------------------------------------------------------------------
    // construct_feed_result: shape and type assertions
    // -----------------------------------------------------------------------

    /// Helper: build an `Expr` with `Fun(dom, cod)` type, carrying a literal payload.
    fn fun_lit(dom: Type, cod: Type, n: i64) -> Expr {
        Expr::lit(Lit::Int(n)).with_ty(Type::fun(dom, cod))
    }

    /// A single feed value is returned as-is — no wrapping.
    #[test]
    fn construct_feed_result_single_passthrough() {
        let v = fun_lit(int_ty(), int_ty(), 1);
        let result = construct_feed_result(vec![v.clone()]);
        assert_eq!(result.ty, v.ty);
        assert_eq!(symbolic(&result), symbolic(&v));
    }

    /// Two feeds with the same codomain produce `Apply(Tuple([v0, v1]), Builtin(CollectionUnion))`
    /// and a `Fun(Union([dom0, dom1]), cod)` result type.
    #[test]
    fn construct_feed_result_two_feeds_shape_and_type() {
        let unit = Type::Base(BaseType::Unit);
        let v0 = fun_lit(unit.clone(), int_ty(), 1);
        let v1 = fun_lit(unit.clone(), int_ty(), 2);
        let result = construct_feed_result(vec![v0, v1]);

        // Top-level node must be Apply(Tuple([..]), Builtin(CollectionUnion)).
        // Expr::apply(argument, function) maps to Apply { argument, function }.
        let TypedExprNode::Apply { function, argument } = &result.node else {
            panic!("expected Apply, got {:?}", result.node);
        };
        assert!(
            matches!(
                &function.node,
                TypedExprNode::Builtin(Builtin::CollectionUnion)
            ),
            "function must be Builtin(CollectionUnion), got {:?}",
            function.node
        );
        assert!(
            matches!(&argument.node, TypedExprNode::Tuple(_)),
            "argument must be a Tuple, got {:?}",
            argument.node
        );

        // Result type: Fun(Union([Unit, Unit]), Int) — identical domains stay as two variants.
        let Type::Fun(dom, cod) = &result.ty else {
            panic!("expected Fun result type, got {:?}", result.ty);
        };
        assert!(
            matches!(dom.as_ref(), Type::Union(vs) if vs.len() == 2),
            "expected Union of two domains, got {:?}",
            dom
        );
        assert_eq!(cod.as_ref(), &int_ty(), "codomain must be Int");
    }

    /// Two feeds with *different* codomains produce a `Union` codomain via `dedup_union_type`.
    #[test]
    fn construct_feed_result_different_codomains_produce_union_codomain() {
        let unit = Type::Base(BaseType::Unit);
        let str_ty = Type::Base(BaseType::String);
        let v0 = fun_lit(unit.clone(), int_ty(), 1);
        let v1 = fun_lit(unit.clone(), str_ty.clone(), 2);
        let result = construct_feed_result(vec![v0, v1]);

        let Type::Fun(_, cod) = &result.ty else {
            panic!("expected Fun result type, got {:?}", result.ty);
        };
        assert!(
            matches!(cod.as_ref(), Type::Union(vs) if vs.len() == 2),
            "different codomains must produce a Union codomain, got {:?}",
            cod
        );
    }

    /// Three feeds produce a 3-element domain union (N-ary tuple path).
    #[test]
    fn construct_feed_result_three_feeds_domain_union() {
        let unit = Type::Base(BaseType::Unit);
        let feeds: Vec<Expr> = (1..=3)
            .map(|n| fun_lit(unit.clone(), int_ty(), n))
            .collect();
        let result = construct_feed_result(feeds);

        let Type::Fun(dom, _) = &result.ty else {
            panic!("expected Fun result type, got {:?}", result.ty);
        };
        assert!(
            matches!(dom.as_ref(), Type::Union(vs) if vs.len() == 3),
            "expected 3-element Union domain, got {:?}",
            dom
        );
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
