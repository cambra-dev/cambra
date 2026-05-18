//! A single pre-lambda-elim inlining pass that substitutes `Let` bindings at
//! their call sites for UDFs with non-iterable domains.
//!
//! # [`inline_non_iterable_lambdas`] — inlines `Let` bindings for functions with non-iterable domains
//!
//! Runs **before** [`crate::ccl::lambda_elim`].  Inlines any `Let` binding
//! (selected by [`should_inline`]) whose domain is not natively iterable by the
//! operator graph.  This covers:
//!
//! - **Scalar UDFs**: `Fun(non_iterable_domain, codomain)`.  These have a
//!   non-iterable (non-enumerable) domain.  Syntactic multi-arg Python lambdas
//!   (`lambda x, y: …`) are uncurried at lowering to `Tuple([…]) → T`, so they
//!   match this rule too.
//!
//! - **List-producing UDFs**: `Fun(Fun(iterable_domain, _), _)`.  Functions
//!   whose domain is itself a function type — generator functions and
//!   list-returning `def`s lowered to `λ user_arg → λ __iter_record → body`.
//!   A `Fun` domain has no iterable extent, so these are covered by the same
//!   non-iterable-domain rule.
//!
//! After substituting the bound lambda at each call site, the resulting
//! `Apply(arg, Lambda(x, body))` nodes are beta-reduced so that downstream
//! passes (lambda-elim, operator conversion) see fully-reduced expressions.
//! Multi-arg uncurried call sites leave behind `Apply(Tuple, Proj(Index(i)))`
//! references; those are folded by [`crate::ccl::simplify`]'s
//! `try_literal_tuple_projection` rule, not here.
//!
//! # Why a single pre-lambda-elim pass works for both
//!
//! Lambda-elim recurses into `Apply` nodes, so an `Apply(arg, Lambda)` produced
//! by inlining a scalar UDF before lambda-elim is handled correctly — the
//! `Lambda` inside the `Apply` gets converted to a combinator by lambda-elim as
//! usual.  Both scalar and list-producing UDFs benefit from the same
//! per-call-site beta-reduction performed here, making a separate post-elim
//! pass unnecessary.
//!
//! # Limitations
//!
//! - **Recursive UDFs** are not supported (already noted in operator conversion).
//! - **Body duplication**: if a scalar UDF is called N times, its body appears N
//!   times in the operator graph. Acceptable for now; caching is only needed for
//!   collection-typed UDFs (iterable domain), which are not inlined.
//!
//! # Alias inlining and defer-returning lift
//!
//! In addition to UDF inlining, this pass also performs two structural rewrites
//! that must happen before [`crate::ccl::lambda_elim`]:
//!
//! - **Alias inlining**: a `Let` binding whose right-hand side is a plain `Var`
//!   is pure α-renaming and is eliminated unconditionally.  Running this before
//!   lambda-elim prevents the let-in-lambda rule from hoisting such bindings into
//!   `const(x)` wrappers, which would otherwise require [`strip_const_wrappers`]
//!   recognition downstream.
//!
//! - **Defer-returning lift**: when a `Let` binding's right-hand side is a
//!   defer-returning expression — `let x = Defer in body_x` where `body_x` ends in
//!   `Var(x)`, possibly after `ExprStmt` and inner `Let` nodes — and possibly
//!   preceded by `ExprStmt` wrappers, the pass merges the inner and outer feed
//!   scopes:
//!   ```text
//!   let y = (let x = Defer in body_x) in body_y
//!     →  let y = Defer in body_x[x→y] with Var(y) replaced by body_y
//!   ```
//!   Because [`substitute`] now renames `Feed`/`Define` target strings when the
//!   replacement is a `Var`, the substitution `x → Var(y)` also rewrites every
//!   `Feed("x", …)` to `Feed("y", …)`, making the alias map from the old
//!   downstream implementation unnecessary.  Any `ExprStmt(Feed("c", …), …)`
//!   prefix produced by a beta-reduction whose argument was defer-returning is
//!   folded in by renaming the stale parameter-name feed targets to `y`.

use crate::ccl::{Branch, Expr, Type, TypedExprNode, lambda_elim::substitute};

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Inline `Let` bindings for UDFs with non-iterable domains and beta-reduce
/// their call sites.
///
/// Runs **before** [`crate::ccl::lambda_elim`].  Walks the expression tree and
/// substitutes each matching UDF at every free occurrence of its binding name
/// in the body, beta-reducing at each call site, then drops the `Let` wrapper.
///
/// Inlines any function whose domain is not natively iterable (see
/// [`should_inline`]): scalar UDFs, list-producing UDFs, and curried functions
/// all qualify.  Only bindings whose domain is natively iterable (`UIntRange`,
/// `DataSource`) are left intact.
///
/// Literal tuple projections that arise from uncurried multi-arg call sites
/// are *not* folded here — `crate::ccl::simplify` handles that rewrite as a
/// general rule so it fires consistently throughout the tree.
pub fn inline_non_iterable_lambdas(expr: Expr) -> Expr {
    let mut ctx = InlineCtx::default();
    inline_impl(expr, &mut ctx)
}

// ---------------------------------------------------------------------------
// Inline context
// ---------------------------------------------------------------------------

/// Mutable state threaded through [`inline_impl`].
///
/// Holds a monotonically increasing counter for minting unique synthetic
/// names that are introduced during inlining (e.g. ANF temporaries for
/// defer-returning Compose sources).
#[derive(Default)]
struct InlineCtx {
    /// Next suffix for `__for_src_N` ANF temporaries.
    counter: u64,
}

impl InlineCtx {
    /// Mint a unique `__for_src_N` name for ANF-ing a defer-returning
    /// Compose source out of its position.
    fn fresh_for_src_name(&mut self) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("__for_src_{n}")
    }
}

// ---------------------------------------------------------------------------
// Domain extent predicates
// ---------------------------------------------------------------------------

/// Returns `true` when `ty` has a finite, enumerable extent — i.e., when the
/// operator graph can natively schedule a function over this domain as
/// `IterateExtent` without inlining.
///
/// | Type | Iterable? | Reason |
/// |------|-----------|--------|
/// | `Base(_)` | no | No finite enumeration of all integers / strings / bools |
/// | `Tuple(ts)` | yes only if ALL `t` are iterable | A tuple can only be iterated if every component can |
/// | `Record(fields)` | yes only if ALL fields are iterable | Same logic as tuples: a record with an unbounded field has no finite extent |
/// | `Refinement(inner, _)` | same as `inner` | Refinement doesn't add iterability |
/// | `UIntRange(_)` | yes | Finite, bounded range |
/// | `DataSource(_)` | yes | Externally-backed finite collection |
/// | `Fun(_, _)` as domain | no | Infinitely many possible functions; cannot enumerate |
/// | anything else | yes | Conservative default: assume iterable so unknown types are not inlined |
fn is_iterable_domain(ty: &Type) -> bool {
    match ty {
        Type::Base(_) => false,
        // A tuple domain is iterable only if ALL components are iterable; you
        // can't enumerate (UIntRange(3), Int) because Int is unbounded.
        Type::Tuple(ts) => ts.iter().all(is_iterable_domain),
        // Records are structurally equivalent to tuples for extent purposes.
        Type::Record(fields) => fields.iter().all(|(_, t)| is_iterable_domain(t)),
        // Refinement inherits the iterability of its base type.
        Type::Refinement(inner, _) => is_iterable_domain(inner),
        // Natively iterable types.
        Type::UIntRange(_) | Type::DataSource(_) => true,
        // There are infinitely many possible functions for any given function
        // type, so function-typed domains cannot be enumerated.
        Type::Fun(_, _) => false,
        _ => true,
    }
}

/// Returns `true` when a `Let` binding of type `bound_ty` should be inlined.
///
/// Inlines `Let` bindings for functions whose domain is not iterable — i.e.,
/// domains the operator graph cannot natively schedule as `IterateExtent`.
/// This covers scalar UDFs (`Fun(Int, Int)`, `Fun(Tuple(Int,Int), Int)`, …),
/// list-producing UDFs (`Fun(Fun(UIntRange,Int), Fun(UIntRange,Int))`, …), and
/// curried functions (`Fun(Int, Fun(Int, Int))`, …): all of them have
/// non-iterable domains and cannot be compiled as standalone operators by
/// operator conversion.
///
/// # What is NOT inlined
///
/// Functions over natively iterable domains (`UIntRange`, `DataSource`) have a
/// domain the operator graph can natively schedule and iterate.  They compile
/// correctly as standalone `Let` bindings via `Memo + Splitter` and benefit
/// from sharing, so they are left intact.
fn should_inline(bound_ty: &Type) -> bool {
    match bound_ty {
        Type::Fun(domain, _) => !is_iterable_domain(domain),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Alias and defer helpers
// ---------------------------------------------------------------------------

/// Returns `true` if `name` is bound (shadowed) anywhere inside `expr` — by a
/// `Let` binder or a `Lambda` parameter.
///
/// Used to guard alias inlining: substituting `y → x` in a body that rebinds
/// `x` via an inner `let x = …` or `λ x → …` would cause the substituted `x`
/// references to be captured by the shadowing binding, producing incorrect
/// semantics.
fn is_let_bound(name: &str, expr: &Expr) -> bool {
    match &expr.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => binding.name == name || is_let_bound(name, bound_expr) || is_let_bound(name, body),
        // Lambda param shadows `name` inside the body — treat it as a binding
        // site so we don't substitute through it.
        TypedExprNode::Lambda { param, body, .. } => param.name == name || is_let_bound(name, body),
        TypedExprNode::Apply { function, argument } => {
            is_let_bound(name, function) || is_let_bound(name, argument)
        }
        TypedExprNode::BinOp { left, right, .. } => {
            is_let_bound(name, left) || is_let_bound(name, right)
        }
        TypedExprNode::UnaryOp(_, inner) => is_let_bound(name, inner),
        TypedExprNode::Tuple(elts) | TypedExprNode::List(elts) | TypedExprNode::Compose(elts) => {
            elts.iter().any(|e| is_let_bound(name, e))
        }
        TypedExprNode::Record(fields) => fields.iter().any(|(_, e)| is_let_bound(name, e)),
        TypedExprNode::Case { branches } => branches
            .iter()
            .any(|b| is_let_bound(name, &b.guard) || is_let_bound(name, &b.body)),
        TypedExprNode::Loop {
            init_args,
            source,
            loop_body,
            ..
        } => {
            is_let_bound(name, source)
                || init_args.iter().any(|a| is_let_bound(name, a))
                || is_let_bound(name, loop_body)
        }
        TypedExprNode::ExprStmt { expr, body } => {
            is_let_bound(name, expr) || is_let_bound(name, body)
        }
        TypedExprNode::Feed { value, .. } | TypedExprNode::Define { value, .. } => {
            is_let_bound(name, value)
        }
        TypedExprNode::Aggregate { input, .. } => is_let_bound(name, input),
        TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Defer => false,
    }
}

/// Returns `true` when `expr` ends in `Var(name)` through a chain of
/// `ExprStmt` sequencings and `Let` bindings, i.e. the expression ultimately
/// yields the named defer handle as its value.
///
/// Both `ExprStmt` (sequenced side-effects) and `Let` (intermediate bindings,
/// e.g. `z = n + 1` before `return x`) are transparent.  A `Let` that rebinds
/// `name` itself is opaque: the search stops and returns `false`.
///
/// Used by [`try_lift_defer`] to detect functions that return their own handle.
pub(crate) fn is_defer_returning(expr: &Expr, name: &str) -> bool {
    match &expr.node {
        TypedExprNode::Var(v) => v == name,
        TypedExprNode::ExprStmt { body, .. } => is_defer_returning(body, name),
        TypedExprNode::Let { binding, body, .. } => {
            binding.name != name && is_defer_returning(body, name)
        }
        _ => false,
    }
}

/// Replace the trailing `Var` at the end of an `ExprStmt`/`Let` chain with
/// `replacement`.
///
/// The caller guarantees (via [`is_defer_returning`]) that `expr` ends in a
/// `Var` node; any other tail shape panics.
pub(crate) fn replace_result_var(expr: Expr, replacement: Expr) -> Expr {
    match expr.node {
        TypedExprNode::Var(_) => replacement,
        TypedExprNode::ExprStmt { expr: e, body } => {
            let new_body = replace_result_var(*body, replacement);
            let ty = new_body.ty.clone();
            Expr {
                ty,
                node: TypedExprNode::ExprStmt {
                    expr: e,
                    body: Box::new(new_body),
                },
                user_annotation: None,
            }
        }
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let new_body = replace_result_var(*body, replacement);
            let ty = new_body.ty.clone();
            Expr {
                ty,
                node: TypedExprNode::Let {
                    binding,
                    bound_expr,
                    body: Box::new(new_body),
                },
                user_annotation: None,
            }
        }
        _ => panic!("replace_result_var: expected a defer-returning expression"),
    }
}

/// Attempt to apply the defer-returning lift to a `Let` binding.
///
/// Detects the pattern:
/// ```text
/// let y = (<prefix_stmts...> let x = Defer in body_x) in body_y
/// ```
/// where `body_x` ends in `Var(x)` (possibly through `ExprStmt`/`Let` chains),
/// and rewrites it to:
/// ```text
/// let y = Defer in <prefix_stmts_renamed...> body_x[x→y][Var(y)→body_y]
/// ```
///
/// The substitution `x → Var(y)` is performed via [`substitute`], which now
/// also renames `Feed("x", …)` → `Feed("y", …)` (the α-renaming fix).  Any
/// `ExprStmt(Feed("c", …), …)` prefix entries that were produced by beta-
/// reducing a defer-returning argument into a surrounding function are folded in
/// by renaming their stale feed targets to `y`.
///
/// Returns `None` when `bound_expr` does not match the liftable pattern.
fn try_lift_defer(binding_name: String, bound_expr: Expr, body: Expr) -> Option<Expr> {
    // Peel any leading ExprStmt layers off bound_expr.  The heads become the
    // `prefix` that must be prepended (with feed-target renames) to the merged body.
    let mut prefix: Vec<Expr> = Vec::new();
    let mut current = bound_expr;
    while let TypedExprNode::ExprStmt {
        expr: head,
        body: tail,
    } = current.node
    {
        prefix.push(*head);
        current = *tail;
    }

    // After peeling, check for `let x = Defer in body_x` with defer-returning body.
    let (inner_name, defer_ty, inner_body) = match current.node {
        TypedExprNode::Let {
            binding: inner_binding,
            bound_expr: inner_be,
            body: inner_body,
        } if inner_be.node == TypedExprNode::Defer
            && is_defer_returning(&inner_body, &inner_binding.name) =>
        {
            (inner_binding.name, inner_be.ty.clone(), *inner_body)
        }
        _ => return None,
    };

    // Substitute x → Var(binding_name) in inner_body.  The fixed substitute
    // renames Feed("x", …) → Feed(binding_name, …) since replacement is a Var.
    let y_var = Expr::var(&binding_name).with_ty(defer_ty.clone());
    let inner_subst = substitute(inner_body, &inner_name, &y_var);

    // Build the outer-body replacement: prefix feeds (renamed to binding_name)
    // wrapped around the original outer body.  Inserting them here — before `body`
    // but inside `replace_result_var` — preserves execution order:
    //   inner body feeds … prefix feeds … outer body feeds
    // This mirrors the Python argument-first evaluation order: the inner function
    // executes first (its feeds come first), then the outer wrapper's feeds.
    let mut new_outer_body = body;
    for head in prefix.into_iter().rev() {
        // Rename Feed/Define targets to binding_name.  These orphaned labels came
        // from lambda-parameter names that no longer exist after beta-reduction.
        let renamed_head = match head.node {
            TypedExprNode::Feed { name: _, value } => Expr {
                ty: head.ty,
                node: TypedExprNode::Feed {
                    name: binding_name.clone(),
                    value,
                },
                user_annotation: None,
            },
            TypedExprNode::Define { name: _, value } => Expr {
                ty: head.ty,
                node: TypedExprNode::Define {
                    name: binding_name.clone(),
                    value,
                },
                user_annotation: None,
            },
            _ => head,
        };
        let ty = new_outer_body.ty.clone();
        new_outer_body = Expr {
            ty,
            node: TypedExprNode::ExprStmt {
                expr: Box::new(renamed_head),
                body: Box::new(new_outer_body),
            },
            user_annotation: None,
        };
    }

    // Replace the trailing Var(y) in inner_subst with new_outer_body so
    // inner body feeds appear before prefix feeds and outer body feeds.
    let result = replace_result_var(inner_subst, new_outer_body);

    // Build `let y = Defer in result`, preserving the type of `result` on the
    // outer expression so downstream passes see a fully-typed tree.
    let result_ty = result.ty.clone();
    let defer_expr = Expr::new(TypedExprNode::Defer).with_ty(defer_ty);
    Some(Expr::let_bind(binding_name, defer_expr, result).with_ty(result_ty))
}

// ---------------------------------------------------------------------------
// Tree walk
// ---------------------------------------------------------------------------

/// Return `true` if `expr` is a liftable defer-returning expression — that is,
/// after peeling any [`TypedExprNode::ExprStmt`] prefixes it is a
/// `let name = Defer in body` where `body` ends in `Var(name)`.
///
/// Used by [`inline_impl`]'s Compose arm to detect when the first element of a
/// Compose (the iteration source) contains an inner defer scope that should be
/// ANF'd out so that [`try_lift_defer`] can merge it with the outer scope.
fn is_liftable_defer(expr: &Expr) -> bool {
    let mut current = expr;
    while let TypedExprNode::ExprStmt { body, .. } = &current.node {
        current = body;
    }
    match &current.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => bound_expr.node == TypedExprNode::Defer && is_defer_returning(body, &binding.name),
        _ => false,
    }
}

/// Recursively inline `Let` bindings that pass [`should_inline`], beta-reducing
/// each call site as the substitution produces it.
///
/// Also applies alias inlining (eliminates `let y = x` via α-renaming) and the
/// defer-returning lift before the UDF-inlining check.  Running these before
/// [`crate::ccl::lambda_elim`] prevents the let-in-lambda rewrite from
/// wrapping aliases in `const(…)` and ensures defer scope merging happens at the
/// right level.
fn inline_impl(expr: Expr, ctx: &mut InlineCtx) -> Expr {
    let Expr {
        node,
        ty,
        user_annotation,
    } = expr;

    let new_node = match node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let bound_expr = inline_impl(*bound_expr, ctx);
            let body = inline_impl(*body, ctx);

            // Alias: `let y = x` is pure α-renaming — substitute y → x in body
            // and drop the Let.  This must run before lambda_elim so that the
            // let-in-lambda rule never wraps such aliases in `const(x)`.
            //
            // Guard: only safe when x is not re-bound inside body.  If body
            // contains `let x = …` the substitution would capture those x
            // references under the wrong binding (e.g. `x = 1; y = x; x += 4;
            // y` must return 1, not 5).
            if let TypedExprNode::Var(repl_name) = &bound_expr.node
                && !is_let_bound(repl_name, &body)
            {
                return substitute(body, &binding.name, &bound_expr);
            }

            // Defer-returning lift: merge inner and outer feed scopes when the
            // bound_expr is a defer-returning let (possibly with ExprStmt prefix).
            if let Some(lifted) =
                try_lift_defer(binding.name.clone(), bound_expr.clone(), body.clone())
            {
                return lifted;
            }

            if should_inline(&bound_expr.ty) {
                // Substitute the bound Lambda at every free occurrence of the
                // binding name in the body, beta-reducing at each call site.
                //
                // Safety: substitution is not capture-avoiding, but this is
                // safe here because lowering assigns unique binding names per
                // scope — no free variable in `bound_expr` can shadow a binder
                // introduced in `body`.
                //
                // Re-run inline_impl after beta-reduction so that newly created
                // Let bindings (e.g. `let y = (let x = Defer in …) in …` after
                // expanding a defer-returning UDF) are eligible for the alias
                // and lift rewrites on the second pass.
                return inline_impl(
                    inline_and_beta_reduce(body, &binding.name, &bound_expr),
                    ctx,
                );
            }
            TypedExprNode::Let {
                binding,
                bound_expr: Box::new(bound_expr),
                body: Box::new(body),
            }
        }

        TypedExprNode::Apply { function, argument } => TypedExprNode::Apply {
            function: Box::new(inline_impl(*function, ctx)),
            argument: Box::new(inline_impl(*argument, ctx)),
        },

        TypedExprNode::BinOp { left, op, right } => TypedExprNode::BinOp {
            left: Box::new(inline_impl(*left, ctx)),
            op,
            right: Box::new(inline_impl(*right, ctx)),
        },

        TypedExprNode::UnaryOp(op, inner) => {
            TypedExprNode::UnaryOp(op, Box::new(inline_impl(*inner, ctx)))
        }

        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => TypedExprNode::Lambda {
            param,
            body: Box::new(inline_impl(*body, ctx)),
            refinement,
        },

        TypedExprNode::Aggregate { input, kind } => TypedExprNode::Aggregate {
            input: Box::new(inline_impl(*input, ctx)),
            kind,
        },

        TypedExprNode::Tuple(elts) => {
            TypedExprNode::Tuple(elts.into_iter().map(|e| inline_impl(e, ctx)).collect())
        }

        TypedExprNode::List(elts) => {
            TypedExprNode::List(elts.into_iter().map(|e| inline_impl(e, ctx)).collect())
        }

        TypedExprNode::Record(fields) => TypedExprNode::Record(
            fields
                .into_iter()
                .map(|(name, e)| (name, inline_impl(e, ctx)))
                .collect(),
        ),

        TypedExprNode::Case { branches } => TypedExprNode::Case {
            branches: branches
                .into_iter()
                .map(|b| Branch {
                    guard: inline_impl(b.guard, ctx),
                    body: inline_impl(b.body, ctx),
                })
                .collect(),
        },

        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
            body_taps,
        } => crate::ccl::walk_loop_children(
            params,
            init_args,
            source,
            loop_body,
            body_taps,
            // Structural traversal — no specific name being substituted.
            None,
            |e| inline_impl(e, ctx),
        ),

        // ANF defer-returning Compose source: when the first element of a Compose
        // (i.e. the for-loop iteration source) is itself a defer-returning
        // expression, wrap it in a fresh `let __for_src_N = source` binding so
        // that `try_lift_defer` can physically rename its inner defer handle,
        // preventing two same-named `__result` defers from coexisting in
        // `remove_defers`. Re-running `inline_impl` on the wrapping `Let`
        // triggers `try_lift_defer` on the new binding.
        TypedExprNode::Compose(terms) => {
            let mut inlined: Vec<Expr> = terms.into_iter().map(|t| inline_impl(t, ctx)).collect();
            if inlined.len() >= 2 && is_liftable_defer(&inlined[0]) {
                let source = inlined.remove(0);
                let source_ty = source.ty.clone();
                let fresh = ctx.fresh_for_src_name();
                // Preserve the original Compose type on the rebuilt Compose and
                // the Let so that the typecheck after UDF inlining still holds.
                let new_compose = Expr::compose(
                    std::iter::once(Expr::var(&fresh).with_ty(source_ty))
                        .chain(inlined)
                        .collect(),
                )
                .with_ty(ty.clone());
                return inline_impl(Expr::let_bind(fresh, source, new_compose).with_ty(ty), ctx);
            }
            TypedExprNode::Compose(inlined)
        }

        TypedExprNode::ExprStmt { expr, body } => TypedExprNode::ExprStmt {
            expr: Box::new(inline_impl(*expr, ctx)),
            body: Box::new(inline_impl(*body, ctx)),
        },

        TypedExprNode::Feed { name: id, value } => TypedExprNode::Feed {
            name: id,
            value: Box::new(inline_impl(*value, ctx)),
        },

        TypedExprNode::Define { name: id, value } => TypedExprNode::Define {
            name: id,
            value: Box::new(inline_impl(*value, ctx)),
        },

        // Leaves — no sub-expressions to recurse into.
        node @ (TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Defer) => node,
    };

    Expr {
        node: new_node,
        ty,
        user_annotation,
    }
}

/// Substitute `lambda` at every free occurrence of `name` in `expr`, and
/// beta-reduce at each call-site Apply chain — i.e. where `Var(name)` sits in
/// the function position of an `Apply(arg, …)` (optionally nested for curried
/// calls).
///
/// Only Apply chains that actually terminate in `Var(name)` participate in
/// beta-reduction. Unrelated `Apply(arg, Lambda)` patterns elsewhere in the
/// tree are left intact so lambda-elim + simplify still produce the structure
/// they expect for list comprehensions, scalar BinOps, etc.
///
/// TODO: immediately-applied anonymous lambdas (`Apply(arg, Lambda(x, body))`
/// not gated on a `Var(name)`) currently fall through this scope and survive
/// into `lambda_elim`.  They are equationally equivalent to a beta-reduction
/// here and would benefit from the same treatment, but doing so today
/// perturbs CCC simplify's input shape for list comprehensions, scalar UDFs,
/// and BinOp paths in ways that need test-suite triage first.  Revisit if a
/// case surfaces where the surviving anon-lambda blocks downstream work.
fn inline_and_beta_reduce(expr: Expr, name: &str, lambda: &Expr) -> Expr {
    // Direct occurrence: replace the variable with the Lambda value.
    if let TypedExprNode::Var(ref n) = expr.node
        && n == name
    {
        return lambda.clone();
    }

    // Apply chain ending in `Var(name)` — beta-reduce after recursively
    // substituting the argument and collapsing the function side.
    if let TypedExprNode::Apply { function, .. } = &expr.node
        && is_name_in_function_position(function, name)
    {
        let Expr {
            node,
            ty,
            user_annotation,
        } = expr;
        let (function, argument) = match node {
            TypedExprNode::Apply { function, argument } => (function, argument),
            _ => unreachable!(),
        };
        let argument = inline_and_beta_reduce(*argument, name, lambda);
        let function = inline_and_beta_reduce(*function, name, lambda);
        match function.node {
            TypedExprNode::Lambda {
                param,
                body,
                refinement,
            } => {
                // A refinement on the outer user-parameter lambda would
                // encode a precondition `P(arg)` that must hold for the
                // beta-reduced form to be equivalent. Current lowering of
                // generator/list-returning `def`s produces no refinement on
                // the outer parameter — the only refinement-bearing lambda
                // in that shape is the inner `__iter_record` lambda (if-guard
                // predicate), which we never beta-reduce here. If a future
                // lowering pass attaches a refinement to the outer param,
                // this branch needs a principled lift (e.g. emit a
                // `restrict(pred)` guard around the substituted body) before
                // proceeding.
                assert!(
                    refinement.is_none(),
                    "inline_and_beta_reduce: outer lambda for `{name}` has a \
                         refinement; beta reduction would silently drop its \
                         precondition. Extend this branch if list-UDF lowering \
                         starts producing refined outer params."
                );
                return substitute(*body, &param.name, &argument);
            }
            // Not a Lambda (e.g. the bound expression is Var("id") rather
            // than a literal lambda) — skip beta-reduction and reconstruct
            // the Apply with the substituted subexpressions.
            _ => {
                return Expr {
                    node: TypedExprNode::Apply {
                        function: Box::new(function),
                        argument: Box::new(argument),
                    },
                    ty,
                    user_annotation,
                };
            }
        }
    }

    // Not a call site of `name`: recurse into sub-expressions. Each recursion
    // carries the same (name, lambda) so that deeper call sites still
    // beta-reduce. This mirrors [`crate::ccl::lambda_elim::substitute`] but
    // preserves the specialised Apply-chain detection above.
    let Expr {
        node,
        ty,
        user_annotation,
    } = expr;
    let new_node = match node {
        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => {
            if param.name == name {
                // shadowed — stop substituting inside
                TypedExprNode::Lambda {
                    param,
                    body,
                    refinement,
                }
            } else {
                TypedExprNode::Lambda {
                    param,
                    body: Box::new(inline_and_beta_reduce(*body, name, lambda)),
                    refinement,
                }
            }
        }

        TypedExprNode::Let {
            binding,
            bound_expr,
            body,
        } => {
            let new_bound = inline_and_beta_reduce(*bound_expr, name, lambda);
            let new_body = if binding.name == name {
                *body
            } else {
                inline_and_beta_reduce(*body, name, lambda)
            };
            TypedExprNode::Let {
                binding,
                bound_expr: Box::new(new_bound),
                body: Box::new(new_body),
            }
        }

        TypedExprNode::Apply { function, argument } => TypedExprNode::Apply {
            function: Box::new(inline_and_beta_reduce(*function, name, lambda)),
            argument: Box::new(inline_and_beta_reduce(*argument, name, lambda)),
        },

        TypedExprNode::BinOp { left, op, right } => TypedExprNode::BinOp {
            left: Box::new(inline_and_beta_reduce(*left, name, lambda)),
            op,
            right: Box::new(inline_and_beta_reduce(*right, name, lambda)),
        },

        TypedExprNode::UnaryOp(op, inner) => {
            TypedExprNode::UnaryOp(op, Box::new(inline_and_beta_reduce(*inner, name, lambda)))
        }

        TypedExprNode::Aggregate { input, kind } => TypedExprNode::Aggregate {
            input: Box::new(inline_and_beta_reduce(*input, name, lambda)),
            kind,
        },

        TypedExprNode::Tuple(elts) => TypedExprNode::Tuple(
            elts.into_iter()
                .map(|e| inline_and_beta_reduce(e, name, lambda))
                .collect(),
        ),

        TypedExprNode::List(elts) => TypedExprNode::List(
            elts.into_iter()
                .map(|e| inline_and_beta_reduce(e, name, lambda))
                .collect(),
        ),

        TypedExprNode::Record(fields) => TypedExprNode::Record(
            fields
                .into_iter()
                .map(|(n, e)| (n, inline_and_beta_reduce(e, name, lambda)))
                .collect(),
        ),

        TypedExprNode::Case { branches } => TypedExprNode::Case {
            branches: branches
                .into_iter()
                .map(|b| Branch {
                    guard: inline_and_beta_reduce(b.guard, name, lambda),
                    body: inline_and_beta_reduce(b.body, name, lambda),
                })
                .collect(),
        },

        TypedExprNode::Compose(elts) => TypedExprNode::Compose(
            elts.into_iter()
                .map(|e| inline_and_beta_reduce(e, name, lambda))
                .collect(),
        ),

        TypedExprNode::Loop {
            params,
            init_args,
            source,
            loop_body,
            body_taps,
        } => crate::ccl::walk_loop_children(
            params,
            init_args,
            source,
            loop_body,
            body_taps,
            // Param shadowing matters here — we're substituting `name`
            // throughout, but if the loop's param binds `name`, the body
            // sees the param's value, not the substituted one.
            Some(name),
            |e| inline_and_beta_reduce(e, name, lambda),
        ),

        TypedExprNode::ExprStmt { expr, body } => TypedExprNode::ExprStmt {
            expr: Box::new(inline_and_beta_reduce(*expr, name, lambda)),
            body: Box::new(inline_and_beta_reduce(*body, name, lambda)),
        },

        TypedExprNode::Feed { name: id, value } => TypedExprNode::Feed {
            name: id,
            value: Box::new(inline_and_beta_reduce(*value, name, lambda)),
        },

        TypedExprNode::Define { name: id, value } => TypedExprNode::Define {
            name: id,
            value: Box::new(inline_and_beta_reduce(*value, name, lambda)),
        },

        // Leaves — no sub-expressions to recurse into.
        node @ (TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Builtin(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)
        | TypedExprNode::Defer) => node,
    };

    Expr {
        node: new_node,
        ty,
        user_annotation,
    }
}

/// Returns `true` when `expr` has `Var(name)` in the function position of its
/// Apply chain — i.e. `Var(name)`, or `Apply(_, …Apply(_, Var(name))…)`.
/// Used by [`inline_and_beta_reduce`] to decide whether an enclosing `Apply`
/// should beta-reduce after the inner substitution collapses a Lambda.
fn is_name_in_function_position(expr: &Expr, name: &str) -> bool {
    match &expr.node {
        TypedExprNode::Var(n) => n == name,
        TypedExprNode::Apply { function, .. } => is_name_in_function_position(function, name),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{BaseType, Lit, Type, TypedExpr, TypedExprNode};

    // -----------------------------------------------------------------------
    // is_iterable_domain predicate
    // -----------------------------------------------------------------------

    #[test]
    fn non_iterable_domain_base_int() {
        assert!(!is_iterable_domain(&Type::Base(BaseType::Int)));
    }

    #[test]
    fn non_iterable_domain_base_string() {
        assert!(!is_iterable_domain(&Type::Base(BaseType::String)));
    }

    #[test]
    fn iterable_domain_uint_range() {
        assert!(is_iterable_domain(&Type::UIntRange(3)));
    }

    #[test]
    fn iterable_domain_datasource() {
        assert!(is_iterable_domain(&Type::DataSource("s".to_string())));
    }

    #[test]
    fn non_iterable_domain_tuple_all_non_iterable() {
        let ty = Type::Tuple(vec![Type::Base(BaseType::Int), Type::Base(BaseType::Int)]);
        assert!(!is_iterable_domain(&ty));
    }

    #[test]
    fn non_iterable_domain_tuple_mixed() {
        // Any non-iterable component makes the whole tuple non-iterable.
        let ty = Type::Tuple(vec![Type::UIntRange(3), Type::Base(BaseType::Int)]);
        assert!(!is_iterable_domain(&ty));
    }

    #[test]
    fn iterable_domain_tuple_all_iterable() {
        let ty = Type::Tuple(vec![Type::UIntRange(3), Type::UIntRange(3)]);
        assert!(is_iterable_domain(&ty));
    }

    #[test]
    fn non_iterable_domain_record_any_non_iterable() {
        let ty = Type::Record(vec![
            ("x".to_string(), Type::Base(BaseType::Int)),
            ("n".to_string(), Type::UIntRange(3)),
        ]);
        assert!(!is_iterable_domain(&ty));
    }

    #[test]
    fn iterable_domain_record_all_iterable() {
        let ty = Type::Record(vec![
            ("a".to_string(), Type::UIntRange(2)),
            ("b".to_string(), Type::UIntRange(5)),
        ]);
        assert!(is_iterable_domain(&ty));
    }

    #[test]
    fn non_iterable_domain_record_all_non_iterable() {
        let ty = Type::Record(vec![
            ("x".to_string(), Type::Base(BaseType::Int)),
            ("y".to_string(), Type::Base(BaseType::String)),
        ]);
        assert!(!is_iterable_domain(&ty));
    }

    #[test]
    fn non_iterable_domain_refinement_wraps_non_iterable() {
        use crate::ccl::{Refinement, RefinementKind, next_refinement_id};
        use std::cell::RefCell;
        use std::rc::Rc;
        let pred = Rc::new(RefCell::new(TypedExpr::lit(Lit::Bool(true))));
        let refinement = Refinement {
            id: next_refinement_id(),
            description: "test".to_string(),
            kind: RefinementKind::Predicate(pred),
        };
        let ty = Type::Refinement(Box::new(Type::Base(BaseType::Int)), refinement);
        assert!(!is_iterable_domain(&ty));
    }

    #[test]
    fn iterable_domain_refinement_wraps_iterable() {
        use crate::ccl::{Refinement, RefinementKind, next_refinement_id};
        use std::cell::RefCell;
        use std::rc::Rc;
        let pred = Rc::new(RefCell::new(TypedExpr::lit(Lit::Bool(true))));
        let refinement = Refinement {
            id: next_refinement_id(),
            description: "test".to_string(),
            kind: RefinementKind::Predicate(pred),
        };
        let ty = Type::Refinement(Box::new(Type::UIntRange(3)), refinement);
        assert!(is_iterable_domain(&ty));
    }

    #[test]
    fn non_iterable_domain_fun() {
        // There are infinitely many possible Int → Int functions, so Fun-as-domain
        // has no finite, enumerable extent.
        let ty = Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Base(BaseType::Int)),
        );
        assert!(!is_iterable_domain(&ty));
    }

    // -----------------------------------------------------------------------
    // should_inline predicate
    // -----------------------------------------------------------------------

    #[test]
    fn should_inline_scalar_to_scalar() {
        let ty = Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Base(BaseType::Int)),
        );
        assert!(should_inline(&ty));
    }

    #[test]
    fn should_inline_curried_fun() {
        // Int → (Int → Int): domain is non-iterable (Int), so the curried
        // function is now inlined. Beta-reduction at concrete call sites
        // eliminates the nested lambda before any `curry` combinator is produced.
        let ty = Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Fun(
                Box::new(Type::Base(BaseType::Int)),
                Box::new(Type::Base(BaseType::Int)),
            )),
        );
        assert!(should_inline(&ty));
    }

    #[test]
    fn should_inline_refined_fun_codomain() {
        // Int → Refinement(Int → Int, pred): domain is non-iterable (Int),
        // so the function is inlined regardless of the refined codomain.
        use crate::ccl::{Refinement, RefinementKind, next_refinement_id};
        use std::cell::RefCell;
        use std::rc::Rc;
        let pred = Rc::new(RefCell::new(TypedExpr::lit(Lit::Bool(true))));
        let refinement = Refinement {
            id: next_refinement_id(),
            description: "test".to_string(),
            kind: RefinementKind::Predicate(pred),
        };
        let inner_fun = Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Base(BaseType::Int)),
        );
        let ty = Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Refinement(Box::new(inner_fun), refinement)),
        );
        assert!(should_inline(&ty));
    }

    #[test]
    fn should_not_inline_iterable_domain() {
        // UIntRange(3) → Int: iterable domain, don't inline.
        let ty = Type::Fun(
            Box::new(Type::UIntRange(3)),
            Box::new(Type::Base(BaseType::Int)),
        );
        assert!(!should_inline(&ty));
    }

    #[test]
    fn should_inline_all_non_iterable_tuple_domain() {
        // (Int, Int) → Int: both components non-iterable, should inline.
        let ty = Type::Fun(
            Box::new(Type::Tuple(vec![
                Type::Base(BaseType::Int),
                Type::Base(BaseType::Int),
            ])),
            Box::new(Type::Base(BaseType::Int)),
        );
        assert!(should_inline(&ty));
    }

    #[test]
    fn should_inline_mixed_tuple_domain() {
        // (UIntRange(3), Int) → Int: any non-iterable component makes the tuple
        // non-iterable, so this is inlined.
        let ty = Type::Fun(
            Box::new(Type::Tuple(vec![
                Type::UIntRange(3),
                Type::Base(BaseType::Int),
            ])),
            Box::new(Type::Base(BaseType::Int)),
        );
        assert!(should_inline(&ty));
    }

    #[test]
    fn should_inline_base_type_not_fun() {
        // Not a function type — should not inline.
        assert!(!should_inline(&Type::Base(BaseType::Int)));
    }

    #[test]
    fn should_inline_list_to_list_udf() {
        // Fun(Fun(UIntRange, Int), Fun(UIntRange, Int)): list-producing UDF, should inline.
        let int = Type::Base(BaseType::Int);
        let list = fn_ty(Type::UIntRange(3), int.clone());
        assert!(should_inline(&fn_ty(list.clone(), list)));
    }

    #[test]
    fn should_inline_tuple_arg_list_udf() {
        // Fun(Tuple(List, Int), List): uncurried multi-arg list UDF, should inline.
        let int = Type::Base(BaseType::Int);
        let list = fn_ty(Type::UIntRange(3), int.clone());
        let domain = Type::Tuple(vec![list.clone(), int]);
        assert!(should_inline(&fn_ty(domain, list)));
    }

    #[test]
    fn should_inline_list_to_scalar_udf() {
        // Fun(Fun(UIntRange, Int), Int): takes a list, returns a scalar (e.g. a
        // user-defined sum/fold). The domain is a Fun type — non-iterable —
        // so this is inlined just like any other non-iterable-domain function.
        let int = Type::Base(BaseType::Int);
        let list = fn_ty(Type::UIntRange(3), int.clone());
        assert!(should_inline(&fn_ty(list, int)));
    }

    // -----------------------------------------------------------------------
    // run pass structural transforms
    // -----------------------------------------------------------------------

    /// Build a scalar `Let` binding: `let x: Int = 2 in BinOp(Var(x), Add, Lit(1))`.
    fn scalar_let() -> Expr {
        let int = Type::Base(BaseType::Int);
        let bound = TypedExpr::lit(Lit::Int(2)).with_ty(int.clone());
        let body = TypedExpr::new(TypedExprNode::BinOp {
            left: Box::new(TypedExpr::var("x").with_ty(int.clone())),
            op: crate::ccl::BinOpKind::Arithmetic(crate::ccl::ArithmeticKind::Add),
            right: Box::new(TypedExpr::lit(Lit::Int(1)).with_ty(int.clone())),
        })
        .with_ty(int.clone());
        TypedExpr::let_bind("x", bound, body)
    }

    #[test]
    fn scalar_let_unchanged() {
        let expr = scalar_let();
        let result = inline_non_iterable_lambdas(expr.clone());
        assert_eq!(result, expr);
    }

    #[test]
    fn collection_let_alias_is_inlined() {
        // let f: UIntRange(3) → Int = id in f
        // Even though the domain is iterable (so should_inline returns false), the bound
        // expression is a plain Var — alias inlining eliminates the let unconditionally.
        let domain = Type::UIntRange(3);
        let codomain = Type::Base(BaseType::Int);
        let fun_ty = Type::fun(domain.clone(), codomain.clone());
        let id_expr = TypedExpr::var("id").with_ty(fun_ty.clone());
        let body = TypedExpr::var("f").with_ty(fun_ty.clone());
        let expr = TypedExpr::let_bind("f", id_expr.clone(), body);
        let result = inline_non_iterable_lambdas(expr);
        // Alias `f → id` is substituted; result is just `id`.
        assert_eq!(result, id_expr);
    }

    #[test]
    fn curried_let_is_inlined() {
        // let f: Int → (Int → Int) = curry_add in f
        // Domain is Int (non-iterable), so the curried Let IS inlined.
        // After inline_non_iterable_lambdas: the Let is dropped and the result is Var("curry_add").
        let int = Type::Base(BaseType::Int);
        let curried_ty = Type::fun(int.clone(), Type::fun(int.clone(), int.clone()));
        let curry_expr = TypedExpr::var("curry_add").with_ty(curried_ty.clone());
        let body = TypedExpr::var("f").with_ty(curried_ty.clone());
        let expr = TypedExpr::let_bind("f", curry_expr.clone(), body);
        let result = inline_non_iterable_lambdas(expr);
        assert_eq!(result, curry_expr);
    }

    #[test]
    fn scalar_function_let_is_inlined() {
        // let f: Int → Int = id in Apply(Lit(3), Var(f))
        // After inlining: Apply(Lit(3), id)
        let int = Type::Base(BaseType::Int);
        let fun_ty = Type::fun(int.clone(), int.clone());
        let id_expr = TypedExpr::var("id").with_ty(fun_ty.clone());
        let apply = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(3)).with_ty(int.clone())),
            function: Box::new(TypedExpr::var("f").with_ty(fun_ty.clone())),
        })
        .with_ty(int.clone());
        let expr = TypedExpr::let_bind("f", id_expr.clone(), apply);

        let result = inline_non_iterable_lambdas(expr);

        // The Let wrapper should be gone; Var(f) replaced by id_expr.
        // Note: id_expr is Var("id"), not a Lambda, so Apply(Lit(3), id_expr)
        // is not beta-reduced (no Lambda to reduce into).
        let expected = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(3)).with_ty(int.clone())),
            function: Box::new(id_expr),
        })
        .with_ty(int.clone());
        assert_eq!(result, expected);
    }

    #[test]
    fn multi_use_inlining_substitutes_all_occurrences() {
        // let f: Int → Int = id in Tuple([Apply(3, f), Apply(4, f)])
        // After inlining: Tuple([Apply(3, id), Apply(4, id)])
        let int = Type::Base(BaseType::Int);
        let fun_ty = Type::fun(int.clone(), int.clone());
        let id_expr = TypedExpr::var("id").with_ty(fun_ty.clone());

        let call3 = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(3)).with_ty(int.clone())),
            function: Box::new(TypedExpr::var("f").with_ty(fun_ty.clone())),
        })
        .with_ty(int.clone());
        let call4 = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(4)).with_ty(int.clone())),
            function: Box::new(TypedExpr::var("f").with_ty(fun_ty.clone())),
        })
        .with_ty(int.clone());
        let body = TypedExpr::tuple(vec![call3, call4])
            .with_ty(Type::Tuple(vec![int.clone(), int.clone()]));
        let expr = TypedExpr::let_bind("f", id_expr.clone(), body);

        let result = inline_non_iterable_lambdas(expr);

        let expected_call3 = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(3)).with_ty(int.clone())),
            function: Box::new(id_expr.clone()),
        })
        .with_ty(int.clone());
        let expected_call4 = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(4)).with_ty(int.clone())),
            function: Box::new(id_expr),
        })
        .with_ty(int.clone());
        let expected = TypedExpr::tuple(vec![expected_call3, expected_call4])
            .with_ty(Type::Tuple(vec![int.clone(), int.clone()]));
        assert_eq!(result, expected);
    }

    #[test]
    fn unused_function_let_is_dropped() {
        // let f: Int → Int = id in Lit(42)
        // After inlining (f is never used): Lit(42)
        let int = Type::Base(BaseType::Int);
        let fun_ty = Type::fun(int.clone(), int.clone());
        let id_expr = TypedExpr::var("id").with_ty(fun_ty);
        let body = TypedExpr::lit(Lit::Int(42)).with_ty(int.clone());
        let expr = TypedExpr::let_bind("f", id_expr, body);

        let result = inline_non_iterable_lambdas(expr);
        let expected = TypedExpr::lit(Lit::Int(42)).with_ty(int);
        assert_eq!(result, expected);
    }

    #[test]
    fn nested_inlining_both_lets_inlined() {
        // let f: Int → Int = id in let g: Int → Int = id in Apply(Apply(3, g), f)
        // After inlining both: Apply(Apply(3, id), id)
        let int = Type::Base(BaseType::Int);
        let fun_ty = Type::fun(int.clone(), int.clone());
        let id_f = TypedExpr::var("id").with_ty(fun_ty.clone());
        let id_g = TypedExpr::var("id").with_ty(fun_ty.clone());

        let inner_apply = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(3)).with_ty(int.clone())),
            function: Box::new(TypedExpr::var("g").with_ty(fun_ty.clone())),
        })
        .with_ty(int.clone());
        let outer_apply = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(inner_apply),
            function: Box::new(TypedExpr::var("f").with_ty(fun_ty.clone())),
        })
        .with_ty(int.clone());

        let inner_let = TypedExpr::let_bind("g", id_g.clone(), outer_apply);
        let expr = TypedExpr::let_bind("f", id_f.clone(), inner_let);

        let result = inline_non_iterable_lambdas(expr);

        // Both f and g should be substituted with id.
        let expected_inner = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::lit(Lit::Int(3)).with_ty(int.clone())),
            function: Box::new(id_g),
        })
        .with_ty(int.clone());
        let expected = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(expected_inner),
            function: Box::new(id_f),
        })
        .with_ty(int.clone());
        assert_eq!(result, expected);
    }

    // -----------------------------------------------------------------------
    // Helper used in the remaining tests
    // -----------------------------------------------------------------------

    /// `Fun(domain, codomain)` shorthand for the tests below.
    fn fn_ty(domain: Type, codomain: Type) -> Type {
        Type::Fun(Box::new(domain), Box::new(codomain))
    }

    // is_name_in_function_position — call-site detector
    // -----------------------------------------------------------------------

    #[test]
    fn name_in_function_position_bare_var() {
        let expr = TypedExpr::var("f");
        assert!(is_name_in_function_position(&expr, "f"));
        assert!(!is_name_in_function_position(&expr, "g"));
    }

    #[test]
    fn name_in_function_position_apply_chain() {
        // `Apply(arg2, Apply(arg1, Var("f")))` — curried call of `f`.
        let int = Type::Base(BaseType::Int);
        let inner = TypedExpr::apply(
            TypedExpr::lit(Lit::Int(1)).with_ty(int.clone()),
            TypedExpr::var("f"),
        );
        let outer = TypedExpr::apply(TypedExpr::lit(Lit::Int(2)).with_ty(int), inner);
        assert!(is_name_in_function_position(&outer, "f"));
        assert!(!is_name_in_function_position(&outer, "g"));
    }

    #[test]
    fn name_in_function_position_in_argument_only() {
        // `Apply(Var("f"), Var("g"))` — `f` sits in the *argument* slot, not
        // function. Should not count as `f` in function position.
        let expr = TypedExpr::apply(TypedExpr::var("f"), TypedExpr::var("g"));
        assert!(is_name_in_function_position(&expr, "g"));
        assert!(!is_name_in_function_position(&expr, "f"));
    }

    #[test]
    fn name_in_function_position_non_apply_non_var() {
        // Lambda/Lit/etc. never put Var(name) in function position by themselves.
        assert!(!is_name_in_function_position(
            &TypedExpr::lit(Lit::Int(1)),
            "f"
        ));
    }

    // inline_and_beta_reduce — targeted behaviour
    // -----------------------------------------------------------------------

    #[test]
    fn inline_and_beta_reduce_bare_var_replaced_with_lambda() {
        // `Var("f")` in a non-call position is substituted literally (the
        // Lambda value), no beta reduction.
        let int = Type::Base(BaseType::Int);
        let lambda = TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
            .with_ty(fn_ty(int.clone(), int.clone()));
        let body = TypedExpr::var("f").with_ty(fn_ty(int.clone(), int));
        let result = inline_and_beta_reduce(body, "f", &lambda);
        assert_eq!(result, lambda);
    }

    #[test]
    fn inline_and_beta_reduce_single_arg_call() {
        // `Apply(lit(3), Var("f"))` with `f = λ x → x` beta-reduces to `3`.
        let int = Type::Base(BaseType::Int);
        let lambda = TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
            .with_ty(fn_ty(int.clone(), int.clone()));
        let arg = TypedExpr::lit(Lit::Int(3)).with_ty(int.clone());
        let call = TypedExpr::apply(arg.clone(), TypedExpr::var("f").with_ty(lambda.ty.clone()))
            .with_ty(int);
        let result = inline_and_beta_reduce(call, "f", &lambda);
        assert_eq!(result, arg);
    }

    #[test]
    fn inline_and_beta_reduce_curried_call() {
        // `Apply(lit(2), Apply(lit(1), Var("f")))` with `f = λ a → λ b → a`
        // reduces to `1` (first argument wins). Mirrors the multi-arg
        // curried UDF call site.
        let int = Type::Base(BaseType::Int);
        let inner = TypedExpr::lambda("b", int.clone(), TypedExpr::var("a").with_ty(int.clone()))
            .with_ty(fn_ty(int.clone(), int.clone()));
        let lambda = TypedExpr::lambda("a", int.clone(), inner)
            .with_ty(fn_ty(int.clone(), fn_ty(int.clone(), int.clone())));
        let call = TypedExpr::apply(
            TypedExpr::lit(Lit::Int(2)).with_ty(int.clone()),
            TypedExpr::apply(
                TypedExpr::lit(Lit::Int(1)).with_ty(int.clone()),
                TypedExpr::var("f").with_ty(lambda.ty.clone()),
            )
            .with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int.clone());
        let result = inline_and_beta_reduce(call, "f", &lambda);
        assert_eq!(result, TypedExpr::lit(Lit::Int(1)).with_ty(int));
    }

    #[test]
    fn inline_and_beta_reduce_shadowing_guard() {
        // `Lambda("f", Var("f"))` — the inner `f` is shadowed by the lambda
        // param, so substitution must not replace it. The input binding of
        // `f` to the lambda we pass in is irrelevant here.
        let int = Type::Base(BaseType::Int);
        let shadowed =
            TypedExpr::lambda("f", int.clone(), TypedExpr::var("f").with_ty(int.clone()))
                .with_ty(fn_ty(int.clone(), int.clone()));
        // Some arbitrary lambda we'd otherwise inline if `f` weren't shadowed.
        let replacement = TypedExpr::lambda(
            "x",
            int.clone(),
            TypedExpr::lit(Lit::Int(42)).with_ty(int.clone()),
        )
        .with_ty(fn_ty(int.clone(), int));
        let result = inline_and_beta_reduce(shadowed.clone(), "f", &replacement);
        assert_eq!(result, shadowed);
    }

    // inline_non_iterable_lambdas — end-to-end pass behaviour
    // -----------------------------------------------------------------------

    #[test]
    fn inline_non_iterable_lambdas_inlines_scalar_let() {
        // Scalar UDF: `let f: Int → Int = id in Var("f")`.
        // After inline_non_iterable_lambdas: the Let is dropped and the result is Var("id").
        let int = Type::Base(BaseType::Int);
        let ident = TypedExpr::var("id").with_ty(fn_ty(int.clone(), int.clone()));
        let body = TypedExpr::var("f").with_ty(fn_ty(int.clone(), int.clone()));
        let expr = TypedExpr::let_bind("f", ident.clone(), body);
        let result = inline_non_iterable_lambdas(expr);
        assert_eq!(result, ident);
    }

    #[test]
    fn inline_non_iterable_lambdas_inlines_user_curried_let() {
        // `let f: Int → (Int → Int) = g in f` — user-curried scalar.
        // Domain is Int (non-iterable), so `should_inline` returns true and
        // the Let IS inlined. After inline_non_iterable_lambdas: the result is Var("g").
        let int = Type::Base(BaseType::Int);
        let curried = fn_ty(int.clone(), fn_ty(int.clone(), int.clone()));
        let ident = TypedExpr::var("g").with_ty(curried.clone());
        let body = TypedExpr::var("f").with_ty(curried);
        let expr = TypedExpr::let_bind("f", ident.clone(), body);
        let result = inline_non_iterable_lambdas(expr);
        assert_eq!(result, ident);
    }

    #[test]
    fn inline_non_iterable_lambdas_inlines_and_beta_reduces_list_udf() {
        // Mirror the simplest generator-function lowering:
        //   let doubles = λ xs → λ __iter_record → __iter_record ▷ xs ▷ (λ x → x)
        //   in [1, 2, 3] ▷ doubles
        // After inline_non_iterable_lambdas: the outer `λ xs` is substituted and beta-reduced,
        // leaving `λ __iter_record → __iter_record ▷ [1, 2, 3] ▷ (λ x → x)`.
        let int = Type::Base(BaseType::Int);
        let range = Type::UIntRange(3);
        let list = fn_ty(range.clone(), int.clone());
        let udf_ty = fn_ty(list.clone(), list.clone());

        let inner_lambda_body = TypedExpr::apply(
            TypedExpr::apply(
                TypedExpr::var("__iter_record").with_ty(range.clone()),
                TypedExpr::var("xs").with_ty(list.clone()),
            )
            .with_ty(int.clone()),
            TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
                .with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int.clone());
        let inner_lambda =
            TypedExpr::lambda("__iter_record", range.clone(), inner_lambda_body.clone())
                .with_ty(list.clone());
        let outer_lambda =
            TypedExpr::lambda("xs", list.clone(), inner_lambda).with_ty(udf_ty.clone());

        let list_literal = TypedExpr::new(TypedExprNode::List(vec![
            TypedExpr::lit(Lit::Int(1)).with_ty(int.clone()),
            TypedExpr::lit(Lit::Int(2)).with_ty(int.clone()),
            TypedExpr::lit(Lit::Int(3)).with_ty(int.clone()),
        ]))
        .with_ty(list.clone());
        let call = TypedExpr::apply(
            list_literal.clone(),
            TypedExpr::var("doubles").with_ty(udf_ty.clone()),
        )
        .with_ty(list.clone());
        let expr = TypedExpr::let_bind("doubles", outer_lambda, call);

        let result = inline_non_iterable_lambdas(expr);

        // Expected: the top-level node is the inner Lambda (no more Let, no
        // more outer `λ xs`), with `xs` substituted by the concrete list.
        let expected_body = TypedExpr::apply(
            TypedExpr::apply(
                TypedExpr::var("__iter_record").with_ty(range.clone()),
                list_literal,
            )
            .with_ty(int.clone()),
            TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
                .with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int);
        let expected = TypedExpr::lambda("__iter_record", range, expected_body).with_ty(list);
        assert_eq!(result, expected);
    }

    #[test]
    fn inline_non_iterable_lambdas_substitutes_arg_pair_into_multi_arg_body() {
        // Mirror the uncurried multi-arg shape:
        //   let f = λ __arg_pair → λ __iter_record → … __arg_pair.0 …
        //   in ([1, 2, 3], 10) ▷ f
        // After inline_non_iterable_lambdas: the outer `λ __arg_pair` is
        // beta-reduced, leaving `Tuple([1,2,3], 10).0` in the body. The
        // literal-tuple-projection fold lives in `crate::ccl::simplify` and
        // is *not* applied here — this test asserts only the substitution +
        // outer-lambda beta-reduction behaviour.
        let int = Type::Base(BaseType::Int);
        let range = Type::UIntRange(3);
        let list = fn_ty(range.clone(), int.clone());
        let arg_pair_ty = Type::Tuple(vec![list.clone(), int.clone()]);
        let udf_ty = fn_ty(arg_pair_ty.clone(), list.clone());

        // body: λ __iter_record → __iter_record ▷ __arg_pair.0 ▷ (λ x → x)
        let proj0 = TypedExpr::new(TypedExprNode::Proj(crate::ccl::ProjKey::Index(0)))
            .with_ty(fn_ty(arg_pair_ty.clone(), list.clone()));
        let pair_proj = TypedExpr::apply(
            TypedExpr::var("__arg_pair").with_ty(arg_pair_ty.clone()),
            proj0.clone(),
        )
        .with_ty(list.clone());
        let inner_body = TypedExpr::apply(
            TypedExpr::apply(
                TypedExpr::var("__iter_record").with_ty(range.clone()),
                pair_proj,
            )
            .with_ty(int.clone()),
            TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
                .with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int.clone());
        let inner_lambda =
            TypedExpr::lambda("__iter_record", range.clone(), inner_body).with_ty(list.clone());
        let outer_lambda = TypedExpr::lambda("__arg_pair", arg_pair_ty.clone(), inner_lambda)
            .with_ty(udf_ty.clone());

        let list_literal = TypedExpr::new(TypedExprNode::List(vec![
            TypedExpr::lit(Lit::Int(1)).with_ty(int.clone()),
            TypedExpr::lit(Lit::Int(2)).with_ty(int.clone()),
            TypedExpr::lit(Lit::Int(3)).with_ty(int.clone()),
        ]))
        .with_ty(list.clone());
        let arg = TypedExpr::tuple(vec![
            list_literal.clone(),
            TypedExpr::lit(Lit::Int(10)).with_ty(int.clone()),
        ])
        .with_ty(arg_pair_ty.clone());
        let call = TypedExpr::apply(arg.clone(), TypedExpr::var("f").with_ty(udf_ty))
            .with_ty(list.clone());
        let expr = TypedExpr::let_bind("f", outer_lambda, call);

        let result = inline_non_iterable_lambdas(expr);

        // Expected: outer Let / outer `λ __arg_pair` are gone; references to
        // `__arg_pair` are rewritten to the concrete tuple literal, so the
        // `Tuple([list, 10]).0` shape now sits inside the body verbatim.
        let folded_pair_proj = TypedExpr::apply(arg, proj0).with_ty(list.clone());
        let expected_body = TypedExpr::apply(
            TypedExpr::apply(
                TypedExpr::var("__iter_record").with_ty(range.clone()),
                folded_pair_proj,
            )
            .with_ty(int.clone()),
            TypedExpr::lambda("x", int.clone(), TypedExpr::var("x").with_ty(int.clone()))
                .with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int);
        let expected = TypedExpr::lambda("__iter_record", range, expected_body).with_ty(list);
        assert_eq!(result, expected);
    }

    #[test]
    fn inline_non_iterable_lambdas_beta_reduces_scalar_lambda_call() {
        // let f: Int → Int = λ x → Lit(42) in Apply(Lit(3), Var("f"))
        // After inline_non_iterable_lambdas: Lit(42) (the constant lambda is beta-reduced,
        // discarding the argument Lit(3)).
        let int = Type::Base(BaseType::Int);
        let lambda = TypedExpr::lambda(
            "x",
            int.clone(),
            TypedExpr::lit(Lit::Int(42)).with_ty(int.clone()),
        )
        .with_ty(fn_ty(int.clone(), int.clone()));
        let call = TypedExpr::apply(
            TypedExpr::lit(Lit::Int(3)).with_ty(int.clone()),
            TypedExpr::var("f").with_ty(fn_ty(int.clone(), int.clone())),
        )
        .with_ty(int.clone());
        let expr = TypedExpr::let_bind("f", lambda, call);

        let result = inline_non_iterable_lambdas(expr);
        let expected = TypedExpr::lit(Lit::Int(42)).with_ty(int);
        assert_eq!(result, expected);
    }

    #[test]
    fn inline_non_iterable_lambdas_substitutes_pair_into_multi_arg_scalar_body() {
        // let add: Tuple(Int, Int) → Int = λ __pair → __pair.0 + __pair.1
        // in add(Tuple(Lit(1), Lit(2)))
        //
        // After inline_non_iterable_lambdas: the body becomes
        //   Tuple(1, 2).0 + Tuple(1, 2).1
        // — the literal-tuple projections survive here and are folded later
        // by `crate::ccl::simplify::try_literal_tuple_projection`.
        use crate::ccl::{ArithmeticKind, BinOpKind};
        let int = Type::Base(BaseType::Int);
        let pair_ty = Type::Tuple(vec![int.clone(), int.clone()]);
        let udf_ty = fn_ty(pair_ty.clone(), int.clone());

        // __pair.0: Apply(argument: Var("__pair"), function: Proj(0))
        let proj0 = TypedExpr::new(TypedExprNode::Proj(crate::ccl::ProjKey::Index(0)))
            .with_ty(fn_ty(pair_ty.clone(), int.clone()));
        let pair_proj0 = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::var("__pair").with_ty(pair_ty.clone())),
            function: Box::new(proj0.clone()),
        })
        .with_ty(int.clone());

        // __pair.1: Apply(argument: Var("__pair"), function: Proj(1))
        let proj1 = TypedExpr::new(TypedExprNode::Proj(crate::ccl::ProjKey::Index(1)))
            .with_ty(fn_ty(pair_ty.clone(), int.clone()));
        let pair_proj1 = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(TypedExpr::var("__pair").with_ty(pair_ty.clone())),
            function: Box::new(proj1.clone()),
        })
        .with_ty(int.clone());

        // body: __pair.0 + __pair.1
        let body = TypedExpr::new(TypedExprNode::BinOp {
            left: Box::new(pair_proj0),
            op: BinOpKind::Arithmetic(ArithmeticKind::Add),
            right: Box::new(pair_proj1),
        })
        .with_ty(int.clone());

        // λ __pair → body
        let lambda = TypedExpr::lambda("__pair", pair_ty.clone(), body).with_ty(udf_ty.clone());

        // arg: Tuple(Lit(1), Lit(2))
        let lit1 = TypedExpr::lit(Lit::Int(1)).with_ty(int.clone());
        let lit2 = TypedExpr::lit(Lit::Int(2)).with_ty(int.clone());
        let arg = TypedExpr::tuple(vec![lit1.clone(), lit2.clone()]).with_ty(pair_ty.clone());

        // call: Apply(argument: arg, function: Var("add"))
        let call = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(arg.clone()),
            function: Box::new(TypedExpr::var("add").with_ty(udf_ty)),
        })
        .with_ty(int.clone());

        let expr = TypedExpr::let_bind("add", lambda, call);
        let result = inline_non_iterable_lambdas(expr);

        // Expected: Tuple(1,2).0 + Tuple(1,2).1 — projections unfolded here.
        let expected_left = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(arg.clone()),
            function: Box::new(proj0),
        })
        .with_ty(int.clone());
        let expected_right = TypedExpr::new(TypedExprNode::Apply {
            argument: Box::new(arg),
            function: Box::new(proj1),
        })
        .with_ty(int.clone());
        let expected = TypedExpr::new(TypedExprNode::BinOp {
            left: Box::new(expected_left),
            op: BinOpKind::Arithmetic(ArithmeticKind::Add),
            right: Box::new(expected_right),
        })
        .with_ty(int);
        assert_eq!(result, expected);
    }

    // -----------------------------------------------------------------------
    // is_defer_returning
    // -----------------------------------------------------------------------

    fn int_ty() -> Type {
        Type::Base(BaseType::Int)
    }

    fn lit(n: i64) -> TypedExpr {
        TypedExpr::lit(Lit::Int(n)).with_ty(int_ty())
    }

    fn var(s: &str) -> TypedExpr {
        TypedExpr::var(s)
    }

    /// `is_defer_returning` sees through a plain `Let` wrapper.
    #[test]
    fn is_defer_returning_through_let() {
        let expr = TypedExpr::let_bind("z", lit(99), var("x"));
        assert!(is_defer_returning(&expr, "x"));
        assert!(!is_defer_returning(&expr, "z"));
    }

    /// A `Let` that rebinds the target name stops the search.
    #[test]
    fn is_defer_returning_stops_at_shadowing_let() {
        let expr = TypedExpr::let_bind("x", lit(42), var("x"));
        assert!(
            !is_defer_returning(&expr, "x"),
            "shadowing let must return false"
        );
        let outer = TypedExpr::let_bind("z", lit(1), expr);
        assert!(
            !is_defer_returning(&outer, "x"),
            "false must propagate outward"
        );
    }

    /// `is_defer_returning` sees through nested `Let` + `ExprStmt`.
    #[test]
    fn is_defer_returning_through_let_and_expr_stmt() {
        let inner = TypedExpr::expr_stmt(
            TypedExpr::new(TypedExprNode::Feed {
                name: "y".into(),
                value: Box::new(lit(2)),
            }),
            var("x"),
        );
        let expr = TypedExpr::let_bind("z", lit(1), inner);
        assert!(is_defer_returning(&expr, "x"));
    }

    // -----------------------------------------------------------------------
    // replace_result_var
    // -----------------------------------------------------------------------

    /// `replace_result_var` threads through a `Let` wrapper.
    #[test]
    fn replace_result_var_through_let() {
        let expr = TypedExpr::let_bind("z", lit(99), var("x"));
        let result = replace_result_var(expr, lit(42));
        use crate::ccl::symbolic::symbolic;
        let s = symbolic(&result);
        assert!(s.contains("99") && s.contains("42"), "unexpected: {s}");
        assert!(!s.contains(" x"), "Var(x) should be replaced: {s}");
    }

    // -----------------------------------------------------------------------
    // Alias inlining + defer-returning lift via inline_non_iterable_lambdas
    // -----------------------------------------------------------------------

    /// `inline_non_iterable_lambdas` lifts `let y = (let x = Defer in body_x) in y`
    /// to `let y = Defer in body_x[x→y]`, enabling `remove_defers` to process it.
    ///
    /// Simulates `def f(): x = defer(); z = 42; x <<= z; x` assigned as `y = f()`.
    #[test]
    fn inline_lifts_defer_returning_nested_let() {
        // let x = Defer[Int] in (let z = 42 in ExprStmt(Define("x", z), x))
        let define_site = TypedExpr::expr_stmt(
            TypedExpr::new(TypedExprNode::Define {
                name: "x".into(),
                value: Box::new(var("z")),
            }),
            var("x"),
        );
        let inner_body = TypedExpr::let_bind("z", lit(42), define_site);
        let x_defer = TypedExpr::new(TypedExprNode::Defer).with_ty(int_ty());
        let inner = TypedExpr::let_bind("x", x_defer, inner_body);

        // let y = <inner> in y
        let expr = TypedExpr::let_bind("y", inner, var("y"));
        let result = inline_non_iterable_lambdas(expr);

        use crate::ccl::symbolic::symbolic;
        let s = symbolic(&result);
        // The lift must have happened: the outer let binds Defer directly, not
        // the whole nested-let expression.
        assert!(
            s.contains("let y") && s.contains("defer"),
            "lift should have produced let y = defer: {s}"
        );
        assert!(
            !s.contains("let x"),
            "inner let x = Defer must be absorbed: {s}"
        );
        assert!(
            s.contains("define(y"),
            "Define target should be renamed to y: {s}"
        );
    }
}
