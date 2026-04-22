//! Inlining pass: substitutes function-typed `Let` bindings at their call sites.
//!
//! This pass runs after [`crate::ccl::lambda_elim`] and before
//! [`crate::ccl::join_plan`]. It eliminates `Let` nodes whose bound expression
//! has a scalar function type (i.e., `Fun(domain, _)` where `domain` has no
//! finite, enumerable extent) by substituting the bound expression at every
//! call site in the body and dropping the `Let` wrapper.
//!
//! # Motivation
//!
//! Operator conversion compiles `Let`-bound expressions independently with
//! `input = None`.  When the bound expression is a scalar-to-scalar function
//! (domain = `Int`, `Bool`, etc.), this causes the operator graph to build an
//! `IterateExtent` over the base type, which has no finite extent — causing a
//! panic at runtime ("Attempted to iterate on infinite Extent").
//!
//! By inlining the function body at each call site before operator conversion,
//! the call site supplies the argument as `input`, so no `IterateExtent` is
//! created for the domain.
//!
//! # What is inlined
//!
//! A `Let { binding, bound_expr, body }` is inlined when
//! [`should_inline`] returns `true` for `bound_expr.ty`:
//!
//! - `bound_expr.ty` is `Fun(domain, codomain)`,
//! - `domain` has an infinite (non-enumerable) extent, and
//! - `codomain` is not itself a `Fun` — see the comment on
//!   [`should_inline`] for why we narrow this way even though syntactic
//!   multi-arg lambdas are uncurried at lowering.
//!
//! Syntactic multi-arg Python lambdas are lowered to a single
//! tupled-domain function (see [`crate::ccl::lower::lower_lambda`]), so
//! common user programs like `add = lambda x, y: x + y` reach this pass
//! with `bound_expr.ty = Tuple([Int, Int]) → Int` — tupled domain, non-Fun
//! codomain — and are inlined by the same rule as single-arg scalar UDFs.
//!
//! Collection-typed functions (`Fun(UIntRange, _)`, `Fun(DataSource, _)`) are
//! **not** inlined; they compile correctly with `Memo + Splitter` and benefit
//! from sharing.
//!
//! # Limitations
//!
//! - **Recursive UDFs** are not supported (already noted in operator conversion).
//! - **Explicitly curried UDFs** (nested `lambda x: lambda y: …` in source, or
//!   explicit `curry(f)` calls) still produce `Apply(body, Var("curry"))`
//!   shapes that operator conversion cannot compile. `should_inline` keeps
//!   these Lets intact so the failure surfaces cleanly at the bound expression
//!   — tracked as follow-up work.
//! - **Body duplication**: if a scalar UDF is called N times, its body appears N
//!   times in the operator graph. Acceptable for now; caching is only needed for
//!   collection-typed UDFs (finite domain), which are not inlined.

use crate::ccl::{lambda_elim::substitute, Branch, Expr, Type, TypedExprNode};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Inline function-typed `Let` bindings whose domain has no finite extent.
///
/// Walks the expression tree and substitutes the bound expression at every
/// free occurrence of the binding name in the body, then drops the `Let`
/// wrapper.  All other nodes are recursed into unchanged.
pub fn run(expr: Expr) -> Expr {
    inline(expr)
}

// ---------------------------------------------------------------------------
// Domain extent predicates
// ---------------------------------------------------------------------------

/// Returns `true` when `ty` has no finite, enumerable extent.
///
/// Used to decide whether a function whose domain is `ty` can be compiled
/// stand-alone (with `IterateExtent`) or must be inlined at call sites.
///
/// | Type | Infinite? | Reason |
/// |------|-----------|--------|
/// | `Base(_)` | yes | No finite enumeration of all integers / strings / bools |
/// | `Tuple(ts)` | yes if any `t` is infinite | A tuple can only be iterated if every component can |
/// | `Record(fields)` | yes if any field is infinite | Same logic as tuples: a record with an unbounded field has no finite extent |
/// | `Refinement(inner, _)` | same as `inner` | Refinement doesn't add finiteness |
/// | `UIntRange(_)` | no | Finite, bounded range |
/// | `DataSource(_)` | no | Externally-backed finite collection |
/// | `Fun(_, _)` as domain | no | Collection UDF; out of scope for this pass |
/// | anything else | no | Conservative default |
fn is_infinite_domain(ty: &Type) -> bool {
    match ty {
        Type::Base(_) => true,
        // A tuple domain is infinite if ANY component is infinite; you can't
        // enumerate (UIntRange(3), Int) because Int is unbounded.
        Type::Tuple(ts) => ts.iter().any(is_infinite_domain),
        // Records are structurally equivalent to tuples for extent purposes.
        Type::Record(fields) => fields.iter().any(|(_, t)| is_infinite_domain(t)),
        // Refinement inherits the finiteness of its base type.
        Type::Refinement(inner, _) => is_infinite_domain(inner),
        // Finite, enumerable types.
        Type::UIntRange(_) | Type::DataSource(_) => false,
        // Fun-as-domain (higher-order / collection UDFs): treat as finite to
        // exclude from inlining — these require a separate fix.
        _ => false,
    }
}

/// Returns `true` when `ty` is a function type (possibly wrapped in `Refinement`).
///
/// Used by [`should_inline`] to detect curried codomains — including
/// `Refinement(Fun, _)` — so that explicitly-curried `Let` bindings are
/// left intact. See the comment on [`should_inline`] for the full rationale.
fn is_fun_type(ty: &Type) -> bool {
    match ty {
        Type::Fun(_, _) => true,
        Type::Refinement(inner, _) => is_fun_type(inner),
        _ => false,
    }
}

/// Returns `true` when a `Let` binding of type `bound_ty` should be inlined.
///
/// Inlines scalar-to-scalar functions: those whose domain is infinite
/// (non-enumerable) and whose codomain is not itself a function type.
///
/// # Why exclude curried codomains
///
/// The `!is_fun_type(codomain)` guard is a defensive narrowing, not a
/// soundness requirement. Syntactic multi-arg Python lambdas are uncurried
/// to a tupled-domain function in
/// [`crate::ccl::lower::lower_lambda`], so their `bound_ty` has a non-Fun
/// codomain and *does* get inlined here. The only way `bound_ty` reaches
/// this pass with a Fun codomain is when the user explicitly curried —
/// e.g. `lambda x: lambda y: body` or an explicit `curry(f)` call. Those
/// programs produce an `Apply(body, Var("curry"))`-shaped bound
/// expression, which operator conversion cannot compile (there is no
/// `curry` combinator case in [`crate::interpreter::operator_conversion`]).
///
/// If we dropped the guard and inlined those Lets, the inlined body would
/// splice the curry combinator into every call site, propagating the
/// failure. By keeping the Let intact, the failure surfaces once, cleanly,
/// at the bound expression with a recognisable "unrecognised Var(curry)"
/// error — much easier to trace than a deeper tree error. When explicit
/// curry support lands in operator conversion, this guard can be dropped.
/// `is_fun_type` handles `Refinement(Fun, _)` so a refinement layer on the
/// curried codomain does not defeat the check.
fn should_inline(bound_ty: &Type) -> bool {
    match bound_ty {
        Type::Fun(domain, codomain) => is_infinite_domain(domain) && !is_fun_type(codomain),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Recursive inlining walk
// ---------------------------------------------------------------------------

/// Recursively inline function-typed `Let` bindings in `expr`.
fn inline(expr: Expr) -> Expr {
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
            // Recurse into the bound expression first (handles nested lets).
            let bound_expr = inline(*bound_expr);
            let body = inline(*body);

            if should_inline(&bound_expr.ty) {
                // Substitute the bound expression at every free occurrence of
                // the binding name in the body, then drop the Let wrapper.
                // Safety: `substitute` is not capture-avoiding, but this is
                // safe here because lowering assigns unique binding names per
                // scope — no free variable in `bound_expr` can shadow a binder
                // introduced in `body`.
                return substitute(body, &binding.name, &bound_expr);
            }
            TypedExprNode::Let {
                binding,
                bound_expr: Box::new(bound_expr),
                body: Box::new(body),
            }
        }

        // Recurse into all other node types.
        TypedExprNode::Apply { function, argument } => TypedExprNode::Apply {
            function: Box::new(inline(*function)),
            argument: Box::new(inline(*argument)),
        },

        TypedExprNode::BinOp { left, op, right } => TypedExprNode::BinOp {
            left: Box::new(inline(*left)),
            op,
            right: Box::new(inline(*right)),
        },

        TypedExprNode::UnaryOp(op, inner) => TypedExprNode::UnaryOp(op, Box::new(inline(*inner))),

        TypedExprNode::Lambda {
            param,
            body,
            refinement,
        } => TypedExprNode::Lambda {
            param,
            body: Box::new(inline(*body)),
            refinement,
        },

        TypedExprNode::Aggregate { input, kind } => TypedExprNode::Aggregate {
            input: Box::new(inline(*input)),
            kind,
        },

        TypedExprNode::Tuple(elts) => TypedExprNode::Tuple(elts.into_iter().map(inline).collect()),

        TypedExprNode::List(elts) => TypedExprNode::List(elts.into_iter().map(inline).collect()),

        TypedExprNode::Record(fields) => TypedExprNode::Record(
            fields
                .into_iter()
                .map(|(name, e)| (name, inline(e)))
                .collect(),
        ),

        TypedExprNode::Case { branches } => TypedExprNode::Case {
            branches: branches
                .into_iter()
                .map(|b| Branch {
                    guard: inline(b.guard),
                    body: inline(b.body),
                })
                .collect(),
        },

        TypedExprNode::Join {
            name,
            params,
            loop_body,
            outer_body,
        } => TypedExprNode::Join {
            name,
            params,
            loop_body: Box::new(inline(*loop_body)),
            outer_body: Box::new(inline(*outer_body)),
        },

        TypedExprNode::Jump { target, args } => TypedExprNode::Jump {
            target,
            args: args.into_iter().map(inline).collect(),
        },

        TypedExprNode::Compose(elts) => {
            TypedExprNode::Compose(elts.into_iter().map(inline).collect())
        }

        TypedExprNode::GroupBy { collection, key } => TypedExprNode::GroupBy {
            collection: Box::new(inline(*collection)),
            key: Box::new(inline(*key)),
        },

        // Leaves — no sub-expressions to recurse into.
        node @ (TypedExprNode::Lit(_)
        | TypedExprNode::Var(_)
        | TypedExprNode::Proj(_)
        | TypedExprNode::Source(_)) => node,
    };

    Expr {
        node: new_node,
        ty,
        user_annotation,
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
    // is_infinite_domain predicate
    // -----------------------------------------------------------------------

    #[test]
    fn infinite_domain_base_int() {
        assert!(is_infinite_domain(&Type::Base(BaseType::Int)));
    }

    #[test]
    fn infinite_domain_base_string() {
        assert!(is_infinite_domain(&Type::Base(BaseType::String)));
    }

    #[test]
    fn infinite_domain_uint_range_is_finite() {
        assert!(!is_infinite_domain(&Type::UIntRange(3)));
    }

    #[test]
    fn infinite_domain_datasource_is_finite() {
        assert!(!is_infinite_domain(&Type::DataSource("s".to_string())));
    }

    #[test]
    fn infinite_domain_tuple_all_infinite() {
        let ty = Type::Tuple(vec![Type::Base(BaseType::Int), Type::Base(BaseType::Int)]);
        assert!(is_infinite_domain(&ty));
    }

    #[test]
    fn infinite_domain_tuple_mixed_is_infinite() {
        // Any infinite component makes the whole tuple infinite.
        let ty = Type::Tuple(vec![Type::UIntRange(3), Type::Base(BaseType::Int)]);
        assert!(is_infinite_domain(&ty));
    }

    #[test]
    fn infinite_domain_tuple_all_finite() {
        let ty = Type::Tuple(vec![Type::UIntRange(3), Type::UIntRange(3)]);
        assert!(!is_infinite_domain(&ty));
    }

    #[test]
    fn infinite_domain_record_any_infinite() {
        let ty = Type::Record(vec![
            ("x".to_string(), Type::Base(BaseType::Int)),
            ("n".to_string(), Type::UIntRange(3)),
        ]);
        assert!(is_infinite_domain(&ty));
    }

    #[test]
    fn infinite_domain_record_all_finite() {
        let ty = Type::Record(vec![
            ("a".to_string(), Type::UIntRange(2)),
            ("b".to_string(), Type::UIntRange(5)),
        ]);
        assert!(!is_infinite_domain(&ty));
    }

    #[test]
    fn infinite_domain_record_all_infinite() {
        let ty = Type::Record(vec![
            ("x".to_string(), Type::Base(BaseType::Int)),
            ("y".to_string(), Type::Base(BaseType::String)),
        ]);
        assert!(is_infinite_domain(&ty));
    }

    #[test]
    fn infinite_domain_refinement_wraps_infinite() {
        use crate::ccl::{next_refinement_id, Refinement, RefinementKind};
        use std::cell::RefCell;
        use std::rc::Rc;
        let pred = Rc::new(RefCell::new(TypedExpr::lit(Lit::Bool(true))));
        let refinement = Refinement {
            id: next_refinement_id(),
            description: "test".to_string(),
            kind: RefinementKind::Predicate(pred),
        };
        let ty = Type::Refinement(Box::new(Type::Base(BaseType::Int)), refinement);
        assert!(is_infinite_domain(&ty));
    }

    #[test]
    fn infinite_domain_refinement_wraps_finite() {
        use crate::ccl::{next_refinement_id, Refinement, RefinementKind};
        use std::cell::RefCell;
        use std::rc::Rc;
        let pred = Rc::new(RefCell::new(TypedExpr::lit(Lit::Bool(true))));
        let refinement = Refinement {
            id: next_refinement_id(),
            description: "test".to_string(),
            kind: RefinementKind::Predicate(pred),
        };
        let ty = Type::Refinement(Box::new(Type::UIntRange(3)), refinement);
        assert!(!is_infinite_domain(&ty));
    }

    #[test]
    fn infinite_domain_fun_as_domain_is_not_infinite() {
        // Fun-as-domain (collection/generator UDF): out of scope, treated as finite.
        let ty = Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Base(BaseType::Int)),
        );
        assert!(!is_infinite_domain(&ty));
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
    fn should_inline_curried_codomain_excluded() {
        // Int → (Int → Int): codomain is Fun, do not inline.
        let ty = Type::Fun(
            Box::new(Type::Base(BaseType::Int)),
            Box::new(Type::Fun(
                Box::new(Type::Base(BaseType::Int)),
                Box::new(Type::Base(BaseType::Int)),
            )),
        );
        assert!(!should_inline(&ty));
    }

    #[test]
    fn should_inline_refined_fun_codomain_excluded() {
        // Int → Refinement(Int → Int, pred): codomain wraps a Fun, do not inline.
        use crate::ccl::{next_refinement_id, Refinement, RefinementKind};
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
        assert!(!should_inline(&ty));
    }

    #[test]
    fn should_inline_finite_domain_excluded() {
        // UIntRange(3) → Int: finite domain, don't inline.
        let ty = Type::Fun(
            Box::new(Type::UIntRange(3)),
            Box::new(Type::Base(BaseType::Int)),
        );
        assert!(!should_inline(&ty));
    }

    #[test]
    fn should_inline_all_infinite_tuple_domain() {
        // (Int, Int) → Int: both components infinite, should inline.
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
        // (UIntRange(3), Int) → Int: any-infinite tuple domain, should inline.
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
        let result = run(expr.clone());
        assert_eq!(result, expr);
    }

    #[test]
    fn collection_let_unchanged() {
        // let f: UIntRange(3) → Int = id in f
        let domain = Type::UIntRange(3);
        let codomain = Type::Base(BaseType::Int);
        let fun_ty = Type::fun(domain.clone(), codomain.clone());
        let id_expr = TypedExpr::var("id").with_ty(fun_ty.clone());
        let body = TypedExpr::var("f").with_ty(fun_ty.clone());
        let expr = TypedExpr::let_bind("f", id_expr, body);
        let result = run(expr.clone());
        assert_eq!(result, expr);
    }

    #[test]
    fn curried_let_unchanged() {
        // let f: Int → (Int → Int) = curry(add) in f
        let int = Type::Base(BaseType::Int);
        let curried_ty = Type::fun(int.clone(), Type::fun(int.clone(), int.clone()));
        let curry_expr = TypedExpr::var("curry_add").with_ty(curried_ty.clone());
        let body = TypedExpr::var("f").with_ty(curried_ty.clone());
        let expr = TypedExpr::let_bind("f", curry_expr, body);
        let result = run(expr.clone());
        assert_eq!(result, expr);
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

        let result = run(expr);

        // The Let wrapper should be gone; Var(f) replaced by id_expr.
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

        let result = run(expr);

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

        let result = run(expr);
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

        let result = run(expr);

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
}
