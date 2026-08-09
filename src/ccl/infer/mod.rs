//! Cambra's inference algorithm — the constraint-emission and coalescing engine.
//!
//! The canonical type inference implementation, invoked via
//! [`crate::ccl::infer::infer`].
//!
//! # Design
//!
//! Two passes over the expression tree:
//!
//! 1. **Constraint emission**: walk the tree, emit `constrain_subtype` calls
//!    over [`Type`] (inference variables are [`Type::Infer`] with mutable
//!    bounds), writing each node's emitted `Type` straight onto `expr.ty`.
//!    Because the vars are shared `Rc<InferVar>`s, later constraints
//!    accumulate into bounds that are already visible through the stored
//!    `Type` — no side table is needed. Domain refinements ride the type
//!    lattice as restriction refinements on [`Type::Refinement`] (introduced by the
//!    `cast` Apply arm), so they flow through the solver structurally.
//! 2. **Coalesce + write-back + monomorphize**: walk the tree again and, for
//!    each node, run
//!    [`coalesce_compact`](crate::ccl::infer::solver::coalesce_compact) to
//!    resolve the inference variables in its `expr.ty` in place. The same
//!    walk lowers let-polymorphism: a use of a generalized `let` is
//!    specialized at first visit, memoized per distinct instantiation
//!    ([`specialize_use`](solve::specialize_use)), and the `let` rebuilds
//!    itself as the chain of demanded specializations
//!    ([`coalesce_generalized_let`](solve::coalesce_generalized_let)).
//!
//! # Let-polymorphism
//!
//! A `let` whose RHS is a *function definition* is **generalized**: its RHS is
//! emitted one level deeper (`in_let_rhs`), then generalized into a
//! [`PolyScheme`](crate::ccl::infer::solver::PolyScheme) at the binding site (`scoped_let`), so each use instantiates
//! fresh quantified variables and is constrained independently. This is what
//! lets `let id = λx.x in (id 1, id "a")` type-check
//! where a monomorphic `let` would collide.
//!
//! Because `ccl::Type` has no `ForAll` and the downstream passes are
//! monomorphic, generalization is paired with **monomorphization**,
//! integrated into the coalesce walk: at a generalized use, the walk resolves
//! the instantiation type off the live constraint graph (complete by then),
//! emits one specialized clone of the definition per distinct instantiation
//! (`freshen_expr_type_slots` + a constrain-against-the-live-use-type pin + a
//! re-entrant coalesce), and rewrites the use to reference its
//! specialization. So inference both type-checks the polymorphism and lowers
//! it to concrete per-type code before lambda-elimination. Sharing one
//! specialization across same-typed uses is what lets a collection/generator
//! UDF used at several element types compile to one *cached* binding per
//! element type rather than a copy per call. Specializing *inside* the walk —
//! rather than splicing after it — is what keeps every parent type derived
//! from concrete children (no post-hoc re-derivation of dependent types), and
//! handles chained polymorphism (a generalized UDF used only inside another
//! generalized definition) by plain recursion.
//!
//! Generalization itself is narrow ([`should_generalize`](context::should_generalize)): only *function*
//! definitions with a quantifiable variable. Value bindings stay monomorphic
//! and shared (the pre-let-poly behavior), since specializing a value would
//! duplicate it, which the feed/define and join-planning machinery is sensitive
//! to.
//!
//! The [`OperatorSchemes`] registry additionally contains [`PolyScheme`](crate::ccl::infer::solver::PolyScheme)s for
//! the handful of operator/projection cases that are inherently polymorphic
//! (`Compare : ∀α β. α → β → Greater(α, β)`, `Max : ∀α γ. (α → γ) → γ`, etc.). Each scheme
//! is `instantiate`d at every use site, minting fresh vars per use.
//!
//! Most `Builtin` nodes are introduced post-inference by
//! `lambda_elim`/`planning` with their type pre-stamped on the node, and
//! inference just rubber-stamps them. The exceptions are polymorphic
//! builtins introduced pre-inference (e.g. `FinalOrDefault` from
//! `lower_mutation_loop`); those have entries in [`OperatorSchemes`] and
//! are freshened at each use site like any other scheme.

mod api;
mod check;
mod context;
mod emit;
mod schemes;
mod solve;
pub mod solver;
mod typing;

// Public surface (consumed by `crate::ccl::infer`): the entry points, the check
// pass, and the operator-scheme registry. (Inference is the only type-synthesis
// pass: feed reads type concretely via their rigid `ChanDom` channel domains,
// which `crate::ccl::channelize` erases by substitution — no post-channelize
// re-typing.)
pub use api::*;
pub use check::check;
pub use schemes::OperatorSchemes;

use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use crate::ccl::FieldKey;
use crate::ccl::infer::solver::{CoalesceError, ConstrainError, ReduceError, prim};
use crate::ccl::{BaseType, BinOpKind, CompareKind, Lit, Refinement, Type, TypedExpr};

use context::InferCtx;
use emit::emit_node;
use solve::{coalesce_pass, resolve_var_type};

// `Name` is no longer debug-only: `lit_singleton` builds its predicate over the
// refinement binder in every build.
use crate::ccl::Name;
#[cfg(debug_assertions)]
use solve::check_scope_valid;

/// Build a structural product [`Type`] from a `FieldKey`-keyed field map:
/// all-`Name` keys → `Record`, otherwise a dense `Tuple` (the emitter only
/// builds dense `Index` products from 0). For a *sparse* / open index
/// position (an index projection's domain), the emitter pads to a dense
/// `Tuple` explicitly rather than going through here — see `emit_proj`.
pub(super) fn product(fields: BTreeMap<FieldKey, Type>) -> Type {
    if fields.keys().all(|k| matches!(k, FieldKey::Name(_))) {
        Type::Record(
            fields
                .into_iter()
                .map(|(k, t)| match k {
                    FieldKey::Name(n) => (n.to_string(), t),
                    _ => unreachable!(),
                })
                .collect(),
        )
    } else {
        // BTreeMap iterates in key order, so dense `Index` keys come out
        // in position order.
        Type::Tuple(fields.into_values().collect())
    }
}

/// Build a [`Type::Variant`] from a `FieldKey`-keyed tag map.
pub(super) fn variant_type(tags: BTreeMap<FieldKey, Type>) -> Type {
    Type::Variant(tags.into_iter().collect())
}

/// Resolve a (possibly variable-laden) [`Type`] to a concrete type for use
/// in error messages. Falls back to [`Type::Hole`] if coalesce fails (which
/// can happen for types with incompatible bounds that triggered the error).
pub(super) fn coalesce_for_error(ty: &Type) -> Type {
    resolve_var_type(ty).unwrap_or(Type::Hole)
}

/// Map a [`ConstrainError`] onto the public [`InferError`] enum.
pub(super) fn map_constrain_err(err: ConstrainError, ctx_label: &str) -> InferError {
    match err {
        ConstrainError::Mismatch { lhs, rhs } => {
            let lhs_ty = coalesce_for_error(&lhs);
            let rhs_ty = coalesce_for_error(&rhs);
            // `constrain_subtype(lhs, rhs)` means `lhs <: rhs`. If rhs is a function
            // and lhs is not, the caller passed a non-function where a function
            // was expected (e.g. applying a non-function at an Apply site).
            if matches!(rhs, Type::Fun { .. }) && !matches!(lhs, Type::Fun { .. }) {
                InferError::ExpectedFunction {
                    found: lhs_ty,
                    at: ctx_label.to_string(),
                }
            } else {
                InferError::TypeMismatch {
                    ctx: ctx_label.to_string(),
                    found: Box::new(lhs_ty),
                    expected: Some(Box::new(rhs_ty)),
                }
            }
        }
        // The offending type is named on its own: the `ctx` already says what is
        // wrong with it, and there is no second type the demand could be.
        ConstrainError::MissingField { key, in_type } => InferError::TypeMismatch {
            ctx: format!("{ctx_label} (missing field {key:?})"),
            found: Box::new(coalesce_for_error(&in_type)),
            expected: None,
        },
        ConstrainError::ExtraTag { tag, in_type } => InferError::TypeMismatch {
            ctx: format!("{ctx_label} (variant tag .{tag} not accepted)"),
            found: Box::new(coalesce_for_error(&in_type)),
            expected: None,
        },
        ConstrainError::NotAFeed { found, required } => InferError::TypeMismatch {
            ctx: format!("{ctx_label} (a feed handle is required here, but the value is not one)"),
            found: Box::new(coalesce_for_error(&found)),
            expected: Some(Box::new(coalesce_for_error(&required))),
        },
        ConstrainError::ComputeWhereDataRequired { lhs, rhs } => InferError::TypeMismatch {
            ctx: format!(
                "{ctx_label} (a compute function ⇒ was supplied where a data \
                 collection ⤇ is required — using a capability as a collection \
                 would iterate a declared domain the value does not cover)"
            ),
            found: Box::new(coalesce_for_error(&lhs)),
            expected: Some(Box::new(coalesce_for_error(&rhs))),
        },
        ConstrainError::DataDomainMismatch { lhs, rhs } => InferError::TypeMismatch {
            ctx: format!(
                "collection domain conflict at {ctx_label} (a collection's domain is \
                 its data, so a join may not narrow it — two collections over distinct \
                 domains have no common data-function type, and their lossless join is \
                 a dependent sum over the candidate domains)"
            ),
            found: Box::new(coalesce_for_error(&lhs)),
            expected: Some(Box::new(coalesce_for_error(&rhs))),
        },
    }
}

/// Map a [`CoalesceError`] onto the public [`InferError`] enum.
pub(super) fn map_coalesce_err(err: CoalesceError, ctx_label: &str) -> InferError {
    match err {
        CoalesceError::IncompatibleBounds {
            polarity,
            vars,
            details,
        } => InferError::IncompatibleBounds {
            polarity,
            conflicting: details,
            vars,
            origin: ctx_label.to_string(),
            context: vec![],
        },
        CoalesceError::UnresolvedPartial { kind, details } => InferError::UnresolvedPartial {
            kind: format!("{:?} ({})", kind, details),
            at: ctx_label.to_string(),
        },
        CoalesceError::RecursiveType { details } => InferError::Unsupported(format!(
            "recursive type at {}: {} (residual μ-types are forbidden)",
            ctx_label, details
        )),
        CoalesceError::DomainJoinConflict { details } => InferError::Unsupported(format!(
            "collection domain conflict at {}: {} \
             (a collection's domain is its data, so a join may not narrow it)",
            ctx_label, details
        )),
        CoalesceError::ComputeWhereDataRequired { details } => InferError::Unsupported(format!(
            "a compute function ⇒ was supplied where a data collection ⤇ is required at {}: {} \
             (using a capability as a collection would iterate a declared domain the value \
             does not cover)",
            ctx_label, details
        )),
        // A reduction conflict is an ordinary type error about the operands, and it
        // says so in its own words. Routing it through `IncompatibleBounds` — the
        // shape the shared-variable scheme used to produce for `1 + "a"` — would
        // reuse that variant's rendering along with its shape, and the rendering is
        // a specific claim ("won't infer an untagged sum from a collision") that is
        // not what happened here: each operand is well typed and nothing collided
        // on a variable.
        CoalesceError::Reduce(ReduceError::NoCommonBase { fun, bases }) => {
            InferError::NoCommonBase {
                fun,
                bases,
                at: ctx_label.to_string(),
            }
        }
        // A rule that cannot answer through a cycle. The program defined something
        // in terms of itself in a way this rule has no answer for, which is a user
        // error about the *program*, not a conflict between two types — so it is
        // reported in its own words rather than as a mismatch.
        CoalesceError::Reduce(ReduceError::CyclicArgument { fun }) => {
            InferError::Unsupported(format!(
                "{fun} cannot be computed at {ctx_label}: one of its arguments is \
                 defined in terms of this very application, and {fun} has no answer \
                 without it"
            ))
        }
    }
}

/// Map a literal to its base [`Type`].
pub(super) fn lit_base(lit: &Lit) -> Type {
    match lit {
        Lit::Int(_) => prim(BaseType::Int),
        Lit::String(_) => prim(BaseType::String),
        Lit::Bool(_) => prim(BaseType::Bool),
        Lit::Unit => prim(BaseType::Unit),
    }
}

/// The type of a literal: its base refined by the **singleton** predicate
/// `__elem == lit`, so `5 : {Int | __elem == 5}`.
///
/// A literal knows more about itself than its base type does, and that knowledge is
/// what a proof obligation needs: `a[0]` can only discharge against `Array(3, 𝑇)`'s
/// index range if `0`'s type says it *is* `0`. Typing `5` as plain `Int` throws that
/// away at the one place it is free to keep.
///
/// Carried as an ordinary [`Type::Refinement`] rather than a `Literal(base, value)`
/// type, so every existing rule applies unchanged and none has to learn a new case:
/// the refinement drops on the way up (a literal stays usable wherever its base is),
/// refinements intersect at a join (so `[1, 2]` has element type `Int`) and union at
/// a meet, and the predicate compiles like any other.
///
/// The predicate is built **typed**, not with `Hole`s. Only *node* annotations get
/// their embedded predicates re-inferred (`emit_annotation_predicates`), and
/// this one rides a type made here rather than written by a user, so an untyped
/// predicate would strand unresolved variables at the post-inference wall. Every type
/// involved is known: both sides are the base and the comparison is `Bool`. The inner
/// literal takes [`lit_base`] — refining *it* too would not terminate.
pub fn lit_singleton(lit: &Lit) -> Type {
    match singleton_predicate(lit) {
        Some(predicate) => Type::refined_one(lit_base(lit), Refinement::born(predicate)),
        None => lit_base(lit),
    }
}

/// The bare predicate of `lit`'s singleton — `__elem == lit` — or `None` for
/// `unit`, whose single inhabitant makes a singleton add nothing to its base.
///
/// Split out from [`lit_singleton`] because the term is **ground**: fully typed at
/// construction, closed but for [`crate::ccl::REFINEMENT_BINDER`], and a pure
/// function of `lit`. That is what lets one `Rc` serve every occurrence of a
/// literal value (`InferCtx::lit_singleton`) — nothing about an occurrence can
/// make its singleton resolve differently, because there is nothing left to
/// resolve.
pub(crate) fn singleton_predicate(lit: &Lit) -> Option<Rc<TypedExpr>> {
    if matches!(lit, Lit::Unit) {
        return None;
    }
    let base = lit_base(lit);
    Some(Rc::new(
        TypedExpr::binop(
            TypedExpr::var(Name::elem()).with_ty(base.clone()),
            BinOpKind::Compare(CompareKind::Equals),
            TypedExpr::lit(lit.clone()).with_ty(base.clone()),
        )
        .with_ty(prim(BaseType::Bool)),
    ))
}

/// Test shorthand for an integer literal's *type* — its singleton, `{Int | __elem == n}`.
/// Tests assert the *real* answer rather than the base, since downstream work depends
/// on a literal carrying what it is.
#[cfg(test)]
pub(crate) fn int_lit_ty(n: i64) -> Type {
    lit_singleton(&Lit::Int(n))
}

/// Test shorthand for a string literal's type — see [`int_lit_ty`].
#[cfg(test)]
pub(crate) fn str_lit_ty(s: &str) -> Type {
    lit_singleton(&Lit::String(s.to_string()))
}

/// Test shorthand for a boolean literal's type — see [`int_lit_ty`].
#[cfg(test)]
pub(crate) fn bool_lit_ty(b: bool) -> Type {
    lit_singleton(&Lit::Bool(b))
}

/// Run Cambra's type inference on `expr`.
///
/// Two-pass: emit constraints, then coalesce. Source types come from
/// the public [`crate::ccl::infer::TypeInferenceContext`] and are
/// normalized (holes → fresh vars) up front.
pub(crate) fn run(
    expr: &mut Expr,
    sources: &HashMap<String, Type>,
) -> Result<Type, Vec<LocatedInferError>> {
    // Convert source registry once; reuse across all node emissions.
    let mut sub_ctx = {
        let pre = InferCtx::new(HashMap::new(), expr.node_id());
        let translated: HashMap<String, Type> = sources
            .iter()
            .map(|(k, v)| (k.clone(), pre.normalize_annotation(v)))
            .collect();
        // Seed the blame cursor with the root: every error is stamped with the
        // node whose rule raised it, and the root is the outermost such node.
        InferCtx::new(translated, expr.node_id())
    };

    // Pass 1: emit constraints. The high-value variants
    // (`UnboundVariable`/`TypeMismatch`/`ExpectedFunction`) all originate here.
    // Emission is fail-fast, so there is at most one error; it already carries
    // the node whose rule raised it (`Typing::raise`).
    emit_node(expr, &mut sub_ctx).map_err(|e| vec![e])?;

    // Emission's leftovers. An obligation whose two sides could not be compared
    // during emission — one of them was an unreduced `Type::App`, and reducing it
    // would have read a graph that was still being built — was parked instead of
    // decided. This is the point the parking was for: every edge has been recorded,
    // so reduction is meaningful and each side materializes to an `App`-free type.
    //
    // It runs *before* coalesce so that a violation is reported as an inference
    // diagnostic rather than reaching the `check_pre_desugar` wall, where a plain
    // user type error would be indistinguishable from a compiler bug and panic as
    // one. See `InferCtx::check_parked_obligations`.
    let parked_errors = sub_ctx.check_parked_obligations();
    if !parked_errors.is_empty() {
        return Err(parked_errors);
    }

    // Pass 2: resolve each node's inference variables in place into expr.ty,
    // fill the binder slots that aren't any node's expr.ty (the `Let` binding
    // slot in particular — this subsumed the former `saturate` pass), and
    // monomorphize generalized `let`s in the same walk: a use specializes at
    // first visit, the `let` rebuilds as its per-type specializations (see
    // `coalesce_node`). Refinement predicates are immutable terms, so a
    // specialization clone freshens its predicates as proper substitution
    // instances and a use-site coalesce *rebuilds* a predicate rather than
    // mutating one shared with the definition — occurrences share no mutable
    // state, so nothing needs to be kept in sync across them.
    // Each coalesce error arrives blamed on the node whose frame raised it, so
    // this pass's (potentially several) errors need no post-hoc attribution.
    let errors = coalesce_pass(expr);
    if !errors.is_empty() {
        return Err(errors);
    }
    #[cfg(debug_assertions)]
    // Scope-validity check (design §6.2): every coalesced node's type is
    // well-formed in the lexical scope at that node — every free term-variable
    // of its refinement predicates is bound by an enclosing Pi binder
    // (subtracted by `type_free_vars`) or an enclosing AST binder. This holds at
    // *every* node now that dependent application discharges its binder to the
    // argument at both polarities and `let`-closing discharges bound names as
    // the type leaves their scope. The program's sources are in scope at the root.
    // Debug-only: the uniform substitution traverses type slots in the same
    // pass as the term (no value-only contract), so a type-borne occurrence of
    // a discharged binder is rewritten where it sits and the dangling-binder
    // class this walk guarded is structurally unrepresentable. The walk stays
    // as the debug-build regression net for substitution-descent bugs.
    #[cfg(debug_assertions)]
    {
        let root_scope: std::collections::BTreeSet<Name> = sources.keys().map(Name::from).collect();
        let mut scope_errors = Vec::new();
        check_scope_valid(expr, &root_scope, &mut scope_errors);
        if !scope_errors.is_empty() {
            return Err(scope_errors);
        }
    }
    Ok(expr.ty.clone())
}

use crate::ccl::Expr;

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use crate::ccl::TypedExpr;
    use crate::ccl::infer::TypeInferenceContext;
    use crate::ccl::{Name, TypedExprNode};

    pub(crate) fn lit_int(n: i64) -> TypedExpr {
        TypedExpr::new(TypedExprNode::Lit(Lit::Int(n)))
    }

    pub(crate) fn lit_string(s: &str) -> TypedExpr {
        TypedExpr::new(TypedExprNode::Lit(Lit::String(s.into())))
    }

    pub(crate) fn run_inference(expr: &mut Expr) -> Result<Type, Vec<InferError>> {
        let mut ctx = TypeInferenceContext::new();
        // These tests assert on error payloads, not blame nodes.
        infer(expr, &mut ctx).map_err(LocatedInferError::bare)
    }

    /// `{Int | __elem > rhs}` — a refinement whose bare predicate compares
    /// the implicit element binder ([`crate::ccl::REFINEMENT_BINDER`]) against `rhs`.
    /// Only the debug-only `scope_check_*` tests use it.
    #[cfg(debug_assertions)]
    pub(crate) fn refined_int(rhs: TypedExpr) -> Type {
        use crate::ccl::{BinOpKind, CompareKind, Refinement};
        use std::rc::Rc;
        let pred = TypedExpr::binop(
            TypedExpr::var(Name::elem()),
            BinOpKind::Compare(CompareKind::Greater),
            rhs,
        );
        Type::refined_one(Type::Base(BaseType::Int), Refinement::born(Rc::new(pred)))
    }

    /// Walk `expr`, counting `Let` bindings minted by specialization (their
    /// names carry the `__mono` marker) and the distinct specialization names
    /// that `Var` nodes reference.
    pub(crate) fn specialization_stats(expr: &Expr) -> (usize, std::collections::BTreeSet<Name>) {
        use crate::ccl::names::SyntheticKind;
        fn is_mono(n: &Name) -> bool {
            matches!(
                n,
                Name::Synthetic {
                    kind: SyntheticKind::Mono(_),
                    ..
                }
            )
        }
        fn go(e: &Expr, lets: &mut usize, used: &mut std::collections::BTreeSet<Name>) {
            match &e.node {
                TypedExprNode::Let { binding, .. } if is_mono(&binding.name) => *lets += 1,
                TypedExprNode::Var(v) if is_mono(v) => {
                    used.insert(v.clone());
                }
                _ => {}
            }
            e.walk_children(|c| go(c, lets, used));
        }
        let mut lets = 0;
        let mut used = std::collections::BTreeSet::new();
        go(expr, &mut lets, &mut used);
        (lets, used)
    }

    /// Collect the lambda param types of every monomorphization specialization
    /// (used by the nested-polymorphism test). A `Synthetic` carries no source
    /// base any more, so this no longer filters to the `inner` binding — but
    /// the test's discriminator stands: only `inner` specializes at `Int`
    /// (the `outer` specialization is at `String`), so finding `Int` here
    /// proves `inner` was specialized per-type.
    pub(crate) fn collect_mono_param_types(expr: &Expr) -> Vec<Type> {
        use crate::ccl::names::SyntheticKind;
        fn go(e: &Expr, out: &mut Vec<Type>) {
            if let TypedExprNode::Let {
                binding,
                bound_expr,
                ..
            } = &e.node
                && matches!(
                    binding.name,
                    Name::Synthetic {
                        kind: SyntheticKind::Mono(_),
                        ..
                    }
                )
                && let TypedExprNode::Lambda { param, .. } = &bound_expr.node
            {
                out.push(param.ty.clone());
            }
            e.walk_children(|c| go(c, out));
        }
        let mut out = Vec::new();
        go(expr, &mut out);
        out
    }
}

#[cfg(test)]
mod tests {
    use super::test_helpers::*;
    use super::*;
    use crate::ccl::{TypedBinding, TypedExpr, TypedExprNode};

    #[test]
    fn smoke_lambda_identity_inferred_int() {
        // λx. x applied to 42 → Int
        let lam = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
            },
            body: Box::new(TypedExpr::new(TypedExprNode::Var("x".into()))),
        });
        let app = TypedExpr::new(TypedExprNode::Apply {
            function: Box::new(lam),
            argument: Box::new(lit_int(42)),
        });
        let mut e = app;
        let ty = run_inference(&mut e).expect("inference succeeds");
        assert_eq!(ty, int_lit_ty(42));
    }

    #[test]
    fn smoke_tuple_literal() {
        let mut e = TypedExpr::new(TypedExprNode::Tuple(vec![lit_int(1), lit_string("x")]));
        let ty = run_inference(&mut e).expect("inference succeeds");
        assert_eq!(ty, Type::Tuple(vec![int_lit_ty(1), str_lit_ty("x")]));
    }

    #[test]
    fn smoke_record_literal() {
        let mut e = TypedExpr::new(TypedExprNode::Record(vec![
            ("a".to_string(), lit_int(1)),
            ("b".to_string(), lit_string("x")),
        ]));
        let ty = run_inference(&mut e).expect("inference succeeds");
        assert_eq!(
            ty,
            Type::Record(vec![
                ("a".to_string(), int_lit_ty(1)),
                ("b".to_string(), str_lit_ty("x")),
            ])
        );
    }

    #[test]
    fn smoke_let_monomorphic() {
        // let x = 42 in x → Int
        let mut e = TypedExpr::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
            },
            bound_expr: Box::new(lit_int(42)),
            body: Box::new(TypedExpr::new(TypedExprNode::Var("x".into()))),
        });
        let ty = run_inference(&mut e).expect("inference succeeds");
        assert_eq!(ty, int_lit_ty(42));
    }
}
