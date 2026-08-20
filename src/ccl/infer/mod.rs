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
//! (`Max : ∀α γ. (α → γ) → γ`, etc.). Each scheme is `instantiate`d at every use
//! site, minting fresh vars per use.
//!
//! Arithmetic and comparison have **no** scheme: their requirement is a trait
//! rather than a signature, because a signature could only relate their operands
//! by sharing a variable — see `src/ccl/design/type-inference.md`, "Traits".
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
#[cfg(debug_assertions)]
pub use api::debug_assert_no_free_witness;
pub use api::*;
pub use check::check;
pub use schemes::OperatorSchemes;

use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use crate::ccl::FieldKey;
use crate::ccl::infer::solver::{CoalesceError, ConstrainError, prim};
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
///
/// **No fields → [`BaseType::Unit`]**, via [`Type::tuple`] / [`Type::record`]:
/// the product of zero types is the unit type, and it has exactly one
/// representation (`docs/chl-spec.md`, "6.6 The empty product is unit").
pub(super) fn product(fields: BTreeMap<FieldKey, Type>) -> Type {
    if fields.keys().all(|k| matches!(k, FieldKey::Name(_))) {
        // Empty is all-`Name` vacuously, so this arm also takes the no-field
        // case; `Type::record` maps it to `Unit`.
        Type::record(
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
        Type::tuple(fields.into_values().collect())
    }
}

/// Build a [`Type::Variant`] from a `FieldKey`-keyed tag map.
pub(super) fn variant_type(tags: BTreeMap<FieldKey, Type>) -> Type {
    Type::variant(tags.into_iter().collect())
}

/// The node to blame for a fact about a *place* — given the variables standing at it,
/// the first node, in pre-order, whose own type mentions any of them.
///
/// Several variables because a place is not a variable: the requirements that
/// contradict each other can sit on operator-minted variables no node's type ever
/// names, while the value they constrain is a component of one that is. Each is tried
/// in turn, against the whole tree, and the first that appears anywhere wins — so the
/// result is the earliest *variable* that is named, not the outermost *node* naming
/// any of them. Sharpening that would mean walking the tree once and asking each node
/// about every variable, which buys a better span for a case that already falls back
/// to a coarse one.
///
/// Blame is read *out of the tree* rather than stamped onto the solver structure that
/// raised it. A `NodeId` is provenance, and a copy of one squirrelled away in the
/// solver would be copied onward by every clone that structure makes — outliving the
/// construct it identifies. The tree cannot go stale that way, because it *is* the
/// thing being described.
///
/// Falls back to the root, so a span can be coarse but never wrong — an interior place
/// is exactly the case where that can happen. Only reached on a failure path, so the
/// walk costs nothing in the passing case.
fn blame_node_for_place(
    expr: &Expr,
    uids: &[crate::ccl::InferVarId],
) -> crate::ccl::provenance::NodeId {
    /// Structural only — deliberately does **not** follow a variable's bounds. The
    /// question is which node's type *is written in terms of* this variable, and
    /// chasing bounds would answer a different one (nearly every node, transitively).
    ///
    /// Exhaustive on purpose: a new [`Type`] variant that can hold a type must break
    /// this build rather than silently degrade a span to the program root.
    fn mentions(ty: &Type, uid: crate::ccl::InferVarId) -> bool {
        match ty {
            Type::Infer(v) => v.uid == uid,
            Type::Refinement(inner, _) => mentions(inner, uid),
            // Unlike the solver walks, this one reads *node type slots* and runs
            // before coalesce clears annotations, so a bounded annotation is still
            // in place. Its bound is an ordinary type and can name the variable.
            Type::BoundedHole(bound) => mentions(bound, uid),
            Type::Fun {
                domain, codomain, ..
            } => mentions(domain, uid) || mentions(codomain, uid),
            Type::History { value, domain, .. } => mentions(value, uid) || mentions(domain, uid),
            Type::Tuple(elems) => elems.iter().any(|t| mentions(t, uid)),
            Type::Record(fields) => fields.iter().any(|(_, t)| mentions(t, uid)),
            Type::Variant(arms, _) => arms.iter().any(|(_, t)| mentions(t, uid)),
            // A sum's candidates and body are ordinary types and can name the variable;
            // a witness reference carries identity alone, so there is nothing to read.
            Type::Sigma(s) => {
                s.witness.types().iter().any(|t| mentions(t, uid)) || mentions(&s.body, uid)
            }
            Type::WitnessRef(_) => false,
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::Hole
            | Type::SharedHole(_)
            | Type::DataSource(_)
            | Type::ChanDom(_, _)
            | Type::Txn => false,
        }
    }
    /// The slots that make this node *itself* the place: its own type, an
    /// annotation written on it, a cast's target. Deliberately **not** the
    /// binder slots [`Expr::walk_type_slots`] also visits — a binder's type is
    /// always mirrored either in the node's own type (a lambda's domain is its
    /// type's domain) or in a child's (a `let` binder's type is the
    /// definition's), so a binder slot never reaches a variable the walk would
    /// otherwise miss. It only lets an enclosing node answer for a type its
    /// child owns, which costs the span its precision: with the binder slot
    /// counted, `f = \a -> …` shadows the `\a -> …` that actually carries the
    /// conflicting requirements.
    fn owns(e: &Expr, uid: crate::ccl::InferVarId) -> bool {
        let own = mentions(&e.ty, uid);
        let annotated = e.user_annotation.as_ref().is_some_and(|a| mentions(a, uid));
        let cast = matches!(
            &e.node,
            crate::ccl::TypedExprNode::Cast { target, .. } if mentions(target, uid)
        );
        own || annotated || cast
    }
    fn go(e: &Expr, uid: crate::ccl::InferVarId) -> Option<crate::ccl::provenance::NodeId> {
        if owns(e, uid) {
            return Some(e.node_id());
        }
        let mut found = None;
        e.walk_children(|child| {
            if found.is_none() {
                found = go(child, uid);
            }
        });
        found
    }
    uids.iter()
        .find_map(|uid| go(expr, *uid))
        .unwrap_or_else(|| expr.node_id())
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
        ConstrainError::MissingField { key, in_type } => InferError::MissingField {
            key,
            found: coalesce_for_error(&in_type),
            at: ctx_label.to_string(),
        },
        // `ExtraTag` is `MissingField`'s dual: the width violation is a *tag set*,
        // not a second type, so there is no demand to report and `expected` is
        // `None`. Giving it its own variant — as `MissingField` now has — is the
        // better fix, and is left to whoever next works the variant diagnostics.
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
        ConstrainError::KindMismatch { lhs, rhs } => InferError::TypeMismatch {
            ctx: format!(
                "{ctx_label} (a compute function ⇒ and a data collection ⤇ met \
                 at one position — the two kinds are incomparable, so neither \
                 stands in for the other)"
            ),
            found: Box::new(coalesce_for_error(&lhs)),
            expected: Some(Box::new(coalesce_for_error(&rhs))),
        },
        ConstrainError::NoTraitInstance {
            trait_,
            position,
            found,
            accepted,
        } => InferError::NoTraitInstance {
            trait_: trait_.to_string(),
            position,
            found: Box::new(found),
            accepted: accepted.into_iter().map(Type::Base).collect(),
            at: ctx_label.to_string(),
        },
        ConstrainError::DataDomainMismatch { lhs, rhs } => InferError::TypeMismatch {
            ctx: format!(
                "collection domain conflict at {ctx_label} (a collection's domain is \
                 its data, so a join may not narrow it — two collections over distinct \
                 domains have no common type. Wrap each arm in `box` to keep both \
                 domains: `box(…) if c else box(…)` has the dependent-sum type they \
                 share, and consuming it distributes over the arms)"
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
        // A kinding failure *is* an annotation mismatch: the user wrote a collection
        // kind and the value's domain does not inhabit it. Reported with the same
        // `ctx` a constraint-time collection mismatch uses, because the two differ
        // only in when the shape became known.
        // The *kind* is the demand, rendered as the sum it classifies — the form the
        // annotation was written as — and the resolved domain is what failed it.
        CoalesceError::KindMismatch { resolved, kind } => InferError::TypeMismatch {
            found: resolved,
            expected: Some(Box::new(Type::Sigma(Box::new(
                crate::ccl::ty::SigmaType::over(kind, None, Type::Hole),
            )))),
            ctx: "collection annotation".to_string(),
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
             (two constraints on this collection's domain have no common answer, and \
             narrowing to one would drop rows. If these are the arms of a conditional, \
             wrap each *arm* in `box` to keep both domains — boxing a collection inside an \
             arm and then filtering it leaves the arms over different domains still)",
            ctx_label, details
        )),
        CoalesceError::KindConflict { details } => InferError::Unsupported(format!(
            "one function was required to be both a compute function ⇒ and a data collection ⤇ \
             at {}: {} (the two kinds are incomparable, so no function is both)",
            ctx_label, details
        )),
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
        Some(predicate) => Type::Refinement(Box::new(lit_base(lit)), Refinement::born(predicate)),
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
    // The witness range index's scope is one inference run: see `clear_witness_ctx`.
    solver::clear_witness_ctx();
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

    // The graph is complete here and nothing has been materialized yet — the one
    // point at which eager trait narrowing can be checked against the ground truth
    // it was approximating incrementally. Debug-only, and a pure read of the graph.
    #[cfg(debug_assertions)]
    solver::traits::verify_narrowing_is_complete(|ty| resolve_var_type(ty).ok());

    // Every requirement a definition places on one of its own values is recorded by
    // now, so this is where they can be read *together* — the step narrowing cannot
    // take, since it only ever sees one contribution at a time. Runs before coalesce
    // for two reasons: the tree is still whole, so a conflict can be blamed on a real
    // node, and a generalized definition's variables are still reachable, which after
    // coalesce they are not.
    {
        use solver::traits::{OperandFailure, OperandRequirement};
        /// Render a solver-side requirement for display: bases become types, and the
        /// trait becomes its name, so no message borrows the solver's vocabulary.
        fn stated(r: OperandRequirement) -> StatedRequirement {
            StatedRequirement {
                trait_: r.trait_.to_string(),
                position: r.position,
                accepted: r.accepted.into_iter().map(Type::Base).collect(),
                siblings: r
                    .siblings
                    .into_iter()
                    .map(|(pos, accepted)| (pos, accepted.into_iter().map(Type::Base).collect()))
                    .collect(),
            }
        }
        let mut cache = solver::ConstrainCache::new();
        if let Err(failure) = solver::traits::resolve_operand_requirements(&mut cache) {
            let (blame_vars, error) = match failure {
                OperandFailure::Unsatisfiable { vars, requirements } => (
                    vars,
                    InferError::UnsatisfiableOperand {
                        requirements: requirements.into_iter().map(stated).collect(),
                    },
                ),
                OperandFailure::ContradictsBound {
                    vars,
                    requirements,
                    required,
                    found,
                } => (
                    vars,
                    InferError::RequirementContradictsBound {
                        requirements: requirements.into_iter().map(stated).collect(),
                        required: Box::new(Type::Base(required)),
                        found: Box::new(Type::Base(found)),
                    },
                ),
                // See `OperandFailure::Conflict`: no program is known to reach this,
                // so it takes the generic vocabulary rather than one of its own.
                OperandFailure::Conflict { error } => (
                    Vec::new(),
                    map_constrain_err(error, "a value an operator constrains"),
                ),
            };
            let node_id = blame_node_for_place(expr, &blame_vars);
            return Err(vec![LocatedInferError { error, node_id }]);
        }
    }
    // Sealed *after* the requirement sweep, not before: the sweep itself narrows, and
    // legitimately so. What must not happen is a later pass narrowing a definition's
    // obligation, which would leave the sweep's verdict stale.
    #[cfg(debug_assertions)]
    solver::traits::seal_emission();

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
    // The witness counterpart of the scope check above, and here rather than only at the
    // pipeline's stage boundaries because *this* is where the close happens: a witness
    // that materialization left with no binder is a defect of the pass that just ran, and
    // a caller who only infers (a type-level test, a REPL) is exactly as entitled to catch
    // it as one who goes on to compile.
    #[cfg(debug_assertions)]
    debug_assert_no_free_witness(expr, "post-inference");
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
        Type::Refinement(
            Box::new(Type::Base(BaseType::Int)),
            Refinement::born(Rc::new(pred)),
        )
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
