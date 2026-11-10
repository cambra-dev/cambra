//! Constraint emission, type materialization, and specialization.
//!
//! [`infer`] writes solver types into `expr.ty` and then materializes them.
//! Those slots expose a live bound graph until materialization; specialization
//! can add bounds during the coalesce walk. For pass order and failure behavior,
//! see `src/ccl/design/type-inference.md`, "2. The Inference Pipeline".
//!
//! [`should_generalize`](context::should_generalize) selects generalized lets;
//! [`specialize_use`](solve::specialize_use) resolves their uses for later passes.
//! Eligibility and clone ownership are specified in `src/ccl/design/type-inference.md`,
//! "3.1 Let-Polymorphism is Freshening (Instantiation)".
//! Clone reuse does not imply runtime sharing; see
//! `src/ccl/design/type-inference.md`, "Key timing and precision limits".
//!
//! # Operator types
//!
//! [`OperatorSchemes`] supplies polymorphic schemes for registered operators and
//! projection cases. Uses instantiate those schemes independently. Arithmetic and
//! comparison use trait requirements instead; see `src/ccl/design/type-inference.md`,
//! "Traits".
//!
//! Builtins introduced after inference carry stamped types. Registered polymorphic
//! builtins that reach inference, including `FinalOrDefault`, use instantiated
//! schemes.

mod api;
mod check;
mod context;
mod emit;
mod schemes;
pub(crate) mod solve;
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
pub use check::{CheckMode, check};
pub use schemes::OperatorSchemes;

/// A type parameter of a module checked on its own, and how the check holds it
/// (`docs/modules.md`, "Checking a module on its own").
#[derive(Debug, Clone)]
pub enum ModuleCheckParam {
    /// `T` with no kind written: one inference variable for the whole module,
    /// which its uses bound.
    Inferred(Rc<crate::ccl::ty::TypeParam>),
    /// `T <: B`, or an abstract type member of a Module type: opaque, known only
    /// through its bound, if it has one.
    Opaque {
        param: Rc<crate::ccl::ty::TypeParam>,
        bound: Option<Type>,
    },
}

impl ModuleCheckParam {
    /// The declared parameter the module writes.
    pub fn param(&self) -> &Rc<crate::ccl::ty::TypeParam> {
        match self {
            ModuleCheckParam::Inferred(param) | ModuleCheckParam::Opaque { param, .. } => param,
        }
    }
}

use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

use crate::ccl::FieldKey;
use crate::ccl::infer::solver::{CoalesceError, ConstrainError, prim};
use crate::ccl::{BaseType, BinOpKind, CompareKind, Lit, Refinement, Type, TypedExpr};

use context::InferCtx;
use emit::emit_node;
use solve::{coalesce_pass, push_barrier_failures, resolve_var_type};
use solver::smt::SmtError;

// `Name` is no longer debug-only: `lit_singleton` builds its predicate over the
// refinement binder in every build.
use crate::ccl::Name;
use crate::ccl::provenance::NodeId;
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
                    FieldKey::Name(n) => (n, t),
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

/// The first node whose type names a variable of a failing operand place.
/// Equivalent requirement copies are grouped before this walk, so an arena-only copy
/// contributes the live variables of the same conflict. An attribution miss reports at
/// the root and leaves no statement out of recovery, since the root may be unrelated.
fn blame_node_for_place(expr: &Expr, uids: &[crate::ccl::InferVarId]) -> Option<NodeId> {
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
            Type::History { function, .. } => mentions(function, uid),
            Type::Tuple(elems) | Type::OpenTuple(elems) | Type::Nominal(_, elems) => {
                elems.iter().any(|t| mentions(t, uid))
            }
            Type::Split { input, output } => mentions(input, uid) || mentions(output, uid),
            Type::DepTuple(cs) => cs.iter().any(|(_, t)| mentions(t, uid)),
            Type::Family { binders, body } => {
                binders.iter().any(|(_, t)| mentions(t, uid)) || mentions(body, uid)
            }
            Type::Record(fields) => fields.iter().any(|(_, t)| mentions(t, uid)),
            Type::Variant(arms, _) => arms.iter().any(|(_, t)| mentions(t, uid)),
            Type::WitnessRef(_) | Type::WitnessProjection(_) | Type::FamilyApp(_) => false,
            Type::Base(_)
            | Type::UIntRange(_)
            | Type::Hole
            | Type::BarrierVar(_)
            | Type::SharedHole(_)
            | Type::DataSource(_)
            | Type::ChanDom(_, _)
            | Type::Param(_)
            | Type::Txn => false,
            Type::Poly(poly) => poly.types().any(|t| mentions(t, uid)),
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
    fn go(e: &Expr, uid: crate::ccl::InferVarId) -> Option<NodeId> {
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
    let node = uids.iter().find_map(|uid| go(expr, *uid));
    debug_assert!(
        node.is_some(),
        "a failing operand place is named by the emitted tree after equivalent copies are grouped",
    );
    node
}

/// `error`, a loop's refusal located at its source, moved to where the source is written:
/// lowering binds a loop's source to a name the loop walks, and the binding holds the
/// expression the program wrote.
fn at_written_source(expr: &Expr, mut error: LocatedInferError) -> LocatedInferError {
    fn bound_at(e: &Expr, name: &Name) -> Option<NodeId> {
        if let crate::ccl::TypedExprNode::Let {
            binding,
            bound_expr,
            ..
        } = &e.node
            && binding.name == *name
        {
            // The source's operands are bound before it, so the expression is the tail.
            let mut tail: &Expr = bound_expr;
            while let crate::ccl::TypedExprNode::Let { body, .. } = &tail.node {
                tail = body;
            }
            return Some(tail.node_id());
        }
        let mut found = None;
        e.walk_children(|c| {
            if found.is_none() {
                found = bound_at(c, name);
            }
        });
        found
    }
    if let Some(crate::ccl::TypedExprNode::Var(name)) =
        find_node(expr, error.node_id).map(|e| &e.node)
        && let Some(bound) = bound_at(expr, name)
    {
        error.node_id = bound;
    }
    error
}

/// The node of `expr` whose id is `id`.
fn find_node(expr: &Expr, id: NodeId) -> Option<&Expr> {
    if expr.node_id() == id {
        return Some(expr);
    }
    let mut found = None;
    expr.walk_children(|child| {
        if found.is_none() {
            found = find_node(child, id);
        }
    });
    found
}

/// Why two functions' kinds do not relate, read off what each side's kind settled to.
fn kind_mismatch_reason(lhs: &Type, rhs: &Type) -> &'static str {
    use crate::ccl::ty::KindPin;
    let pin = |t: &Type| t.peel_refinements().fun_kind_of().map(|k| k.resolved());
    match (pin(lhs), pin(rhs)) {
        (Some(KindPin::Sum(_)), Some(KindPin::Plain)) => {
            "a sum reached a plain collection — a sum's domain is its witness, which no written \
             domain names; an annotation admits a sum with the domain `_`, as in `_ |=> V`, or \
             as `Collection(V)`"
        }
        (Some(KindPin::Plain), Some(KindPin::Sum(_))) => {
            "a plain collection reached a sum — a collection becomes a sum only through `box`"
        }
        (Some(KindPin::Sum(a)), Some(KindPin::Sum(b))) if a != b => {
            "two sums over different numbers of witnesses met at one position"
        }
        _ => {
            "a compute function ⇒ and a data collection ⤇ met at one position — the two \
             kinds are incomparable, so neither stands in for the other"
        }
    }
}
/// Resolve a (possibly variable-laden) [`Type`] to a concrete type for use
/// in error messages. Falls back to [`Type::Hole`] if coalesce fails (which
/// can happen for types with incompatible bounds that triggered the error).
///
/// The types inside its refinement predicates are resolved too, here rather than
/// when the message is written: the variables' bounds are gone by then, and the
/// message reads them (`chl_print` writes a read of a collection as `xs[i]!` and a
/// call as `f(x)`, which only the callee's type tells apart).
pub(super) fn coalesce_for_error(ty: &Type) -> Type {
    let mut resolved = resolve_var_type(ty).unwrap_or(Type::Hole);
    resolve_predicate_types(&mut resolved);
    respell_tuple_binders(&mut resolved);
    resolved
}

/// Write each dependent tuple in `ty` with the component names a reader can use: a component
/// no later one reads is unnamed, as a plain tuple's are, and a name the compiler minted that a
/// later component reads, as `uncurry`'s scheme names its keys, is respelled `k`, numbered where
/// the type already holds that spelling (the spelling `chl_print` gives a minted key binder).
fn respell_tuple_binders(ty: &mut Type) {
    let mut taken: HashSet<String> = crate::ccl::subst::type_free_vars(ty)
        .iter()
        .map(|n| n.base().to_string())
        .collect();
    respell_in(ty, &mut taken);

    fn respell_in(ty: &mut Type, taken: &mut HashSet<String>) {
        ty.walk_children_mut(|child| respell_in(child, taken));
        let Type::DepTuple(components) = ty else {
            return;
        };
        // Open every component at a placeholder per earlier component, so a later component
        // reads an earlier one by a name whether it was open or closed.
        let placeholders: Vec<Name> = (0..components.len())
            .map(|_| Name::fresh("__respelled"))
            .collect();
        let mut opened = crate::ccl::subst::open_tuple_components(components, |j, _| {
            crate::ccl::subst::Mapping::Rename(placeholders[j].clone())
        });
        let mut names: Vec<Option<Name>> = Vec::with_capacity(components.len());
        for i in 0..components.len() {
            let own = components[i].0.clone();
            let read = opened[i + 1..].iter().any(|t| {
                let free = crate::ccl::subst::type_free_vars(t);
                free.contains(&placeholders[i]) || own.as_ref().is_some_and(|n| free.contains(n))
            });
            let name = match own {
                _ if !read => None,
                Some(n) if !n.base().starts_with("__") => Some(n),
                _ => {
                    let spelling = std::iter::once("k".to_string())
                        .chain((1..).map(|i| format!("k{i}")))
                        .find(|s| !taken.contains(s))
                        .expect("an unbounded sequence of spellings has one not taken");
                    taken.insert(spelling.clone());
                    Some(Name::from(spelling.as_str()))
                }
            };
            if let Some(to) = &name {
                let renames = std::iter::once(&placeholders[i])
                    .chain(components[i].0.as_ref())
                    .filter(|from| *from != to);
                for from in renames {
                    let rename = crate::ccl::subst::Subst::rename(from.clone(), to.clone());
                    for later in &mut opened[i + 1..] {
                        *later = rename.apply_type(later);
                    }
                }
            }
            names.push(name);
        }
        *components = names.into_iter().zip(opened).collect();
    }
}

/// Resolve every node type inside `ty`'s refinement predicates, on a copy of each
/// predicate: the copy is for a message, so nothing shares it. See
/// [`coalesce_for_error`] for why a message's types are resolved when it is raised.
pub(super) fn resolve_predicate_types(ty: &mut Type) {
    fn resolve_expr(e: &mut TypedExpr) {
        // A collection's `elements` call is the identity, which coalescing drops; the message
        // reads the collection as the program spells it.
        while let Some(collection) = solve::elements_of_a_collection(e) {
            *e = collection;
        }
        if let Ok(resolved) = resolve_var_type(&e.ty) {
            e.ty = resolved;
        }
        resolve_predicate_types(&mut e.ty);
        e.walk_children_mut(resolve_expr);
    }
    match ty {
        Type::Refinement(_, refinements) => {
            refinements.rewrite_each(|_, r| {
                let _frame = crate::ccl::provenance::copy_frame("infer.error_predicate_types");
                let mut predicate = (*r.predicate).clone();
                resolve_expr(&mut predicate);
                *r = Refinement::born(Rc::new(predicate));
            });
        }
        // A projection quotes the sum it reads, which a loop source reads through its
        // `elements` call.
        Type::WitnessProjection(p) => {
            let _frame = crate::ccl::provenance::copy_frame("infer.error_predicate_types");
            let mut term = (*p.term).clone();
            resolve_expr(&mut term);
            *p = crate::ccl::ty::WitnessProjection::new(Rc::new(term), p.position);
        }
        _ => {}
    }
    ty.walk_children_mut(resolve_predicate_types);
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
            if matches!(*rhs, Type::Fun { .. }) && !matches!(*lhs, Type::Fun { .. }) {
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
            found: Box::new(coalesce_for_error(&in_type)),
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
            ctx: format!("{ctx_label} ({})", kind_mismatch_reason(&lhs, &rhs)),
            found: Box::new(coalesce_for_error(&lhs)),
            expected: Some(Box::new(coalesce_for_error(&rhs))),
        },
        ConstrainError::ParamReadsBinder { chosen, binder } => {
            let binder = binder.source_spelling().map(str::to_string);
            match chosen {
                crate::ccl::infer_var::StandsFor::Param(param) => InferError::ParamReadsBinder {
                    param: param.to_string(),
                    binder,
                },
                crate::ccl::infer_var::StandsFor::ConstantFamily(param) => {
                    InferError::ConstantFamilyReadsBinder {
                        param: param.to_string(),
                        binder,
                    }
                }
            }
        }
        ConstrainError::TypeParamEscapes { param } => InferError::TypeParamEscapes {
            param: param.spelling.to_string(),
            target: None,
            at: ctx_label.to_string(),
        },
        // A method called on a value of a type parameter's type, which has no methods.
        ConstrainError::MissingRequirement { trait_, param, .. } if trait_.is_method() => {
            InferError::UnresolvedMethod {
                method: trait_.name().to_string(),
                receiver: Some(Type::Param(param)),
            }
        }
        ConstrainError::MissingRequirement {
            trait_,
            position,
            param,
        } => InferError::MissingRequirement {
            trait_: trait_.to_string(),
            position,
            param: param.spelling.to_string(),
            at: ctx_label.to_string(),
        },
        // What a method's receiver turned out to be: a type with no method of the name, or
        // one that is not nominal.
        ConstrainError::NoTraitInstance { trait_, found, .. } if trait_.is_method() => {
            InferError::UnresolvedMethod {
                method: trait_.name().to_string(),
                receiver: Some(found),
            }
        }
        ConstrainError::MethodCall(error) => *error,
        ConstrainError::NoTraitInstance {
            trait_,
            position,
            found,
            accepted,
            ..
        } => InferError::NoTraitInstance {
            trait_: trait_.to_string(),
            position,
            found: Box::new(found),
            accepted,
            at: ctx_label.to_string(),
        },
        // Reported with the same `ctx` a coalesce-time kinding failure uses: the two
        // differ only in when the type side became known.
        ConstrainError::NotOfKind { found, type_kind } => InferError::TypeMismatch {
            found: Box::new(coalesce_for_error(&found)),
            expected: Some(Box::new(Type::sum_over(type_kind, None, Type::Hole))),
            ctx: "collection annotation".to_string(),
        },
        // A **demand**: `rhs` is the domain a declaration or parameter requires and `lhs`
        // is what was supplied, so this is the ordinary expected/found sentence. No `box`
        // advice — nothing is being joined here, and boxing the value would change what it
        // is rather than reconcile two arms. No `ctx_label` either: the report's span
        // underlines the expression already, so rendering it again says the same thing
        // twice, once in source and once in CCL.
        ConstrainError::NotCompiledYet(what) => {
            InferError::Unsupported(format!("{what} is not compiled yet"))
        }
        ConstrainError::NoJoinOverBinder {
            binders,
            refinement,
        } => InferError::NoJoinOverBinder {
            binders,
            reads: Vec::new(),
            predicate: refinement.predicate,
            position: solver::compact::JoinedPosition::Keys,
            fed_elsewhere: false,
        },
        ConstrainError::DataDomainMismatch { lhs, rhs, cause } => {
            // A side whose bounds do not coalesce holds the conflict itself: two domains reached
            // one of its variables, and the comparison only exposed them. The report is that
            // conflict, since the side would otherwise render as `_`.
            if let Some(conflict) = [&lhs, &rhs]
                .into_iter()
                .find_map(|t| resolve_var_type(t).err())
            {
                return map_coalesce_err(conflict, ctx_label);
            }
            let (found, expected) = (coalesce_for_error(&lhs), coalesce_for_error(&rhs));
            // Where the two render alike, the report is the sub-comparison that found
            // them unequal ([`ConstrainError::DataDomainMismatch`]'s `cause`, whose doc
            // says why it is carried): its own sides differ structurally, so
            // [`identical_rendering_hint`] can quote the divergence.
            if crate::ccl::chl_print::renders_alike(&found, &expected) {
                return map_constrain_err(*cause, ctx_label);
            }
            InferError::TypeMismatch {
                ctx: "collection domain (a collection's domain is its data, so it is \
                      invariant — a collection over one domain does not stand in for a \
                      collection over another)"
                    .to_string(),
                found: Box::new(found),
                expected: Some(Box::new(expected)),
            }
        }
        // A **join**, and the same fact the coalesce-time face reports. Converted to the
        // same `InferError` so the message follows the situation rather than which phase
        // noticed it.
        ConstrainError::DomainJoinConflict { domains } => InferError::DomainJoinConflict {
            domains: domains.iter().map(coalesce_for_error).collect(),
            origin: ctx_label.to_string(),
        },
        // TODO(smt-undecided): every arm below aborts the compiler, which is a
        // prototype tripwire rather than the policy. The policy this wants is the
        // one `constrain`'s deficit rule already applies to a predicate the
        // encoder cannot read — an undecided query is a structural mismatch —
        // extended to `unknown`, which z3 answers for reasons outside this
        // encoder's control, and to `SolverError`, which the variant's own doc
        // calls a misencoding on this side and which
        // `smt::tests::the_solver_will_error_on_type_errors` reaches from a
        // well-formed query. A solver that will not start stays a hard failure
        // under any policy: it is a fact about the machine, not about the program.
        ConstrainError::SmtError { lhs, rhs, error } => match error.as_ref() {
            // `constrain` decides an unreadable predicate as a mismatch, so the
            // variant reaches no caller.
            SmtError::Encoding { .. } => {
                unreachable!("an Encoding failure is decided at the deficit rule: {error}")
            }
            // Names no types: which comparison raised the query says nothing about
            // a solver that is not there.
            SmtError::Process { .. } => panic!("{error}"),
            SmtError::SolverReportedUnknown | SmtError::SolverError { .. } => {
                panic!("could not compare {lhs} <: {rhs}: {error}")
            }
        },
    }
}

/// Map a [`CoalesceError`] onto the public [`InferError`] enum.
pub(super) fn map_coalesce_err(err: CoalesceError, ctx_label: &str) -> InferError {
    match err {
        CoalesceError::IncompatibleBounds {
            polarity, details, ..
        } => InferError::IncompatibleBounds {
            polarity,
            conflicting: details,
            origin: ctx_label.to_string(),
        },
        CoalesceError::TupleWidthConflict { widths, .. } => InferError::TupleWidthConflict {
            widths,
            origin: ctx_label.to_string(),
        },
        // A kinding failure *is* an annotation mismatch: the user wrote a collection
        // kind and the value's domain does not inhabit it. Reported with the same
        // `ctx` a constraint-time collection mismatch uses, because the two differ
        // only in when the shape became known.
        // The *kind* is the demand, rendered as the sum it classifies — the form the
        // annotation was written as — and the resolved domain is what failed it.
        CoalesceError::KindMismatch {
            resolved,
            type_kind,
        } => InferError::TypeMismatch {
            found: resolved,
            expected: Some(Box::new(Type::sum_over(type_kind, None, Type::Hole))),
            ctx: "collection annotation".to_string(),
        },
        CoalesceError::UnresolvedPartial { details, .. } => InferError::UnresolvedPartial {
            keys: details,
            at: ctx_label.to_string(),
        },
        CoalesceError::RecursiveType { details } => InferError::Unsupported(format!(
            "recursive type: {details} (residual μ-types are forbidden)"
        )),
        CoalesceError::DomainJoinConflict { domains, .. } => InferError::DomainJoinConflict {
            domains,
            origin: ctx_label.to_string(),
        },
        CoalesceError::NoJoinOverBinder {
            binders,
            refinement,
            position,
        } => InferError::NoJoinOverBinder {
            binders,
            reads: Vec::new(),
            predicate: refinement.predicate,
            position,
            fed_elsewhere: false,
        },
        // The same violation `check_scope_valid` reports post-inference, caught where it is
        // made: a materialized type carrying a witness reference no binder covers. A
        // compiler bug in whatever built the position, like `KindConflict` below.
        CoalesceError::WitnessScope { details } => InferError::Unsupported(format!(
            "a witness reference escaped its binder: {details} (a \
             `WitnessRef` denotes \"whichever domain\", so outside its sum it denotes nothing)"
        )),
        CoalesceError::KindConflict { details, .. } => InferError::Unsupported(format!(
            "one function was required to be both a compute function ⇒ and a data collection ⤇: \
             {details} (the two kinds are incomparable, so no function is both)"
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
/// what a proof obligation needs: `a[0]!` can only discharge against `Array(3, 𝑇)`'s
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
    lit_singleton(&Lit::String(s.into()))
}

/// Test shorthand for a boolean literal's type — see [`int_lit_ty`].
#[cfg(test)]
pub(crate) fn bool_lit_ty(b: bool) -> Type {
    lit_singleton(&Lit::Bool(b))
}

/// The type the `Case` rule gives a `Case` built after inference whose arms have the types
/// `arms`: a fresh result variable with every arm's type as a lower bound, resolved
/// (`emit_case`). Record width, variant tags, and refinements join as they do for a `Case`
/// inference types.
///
/// Each arm is closed over the bindings local to it, so an arm type reads only names bound
/// around the `Case`. The variable's telescope is those names, which is the part of the
/// enclosing scope the bounds can mention.
pub(crate) fn case_result_ty<'a>(
    arms: impl IntoIterator<Item = &'a Type>,
) -> Result<Type, InferError> {
    let arms: Vec<&Type> = arms.into_iter().collect();
    let mut telescope = crate::ccl::infer_var::Telescope::empty();
    for name in arms
        .iter()
        .flat_map(|ty| crate::ccl::subst::type_free_vars(ty))
        .collect::<std::collections::BTreeSet<_>>()
    {
        telescope = telescope.extended(name);
    }
    let result = Type::Infer(crate::ccl::InferVar::fresh_in(0, &telescope));
    let mut cache = solver::ConstrainCache::for_derivation(solver::Derivation::PostPass);
    for arm in arms {
        solver::constrain_subtype_in(arm, &result, &mut cache, &solver::smt::NoScope)
            .map_err(|e| map_constrain_err(e, "Case arm"))?;
    }
    resolve_var_type(&result).map_err(|e| map_coalesce_err(e, "Case arm"))
}

/// Run Cambra's type inference on `expr`.
///
/// Two-pass: emit constraints, then coalesce. Source types come from
/// the public [`crate::ccl::infer::TypeInferenceContext`] and are
/// normalized (holes → fresh vars) up front.
pub(crate) fn run(
    arena: &mut InferArena,
    expr: &mut Expr,
    sources: &HashMap<String, Type>,
    instances: &Rc<solver::traits::InstanceTable>,
    public: &HashSet<Name>,
    marks: &HashMap<NodeId, crate::ccl::lower::Mark>,
) -> Result<(Type, Vec<LocatedInferError>), Vec<LocatedInferError>> {
    let outcome = run_with_params(
        arena,
        expr,
        sources,
        instances,
        &[],
        &HashSet::new(),
        public,
        marks,
        false,
    );
    match outcome.typed {
        Some(inferred) if outcome.errors.is_empty() => Ok((inferred.ty, inferred.inert)),
        _ => Err(outcome.errors),
    }
}

/// An error for each capability variable's upper bound that its capabilities exceed, at the node where
/// the first capability beyond it entered, with the clause or the written type as the secondary
/// label.
/// `beyond_clause` spells a capability a clause does not list ([`InferCtx::item_beyond_clause`]).
fn push_capability_failures(
    errors: &mut Vec<LocatedInferError>,
    expr: &Expr,
    beyond_clause: &dyn Fn(&crate::ccl::capabilities::Capability, chl_parser::ast::Span) -> String,
) {
    use crate::ccl::capabilities::Blame;
    use crate::ccl::infer_var::Origin;
    // Each use of a polymorphic definition checks its own copy of the definition's bounds,
    // and the copies name the definition's nodes, so one failure is reported once.
    let mut reported = HashSet::new();
    for failure in crate::ccl::capabilities::exceeded_uppers() {
        let item = match failure.blame {
            Blame::Clause(at) => beyond_clause(&failure.capability.item, at),
            _ => failure.capability.item.to_string(),
        };
        if !reported.insert((failure.capability.at, item.clone(), failure.blame)) {
            continue;
        }
        // A compiler trait's signature is written nowhere, so it labels nothing.
        let (error, written) = match failure.blame {
            Blame::Clause(at) => (InferError::CapabilityBeyondClause { item }, Some(at)),
            Blame::Signature(at) => (
                InferError::CapabilityBeyondSignature {
                    item,
                    compiler: at.is_none(),
                },
                at,
            ),
            // Through a polymorphic definition, the use passing what commits is at fault: the
            // error is there, with the commit inside the definition and the block beside it.
            Blame::NestedTransaction { block, used_at } => {
                let committed = failure.capability.at;
                let top = match &failure.capability.item {
                    crate::ccl::capabilities::Capability::Every(_) => {
                        Some(failure.capability.item.to_string())
                    }
                    _ => None,
                };
                let mut error = LocatedInferError::new(
                    InferError::NestedTransaction {
                        through_use: used_at.is_some(),
                        top,
                    },
                    used_at.or(committed).unwrap_or_else(|| expr.node_id()),
                );
                if used_at.is_some()
                    && let Some(committed) = committed
                {
                    error.related.set(Related {
                        origin: Origin::Node(committed),
                        role: RelatedRole::Commit,
                    });
                }
                error.related.set(Related {
                    origin: Origin::Node(block),
                    role: RelatedRole::Block,
                });
                errors.push(error);
                continue;
            }
            Blame::Written(at) => (InferError::CapabilityNotStated { item }, Some(at)),
            Blame::Bound(at) => (InferError::CapabilityBeyondBound { item }, Some(at)),
        };
        errors.push(
            LocatedInferError {
                error,
                node_id: failure.capability.at.unwrap_or_else(|| expr.node_id()),
                also: Box::default(),
                related: RelatedPositions::default(),
            }
            .with_failure((None, written.map(Origin::Written))),
        );
    }
}

/// The scheme each generalized binding a module check reports was bound at.
pub(crate) type NotedSchemes = Vec<(Name, solver::display::InferredPoly)>;

/// The variable each [`ModuleCheckParam::Inferred`] parameter is opened as, with the
/// parameter.
pub(crate) type OpenedVars = HashMap<crate::ccl::InferVarId, Rc<crate::ccl::ty::TypeParam>>;

/// A run's errors and the result of its last successful recovery run.
pub(crate) struct RunOutcome {
    /// The tree before emission, at the identities earlier errors can still name.
    pub before: Expr,
    pub typed: Option<Inferred>,
    pub errors: Vec<LocatedInferError>,
    pub recovered: HashMap<NodeId, StandIn>,
    pub unavailable: HashSet<Name>,
}

/// [`run`] with a module's type parameters `params` open throughout `expr`, returning what it
/// infers ([`Inferred`]): besides the type, the scheme each generalized binding in `reported` is
/// bound at ([`typing::Typing::note_scheme`]), the variable each parameter with no kind written is
/// opened as, what the top level requires and causes, and the expression statements that cause
/// nothing.
///
/// A run whose emission recovered from a statement stops after emission, and inference
/// starts over in `arena`, restarted, on a copy of `expr` as it was, with the expression of
/// each statement recovered from replaced by the [`Error`](crate::ccl::TypedExprNode::Error)
/// stand-in. A run the barrier check or the requirement sweep stops starts over the same
/// way, without the statements enclosing their failures ([`context::InferCtx::failure`]). The
/// statements left in are then solved over a graph holding exactly their constraints, and
/// what that run reports is added, but for a value it leaves undetermined
/// ([`InferError::is_undetermined`]): the missing statements' constraints may be what
/// determines it. Each run that stops so again starts over the same way. See
/// `src/ccl/design/type-inference.md`, "An error stops its statement, not the pass".
///
/// Module checks set `recover_all`: failures after coalescing also omit their statements,
/// and the last successful run supplies partial contracts. Its tree replaces `expr`, while
/// errors from earlier runs remain reported. A failed function retains its declared
/// parameters and result for checking its callers.
#[expect(
    clippy::too_many_arguments,
    reason = "the module check's inputs, each read by every run, and the recovery switch"
)]
pub(crate) fn run_with_params(
    arena: &mut InferArena,
    expr: &mut Expr,
    sources: &HashMap<String, Type>,
    instances: &Rc<solver::traits::InstanceTable>,
    params: &[ModuleCheckParam],
    reported: &HashSet<Name>,
    public: &HashSet<Name>,
    marks: &HashMap<NodeId, crate::ccl::lower::Mark>,
    recover_all: bool,
) -> RunOutcome {
    // Emission rewrites the tree it types, so a run that starts over needs it as it was: a
    // snapshot, at the same identities, since the statements recovered from are named by
    // node. Neither copy joins the tree `expr` is.
    let pristine = expr.clone_preserving_ids();
    let mut unavailable = if recover_all {
        unavailable_contracts(&pristine)
    } else {
        HashSet::new()
    };
    let RunFailure {
        mut errors,
        mut recovered,
    } = match run_once(expr, sources, instances, params, reported, public, marks) {
        Ok(typed) => {
            return RunOutcome {
                before: pristine,
                typed: Some(typed),
                errors: Vec::new(),
                recovered: HashMap::new(),
                unavailable,
            };
        }
        Err(failure) => failure,
    };
    // A tree lowering failed in holds statements left out already, which may be what
    // determines a value, as a run that starts over does.
    if holds_stand_in(&pristine) {
        errors.retain(|e| !e.error.is_undetermined());
    }
    let mut stood_in: HashMap<NodeId, StandIn> = HashMap::new();
    let mut typed = None;
    if recover_all && recovered.is_empty() {
        recovered = failed_after_coalesce(&pristine, errors.clone()).recovered;
    }
    loop {
        // A statement recovered from stands in; one that is recovered from as a stand-in
        // stands in bare. Each statement goes the two steps at most, so this ends.
        let mut changed = false;
        for node in recovered {
            let next = match stood_in.get(&node) {
                None => StandIn::Expression,
                Some(StandIn::Expression) => StandIn::Bare,
                Some(StandIn::Bare) => continue,
            };
            stood_in.insert(node, next);
            changed = true;
        }
        if !changed {
            break;
        }
        arena.restart();
        let mut rest = pristine.clone_preserving_ids();
        stand_in_for_recovered(&mut rest, &stood_in, recover_all);
        if recover_all {
            unavailable = unavailable_contracts(&rest);
        }
        let failure = match run_once(
            &mut rest, sources, instances, params, reported, public, marks,
        ) {
            Ok(found) => {
                typed = Some(found);
                if recover_all {
                    *expr = rest;
                }
                break;
            }
            Err(failure) => failure,
        };
        // Restart copies preserve node identities. Equal messages at different nodes can
        // report independent defects, so only a repeat at the same node is dropped.
        recovered = if recover_all && failure.recovered.is_empty() {
            failed_after_coalesce(&pristine, failure.errors.clone()).recovered
        } else {
            failure.recovered
        };
        for error in failure.errors {
            if !error.error.is_undetermined()
                && !errors.iter().any(|said| {
                    said.node_id == error.node_id && said.error.same_defect(&error.error)
                })
            {
                errors.push(error);
            }
        }
    }
    drop_met_downstream(&pristine, &mut errors);
    RunOutcome {
        before: pristine,
        typed,
        errors,
        recovered: stood_in,
        unavailable,
    }
}

/// Bindings whose recovered definitions establish no complete contract. An unconstrained
/// result of an omitted body is a poison for diagnosis, not a polymorphic export.
fn unavailable_contracts(tree: &Expr) -> HashSet<Name> {
    fn complete(ty: &Type) -> bool {
        !ty.holds_type(&|ty| {
            matches!(
                ty,
                Type::Hole
                    | Type::Infer(_)
                    | Type::BarrierVar(_)
                    | Type::SharedHole(_)
                    | Type::BoundedHole(_)
            )
        })
    }
    fn declared_reads(expr: &Expr) -> Option<std::collections::BTreeSet<Name>> {
        match &expr.node {
            crate::ccl::TypedExprNode::Lambda { param, body } => {
                let annotation = param.annotation_ty().unwrap_or(&param.ty);
                if !complete(annotation) {
                    return None;
                }
                let mut reads = declared_reads(body)?;
                reads.extend(crate::ccl::subst::type_free_vars(annotation));
                reads.remove(&param.name);
                Some(reads)
            }
            crate::ccl::TypedExprNode::Let { binding, .. }
                if crate::ccl::opaque_output::is_annotated_result(expr) =>
            {
                binding
                    .annotation_ty()
                    .filter(|ty| complete(ty))
                    .map(crate::ccl::subst::type_free_vars)
            }
            _ => None,
        }
    }
    fn walk(
        tree: &Expr,
        out: &mut HashSet<Name>,
        dependencies: &mut Vec<(Name, std::collections::BTreeSet<Name>)>,
    ) {
        if let crate::ccl::TypedExprNode::Let {
            binding,
            bound_expr,
            ..
        } = &tree.node
        {
            let declared = binding
                .annotation_ty()
                .filter(|ty| complete(ty))
                .map(crate::ccl::subst::type_free_vars)
                .or_else(|| declared_reads(bound_expr));
            if holds_stand_in(bound_expr) && declared.is_none() {
                out.insert(binding.name.clone());
            }
            // A complete declaration depends on its own types, independently of the body.
            // Partial declarations remain on the recovered tree for checking callers;
            // their missing parts do not establish an inferred export contract.
            let mut reads =
                declared.unwrap_or_else(|| crate::ccl::ccl_utils::free_names(bound_expr));
            if let Some(annotation) = binding.annotation_ty() {
                reads.extend(crate::ccl::subst::type_free_vars(annotation));
            }
            dependencies.push((binding.name.clone(), reads));
        }
        tree.walk_children(|child| walk(child, out, dependencies));
    }
    let mut out = HashSet::new();
    let mut dependencies = Vec::new();
    walk(tree, &mut out, &mut dependencies);
    loop {
        let before = out.len();
        for (name, reads) in &dependencies {
            if reads.iter().any(|read| out.contains(read)) {
                out.insert(name.clone());
            }
        }
        if out.len() == before {
            return out;
        }
    }
}

/// Drop each error whose value came from inside a join already reported as having no common
/// type (`src/ccl/design/diagnostics.md`, "One report per defect"): `x + 1` over the
/// elements of `[1, "a"]` fails at `"a"` because the list joins `Int` and `String`, and fixing
/// the list fixes both. The join is the defect, and the error is it met downstream.
fn drop_met_downstream(tree: &Expr, errors: &mut Vec<LocatedInferError>) {
    fn find(e: &Expr, node: NodeId) -> Option<&Expr> {
        if e.node_id() == node {
            return Some(e);
        }
        let mut found = None;
        e.walk_children(|c| {
            if found.is_none() {
                found = find(c, node);
            }
        });
        found
    }
    fn collect(e: &Expr, out: &mut HashSet<NodeId>) {
        use crate::ccl::TypedExprNode;
        // A statement's type is its continuation's value. A failure at the statement
        // therefore identifies neither its initializer nor later statements as join
        // contributors. The expression forming the join supplies its own report.
        if matches!(
            e.node,
            TypedExprNode::Let { .. }
                | TypedExprNode::MutDecl { .. }
                | TypedExprNode::ExprStmt { .. }
                | TypedExprNode::DefGroup { .. }
        ) {
            return;
        }
        out.insert(e.node_id());
        e.walk_children(|child| collect(child, out));
    }

    let mut joined: HashSet<NodeId> = HashSet::new();
    for error in errors.iter() {
        if let InferError::IncompatibleBounds { polarity: true, .. } = error.error
            && let Some(join) = find(tree, error.node_id)
        {
            collect(join, &mut joined);
        }
    }
    if joined.is_empty() {
        return;
    }
    errors.retain(|error| {
        matches!(
            error.error,
            InferError::IncompatibleBounds { polarity: true, .. }
        ) || !error.related.iter().any(|related| {
            related.role == RelatedRole::Value
                && matches!(related.origin, crate::ccl::infer_var::Origin::Node(node)
                        if joined.contains(&node))
        })
    });
}

/// Whether `expr` holds the [`Error`](crate::ccl::TypedExprNode::Error) placeholder of a
/// statement lowering failed in.
fn holds_stand_in(expr: &Expr) -> bool {
    matches!(expr.node, crate::ccl::TypedExprNode::Error)
        || !expr.all_children(|c| !holds_stand_in(c))
}

/// Why one run of inference ([`run_once`]) failed.
struct RunFailure {
    /// What it reports.
    errors: Vec<LocatedInferError>,
    /// The expression of each statement a run that starts over leaves out: one emission
    /// owned during emission, including deferred calls and whole-graph failures
    /// ([`context::InferCtx::failure`]). Empty when coalesce or a later pass failed, since those
    /// report every failing node already.
    recovered: Vec<NodeId>,
}

/// How much of a statement recovered from a run that starts over leaves out
/// ([`run_with_params`]).
#[derive(Clone, Copy)]
pub(crate) enum StandIn {
    /// Its expression: a `let` still binds at an exact annotation, and a `:=` at its
    /// declared history.
    Expression,
    /// Its expression and its declared type, for a statement whose annotation fails on its
    /// own: a `let` binds at a poison, and a `:=` at a history of undeclared value type.
    Bare,
}

/// Replace each statement expression in `stood_in` with the
/// [`Error`](crate::ccl::TypedExprNode::Error) stand-in: a `let`'s right-hand side, an
/// expression statement's expression, a `:=`'s initializer, or a
/// [`DefGroup`](crate::ccl::TypedExprNode::DefGroup) member's definition. A
/// [bare](StandIn::Bare) one's statement loses its declared type too. With `keep_signature`,
/// an omitted function retains its lambdas and annotated result: callers still have to
/// meet declarations whose implementations failed.
pub(crate) fn stand_in_for_recovered(
    expr: &mut Expr,
    stood_in: &HashMap<NodeId, StandIn>,
    keep_signature: bool,
) {
    use crate::ccl::TypedExprNode;
    /// Stand in for `part` if it is listed, returning whether to drop its declared type.
    fn stand_in(
        part: &mut Expr,
        stood_in: &HashMap<NodeId, StandIn>,
        keep_signature: bool,
    ) -> bool {
        let Some(how) = stood_in.get(&part.node_id()) else {
            return false;
        };
        if keep_signature && matches!(how, StandIn::Expression) {
            stand_in_body(part);
        } else {
            part.node = TypedExprNode::Error;
            part.ty = Type::Hole;
        }
        matches!(how, StandIn::Bare)
    }
    fn stand_in_body(part: &mut Expr) {
        if let TypedExprNode::Lambda { body, .. } = &mut part.node {
            stand_in_body(body);
        } else if crate::ccl::opaque_output::is_annotated_result(part) {
            let TypedExprNode::Let { bound_expr, .. } = &mut part.node else {
                unreachable!()
            };
            bound_expr.node = TypedExprNode::Error;
            bound_expr.ty = Type::Hole;
        } else {
            part.node = TypedExprNode::Error;
            part.ty = Type::Hole;
        }
    }
    match &mut expr.node {
        TypedExprNode::Let {
            binding,
            bound_expr,
            ..
        } => {
            if stand_in(bound_expr, stood_in, keep_signature) {
                binding.user_annotation = None;
            }
        }
        TypedExprNode::ExprStmt { expr: e, .. } => {
            stand_in(e, stood_in, keep_signature);
        }
        TypedExprNode::MutDecl { binding, init, .. } => {
            if stand_in(init, stood_in, keep_signature)
                && let Some((domain, _, _)) = binding.ty.history_parts()
            {
                binding.ty = Type::mutable(domain.clone(), Type::Hole);
            }
        }
        TypedExprNode::DefGroup { bindings, .. } => {
            for (binding, def) in bindings {
                if stand_in(def, stood_in, keep_signature) {
                    binding.user_annotation = None;
                }
            }
        }
        _ => {}
    }
    expr.walk_children_mut(|child| stand_in_for_recovered(child, stood_in, keep_signature));
}

/// Locate post-coalesce failures in the original tree for partial module contracts.
/// Pre-coalesce failures use the ownership recorded while emitting each statement.
fn failed_after_coalesce(expr: &Expr, errors: Vec<LocatedInferError>) -> RunFailure {
    use crate::ccl::TypedExprNode;
    fn go(e: &Expr, within: Option<NodeId>, nodes: &HashSet<NodeId>, out: &mut Vec<NodeId>) {
        let expression = match &e.node {
            TypedExprNode::Let { bound_expr, .. } => Some(&**bound_expr),
            TypedExprNode::ExprStmt { expr, .. } => Some(&**expr),
            TypedExprNode::MutDecl { init, .. } => Some(&**init),
            _ => None,
        };
        // A statement's own node is blamed for what its rule raises, an annotation
        // mismatch, and stands for its expression.
        if nodes.contains(&e.node_id())
            && let Some(at) = expression.map(Expr::node_id).or(within)
        {
            out.push(at);
        }
        let members: Vec<&Expr> = match &e.node {
            TypedExprNode::DefGroup { bindings, .. } => bindings.iter().map(|(_, d)| d).collect(),
            _ => expression.into_iter().collect(),
        };
        e.walk_children(|child| {
            let within = if members.iter().any(|m| std::ptr::eq(*m, child)) {
                Some(child.node_id())
            } else {
                within
            };
            go(child, within, nodes, out);
        });
    }
    let nodes = errors.iter().map(|e| e.node_id).collect();
    let mut recovered = Vec::new();
    go(expr, None, &nodes, &mut recovered);
    RunFailure { errors, recovered }
}

/// One run of inference over `expr`, as [`run_with_params`] describes.
fn run_once(
    expr: &mut Expr,
    sources: &HashMap<String, Type>,
    instances: &Rc<solver::traits::InstanceTable>,
    params: &[ModuleCheckParam],
    reported: &HashSet<Name>,
    public: &HashSet<Name>,
    marks: &HashMap<NodeId, crate::ccl::lower::Mark>,
) -> Result<Inferred, RunFailure> {
    let failed = |errors| RunFailure {
        errors,
        recovered: Vec::new(),
    };
    // Convert source registry once; reuse across all node emissions.
    let mut sub_ctx = {
        let pre = InferCtx::new(HashMap::new(), expr.node_id());
        let translated: HashMap<String, Type> = sources
            .iter()
            .map(|(k, v)| (k.clone(), pre.normalize_annotation(v)))
            .collect();
        // Seed the blame cursor with the root: every error is stamped with the
        // node whose rule raised it, and the root is the outermost such node.
        let mut ctx = InferCtx::new(translated, expr.node_id());
        ctx.instances = Rc::clone(instances);
        ctx
    };
    let opened = sub_ctx
        .open_module_params(params)
        .map_err(|e| failed(vec![e]))?;
    sub_ctx.reported = reported.clone();
    sub_ctx.public = public.clone();
    sub_ctx.marks = marks.clone();

    // Pass 1: emit constraints. The high-value variants
    // (`UnboundVariable`/`TypeMismatch`/`ExpectedFunction`) all originate here.
    // Emission recovers at each statement (`Typing::recover`), so it reports
    // one error per failing statement, each carrying the node whose rule raised
    // it (`Typing::raise`). An error no statement encloses ends the walk.
    //
    // After any error the passes below do not run: the graph holds whatever
    // constraints the failed statements wrote before they failed, and lacks the
    // rest. `run_with_params` starts over without those statements instead.
    let emitted = emit_node(expr, &mut sub_ctx);
    let mut errors = std::mem::take(&mut sub_ctx.errors);
    // A method call the program's own statements deferred, and nothing after it resolved
    // or failed (`src/ccl/design/nominal-types.md`, "Method calls"). A walk an error ended leaves
    // the calls of the statements it was inside, which report nothing.
    if emitted.is_ok() {
        let [calls] = std::mem::take(&mut sub_ctx.method_calls)
            .try_into()
            .unwrap_or_else(|_| panic!("every definition closes the method calls it opens"));
        errors.extend(
            calls
                .iter()
                .filter(|call| call.obligation.is_waiting())
                .map(|call| call.unresolved()),
        );
    }
    if let Err(e) = emitted {
        errors.push(e);
    }
    let failure = sub_ctx.failure(errors);
    if !failure.errors.is_empty() || !failure.recovered.is_empty() {
        return Err(failure);
    }
    let mut errors = Vec::new();

    // Check each barrier variable's upper bounds against its resolution. The checks add
    // bounds, so they run before anything reads the graph: compaction reads a barrier
    // variable's lower bounds and nothing else (`solver::barrier`).
    push_barrier_failures(&mut errors, expr.node_id(), "this value");
    if !errors.is_empty() {
        return Err(sub_ctx.failure(errors));
    }

    // Each capability variable's capabilities are complete once emission is, so its upper bounds are
    // checked here (`src/ccl/design/type-inference.md`, "Written clauses"), after each
    // associated effect type is given what the obligation standing for it selected.
    sub_ctx.settle_effect_links();
    errors.extend(sub_ctx.escaping_results());
    if !errors.is_empty() {
        return Err(sub_ctx.failure(errors));
    }

    // The graph is complete here and nothing has been materialized yet — the one
    // point at which eager trait narrowing can be checked against the ground truth
    // it was approximating incrementally. Debug-only, and it leaves the graph as it
    // found it; the seal is for the terms `resolve_var_type` rebuilds and drops.
    #[cfg(debug_assertions)]
    crate::ccl::provenance::run_debug_check(|| {
        solver::traits::verify_narrowing_is_complete(|ty| resolve_var_type(ty).ok())
    });

    // Every requirement a definition places on one of its own values is recorded by
    // now, so this is where they can be read *together* — the step narrowing cannot
    // take, since it only ever sees one contribution at a time. Runs before coalesce
    // for two reasons: the tree is still whole, so a conflict can be blamed on a real
    // node, and a generalized definition's variables are still reachable, which after
    // coalesce they are not.
    {
        use solver::traits::{InstanceHead, OperandFailure, OperandRequirement};
        /// Render a solver-side requirement for display: bases become types, and the
        /// trait becomes its name, so no message borrows the solver's vocabulary.
        fn stated(r: OperandRequirement) -> StatedRequirement {
            StatedRequirement {
                trait_: r.trait_.to_string(),
                position: r.position,
                accepted: r.accepted.iter().map(InstanceHead::as_type).collect(),
                siblings: r
                    .siblings
                    .into_iter()
                    .map(|(pos, accepted)| {
                        (pos, accepted.iter().map(InstanceHead::as_type).collect())
                    })
                    .collect(),
            }
        }
        let mut cache = solver::ConstrainCache::new();
        let failures = solver::traits::resolve_operand_requirements(&mut cache);
        let located = failures.into_iter().map(|failure| {
            let (blame_vars, error, origins) = match failure {
                OperandFailure::Unsatisfiable { vars, requirements } => (
                    vars,
                    InferError::UnsatisfiableOperand {
                        requirements: requirements.into_iter().map(stated).collect(),
                    },
                    (None, None),
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
                    (None, None),
                ),
                OperandFailure::Conflict {
                    vars,
                    error,
                    origins,
                } => (
                    vars,
                    map_constrain_err(error, "a value an operator constrains"),
                    origins,
                ),
            };
            let node_id = match origins.0 {
                Some(crate::ccl::infer_var::Origin::Node(node)) => Some(node),
                _ => blame_node_for_place(expr, &blame_vars),
            };
            (
                LocatedInferError::new(error, node_id.unwrap_or(expr.node_id()))
                    .with_failure(origins),
                node_id.is_some(),
            )
        });
        let located: Vec<_> = located.collect();
        if !located.is_empty() {
            let attributed = located
                .iter()
                .filter(|(_, known)| *known)
                .map(|(e, _)| e.clone())
                .collect();
            let mut failure = sub_ctx.failure(attributed);
            failure.errors = located.into_iter().map(|(error, _)| error).collect();
            return Err(failure);
        }
    }
    // An ordered loop over a keyed collection requires `Orderable` of its keys, which its
    // source's type states once resolved.
    let unordered = sub_ctx.order_keyed_loops();
    if !unordered.is_empty() {
        return Err(failed(
            unordered
                .into_iter()
                .map(|e| at_written_source(expr, e))
                .collect(),
        ));
    }
    // An operand no contribution reached is judged by what it resolves to, which the sweep's
    // own deposits can determine, so this follows the sweep.
    {
        let mut cache = solver::ConstrainCache::new();
        if let Err((error, node)) =
            solver::traits::deliver_resolutions(&mut cache, |ty| resolve_var_type(ty).ok())
        {
            let failure = cache.take_failure();
            // A loop's positions are the one operand known to reach here
            // (`deliver_resolutions`); anything else is named generically.
            let unordered = match (find_node(expr, node).map(|e| &e.node), &error) {
                (
                    Some(crate::ccl::TypedExprNode::For { iter, .. }),
                    ConstrainError::NoTraitInstance { found, .. },
                ) => typing::Typing::unordered_loop(&sub_ctx, node, iter.node_id(), found),
                _ => None,
            };
            if let Some(unordered) = unordered {
                return Err(failed(vec![at_written_source(expr, unordered)]));
            }
            let what = match find_node(expr, node).map(|e| &e.node) {
                Some(crate::ccl::TypedExprNode::For { .. }) => {
                    "the positions of a loop whose iterations interact, which runs in their order"
                }
                _ => "a value a trait requires",
            };
            return Err(failed(vec![
                LocatedInferError::new(map_constrain_err(error, what), node).with_failure(failure),
            ]));
        }
    }
    // A loop's refusal moves to its written source, and a use's stays at the use; a
    // capability's failure stays where it is raised, at a use of a definition among them.
    let mut conditional: Vec<_> = sub_ctx
        .check_loop_orders()
        .into_iter()
        .map(|e| match e.error {
            InferError::UnorderedLoop { at_use: true, .. } => e,
            _ => at_written_source(expr, e),
        })
        .collect();
    push_capability_failures(&mut conditional, expr, &|item, clause| {
        sub_ctx.item_beyond_clause(item, clause)
    });
    conditional.extend(sub_ctx.requirements_beyond_clauses());
    if !conditional.is_empty() {
        return Err(failed(conditional));
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
    // Each coalesce error arrives blamed on the node whose rule raised it, so
    // this pass's (potentially several) errors need no post-hoc attribution.
    let mut errors = coalesce_pass(
        expr,
        std::mem::take(&mut sub_ctx.bound_at_annotation),
        std::mem::take(&mut sub_ctx.definition_telescopes),
        Rc::clone(instances),
        std::mem::take(&mut sub_ctx.use_capabilities),
    );
    sub_ctx.name_varying_binders(&mut errors);
    sub_ctx.name_other_feed_places(&mut errors);
    // The mutability rules on resolved types read the tree coalesce left, which is
    // whole past a node coalesce failed at.
    errors.extend(check_mut_discipline(expr).err().unwrap_or_default());
    if !errors.is_empty() {
        return Err(failed(errors));
    }

    // Coalesce can retain a witness before its enclosing binder is known. Validate
    // the complete expression before accepting inference, in every build.
    let mut scope_errors = Vec::new();
    check_scope_valid(expr, &Default::default(), &mut scope_errors);
    if !scope_errors.is_empty() {
        return Err(failed(scope_errors));
    }
    // Also inspect predicate, binder and target type slots, which the node-type scope
    // validator does not traverse for witness references. This additional walk is debug-only.
    #[cfg(debug_assertions)]
    debug_assert_no_free_witness(expr, "post-inference");
    // An expression statement, and a `with begin():` block, does something only by what it
    // causes.
    let inert: Vec<LocatedInferError> = sub_ctx
        .does_nothing()
        .into_iter()
        .map(|(node, error)| LocatedInferError::new(error, node))
        .collect();
    // A public function's type naming a variable its module keeps is a type the module's
    // interface cannot state, so it fails inference outright.
    let exported = sub_ctx.exported_capabilities();
    let escaping: Vec<LocatedInferError> = exported
        .escaping
        .into_iter()
        .map(|(node, name, capability)| {
            let item = capability.item.to_string();
            LocatedInferError::new(
                InferError::VariablePastItsScope {
                    member: name.base().to_string(),
                    item,
                },
                node,
            )
        })
        .collect();
    if !escaping.is_empty() {
        return Err(failed(escaping));
    }
    // A private feed a public function appends to is appended to by other modules, so it is
    // the run's, as a public feed is.
    let mut top_level = sub_ctx.top_level_capabilities();
    // Only a `with begin():` block's body supplies a transaction, so one a top level requires,
    // itself or through `Context`, is supplied by nothing.
    let transaction = crate::ccl::capabilities::Capability::Requires(
        crate::ccl::capabilities::Requirement::transaction(),
    );
    let unsupplied: Vec<LocatedInferError> = top_level
        .iter()
        .filter(|l| match &l.item {
            crate::ccl::capabilities::Capability::Every(every) => every.holds(&transaction),
            item => *item == transaction,
        })
        .map(|l| {
            let at = l
                .at
                .expect("a top-level requirement enters at the node that records or carries it");
            LocatedInferError::new(InferError::TransactionOutsideBlock, at)
        })
        .collect();
    if !unsupplied.is_empty() {
        return Err(failed(unsupplied));
    }
    top_level.extend(exported.appends);
    Ok(Inferred {
        ty: expr.ty.clone(),
        schemes: sub_ctx.schemes_noted,
        opened,
        top_level,
        inert,
    })
}

/// What [`run_with_params`] infers of a tree.
pub(crate) struct Inferred {
    pub(crate) ty: Type,
    pub(crate) schemes: NotedSchemes,
    pub(crate) opened: OpenedVars,
    /// What the tree's top level requires and causes, less what its scopes discharge, each
    /// label at the node where it entered.
    pub(crate) top_level: Vec<crate::ccl::capabilities::ScopedCapability>,
    /// The expression statements that cause nothing, each an error the caller reports once
    /// the checks that diagnose a statement more precisely have run.
    pub(crate) inert: Vec<LocatedInferError>,
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
    /// Used by scope-validation and type-comparison tests.
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
    use crate::ccl::Occurrence;
    use crate::ccl::RecordEntry;
    use crate::ccl::{BindingTransparency, TypedBinding, TypedExpr, TypedExprNode};

    #[test]
    fn distinct_domain_variables_keep_the_domain_mismatch() {
        let error = map_constrain_err(
            ConstrainError::DataDomainMismatch {
                lhs: Box::new(Type::Infer(crate::ccl::InferVar::fresh(0))),
                rhs: Box::new(Type::Infer(crate::ccl::InferVar::fresh(0))),
                cause: Box::new(ConstrainError::Mismatch {
                    lhs: Box::new(Type::Base(BaseType::Int)),
                    rhs: Box::new(Type::Base(BaseType::String)),
                }),
            },
            "this call",
        );
        assert!(
            matches!(&error, InferError::TypeMismatch { ctx, .. } if ctx.starts_with("collection domain")),
            "{error:?}"
        );
    }

    #[test]
    fn smoke_lambda_identity_inferred_int() {
        // λx. x applied to 42 → Int
        let lam = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                occurrence: Occurrence::mint(),
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
                transparency: BindingTransparency::Transparent,
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
            RecordEntry::new("a", Occurrence::mint(), lit_int(1)),
            RecordEntry::new("b", Occurrence::mint(), lit_string("x")),
        ]));
        let ty = run_inference(&mut e).expect("inference succeeds");
        assert_eq!(
            ty,
            Type::Record(vec![
                ("a".into(), int_lit_ty(1)),
                ("b".into(), str_lit_ty("x")),
            ])
        );
    }

    #[test]
    fn smoke_let_monomorphic() {
        // let x = 42 in x → Int
        let mut e = TypedExpr::new(TypedExprNode::Let {
            binding: TypedBinding {
                occurrence: Occurrence::mint(),
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
                transparency: BindingTransparency::Transparent,
            },
            bound_expr: Box::new(lit_int(42)),
            body: Box::new(TypedExpr::new(TypedExprNode::Var("x".into()))),
        });
        let ty = run_inference(&mut e).expect("inference succeeds");
        assert_eq!(ty, int_lit_ty(42));
    }
}
