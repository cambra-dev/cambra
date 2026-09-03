//! Coalesce: materialize a [`CompactGraph`] back into a concrete
//! [`crate::ccl::Type`].
//!
//! The final step of the `compact` → `simplify` → `coalesce` pipeline. It
//! counts the concrete structural contributions remaining at each polarity
//! position and reads off a single `Type` (or raises a [`CoalesceError`] on a
//! primitive collision / under-determined shape / residual cycle).

use std::collections::BTreeMap;

use crate::ccl::{HistoryKind, InferVar, InferVarId, Type};

use super::compact::{CompactGraph, CompactType, CompactVariant};
use crate::ccl::FieldKey;

// ---------------------------------------------------------------------------
// Coalesce errors
// ---------------------------------------------------------------------------

/// Errors raised by [`coalesce_compact`].
///
/// These are reported back to the caller and ultimately mapped onto
/// [`crate::ccl::infer::InferError`].
#[derive(Debug, Clone)]
pub enum CoalesceError {
    /// A variable's bounds at a positive position (or the upper bounds at
    /// a negative position) included multiple incompatible structural
    /// types — e.g. `Int` and `String` both flowing into the same value.
    /// The solver rejects this rather than inventing an anonymous (untagged)
    /// sum from the collision — a genuinely tagged `Variant` is a single
    /// shape and never triggers this.
    ///
    /// Two products that share no field are the same conflict read one level
    /// down: a positive merge intersects field sets, so the merged product has
    /// no fields, and there is no zero-field product for it to be. Unit is a
    /// *base* type, which a product reaches only through an operation that says
    /// so (`docs/chl-spec.md`, "6.6 The empty product is unit"), so answering
    /// `Unit` would drop every field with nothing in the program marking the
    /// loss. `details` names the empty field set rather than the operands, which
    /// the merge has already consumed by the time the position materializes.
    IncompatibleBounds {
        /// `true` = positive polarity (lower bounds forming a union);
        /// `false` = negative polarity (upper bounds forming an intersection).
        polarity: bool,
        /// UIDs of the inference variables that contributed these bounds.
        vars: Vec<InferVarId>,
        /// Pretty representation of the conflicting bounds.
        details: String,
    },
    /// A variable carried a **kinding** constraint (`α :: 𝐾`) that its resolved type
    /// does not satisfy: a computed collection annotated `List(𝑉)` whose domain turned
    /// out to be a data source, say, so it cannot supply the length witness a `List`
    /// ranges over.
    ///
    /// Raised here rather than at constraint emission because membership is a predicate
    /// on a *shape*, and the shape is what a variable does not have until it resolves.
    KindMismatch {
        /// What the position resolved to.
        resolved: Box<Type>,
        /// The type kind it was required to inhabit.
        type_kind: crate::ccl::ty::TypeKind,
    },
    /// A record-shaped variable still had open width at coalesce time —
    /// no closing equality constraint pinned its full set of fields.
    /// Mirrors today's `UnresolvedPartial` error so existing callers see
    /// the same error semantics.
    UnresolvedPartial {
        /// Whether the open record is index-keyed (tuple) or name-keyed
        /// (record), for diagnostic clarity.
        kind: PartialKind,
        /// Pretty representation of the partial fields.
        details: String,
    },
    /// A recursive (cyclic) type was inferred. The solver deliberately
    /// rejects these per the plan's R2 review note; they would otherwise
    /// silently arise from programs like `λx. x x`.
    RecursiveType {
        /// Pretty representation of the cycle entry point.
        details: String,
    },
    /// A data function carrying >= 2 candidate domains (a conditional collection) met a compute
    /// function at a positive join, so collapsing to the ordinary meet would
    /// drop domains. Reported loudly rather than silently losing data (no
    /// current program produces this shape). See `design/type-inference.md`,
    /// "4.6 Data vs compute functions".
    DomainJoinConflict {
        /// The domains that have no common answer, in the order they were met.
        ///
        /// The domains rather than a rendering of them: a caller decides how to say it, and
        /// the one thing it must be able to say is *which* domains — a merged position is
        /// neither of the two a conditional's arms were written over, so reporting the
        /// position names a domain that appears nowhere in the source.
        domains: Vec<Type>,
    },
    /// A single function slot whose kind resolved contradictorily: one kind
    /// variable at [`crate::ccl::ty::KindPin::Conflict`].
    ///
    /// The two kinds are incomparable, so an edge between them is a rejection
    /// wherever it is drawn; this is the coalesce-time face of
    /// [`super::constrain::ConstrainError::KindMismatch`], for the case where the
    /// violation only becomes provable once the variable's pins are all in
    /// (a kind-polymorphic parameter used as a collection at one site and as a
    /// capability at another). See `src/ccl/design/type-inference.md`,
    /// "4.6 Data vs compute functions".
    KindConflict {
        /// Pretty representation of the offending function slot.
        details: String,
    },
    /// A witness reference materialized with no binder over it.
    ///
    /// A [`Type::WitnessRef`] is a leaf, so a materialized type that carries a free one
    /// means nothing and every consumer downstream compares it against real domains.
    /// Reported here because this is where the close happens: a sum whose body names a
    /// binder it does not bind, or two indices meeting at one position, are both decided
    /// at this materialization and nowhere earlier.
    WitnessScope {
        /// What the position was materializing, and which binder had no scope.
        details: String,
    },
}

/// Distinguishes a partial tuple (Index keys) from a partial record
/// (Name keys) for [`CoalesceError::UnresolvedPartial`] diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PartialKind {
    /// Index-keyed; would coalesce to `Type::Tuple` if dense and closed.
    Tuple,
    /// Name-keyed; would coalesce to `Type::Record` if closed.
    Record,
}

// ---------------------------------------------------------------------------
// Coalesce: CompactGraph → ccl::Type
// ---------------------------------------------------------------------------

/// Materialize a CompactType into `ccl::Type`.
///
/// Multiple atom contributions at the same position is an error
/// (`IncompatibleBounds`) — the solver won't invent an anonymous sum from a
/// primitive collision. A
/// CompactType with no concrete contributions coalesces to a fresh
/// `Type::Infer` (caller's `check_fully_typed` reports it).
///
/// Variable contributions are *consumed* — they don't appear directly
/// in the output. Their information already flowed into the bound list
/// during `compact_type`. If a variable contributes nothing structural
/// (no atom/rec/fun) and there are no co-occurring atoms, we emit
/// `Type::Infer`.
pub fn coalesce_compact(graph: &CompactGraph) -> Result<Type, CoalesceError> {
    if !graph.rec_vars.is_empty() {
        return Err(CoalesceError::RecursiveType {
            details: format!("{} recursive variable(s) in graph", graph.rec_vars.len()),
        });
    }
    coalesce_compact_go(&graph.term, true, &[])
}

/// A binder as the output spells it: the name its position answers to, over what the
/// position turned out to range over.
///
/// Materialization is where both can be answered. Every contribution to the position has
/// arrived, so the kind's children resolve like any other position; and the name is minted
/// once per position ([`crate::ccl::ty::FunKindVar::binder_ids`]), so every occurrence comes
/// back as one name with nothing rewritten. A binder that was already settled is already its
/// own answer.
fn settle(
    w: &super::compact::CompactWitness,
    polarity: bool,
    scope: &[crate::ccl::ty::Witness],
) -> Result<crate::ccl::ty::Witness, CoalesceError> {
    Ok(crate::ccl::ty::Witness::bound_to(
        w.id.bound(),
        coalesce_type_kind(&w.type_kind, polarity, scope)?,
    ))
}

/// A binder's kind with its children materialized — the way back from
/// [`CompactTypeKind`](super::compact::CompactTypeKind).
///
/// The children are candidate *domains*, so they materialize contravariantly, exactly as the
/// function's own domain does.
fn coalesce_type_kind(
    type_kind: &super::compact::CompactTypeKind,
    polarity: bool,
    scope: &[crate::ccl::ty::Witness],
) -> Result<crate::ccl::ty::TypeKind, CoalesceError> {
    use super::compact::CompactTypeKind;
    match type_kind {
        CompactTypeKind::Enumerated(candidates) => {
            // Deduplicated **after** materializing, not before: a kind's candidates are a
            // set, and two that were spelled as distinct variables are one candidate once
            // the variables answer. Comparing the spellings is what let a two-candidate kind
            // survive a conditional whose arms turned out to be over one domain.
            let mut out: Vec<Type> = Vec::new();
            for c in candidates {
                let t = coalesce_compact_go(c, polarity, scope)?;
                if !out.contains(&t) {
                    out.push(t);
                }
            }
            // **The candidates are a set, so their order is canonical rather than
            // arrival's.** Candidates kept in the order their arms were recorded makes
            // the type a function of which constraint arrived first: the same conditional
            // materializes as `Σ (σ : [A, B]). …` or `Σ (σ : [B, A]). …`, and `Type`
            // compares candidates positionally, so those are two types. Sorted by rendering,
            // the same key planning uses to order a refinement set. Found by
            // `tests/constraint_order_fuzz.rs`.
            out.sort_by_cached_key(|t| t.to_string());
            Ok(crate::ccl::ty::TypeKind::Enumerated(out))
        }
        CompactTypeKind::SubtypesOf(bound) => Ok(crate::ccl::ty::TypeKind::SubtypesOf(Box::new(
            coalesce_compact_go(bound, polarity, scope)?,
        ))),
        CompactTypeKind::UIntRanges => Ok(crate::ccl::ty::TypeKind::UIntRanges),
        CompactTypeKind::Type => Ok(crate::ccl::ty::TypeKind::Type),
    }
}

fn coalesce_compact_go(
    ct: &CompactType,
    polarity: bool,
    scope: &[crate::ccl::ty::Witness],
) -> Result<Type, CoalesceError> {
    // Transparent read at joins: a feed handle meeting *non-feed*
    // contributions at one position is being read — `x + 1` joins x's
    // payload with `Int` through a shared join variable, so the handle
    // dissolves into its payload before the contribution count below
    // (otherwise `feed(Int)` and `Int` would spuriously collide). A feed
    // handle alone at a position keeps its constructor; so do two handles
    // meeting (their `history_slot`s merged upstream). This is the
    // join-variable counterpart of `constrain_go`'s direct feed read-through
    // rule (a feed history `<: T` reads through to its stream `domain ⇒ value`).
    let ct = &dissolve_read_feeds(ct.clone(), polarity);
    // Count concrete (non-variable) contributions to pick the output
    // type. With multiple distinct contributions, we would need
    // a Union/Intersection — we error instead.
    let mut atoms: Vec<Type> = Vec::new();
    // **A witness reference materializes only under its binder, and only alone.**
    //
    // Out of scope, it is a leaf naming nothing, and every consumer downstream compares it
    // against real domains. Beside another witness, the position is two indices at once —
    // and picking one of them, however the choice is made, answers with one index where two
    // arrived and strands the other's occurrences, since nothing here renames them.
    let mut seen: Vec<crate::ccl::ty::WitnessId> = Vec::new();
    for a in &ct.atoms {
        match a {
            // **A binder in scope names the index it recorded.** An occurrence spelled with
            // any of a position's aliases denotes that position, so it materializes as the
            // position's name — which is what leaves one name where several derivations of
            // one index arrived, with nothing renamed after the fact.
            super::compact::AtomKey::Witness(w) => seen.push(*w),
            other => atoms.push(other.to_type()),
        }
    }
    if !seen.is_empty() {
        // **A reference is resolved against the scope, not against its neighbours.** The
        // binders enclosing this position are settled before its parts materialize, so a
        // reference naming one of them denotes it, and a reference naming anything else is
        // a spelling from the route it arrived by — the same index, written in a scope that
        // is not this one. Comparing the atoms to each other instead reports the *pair*,
        // which says a position holds two indices where in fact it holds one and a stale
        // name for it.
        let mut bound = seen.iter().filter(|x| scope.iter().any(|b| b.id() == *x));
        let resolved = match bound.next() {
            // Two binders **both in scope** is the real thing this rejects: one position
            // required to be two domains at once, which no rename reconciles.
            Some(first) => {
                if let Some(other) = bound.find(|o| o != &first) {
                    return Err(CoalesceError::WitnessScope {
                        details: format!(
                            "{first:?} and {other:?} are both in scope at one position"
                        ),
                    });
                }
                *first
            }
            // **Nothing here is bound yet**, so this walk cannot say which index the
            // position denotes — coalesce runs bottom-up, and what binds a node's type is
            // decided above it. So one name rides through, and the tree-level escape check
            // reports it if nothing ever binds it (`check_scope_valid`, the check the design
            // gives this job precisely because a per-type check cannot do it).
            //
            // Rejecting here instead treats "this walk cannot tell yet" as "the program is
            // wrong". Measured: every position reaching this arm holds names none of which
            // are bound, and no position in the suite ever holds two names that *are* — so
            // the pair being reported was never the conflict the report claimed.
            //
            // The least id, for an answer that does not depend on which contribution the
            // lattice happened to store first (`tests/constraint_order_fuzz.rs`).
            None => *seen.iter().min().expect("seen is non-empty"),
        };
        atoms.push(Type::WitnessRef(resolved));
    }
    let mut shapes: Vec<Type> = Vec::new();

    if let Some(rec) = &ct.rec {
        let vars: Vec<InferVarId> = ct.vars.iter().copied().collect();
        shapes.push(materialize_record(rec, polarity, &vars, scope)?);
    }
    if let Some(var) = &ct.var {
        shapes.push(materialize_variant(var, polarity, scope)?);
    }
    if let Some(cf) = &ct.fun {
        use crate::ccl::ty::KindPin;
        // **The binders settle before the parts materialize**, so the domain and codomain
        // come back naming them and there is nothing to rewrite afterwards.
        let binders = cf
            .binders
            .iter()
            .map(|w| settle(w, !polarity, scope))
            .collect::<Result<Vec<_>, _>>()?;
        let mut inner_scope = scope.to_vec();
        inner_scope.extend(binders.iter().cloned());
        let scope: &[crate::ccl::ty::Witness] = &inner_scope;
        // Materialize the codomain once (covariant), and each candidate
        // domain (contravariant), deduplicating at the `Type` level — this catches
        // var-level equalities that the compact-time `CompactType ==` dedup in
        // `CompactTypeKind::merge` missed (simplify may have merged uids after compaction).
        let c = coalesce_compact_go(&cf.codomain, polarity, scope)?;
        // The domain, materialized contravariantly. At a `Data` position the atoms are
        // *alternatives* — one candidate each (see `denoted_domains`) — and a
        // `DomainConflict` reads them the same way, since naming both is the whole content
        // of its diagnostic. Everywhere else they are a collision, which
        // `coalesce_compact_go` reports. Deduplicated at the
        // `Type` level, which catches var-level equalities the compact-time `==` missed.
        let candidates: Vec<Type> = if (cf.kind.is_data() || cf.domains_disagree)
            && let Some(ds) = super::compact::denoted_domains(&cf.domain)
        {
            let mut out: Vec<Type> = Vec::new();
            for d in ds {
                if !out.contains(&d) {
                    out.push(d);
                }
            }
            out
        } else {
            vec![coalesce_compact_go(&cf.domain, !polarity, scope)?]
        };
        // Strip the Pi binder unless the codomain actually depends on it
        // (design §3.2 / O10): keeps ordinary functions `name: None` while a
        // genuinely dependent codomain keeps its binder. Closed or name-spelled
        // both count (`subst::codomain_depends_on`) — the kept name slot is what
        // lets descent and application open the function later, so dropping it
        // on a codomain that references it strands the reference.
        debug_assert!(
            cf.name.is_some() || !crate::ccl::subst::references_enclosing_function(&c),
            "an index is only ever assigned pointing at a *named* function, so an \
             unnamed function's codomain cannot reference it",
        );
        let kept_name = cf
            .name
            .clone()
            .filter(|b| crate::ccl::subst::codomain_depends_on(b, &c));
        let type_kind = crate::ccl::ty::TypeKind::Enumerated(candidates);
        match cf.kind {
            // Each conflict reports the fact it *is*. Deciding between them by asking
            // whether the merged kind names more than one domain reads the shape of the
            // answer rather than the reason for it, and mis-reported a domain conflict as
            // a kind collision whenever the candidates deduplicated to one.
            KindPin::Conflict => {
                assert!(
                    !matches!(&type_kind, crate::ccl::ty::TypeKind::Enumerated(ds) if ds.is_empty()),
                    "a kind naming candidates reaches materialization with at least one"
                );
                return Err(CoalesceError::KindConflict {
                    details: format!("a compute function (capability) over {type_kind}"),
                });
            }
            _ if cf.domains_disagree => {
                assert!(
                    !matches!(&type_kind, crate::ccl::ty::TypeKind::Enumerated(ds) if ds.is_empty()),
                    "a kind naming candidates reaches materialization with at least one"
                );
                // The **operands** where a merge kept them. A contravariant meet unions a
                // record's fields, so two domains that disagreed on their key sets leave as
                // one and the position no longer holds either of the two the program wrote;
                // `kind` would name the union. Where nothing was combined the position's own
                // candidates are the conflicting domains and say it directly.
                let domains = match &cf.combined {
                    Some(combined) => {
                        let (a, b) = combined.pair();
                        vec![
                            coalesce_compact_go(a, !polarity, scope)?,
                            coalesce_compact_go(b, !polarity, scope)?,
                        ]
                    }
                    None => match &type_kind {
                        crate::ccl::ty::TypeKind::Enumerated(ds) => ds.clone(),
                        _ => Vec::new(),
                    },
                };
                return Err(CoalesceError::DomainJoinConflict { domains });
            }
            // Nothing pinned this kind, so the capability default applies — the
            // same shape as `Compute`, decided here rather than at the merge, where
            // "unrequired" still had to stay distinct from "required to be a
            // capability" (`KindPin::Unpinned`).
            KindPin::Unpinned | KindPin::Compute => {
                // A compute function's domain is an ordinary parameter type. A domain that
                // names no candidates arises only from a sum's body, which is always `Data`,
                // and `CompactTypeKind::merge` produces one only from another, so a compute
                // slot never carries a sum's domain.
                let crate::ccl::ty::TypeKind::Enumerated(domains) = &type_kind else {
                    unreachable!("a compute function slot's domain kind names no candidates")
                };
                let [sole] = domains.as_slice() else {
                    unreachable!("a compute function slot carries several candidate domains")
                };
                shapes.push(Type::Fun {
                    name: kept_name,
                    fun_kind: crate::ccl::ty::FunKind::Compute,
                    domain: Box::new(sole.clone()),
                    codomain: Box::new(c),
                });
            }
            KindPin::Data | KindPin::Plain | KindPin::Sum(_) => {
                // **A data function's domain is one domain.** A consumed sum *names* its
                // witness rather than putting a sum where a domain belongs, and a join
                // forms no sum at all — that is `box`'s job — so nothing puts several
                // candidates here. This is the property that lets [`CompactFun::domain`]
                // be one ordinary position rather than a candidate set, so it is asserted
                // rather than assumed. A sum materializes from the Σ slot beside this one,
                // never by reading a second candidate off the domain.
                let crate::ccl::ty::TypeKind::Enumerated(domains) = &type_kind else {
                    unreachable!("a data function slot's domain kind names no candidates")
                };
                let [_] = domains.as_slice() else {
                    unreachable!("a data function's domain names several candidates: {type_kind}")
                };
                // **A binder's name is the binder's**, minted on the kind variable
                // ([`crate::ccl::ty::FunKindVar::binder_ids`]) and never read back off the
                // domain: the domain *refers* to the binder, so taking a name from it inverts
                // which of the two is the fact. Every occurrence reaching this position is
                // renamed onto the binder by the correspondence the relating edge draws
                // (`fun_kind_correspondence`), which is what has to be complete.
                // **The binders close the function.** They settled above, so the parts
                // already name them; a plain collection has none and comes back as it is.
                shapes.push(Type::Fun {
                    name: kept_name,
                    fun_kind: if binders.is_empty() {
                        crate::ccl::ty::FunKind::Data(None)
                    } else {
                        crate::ccl::ty::FunKind::Data(Some(std::rc::Rc::new(binders.clone())))
                    },
                    domain: Box::new(domains[0].clone()),
                    codomain: Box::new(c),
                });
            }
        }
    }
    if let Some((value, domain, history_kind)) = &ct.history_slot {
        // Both children materialize at the same polarity (invariant — both
        // directions were resolved at constraint time). The `kind` rides through
        // from compaction so a feed rebuilds as a feed, a mutable variable as a mutable variable.
        shapes.push(Type::History {
            value: Box::new(coalesce_compact_go(value, polarity, scope)?),
            domain: Box::new(coalesce_compact_go(domain, polarity, scope)?),
            history_kind: *history_kind,
        });
    }
    let mut all = Vec::new();
    all.append(&mut atoms);
    all.append(&mut shapes);

    let inner = match all.len() {
        0 => {
            // **A position with variables keeps one of them.** No concrete contribution
            // is two situations, and only one is an error. A *parameter's* domain has
            // none because the caller supplies it, and generalization is what carries
            // that: quantifying the variable is only possible if the variable survives,
            // with its level, its telescope and whatever was recorded against it. Minting
            // a scope-free placeholder instead discards all three — the kinding edge
            // included — and severs every use site from the definition, since a level-0
            // variable is shared rather than freshened.
            //
            // With no variables either, the position genuinely stands for nothing, and the
            // placeholder is the error slot `check_fully_typed` reports as
            // `UnresolvedInfer`.
            match ct.vars.iter().min().and_then(crate::ccl::infer_var::lookup) {
                Some(v) => Type::Infer(v),
                None => Type::Infer(InferVar::fresh(0)),
            }
        }
        1 => all.remove(0),
        _ => {
            // Multiple incompatible contributions. Reject.
            //
            // NB: a positive-polarity union relaxation for heterogeneous scalar
            // `Case` arms (`1 if c else "x"` → `Int | String`) is *not* done
            // here: it is indistinguishable at coalesce from a binop-operand
            // join (`1 + true`), which must stay a hard error. A sound version
            // needs strict scalar consumers (binops, …) to impose concrete
            // bounds so the union is rejected at *their* site; that is deferred
            // past the conditional-collection foundation. Collection arms still join losslessly — that happens in
            // the `fun` slot above (`CompactFun::merge`), not through atoms.
            let pretty = all
                .iter()
                .map(|t| format!("{t}"))
                .collect::<Vec<_>>()
                .join(" | ");
            let vars: Vec<InferVarId> = ct.vars.iter().copied().collect();
            return Err(CoalesceError::IncompatibleBounds {
                polarity,
                vars,
                details: pretty,
            });
        }
    };

    // Re-attach the refinements carried at this position.
    // A position with no refinement contribution materializes as the bare type: `None`
    // and an empty set both mean "no refinements hold here".
    let out = Type::refined(inner, ct.refinements.clone().unwrap_or_default());
    // Discharge the kinding constraints this position gathered. A variable's kinding
    // constraint is the one thing about it that cannot be recorded as a bound, so it
    // rode compaction in its own slot and is answered here, where the position has
    // finally become a type — the same moment its bounds become one.
    //
    // **Membership, not containment.** `𝛼 :: 𝐾` asks whether one domain lies in a kind,
    // which is [`crate::ccl::ty::TypeKind::refuses`]; the kind premise asks whether one
    // *set* of domains lies in another, and that one draws edges
    // (`super::constrain::constrain_type_kinds`). Post-coalesce there is no graph left to
    // emit into, so this side is the structural answer and can only be that.
    // A position that materializes as a **variable** has not become a type yet, so the
    // membership edge has no answer here, and needs none: `𝛼 :: 𝐾` is recorded on
    // the variable and discharged wherever a type reaches it
    // (`super::constrain::answer_type_kinds`), including at each instantiation of a
    // generalized definition. Deciding it here would answer for a definition what only its
    // uses can say.
    let undecided = matches!(out.peel_refinements(), Type::Infer(_));
    for k in &ct.kinds {
        if undecided {
            continue;
        }
        if k.refuses(&out) {
            return Err(CoalesceError::KindMismatch {
                resolved: Box::new(out),
                type_kind: k.clone(),
            });
        }
    }
    Ok(out)
}

/// Dissolve a position's feed `history_slot` into its other contributions when
/// both are present — see the transparent-read comment in [`coalesce_compact_go`].
///
/// This performs at most one merge per position: reconstructing the channel as a
/// `fun`-slot type and merging it leaves `history_slot` empty, so the loop
/// exits. A *chained* defer read (a feed handle nested in the payload) rides
/// inside the merged `fun` codomain and is resolved by ordinary recursion in
/// [`coalesce_compact_go`], not by re-entering here. A mutable-variable slot, or a lone
/// feed with no other content, is left intact. The `while` form is a defensive
/// fixpoint; the body never re-arms `history_slot`.
fn dissolve_read_feeds(mut ct: CompactType, polarity: bool) -> CompactType {
    while let Some((value, domain, kind)) = ct.history_slot.take() {
        // Only a *feed channel* dissolves into a read view; a mutable variable is read as
        // its scalar value, never merged into the surrounding type.
        if kind != HistoryKind::Append {
            ct.history_slot = Some((value, domain, kind));
            break;
        }
        let has_other =
            !ct.atoms.is_empty() || ct.rec.is_some() || ct.var.is_some() || ct.fun.is_some();
        if !has_other {
            ct.history_slot = Some((value, domain, kind));
            break;
        }
        // The channel is the `domain ⇒ value` function; reconstruct it as a
        // `fun`-slot CompactType (exactly what the old single-payload slot held)
        // and merge it into the read view.
        //
        // Not [`CompactType::value`]: this re-expresses content already at this
        // position rather than arriving as a second bound, so it imposes no refinement
        // of its own and leaves `refinements` at the merge identity. Building it
        // as a value would intersect the position's own refinements away at a positive
        // polarity (see `CompactType::refinements`).
        let chan = CompactType {
            fun: Some(super::compact::CompactFun {
                name: None,
                binders: Vec::new(),
                // A feed's read view is a collection stream: a data function.
                kind: super::compact::KindPin::Data,
                // A stream is over its channel domain, not over an index of its own.
                domains_disagree: false,
                domain,
                combined: None,
                codomain: value,
            }),
            ..Default::default()
        };
        ct = CompactType::merge(polarity, ct, chan);
    }
    ct
}

/// How a position's polarity reads in a diagnostic.
fn polarity_word(polarity: bool) -> &'static str {
    if polarity { "produced" } else { "required" }
}

/// Materialize a variant contribution into [`Type::Variant`], preserving tag
/// order by name (BTreeMap iterates in key order, so output is stable).
/// Payloads coalesce at the same polarity as the outer (covariant depth).
///
/// The [`Openness`] rides through unchanged. It reaches here only from a
/// *demand* — the arm set of a `match` with a `case _:` — which is what makes a
/// diagnostic naming that demand render it as the partial arm set it is
/// (``{`a{Int} | …}``) rather than as an exact sum the scrutinee failed to be.
fn materialize_variant(
    variant: &CompactVariant,
    polarity: bool,
    scope: &[crate::ccl::ty::Witness],
) -> Result<Type, CoalesceError> {
    let mut out = Vec::with_capacity(variant.tags.len());
    for (k, v) in &variant.tags {
        out.push((k.clone(), coalesce_compact_go(v, polarity, scope)?));
    }
    Ok(Type::Variant(out, variant.openness))
}

fn materialize_record(
    rec: &BTreeMap<FieldKey, CompactType>,
    polarity: bool,
    vars: &[InferVarId],
    scope: &[crate::ccl::ty::Witness],
) -> Result<Type, CoalesceError> {
    // No zero-field product exists, and `Unit` is not one: it is a base type, and
    // a product reaches it only through an operation that says so
    // (`docs/chl-spec.md`, "6.6 The empty product is unit"). Answering `Unit` here
    // would be the silent arrival that section rules out. A positive merge
    // intersects field sets, so an empty map is what products sharing no field
    // merge to — bounds with no common shape, which is what
    // `IncompatibleBounds` already says.
    if rec.is_empty() {
        return Err(CoalesceError::IncompatibleBounds {
            polarity,
            vars: vars.to_vec(),
            details: format!("{} products sharing no field", polarity_word(polarity)),
        });
    }
    let all_index = rec.keys().all(|k| matches!(k, FieldKey::Index(_)));
    let all_name = rec.keys().all(|k| matches!(k, FieldKey::Name(_)));

    if all_index {
        let mut indexed: Vec<(usize, &CompactType)> = rec
            .iter()
            .map(|(k, v)| match k {
                FieldKey::Index(i) => (*i, v),
                _ => unreachable!(),
            })
            .collect();
        indexed.sort_by_key(|(i, _)| *i);
        let dense = indexed
            .iter()
            .enumerate()
            .all(|(pos, (idx, _))| pos == *idx);
        if dense {
            // Closed dense tuple.
            let mut out = Vec::with_capacity(indexed.len());
            for (_, v) in indexed {
                out.push(coalesce_compact_go(v, polarity, scope)?);
            }
            Ok(Type::Tuple(out))
        } else {
            // Sparse indices — an open record-var (e.g. an isolated
            // index-projection domain) that never got pinned to a closed
            // tuple shape during inference. It is genuinely
            // under-determined and unconstructable by the runtime, so it
            // coalesces to a fresh `Type::Infer` (an ambiguous-type
            // condition, reported by `check_fully_typed` if it survives to
            // the program's output). Note: still recurse the payloads so
            // any nested var bounds are visited even though we discard the
            // shape.
            for (_, v) in indexed {
                coalesce_compact_go(v, polarity, scope)?;
            }
            Ok(Type::Infer(InferVar::fresh(0)))
        }
    } else if all_name {
        let mut out = Vec::with_capacity(rec.len());
        for (k, v) in rec {
            let name = match k {
                FieldKey::Name(s) => s.to_string(),
                _ => unreachable!(),
            };
            out.push((name, coalesce_compact_go(v, polarity, scope)?));
        }
        // We don't have a way to distinguish open vs closed name-keyed
        // records at this layer (no field-count invariant analogous
        // to dense indices). For now, emit Record always — the
        // existing path's Record/PartialRecord distinction is driven
        // by lowering, which already differentiates field-set-known
        // sites from projection sites.
        Ok(Type::Record(out))
    } else {
        Err(CoalesceError::UnresolvedPartial {
            kind: PartialKind::Record,
            details: format!(
                "mixed Index/Name keys: {:?}",
                rec.keys().collect::<Vec<_>>()
            ),
        })
    }
}

#[cfg(test)]
mod tests {
    // `ConstrainCache` keys on `(Type, Type)`; its interior mutability is
    // identity-by-`uid` and never inspected by `Hash`/`Eq`, so the lint's
    // hazard does not apply (see `constrain`'s module-level note).
    #![allow(clippy::mutable_key_type)]

    use std::collections::BTreeMap;

    use super::*;
    use crate::ccl::infer::solver::compact::{AtomKey, CompactGraph, CompactType};
    use crate::ccl::infer::solver::test_helpers::{record, refined, variant};
    use crate::ccl::infer::solver::{
        ConstrainCache, compact_type, constrain_subtype, fresh_var, fun, prim, simplify_type,
    };
    use crate::ccl::{BaseType, Bound, FieldKey, Type};

    #[test]
    fn coalesce_primitive_round_trips() {
        let s = prim(BaseType::Int);
        assert_eq!(
            coalesce_compact(&compact_type(&s)).unwrap(),
            Type::Base(BaseType::Int)
        );
    }

    #[test]
    fn coalesce_uintranges_sigma_round_trips() {
        // A `List` Σ compacts into the `fun` slot with a domain naming no candidates — the
        // kind rides through verbatim, only the codomain compacts — so
        // compact → coalesce re-forms the identical type. Contrast the
        // conditional-collection Σ, whose candidates join the lattice.
        let list_ty = Type::list_of(Type::Base(BaseType::Int));
        let t = coalesce_compact(&compact_type(&list_ty)).unwrap();
        assert_eq!(t, list_ty);
    }

    #[test]
    fn coalesce_collection_sigma_round_trips() {
        // A `Collection` (`TypeKind::Type`) Σ rides through exactly as the `List` Σ above
        // does — the kind inert, only the codomain compacted — so the ⊤ of the kind order
        // needs no carrier of its own to survive the round trip.
        let coll = Type::collection_of(Type::Base(BaseType::Int));
        let t = coalesce_compact(&compact_type(&coll)).unwrap();
        assert_eq!(t, coll);
    }

    #[test]
    fn coalesce_function_preserves_shape() {
        let s = fun(prim(BaseType::Int), prim(BaseType::Bool));
        let t = coalesce_compact(&compact_type(&s)).unwrap();
        assert_eq!(
            t,
            Type::Fun {
                name: None,
                fun_kind: crate::ccl::ty::FunKind::Compute,
                domain: Box::new(Type::Base(BaseType::Int)),
                codomain: Box::new(Type::Base(BaseType::Bool))
            }
        );
    }

    #[test]
    fn coalesce_single_data_domain_is_plain_data_fun() {
        use crate::ccl::infer::solver::compact::{CompactFun, KindPin};
        // One surviving domain collapses to a plain `Data` fun (idempotence:
        // `xs if c else xs` types as `xs`).
        let graph = CompactGraph {
            term: CompactType {
                fun: Some(CompactFun {
                    binders: Vec::new(),
                    name: None,
                    kind: KindPin::Data,
                    domains_disagree: false,
                    domain: Box::new(compact_type(&Type::UIntRange(2)).term),
                    combined: None,
                    codomain: Box::new(compact_type(&prim(BaseType::Int)).term),
                }),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };
        assert_eq!(
            coalesce_compact(&graph).unwrap(),
            Type::Fun {
                name: None,
                fun_kind: crate::ccl::ty::FunKind::Data(None),
                domain: Box::new(Type::UIntRange(2)),
                codomain: Box::new(Type::Base(BaseType::Int)),
            }
        );
    }

    #[test]
    fn coalesce_domain_join_conflict_errs() {
        use crate::ccl::infer::solver::compact::{CompactFun, KindPin};
        // Two domains with no common answer is a loud coalesce error, never a silent
        // domain drop — and it reports as a *domain* conflict, which is the fact it is.
        // The kind collision (`KindPin::Conflict`, a collection demanded of a compute
        // capability) is a different fact, so it carries its own variant rather than
        // being told apart from this one by the shape of the merged kind.
        let graph = CompactGraph {
            term: CompactType {
                fun: Some(CompactFun {
                    binders: Vec::new(),
                    name: None,
                    kind: KindPin::Plain,
                    domains_disagree: true,
                    // Two domains at one position: a `fun` slot holds one domain, so a
                    // second one arriving there is the conflict.
                    domain: Box::new(CompactType::merge(
                        true,
                        compact_type(&Type::UIntRange(2)).term,
                        compact_type(&Type::UIntRange(3)).term,
                    )),
                    combined: None,
                    codomain: Box::new(compact_type(&prim(BaseType::Int)).term),
                }),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };
        assert!(matches!(
            coalesce_compact(&graph),
            Err(CoalesceError::DomainJoinConflict { .. })
        ));
    }

    #[test]
    fn coalesce_single_domain_conflict_is_a_kind_conflict() {
        use crate::ccl::infer::solver::compact::{CompactFun, KindPin};
        // A `Conflict` over a *single* domain is one function slot demanded as a
        // data domain while being a compute capability — the coalesce-time face
        // of a kind conflict, reported as `KindConflict` rather
        // than the multi-domain `DomainJoinConflict`.
        let graph = CompactGraph {
            term: CompactType {
                fun: Some(CompactFun {
                    binders: Vec::new(),
                    name: None,
                    kind: KindPin::Conflict,
                    domains_disagree: false,
                    domain: Box::new(compact_type(&prim(BaseType::Int)).term),
                    combined: None,
                    codomain: Box::new(compact_type(&prim(BaseType::Int)).term),
                }),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };
        assert!(matches!(
            coalesce_compact(&graph),
            Err(CoalesceError::KindConflict { .. })
        ));
    }

    #[test]
    fn coalesce_dense_index_record_becomes_tuple() {
        let r = record(&[
            (FieldKey::Index(0), prim(BaseType::Int)),
            (FieldKey::Index(1), prim(BaseType::String)),
        ]);
        let t = coalesce_compact(&compact_type(&r)).unwrap();
        assert_eq!(
            t,
            Type::Tuple(vec![
                Type::Base(BaseType::Int),
                Type::Base(BaseType::String)
            ])
        );
    }

    #[test]
    fn coalesce_named_record_becomes_record() {
        let r = record(&[
            (FieldKey::Name("x".into()), prim(BaseType::Int)),
            (FieldKey::Name("y".into()), prim(BaseType::Bool)),
        ]);
        let t = coalesce_compact(&compact_type(&r)).unwrap();
        assert_eq!(
            t,
            Type::Record(vec![
                ("x".to_string(), Type::Base(BaseType::Int)),
                ("y".to_string(), Type::Base(BaseType::Bool))
            ])
        );
    }

    #[test]
    fn coalesce_sparse_index_emits_infer() {
        // A sparse Index record (e.g. an isolated index-projection domain
        // that never closed to a dense tuple) is under-determined and
        // unconstructable, so coalesce emits a fresh `Type::Infer`. There
        // is no `ccl::Type` for a sparse-index product, so build the
        // `CompactType` directly (the input the solver would produce
        // internally).
        let mut rec = BTreeMap::new();
        rec.insert(
            FieldKey::Index(0),
            CompactType::from_atom(AtomKey::Prim(BaseType::Int)),
        );
        rec.insert(
            FieldKey::Index(2),
            CompactType::from_atom(AtomKey::Prim(BaseType::String)),
        );
        let graph = CompactGraph {
            term: CompactType {
                rec: Some(rec),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };
        let t = coalesce_compact(&graph).unwrap();
        assert!(matches!(t, Type::Infer(_)), "expected Infer, got {t:?}");
    }

    #[test]
    fn coalesce_var_with_one_lower_bound_at_positive_position() {
        // α : lower=[Int]. At positive, coalesces to Int.
        let v = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&prim(BaseType::Int), &v, &mut cache).unwrap();
        assert_eq!(
            coalesce_compact(&compact_type(&v)).unwrap(),
            Type::Base(BaseType::Int)
        );
    }

    #[test]
    fn coalesce_var_with_one_upper_bound_at_negative_position() {
        // α : upper=[Int]. compact_type at default polarity (positive
        // top-level) walks a Var's lower bounds; the opposite-polarity
        // fallback in compact_go pulls in upper bounds when lowers are
        // empty, so this still resolves to Int. Will tighten once
        // simplify_type lands.
        let v = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&v, &prim(BaseType::Int), &mut cache).unwrap();
        assert_eq!(
            coalesce_compact(&compact_type(&v)).unwrap(),
            Type::Base(BaseType::Int)
        );
    }

    #[test]
    fn coalesce_var_with_no_bounds_emits_infer() {
        let v = fresh_var(0);
        match coalesce_compact(&compact_type(&v)).unwrap() {
            Type::Infer(_) => {}
            other => panic!("expected Type::Infer, got {:?}", other),
        }
    }

    #[test]
    fn coalesce_var_with_incompatible_lowers_fails() {
        // α : lower=[Int, String]. The solver rejects unions — both
        // primitives flow into the atom set, and coalesce_compact
        // emits IncompatibleBounds when more than one concrete
        // contribution survives.
        let v = fresh_var(0);
        let mut cache = ConstrainCache::new();
        constrain_subtype(&prim(BaseType::Int), &v, &mut cache).unwrap();
        constrain_subtype(&prim(BaseType::String), &v, &mut cache).unwrap();
        assert!(matches!(
            coalesce_compact(&compact_type(&v)),
            Err(CoalesceError::IncompatibleBounds { .. })
        ));
    }

    #[test]
    fn coalesce_self_referential_var_emits_infer() {
        // α with α directly in its own lower bounds. compact_type's
        // `parents` filter treats this as a spurious cycle (no
        // structural intermediary), drops the bound, and
        // returns a CompactType containing just the variable. With no
        // concrete contributions, coalesce_compact emits Type::Infer.
        //
        // Real recursive bounds (α reachable from itself through a
        // structural intermediary, e.g. `α <: Fun(α, _)`) flow through
        // compact_type's structural recursion — a `Function` boundary
        // resets `parents` to empty, so re-encountering α at the same
        // polarity inside the Fun body triggers the
        // placeholder/RecursiveType path. One-way constraint emission
        // produces no such cycles today (even `λx. x x` types cleanly);
        // the path is defensive.
        let v = fresh_var(0);
        if let Type::Infer(state) = &v {
            state
                .bounds
                .borrow_mut()
                .lower_mut()
                .push(Bound::conc(v.clone()));
        }
        match coalesce_compact(&compact_type(&v)).unwrap() {
            Type::Infer(_) => {}
            other => panic!("expected Type::Infer for spurious self-cycle, got {other:?}"),
        }
    }

    #[test]
    fn distinct_refinements_survive_simplification() {
        // A record carrying two *different* refinements at two field
        // positions must round-trip through compact → simplify → coalesce
        // with both refinements intact (they are positional, not folded into a
        // variable identity, so co-occurrence analysis cannot merge them).
        let (p, q) = (1, 2);
        let ty = Type::Record(vec![
            ("a".to_string(), refined(prim(BaseType::Int), p)),
            ("b".to_string(), refined(prim(BaseType::Int), q)),
        ]);
        let out = coalesce_compact(&simplify_type(compact_type(&ty))).unwrap();
        assert_eq!(out, ty);
    }

    #[test]
    fn refinements_meeting_at_one_variable_do_not_depend_on_arrival_order() {
        // Two refined upper bounds meet at one variable. As nested layers the
        // result was `{{Int | q} | p}` or `{{Int | p} | q}` by which arrived
        // first; subtyping was indifferent either way (deficit matching compares
        // refinements as a set), but `Type`'s equality was not, and structural
        // equality is load-bearing where a type is an *identity*: the
        // trivial-equality short-circuit, cache keys, and the
        // recorded-vs-recomputed walls. One unordered set makes the two orders
        // build the same type, so this asserts plain equality rather than
        // equality after a canonical sort.
        let coalesce_with_order = |first: &Type, second: &Type| {
            let v = fresh_var(0);
            constrain_subtype(&v, first, &mut ConstrainCache::new()).unwrap();
            constrain_subtype(&v, second, &mut ConstrainCache::new()).unwrap();
            coalesce_compact(&simplify_type(compact_type(&v))).unwrap()
        };
        let (p, q) = (
            refined(prim(BaseType::Int), 1),
            refined(prim(BaseType::Int), 2),
        );
        let a = coalesce_with_order(&p, &q);
        let b = coalesce_with_order(&q, &p);
        assert_eq!(a, b, "refinements must not depend on arrival order");
        // Both survived: the meet of two refined upper bounds carries each
        // side's restriction, so this is a two-member set and not one order
        // winning.
        assert_eq!(
            a.refinements().len(),
            2,
            "expected both refinements, got {a}"
        );
        // Rendering is order-stable too, so a diagnostic cannot leak the order.
        assert_eq!(format!("{a}"), format!("{b}"));
    }

    #[test]
    fn var_constrained_to_refined_coalesces_refined() {
        // A fresh var equated to a refined type (both bounds) must coalesce
        // *carrying* the refinement, not drop it to the bare base. Solver-level
        // property: equality bounds may still arise (e.g. `bind_annotation`,
        // `require_eq` on list elements), so refinements must survive them.
        let p = 1;
        let v = fresh_var(0);
        let refined_int = refined(prim(BaseType::Int), p);
        let mut cache = ConstrainCache::new();
        // v ⟺ {Int | p}
        constrain_subtype(&v, &refined_int, &mut cache).unwrap();
        constrain_subtype(&refined_int, &v, &mut cache).unwrap();
        let out = coalesce_compact(&simplify_type(compact_type(&v))).unwrap();
        assert_eq!(
            out, refined_int,
            "var equated to {{Int|p}} lost its refinement"
        );
    }

    #[test]
    fn apply_index_var_coalesces_refined() {
        // Solver-level refinement-propagation property: an index var `v` equated
        // (both bounds) with the domain `dom` of a function shape that is
        // itself equated with `{d | p} ⇒ cod` (d ⟺ Int). The refinement `p` must
        // propagate through the var⇄var equality chain onto `v`'s coalesced
        // type, `{Int | p}` — refinements ride the lattice; they must not be
        // dropped at var merges.
        let p = 1;
        let d = fresh_var(0);
        let cod = fresh_var(0);
        let dom = fresh_var(0);
        let cap = fresh_var(0);
        let v = fresh_var(0);
        let mut cache = ConstrainCache::new();
        // d ⟺ Int
        constrain_subtype(&d, &prim(BaseType::Int), &mut cache).unwrap();
        constrain_subtype(&prim(BaseType::Int), &d, &mut cache).unwrap();
        // fn = {d|p} ⇒ cod
        let fn_ty = fun(refined(d.clone(), p), cod.clone());
        // as_function_eq: fn ⟺ dom ⇒ cap
        let shape = fun(dom.clone(), cap.clone());
        constrain_subtype(&fn_ty, &shape, &mut cache).unwrap();
        constrain_subtype(&shape, &fn_ty, &mut cache).unwrap();
        // constrain_argument(v, dom): two-way
        constrain_subtype(&v, &dom, &mut cache).unwrap();
        constrain_subtype(&dom, &v, &mut cache).unwrap();
        let out = coalesce_compact(&simplify_type(compact_type(&v))).unwrap();
        assert_eq!(
            out,
            refined(prim(BaseType::Int), p),
            "Apply index var lost its refinement"
        );
    }

    /// Coalesce a variant `Type` into `Type::Variant` with preserved tags.
    #[test]
    fn coalesce_variant_roundtrips_to_type_variant() {
        let v = variant([
            ("Some", prim(BaseType::Int)),
            ("None", prim(BaseType::Unit)),
        ]);
        let scheme = simplify_type(compact_type(&v));
        let ty = coalesce_compact(&scheme).expect("coalesce ok");
        match ty {
            Type::Variant(tags, _) => {
                let names: Vec<String> = tags.iter().map(|(n, _)| n.to_string()).collect();
                // BTreeMap iteration order is by FieldKey key — Name tags
                // sort lexicographically.
                assert_eq!(names, vec!["None", "Some"]);
            }
            other => panic!("expected Variant, got {other}"),
        }
    }
}
