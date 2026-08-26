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
    /// A data-function join whose domain alternatives survive materialization as
    /// distinct domains, so no single domain holds every arm's rows. Raised either
    /// by a `Data ⊔ Data` join (the common case) or by a multi-alternative slot
    /// meeting a compute function, where collapsing to the ordinary meet would drop
    /// domains. Reported loudly rather than silently losing rows. See
    /// `src/ccl/design/type-inference.md`, "The domain join is a Σ".
    DomainJoinConflict {
        /// Pretty representation of the conflicting function shapes.
        details: String,
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
    coalesce_compact_go(&graph.term, true)
}

fn coalesce_compact_go(ct: &CompactType, polarity: bool) -> Result<Type, CoalesceError> {
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
    let mut atoms: Vec<Type> = ct.atoms.iter().map(|a| a.to_type()).collect();
    let mut shapes: Vec<Type> = Vec::new();

    if let Some(rec) = &ct.rec {
        let vars: Vec<InferVarId> = ct.vars.iter().copied().collect();
        shapes.push(materialize_record(rec, polarity, &vars)?);
    }
    if let Some(var) = &ct.var {
        shapes.push(materialize_variant(var, polarity)?);
    }
    if let Some(cf) = &ct.fun {
        use super::compact::KindMerge;
        // Materialize the codomain once (covariant), then read the domain
        // alternatives a positive join accumulated under the *resolved* kind — the
        // one place that reading is available, which is why `CompactFun::merge`
        // does not take it (see there).
        //
        // A compute function has one domain: its alternatives meet
        // contravariantly, and the meet runs in compact space, before
        // materialization, because that is where a meet is defined. A `Data`
        // domain *is* the data, so its alternatives never meet — they are
        // materialized and deduplicated at the `Type` level, which is where the
        // "same domain or not?" question is actually decided: the compact-time
        // `CompactType ==` dedup in `DomainSet` cannot settle it, because a
        // compact domain still carries variable identity that `simplify_type` may
        // merge afterwards, so two identical domains can arrive as two
        // alternatives. A conflicted slot keeps every alternative for its
        // diagnostic.
        let c = coalesce_compact_go(&cf.codomain, polarity)?;
        let mut doms: Vec<Type> = Vec::new();
        match cf.kind {
            KindMerge::Compute | KindMerge::Unknown => {
                if let Some(met) = cf
                    .domains
                    .iter()
                    .cloned()
                    .reduce(|acc, d| CompactType::merge(!polarity, acc, d))
                {
                    doms.push(coalesce_compact_go(&met, !polarity)?);
                }
            }
            KindMerge::Data | KindMerge::Conflict => {
                for d in &cf.domains {
                    let dt = coalesce_compact_go(d, !polarity)?;
                    if !doms.contains(&dt) {
                        doms.push(dt);
                    }
                }
            }
        }
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
        match cf.kind {
            KindMerge::Conflict => {
                let doms_s = doms
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(" ⊔ ");
                // A single surviving domain means one function slot whose kind
                // resolved contradictorily — one kind variable pinned to both
                // points, the coalesce-time face of a `KindMismatch`.
                // Two or more surviving domains mean a data function's domains
                // would be dropped by collapsing to a compute meet (a genuine
                // domain-join collision). See `src/ccl/design/type-inference.md`,
                // "The domain join is a Σ".
                if doms.len() <= 1 {
                    return Err(CoalesceError::KindConflict {
                        details: format!("a compute function (capability) over {{{doms_s}}}"),
                    });
                }
                return Err(CoalesceError::DomainJoinConflict {
                    details: format!("a data function over {{{doms_s}}}"),
                });
            }
            // Nothing pinned this kind, so the capability default applies — the
            // same shape as `Compute` below, decided here rather than at the
            // merge, where "unrequired" still had to stay distinct from
            // "required to be a capability" (`KindMerge::Unknown`).
            KindMerge::Unknown | KindMerge::Compute => {
                debug_assert_eq!(
                    doms.len(),
                    1,
                    "the compute reading met its alternatives above"
                );
                shapes.push(Type::Fun {
                    name: kept_name,
                    kind: crate::ccl::ty::FunKind::Compute,
                    domain: Box::new(doms.into_iter().next().expect("compute fun has one domain")),
                    codomain: Box::new(c),
                });
            }
            KindMerge::Data => {
                // One surviving alternative: they reconciled, so the join loses
                // nothing and this is a plain data function. `xs if c else xs` types
                // as `xs`, and so does any join whose arms turn out to share an
                // domain once their domains are materialized.
                let [dom] = <[Type; 1]>::try_from(doms).map_err(|doms: Vec<Type>| {
                    // Two or more: the arms hold different domains, and a
                    // collection's domain *is* its data, so no single domain holds
                    // both arms' rows. The contravariant meet the compute lattice
                    // would take here drops whichever rows the narrower domain
                    // lacks; refusing is what the `Data` kind buys. The lossless
                    // answer — a dependent sum over the candidate domains — is the
                    // collections work.
                    let doms_s = doms
                        .iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    CoalesceError::DomainJoinConflict {
                        details: format!(
                            "collections over the distinct domains {{{doms_s}}} join at none \
                             of them without losing rows"
                        ),
                    }
                })?;
                shapes.push(Type::Fun {
                    name: kept_name,
                    kind: crate::ccl::ty::FunKind::Data,
                    domain: Box::new(dom),
                    codomain: Box::new(c),
                });
            }
        }
    }
    if let Some((value, domain, kind)) = &ct.history_slot {
        // Both children materialize at the same polarity (invariant — both
        // directions were resolved at constraint time). The `kind` rides through
        // from compaction so a feed rebuilds as a feed, a mutable variable as a mutable variable.
        shapes.push(Type::History {
            value: Box::new(coalesce_compact_go(value, polarity)?),
            domain: Box::new(coalesce_compact_go(domain, polarity)?),
            kind: *kind,
        });
    }

    let mut all = Vec::new();
    all.append(&mut atoms);
    all.append(&mut shapes);

    let inner = match all.len() {
        0 => {
            // No concrete contribution; emit a fresh Infer slot.
            // check_fully_typed reports it as UnresolvedInfer if it
            // survives. Scope-free: the slot is an error placeholder that
            // never takes a bound, so it has no telescope to close against.
            Type::Infer(InferVar::fresh(0))
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
            // the `fun` slot above (`DomainSet::union`), not through atoms.
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
    Ok(Type::refined(
        inner,
        ct.refinements.clone().unwrap_or_default(),
    ))
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
                // A feed's read view is a collection stream: a data function.
                kind: super::compact::KindMerge::Data,
                domains: super::compact::DomainSet::one(*domain),
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
fn materialize_variant(variant: &CompactVariant, polarity: bool) -> Result<Type, CoalesceError> {
    let mut out = Vec::with_capacity(variant.tags.len());
    for (k, v) in &variant.tags {
        out.push((k.clone(), coalesce_compact_go(v, polarity)?));
    }
    Ok(Type::Variant(out, variant.openness))
}

fn materialize_record(
    rec: &BTreeMap<FieldKey, CompactType>,
    polarity: bool,
    vars: &[InferVarId],
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
                out.push(coalesce_compact_go(v, polarity)?);
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
                coalesce_compact_go(v, polarity)?;
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
            out.push((name, coalesce_compact_go(v, polarity)?));
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
    fn coalesce_function_preserves_shape() {
        let s = fun(prim(BaseType::Int), prim(BaseType::Bool));
        let t = coalesce_compact(&compact_type(&s)).unwrap();
        assert_eq!(
            t,
            Type::Fun {
                name: None,
                kind: crate::ccl::ty::FunKind::Compute,
                domain: Box::new(Type::Base(BaseType::Int)),
                codomain: Box::new(Type::Base(BaseType::Bool))
            }
        );
    }

    #[test]
    fn coalesce_two_data_domains_is_a_join_conflict() {
        use crate::ccl::infer::solver::compact::{CompactFun, KindMerge};
        // A `Data` fun slot whose two alternatives survive materialization as
        // distinct domains has no lossless single domain, so it is rejected here
        // rather than narrowed to a meet.
        let graph = CompactGraph {
            term: CompactType {
                fun: Some(CompactFun {
                    name: None,
                    kind: KindMerge::Data,
                    domains: [
                        compact_type(&Type::UIntRange(2)).term,
                        compact_type(&Type::UIntRange(3)).term,
                    ]
                    .into_iter()
                    .collect(),
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
    fn coalesce_single_data_domain_is_plain_data_fun() {
        use crate::ccl::infer::solver::compact::{CompactFun, KindMerge};
        // One surviving domain collapses to a plain `Data` fun (idempotence:
        // `xs if c else xs` types as `xs`).
        let graph = CompactGraph {
            term: CompactType {
                fun: Some(CompactFun {
                    name: None,
                    kind: KindMerge::Data,
                    domains: [compact_type(&Type::UIntRange(2)).term]
                        .into_iter()
                        .collect(),
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
                kind: crate::ccl::ty::FunKind::Data,
                domain: Box::new(Type::UIntRange(2)),
                codomain: Box::new(Type::Base(BaseType::Int)),
            }
        );
    }

    #[test]
    fn coalesce_duplicate_data_domains_dedup_to_plain_fun() {
        use crate::ccl::infer::solver::compact::{CompactFun, KindMerge};
        // Two structurally-equal domains dedup to one → a plain `Data` fun, not
        // a spurious 2-choice conditional collection.
        let graph = CompactGraph {
            term: CompactType {
                fun: Some(CompactFun {
                    name: None,
                    kind: KindMerge::Data,
                    domains: [
                        compact_type(&Type::UIntRange(2)).term,
                        compact_type(&Type::UIntRange(2)).term,
                    ]
                    .into_iter()
                    .collect(),
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
                kind: crate::ccl::ty::FunKind::Data,
                domain: Box::new(Type::UIntRange(2)),
                codomain: Box::new(Type::Base(BaseType::Int)),
            }
        );
    }

    #[test]
    fn coalesce_domain_join_conflict_errs() {
        use crate::ccl::infer::solver::compact::{CompactFun, KindMerge};
        // A `Conflict` kind (a multi-domain data function met a compute function) is
        // a loud coalesce error, never a silent domain drop.
        let graph = CompactGraph {
            term: CompactType {
                fun: Some(CompactFun {
                    name: None,
                    kind: KindMerge::Conflict,
                    domains: [
                        compact_type(&Type::UIntRange(2)).term,
                        compact_type(&Type::UIntRange(3)).term,
                    ]
                    .into_iter()
                    .collect(),
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
        use crate::ccl::infer::solver::compact::{CompactFun, KindMerge};
        // A `Conflict` over a *single* domain is one function slot demanded as a
        // data domain while being a compute capability — the coalesce-time face
        // of a kind conflict, reported as `KindConflict` rather
        // than the multi-domain `DomainJoinConflict`.
        let graph = CompactGraph {
            term: CompactType {
                fun: Some(CompactFun {
                    name: None,
                    kind: KindMerge::Conflict,
                    domains: [compact_type(&prim(BaseType::Int)).term]
                        .into_iter()
                        .collect(),
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
