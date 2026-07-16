//! Coalesce: materialize a [`CompactGraph`] back into a concrete
//! [`crate::ccl::Type`].
//!
//! The final step of the `compact` → `simplify` → `coalesce` pipeline. It
//! counts the concrete structural contributions remaining at each polarity
//! position and reads off a single `Type` (or raises a [`CoalesceError`] on a
//! primitive collision / under-determined shape / residual cycle).

use std::collections::BTreeMap;

use crate::ccl::{HistoryKind, InferVar, InferVarId, Type};

use super::compact::{CompactGraph, CompactType};
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
    /// A data function carrying ≥ 2 candidate extents (a Σ) met a compute
    /// function at a positive join, so collapsing to the ordinary meet would
    /// drop extents. Reported loudly rather than silently losing data (no
    /// current program produces this shape). See `design/type-inference.md`
    /// §4.6.
    ExtentJoinConflict {
        /// Pretty representation of the conflicting function shapes.
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
        shapes.push(materialize_record(rec, polarity)?);
    }
    if let Some(var) = &ct.var {
        shapes.push(materialize_variant(var, polarity)?);
    }
    if let Some(cf) = &ct.fun {
        use super::compact::KindMerge;
        // Materialize the codomain once (covariant), and each domain
        // alternative (contravariant), deduplicating at the `Type` level —
        // this catches var-level equalities that the compact-time
        // `CompactType ==` dedup in `sigma_join` missed (simplify may have
        // merged uids after compaction).
        let c = coalesce_compact_go(&cf.codomain, polarity)?;
        let mut doms: Vec<Type> = Vec::new();
        for d in &cf.domains {
            let dt = coalesce_compact_go(d, !polarity)?;
            if !doms.contains(&dt) {
                doms.push(dt);
            }
        }
        // Strip the Pi binder unless the codomain's refinement predicates
        // actually reference it (design §3.2 / O10): keeps ordinary functions
        // `name: None` while a genuinely dependent codomain keeps its binder.
        let kept_name = cf
            .name
            .clone()
            .filter(|b| crate::ccl::subst::type_free_vars(&c).contains(b));
        match cf.kind {
            KindMerge::Conflict => {
                let doms_s = doms
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(" ⊔ ");
                return Err(CoalesceError::ExtentJoinConflict {
                    details: format!(
                        "data function over {{{doms_s}}} joined with a compute function"
                    ),
                });
            }
            KindMerge::Compute => {
                debug_assert_eq!(doms.len(), 1, "compute fun accumulated domain alternatives");
                shapes.push(Type::Fun {
                    name: kept_name,
                    kind: crate::ccl::ty::FunKind::Compute,
                    domain: Box::new(doms.into_iter().next().expect("compute fun has one domain")),
                    codomain: Box::new(c),
                });
            }
            KindMerge::Data => {
                if doms.len() == 1 {
                    // Idempotence: a single surviving extent is a plain data fun.
                    shapes.push(Type::Fun {
                        name: kept_name,
                        kind: crate::ccl::ty::FunKind::Data,
                        domain: Box::new(doms.into_iter().next().expect("len == 1")),
                        codomain: Box::new(c),
                    });
                } else {
                    // ≥ 2 extents: a Σ. The witness is kept only if a codomain
                    // predicate references it — nothing mints such a predicate
                    // yet, so it is always `None` here (dormant machinery).
                    //
                    // Materialization invariant: the choices are ground extents.
                    // The Σ<:Σ constrain rule matches choices by exact structural
                    // `==` while `compact_go`/`extrude` treat them contravariantly
                    // (at `!pol`); those two treatments only agree while a choice
                    // carries no inference variable, so an `Infer`-bearing choice
                    // would record a bound at the wrong polarity relative to how
                    // constrain compares it. Enforce the invariant the rules rely on.
                    debug_assert!(
                        !doms.iter().any(crate::ccl::subst::type_contains_infer),
                        "Σ materialized with an inference variable in a choice extent"
                    );
                    shapes.push(Type::sigma(None, doms, kept_name, c));
                }
            }
        }
    }
    if let Some((value, domain, kind)) = &ct.history_slot {
        // Both children materialize at the same polarity (invariant — both
        // directions were resolved at constraint time). The `kind` rides through
        // from compaction so a feed rebuilds as a feed, a store as a store.
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
            // survives.
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
            // past PR1. Collection arms still join losslessly — that happens in
            // the `fun` slot above (`sigma_join` → Σ), not through atoms.
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

    // Re-wrap the refinement witnesses carried at this position. `extent_of`
    // strips refinements at every depth and composes the resulting
    // `Restrict`s, so the wrap order is semantically irrelevant;
    // first-insertion order in the `Vec` makes it stable.
    let out = ct
        .refinements
        .iter()
        .fold(inner, |acc, r| Type::Refinement(Box::new(acc), r.clone()));
    Ok(out)
}

/// Dissolve a position's feed `history_slot` into its other contributions when
/// both are present — see the transparent-read comment in [`coalesce_compact_go`].
///
/// This performs at most one merge per position: reconstructing the channel as a
/// `fun`-slot type and merging it leaves `history_slot` empty, so the loop
/// exits. A *chained* defer read (a feed handle nested in the payload) rides
/// inside the merged `fun` codomain and is resolved by ordinary recursion in
/// [`coalesce_compact_go`], not by re-entering here. A `store` slot, or a lone
/// feed with no other content, is left intact. The `while` form is a defensive
/// fixpoint; the body never re-arms `history_slot`.
fn dissolve_read_feeds(mut ct: CompactType, polarity: bool) -> CompactType {
    while let Some((value, domain, kind)) = ct.history_slot.take() {
        // Only a *feed channel* dissolves into a read view; a store is read as
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
        let chan = CompactType {
            fun: Some(super::compact::CompactFun {
                name: None,
                // A feed's read view is a collection stream: a data function.
                kind: super::compact::KindMerge::Data,
                domains: vec![*domain],
                codomain: value,
            }),
            ..Default::default()
        };
        ct = CompactType::merge(polarity, ct, chan);
    }
    ct
}

/// Materialize a variant-tag map into [`Type::Variant`], preserving tag
/// order by name (BTreeMap iterates in key order, so output is stable).
/// Payloads coalesce at the same polarity as the outer (covariant depth).
fn materialize_variant(
    tags: &BTreeMap<FieldKey, CompactType>,
    polarity: bool,
) -> Result<Type, CoalesceError> {
    let mut out = Vec::with_capacity(tags.len());
    for (k, v) in tags {
        out.push((k.clone(), coalesce_compact_go(v, polarity)?));
    }
    Ok(Type::Variant(out))
}

fn materialize_record(
    rec: &BTreeMap<FieldKey, CompactType>,
    polarity: bool,
) -> Result<Type, CoalesceError> {
    if rec.is_empty() {
        return Ok(Type::Tuple(Vec::new()));
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
    fn coalesce_two_data_extents_form_sigma() {
        use crate::ccl::infer::solver::compact::{CompactFun, KindMerge};
        // A `Data` fun slot carrying two distinct extents with a shared `Int`
        // codomain coalesces to `Σ{[0,1], [0,2]} ⤇ Int` (dormant until PR1
        // commit 3 wires the introduction sites, but the materialization is
        // load-bearing here).
        let graph = CompactGraph {
            term: CompactType {
                fun: Some(CompactFun {
                    name: None,
                    kind: KindMerge::Data,
                    domains: vec![
                        compact_type(&Type::UIntRange(2)).term,
                        compact_type(&Type::UIntRange(3)).term,
                    ],
                    codomain: Box::new(compact_type(&prim(BaseType::Int)).term),
                }),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };
        assert_eq!(
            coalesce_compact(&graph).unwrap(),
            Type::sigma(
                None,
                vec![Type::UIntRange(2), Type::UIntRange(3)],
                None,
                Type::Base(BaseType::Int),
            )
        );
    }

    #[test]
    fn coalesce_single_data_extent_is_plain_data_fun() {
        use crate::ccl::infer::solver::compact::{CompactFun, KindMerge};
        // One surviving extent collapses to a plain `Data` fun (idempotence:
        // `xs if c else xs` types as `xs`).
        let graph = CompactGraph {
            term: CompactType {
                fun: Some(CompactFun {
                    name: None,
                    kind: KindMerge::Data,
                    domains: vec![compact_type(&Type::UIntRange(2)).term],
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
    fn coalesce_duplicate_data_extents_dedup_to_plain_fun() {
        use crate::ccl::infer::solver::compact::{CompactFun, KindMerge};
        // Two structurally-equal extents dedup to one → a plain `Data` fun, not
        // a spurious 2-choice Σ.
        let graph = CompactGraph {
            term: CompactType {
                fun: Some(CompactFun {
                    name: None,
                    kind: KindMerge::Data,
                    domains: vec![
                        compact_type(&Type::UIntRange(2)).term,
                        compact_type(&Type::UIntRange(2)).term,
                    ],
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
    fn coalesce_extent_join_conflict_errs() {
        use crate::ccl::infer::solver::compact::{CompactFun, KindMerge};
        // A `Conflict` kind (a Σ met a compute function) is a loud coalesce
        // error, never a silent extent drop.
        let graph = CompactGraph {
            term: CompactType {
                fun: Some(CompactFun {
                    name: None,
                    kind: KindMerge::Conflict,
                    domains: vec![
                        compact_type(&Type::UIntRange(2)).term,
                        compact_type(&Type::UIntRange(3)).term,
                    ],
                    codomain: Box::new(compact_type(&prim(BaseType::Int)).term),
                }),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };
        assert!(matches!(
            coalesce_compact(&graph),
            Err(CoalesceError::ExtentJoinConflict { .. })
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
            state.bounds.borrow_mut().lower.push(Bound::conc(v.clone()));
        }
        match coalesce_compact(&compact_type(&v)).unwrap() {
            Type::Infer(_) => {}
            other => panic!("expected Type::Infer for spurious self-cycle, got {other:?}"),
        }
    }

    #[test]
    fn distinct_refinements_survive_simplification() {
        // A record carrying two *different* refinement witnesses at two field
        // positions must round-trip through compact → simplify → coalesce
        // with both witnesses intact (they are positional, not folded into a
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
    fn var_constrained_to_refined_coalesces_refined() {
        // A fresh var equated to a refined type (both bounds) must coalesce
        // *carrying* the refinement, not drop it to the bare base. Solver-level
        // property: equality bounds may still arise (e.g. `bind_annotation`,
        // `require_eq` on list elements), so witnesses must survive them.
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
            "var equated to {{Int|p}} lost its witness"
        );
    }

    #[test]
    fn apply_index_var_coalesces_refined() {
        // Solver-level witness-propagation property: an index var `v` equated
        // (both bounds) with the domain `dom` of a function shape that is
        // itself equated with `{d | p} ⇒ cod` (d ⟺ Int). The witness `p` must
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
            "Apply index var lost its witness"
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
            Type::Variant(tags) => {
                let names: Vec<String> = tags.iter().map(|(n, _)| n.to_string()).collect();
                // BTreeMap iteration order is by FieldKey key — Name tags
                // sort lexicographically.
                assert_eq!(names, vec!["None", "Some"]);
            }
            other => panic!("expected Variant, got {other}"),
        }
    }
}
