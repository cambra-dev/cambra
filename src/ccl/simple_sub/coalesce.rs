//! Coalesce: materialize a [`CompactGraph`] back into a concrete
//! [`crate::ccl::Type`].
//!
//! The final step of the `compact` → `simplify` → `coalesce` pipeline. It
//! counts the concrete structural contributions remaining at each polarity
//! position and reads off a single `Type` (or raises a [`CoalesceError`] on a
//! primitive collision / under-determined shape / residual cycle).

use std::collections::BTreeMap;

use crate::ccl::{InferVar, InferVarId, Type};

use super::FieldKey;
use super::compact::{CompactGraph, CompactType};

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
        /// UIDs of the simple-sub variables that contributed these bounds.
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
    if let Some((name, dom, cod)) = &ct.fun {
        let d = coalesce_compact_go(dom, !polarity)?;
        let c = coalesce_compact_go(cod, polarity)?;
        // Strip the Pi binder unless the codomain's refinement predicates
        // actually reference it (design §3.2 / O10): keeps ordinary functions
        // `name: None` while a genuinely dependent codomain keeps its binder
        // bound.
        let kept_name = name
            .clone()
            .filter(|b| crate::ccl::subst::type_free_vars(&c).contains(b));
        shapes.push(Type::Fun {
            name: kept_name,
            domain: Box::new(d),
            codomain: Box::new(c),
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
    // and `iterate_type` both strip refinements at every depth and compose
    // the resulting `Restrict`s, so the wrap order is semantically
    // irrelevant; first-insertion order in the `Vec` makes it stable.
    let out = ct
        .refinements
        .iter()
        .fold(inner, |acc, r| Type::Refinement(Box::new(acc), r.clone()));
    Ok(out)
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
    use crate::ccl::simple_sub::compact::{AtomKey, CompactGraph, CompactType};
    use crate::ccl::simple_sub::test_helpers::{record, refined, variant};
    use crate::ccl::simple_sub::{
        ConstrainCache, FieldKey, compact_type, constrain_subtype, fresh_var, fun, prim,
        simplify_type,
    };
    use crate::ccl::{BaseType, Bound, Type};

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
                domain: Box::new(Type::Base(BaseType::Int)),
                codomain: Box::new(Type::Base(BaseType::Bool))
            }
        );
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
