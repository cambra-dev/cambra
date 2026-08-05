//! Type simplification: polar co-occurrence analysis.
//!
//! [`simplify_type`] sits between [`super::compact::compact_type`] and
//! [`super::coalesce::coalesce_compact`], merging or dropping inference
//! variables that carry no information (polar-only, co-occurring, or
//! atom-absorbed). It operates on the shared [`CompactGraph`] currency
//! defined in [`super::compact`].
//!
//! Named `simplify_type` to distinguish it from the top-level
//! [`crate::ccl::simplify`] pass, which operates on the AST.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::ccl::InferVarId;

use super::compact::{AtomKey, CompactFun, CompactGraph, CompactType};

// ---------------------------------------------------------------------------
// Type simplification: co-occurrence analysis
// ---------------------------------------------------------------------------

/// An item that can appear in a co-occurrence set during [`simplify_type`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CoOccItem {
    Var(InferVarId),
    Atom(AtomKey),
}

/// Simplify a [`CompactGraph`] by per-polarity co-occurrence analysis.
///
/// Two simplifications:
///
/// 1. **Polar-only elimination.** A variable that appears at only one
///    polarity contributes no structural information (any concrete value
///    filling the one polarity is unconstrained on the other side). It is
///    dropped: its position becomes empty, which coalesces to `Type::Infer`.
///
/// 2. **Co-occurrence merging.** If variable `v` always appears together with
///    variable `w` at a given polarity, and symmetrically `w` always appears
///    with `v`, they carry identical information and `w` can be merged into
///    `v`. Only non-recursive variables are merged with non-recursive ones,
///    and recursive with recursive (mixing would violate strict polarity for
///    recursive types).
///
/// 3. **Atomic absorption.** If atom `A` co-occurs with variable `v` at both
///    polarities, `v` is "sandwiched" between two structural `A` constraints
///    and is redundant; it is dropped.
///
/// The operation is currently cosmetic (all types are monomorphic) but
/// becomes load-bearing once let-polymorphism introduces genuine polar
/// asymmetry. It is placed between
/// [`compact_type`](super::compact::compact_type) and
/// [`coalesce_compact`](super::coalesce::coalesce_compact) in the pipeline.
///
/// **Refinements need no special handling here.** Refinements live on
/// each [`CompactType`] *position* (`ct.refinements`), not on variable
/// identity, and [`simplify_reconstruct`] copies them through unchanged while
/// `var_subst` only ever rewrites or drops variable uids. Co-occurring
/// variables (the merge candidates) sit in the same position and therefore
/// carry the same refinements, so merging or eliminating a variable can never move
/// or lose a refinement. (The classic "merge x>0 with x<10" hazard applies
/// only to representations that fold the predicate into the variable's
/// identity; ours keeps them positional.)
///
/// Recursive variables: the solver never produces non-empty `rec_vars`
/// today, so the recursive-variable merge path is guarded but remains
/// unexercised until recursive types are supported.
pub fn simplify_type(cty: CompactGraph) -> CompactGraph {
    // All variable UIDs encountered during the walk.
    let mut all_vars: BTreeSet<InferVarId> = cty.rec_vars.keys().cloned().collect();
    // Guards against re-entering a rec-var bound during analysis.
    let mut rec_processed: BTreeSet<InferVarId> = BTreeSet::new();
    // co_occurrences[(pol, uid)] = set of items that ALWAYS co-occur with uid at polarity pol.
    let mut co_occurrences: HashMap<(bool, InferVarId), HashSet<CoOccItem>> = HashMap::new();

    // Phase 1: analysis — walk the term, collecting co-occurrence sets.
    simplify_analyze(
        &cty.term,
        true,
        &cty.rec_vars,
        &mut all_vars,
        &mut rec_processed,
        &mut co_occurrences,
    );

    // Phase 2: decision — determine substitutions.
    let mut var_subst: HashMap<InferVarId, Option<InferVarId>> = HashMap::new();

    // Eliminate polar-only non-recursive variables.
    for &v in &all_vars {
        if !cty.rec_vars.contains_key(&v) {
            let has_pos = co_occurrences.contains_key(&(true, v));
            let has_neg = co_occurrences.contains_key(&(false, v));
            if has_pos != has_neg {
                var_subst.insert(v, None);
            }
        }
    }

    // Unify co-occurring variables; absorb atom-sandwiched variables.
    let all_vars_vec: Vec<InferVarId> = all_vars.iter().cloned().collect();
    for &v in &all_vars_vec {
        if var_subst.contains_key(&v) {
            continue;
        }
        for pol in [true, false] {
            let occs: Vec<CoOccItem> = co_occurrences
                .get(&(pol, v))
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .collect();
            for item in occs {
                if var_subst.contains_key(&v) {
                    break; // v was just eliminated; stop processing
                }
                match item {
                    CoOccItem::Var(w) if w != v && !var_subst.contains_key(&w) => {
                        // Only merge rec↔rec or non-rec↔non-rec.
                        if cty.rec_vars.contains_key(&v) != cty.rec_vars.contains_key(&w) {
                            continue;
                        }
                        // Merge w into v when v always co-occurs in w's set at pol.
                        let v_in_w = co_occurrences
                            .get(&(pol, w))
                            .map(|s| s.contains(&CoOccItem::Var(v)))
                            .unwrap_or(false);
                        if v_in_w {
                            var_subst.insert(w, Some(v));
                            if cty.rec_vars.contains_key(&w) {
                                // Both recursive: rec-bound merging deferred until recursive types land.
                                // (Never reached today — rec_vars is always empty.)
                            } else {
                                // Non-recursive: intersect v's !pol co-occs with w's !pol co-occs.
                                let w_neg: HashSet<CoOccItem> =
                                    co_occurrences.get(&(!pol, w)).cloned().unwrap_or_default();
                                if let Some(v_neg) = co_occurrences.get_mut(&(!pol, v)) {
                                    v_neg.retain(|t| *t == CoOccItem::Var(v) || w_neg.contains(t));
                                }
                            }
                        }
                    }
                    CoOccItem::Atom(ref atom) => {
                        // v is sandwiched: atom co-occurs with v at both polarities.
                        let neg_has_atom = co_occurrences
                            .get(&(!pol, v))
                            .map(|s| s.contains(&CoOccItem::Atom(atom.clone())))
                            .unwrap_or(false);
                        if neg_has_atom {
                            var_subst.insert(v, None);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    // Phase 3: reconstruction — apply var_subst to the term and rec_var bounds.
    let new_rec_vars: BTreeMap<InferVarId, CompactType> = cty
        .rec_vars
        .iter()
        .filter(|&(&uid, _)| !var_subst.contains_key(&uid))
        .map(|(&uid, bound)| (uid, simplify_reconstruct(bound.clone(), &var_subst)))
        .collect();

    CompactGraph {
        term: simplify_reconstruct(cty.term, &var_subst),
        rec_vars: new_rec_vars,
    }
}

/// Walk a [`CompactType`], recording per-polarity co-occurrences for each variable.
///
/// At each position, the co-occurrence set for variable `v` is intersected
/// with the set of items present at that position. This implements the
/// "always appears with" invariant: after a full walk, `co_occurrences[(pol,
/// v)]` contains only items that appeared alongside `v` every time `v` was
/// seen at polarity `pol`.
fn simplify_analyze(
    ct: &CompactType,
    pol: bool,
    input_rec_vars: &BTreeMap<InferVarId, CompactType>,
    all_vars: &mut BTreeSet<InferVarId>,
    rec_processed: &mut BTreeSet<InferVarId>,
    co_occurrences: &mut HashMap<(bool, InferVarId), HashSet<CoOccItem>>,
) {
    // Items present at this position (vars + atoms).
    let here: HashSet<CoOccItem> = ct
        .vars
        .iter()
        .map(|&v| CoOccItem::Var(v))
        .chain(ct.atoms.iter().map(|a| CoOccItem::Atom(a.clone())))
        .collect();

    for &tv in &ct.vars {
        all_vars.insert(tv);
        // Intersect existing co-occurrence set with items here, or initialize it.
        match co_occurrences.entry((pol, tv)) {
            std::collections::hash_map::Entry::Occupied(mut e) => {
                e.get_mut().retain(|x| here.contains(x));
            }
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(here.clone());
            }
        }
        // If tv has a recursive bound in the input, process it once (guards cycles).
        if let Some(bound) = input_rec_vars.get(&tv)
            && rec_processed.insert(tv)
        {
            simplify_analyze(
                bound,
                pol,
                input_rec_vars,
                all_vars,
                rec_processed,
                co_occurrences,
            );
        }
    }

    // Recurse into record fields (same polarity) and function (flip domain polarity).
    if let Some(fields) = &ct.rec {
        for v in fields.values() {
            simplify_analyze(
                v,
                pol,
                input_rec_vars,
                all_vars,
                rec_processed,
                co_occurrences,
            );
        }
    }
    // Variant payloads recurse at the same polarity (covariant depth),
    // matching how records' payloads behave.
    if let Some(tags) = &ct.var {
        for v in tags.values() {
            simplify_analyze(
                v,
                pol,
                input_rec_vars,
                all_vars,
                rec_processed,
                co_occurrences,
            );
        }
    }
    if let Some(cf) = &ct.fun {
        for dom in &cf.domains {
            simplify_analyze(
                dom,
                !pol,
                input_rec_vars,
                all_vars,
                rec_processed,
                co_occurrences,
            );
        }
        simplify_analyze(
            &cf.codomain,
            pol,
            input_rec_vars,
            all_vars,
            rec_processed,
            co_occurrences,
        );
    }
    // A history's children (value + domain) recurse at the same polarity
    // (invariant payload, materialization-only depth; see
    // `CompactType::history_slot`).
    if let Some((value, domain, _)) = &ct.history_slot {
        simplify_analyze(
            value,
            pol,
            input_rec_vars,
            all_vars,
            rec_processed,
            co_occurrences,
        );
        simplify_analyze(
            domain,
            pol,
            input_rec_vars,
            all_vars,
            rec_processed,
            co_occurrences,
        );
    }
}

/// Apply `var_subst` to a [`CompactType`], producing the simplified version.
fn simplify_reconstruct(
    ct: CompactType,
    var_subst: &HashMap<InferVarId, Option<InferVarId>>,
) -> CompactType {
    let new_vars: BTreeSet<InferVarId> = ct
        .vars
        .iter()
        .flat_map(|&tv| match var_subst.get(&tv) {
            Some(Some(w)) => Some(*w), // replaced by w
            Some(None) => None,        // eliminated
            None => Some(tv),          // unchanged
        })
        .collect();

    let new_rec = ct.rec.map(|fields| {
        fields
            .into_iter()
            .map(|(k, v)| (k, simplify_reconstruct(v, var_subst)))
            .collect()
    });

    let new_var = ct.var.map(|tags| {
        tags.into_iter()
            .map(|(k, v)| (k, simplify_reconstruct(v, var_subst)))
            .collect()
    });

    let new_fun = ct.fun.map(|cf| CompactFun {
        name: cf.name,
        kind: cf.kind,
        domains: cf
            .domains
            .into_iter()
            .map(|d| simplify_reconstruct(d, var_subst))
            .collect(),
        codomain: Box::new(simplify_reconstruct(*cf.codomain, var_subst)),
    });

    let new_history_slot = ct.history_slot.map(|(value, domain, kind)| {
        (
            Box::new(simplify_reconstruct(*value, var_subst)),
            Box::new(simplify_reconstruct(*domain, var_subst)),
            kind,
        )
    });

    CompactType {
        vars: new_vars,
        atoms: ct.atoms,
        rec: new_rec,
        var: new_var,
        fun: new_fun,
        refinements: ct.refinements,
        history_slot: new_history_slot,
    }
}

#[cfg(test)]
mod tests {
    use super::super::compact::KindMerge;
    use super::*;
    use crate::ccl::{BaseType, InferVar};

    /// A single-domain compute `fun` slot, for the simplify tests below.
    fn compute_fun(dom: CompactType, cod: CompactType) -> Option<CompactFun> {
        Some(CompactFun {
            name: None,
            kind: KindMerge::Compute,
            domains: vec![dom],
            codomain: Box::new(cod),
        })
    }

    /// Build a fresh [`InferVarId`] for use in hand-constructed CompactTypes.
    fn fresh_uid() -> InferVarId {
        InferVar::fresh(0).uid
    }

    #[test]
    fn simplify_polar_only_elimination() {
        // term: Fun(dom={a}, cod={a,b})
        // b appears only at positive polarity (cod) → eliminated.
        // a appears at both → kept.
        let uid_a = fresh_uid();
        let uid_b = fresh_uid();

        let dom = CompactType {
            vars: [uid_a].into_iter().collect(),
            ..Default::default()
        };
        let cod = CompactType {
            vars: [uid_a, uid_b].into_iter().collect(),
            ..Default::default()
        };
        let graph = CompactGraph {
            term: CompactType {
                fun: compute_fun(dom, cod),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };

        let simplified = simplify_type(graph);
        let cf = simplified.term.fun.unwrap();
        let dom_s = &cf.domains[0];
        let cod_s = &cf.codomain;
        assert!(dom_s.vars.contains(&uid_a), "a kept in dom");
        assert!(cod_s.vars.contains(&uid_a), "a kept in cod");
        assert!(!cod_s.vars.contains(&uid_b), "b eliminated from cod");
    }

    #[test]
    fn simplify_atomic_absorption() {
        // term: Fun(dom={a,Int}, cod={a,Int})
        // Int co-occurs with a at both polarities → a is sandwiched and eliminated.
        let uid_a = fresh_uid();
        let int_key = AtomKey::Prim(BaseType::Int);

        let make_side = |vars: BTreeSet<InferVarId>| CompactType {
            vars,
            atoms: [int_key.clone()].into_iter().collect(),
            ..Default::default()
        };
        let graph = CompactGraph {
            term: CompactType {
                fun: compute_fun(
                    make_side([uid_a].into_iter().collect()),
                    make_side([uid_a].into_iter().collect()),
                ),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };

        let simplified = simplify_type(graph);
        let cf = simplified.term.fun.unwrap();
        let dom_s = &cf.domains[0];
        let cod_s = &cf.codomain;
        assert!(dom_s.vars.is_empty(), "a absorbed in dom");
        assert!(cod_s.vars.is_empty(), "a absorbed in cod");
        assert!(dom_s.atoms.contains(&int_key), "Int remains in dom");
        assert!(cod_s.atoms.contains(&int_key), "Int remains in cod");
    }

    #[test]
    fn simplify_co_occurrence_merge() {
        // term: Fun(dom={a,b}, cod={a,b})
        // a and b always appear together at both polarities → one merged into the other.
        let uid_a = fresh_uid();
        let uid_b = fresh_uid();
        let both: BTreeSet<InferVarId> = [uid_a, uid_b].into_iter().collect();

        let graph = CompactGraph {
            term: CompactType {
                fun: compute_fun(
                    CompactType {
                        vars: both.clone(),
                        ..Default::default()
                    },
                    CompactType {
                        vars: both,
                        ..Default::default()
                    },
                ),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };

        let simplified = simplify_type(graph);
        let cf = simplified.term.fun.unwrap();
        let dom_s = &cf.domains[0];
        let cod_s = &cf.codomain;
        assert_eq!(dom_s.vars.len(), 1, "one var after merge in dom");
        assert_eq!(cod_s.vars.len(), 1, "one var after merge in cod");
        assert_eq!(dom_s.vars, cod_s.vars, "same representative in dom and cod");
    }

    #[test]
    fn simplify_identity_both_polarities_preserved() {
        // term: Fun(dom={a}, cod={a})
        // a appears at both polarities; no simplification applies.
        let uid_a = fresh_uid();

        let graph = CompactGraph {
            term: CompactType {
                fun: compute_fun(
                    CompactType {
                        vars: [uid_a].into_iter().collect(),
                        ..Default::default()
                    },
                    CompactType {
                        vars: [uid_a].into_iter().collect(),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            },
            rec_vars: BTreeMap::new(),
        };

        let simplified = simplify_type(graph);
        let cf = simplified.term.fun.unwrap();
        let dom_s = &cf.domains[0];
        let cod_s = &cf.codomain;
        assert!(dom_s.vars.contains(&uid_a), "a preserved in dom");
        assert!(cod_s.vars.contains(&uid_a), "a preserved in cod");
    }
}
