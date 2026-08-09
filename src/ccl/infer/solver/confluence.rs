//! Order-independence (confluence) fuzz for the bound graph.
//!
//! The solver's design leans on arrival order not mattering: bounds are
//! recorded and swept pairwise as constraints arrive, `KindMerge` forces
//! "propagate transitively along links as they arrive, so ordering does not
//! matter", and the one-sided var-var propagation is an explicitly open
//! question (`design/type-inference.md`, "1. Algorithm Overview"). None of
//! that is tested as a property. This harness does: apply the same
//! constraint **set** in permuted orders, coalesce every variable, and
//! assert the outcomes agree — where an outcome is the per-variable
//! coalesced type (canonicalized: inference/kind variable ids renamed in
//! first-occurrence order) or the fact of rejection.
//!
//! A violation is typing that depends on constraint arrival order — the
//! same defect class the retired bridge arm had at the relation level
//! (`differential.rs :: bridge_normalization_composes`), one level up.

use super::constrain::{ConstrainCache, constrain_subtype};
use super::differential::{Rng, gen_ty};
use super::{coalesce_compact, compact_type, fresh_var, simplify_type};
use crate::ccl::Type;
use crate::ccl::ty::{FunKind, FunKindVar};

/// One constraint in a generated set, phrased over variable *indices* so the
/// same set can be replayed against freshly-minted variables per run.
#[derive(Clone, Debug)]
enum Spec {
    /// `ground <: vᵢ` — a lower bound arrives.
    Low(usize, Type),
    /// `vᵢ <: ground` — an upper bound arrives.
    Up(usize, Type),
    /// `vᵢ <: vⱼ` — a var-var edge; the one-sided propagation target.
    VarVar(usize, usize),
}

/// Replay `specs` in `order` against fresh variables.
///
/// The outcome is **acceptance** (no constraint rejected, every variable
/// coalesces) plus, when accepted, the per-variable coalesced types. *Which*
/// constraint trips the rejection of an unsatisfiable set is intrinsically
/// order-relative under record-then-sweep (the last edge to arrive meets
/// the already-recorded bounds) and emission order is fixed by the AST walk
/// in the real pipeline — so error identity is deliberately not part of the
/// outcome, but a set flipping between accepted and rejected across orders
/// is a hard violation. Every constraint gets a fresh cache, as real
/// emission does.
fn run(nvars: usize, specs: &[Spec], order: &[usize]) -> String {
    let vars: Vec<Type> = (0..nvars).map(|_| fresh_var(0)).collect();
    let mut rejected = false;
    for &i in order {
        let result = match &specs[i] {
            Spec::Low(v, t) => constrain_subtype(t, &vars[*v], &mut ConstrainCache::new()),
            Spec::Up(v, t) => constrain_subtype(&vars[*v], t, &mut ConstrainCache::new()),
            Spec::VarVar(a, b) => {
                constrain_subtype(&vars[*a], &vars[*b], &mut ConstrainCache::new())
            }
        };
        rejected |= result.is_err();
    }
    let mut coalesced = Vec::with_capacity(nvars);
    for v in &vars {
        match coalesce_compact(&simplify_type(compact_type(v))) {
            Ok(t) => coalesced.push(format!("{}", sort_refinement_chains(&t))),
            Err(_) => rejected = true,
        }
    }
    if rejected {
        "rejected".to_string()
    } else {
        canonicalize(&format!("{coalesced:?}"))
    }
}

/// Quarantine for the one **known** order-dependence
/// (`refinement_layer_order_depends_on_arrival_order` below): refinement
/// layers stack in arrival order, so before comparing outcomes each
/// refinement *chain* is re-sorted into a canonical order. Subtyping treats
/// the layers as a set, so this normalizes exactly the semantically-invisible
/// difference — any *other* divergence still fails the fuzz.
fn sort_refinement_chains(t: &Type) -> Type {
    use crate::ccl::Refinement;
    fn peel(t: &Type) -> (&Type, Vec<&Refinement>) {
        let mut refs = Vec::new();
        let mut cur = t;
        while let Type::Refinement(base, r) = cur {
            refs.push(r);
            cur = base;
        }
        (cur, refs)
    }
    let (base, mut refs) = peel(t);
    let base = match base {
        Type::Fun {
            name,
            kind,
            domain,
            codomain,
        } => Type::Fun {
            name: name.clone(),
            kind: kind.clone(),
            domain: Box::new(sort_refinement_chains(domain)),
            codomain: Box::new(sort_refinement_chains(codomain)),
        },
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(sort_refinement_chains).collect()),
        Type::Record(fs) => Type::Record(
            fs.iter()
                .map(|(n, t)| (n.clone(), sort_refinement_chains(t)))
                .collect(),
        ),
        Type::Variant(tags) => Type::Variant(
            tags.iter()
                .map(|(k, t)| (k.clone(), sort_refinement_chains(t)))
                .collect(),
        ),
        other => other.clone(),
    };
    refs.sort_by_key(|r| crate::ccl::symbolic::symbolic(&r.predicate));
    refs.iter()
        .rev()
        .fold(base, |acc, r| Type::Refinement(Box::new(acc), (*r).clone()))
}

/// Rename `?N` (inference vars) and `κN` (kind vars) in first-occurrence
/// order, so globally-fresh uids across runs compare equal.
fn canonicalize(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut seen: Vec<String> = Vec::new();
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '?' || c == 'κ' {
            let mut num = String::new();
            while let Some(d) = chars.peek() {
                if d.is_ascii_digit() {
                    num.push(*d);
                    chars.next();
                } else {
                    break;
                }
            }
            if num.is_empty() {
                out.push(c);
                continue;
            }
            let key = format!("{c}{num}");
            let idx = match seen.iter().position(|k| *k == key) {
                Some(i) => i,
                None => {
                    seen.push(key);
                    seen.len() - 1
                }
            };
            out.push(c);
            out.push_str(&format!("#{idx}"));
        } else {
            out.push(c);
        }
    }
    out
}

/// Replace a function's concrete kind with a fresh kind *variable*
/// (sometimes, top-level only) — the `KindMerge` force/link machinery only
/// runs when kind vars exist, and its "ordering does not matter" claim is a
/// prime target. Kind vars are stateful (`Rc`, forces accumulate), which is
/// why `gen_specs` is re-run per permutation rather than the specs being
/// cloned.
fn maybe_kind_var(rng: &mut Rng, t: Type) -> Type {
    match t {
        Type::Fun {
            name,
            kind: _,
            domain,
            codomain,
        } if rng.chance(1, 2) => Type::Fun {
            name,
            kind: FunKind::Var(FunKindVar::fresh()),
            domain,
            codomain,
        },
        other => other,
    }
}

fn gen_specs(rng: &mut Rng, nvars: usize) -> Vec<Spec> {
    let count = 2 + rng.below(5) as usize;
    let mut specs = Vec::with_capacity(count);
    for _ in 0..count {
        let v = rng.below(nvars as u64) as usize;
        match rng.below(4) {
            0 => {
                let t = gen_ty(rng, 2);
                let t = maybe_kind_var(rng, t);
                specs.push(Spec::Low(v, t));
            }
            1 => {
                let t = gen_ty(rng, 2);
                let t = maybe_kind_var(rng, t);
                specs.push(Spec::Up(v, t));
            }
            2 if nvars > 1 => {
                let mut w = rng.below(nvars as u64) as usize;
                if w == v {
                    w = (v + 1) % nvars;
                }
                specs.push(Spec::VarVar(v, w));
            }
            _ => {
                // Correlated bounds — the same ground type arriving on both
                // sides is where joins actually meet.
                let t = gen_ty(rng, 2);
                let t = maybe_kind_var(rng, t);
                specs.push(if rng.chance(1, 2) {
                    Spec::Low(v, t)
                } else {
                    Spec::Up(v, t)
                });
            }
        }
    }
    specs
}

fn shuffle(rng: &mut Rng, n: usize) -> Vec<usize> {
    let mut order: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        let j = rng.below((i + 1) as u64) as usize;
        order.swap(i, j);
    }
    order
}

/// **Finding, pinned: a coalesced type's refinement layers stack in
/// constraint arrival order.** Two refined upper bounds meeting at one
/// variable coalesce to `{{𝑇 | 𝑞} | 𝑝}` or `{{𝑇 | 𝑝} | 𝑞}` depending on
/// which bound arrived first. Subtyping is indifferent (layers compare as a
/// set in the deficit machinery), but `Type`'s derived `PartialEq` is
/// order-sensitive, and structural equality is load-bearing where types are
/// *identities*: the trivial-equality short-circuit, cache keys, and the
/// recorded-vs-recomputed walls. (`SpecKey` compares refinement sets as
/// sets and is not exposed to layer order; its α-variance exposure is
/// `spec_key_splits_on_alpha_variant_dependent_types` below.)
///
/// **The obvious fix is wrong, which is the deeper finding.** Canonically
/// sorting `CompactType::refinements` (tried and reverted) breaks join
/// planning: planning reads the refinement chain *positionally* — the
/// outermost layer drives which cast/restrict it materializes — so
/// reordering changed what planning built (`comprehensions::case_6` grew a
/// spurious `cast(cast(..))`). One `Vec` currently serves three
/// incompatible views: a *set* to subtyping, a *stack* to planning, an
/// *identity* to `SpecKey`/caches. The repair needs planning to stop
/// depending on layer order (or the representation to carry acquisition
/// order separately) before the order can be canonicalized. If this test
/// starts failing, that landed — remove the `sort_refinement_chains`
/// quarantine from the fuzz above.
#[test]
fn refinement_layer_order_depends_on_arrival_order() {
    use crate::ccl::{Lit, Refinement, TypedExpr};
    use std::rc::Rc;

    let refined = |marker: i64| {
        Type::Refinement(
            Box::new(Type::Base(crate::ccl::BaseType::Int)),
            Refinement::born(Rc::new(TypedExpr::lit(Lit::Int(marker)))),
        )
    };
    let coalesce_with_order = |first: &Type, second: &Type| {
        let v = fresh_var(0);
        constrain_subtype(&v, first, &mut ConstrainCache::new()).unwrap();
        constrain_subtype(&v, second, &mut ConstrainCache::new()).unwrap();
        coalesce_compact(&simplify_type(compact_type(&v))).unwrap()
    };
    let (p, q) = (refined(1), refined(2));
    let a = coalesce_with_order(&p, &q);
    let b = coalesce_with_order(&q, &p);
    assert_ne!(
        a, b,
        "layer order became arrival-independent — canonicalization landed; \
         remove the fuzz quarantine"
    );
    // The difference is exactly the layer order: canonically sorted, the
    // two coalesce results agree.
    assert_eq!(sort_refinement_chains(&a), sort_refinement_chains(&b));
}

#[test]
fn bound_order_permutation_fuzz() {
    let seed: u64 = std::env::var("CAMBRA_DIFF_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0xD1CE);
    let n: usize = std::env::var("CAMBRA_DIFF_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(2000);

    let mut rng = Rng::new(seed);
    let mut mismatches = Vec::new();
    for case in 0..n {
        // Specs are regenerated from the same sub-seed per permutation run:
        // kind variables carry mutable force/link state in an `Rc`, so a
        // cloned spec would leak one run's resolution into the next.
        let case_seed = rng.next();
        let build = || {
            let mut r = Rng::new(case_seed);
            let nvars = 1 + r.below(3) as usize;
            let specs = gen_specs(&mut r, nvars);
            (nvars, specs)
        };
        let (nvars, specs) = build();
        let baseline = run(nvars, &specs, &(0..specs.len()).collect::<Vec<_>>());
        for _ in 0..8 {
            let (nvars, specs) = build();
            let order = shuffle(&mut rng, specs.len());
            let outcome = run(nvars, &specs, &order);
            if outcome != baseline {
                mismatches.push(format!(
                    "case {case}: order {order:?} diverges\n  specs = {specs:?}\n  \
                     baseline = {baseline}\n  permuted = {outcome}"
                ));
                break;
            }
        }
    }
    eprintln!(
        "confluence: {n} constraint sets (seed {seed}), 8 permutations each, \
         {} order-dependent",
        mismatches.len()
    );
    assert!(
        mismatches.is_empty(),
        "{} order-dependent outcomes (first 3):\n{}",
        mismatches.len(),
        mismatches[..mismatches.len().min(3)].join("\n\n")
    );
}

/// **Finding, pinned: α-variant dependent types split `SpecKey`.** The key
/// deliberately excludes the Pi binder *name* (`spec_key.rs :: fun` — keying
/// on it "would split every use into its own key"), but the name survives
/// through the *predicates* that reference it, which the key compares
/// structurally. Two independently-derived, semantically-identical dependent
/// instantiation types — `(𝑥: 𝐷) ⤇ {Int | __elem == 𝑥}` at one call site,
/// the same under `𝑦` at another — therefore key apart, and uses that should
/// share a specialization get one clone each (over-splitting: a wasted
/// clone, not a miscompile, per `spec_key.rs`'s own taxonomy). Canonical Pi
/// binder names (the `REFINEMENT_BINDER` treatment, positionally) would make
/// α-variants structurally identical and this test flip.
#[test]
fn spec_key_splits_on_alpha_variant_dependent_types() {
    use super::differential::dep_pred;
    use super::spec_key;
    use crate::ccl::{Name, Refinement};

    let dep_fun = |binder: &str| Type::Fun {
        name: Some(Name::raw(binder)),
        kind: FunKind::Data,
        domain: Box::new(Type::UIntRange(3)),
        codomain: Box::new(Type::Refinement(
            Box::new(Type::Base(crate::ccl::BaseType::Int)),
            Refinement::born(dep_pred(binder)),
        )),
    };
    let fx = dep_fun("x");
    let fy = dep_fun("y");

    // The relation reconciles the α-variants both ways…
    let mut c = ConstrainCache::new();
    assert!(constrain_subtype(&fx, &fy, &mut c).is_ok());
    let mut c = ConstrainCache::new();
    assert!(constrain_subtype(&fy, &fx, &mut c).is_ok());
    // …but the specialization key does not.
    assert_ne!(
        spec_key(&fx),
        spec_key(&fy),
        "SpecKey became α-insensitive — canonical binders landed; \
         revisit the α-identity finding set"
    );
}

/// **Finding, pinned: merging α-variant dependent bounds is order-dependent
/// and leaves a dangling binder reference.** Two α-variant upper bounds
/// meeting at one variable merge into a fun shape that keeps the **first
/// arrival's** binder name (`compact.rs`: `a.name.or_else(|| b.name)`) while
/// the refinement sets *union* — so the coalesced type is
/// `(𝑥: 𝐷) ⤇ {{Int | __elem == 𝑥} | __elem == 𝑦}`: order-dependent in the
/// surviving binder, and carrying a predicate that references a binder the
/// type no longer binds. The two predicates are α-copies of one constraint
/// and should have collapsed to one; structural (α-sensitive) dedup cannot
/// see that. Same repair direction as above.
#[test]
fn alpha_variant_bound_merge_is_order_dependent() {
    use super::differential::dep_pred;
    use crate::ccl::{Name, Refinement};

    let dep_fun = |binder: &str| Type::Fun {
        name: Some(Name::raw(binder)),
        kind: FunKind::Data,
        domain: Box::new(Type::UIntRange(3)),
        codomain: Box::new(Type::Refinement(
            Box::new(Type::Base(crate::ccl::BaseType::Int)),
            Refinement::born(dep_pred(binder)),
        )),
    };
    let coalesce_with_order = |first: &Type, second: &Type| {
        let v = fresh_var(0);
        constrain_subtype(&v, first, &mut ConstrainCache::new()).unwrap();
        constrain_subtype(&v, second, &mut ConstrainCache::new()).unwrap();
        coalesce_compact(&simplify_type(compact_type(&v))).unwrap()
    };
    let (fx, fy) = (dep_fun("x"), dep_fun("y"));
    assert_ne!(
        coalesce_with_order(&fx, &fy),
        coalesce_with_order(&fy, &fx),
        "α-variant bound merge became order-independent — canonical binders \
         (or α-aware dedup) landed; revisit the α-identity finding set"
    );
}
