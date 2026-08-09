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
            Ok(t) => coalesced.push(format!("{t}")),
            Err(_) => rejected = true,
        }
    }
    if rejected {
        "rejected".to_string()
    } else {
        canonicalize(&format!("{coalesced:?}"))
    }
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

/// **Finding, repaired: a coalesced type's refinement claims are
/// arrival-order-independent.** Two refined upper bounds meeting at one
/// variable used to stack as `{{𝑇 | 𝑞} | 𝑝}` or `{{𝑇 | 𝑝} | 𝑞}` depending on
/// which arrived first. Subtyping was always indifferent (the deficit
/// machinery compares claims as a set), but `Type`'s equality was not, and
/// structural equality is load-bearing where types are *identities*: the
/// trivial-equality short-circuit, cache keys, and the recorded-vs-recomputed
/// walls.
///
/// With [`RefinementSet`](crate::ccl::RefinementSet) the layers are one
/// unordered set, so the two orders build the *same* type rather than two
/// types a canonical sort could reconcile — which is why this asserts plain
/// equality and the fuzz above needs no normalization.
#[test]
fn refinement_claims_are_arrival_order_independent() {
    use crate::ccl::{Lit, Refinement, TypedExpr};
    use std::rc::Rc;

    let refined = |marker: i64| {
        Type::refined_one(
            Type::Base(crate::ccl::BaseType::Int),
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
    assert_eq!(a, b, "refinement claims must not depend on arrival order");
    // Both claims survived — the meet of two refined upper bounds carries each
    // side's restriction, so this is a two-member set, not one order winning.
    assert_eq!(a.claims().len(), 2, "expected both claims, got {a}");
    // Rendering is order-stable too, so a diagnostic cannot leak the order.
    assert_eq!(format!("{a}"), format!("{b}"));
}

/// **Exhibit (behaviour retained by design): refinement equality
/// distinguishes cast-target vintages that rendering does not.**
///
/// Two claims can be `eq`-**unequal** while rendering identically, because
/// `eq_refinement_predicate` deliberately compares a cast's target predicate —
/// a semantic filter, not inference metadata (pinned by
/// `refinement_eq_distinguishes_cast_target_predicates`). Conflating two casts
/// whose targets carry different filters would let refinement-deficit matching
/// accept an unsatisfied demand, so dedup must not collapse them.
///
/// This used to be the order-sensitivity residue: passes *manufactured*
/// divergent vintages of one claim (wholesale `target := expr.ty` overwrites
/// promoted route-dependent rebuilt types into the compared slot), and dedup
/// correctly refused to collapse them — surfacing as duplicated claims under
/// `CAMBRA_REFINEMENT_ORDER=reverse`. The canonical-discharge ruling closed
/// that at the source (a cast's claims are term-determined; see
/// `canonical_cast_ty` / `canonicalize_cast_types`, and `formal/design.md`),
/// so the pipeline no longer produces render-alike unequal twins. This test
/// keeps the equality's semantics pinned from the other side: when targets
/// *genuinely* differ, rendering alike must not make them one claim.
#[test]
fn vintage_claims_render_alike_but_do_not_dedup() {
    use crate::ccl::{BaseType, Refinement, Type, TypedExpr, ccl_utils::make_cast};
    use std::rc::Rc;

    // Two casts of one value, differing *only* in their targets' domain
    // refinement — the shape a discharge mints at two comprehension depths.
    let vintage = |marker: i64| {
        let target = crate::ccl::ccl_utils::refined_data_fun(
            Type::Base(BaseType::Int),
            TypedExpr::lit(crate::ccl::Lit::Int(marker)),
            Type::Base(BaseType::Int),
        );
        // A resolved `ty` is what makes the rendering elide the target — the
        // post-inference form, where the two vintages become indistinguishable.
        Refinement::born(Rc::new(
            make_cast(TypedExpr::lit(crate::ccl::Lit::Int(0)), target)
                .with_ty(Type::Base(BaseType::Int)),
        ))
    };
    let (a, b) = (vintage(1), vintage(2));
    assert_eq!(
        crate::ccl::symbolic::symbolic(&a.predicate),
        crate::ccl::symbolic::symbolic(&b.predicate),
        "the two vintages must be indistinguishable in the rendering"
    );
    assert_ne!(a, b, "cast-target predicates distinguish the two vintages");

    // So a set holds both, and which one an equal-rendering position ends up
    // carrying depends on arrival — the residue the representation change does
    // not reach.
    let mut set = crate::ccl::RefinementSet::new();
    set.insert(a.clone());
    set.insert(b.clone());
    assert_eq!(set.len(), 2, "vintages do not dedup: {set:?}");
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

/// **Finding, repaired: α-variant dependent types key together.** Before
/// canonical Pi binders (`key_go` renaming references to `Name::pi(depth)`
/// as it walks), the binder name — deliberately excluded from the key —
/// leaked back in through the *predicates* that reference it, so
/// `(𝑥: 𝐷) ⤇ {Int | __elem == 𝑥}` at one call site and its `𝑦`-twin at
/// another keyed apart and split a specialization that should be shared.
#[test]
fn spec_key_shares_alpha_variant_dependent_types() {
    use super::differential::dep_pred;
    use super::spec_key;
    use crate::ccl::{Name, Refinement};

    let dep_fun = |binder: &str| Type::Fun {
        name: Some(Name::raw(binder)),
        kind: FunKind::Data,
        domain: Box::new(Type::UIntRange(3)),
        codomain: Box::new(Type::refined_one(
            Type::Base(crate::ccl::BaseType::Int),
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
    // …and the specialization key now agrees.
    assert_eq!(
        spec_key(&fx),
        spec_key(&fy),
        "α-variant dependent instantiation types must share a specialization"
    );
}

/// **Finding, repaired: merging α-variant dependent bounds is canonical.**
/// Before canonical Pi binders, the merged fun shape kept the *first
/// arrival's* binder while the refinement sets unioned both α-copies of one
/// constraint, coalescing to the order-dependent — and dangling —
/// `(𝑥: 𝐷) ⤇ {{Int | __elem == 𝑥} | __elem == 𝑦}`. With `compact_go`
/// renaming binders and references to `Name::pi(depth)` as bounds flatten,
/// α-variants compact identically: the copies dedup, the binder is
/// arrival-independent, and nothing dangles.
#[test]
fn alpha_variant_bound_merge_is_canonical() {
    use super::differential::dep_pred;
    use crate::ccl::{Name, Refinement};

    let dep_fun = |binder: &str| Type::Fun {
        name: Some(Name::raw(binder)),
        kind: FunKind::Data,
        domain: Box::new(Type::UIntRange(3)),
        codomain: Box::new(Type::refined_one(
            Type::Base(crate::ccl::BaseType::Int),
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
    let a = coalesce_with_order(&fx, &fy);
    let b = coalesce_with_order(&fy, &fx);
    assert_eq!(
        a, b,
        "α-variant bound merge must be arrival-order-independent"
    );
    // The α-copies collapsed: one binder, one predicate, nothing dangling.
    let Type::Fun { name, codomain, .. } = &a else {
        panic!("expected a function, got {a}");
    };
    assert_eq!(*name, Some(Name::pi(0)));
    let Type::Refinement(base, _) = &**codomain else {
        panic!("expected exactly one refinement layer, got {codomain}");
    };
    assert!(
        !matches!(&**base, Type::Refinement(..)),
        "the two α-copies of one constraint must dedup to one layer, got {codomain}"
    );
}
