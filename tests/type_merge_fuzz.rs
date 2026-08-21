//! Fuzz the bound merge for order-independence.
//!
//! The solver's design leans on constraint arrival order not mattering: bounds
//! are recorded and swept pairwise as constraints arrive, and `KindMerge`
//! forces "propagate transitively along links as they arrive, so ordering does
//! not matter" (`src/ccl/design/type-inference.md`, "1. Algorithm Overview").
//! No unit test states that as a property, because a single case cannot: the
//! property is over *every* permutation of a constraint set, and the sets where
//! it fails are the ones nobody thought to write down.
//!
//! This applies the same constraint **set** in permuted orders, coalesces every
//! variable, and asserts the outcomes agree. A violation is typing that depends
//! on constraint arrival order — the same defect class as a non-transitive
//! subtype relation, one level up.
//!
//! Seeded and dependency-free, so a failure replays: `CAMBRA_FUZZ_SEED` picks
//! the seed and `CAMBRA_FUZZ_N` the number of constraint sets.

mod type_gen;

use cambra::ccl::infer::solver::{
    ConstrainCache, coalesce_compact, compact_type, constrain_subtype, simplify_type,
};
use cambra::ccl::{InferVar, Name, Telescope, Type};
use type_gen::{Rng, gen_ty, maybe_kind_var};

/// One constraint in a generated set, phrased over variable *indices* so the
/// same set can be replayed against freshly-minted variables per run.
#[derive(Clone, Debug)]
enum Spec {
    /// `ground <: vᵢ` — a lower bound arrives.
    Low(usize, Type),
    /// `vᵢ <: ground` — an upper bound arrives.
    Up(usize, Type),
    /// `vᵢ <: vⱼ` — a var-var edge, where propagation is one-sided.
    VarVar(usize, usize),
}

/// Replay `specs` in `order` against fresh variables, and render the outcome.
///
/// The outcome is **acceptance** — no constraint rejected, every variable
/// coalesces — plus, when accepted, the per-variable coalesced types. *Which*
/// constraint trips the rejection of an unsatisfiable set is intrinsically
/// order-relative under record-then-sweep (the last edge to arrive meets the
/// already-recorded bounds), and emission order is fixed by the AST walk in the
/// real pipeline, so error identity is deliberately not part of the outcome. A
/// set flipping between accepted and rejected across orders is a violation.
///
/// Every constraint gets a fresh cache, as real emission does.
fn run(nvars: usize, specs: &[Spec], order: &[usize]) -> String {
    // The generator's predicates reference its two Pi binder names, and it emits
    // a dependent refinement independently of whether an enclosing function
    // binds one. The variables therefore stand in a context holding both, which
    // is what their telescope records; minting them scope-free would make the
    // record-time closure check reject the generator's own output.
    let scope = Telescope::empty()
        .extended(Name::raw("x"))
        .extended(Name::raw("y"));
    let vars: Vec<Type> = (0..nvars)
        .map(|_| Type::Infer(InferVar::fresh_in(0, &scope)))
        .collect();
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

/// Rename `?N` (inference variables) and `κN` (kind variables) in
/// first-occurrence order, so globally-fresh uids across runs compare equal.
fn canonicalize(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut seen: Vec<String> = Vec::new();
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '?' && c != 'κ' {
            out.push(c);
            continue;
        }
        let mut num = String::new();
        while let Some(d) = chars.peek() {
            if !d.is_ascii_digit() {
                break;
            }
            num.push(*d);
            chars.next();
        }
        if num.is_empty() {
            out.push(c);
            continue;
        }
        let key = format!("{c}{num}");
        let idx = seen.iter().position(|k| *k == key).unwrap_or_else(|| {
            seen.push(key);
            seen.len() - 1
        });
        out.push(c);
        out.push_str(&format!("#{idx}"));
    }
    out
}

fn gen_specs(rng: &mut Rng, nvars: usize) -> Vec<Spec> {
    let count = 2 + rng.below(5) as usize;
    let mut specs = Vec::with_capacity(count);
    for _ in 0..count {
        let v = rng.below(nvars as u64) as usize;
        let ground = |rng: &mut Rng| {
            let t = gen_ty(rng, 2);
            maybe_kind_var(rng, t)
        };
        match rng.below(4) {
            0 => specs.push(Spec::Low(v, ground(rng))),
            1 => specs.push(Spec::Up(v, ground(rng))),
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
                let t = ground(rng);
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

fn env_or<T: std::str::FromStr>(key: &str, default: T) -> T {
    std::env::var(key)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

#[test]
fn merging_bounds_is_independent_of_their_arrival_order() {
    let seed: u64 = env_or("CAMBRA_FUZZ_SEED", 0xD1CE);
    let n: usize = env_or("CAMBRA_FUZZ_N", 2000);

    let mut rng = Rng::new(seed);
    let mut mismatches = Vec::new();
    for case in 0..n {
        // Specs are regenerated from the same sub-seed per permutation run:
        // kind variables carry mutable force/link state in an `Rc`, so a cloned
        // spec would leak one run's resolution into the next.
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
        "type merge fuzz: {n} constraint sets (seed {seed}), 8 permutations each, \
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
