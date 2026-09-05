//! Fuzz the solver for constraint arrival-order independence.
//!
//! The solver's design leans on constraint arrival order not mattering, and
//! record-then-sweep makes that a property of the algorithm rather than of any
//! one constraint (`src/ccl/design/type-inference.md`, "1. Algorithm Overview").
//! No unit test states the property, because a single case cannot: it is over
//! *every* permutation of a constraint set, and the sets where it fails are the
//! ones nobody thought to write down.
//!
//! This applies the same constraint **set** in permuted orders, coalesces every
//! variable, and asserts the outcomes agree. A violation is typing that depends
//! on constraint arrival order — the same defect class as a non-transitive
//! subtype relation, one level up.
//!
//! Seeded and dependency-free, so a failure replays: `CAMBRA_FUZZ_SEED` picks
//! the seed and `CAMBRA_FUZZ_N` the number of constraint sets.

mod type_gen;

use std::rc::Rc;

use cambra::ccl::infer::solver::{
    ConstrainCache, coalesce_compact, compact_type, constrain_subtype, simplify_type,
};
use cambra::ccl::{BaseType, FunKind, FunKindVar, InferVar, Name, Telescope, Type};
use type_gen::{Fragment, KindVarPool, Rng, env_or, gen_ty, maybe_kind_var_from};

/// One constraint in a generated set, phrased over variable *indices* so the
/// same set can be replayed against freshly-minted variables per run.
#[derive(Clone, Debug)]
enum Spec {
    /// `𝑇 <: vᵢ` — a lower bound arrives.
    Low(usize, Type),
    /// `vᵢ <: 𝑇` — an upper bound arrives.
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
    // One pool per set, so two constraints can carry the same kind variable and a
    // pin recorded by one is read through the other.
    let mut kinds = KindVarPool::new();
    for _ in 0..count {
        let v = rng.below(nvars as u64) as usize;
        let concrete = |rng: &mut Rng, kinds: &mut KindVarPool| {
            let t = gen_ty(rng, 2, Fragment::WithSums);
            maybe_kind_var_from(rng, kinds, t)
        };
        match rng.below(4) {
            0 => specs.push(Spec::Low(v, concrete(rng, &mut kinds))),
            1 => specs.push(Spec::Up(v, concrete(rng, &mut kinds))),
            2 if nvars > 1 => {
                let mut w = rng.below(nvars as u64) as usize;
                if w == v {
                    w = (v + 1) % nvars;
                }
                specs.push(Spec::VarVar(v, w));
            }
            _ => {
                // Correlated bounds — the same type arriving on both sides
                // is where joins actually meet.
                let t = concrete(rng, &mut kinds);
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

/// The one shape the generated sets reach only by luck, stated directly: a kind
/// variable shared between two inference variables, where the pin arrives after
/// the edge that relates it.
///
/// Every permutation of these four constraints has to coalesce both variables the
/// same way. `constrain_fun_kind` relates two kind variables and `FunKindVar::pin`
/// joins over the relation at the read, so the answer is a function of the set;
/// resolving at the edge instead answers from the pins that had arrived, and `v1`
/// renders `⇒` in the orders where the edge precedes the pin and `⤇` in the rest.
///
/// A generated set reaches this only when it draws two *distinct* kind variables
/// onto opposite bounds of one variable, a third bound pinning one of them, and a
/// second variable giving the other a rendered position — so it is written out
/// rather than left to the sampler.
#[test]
fn a_shared_kind_var_resolves_the_same_way_in_every_order() {
    let fun_over = |fun_kind: FunKind| Type::Fun {
        name: None,
        fun_kind,
        domain: Box::new(Type::UIntRange(3)),
        codomain: Box::new(Type::Base(BaseType::Int)),
    };
    // `k1` and `k2` meet on opposite bounds of `v0`, which is the var-var kind
    // edge; `Data` reaches `k1` only; `k2` also sits in a positive position of
    // `v1`, which is what makes its resolution show up in a coalesced type.
    let build = |order: &[usize]| -> String {
        let scope = Telescope::empty();
        let v0 = Type::Infer(InferVar::fresh_in(0, &scope));
        let v1 = Type::Infer(InferVar::fresh_in(0, &scope));
        let (k1, k2) = (FunKindVar::fresh(), FunKindVar::fresh());
        let mut rejected = false;
        for &i in order {
            let r = match i {
                0 => constrain_subtype(
                    &fun_over(FunKind::Var(Rc::clone(&k1))),
                    &v0,
                    &mut ConstrainCache::new(),
                ),
                1 => constrain_subtype(
                    &v0,
                    &fun_over(FunKind::Var(Rc::clone(&k2))),
                    &mut ConstrainCache::new(),
                ),
                2 => constrain_subtype(
                    &fun_over(FunKind::Var(Rc::clone(&k2))),
                    &v1,
                    &mut ConstrainCache::new(),
                ),
                _ => constrain_subtype(
                    &v0,
                    &fun_over(FunKind::Data(None)),
                    &mut ConstrainCache::new(),
                ),
            };
            rejected |= r.is_err();
        }
        let mut out = Vec::new();
        for v in [&v0, &v1] {
            match coalesce_compact(&simplify_type(compact_type(v))) {
                Ok(t) => out.push(format!("{t}")),
                Err(_) => {
                    rejected = true;
                    out.push("rejected".to_string())
                }
            }
        }
        format!(
            "{}{}",
            if rejected { "rejected " } else { "" },
            out.join(", ")
        )
    };

    let baseline = build(&[0, 1, 2, 3]);
    let mut divergent = Vec::new();
    for order in permutations(4) {
        let got = build(&order);
        if got != baseline {
            divergent.push(format!("  order {order:?} -> {got}"));
        }
    }
    assert!(
        divergent.is_empty(),
        "a shared kind variable resolves differently by arrival order\n  \
         baseline [0, 1, 2, 3] -> {baseline}\n{}",
        divergent.join("\n")
    );
}

/// Every permutation of `0..n`, in lexicographic order.
fn permutations(n: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    let mut cur: Vec<usize> = (0..n).collect();
    loop {
        out.push(cur.clone());
        // Next lexicographic permutation.
        let Some(i) = (0..n.saturating_sub(1))
            .rev()
            .find(|&i| cur[i] < cur[i + 1])
        else {
            return out;
        };
        let j = (i + 1..n)
            .rev()
            .find(|&j| cur[j] > cur[i])
            .expect("a larger successor exists");
        cur.swap(i, j);
        cur[i + 1..].reverse();
    }
}

#[test]
fn solving_is_independent_of_constraint_arrival_order() {
    let seed: u64 = env_or("CAMBRA_FUZZ_SEED", 0xD1CE);
    let n: usize = env_or("CAMBRA_FUZZ_N", 2000);

    let mut rng = Rng::new(seed);
    let mut mismatches = Vec::new();
    for case in 0..n {
        // Specs are regenerated from the same sub-seed per permutation run: a
        // kind variable carries its pin in an `Rc<RefCell<_>>`, so a cloned spec
        // would leak one run's pins into the next.
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
        "constraint order fuzz: {n} constraint sets (seed {seed}), 8 permutations each, \
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
