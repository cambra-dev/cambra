//! Seeded generation of variable-free `Type`s, shared by the integration tests that
//! fuzz the solver. Deterministic and dependency-free, so a failing case
//! replays from its seed.
//!
//! Three test binaries include it — the differential oracles, the
//! constraint-order fuzz, and the subtype-transitivity fuzz — and each uses only
//! part of it, so every item is `allow(dead_code)`: `mod type_gen;` compiles the
//! whole module into each one, and the order fuzz does not generate leaves and
//! predicates directly the way the edit-driven harnesses do.
#![allow(dead_code)]

use std::rc::Rc;

use smol_str::SmolStr;

use cambra::ccl::{
    BaseType, BinOpKind, CompareKind, FieldKey, FunKind, FunKindVar, Lit, Name, Openness,
    Refinement, Type, TypeKind, TypedExpr, UnaryOpKind, ccl_utils,
};

/// A seed or case count from the environment, or `default`. Every harness here
/// is replayable from its seed, which means every harness reads the same two
/// knobs; one reader keeps them spelled once.
pub fn env_or<T: std::str::FromStr>(key: &str, default: T) -> T {
    std::env::var(key)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

/// xorshift64* — deterministic, dependency-free.
pub struct Rng(pub u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed | 1)
    }
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    pub fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }
}

/// A predicate covering the model's whole `Predicate` vocabulary
/// (`formal/CclFormal/Ty.lean`): `__elem`, each literal species, a binder
/// reference, `__elem == <binder>` (the dependent-refinement shape), and the
/// compound nodes — unary, projection, and application. Structural equality is
/// all subtyping observes, so a small closed set that can collide and differ is
/// enough; what the set has to be is *complete*, because a constructor no
/// generator emits is a constructor no differential compares.
///
/// Weighted toward the flat shapes the near-miss pairs are built from, with the
/// compound ones reached through a bounded recursion so a binder reference can
/// sit under a projection or a call — which is where a walk that names the node
/// kinds it descends stops seeing it.
pub fn gen_pred(rng: &mut Rng) -> Rc<TypedExpr> {
    gen_pred_at(rng, 2)
}

fn gen_pred_at(rng: &mut Rng, depth: u32) -> Rc<TypedExpr> {
    let binder = |rng: &mut Rng| if rng.chance(1, 2) { "x" } else { "y" };
    if depth == 0 {
        return Rc::new(TypedExpr::var(Name::elem()));
    }
    match rng.below(12) {
        0 => Rc::new(TypedExpr::var(Name::elem())),
        1 => Rc::new(TypedExpr::lit(Lit::Bool(true))),
        2 => Rc::new(TypedExpr::lit(Lit::Int(rng.below(3) as i64))),
        3 => Rc::new(TypedExpr::lit(Lit::String(
            if rng.chance(1, 2) { "p" } else { "q" }.to_string(),
        ))),
        4 => Rc::new(TypedExpr::lit(Lit::Unit)),
        5 => Rc::new(TypedExpr::unary(
            if rng.chance(1, 2) {
                UnaryOpKind::Not
            } else {
                UnaryOpKind::Neg
            },
            (*gen_pred_at(rng, depth - 1)).clone(),
        )),
        // A projection: `Apply` of a `Proj` morphism, which is how field and
        // index access is spelled (`TypedExpr::proj_field` / `proj_index`).
        6 => {
            let key = if rng.chance(1, 2) {
                TypedExpr::proj_field(if rng.chance(1, 2) { "a" } else { "b" })
            } else {
                TypedExpr::proj_index(rng.below(2) as usize)
            };
            Rc::new(TypedExpr::apply(
                (*gen_pred_at(rng, depth - 1)).clone(),
                key,
            ))
        }
        // A general application, the other compound the model's `Predicate` carries.
        7 => Rc::new(TypedExpr::apply(
            (*gen_pred_at(rng, depth - 1)).clone(),
            TypedExpr::var(Name::raw(binder(rng))),
        )),
        // A binder the predicate itself introduces, referenced from its body —
        // the shape a filter's lambda has. Two of these differing only in the
        // binder's spelling are one restriction, which is what makes the
        // encoder's index representation load-bearing rather than cosmetic.
        8 => {
            let name = Name::raw(binder(rng));
            let body = if rng.chance(2, 3) {
                TypedExpr::binop(
                    TypedExpr::var(name.clone()),
                    BinOpKind::Compare(CompareKind::Equals),
                    (*gen_pred_at(rng, depth - 1)).clone(),
                )
            } else {
                (*gen_pred_at(rng, depth - 1)).clone()
            };
            Rc::new(TypedExpr::lambda(name, Type::Base(BaseType::Int), body))
        }
        // A cast whose target refines its domain — the embedded-collection shape
        // whose target predicates `eq_refinement_predicate` compares.
        9 => {
            let target = ccl_utils::refined_data_fun(
                Type::Base(BaseType::Int),
                (*gen_pred_at(rng, depth - 1)).clone(),
                Type::Base(BaseType::Int),
                // A plain collection: the sum shapes come from `gen_ty`'s
                // `Type::sum_over` arm.
                FunKind::Data(None),
            );
            Rc::new(
                ccl_utils::make_cast((*gen_pred_at(rng, depth - 1)).clone(), target)
                    .with_ty(Type::Base(BaseType::Int)),
            )
        }
        _ => {
            let x = binder(rng);
            Rc::new(TypedExpr::binop(
                (*gen_pred_at(rng, depth - 1)).clone(),
                BinOpKind::Compare(CompareKind::Equals),
                TypedExpr::var(Name::raw(x)),
            ))
        }
    }
}

pub fn gen_leaf(rng: &mut Rng) -> Type {
    match rng.below(6) {
        0 => Type::Base(BaseType::Int),
        1 => Type::Base(BaseType::Bool),
        2 => Type::Base(BaseType::String),
        3 => Type::UIntRange(2 + rng.below(3) as usize),
        4 => Type::DataSource(if rng.chance(1, 2) { "s" } else { "t" }.into()),
        _ => Type::Txn,
    }
}

/// The kind variables one generated constraint set draws from.
///
/// Sharing is the point. A variable minted per generated type is written by at
/// most one constraint, which leaves the relation `constrain_fun_kind` records
/// between two kind variables unobservable: nothing checks whether a pin reaches
/// the far side, or whether it still does when it arrives after the edge. Drawing
/// from a pool gives a set a few variables spread across many constraints, so a
/// pin recorded by one is read through another.
pub struct KindVarPool(Vec<Rc<FunKindVar>>);

impl Default for KindVarPool {
    fn default() -> Self {
        Self::new()
    }
}

impl KindVarPool {
    pub fn new() -> Self {
        KindVarPool(Vec::new())
    }

    /// One of the variables already handed out, or a fresh one. Biased toward
    /// reuse, since a set of all-distinct variables is the case that already had
    /// coverage.
    fn pick(&mut self, rng: &mut Rng) -> Rc<FunKindVar> {
        if !self.0.is_empty() && rng.chance(2, 3) {
            let i = rng.below(self.0.len() as u64) as usize;
            return Rc::clone(&self.0[i]);
        }
        let v = FunKindVar::fresh();
        self.0.push(Rc::clone(&v));
        v
    }
}

/// Replace a function's concrete kind with a kind *variable* from `pool`
/// (sometimes, top-level only). Nothing else produces one: [`gen_ty`] stamps a
/// concrete `FunKind`, so the states only a variable kind reaches —
/// `KindMerge::Unknown`, and `constrain_fun_kind`'s variable-against-variable arm —
/// are unreachable without this. A kind variable holds mutable state behind an
/// `Rc` (its pin, and the variables it is related to), which is why a generator
/// that replays re-runs rather than cloning.
pub fn maybe_kind_var_from(rng: &mut Rng, pool: &mut KindVarPool, t: Type) -> Type {
    match t {
        Type::Fun {
            name,
            fun_kind: _,
            domain,
            codomain,
        } if rng.chance(1, 2) => Type::Fun {
            name,
            fun_kind: FunKind::Var(pool.pick(rng)),
            domain,
            codomain,
        },
        other => other,
    }
}

/// [`maybe_kind_var_from`] with a pool of its own, so the variable is fresh — for
/// a harness whose cases are independent and share nothing.
pub fn maybe_kind_var(rng: &mut Rng, t: Type) -> Type {
    maybe_kind_var_from(rng, &mut KindVarPool::new(), t)
}

/// Which fragment of the type language a sampler draws from.
///
/// The differential oracles compare against the Lean model, whose `Ty` has no dependent
/// sum, and they **assert** that every generated case reaches the wire rather than counting
/// skips — a sampler wandering outside the fragment would quietly stop comparing. The
/// property fuzzers answer to no model and want the sums: they are the only shapes that
/// reach `FunKindVar::record_sum`, the witness scope change a kind edge carries, or
/// `TypeKindVar` at all.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Fragment {
    /// Everything the model's `Ty` expresses, and nothing else.
    Modelled,
    /// The above plus dependent sums.
    WithSums,
}

pub fn gen_ty(rng: &mut Rng, depth: u32, fragment: Fragment) -> Type {
    if depth == 0 || rng.chance(1, 3) {
        return gen_leaf(rng);
    }
    // The sum arm is last, so dropping it is dropping the top of the range.
    let arms = match fragment {
        Fragment::WithSums => 6,
        Fragment::Modelled => 5,
    };
    match rng.below(arms) {
        // A dependent sum, built the one way a sum is ever built: over named candidates
        // (`Type::sum_over`). Generated because nothing else in this sampler reaches
        // `FunKindVar::record_sum`, the witness scope change a kind edge carries, or
        // `TypeKindVar` at all — and those are exactly where a fact recorded on one
        // derivation has to be visible from another, which is the property this harness
        // states.
        5 => {
            let candidates: Vec<Type> = (0..1 + rng.below(2)).map(|_| gen_leaf(rng)).collect();
            let name = rng.chance(1, 3).then(|| Name::raw("k"));
            Type::sum_over(
                TypeKind::Enumerated(candidates),
                name,
                gen_ty(rng, depth - 1, fragment),
            )
        }
        0 => {
            let fun_kind = if rng.chance(1, 2) {
                FunKind::Data(None)
            } else {
                FunKind::Compute
            };
            let domain = gen_ty(rng, depth - 1, fragment);
            let name = match rng.below(3) {
                0 => None,
                1 => Some(Name::raw("x")),
                _ => Some(Name::raw("y")),
            };
            // With a Pi binder present, bias the codomain toward a dependent
            // refinement so the binder correspondence actually fires.
            let codomain = if name.is_some() && rng.chance(1, 2) {
                Type::refined_one(
                    gen_ty(rng, depth - 1, fragment),
                    Refinement::born(gen_pred(rng)),
                )
            } else {
                gen_ty(rng, depth - 1, fragment)
            };
            Type::Fun {
                name,
                fun_kind,
                domain: Box::new(domain),
                codomain: Box::new(codomain),
            }
        }
        1 => Type::Tuple(
            (0..rng.below(3))
                .map(|_| gen_ty(rng, depth - 1, fragment))
                .collect(),
        ),
        2 => {
            let mut fields = Vec::new();
            for key in ["a", "b", "c"] {
                if rng.chance(1, 2) {
                    fields.push((key.to_string(), gen_ty(rng, depth - 1, fragment)));
                }
            }
            Type::Record(fields)
        }
        3 => {
            let mut tags = Vec::new();
            if rng.chance(1, 2) {
                for key in ["t0", "t1"] {
                    if rng.chance(2, 3) {
                        tags.push((
                            FieldKey::Name(SmolStr::from(key)),
                            gen_ty(rng, depth - 1, fragment),
                        ));
                    }
                }
            } else {
                for i in 0..rng.below(3) {
                    tags.push((
                        FieldKey::Index(i as usize),
                        gen_ty(rng, depth - 1, fragment),
                    ));
                }
            }
            // Closed: an open arm set is only ever *demanded*, never produced, so
            // a generated type — which stands in for a value's type — is closed.
            Type::Variant(tags, Openness::Closed)
        }
        _ => Type::refined_one(
            gen_ty(rng, depth - 1, fragment),
            Refinement::born(gen_pred(rng)),
        ),
    }
}

// Near-miss generation: a type paired with a small directed edit of itself. A
// uniformly generated pair of types is almost always unrelated, and an unrelated
// pair exercises only the mismatch arms. Editing one side keeps the pair close
// enough that the width, refinement, and contravariance rules decide the
// verdict — which is where the interesting disagreements live, for the
// differential oracle and for a transitivity chain alike.

/// A small directed edit of `t` — targets the width/refinement rules, where
/// near-miss pairs have the interesting verdicts.
pub fn edit(rng: &mut Rng, t: &Type, fragment: Fragment) -> Type {
    match rng.below(4) {
        // Add a refinement layer (rhs gains a demand / lhs gains a supply).
        0 => Type::refined_one(t.clone(), Refinement::born(gen_pred(rng))),
        // Peel a refinement layer if there is one.
        1 => match t {
            Type::Refinement(base, _) => (**base).clone(),
            _ => Type::Base(BaseType::Int),
        },
        // Narrow a product / widen a sum by one entry.
        2 => match t {
            Type::Record(fields) if !fields.is_empty() => {
                Type::Record(fields[..fields.len() - 1].to_vec())
            }
            Type::Variant(tags, openness) => {
                let mut tags = tags.clone();
                tags.push((FieldKey::Name(SmolStr::from("extra")), Type::Txn));
                Type::Variant(tags, *openness)
            }
            Type::Tuple(ts) => {
                let mut ts = ts.clone();
                ts.push(Type::Base(BaseType::Bool));
                Type::Tuple(ts)
            }
            _ => gen_ty(rng, 2, fragment),
        },
        _ => gen_ty(rng, 3, fragment),
    }
}

/// A plausible subtype-partner for `t`, biased toward *accepted* edges so
/// transitivity chains form at a workable rate: clones, directed edits, and
/// domain/codomain-level edits that exercise contravariance.
pub fn partner(rng: &mut Rng, t: &Type, fragment: Fragment) -> Type {
    match rng.below(8) {
        0 | 1 => t.clone(),
        2 | 3 => edit(rng, t, fragment),
        4..=6 => match t {
            // Edit *inside* a function: domain/codomain near-misses probe the
            // contravariant edge and the codomain correspondence.
            Type::Fun {
                name,
                fun_kind,
                domain,
                codomain,
            } => {
                let flip_kind = rng.chance(1, 4);
                Type::Fun {
                    name: name.clone(),
                    // Flipping data-vs-compute, not the binder slot: a slot carrying
                    // binders is a sum, and dropping them here would edit the *kind* into
                    // a shape no term built.
                    fun_kind: if flip_kind {
                        match fun_kind {
                            FunKind::Data(..) => FunKind::Compute,
                            _ => FunKind::Data(None),
                        }
                    } else {
                        fun_kind.clone()
                    },
                    domain: Box::new(if rng.chance(1, 2) {
                        edit(rng, domain, fragment)
                    } else {
                        (**domain).clone()
                    }),
                    codomain: Box::new(if rng.chance(1, 2) {
                        edit(rng, codomain, fragment)
                    } else {
                        (**codomain).clone()
                    }),
                }
            }
            _ => edit(rng, t, fragment),
        },
        _ => gen_ty(rng, 3, fragment),
    }
}
