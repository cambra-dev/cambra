//! Seeded generation of ground `Type`s, shared by the integration tests that
//! fuzz the solver. Deterministic and dependency-free, so a failing case
//! replays from its seed.
//!
//! A test binary uses only part of this, so each item is `allow(dead_code)`:
//! `mod type_gen;` compiles the whole module into every including binary, and
//! `tests/type_merge_fuzz.rs` does not generate the leaves and predicates
//! directly the way an edit-driven harness does.
#![allow(dead_code)]

use std::rc::Rc;

use smol_str::SmolStr;

use cambra::ccl::{
    BaseType, BinOpKind, CompareKind, FieldKey, FunKind, FunKindVar, Lit, Name, Openness,
    Refinement, Type, TypedExpr,
};

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

/// A predicate from the model's `Pred` vocabulary: `__elem`, literals, a
/// binder reference, or `__elem == <binder>` (the dependent-refinement
/// shape). Structural equality is all subtyping observes, so a small closed
/// set that can collide and differ is enough.
pub fn gen_pred(rng: &mut Rng) -> Rc<TypedExpr> {
    match rng.below(6) {
        0 => Rc::new(TypedExpr::var(Name::elem())),
        1 => Rc::new(TypedExpr::lit(Lit::Bool(true))),
        2 => Rc::new(TypedExpr::lit(Lit::Int(rng.below(3) as i64))),
        _ => {
            let x = if rng.chance(1, 2) { "x" } else { "y" };
            Rc::new(TypedExpr::binop(
                TypedExpr::var(Name::elem()),
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

/// Replace a function's concrete kind with a fresh kind *variable* (sometimes,
/// top-level only). Nothing else produces one: [`gen_ty`] stamps a concrete
/// `FunKind`, so the states that only a *variable* kind reaches —
/// `KindMerge::Unknown`, and the force/link machinery whose "ordering does not
/// matter" rule a fuzz targets — are unreachable without this. Kind vars
/// are stateful (`Rc`, forces accumulate), which is why a generator that replays
/// re-runs rather than cloning.
pub fn maybe_kind_var(rng: &mut Rng, t: Type) -> Type {
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

pub fn gen_ty(rng: &mut Rng, depth: u32) -> Type {
    if depth == 0 || rng.chance(1, 3) {
        return gen_leaf(rng);
    }
    match rng.below(5) {
        0 => {
            let kind = if rng.chance(1, 2) {
                FunKind::Data
            } else {
                FunKind::Compute
            };
            let domain = gen_ty(rng, depth - 1);
            let name = match rng.below(3) {
                0 => None,
                1 => Some(Name::raw("x")),
                _ => Some(Name::raw("y")),
            };
            // With a Pi binder present, bias the codomain toward a dependent
            // refinement so the binder correspondence actually fires.
            let codomain = if name.is_some() && rng.chance(1, 2) {
                Type::refined_one(gen_ty(rng, depth - 1), Refinement::born(gen_pred(rng)))
            } else {
                gen_ty(rng, depth - 1)
            };
            Type::Fun {
                name,
                kind,
                domain: Box::new(domain),
                codomain: Box::new(codomain),
            }
        }
        1 => Type::Tuple((0..rng.below(3)).map(|_| gen_ty(rng, depth - 1)).collect()),
        2 => {
            let mut fields = Vec::new();
            for key in ["a", "b", "c"] {
                if rng.chance(1, 2) {
                    fields.push((key.to_string(), gen_ty(rng, depth - 1)));
                }
            }
            Type::Record(fields)
        }
        3 => {
            let mut tags = Vec::new();
            if rng.chance(1, 2) {
                for key in ["t0", "t1"] {
                    if rng.chance(2, 3) {
                        tags.push((FieldKey::Name(SmolStr::from(key)), gen_ty(rng, depth - 1)));
                    }
                }
            } else {
                for i in 0..rng.below(3) {
                    tags.push((FieldKey::Index(i as usize), gen_ty(rng, depth - 1)));
                }
            }
            // Closed: an open arm set is only ever *demanded*, never produced, so
            // a generated type — which stands in for a value's type — is closed.
            Type::Variant(tags, Openness::Closed)
        }
        _ => Type::refined_one(gen_ty(rng, depth - 1), Refinement::born(gen_pred(rng))),
    }
}
