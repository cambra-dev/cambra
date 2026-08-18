//! M1 differential oracle: `constrain_subtype`'s verdict on **ground** type
//! pairs (no `Infer` on either side) diffed against the Lean model's
//! `subCheck` (`formal/CclFormal/Decide.lean`; plan and adjudications in
//! `formal/design.md`).
//!
//! The test generates biased ground pairs with a seeded PRNG, serializes
//! them to the wire schema the Lean codec defines (`formal/CclFormal/Json.lean`),
//! streams them through the `subverdict` oracle binary, and asserts the two
//! verdicts agree case by case. It **skips loudly** when the oracle is not
//! built (`cd formal && lake build`) so the suite stays green on machines
//! without a Lean toolchain.
//!
//! Deliberately not generated: duplicate record/variant keys — outside
//! `Ty.WF`, where the Rust's trivial-equality short-circuit and its
//! find-first arms genuinely disagree (pinned below as
//! `dup_key_record_trips_the_uniquely_keyed_invariant`). Everything else in
//! the ground fragment is fair game.

use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};
use std::rc::Rc;

use smol_str::SmolStr;

use super::constrain::{ConstrainCache, constrain_subtype};
use crate::ccl::ty::FunKind;
use crate::ccl::{
    BaseType, BinOpKind, CompareKind, FieldKey, Lit, Name, Refinement, Type, TypedExpr,
    TypedExprNode,
};

/// xorshift64* — deterministic, dependency-free.
pub(super) struct Rng(pub(super) u64);

impl Rng {
    pub(super) fn new(seed: u64) -> Self {
        Rng(seed | 1)
    }
    pub(super) fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    pub(super) fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    pub(super) fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }
}

/// A predicate from the model's `Pred` vocabulary: `__elem`, literals, a
/// binder reference, or `__elem == <binder>` (the dependent-refinement
/// shape). Structural equality is all subtyping observes, so a small closed
/// set that can collide and differ is enough.
fn gen_pred(rng: &mut Rng) -> Rc<TypedExpr> {
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

fn gen_leaf(rng: &mut Rng) -> Type {
    match rng.below(6) {
        0 => Type::Base(BaseType::Int),
        1 => Type::Base(BaseType::Bool),
        2 => Type::Base(BaseType::String),
        3 => Type::UIntRange(2 + rng.below(3) as usize),
        4 => Type::DataSource(if rng.chance(1, 2) { "s" } else { "t" }.into()),
        _ => Type::Txn,
    }
}

pub(super) fn gen_ty(rng: &mut Rng, depth: u32) -> Type {
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
            Type::Variant(tags)
        }
        _ => Type::refined_one(gen_ty(rng, depth - 1), Refinement::born(gen_pred(rng))),
    }
}

/// A small directed edit of `t` — targets the width/refinement rules, where
/// near-miss pairs have the interesting verdicts.
fn edit(rng: &mut Rng, t: &Type) -> Type {
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
            Type::Variant(tags) => {
                let mut tags = tags.clone();
                tags.push((FieldKey::Name(SmolStr::from("extra")), Type::Txn));
                Type::Variant(tags)
            }
            Type::Tuple(ts) => {
                let mut ts = ts.clone();
                ts.push(Type::Base(BaseType::Bool));
                Type::Tuple(ts)
            }
            _ => gen_ty(rng, 2),
        },
        _ => gen_ty(rng, 3),
    }
}

/// `__elem == <name>` — the dependent-refinement predicate shape, aimed at
/// a specific Pi binder.
pub(super) fn dep_pred(name: &str) -> Rc<TypedExpr> {
    Rc::new(TypedExpr::binop(
        TypedExpr::var(Name::elem()),
        BinOpKind::Compare(CompareKind::Equals),
        TypedExpr::var(Name::raw(name)),
    ))
}

/// Generate a **correlated** pair: both sides are built together, usually
/// emitting identical nodes and occasionally diverging in exactly one aspect
/// (a leaf, a kind, a binder name, a predicate, a width). Deep near-misses
/// are where subtle rule divergence hides — top-level edits never reach a
/// nested Pi correspondence or a refinement two constructors down.
fn gen_pair(rng: &mut Rng, depth: u32) -> (Type, Type) {
    if rng.chance(1, 8) {
        return (gen_ty(rng, depth), gen_ty(rng, depth));
    }
    if depth == 0 || rng.chance(1, 3) {
        let l = gen_leaf(rng);
        let r = if rng.chance(1, 4) {
            gen_leaf(rng)
        } else {
            l.clone()
        };
        return (l, r);
    }
    match rng.below(5) {
        0 => {
            let kl = if rng.chance(1, 2) {
                FunKind::Data
            } else {
                FunKind::Compute
            };
            let kr = if rng.chance(1, 6) {
                match kl {
                    FunKind::Data => FunKind::Compute,
                    _ => FunKind::Data,
                }
            } else {
                kl.clone()
            };
            let (dl, dr) = gen_pair(rng, depth - 1);
            let binder = |rng: &mut Rng| match rng.below(3) {
                0 => None,
                1 => Some("x"),
                _ => Some("y"),
            };
            let nl = binder(rng);
            let nr = if rng.chance(1, 4) { binder(rng) } else { nl };
            let (mut cl, mut cr) = gen_pair(rng, depth - 1);
            // Dependent refinements referencing each side's *own* binder:
            // structurally α-equivalent, so they must match through the
            // rename correspondence — unless we deliberately misaim one.
            if rng.chance(1, 2) {
                if let Some(bl) = nl {
                    cl = Type::refined_one(cl, Refinement::born(dep_pred(bl)));
                }
                if let Some(br) = nr {
                    let target = if rng.chance(1, 5) { "z" } else { br };
                    cr = Type::refined_one(cr, Refinement::born(dep_pred(target)));
                }
            }
            let fun = |n: Option<&str>, k: FunKind, d: Type, c: Type| Type::Fun {
                name: n.map(Name::raw),
                kind: k,
                domain: Box::new(d),
                codomain: Box::new(c),
            };
            (fun(nl, kl, dl, cl), fun(nr, kr, dr, cr))
        }
        1 => {
            let len_l = rng.below(3) as usize;
            let len_r = if rng.chance(1, 4) {
                rng.below(3) as usize
            } else {
                len_l
            };
            let mut ls = Vec::new();
            let mut rs = Vec::new();
            for i in 0..len_l.max(len_r) {
                let (l, r) = gen_pair(rng, depth - 1);
                if i < len_l {
                    ls.push(l);
                }
                if i < len_r {
                    rs.push(r);
                }
            }
            (Type::Tuple(ls), Type::Tuple(rs))
        }
        2 => {
            let mut ls = Vec::new();
            let mut rs = Vec::new();
            for key in ["a", "b", "c"] {
                let in_l = rng.chance(1, 2);
                let in_r = if rng.chance(1, 6) { !in_l } else { in_l };
                let (l, r) = gen_pair(rng, depth - 1);
                if in_l {
                    ls.push((key.to_string(), l));
                }
                if in_r {
                    rs.push((key.to_string(), r));
                }
            }
            (Type::Record(ls), Type::Record(rs))
        }
        3 => {
            let mut ls = Vec::new();
            let mut rs = Vec::new();
            for key in ["t0", "t1"] {
                let in_l = rng.chance(1, 2);
                let in_r = if rng.chance(1, 6) { !in_l } else { in_l };
                let (l, r) = gen_pair(rng, depth - 1);
                if in_l {
                    ls.push((FieldKey::Name(SmolStr::from(key)), l));
                }
                if in_r {
                    rs.push((FieldKey::Name(SmolStr::from(key)), r));
                }
            }
            (Type::Variant(ls), Type::Variant(rs))
        }
        _ => {
            let (bl, br) = gen_pair(rng, depth - 1);
            let pl = gen_pred(rng);
            let pr = if rng.chance(1, 4) {
                gen_pred(rng)
            } else {
                Rc::clone(&pl)
            };
            let mut l = Type::refined_one(bl, Refinement::born(pl));
            let mut r = Type::refined_one(br, Refinement::born(pr));
            // Occasionally give one side an extra layer — width on the
            // refinement *set*.
            if rng.chance(1, 4) {
                l = Type::refined_one(l, Refinement::born(gen_pred(rng)));
            }
            if rng.chance(1, 6) {
                r = Type::refined_one(r, Refinement::born(gen_pred(rng)));
            }
            (l, r)
        }
    }
}

/// A plausible subtype-partner for `t`, biased toward *accepted* edges so
/// transitivity chains form at a workable rate: clones, directed edits, and
/// domain/codomain-level edits that exercise contravariance.
fn partner(rng: &mut Rng, t: &Type) -> Type {
    match rng.below(8) {
        0 | 1 => t.clone(),
        2 | 3 => edit(rng, t),
        4..=6 => match t {
            // Edit *inside* a function: domain/codomain near-misses probe the
            // contravariant edge and the codomain correspondence.
            Type::Fun {
                name,
                kind,
                domain,
                codomain,
            } => {
                let flip_kind = rng.chance(1, 4);
                Type::Fun {
                    name: name.clone(),
                    kind: if flip_kind {
                        match kind {
                            FunKind::Data => FunKind::Compute,
                            _ => FunKind::Data,
                        }
                    } else {
                        kind.clone()
                    },
                    domain: Box::new(if rng.chance(1, 2) {
                        edit(rng, domain)
                    } else {
                        (**domain).clone()
                    }),
                    codomain: Box::new(if rng.chance(1, 2) {
                        edit(rng, codomain)
                    } else {
                        (**codomain).clone()
                    }),
                }
            }
            _ => edit(rng, t),
        },
        _ => gen_ty(rng, 3),
    }
}

/// Serialize a predicate into the model's `Pred` wire schema. `None` means
/// "outside the modeled vocabulary" — the case is refused rather than
/// serialized wrongly (the generator never produces such a predicate, so a
/// `None` here is a harness bug).
fn pred_json(e: &TypedExpr) -> Option<String> {
    match &e.node {
        TypedExprNode::Var(n) if *n == Name::elem() => Some(r#"{"k":"elem"}"#.to_string()),
        TypedExprNode::Var(Name::Raw(s)) => Some(format!(r#"{{"k":"var","x":"{s}"}}"#)),
        TypedExprNode::Lit(Lit::Int(n)) => Some(format!(r#"{{"k":"litInt","n":{n}}}"#)),
        TypedExprNode::Lit(Lit::Bool(b)) => Some(format!(r#"{{"k":"litBool","b":{b}}}"#)),
        TypedExprNode::BinOp { left, op, right } => Some(format!(
            r#"{{"k":"binop","op":"{op:?}","a":{},"b":{}}}"#,
            pred_json(left)?,
            pred_json(right)?
        )),
        _ => None,
    }
}

fn base_json(b: &BaseType) -> &'static str {
    b.keyword()
}

fn key_json(k: &FieldKey) -> String {
    match k {
        FieldKey::Index(n) => format!(r#"{{"k":"idx","n":{n}}}"#),
        FieldKey::Name(s) => format!(r#"{{"k":"name","s":"{s}"}}"#),
    }
}

/// Serialize a ground `Type` into the model's `Ty` wire schema; `None` for
/// anything outside the ground fragment.
fn ty_json(t: &Type) -> Option<String> {
    Some(match t {
        Type::Base(b) => format!(r#"{{"k":"base","base":"{}"}}"#, base_json(b)),
        Type::UIntRange(n) => format!(r#"{{"k":"uintRange","n":{n}}}"#),
        Type::DataSource(s) => format!(r#"{{"k":"dataSource","name":"{s}"}}"#),
        Type::Txn => r#"{"k":"txn"}"#.to_string(),
        Type::Fun {
            name,
            kind,
            domain,
            codomain,
        } => {
            let binder = match name {
                None => "null".to_string(),
                Some(Name::Raw(s)) => format!(r#""{s}""#),
                Some(_) => return None,
            };
            let kind = match kind {
                FunKind::Compute => "compute",
                FunKind::Data => "data",
                FunKind::Var(_) => return None,
            };
            format!(
                r#"{{"k":"fn","binder":{binder},"kind":"{kind}","dom":{},"cod":{}}}"#,
                ty_json(domain)?,
                ty_json(codomain)?
            )
        }
        Type::Tuple(ts) => {
            let ts: Option<Vec<_>> = ts.iter().map(ty_json).collect();
            format!(r#"{{"k":"tuple","ts":[{}]}}"#, ts?.join(","))
        }
        Type::Record(fields) => {
            let fs: Option<Vec<_>> = fields
                .iter()
                .map(|(n, t)| Some(format!(r#"["{n}",{}]"#, ty_json(t)?)))
                .collect();
            format!(r#"{{"k":"record","fields":[{}]}}"#, fs?.join(","))
        }
        Type::Variant(tags) => {
            let ts: Option<Vec<_>> = tags
                .iter()
                .map(|(k, t)| Some(format!(r#"[{},{}]"#, key_json(k), ty_json(t)?)))
                .collect();
            format!(r#"{{"k":"variant","tags":[{}]}}"#, ts?.join(","))
        }
        // The model's `refined` node carries the whole claim set, matching
        // `RefinementSet` — so a multi-claim position serializes as one node
        // with a `claims` array rather than as nested single-predicate layers.
        Type::Refinement(base, claims) => {
            let preds: Option<Vec<String>> =
                claims.iter().map(|r| pred_json(&r.predicate)).collect();
            format!(
                r#"{{"k":"refined","base":{},"claims":[{}]}}"#,
                ty_json(base)?,
                preds?.join(",")
            )
        }
        _ => return None,
    })
}

/// Transitivity chain fuzz: build chains `a <: b <: c` that `constrain`
/// accepts and check the direct edge. No violations are tolerated — a hit is
/// a finding, and fails the test with the triple printed.
#[test]
fn transitivity_chain_fuzz() {
    let seed: u64 = std::env::var("CAMBRA_DIFF_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0xBEEF);
    let n: usize = std::env::var("CAMBRA_DIFF_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(4000);

    let ok = |x: &Type, y: &Type| {
        let mut cache = ConstrainCache::new();
        constrain_subtype(x, y, &mut cache).is_ok()
    };
    let mut rng = Rng::new(seed);
    let mut chains = 0usize;
    let mut attempts = 0usize;
    let mut violations: Vec<(Type, Type, Type)> = Vec::new();
    while chains < n && attempts < n * 100 {
        attempts += 1;
        let b = gen_ty(&mut rng, 3);
        let a = partner(&mut rng, &b);
        let c = partner(&mut rng, &b);
        if !(ok(&a, &b) && ok(&b, &c)) {
            continue;
        }
        chains += 1;
        if !ok(&a, &c) {
            violations.push((a, b, c));
        }
    }

    eprintln!(
        "transitivity: {chains} chains (seed {seed}, {attempts} attempts), {} violations",
        violations.len()
    );
    let render = |t: &Type| ty_json(t).unwrap_or_else(|| format!("{t:?}"));
    assert!(
        violations.is_empty(),
        "transitivity violations (first 5):\n{}",
        violations
            .iter()
            .take(5)
            .map(|(a, b, c)| format!("a={}\nb={}\nc={}\n", render(a), render(b), render(c)))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn differential_ground_subtype_vs_lean_model() {
    let oracle = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/formal/.lake/build/bin/subverdict"
    );
    if !std::path::Path::new(oracle).exists() {
        eprintln!(
            "SKIPPED differential_ground_subtype_vs_lean_model: Lean oracle not built \
             (cd formal && lake build)"
        );
        return;
    }
    let seed: u64 = std::env::var("CAMBRA_DIFF_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0xC0FFEE);
    let n: usize = std::env::var("CAMBRA_DIFF_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(4000);

    let mut rng = Rng::new(seed);
    let mut cases = Vec::with_capacity(n);
    while cases.len() < n {
        let (lhs, rhs) = match rng.below(8) {
            0 => {
                let t = gen_ty(&mut rng, 3);
                (t.clone(), t)
            }
            1 | 2 => {
                let t = gen_ty(&mut rng, 3);
                let e = edit(&mut rng, &t);
                (t, e)
            }
            _ => gen_pair(&mut rng, 3),
        };
        let (Some(lj), Some(rj)) = (ty_json(&lhs), ty_json(&rhs)) else {
            panic!("generator produced a type outside the ground wire schema: {lhs:?} / {rhs:?}");
        };
        let mut cache = ConstrainCache::new();
        let rust = constrain_subtype(&lhs, &rhs, &mut cache).is_ok();
        cases.push((format!(r#"{{"lhs":{lj},"rhs":{rj}}}"#), rust));
    }

    let mut child = Command::new(oracle)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("spawn the subverdict oracle");
    let mut stdin = child.stdin.take().unwrap();
    let input: String = cases.iter().map(|(line, _)| format!("{line}\n")).collect();
    let writer = std::thread::spawn(move || stdin.write_all(input.as_bytes()));

    let mut verdicts = 0usize;
    let mut mismatches = Vec::new();
    for (i, line) in BufReader::new(child.stdout.take().unwrap())
        .lines()
        .enumerate()
    {
        let line = line.expect("read oracle verdict");
        if i >= cases.len() {
            break;
        }
        verdicts += 1;
        let (case, rust) = &cases[i];
        match line.as_str() {
            "true" if *rust => {}
            "false" if !*rust => {}
            "true" | "false" => {
                mismatches.push(format!("case {i}: rust={rust} lean={line}\n  {case}"))
            }
            other => mismatches.push(format!("case {i}: oracle said {other:?}\n  {case}")),
        }
    }
    writer.join().unwrap().expect("write cases to oracle");
    let _ = child.wait();

    let accepted = cases.iter().filter(|(_, rust)| *rust).count();
    eprintln!(
        "differential: {} cases (seed {seed}), rust accepted {accepted}, rejected {}",
        cases.len(),
        cases.len() - accepted
    );
    assert_eq!(
        verdicts,
        cases.len(),
        "oracle answered {verdicts}/{} cases",
        cases.len()
    );
    assert!(
        mismatches.is_empty(),
        "{} verdict mismatches (seed {seed}, n {n}); first 10:\n{}",
        mismatches.len(),
        mismatches[..mismatches.len().min(10)].join("\n")
    );
}
