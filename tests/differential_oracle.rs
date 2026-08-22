//! Differential oracles: two solver operations diffed against the Lean model
//! (plan and adjudications in `formal/design.md`).
//!
//! - **Ground subtyping.** `constrain_subtype`'s verdict on ground type pairs
//!   (no `Infer` on either side) against `subCheck`
//!   (`formal/CclFormal/Decide.lean`).
//! - **The bound merge.** Every step of a fold through `CompactType::merge`
//!   against `CTy.merge` (`formal/CclFormal/Merge.lean`), judged by the model's
//!   `eqv` — the equality every theorem there is stated up to. Nothing else
//!   checks that correspondence, and the merge algebra is proved rather than
//!   fuzzed, so without this the model can drift from the solver while both
//!   stay internally consistent.
//!
//! Both generate cases with a seeded PRNG, serialize them to the wire schema the
//! Lean codec defines (`formal/CclFormal/Json.lean`), and stream them through
//! the oracle binary. They **skip loudly** when it is not built (`cd formal &&
//! lake build`) so the suite stays green on machines without a Lean toolchain.
//!
//! Deliberately not generated for the subtype oracle: duplicate record/variant
//! keys — outside `Ty.WF`, where the Rust's trivial-equality short-circuit and
//! its find-first arms genuinely disagree (pinned below as
//! `dup_key_record_trips_the_uniquely_keyed_invariant`) — and open variant arm
//! sets, which the model's `Ty` has no node for. Everything else in the ground
//! fragment is fair game.

use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};
use std::rc::Rc;

use smol_str::SmolStr;

mod type_gen;

use cambra::ccl::infer::solver::compact::{AtomKey, CompactType, KindMerge, compact_type};
use cambra::ccl::infer::solver::{
    CoalesceError, CompactGraph, ConstrainCache, coalesce_compact, constrain_subtype,
};
use cambra::ccl::{
    BaseType, BinOpKind, CompareKind, FieldKey, FunKind, Lit, Name, Openness, Refinement, Type,
    TypedExpr, TypedExprNode,
};
use type_gen::{Rng, gen_leaf, gen_pred, gen_ty, maybe_kind_var};

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
            _ => gen_ty(rng, 2),
        },
        _ => gen_ty(rng, 3),
    }
}

/// `__elem == <name>` — the dependent-refinement predicate shape, aimed at
/// a specific Pi binder.
fn dep_pred(name: &str) -> Rc<TypedExpr> {
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
            (
                Type::Variant(ls, Openness::Closed),
                Type::Variant(rs, Openness::Closed),
            )
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
        // The index alone: the reference's spelling hint is display metadata the
        // oracle must not see, since identity ignores it (`PiRef`).
        TypedExprNode::Var(Name::PiBound(r)) => {
            Some(format!(r#"{{"k":"piBound","i":{}}}"#, r.index))
        }
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

/// Close every function of a generated type bottom-up: each named binder's
/// free references in its codomain become indices, which is the ground
/// (closed) fragment the model states `Sub` over — a constructed `Type::Fun`
/// never carries a free name for its own binder. The generators build
/// name-based dependent shapes (the solver's mid-solve form) because that is
/// the natural way to write them; this normalizes each case into the form
/// both the solver's construction sites and the model's grammar mean.
fn close_all(ty: &Type) -> Type {
    use cambra::ccl::subst::close_pi_binder;
    match ty {
        Type::Fun {
            name,
            kind,
            domain,
            codomain,
        } => {
            let domain = close_all(domain);
            let codomain = close_all(codomain);
            let codomain = match name {
                Some(b) => close_pi_binder(b, &codomain),
                None => codomain,
            };
            Type::Fun {
                name: name.clone(),
                kind: kind.clone(),
                domain: Box::new(domain),
                codomain: Box::new(codomain),
            }
        }
        Type::Refinement(base, r) => Type::Refinement(Box::new(close_all(base)), r.clone()),
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(close_all).collect()),
        Type::Record(fs) => {
            Type::Record(fs.iter().map(|(n, t)| (n.clone(), close_all(t))).collect())
        }
        Type::Variant(tags, openness) => Type::Variant(
            tags.iter()
                .map(|(k, t)| (k.clone(), close_all(t)))
                .collect(),
            *openness,
        ),
        other => other.clone(),
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
        // Closed only: the model's `variant` node is an arm set with no
        // openness, so an open arm set is outside the fragment and falls
        // through to `None`.
        Type::Variant(tags, Openness::Closed) => {
            let ts: Option<Vec<_>> = tags
                .iter()
                .map(|(k, t)| Some(format!(r#"[{},{}]"#, key_json(k), ty_json(t)?)))
                .collect();
            format!(r#"{{"k":"variant","tags":[{}]}}"#, ts?.join(","))
        }
        // The model's `refined` node carries a whole refinement set, exactly like
        // `RefinementSet`.
        Type::Refinement(base, refinements) => {
            let preds: Option<Vec<String>> = refinements
                .iter()
                .map(|r| pred_json(&r.predicate))
                .collect();
            format!(
                r#"{{"k":"refined","base":{},"refinements":[{}]}}"#,
                ty_json(base)?,
                preds?.join(",")
            )
        }
        _ => return None,
    })
}

/// The oracle binary, or `None` when it is not built (`cd formal && lake build`) —
/// the harnesses skip themselves loudly rather than fail on a machine with no Lean
/// toolchain.
fn oracle_path() -> Option<&'static str> {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/formal/.lake/build/bin/subverdict"
    );
    std::path::Path::new(path).exists().then_some(path)
}

/// Stream one case per line through the oracle and collect its verdict lines.
fn ask_oracle(oracle: &str, cases: &[String]) -> Vec<String> {
    let mut child = Command::new(oracle)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("spawn the oracle");
    let mut stdin = child.stdin.take().unwrap();
    let input: String = cases.iter().map(|line| format!("{line}\n")).collect();
    let writer = std::thread::spawn(move || stdin.write_all(input.as_bytes()));
    let verdicts: Vec<String> = BufReader::new(child.stdout.take().unwrap())
        .lines()
        .take(cases.len())
        .map(|l| l.expect("read an oracle verdict"))
        .collect();
    writer.join().unwrap().expect("write cases to the oracle");
    let _ = child.wait();
    verdicts
}

/// Serialize an atom into the merge model's `Atom` schema. `None` for
/// `ChanDom`, which the model excludes for the same reason `Ty` excludes the
/// pipeline transients.
fn atom_json(a: &AtomKey) -> Option<String> {
    Some(match a {
        AtomKey::Prim(b) => format!(r#"{{"k":"prim","base":"{}"}}"#, base_json(b)),
        AtomKey::UIntRange(n) => format!(r#"{{"k":"uintRange","n":{n}}}"#),
        AtomKey::Source(s) => format!(r#"{{"k":"source","s":"{s}"}}"#),
        AtomKey::Txn => r#"{"k":"txn"}"#.to_string(),
        AtomKey::ChanDom(..) => return None,
    })
}

/// Serialize a `CompactType` into the merge model's `CTy` schema
/// (`formal/CclFormal/Json.lean`). The model's abstractions are applied here, so
/// the wire carries what it can express and no comparison is made against a slot
/// the model does not model:
///
/// - `vars` has no field: the ground algebra does not read variable identity.
/// - A conflicted slot's alternatives are dropped: coalesce prints them without
///   reading them, and `widest` breaks an equal-length tie by arrival order, which
///   the model does not mirror.
/// - `Openness` has no field. Nothing is hidden inside the generated fragment:
///   every generated arm set is closed and `meet_openness` keeps it closed.
///
/// `None` for a contribution outside the fragment — a history slot, a `ChanDom`
/// atom, or a predicate outside the modeled `Pred` vocabulary.
fn cty_json(ct: &CompactType) -> Option<String> {
    if ct.history_slot.is_some() {
        return None;
    }
    let atoms: Option<Vec<String>> = ct.atoms.iter().map(atom_json).collect();
    let map = |m: &std::collections::BTreeMap<FieldKey, CompactType>| -> Option<String> {
        let entries: Option<Vec<String>> = m
            .iter()
            .map(|(k, v)| Some(format!("[{},{}]", key_json(k), cty_json(v)?)))
            .collect();
        Some(format!("[{}]", entries?.join(",")))
    };
    let rec = match &ct.rec {
        None => "null".to_string(),
        Some(m) => map(m)?,
    };
    let var = match &ct.var {
        None => "null".to_string(),
        Some(v) => map(&v.tags)?,
    };
    let fun = match &ct.fun {
        None => "null".to_string(),
        Some(cf) => {
            let kind = match cf.kind {
                KindMerge::Data => "data",
                KindMerge::Compute => "compute",
                KindMerge::Conflict => "conflict",
                KindMerge::Unknown => "unknown",
            };
            // A conflicted slot's alternatives are diagnostic — coalesce prints
            // them and reads nothing — and `widest` picks between equal-length
            // lists by arrival order, so the model drops the payload rather than
            // mirror an order-dependent choice.
            let doms: Option<Vec<String>> = match cf.kind {
                KindMerge::Conflict => Some(Vec::new()),
                _ => cf.domains.iter().map(cty_json).collect(),
            };
            format!(
                r#"{{"kind":"{kind}","doms":[{}],"cod":{}}}"#,
                doms?.join(","),
                cty_json(&cf.codomain)?
            )
        }
    };
    // `null` for no refinement contribution and `[]` for a value that carries none:
    // the sentinel the model mirrors, and the merge identity the two differ by.
    let refinements = match &ct.refinements {
        None => "null".to_string(),
        Some(set) => {
            let preds: Option<Vec<String>> = set.iter().map(|r| pred_json(&r.predicate)).collect();
            format!("[{}]", preds?.join(","))
        }
    };
    Some(format!(
        r#"{{"atoms":[{}],"rec":{rec},"var":{var},"fn":{fun},"refinements":{refinements}}}"#,
        atoms?.join(",")
    ))
}

/// One merge operand: a ground bound as `compact_go` builds it, or the empty
/// contribution a `Hole` compacts to (the merge identity). A generated function
/// sometimes carries a kind *variable*, which is the only way to reach
/// `KindMerge::Unknown`.
fn gen_bound(rng: &mut Rng) -> CompactType {
    if rng.chance(1, 10) {
        return compact_type(&Type::Hole).term;
    }
    let ty = gen_ty(rng, 3);
    compact_type(&maybe_kind_var(rng, ty)).term
}

/// Erase every function binder. `CTy` has no binder slot, so the model always
/// materializes `name: None` and cannot predict `coalesce_compact_go`'s
/// `kept_name`; the comparison drops the binder on this side rather than pretend
/// the model decides it.
fn strip_binders(t: &Type) -> Type {
    match t {
        Type::Fun {
            name: _,
            kind,
            domain,
            codomain,
        } => Type::Fun {
            name: None,
            kind: kind.clone(),
            domain: Box::new(strip_binders(domain)),
            codomain: Box::new(strip_binders(codomain)),
        },
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(strip_binders).collect()),
        Type::Record(fs) => Type::Record(
            fs.iter()
                .map(|(n, t)| (n.clone(), strip_binders(t)))
                .collect(),
        ),
        Type::Variant(tags, o) => Type::Variant(
            tags.iter()
                .map(|(k, t)| (k.clone(), strip_binders(t)))
                .collect(),
            *o,
        ),
        Type::Refinement(b, cs) => Type::Refinement(Box::new(strip_binders(b)), cs.clone()),
        other => other.clone(),
    }
}

/// The wire form of one materialization outcome. `None` when the type falls
/// outside the model's grammar (a nested `Infer`, say).
fn coalesce_outcome(r: &Result<Type, CoalesceError>) -> Option<String> {
    match r {
        // A position with nothing concrete materializes to a fresh variable, which
        // the model reports as a fact rather than a type: `Ty` has no `Infer` node,
        // so the refinements the Rust hangs on it are outside the comparison too.
        Ok(t) if matches!(peel(t), Type::Infer(_)) => Some(r#"{"k":"unresolved"}"#.to_string()),
        Ok(t) => Some(format!(
            r#"{{"k":"ok","ty":{}}}"#,
            ty_json(&strip_binders(t))?
        )),
        Err(e) => {
            let kind = match e {
                CoalesceError::IncompatibleBounds { .. } => "IncompatibleBounds",
                CoalesceError::UnresolvedPartial { .. } => "UnresolvedPartial",
                CoalesceError::RecursiveType { .. } => "RecursiveType",
                CoalesceError::DomainJoinConflict { .. } => "DomainJoinConflict",
                CoalesceError::KindConflict { .. } => "KindConflict",
            };
            Some(format!(r#"{{"k":"err","kind":"{kind}"}}"#))
        }
    }
}

/// A type with its refinement layers peeled.
fn peel(t: &Type) -> &Type {
    match t {
        Type::Refinement(b, _) => peel(b),
        other => other,
    }
}

/// Differential on **materialization**: coalesce each bound the fold produces and
/// check the outcome against the model. This is the pass on the other side of the
/// merge, and the one where the resolved kind's domain rule lives.
#[test]
fn differential_coalesce_vs_lean_model() {
    let Some(oracle) = oracle_path() else {
        eprintln!(
            "SKIPPED differential_coalesce_vs_lean_model: Lean oracle not built \
             (cd formal && lake build)"
        );
        return;
    };
    let seed: u64 = std::env::var("CAMBRA_DIFF_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0xC0A1);
    let n: usize = std::env::var("CAMBRA_DIFF_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(4000);

    let mut rng = Rng::new(seed);
    let mut cases: Vec<String> = Vec::new();
    let mut skipped = 0usize;
    while cases.len() < n {
        let pol = rng.chance(1, 2);
        let bounds: Vec<CompactType> = (0..1 + rng.below(3)).map(|_| gen_bound(&mut rng)).collect();
        let mut acc = bounds[0].clone();
        for b in &bounds[1..] {
            acc = CompactType::merge(pol, acc, b.clone());
        }
        let graph = CompactGraph {
            term: acc.clone(),
            rec_vars: std::collections::BTreeMap::new(),
        };
        match (cty_json(&acc), coalesce_outcome(&coalesce_compact(&graph))) {
            (Some(ct), Some(got)) => cases.push(format!(
                r#"{{"op":"coalesce","pol":{pol},"ct":{ct},"got":{got}}}"#
            )),
            _ => skipped += 1,
        }
    }

    let verdicts = ask_oracle(oracle, &cases);
    let mismatches: Vec<String> = verdicts
        .iter()
        .zip(&cases)
        .filter(|(v, _)| v.as_str() != "ok")
        .map(|(v, case)| format!("{v}\n  case: {case}"))
        .collect();
    eprintln!(
        "coalesce differential: {} bounds (seed {seed}), {skipped} outside the fragment, {} mismatches",
        cases.len(),
        mismatches.len()
    );
    assert_eq!(
        verdicts.len(),
        cases.len(),
        "oracle answered {}/{}",
        verdicts.len(),
        cases.len()
    );
    assert!(
        mismatches.is_empty(),
        "{} coalesce mismatches (seed {seed}, n {n}); first 5:\n{}",
        mismatches.len(),
        mismatches[..mismatches.len().min(5)].join("\n")
    );
}

/// Differential on the *bound merge*: fold generated bound lists exactly as
/// `compact_go` folds a variable's bounds, and check every step against the
/// model's `merge`. Each step's `lhs` is the previous step's result, so the
/// conflicted and multi-alternative states only merging produces are operands
/// too — which is where a pairwise rule and an associative one diverge.
#[test]
fn differential_bound_merge_vs_lean_model() {
    let Some(oracle) = oracle_path() else {
        eprintln!(
            "SKIPPED differential_bound_merge_vs_lean_model: Lean oracle not built \
             (cd formal && lake build)"
        );
        return;
    };
    let seed: u64 = std::env::var("CAMBRA_DIFF_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0x5EED);
    let n: usize = std::env::var("CAMBRA_DIFF_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(4000);

    let mut rng = Rng::new(seed);
    let mut cases: Vec<String> = Vec::new();
    let mut skipped = 0usize;
    while cases.len() < n {
        let pol = rng.chance(1, 2);
        let bounds: Vec<CompactType> = (0..2 + rng.below(3)).map(|_| gen_bound(&mut rng)).collect();
        let mut acc = bounds[0].clone();
        for b in &bounds[1..] {
            let merged = CompactType::merge(pol, acc.clone(), b.clone());
            match (cty_json(&acc), cty_json(b), cty_json(&merged)) {
                (Some(l), Some(r), Some(g)) => cases.push(format!(
                    r#"{{"op":"merge","pol":{pol},"lhs":{l},"rhs":{r},"got":{g}}}"#
                )),
                _ => skipped += 1,
            }
            acc = merged;
        }
    }

    let verdicts = ask_oracle(oracle, &cases);
    let mismatches: Vec<String> = verdicts
        .iter()
        .zip(&cases)
        .filter(|(v, _)| v.as_str() != "ok")
        .map(|(v, case)| format!("{v}\n  case: {case}"))
        .collect();
    eprintln!(
        "merge differential: {} steps (seed {seed}), {skipped} outside the fragment, {} mismatches",
        cases.len(),
        mismatches.len()
    );
    assert_eq!(
        verdicts.len(),
        cases.len(),
        "oracle answered {}/{} cases",
        verdicts.len(),
        cases.len()
    );
    assert!(
        mismatches.is_empty(),
        "{} merge mismatches (seed {seed}, n {n}); first 5:\n{}",
        mismatches.len(),
        mismatches[..mismatches.len().min(5)].join("\n")
    );
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
        // Enter the ground (closed) fragment: what construction produces and
        // what the model's grammar means.
        let (lhs, rhs) = (close_all(&lhs), close_all(&rhs));
        let (Some(lj), Some(rj)) = (ty_json(&lhs), ty_json(&rhs)) else {
            panic!("generator produced a type outside the ground wire schema: {lhs:?} / {rhs:?}");
        };
        if let Some(path) = std::env::var_os("CAMBRA_DIFF_DUMP") {
            use std::io::Write;
            if let Ok(mut f) = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)
            {
                let _ = writeln!(f, "{{\"op\":\"sub\",\"lhs\":{lj},\"rhs\":{rj}}}");
            }
        }
        let mut cache = ConstrainCache::new();
        let rust = constrain_subtype(&lhs, &rhs, &mut cache).is_ok();
        cases.push((format!(r#"{{"op":"sub","lhs":{lj},"rhs":{rj}}}"#), rust));
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
