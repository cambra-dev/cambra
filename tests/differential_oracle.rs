//! Differential oracles: three solver operations diffed against the Lean model
//! (plan and adjudications in `formal/design.md`).
//!
//! - **Subtyping.** `constrain_subtype`'s verdict on type pairs carrying no
//!   `Infer` on either side — the model's *concrete* fragment — against `subtypeCheck`
//!   (`formal/CclFormal/SubtypeChecker.lean`).
//! - **The polar merge.** Every step of a fold through `CompactType::merge`
//!   against `CompactTy.merge` (`formal/CclFormal/Merge.lean`), judged by the model's
//!   `equiv` — the equality every theorem there is stated up to. Nothing else
//!   checks that correspondence, and the merge algebra is proved rather than
//!   fuzzed, so without this the model can drift from the solver while both
//!   stay internally consistent.
//! - **The kind merge.** Every step of a fold through `CompactTypeKind::merge` against
//!   `mergeTypeKind` (`formal/CclFormal/TypeKindMerge.lean`), judged by `equivTypeKind`. The
//!   polar merge's oracle cannot reach this: the model's `CompactTy` has no Σ binder slot, so
//!   `cty_json` refuses a bound carrying binders and every case that would exercise a kind is
//!   filtered out before the wire. Without this the kind lattice and its model can diverge
//!   with both gates green, which they did.
//! - **Certain non-membership.** `TypeKind::refuses` against the model's `refuses`
//!   (`formal/CclFormal/TypeKind.lean`) on the concrete fragment. Every caller of it raises,
//!   so a disagreement is a program refused or an error missed. The model proves a refusal
//!   never lands on a member (`not_admits_of_refuses`); this checks the two sides refuse the
//!   same things.
//! - **Materialization.** Each bound the fold produces, coalesced and checked
//!   against `CompactTy.coalesce` (`formal/CclFormal/Coalesce.lean`) — the pass on
//!   the other side of the merge, and where the resolved kind's domain rule
//!   lives.
//!
//! Each oracle generates cases with a seeded PRNG, serializes them to the wire
//! schema the Lean codec defines (`formal/CclFormal/Json.lean`), and streams
//! them through the oracle binary. All three **skip loudly** when it is
//! not built (`cd formal && lake build`) so the suite stays green on machines
//! without a Lean toolchain — except under `CI`, where a skipped differential is
//! a gate reporting a pass without having compared anything, so it fails
//! (`oracle_or_skip`).
//!
//! A generated value the wire schema cannot express **panics** rather than being
//! counted. A tally of such cases reports zero whether the encoder covers the
//! fragment or the generator never reaches it, which is the same silent-skip
//! failure a default-off feature has: the two readings are indistinguishable and
//! only one of them is a working gate.
//!
//! Deliberately not generated for the subtype oracle: duplicate record/variant
//! keys — outside `Ty.WellFormed`, where the Rust's trivial-equality short-circuit and
//! its find-first arms genuinely disagree (pinned below as
//! `dup_key_record_trips_the_uniquely_keyed_invariant`) — and open variant arm
//! sets, which the model's `Ty` has no node for. Everything else in that
//! fragment is fair game.

use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};
use std::rc::Rc;

use smol_str::SmolStr;

mod type_gen;

use cambra::ccl::infer::solver::compact::{
    AtomKey, CompactType, CompactTypeKind, KindPin, compact_type,
};
use cambra::ccl::infer::solver::{
    CoalesceError, CompactGraph, ConstrainCache, coalesce_compact, constrain_subtype,
};
use cambra::ccl::{
    BaseType, BinOpKind, CompareKind, FieldKey, FunKind, Lit, Name, Openness, ProjKey, Refinement,
    Type, TypeKind, TypedExpr, TypedExprNode, ccl_utils,
};
use type_gen::{Fragment, Rng, edit, env_or, gen_leaf, gen_pred, gen_ty, maybe_kind_var};

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
        return (
            gen_ty(rng, depth, Fragment::Modelled),
            gen_ty(rng, depth, Fragment::Modelled),
        );
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
                FunKind::Data(None)
            } else {
                FunKind::Compute
            };
            let kr = if rng.chance(1, 6) {
                match kl {
                    FunKind::Data(..) => FunKind::Compute,
                    _ => FunKind::Data(None),
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
                fun_kind: k,
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

/// Serialize a predicate into the model's `Predicate` wire schema. `None` means
/// "outside the modeled vocabulary" — the case is refused rather than
/// serialized wrongly (the generator never produces such a predicate, so a
/// `None` here is a harness bug).
/// A free reference's wire spelling, carrying exactly what `Name`'s equality
/// carries: the `uid` for a `Unique` or a `Synthetic`, the string for a `Raw`,
/// the canonical spelling for a `Reserved` one. The model compares these
/// strings structurally, so anything the spelling drops is a distinction the
/// comparison loses — `field_key` and `Display` both keep only the display
/// spelling, which conflates two independently-uniquified binders that render
/// alike. The `base` and the stem ride along for a readable failure message and
/// carry no identity; both are source-shaped, so neither can break the JSON
/// string this lands in.
fn name_identity(n: &Name) -> String {
    match n {
        Name::Unique { base, uid } => format!("u{uid:?}:{base}"),
        Name::Synthetic { kind, uid } => format!("s{uid:?}:{}", kind.stem()),
        _ => n.field_key(),
    }
}

/// Serialize a refinement predicate into the model's `Predicate` schema.
///
/// `scope` holds the binders the predicate has introduced, innermost last. A
/// reference resolving into it becomes a `boundVar` index; anything else is a
/// reference to a binder *outside* the predicate and keeps its identity. That
/// split is `eq_refinement_predicate`'s rule — an interior binder compares by
/// position, an exterior one by identity — moved from comparison time to encode
/// time, which is what lets the model's structural `Predicate` equality mean the same
/// relation. Innermost-first lookup mirrors the `rposition` that makes shadowing
/// right there.
///
/// A free reference is spelled by `name_identity`, which carries what `Name`'s
/// own equality carries.
fn pred_json(e: &TypedExpr, scope: &mut Vec<Name>) -> Option<String> {
    match &e.node {
        TypedExprNode::Var(n) if *n == Name::elem() => Some(r#"{"k":"elem"}"#.to_string()),
        // The index alone: the reference's spelling hint is display metadata the
        // oracle must not see, since identity ignores it (`PiRef`).
        TypedExprNode::Var(Name::PiBound(r)) => {
            Some(format!(r#"{{"k":"piBound","i":{}}}"#, r.index))
        }
        TypedExprNode::Var(n) => Some(match scope.iter().rposition(|b| b == n) {
            Some(i) => format!(r#"{{"k":"boundVar","i":{}}}"#, scope.len() - 1 - i),
            None => format!(r#"{{"k":"var","x":"{}"}}"#, name_identity(n)),
        }),
        // A cast's target contributes only its domain's refinement *predicates*
        // (`cast_target_refinement`), which is all `eq_refinement_predicate`
        // reads of it — the target's base types are skipped there and absent
        // from the model. The set is emitted in a canonical order because
        // `Predicate`'s structural equality compares the list positionally while the
        // Rust compares a `RefinementSet`; sorting by the encoded form is what
        // makes the two agree, and it is the same move `ccl::application_order`
        // makes for the same reason. Encoded under the enclosing `scope`, since
        // a target predicate may reference a binder the outer predicate
        // introduced.
        TypedExprNode::Cast { value, target } => {
            let mut refs: Vec<String> = match ccl_utils::cast_target_refinement(target) {
                Some(set) => set
                    .iter()
                    .map(|r| pred_json(&r.predicate, scope))
                    .collect::<Option<Vec<_>>>()?,
                None => Vec::new(),
            };
            refs.sort();
            Some(format!(
                r#"{{"k":"cast","v":{},"refs":[{}]}}"#,
                pred_json(value, scope)?,
                refs.join(",")
            ))
        }
        TypedExprNode::Lambda { param, body } => {
            scope.push(param.name.clone());
            let body = pred_json(body, scope);
            scope.pop();
            Some(format!(r#"{{"k":"lam","body":{}}}"#, body?))
        }
        TypedExprNode::Lit(Lit::Int(n)) => Some(format!(r#"{{"k":"litInt","n":{n}}}"#)),
        TypedExprNode::Lit(Lit::Bool(b)) => Some(format!(r#"{{"k":"litBool","b":{b}}}"#)),
        TypedExprNode::Lit(Lit::String(s)) => Some(format!(r#"{{"k":"litStr","s":"{s}"}}"#)),
        TypedExprNode::Lit(Lit::Unit) => Some(r#"{"k":"litUnit"}"#.to_string()),
        TypedExprNode::BinOp { left, op, right } => Some(format!(
            r#"{{"k":"binop","op":"{op:?}","a":{},"b":{}}}"#,
            pred_json(left, scope)?,
            pred_json(right, scope)?
        )),
        TypedExprNode::UnaryOp(op, inner) => Some(format!(
            r#"{{"k":"unop","op":"{op:?}","a":{}}}"#,
            pred_json(inner, scope)?
        )),
        // Field and index access is an `Apply` of a `Proj` morphism, and the
        // model carries it as one node (`Predicate.proj`); a general `Apply` is
        // `Predicate.app`. Splitting on the function's shape is what keeps the two
        // apart, so the wire form matches the constructor the model compares.
        TypedExprNode::Apply { function, argument } => match &function.node {
            TypedExprNode::Proj(key) => Some(format!(
                r#"{{"k":"proj","a":{},"key":{}}}"#,
                pred_json(argument, scope)?,
                key_json(&proj_field_key(key))
            )),
            _ => Some(format!(
                r#"{{"k":"app","f":{},"a":{}}}"#,
                pred_json(function, scope)?,
                pred_json(argument, scope)?
            )),
        },
        _ => None,
    }
}

/// A projection key as the `FieldKey` the model's `Predicate.proj` carries — one
/// wire form for keys, so `key_json` stays the single encoder.
fn proj_field_key(k: &ProjKey) -> FieldKey {
    match k {
        ProjKey::Field(f) => FieldKey::Name(SmolStr::from(f.as_str())),
        ProjKey::Index(i) => FieldKey::Index(*i),
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
/// free references in its codomain become indices, which is the concrete
/// (closed) fragment the model states `Subtyping` over — a constructed `Type::Fun`
/// never carries a free name for its own binder. The generators build
/// name-based dependent shapes (the solver's mid-solve form) because that is
/// the natural way to write them; this normalizes each case into the form
/// both the solver's construction sites and the model's grammar mean.
fn close_all(ty: &Type) -> Type {
    use cambra::ccl::subst::close_pi_binder;
    match ty {
        Type::Fun {
            name,
            fun_kind,
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
                fun_kind: fun_kind.clone(),
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

/// Serialize a `Type` into the model's `Ty` wire schema; `None` for anything
/// outside the concrete fragment.
fn ty_json(t: &Type) -> Option<String> {
    Some(match t {
        Type::Base(b) => format!(r#"{{"k":"base","base":"{}"}}"#, base_json(b)),
        Type::UIntRange(n) => format!(r#"{{"k":"uintRange","n":{n}}}"#),
        Type::DataSource(s) => format!(r#"{{"k":"dataSource","name":"{s}"}}"#),
        Type::Txn => r#"{"k":"txn"}"#.to_string(),
        Type::Fun {
            name,
            fun_kind,
            domain,
            codomain,
        } => {
            let binder = match name {
                None => "null".to_string(),
                Some(Name::Raw(s)) => format!(r#""{s}""#),
                Some(_) => return None,
            };
            let kind = match fun_kind {
                FunKind::Compute => "compute",
                FunKind::Data(None) => "data",
                // A slot carrying binders is a dependent sum, and the model's `Ty` has no
                // sum — so it is outside the concrete fragment, like a kind variable.
                FunKind::Data(Some(_)) | FunKind::Var(_) => return None,
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
                .map(|r| pred_json(&r.predicate, &mut Vec::new()))
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

/// The oracle binary, or a skip — except under CI, where a skipped differential
/// is a gate that reports a pass without comparing anything. `ci.sh`'s
/// `ci_formal` applies that rule to a missing *toolchain*; this applies it to a
/// missing *binary*, which is the state a renamed `lean_exe` or a partial build
/// leaves behind, and the one a green `lake build` does not rule out.
fn oracle_or_skip(test: &str) -> Option<&'static str> {
    match oracle_path() {
        Some(path) => Some(path),
        None if std::env::var_os("CI").is_some() => {
            panic!("{test}: Lean oracle not built under CI — this gate would be a no-op");
        }
        None => {
            eprintln!("SKIPPED {test}: Lean oracle not built (cd formal && lake build)");
            None
        }
    }
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
        // A witness reference is a name for whichever domain a Σ picked, and the model
        // has no witness — outside the fragment for the same reason `ChanDom` is.
        AtomKey::ChanDom(..) | AtomKey::Witness(..) => return None,
    })
}

/// Serialize a `CompactType` into the merge model's `CompactTy` schema
/// (`formal/CclFormal/Json.lean`). The model's abstractions are applied here, so
/// the wire carries what it can express and no comparison is made against a slot
/// the model does not model:
///
/// - `vars` has no field: the model's algebra does not read variable identity.
/// - A conflicted slot's alternatives are dropped: coalesce prints them without
///   reading them, and `widest` breaks an equal-length tie by arrival order, which
///   the model does not mirror.
/// - `Openness` has no field. Nothing is hidden inside the generated fragment:
///   every generated arm set is closed and `meet_openness` keeps it closed.
///
/// `None` for a contribution outside the fragment — a history slot, a `ChanDom`
/// atom, or a predicate outside the modeled `Predicate` vocabulary.
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
            // A function over binders is a dependent sum, which `CompactTy` has no slot
            // for — outside the concrete fragment, like a `history_slot`.
            if !cf.binders.is_empty() {
                return None;
            }
            let kind = match cf.kind {
                // `Data` and `Plain` are one wire value: the model has no
                // plain-versus-sum axis, so "pinned to data" is all it can say.
                KindPin::Data | KindPin::Plain => "data",
                KindPin::Compute => "compute",
                KindPin::Conflict => "conflict",
                KindPin::Unpinned => "unknown",
                KindPin::Sum(_) => return None,
            };
            // **One domain, because that is all the slot now states.** The model keeps the
            // alternatives as a list; this solver joins them into one position and keeps
            // only `combined`, the pair that *first* had no common answer — inherited
            // across later merges, so it is a diagnostic snapshot and not the current
            // alternatives. There is nothing here to reconstruct the list from.
            //
            // `domains_disagree` is not the model's `conflict` either: it says the arms are
            // over data with no common answer, which coalesce decides, and
            // `differential_coalesce_vs_lean_model` is what compares that decision.
            //
            format!(
                r#"{{"kind":"{kind}","dom":{},"cod":{}}}"#,
                cty_json(&cf.domain)?,
                cty_json(&cf.codomain)?
            )
        }
    };
    // `null` for no refinement contribution and `[]` for a value that carries none:
    // the sentinel the model mirrors, and the merge identity the two differ by.
    let refinements = match &ct.refinements {
        None => "null".to_string(),
        Some(set) => {
            let preds: Option<Vec<String>> = set
                .iter()
                .map(|r| pred_json(&r.predicate, &mut Vec::new()))
                .collect();
            format!("[{}]", preds?.join(","))
        }
    };
    Some(format!(
        r#"{{"atoms":[{}],"rec":{rec},"var":{var},"fn":{fun},"refinements":{refinements}}}"#,
        atoms?.join(",")
    ))
}

/// One merge operand: a bound as `compact_go` builds it, or the empty
/// contribution a `Hole` compacts to (the merge identity). A generated function
/// sometimes carries a kind *variable*, which is the only way to reach
/// `KindMerge::Unknown`.
fn gen_bound(rng: &mut Rng) -> CompactType {
    if rng.chance(1, 10) {
        return compact_type(&Type::Hole).term;
    }
    let ty = gen_ty(rng, 3, Fragment::Modelled);
    compact_type(&maybe_kind_var(rng, ty)).term
}

/// Erase every function binder. `CompactTy` has no binder slot, so the model always
/// materializes `name: None` and cannot predict `coalesce_compact_go`'s
/// `kept_name`; the comparison drops the binder on this side rather than pretend
/// the model decides it.
fn strip_binders(t: &Type) -> Type {
    match t {
        Type::Fun {
            name: _,
            fun_kind,
            domain,
            codomain,
        } => Type::Fun {
            name: None,
            fun_kind: fun_kind.clone(),
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
                // Two rejections the model has no counterpart for: a kind edge whose two
                // sides state incomparable kinds, and a witness whose binder is not in
                // scope where the reference materialized. Neither is reachable from the
                // fragment this oracle serializes — a sum leaves it at `ty_json` — so
                // report no verdict rather than inventing a wire name.
                CoalesceError::KindMismatch { .. } | CoalesceError::WitnessScope { .. } => {
                    return None;
                }
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
    let Some(oracle) = oracle_or_skip("differential_coalesce_vs_lean_model") else {
        return;
    };
    let seed: u64 = env_or("CAMBRA_DIFF_SEED", 0xC0A1);
    let n: usize = env_or("CAMBRA_DIFF_N", 4000);

    let mut rng = Rng::new(seed);
    let mut cases: Vec<String> = Vec::new();
    while cases.len() < n {
        let pol = rng.chance(1, 2);
        let bounds: Vec<CompactType> = (0..1 + rng.below(3)).map(|_| gen_bound(&mut rng)).collect();
        let mut acc = bounds[0].clone();
        for b in &bounds[1..] {
            acc = CompactType::merge_bounds(pol, acc, b.clone());
        }
        let graph = CompactGraph {
            term: acc.clone(),
            rec_vars: std::collections::BTreeMap::new(),
        };
        let (Some(ct), Some(got)) = (cty_json(&acc), coalesce_outcome(&coalesce_compact(&graph)))
        else {
            panic!("generator produced a bound outside the wire schema: {acc:?}");
        };
        cases.push(format!(
            r#"{{"op":"coalesce","pol":{pol},"ct":{ct},"got":{got}}}"#
        ));
    }

    let verdicts = ask_oracle(oracle, &cases);
    let mismatches: Vec<String> = verdicts
        .iter()
        .zip(&cases)
        .filter(|(v, _)| v.as_str() != "ok")
        .map(|(v, case)| format!("{v}\n  case: {case}"))
        .collect();
    eprintln!(
        "coalesce differential: {} bounds (seed {seed}), {} mismatches",
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

/// A Σ binder's kind over `Type`, on the wire. Reuses [`ty_json`], so a parameter or candidate
/// outside the concrete fragment takes the whole kind out with it.
fn tk_json(k: &TypeKind) -> Option<String> {
    Some(match k {
        TypeKind::Type => r#"{"k":"everyType"}"#.to_string(),
        TypeKind::UIntRanges => r#"{"k":"uintRanges"}"#.to_string(),
        TypeKind::SubtypesOf(p) => format!(r#"{{"k":"subtypesOf","param":{}}}"#, ty_json(p)?),
        TypeKind::Enumerated(ds) => {
            let each = ds.iter().map(ty_json).collect::<Option<Vec<_>>>()?;
            format!(r#"{{"k":"candidates","ds":[{}]}}"#, each.join(","))
        }
    })
}

/// A kind over generated types, weighted toward the two arms that decide. The other two refuse
/// nothing and so agree by construction — generating them checks that both sides know it.
fn gen_type_kind(rng: &mut Rng) -> TypeKind {
    match rng.below(10) {
        0 => TypeKind::Type,
        1..=3 => TypeKind::UIntRanges,
        4..=5 => TypeKind::SubtypesOf(Box::new(gen_ty(rng, 2, Fragment::Modelled))),
        _ => TypeKind::Enumerated(
            (0..rng.below(3))
                .map(|_| gen_ty(rng, 2, Fragment::Modelled))
                .collect(),
        ),
    }
}

/// `TypeKind::refuses` against the model's, on the concrete fragment.
///
/// `Ty` carries no `Infer` and no `Hole`, so what the wire can express of
/// `Type::holds_an_unresolved_position` is its refinement disjunct — which is the one that
/// decides real cases anyway, a refined range being the thing the range test exists to refuse.
///
/// Half the subjects are drawn from the kind's own parameter or candidates. A sampler that only
/// ever asks about an unrelated type checks one of the two answers, and the refusing one is
/// already the easy side.
#[test]
fn differential_refuses_vs_lean_model() {
    let Some(oracle) = oracle_or_skip("differential_refuses_vs_lean_model") else {
        return;
    };
    let seed: u64 = env_or("CAMBRA_DIFF_SEED", 0x5EED);
    let n: usize = env_or("CAMBRA_DIFF_N", 4000);

    let mut rng = Rng::new(seed);
    let mut cases: Vec<String> = Vec::new();
    let mut refused = 0usize;
    while cases.len() < n {
        let kind = gen_type_kind(&mut rng);
        let named = rng.chance(1, 2);
        let ty = match &kind {
            TypeKind::Enumerated(ds) if named && !ds.is_empty() => {
                ds[rng.below(ds.len() as u64) as usize].clone()
            }
            TypeKind::SubtypesOf(p) if named => (**p).clone(),
            _ => gen_ty(&mut rng, 2, Fragment::Modelled),
        };
        let (Some(k), Some(t)) = (tk_json(&kind), ty_json(&ty)) else {
            continue;
        };
        let got = kind.refuses(&ty);
        refused += usize::from(got);
        cases.push(format!(
            r#"{{"op":"refuses","kind":{k},"ty":{t},"got":{got}}}"#
        ));
    }

    let verdicts = ask_oracle(oracle, &cases);
    let mismatches: Vec<String> = verdicts
        .iter()
        .zip(&cases)
        .filter(|(v, _)| v.as_str() != "ok")
        .map(|(v, case)| format!("{v}\n  case: {case}"))
        .collect();
    eprintln!(
        "refuses differential: {} cases (seed {seed}), rust refused {refused}, {} mismatches",
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
    // Both answers, or the sweep is checking one of them.
    assert!(
        refused > cases.len() / 20 && refused < cases.len() - cases.len() / 20,
        "one-sided sweep: {refused} of {} refused (seed {seed})",
        cases.len()
    );
    assert!(
        mismatches.is_empty(),
        "{} refuses mismatches (seed {seed}, n {n}); first 5:\n{}",
        mismatches.len(),
        mismatches[..mismatches.len().min(5)].join("\n")
    );
}

/// A Σ binder's kind on the wire. Reuses [`cty_json`] for the positions it carries, so a
/// parameter or candidate outside the wire schema takes the whole kind out with it.
fn ctk_json(k: &CompactTypeKind) -> Option<String> {
    Some(match k {
        CompactTypeKind::Type => r#"{"k":"everyType"}"#.to_string(),
        CompactTypeKind::UIntRanges => r#"{"k":"uintRanges"}"#.to_string(),
        CompactTypeKind::SubtypesOf(p) => {
            format!(r#"{{"k":"subtypesOf","param":{}}}"#, cty_json(p)?)
        }
        CompactTypeKind::Enumerated(ds) => {
            let each = ds.iter().map(cty_json).collect::<Option<Vec<_>>>()?;
            format!(r#"{{"k":"candidates","ds":[{}]}}"#, each.join(","))
        }
    })
}

/// A Σ binder's kind: the two that name members carry generated positions, the two that state a
/// property carry nothing. Weighted toward the member-naming pair, which is where the rows that
/// can disagree live — and a candidate list of length zero is generated, since the empty kind is
/// what both degenerate parameters answer.
fn gen_kind(rng: &mut Rng) -> CompactTypeKind {
    match rng.below(10) {
        0 => CompactTypeKind::Type,
        1 => CompactTypeKind::UIntRanges,
        2..=5 => CompactTypeKind::SubtypesOf(Box::new(gen_bound(rng))),
        _ => CompactTypeKind::Enumerated((0..rng.below(3)).map(|_| gen_bound(rng)).collect()),
    }
}

/// The kind merge, folded, against the model's `mergeTypeKind`.
///
/// A **fold** rather than a pair, because the parameters worth testing are ones the merge itself
/// builds: two incomparable bounds meet to a parameter naming two shapes, which no single
/// generated type is, and which is exactly the state the rows that read a parameter must refuse.
/// The generator reaches the other degenerate parameter directly — `gen_bound` returns a
/// position compacted from a `Hole`, which names no shape.
#[test]
fn differential_type_kind_merge_vs_lean_model() {
    let Some(oracle) = oracle_or_skip("differential_type_kind_merge_vs_lean_model") else {
        return;
    };
    let seed: u64 = env_or("CAMBRA_DIFF_SEED", 0x5EED);
    let n: usize = env_or("CAMBRA_DIFF_N", 4000);

    let mut rng = Rng::new(seed);
    let mut cases: Vec<String> = Vec::new();
    while cases.len() < n {
        let pol = rng.chance(1, 2);
        let kinds: Vec<CompactTypeKind> =
            (0..2 + rng.below(3)).map(|_| gen_kind(&mut rng)).collect();
        let mut acc = kinds[0].clone();
        for k in &kinds[1..] {
            let merged = CompactTypeKind::merge_kinds(pol, acc.clone(), k.clone());
            let (Some(l), Some(r), Some(g)) = (ctk_json(&acc), ctk_json(k), ctk_json(&merged))
            else {
                // A kind carrying a position the wire cannot express: skip the *case*, not the
                // fold, and keep folding — the merge's own answers are what this checks, and
                // the same silent-skip reading a tally would give applies to a wire gap here
                // as anywhere else, so the fold must not quietly shorten.
                acc = merged;
                continue;
            };
            cases.push(format!(
                r#"{{"op":"mergeKind","pol":{pol},"lhs":{l},"rhs":{r},"got":{g}}}"#
            ));
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
        "kind merge differential: {} steps (seed {seed}), {} mismatches",
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
        "{} kind merge mismatches (seed {seed}, n {n}); first 5:\n{}",
        mismatches.len(),
        mismatches[..mismatches.len().min(5)].join("\n")
    );
}

/// Differential on the *polar merge*: fold generated bound lists exactly as
/// `compact_go` folds a variable's bounds, and check every step against the
/// model's `merge`. Each step's `lhs` is the previous step's result, so the
/// conflicted and multi-alternative states only merging produces are operands
/// too — which is where a pairwise rule and an associative one diverge.
#[test]
fn differential_polar_merge_vs_lean_model() {
    let Some(oracle) = oracle_or_skip("differential_polar_merge_vs_lean_model") else {
        return;
    };
    let seed: u64 = env_or("CAMBRA_DIFF_SEED", 0x5EED);
    let n: usize = env_or("CAMBRA_DIFF_N", 4000);

    let mut rng = Rng::new(seed);
    let mut cases: Vec<String> = Vec::new();
    while cases.len() < n {
        let pol = rng.chance(1, 2);
        let bounds: Vec<CompactType> = (0..2 + rng.below(3)).map(|_| gen_bound(&mut rng)).collect();
        let mut acc = bounds[0].clone();
        for b in &bounds[1..] {
            let merged = CompactType::merge_bounds(pol, acc.clone(), b.clone());
            let (Some(l), Some(r), Some(g)) = (cty_json(&acc), cty_json(b), cty_json(&merged))
            else {
                panic!("generator produced a bound outside the wire schema: {acc:?} / {b:?}");
            };
            cases.push(format!(
                r#"{{"op":"merge","pol":{pol},"lhs":{l},"rhs":{r},"got":{g}}}"#
            ));
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
        "merge differential: {} steps (seed {seed}), {} mismatches",
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

#[test]
fn differential_concrete_subtype_vs_lean_model() {
    let Some(oracle) = oracle_or_skip("differential_concrete_subtype_vs_lean_model") else {
        return;
    };
    let seed: u64 = env_or("CAMBRA_DIFF_SEED", 0xC0FFEE);
    let n: usize = env_or("CAMBRA_DIFF_N", 4000);

    let mut rng = Rng::new(seed);
    let mut cases = Vec::with_capacity(n);
    while cases.len() < n {
        let (lhs, rhs) = match rng.below(8) {
            0 => {
                let t = gen_ty(&mut rng, 3, Fragment::Modelled);
                (t.clone(), t)
            }
            1 | 2 => {
                let t = gen_ty(&mut rng, 3, Fragment::Modelled);
                let e = edit(&mut rng, &t, Fragment::Modelled);
                (t, e)
            }
            _ => gen_pair(&mut rng, 3),
        };
        // Enter the model's concrete fragment, which is closed — what
        // construction produces, and what the model's grammar means.
        let (lhs, rhs) = (close_all(&lhs), close_all(&rhs));
        let (Some(lj), Some(rj)) = (ty_json(&lhs), ty_json(&rhs)) else {
            panic!("generator produced a type outside the concrete wire schema: {lhs:?} / {rhs:?}");
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

    let lines: Vec<String> = cases.iter().map(|(line, _)| line.clone()).collect();
    let verdicts_out = ask_oracle(oracle, &lines);

    let mut mismatches = Vec::new();
    for (i, (line, (case, rust))) in verdicts_out.iter().zip(&cases).enumerate() {
        match line.as_str() {
            "true" if *rust => {}
            "false" if !*rust => {}
            "true" | "false" => {
                mismatches.push(format!("case {i}: rust={rust} lean={line}\n  {case}"))
            }
            other => mismatches.push(format!("case {i}: oracle said {other:?}\n  {case}")),
        }
    }
    let verdicts = verdicts_out.len();

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

/// A free reference's wire spelling is its identity, not its display name.
/// `Name::fresh` mints a `Unique` whose identity is its `uid`, so two binders
/// spelled alike are distinct to the solver; encoding them alike would make the
/// model accept a refinement demand the solver rejects.
#[test]
fn two_uniquified_binders_that_render_alike_encode_apart() {
    let x1 = Name::fresh("x");
    let x2 = Name::fresh("x");
    assert_ne!(x1, x2, "`fresh` mints a distinct uid per binder");
    assert_eq!(x1.field_key(), x2.field_key(), "they render alike");

    let encode = |n: &Name| pred_json(&TypedExpr::var(n.clone()), &mut Vec::new()).unwrap();
    assert_ne!(
        encode(&x1),
        encode(&x2),
        "the wire spelling must carry the uid, or the comparison loses the distinction"
    );
    assert_eq!(encode(&x1), encode(&x1), "and it is stable for one binder");
}
