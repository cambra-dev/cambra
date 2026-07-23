// ---------------------------------------------------------------------------
// Operator/projection scheme registry (Step 7b)
// ---------------------------------------------------------------------------

use std::collections::BTreeMap;

use crate::ccl::FieldKey;
use crate::ccl::infer::solver::{PolyScheme, fresh_var, fun, prim};
use crate::ccl::{AggregateKind, BaseType, BinOpKind, Builtin, Level, Type, UnaryOpKind};

use super::product;

/// Schemes for operators that lift cleanly to fixed signatures.
///
/// Each scheme is built once per [`InferCtx`](super::context::InferCtx);
/// `instantiate` runs at every use site to mint fresh quantified variables.
/// Operators with structural result types (`BinOp::CollectionUnion`) and nodes
/// whose typing rules require AST-level reasoning (`Apply`, `Lambda`,
/// `Let`, `Case`, `List`, …) are handled by per-case rules in
/// `emit_node` rather than via this registry.
pub struct OperatorSchemes {
    /// `∀α. α → α → α` — both operands agree, result is the same type.
    /// Matches today's `infer_binop` Arithmetic rule which only enforces
    /// operand agreement, not numeric-ness (operator conversion catches
    /// non-numeric arithmetic later).
    arithmetic: PolyScheme,
    /// `∀α. α → α → Bool`.
    compare: PolyScheme,
    /// `Bool → Bool → Bool`.
    bool_logic: PolyScheme,
    /// `String → String → String`.
    concat: PolyScheme,
    /// `Int → Int`.
    neg: PolyScheme,
    /// `Bool → Bool`.
    not_op: PolyScheme,
    /// `∀α. (α → Int) → Int` — the full Sum operator type, applied
    /// directly to the input collection (function), folding its Int
    /// codomain to an Int.
    aggregate_sum: PolyScheme,
    /// `∀α γ. (α → γ) → γ` — the full Max operator type, applied directly
    /// to the input collection (function), folding its codomain γ to a
    /// result of the same type.
    aggregate_max: PolyScheme,
    /// `∀α γ. (α → γ) → unit` — the terminal aggregate ([`AggregateKind::Drain`]):
    /// consume a collection of any element type and yield `unit`. Used by the
    /// `set` constructor's group collapse.
    aggregate_drain: PolyScheme,
    /// `∀α β. ((α → β), β) → β` — extract the last value from a
    /// function-typed stream, falling back to the default scalar when the
    /// stream's domain is empty. Polymorphic in both the stream domain
    /// (`α`) and the shared codomain/default type (`β`); inline construction
    /// is required because both vars are shared across positions, which
    /// `normalize_annotation` (one fresh var per `Hole`) can't express.
    final_or_default: PolyScheme,
    /// `∀𝑎. 𝑎 ⇒ Σ σ ∈ {𝑎}. σ` — [`Builtin::Box`], the way into a sum. Inline-built
    /// because `𝑎` is shared between the parameter and the sum's single candidate,
    /// and because the candidate sits inside a [`TypeKind`] rather than in a type
    /// position `normalize_annotation` would reach.
    box_intro: PolyScheme,
    /// `∀ι ν. ((ι → ν), ι, ν) → ν` — the history value at the predecessor
    /// of the given position, or the default at the first position (the
    /// letrec guard accessor, [`Builtin::GetPrevSeq`]). Inline-built for
    /// the same reason as `final_or_default`: the domain `ι` and value `ν`
    /// are each shared across positions.
    get_prev_seq: PolyScheme,
    /// `∀ι ν. ((ι → {time: Txn, write: ν}), Txn, ν) → ν` — the write carried
    /// by the latest commit strictly before the given time, or the default if
    /// none (the transaction-domain guard accessor, [`Builtin::GetPrevTxn`]).
    /// The history domain `ι` (the writer's iteration domain) and the value `ν`
    /// are quantified; the search position and the record's `time` field are the
    /// concrete commit-time `Txn`. `ν` is shared across the `write` field, the
    /// default, and the result, so this is inline-built like `get_prev_seq`.
    get_prev_txn: PolyScheme,
}

impl OperatorSchemes {
    /// Build the registry. Schemes are quantified at level 0; their
    /// internal fresh vars live at level 1 so `instantiate(0)` mints
    /// fresh copies at the active inference level.
    pub fn new() -> Self {
        const SCHEME_LEVEL: Level = 0;
        const BODY_LEVEL: Level = 1;

        // Box: ∀α. α ⇒ Σ σ ∈ {α}. σ — the sum over the one candidate α, body the bare
        // witness. `α` occurs in the candidate list, which is an *invariant* position,
        // so the argument's type is pinned exactly rather than widened on the way in.
        let alpha = fresh_var(BODY_LEVEL);
        let box_intro = PolyScheme::poly(
            SCHEME_LEVEL,
            fun(
                alpha.clone(),
                Type::Sigma(Box::new(crate::ccl::ty::SigmaType::of(
                    crate::ccl::ty::TypeKind::Enumerated(vec![alpha]),
                ))),
            ),
        );

        // Arithmetic: ∀α. α → α → α
        let alpha = fresh_var(BODY_LEVEL);
        let arithmetic =
            PolyScheme::poly(SCHEME_LEVEL, fun(alpha.clone(), fun(alpha.clone(), alpha)));

        // Compare: ∀α. α → α → Bool
        let alpha = fresh_var(BODY_LEVEL);
        let compare = PolyScheme::poly(
            SCHEME_LEVEL,
            fun(alpha.clone(), fun(alpha, prim(BaseType::Bool))),
        );

        // BoolLogic: Bool → Bool → Bool
        let bool_logic = PolyScheme::mono(fun(
            prim(BaseType::Bool),
            fun(prim(BaseType::Bool), prim(BaseType::Bool)),
        ));

        // Concat: String → String → String
        let concat = PolyScheme::mono(fun(
            prim(BaseType::String),
            fun(prim(BaseType::String), prim(BaseType::String)),
        ));

        // Neg: Int → Int
        let neg = PolyScheme::mono(fun(prim(BaseType::Int), prim(BaseType::Int)));

        // Not: Bool → Bool
        let not_op = PolyScheme::mono(fun(prim(BaseType::Bool), prim(BaseType::Bool)));

        // Sum: ∀α. (α ⤇ Int) → Int. The full operator type: consumes a
        // **collection** (a data function whose domain α is unconstrained) and
        // folds its Int codomain to an Int. Inline-built so α gets its own
        // fresh var even though it's unconstrained.
        let alpha = fresh_var(BODY_LEVEL);
        let aggregate_sum = PolyScheme::poly(
            SCHEME_LEVEL,
            fun(
                Type::data_fun(alpha.clone(), prim(BaseType::Int)),
                prim(BaseType::Int),
            ),
        );

        // Max: ∀α γ. (α ⤇ γ) → γ. Consumes a collection and folds its
        // codomain γ to a result of the same type.
        let alpha = fresh_var(BODY_LEVEL);
        let gamma = fresh_var(BODY_LEVEL);
        let aggregate_max = PolyScheme::poly(
            SCHEME_LEVEL,
            fun(Type::data_fun(alpha, gamma.clone()), gamma),
        );

        // Drain: ∀α γ. (α ⤇ γ) → unit. Consumes a collection of any element
        // type and yields the trivial `unit` — the terminal aggregate. `set`
        // uses it to collapse each key's (duplicate-bearing) group to the single
        // `unit` payload of `Set(K)`; consuming the group is also what abstracts its
        // key-dependence, since that is where the sum is consumed.
        let alpha = fresh_var(BODY_LEVEL);
        let gamma = fresh_var(BODY_LEVEL);
        let aggregate_drain = PolyScheme::poly(
            SCHEME_LEVEL,
            fun(Type::data_fun(alpha, gamma), prim(BaseType::Unit)),
        );

        // FinalOrDefault: ∀α β. ((α ⤇ β), β) → β. The first field is a
        // collection stream. Inline-built (not via `normalize_annotation`) so
        // the codomain of the stream and the default share one variable `β`.
        let alpha = fresh_var(BODY_LEVEL);
        let beta = fresh_var(BODY_LEVEL);
        let mut tup: BTreeMap<FieldKey, Type> = BTreeMap::new();
        tup.insert(
            FieldKey::Index(0),
            Type::data_fun(alpha.clone(), beta.clone()),
        );
        tup.insert(FieldKey::Index(1), beta.clone());
        let final_or_default = PolyScheme::poly(SCHEME_LEVEL, fun(product(tup), beta));

        // GetPrevSeq: ∀ι ν. ((ι ⤇ ν), ι, ν) → ν — history (a collection),
        // position, default.
        let iota = fresh_var(BODY_LEVEL);
        let nu = fresh_var(BODY_LEVEL);
        let mut tup: BTreeMap<FieldKey, Type> = BTreeMap::new();
        tup.insert(FieldKey::Index(0), Type::data_fun(iota.clone(), nu.clone()));
        tup.insert(FieldKey::Index(1), iota);
        tup.insert(FieldKey::Index(2), nu.clone());
        let get_prev_seq = PolyScheme::poly(SCHEME_LEVEL, fun(product(tup), nu));

        // GetPrevTxn: ∀ι ν. ((ι → {time: Txn, write: ν}), Txn, ν) → ν. The commit
        // stream is indexed by the writer's *iteration* domain `ι` (a UIntRange /
        // DataSource — the site's source, *not* `Txn`, per the builtin table in
        // design/mutability.md and the view type `transact_phase` stamps); the
        // search position and the record's `time` field are the concrete
        // commit-time `Txn`, and the carried write value `ν` is shared across the
        // record's `write` field, the default, and the result. Quantifying `ι`
        // (rather than pinning it to `Txn`, as `get_prev_seq` quantifies its
        // domain) keeps the scheme faithful to the site-indexed stream, so a
        // future routing of it through inference would not reject the real
        // commit view — inline-built like `get_prev_seq`.
        let iota = fresh_var(BODY_LEVEL);
        let nu = fresh_var(BODY_LEVEL);
        let commit_record = Type::Record(vec![
            ("time".to_string(), Type::Txn),
            ("write".to_string(), nu.clone()),
        ]);
        let mut tup: BTreeMap<FieldKey, Type> = BTreeMap::new();
        // The commit stream (field 0) is a collection — a data function.
        tup.insert(FieldKey::Index(0), Type::data_fun(iota, commit_record));
        tup.insert(FieldKey::Index(1), Type::Txn);
        tup.insert(FieldKey::Index(2), nu.clone());
        let get_prev_txn = PolyScheme::poly(SCHEME_LEVEL, fun(product(tup), nu));

        Self {
            box_intro,
            arithmetic,
            compare,
            bool_logic,
            concat,
            neg,
            not_op,
            aggregate_sum,
            aggregate_max,
            aggregate_drain,
            final_or_default,
            get_prev_seq,
            get_prev_txn,
        }
    }

    pub(super) fn binop(&self, op: BinOpKind) -> &PolyScheme {
        match op {
            BinOpKind::Arithmetic(_) => &self.arithmetic,
            BinOpKind::Compare(_) => &self.compare,
            BinOpKind::BoolLogic(_) => &self.bool_logic,
            BinOpKind::Concat => &self.concat,
        }
    }

    pub(super) fn unary(&self, op: UnaryOpKind) -> &PolyScheme {
        match op {
            UnaryOpKind::Neg => &self.neg,
            UnaryOpKind::Not => &self.not_op,
        }
    }

    pub(super) fn aggregate(&self, kind: AggregateKind) -> &PolyScheme {
        match kind {
            AggregateKind::Sum => &self.aggregate_sum,
            AggregateKind::Max => &self.aggregate_max,
            AggregateKind::Drain => &self.aggregate_drain,
        }
    }

    /// Polymorphic-builtin lookup. Returns `Some` for builtins whose
    /// signature has shared type variables across positions (and so cannot
    /// be expressed via the generic `Hole → fresh_var` conversion); `None`
    /// for builtins whose pre-stamped `expr.ty` is already monomorphic
    /// (or polymorphic only in independent vars).
    pub(super) fn builtin(&self, b: Builtin) -> Option<&PolyScheme> {
        match b {
            Builtin::Box => Some(&self.box_intro),
            Builtin::FinalOrDefault => Some(&self.final_or_default),
            Builtin::GetPrevSeq => Some(&self.get_prev_seq),
            Builtin::GetPrevTxn => Some(&self.get_prev_txn),
            _ => None,
        }
    }
}

impl Default for OperatorSchemes {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_helpers::*;
    use super::OperatorSchemes;
    use crate::ccl::infer::int_lit_ty;
    use crate::ccl::{AggregateKind, Builtin, Type, TypedBinding, TypedExpr, TypedExprNode};

    /// `GetPrevTxn`'s scheme instantiates to
    /// `((ι ⇒ {time: Txn, write: ν}), Txn, ν) ⇒ ν`: the history domain `ι` is a
    /// fresh variable (the writer's iteration domain — *not* `Txn`), while the
    /// `time` field and the search position are the concrete commit-time `Txn`,
    /// and the carried write value / default / result share one variable `ν`.
    #[test]
    fn get_prev_txn_scheme_shape() {
        let schemes = OperatorSchemes::new();
        let scheme = schemes
            .builtin(Builtin::GetPrevTxn)
            .expect("GetPrevTxn has a scheme");
        let inst = scheme.instantiate(0);

        let Type::Fun {
            domain, codomain, ..
        } = &inst
        else {
            panic!("expected a function type, got {inst}");
        };
        let Type::Tuple(args) = domain.as_ref() else {
            panic!("expected a tupled argument, got {domain}");
        };
        assert_eq!(args.len(), 3, "history, time, default");

        // arg 0: Txn ⇒ {time: Txn, write: ν}
        let Type::Fun {
            domain: hist_dom,
            codomain: rec,
            ..
        } = &args[0]
        else {
            panic!("history must be a function, got {}", args[0]);
        };
        // The history domain is the writer's iteration domain — a fresh
        // quantified variable, distinct from the write value `ν` — not `Txn`.
        assert!(
            matches!(**hist_dom, Type::Infer(_)),
            "history domain is a fresh variable ι, got {hist_dom}"
        );
        assert_ne!(
            **hist_dom,
            Type::Txn,
            "history domain is ι (iteration domain), not Txn"
        );
        let Type::Record(fields) = rec.as_ref() else {
            panic!("history codomain must be a record, got {rec}");
        };
        assert_eq!(fields[0].0, "time");
        assert_eq!(fields[0].1, Type::Txn, "time field is Txn");
        assert_eq!(fields[1].0, "write");

        // arg 1 (position) is Txn; the write field, the default (arg 2), and
        // the result all share the same freshened variable ν, distinct from ι.
        assert_eq!(args[1], Type::Txn, "position is Txn");
        assert_eq!(fields[1].1, args[2], "write field and default share ν");
        assert_eq!(**codomain, args[2], "result and default share ν");
        assert_ne!(
            **hist_dom, args[2],
            "history domain ι is distinct from the write value ν"
        );
    }

    /// TRIPWIRE — documents a known soundness gap, NOT desired behavior.
    ///
    /// `Max` has scheme `∀α γ. (α ⇒ γ) ⇒ γ` (see `aggregate_max`), so its
    /// codomain `γ` is wholly unconstrained and it type-checks over *any*
    /// codomain. But `Max` is only *defined* at eval for orderable base types
    /// (`Int`/`UInt`/`String` — see merge/identity in `ccl/mod.rs`). So `max`
    /// over a function with a tuple codomain type-checks and infers
    /// `Tuple([Int, Int])`, even though it has no defined runtime behavior.
    ///
    /// `Max` *should* require an orderable codomain. The correct long-term fix
    /// is a first-class comparability bound, which arrives with traits — there
    /// is no value in a stopgap validation now. When that lands, inference will
    /// start rejecting this program and this test will fail loudly; whoever
    /// lands traits should flip it to assert rejection.
    ///
    /// Tracked by `type-checker-traits-comparability` (P3) in the project vault.
    #[test]
    fn max_over_non_orderable_codomain_is_unsoundly_accepted() {
        // Aggregate { input: λx → (1, 2), kind: Max }. The input stands in for a
        // data collection of tuples (what `max` really consumes), so it carries
        // the `data_fun` provenance stamp lowering puts on a collection — without
        // it, the bare lambda is a `Compute` capability and `max`'s `Data` demand
        // rejects it on *kind* before the codomain-orderability gap under test.
        let lam = TypedExpr::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: "x".into(),
                ty: Type::Hole,
                user_annotation: None,
            },
            body: Box::new(TypedExpr::new(TypedExprNode::Tuple(vec![
                lit_int(1),
                lit_int(2),
            ]))),
        })
        .with_user_annotation(Type::data_fun(Type::Hole, Type::Hole));
        let mut e = TypedExpr::aggregate(lam, AggregateKind::Max);
        let ty = run_inference(&mut e).expect("inference succeeds (the bug under test)");
        // Buggy current behavior: the non-orderable tuple codomain is accepted.
        assert_eq!(ty, Type::Tuple(vec![int_lit_ty(1), int_lit_ty(2)]));
    }
}
