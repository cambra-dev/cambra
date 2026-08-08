// ---------------------------------------------------------------------------
// Operator/projection scheme registry (Step 7b)
// ---------------------------------------------------------------------------

use std::collections::BTreeMap;

use crate::ccl::FieldKey;
use crate::ccl::infer::solver::{PolyScheme, fresh_var, fun, prim};
use crate::ccl::{
    AggregateKind, ArithmeticKind, BaseType, BinOpKind, Builtin, CompareKind, Level, Type, TypeFn,
    UnaryOpKind,
};

use super::product;

/// Schemes for operators that lift cleanly to fixed signatures.
///
/// Each scheme is built once per [`InferCtx`](super::context::InferCtx);
/// `instantiate` runs at every use site to mint fresh quantified variables.
/// Operators with structural result types (`BinOp::CollectionUnion`) and nodes
/// whose typing rules require AST-level reasoning (`Apply`, `Lambda`,
/// `Let`, `Case`, `List`, …) are handled by per-case rules in
/// `emit_node` rather than via this registry.
///
/// # An operand requirement must be reachable from the result type
///
/// **A scheme that states a requirement on its operand variables must mention
/// those variables in its result**, as a [`Type::App`] over them. Writing a
/// concrete result instead compiles, infers, and silently accepts programs the
/// requirement was written to reject.
///
/// The reason is the solver's, not the operator's. A rule runs when something
/// **materializes** the application it belongs to, and an application is
/// materialized only when some node's type reaches it. A scheme's operand
/// variables are nobody's node type: a use site records `left <: α` and
/// `right <: β`, so `α` and `β` are reachable *from* the operands, but nothing
/// walks *from* them. The only thing that can reach them is the result, because
/// the result is the node's type.
///
/// So arithmetic's result is `Add(α, β)` and a comparison's is `Greater(α, β)`,
/// reducing to `Bool` for any operands that share a base and to an error for any
/// that do not. A bare `Bool` there would let `1 > "a"` type-check and then panic
/// in the interpreter — a rule that is never run rejects nothing.
///
/// This is also why an operand requirement stated *beside* the result rather than
/// in it does not work, and [`binary_operands`] records what happened when one was.
///
/// Every other scheme here states its requirement **structurally**, in an operand's
/// own shape — `Sum`'s `∀α. (α ⇒ Int) ⇒ Int` puts the `Int` in the argument's
/// codomain position, so `constrain_go` records it on the argument expression's
/// variable, which is a node's type and is materialized like any other. Those need
/// nothing.
pub struct OperatorSchemes {
    /// One scheme per arithmetic operator: `∀α β. α → β → Add(α, β)` and siblings,
    /// over two **unrelated** operand variables.
    ///
    /// **Nothing is shared between the operands and the result**, and that is the
    /// point. A shared variable (`∀α. α → α → α`) states *equality*, which drags
    /// the whole lattice along with the base, once per polarity: the operand
    /// occurrences are negative positions where refinement sets union, so one
    /// operand's refinement becomes a *requirement* on the other (`\x -> x + 1`
    /// demanding `x : {Int | __elem == 1}`), while the result occurrence is positive
    /// where they intersect, so a refinement both operands carry survives onto the
    /// result (`x + x` where `x` is `2` claiming the sum is `2`). Arithmetic
    /// *computes* a new value, so it may inherit neither.
    ///
    /// The result is a [`Type::App`] instead: `Add(α, β)`, whose rule reduces to the
    /// operands' shared base once they resolve and rejects operands that have none.
    /// Deciding what is addable is that rule's job, which is what the reachability
    /// section above is for — the result *is* the node's type, so it is the one
    /// thing guaranteed to be materialized. It keeps the operator kind because a
    /// sharper rule needs it (`+` and `*` map operand ranges to different result
    /// ranges, so `([0,2], [5,7]) ⇒ [5,9]` will live there), and one scheme per kind
    /// follows from the kind being part of the type.
    arithmetic: BTreeMap<ArithmeticKind, PolyScheme>,
    /// One scheme per comparison: `∀α β. α → β → Greater(α, β)` and siblings, over
    /// two unrelated operand variables like [`arithmetic`](Self::arithmetic).
    ///
    /// A comparison is exposed to only the *operand* half of the shared-variable
    /// problem — its result is `Bool`, so it could never inherit a refinement — but
    /// that half is the same shared variable, so it takes the same treatment.
    ///
    /// The result is an application even though it reduces to a constant, and that
    /// is the reachability section in miniature: a bare `Bool` mentions neither
    /// operand, so nothing would ever materialize them and the rule that checks them
    /// would never run. `Compare(kind, α, β)` reduces to `Bool` for operands that
    /// share a base and to an error for operands that do not, which is both what a
    /// comparison means and what gets the check to happen at all.
    compare: BTreeMap<CompareKind, PolyScheme>,
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
    /// `∀α β. ((α → β), β) → β` — extract the last value from a
    /// function-typed stream, falling back to the default scalar when the
    /// stream's domain is empty. Polymorphic in both the stream domain
    /// (`α`) and the shared codomain/default type (`β`); inline construction
    /// is required because both vars are shared across positions, which
    /// `normalize_annotation` (one fresh var per `Hole`) can't express.
    final_or_default: PolyScheme,
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

/// Two fresh, **unrelated** operand variables for a binary operator.
///
/// Nothing here states a requirement between them, and nothing needs to: the
/// operator's *result* is a [`Type::App`] over both, so materializing the node
/// reduces it, and the rule decides whether the operands are acceptable. That is
/// the whole content of "an operand requirement must be reachable from the result
/// type" — the reachability is what makes the check happen, and the rule is where
/// the check belongs.
///
/// An operand nothing else determines therefore stays undetermined — `\x -> x + 1`
/// leaves its parameter open. That lambda *is* polymorphic and `Type` has no way to
/// say so, which makes it an ambiguous program, exactly as `\x -> [x, x]` is.
fn binary_operands() -> (Type, Type) {
    const BODY_LEVEL: Level = 1;
    (fresh_var(BODY_LEVEL), fresh_var(BODY_LEVEL))
}

impl OperatorSchemes {
    /// Build the registry. Schemes are quantified at level 0; their
    /// internal fresh vars live at level 1 so `instantiate(0)` mints
    /// fresh copies at the active inference level.
    pub fn new() -> Self {
        const SCHEME_LEVEL: Level = 0;
        const BODY_LEVEL: Level = 1;

        // Arithmetic: one scheme per operator, ∀α β. α → β → <Op>(α, β), with the
        // operand requirement recorded as a bound on α and β (see the field doc).
        let arithmetic = ArithmeticKind::ALL
            .into_iter()
            .map(|kind| {
                let (alpha, beta) = binary_operands();
                let result = Type::App {
                    fun: TypeFn::Arithmetic(kind),
                    args: vec![alpha.clone(), beta.clone()],
                };
                (
                    kind,
                    PolyScheme::poly(SCHEME_LEVEL, fun(alpha, fun(beta, result))),
                )
            })
            .collect();

        // Compare: one scheme per operator, ∀α β. α → β → <Op>(α, β), same operand
        // requirement. The result is an operator rather than a bare `Bool` so that
        // the requirement is reachable from it — see the type doc.
        let compare = CompareKind::ALL
            .into_iter()
            .map(|kind| {
                let (alpha, beta) = binary_operands();
                let result = Type::App {
                    fun: TypeFn::Compare(kind),
                    args: vec![alpha.clone(), beta.clone()],
                };
                (
                    kind,
                    PolyScheme::poly(SCHEME_LEVEL, fun(alpha, fun(beta, result))),
                )
            })
            .collect();

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
            arithmetic,
            compare,
            bool_logic,
            concat,
            neg,
            not_op,
            aggregate_sum,
            aggregate_max,
            final_or_default,
            get_prev_seq,
            get_prev_txn,
        }
    }

    pub(super) fn binop(&self, op: BinOpKind) -> &PolyScheme {
        match op {
            BinOpKind::Arithmetic(k) => self
                .arithmetic
                .get(&k)
                .expect("every ArithmeticKind has a scheme"),
            BinOpKind::Compare(k) => self
                .compare
                .get(&k)
                .expect("every CompareKind has a scheme"),
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
        }
    }

    /// Polymorphic-builtin lookup. Returns `Some` for builtins whose
    /// signature has shared type variables across positions (and so cannot
    /// be expressed via the generic `Hole → fresh_var` conversion); `None`
    /// for builtins whose pre-stamped `expr.ty` is already monomorphic
    /// (or polymorphic only in independent vars).
    pub(super) fn builtin(&self, b: Builtin) -> Option<&PolyScheme> {
        match b {
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
