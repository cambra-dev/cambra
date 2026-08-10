// ---------------------------------------------------------------------------
// Operator/projection scheme registry (Step 7b)
// ---------------------------------------------------------------------------

use std::collections::BTreeMap;

use crate::ccl::FieldKey;
use crate::ccl::infer::solver::traits::{Assoc, Trait};
use crate::ccl::infer::solver::{PolyScheme, fresh_var, fun, prim};
use crate::ccl::{
    AggregateKind, ArithmeticKind, BaseType, BinOpKind, Builtin, CompareKind, Level, Type,
    UnaryOpKind,
};

use super::product;

/// Where a trait-typed operator's result type comes from.
///
/// This is the operator's half of the contract, which is why it lives here beside the
/// signatures rather than with the traits: a trait *associates* a type when that type
/// depends on the types satisfying it, and an operator whose result is the same
/// whatever it accepts states that itself. Keeping the two apart is what stops a
/// constant from being mis-recorded as an associated type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OperatorResult {
    /// An associated type of the required trait — `+`'s result is `Addable`'s
    /// `Output`.
    Associated(Assoc),
    /// Fixed by the operator regardless of the operand types — `==` yields `Bool` for
    /// every pair `Equatable` accepts, which is why `Equatable` associates nothing.
    Fixed(BaseType),
}

/// How an operator states what it requires of its operands.
///
/// Two shapes, because there are two genuinely different situations: an operator
/// whose operand types are *fixed* is fully described by a signature, and one that is
/// polymorphic in them is not — the only relation a signature can state between two
/// operands is that they share a variable, which also forces every other lattice
/// dimension to agree.
pub(super) enum OpSignature {
    /// A fixed signature: `and`, `or`, …, `++`, and `not`.
    Scheme(PolyScheme),
    /// The operands — **all of them, in order** — are the arguments of exactly one
    /// obligation `trait_(𝐴₁, …, 𝐴ₙ)`, and the operator's result is either fixed or
    /// one of *that* obligation's associated types.
    ///
    /// Deliberately narrower than "this operator is trait-typed", and named for the
    /// shape rather than the mechanism because it cannot express: more than one
    /// obligation; an obligation over a subset of the operands; a separate obligation
    /// per operand; or a result drawn from some obligation other than the one
    /// constraining the operands. Every operator has this shape today. One that did
    /// not would want its own rule in `emit_node` rather than a wider variant here,
    /// since a wider variant would have to be interpreted somewhere and that
    /// interpretation is what a rule *is*.
    SingleObligation {
        /// The trait the operands jointly satisfy.
        trait_: Trait,
        /// Where the operator's own result type comes from.
        result: OperatorResult,
    },
}

/// Schemes for operators that lift cleanly to fixed signatures.
///
/// Each scheme is built once per [`InferCtx`](super::context::InferCtx);
/// `instantiate` runs at every use site to mint fresh quantified variables.
/// Operators with structural result types (`BinOp::CollectionUnion`) and nodes
/// whose typing rules require AST-level reasoning (`Apply`, `Lambda`,
/// `Let`, `Case`, `List`, …) are handled by per-case rules in
/// `emit_node` rather than via this registry.
///
/// Arithmetic, comparison and negation are absent for a different reason: they are
/// polymorphic in their operands, which no signature can state without also forcing
/// every other lattice dimension to agree. They state a [`Trait`] instead — see
/// [`OpSignature`], which is what a lookup here returns.
pub struct OperatorSchemes {
    /// `Bool → Bool → Bool`.
    bool_logic: PolyScheme,
    /// `String → String → String`.
    concat: PolyScheme,
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
    /// `∀α β. ((α → β), β) → β` — extract the final value from a
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

impl OperatorSchemes {
    /// Build the registry. Schemes are quantified at level 0; their
    /// internal fresh vars live at level 1 so `instantiate(0)` mints
    /// fresh copies at the active inference level.
    pub fn new() -> Self {
        const SCHEME_LEVEL: Level = 0;
        const BODY_LEVEL: Level = 1;

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
            bool_logic,
            concat,
            not_op,
            aggregate_sum,
            aggregate_max,
            final_or_default,
            get_prev_seq,
            get_prev_txn,
        }
    }

    /// How `op`'s signature is stated — a fixed scheme, or a trait requirement.
    ///
    /// The split is total and exclusive: an operator whose operand types are fixed
    /// has a scheme, and one that is polymorphic in them has a trait. There is no
    /// operator with both, because a scheme that quantified over its operands could
    /// only relate them by *sharing a variable*, which is precisely the claim that
    /// is wrong in both polarities (see [`OpSignature::SingleObligation`]).
    /// Which typing rule `op` states.
    ///
    /// The arithmetic and comparison operators are polymorphic in their operands, so
    /// they state a trait; `and`/`or`/… and `++` have fixed operand types, so an
    /// ordinary scheme says everything there is to say and an obligation would add a
    /// mechanism with no choice to make.
    ///
    /// A scheme is cloned rather than borrowed so the caller's `ctx` borrow is
    /// released before the rule takes `ctx` mutably; a [`PolyScheme`] is `Rc`-shaped,
    /// so this is cheap.
    pub(super) fn binop(&self, op: BinOpKind) -> OpSignature {
        let arithmetic = |trait_| OpSignature::SingleObligation {
            trait_,
            result: OperatorResult::Associated(Assoc::Output),
        };
        // Every comparison yields `Bool` whatever operands it accepts, so the result
        // is the operator's to state and `Equatable`/`Orderable` associate nothing.
        let comparison = |trait_| OpSignature::SingleObligation {
            trait_,
            result: OperatorResult::Fixed(BaseType::Bool),
        };
        match op {
            BinOpKind::Arithmetic(ArithmeticKind::Add) => arithmetic(Trait::Addable),
            BinOpKind::Arithmetic(ArithmeticKind::Sub) => arithmetic(Trait::Subtractable),
            BinOpKind::Arithmetic(ArithmeticKind::Mul) => arithmetic(Trait::Multipliable),
            BinOpKind::Arithmetic(ArithmeticKind::FloorDiv) => arithmetic(Trait::Divisible),
            BinOpKind::Compare(CompareKind::Equals | CompareKind::NotEquals) => {
                comparison(Trait::Equatable)
            }
            BinOpKind::Compare(_) => comparison(Trait::Orderable),
            BinOpKind::BoolLogic(_) => OpSignature::Scheme(self.bool_logic.clone()),
            BinOpKind::Concat => OpSignature::Scheme(self.concat.clone()),
        }
    }

    /// See [`Self::binop`] — the same split. `not` is genuinely monomorphic
    /// (`Bool → Bool`), so it keeps a scheme.
    pub(super) fn unary(&self, op: UnaryOpKind) -> OpSignature {
        match op {
            UnaryOpKind::Neg => OpSignature::SingleObligation {
                trait_: Trait::Negatable,
                result: OperatorResult::Associated(Assoc::Output),
            },
            UnaryOpKind::Not => OpSignature::Scheme(self.not_op.clone()),
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

    /// `max` is defined at eval only for orderable bases (`Int`/`UInt`/`String` —
    /// see merge/identity in `ccl/mod.rs`), and its scheme `∀α γ. (α ⤇ γ) ⇒ γ`
    /// cannot say so: `γ` is the codomain it *returns*, so nothing about it is
    /// constrained.
    ///
    /// `Comparable(γ)` says it — a **pure requirement**, associating nothing, since
    /// the scheme already supplies the result type. A codomain the program never
    /// determines is still accepted here, as an unresolved variable rather than a
    /// missing implementation; that is the ordinary limit of narrowing, not a gap
    /// specific to `max`.
    ///
    /// Closes `type-checker-traits-comparability` (P3) in the project vault.
    #[test]
    fn max_over_a_non_orderable_codomain_is_rejected() {
        // Aggregate { input: λx → (1, 2), kind: Max }. The input stands in for a
        // data collection of tuples (what `max` really consumes), so it carries
        // the `data_fun` provenance stamp lowering puts on a collection — without
        // it, the bare lambda is a `Compute` capability and `max`'s `Data` demand
        // rejects it on *kind* before the codomain orderability under test.
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
        let errs = run_inference(&mut e).expect_err("a tuple codomain is not orderable");
        assert!(
            errs.iter().any(|e| matches!(
                e,
                crate::ccl::infer::InferError::NoTraitImpl { trait_, .. }
                    if trait_ == "Comparable"
            )),
            "expected NoTraitImpl for Comparable, got {errs:?}"
        );
    }
}
