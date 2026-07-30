//! Scalar primitives shared across the CCL pipeline: base types, literal
//! constants, the binary / unary operator kinds, the [`Builtin`] combinator
//! enum, projection keys, and the cross-phase [`TypeError`].

use std::fmt;
use std::sync::atomic::{AtomicU32, Ordering};

use crate::ccl::AggregateKind;

/// Identity of a [`Builtin::KeyDom`] token — which key domain it is.
///
/// Minted per creation site, so two concrete keyed collections have the same key
/// domain iff they were created by the same site. That is the whole content of
/// keyed-collection identity: the token is opaque, so the id is all there is to
/// compare.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KeyDomId(u32);

static KEY_DOM_COUNTER: AtomicU32 = AtomicU32::new(0);

impl KeyDomId {
    /// Mint a fresh, globally-unique key-domain identity.
    pub fn fresh() -> Self {
        KeyDomId(KEY_DOM_COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

/// Primitive base types shared between the CCL type system and the interpreter.
///
/// Defined here (in `ccl`) and re-exported by the interpreter so that
/// `ccl` does not depend upward on `interpreter`. See `interpreter/types/`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BaseType {
    /// Signed 64-bit integer.
    Int,
    /// Unsigned 64-bit integer.
    UInt,
    /// Unicode string.
    String,
    /// Boolean value.
    Bool,
    /// The unit type (equivalent to Python `None`).
    Unit,
}

impl BaseType {
    /// The CHL/CCL surface spelling of this primitive (`Caps` means type —
    /// `docs/chl-spec.md`). Single source of truth for the reader
    /// ([`from_keyword`](Self::from_keyword)) and every `Display`/pretty site,
    /// so a new variant fails to compile until all of them are updated rather
    /// than silently diverging.
    pub const fn keyword(&self) -> &'static str {
        match self {
            BaseType::Int => "Int",
            BaseType::UInt => "UInt",
            BaseType::String => "String",
            BaseType::Bool => "Bool",
            BaseType::Unit => "Unit",
        }
    }

    /// Inverse of [`keyword`](Self::keyword): recognise a primitive-type name.
    /// Total round-trip over every variant (`from_keyword(b.keyword()) ==
    /// Some(b)`), so all five spellings — `UInt` and `Unit` included — are
    /// accepted wherever a primitive annotation is read.
    pub fn from_keyword(s: &str) -> Option<Self> {
        Some(match s {
            "Int" => BaseType::Int,
            "UInt" => BaseType::UInt,
            "String" => BaseType::String,
            "Bool" => BaseType::Bool,
            "Unit" => BaseType::Unit,
            _ => return None,
        })
    }
}

/// Errors about types that can be used by any phase of compilation
pub enum TypeError {
    /// Generic type error
    Unsupported(String),
}

/// A literal constant value.
///
/// Covers the subset of [`crate::interpreter::Value`] that can appear as
/// compile-time constants.
///
/// Named `Lit` to avoid shadowing `crate::interpreter::Literal`, which is
/// an unrelated operator struct.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Lit {
    /// An integer constant.
    Int(i64),
    /// A string constant.
    String(String),
    /// A boolean constant.
    Bool(bool),
    /// The unit (null/None) constant.
    Unit,
}

/// Arithmetic sub-operations for [`BinOpKind::Arithmetic`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArithmeticKind {
    /// Integer addition (`+`).
    Add,
    /// Integer subtraction (`-`).
    Sub,
    /// Integer multiplication (`*`).
    Mul,
    /// Floor division (`//`).
    FloorDiv,
}

/// Comparison sub-operations for [`BinOpKind::Compare`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompareKind {
    /// Equality (`==`).
    Equals,
    /// Inequality (`!=`).
    NotEquals,
    /// Less than (`<`).
    Less,
    /// Less than or equal (`<=`).
    LessOrEq,
    /// Greater than (`>`).
    Greater,
    /// Greater than or equal (`>=`).
    GreaterOrEq,
}

/// Boolean logic sub-operations for [`BinOpKind::BoolLogic`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogicKind {
    /// Logical AND.
    And,
    /// Logical NAND.
    Nand,
    /// Logical OR.
    Or,
    /// Logical NOR.
    Nor,
    /// Logical XOR.
    Xor,
    /// Logical XNOR.
    Xnor,
}

/// Binary operation kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOpKind {
    /// An arithmetic operation (add, sub, mul, floor-div).
    Arithmetic(ArithmeticKind),
    /// A boolean logic operation (and, or, xor, …).
    BoolLogic(LogicKind),
    /// String concatenation (`+` on strings).
    Concat,
    /// A comparison that produces a boolean result.
    Compare(CompareKind),
}

impl BinOpKind {
    /// Returns the canonical infix symbol for this operator (e.g. `"+"`, `"and"`, `"<="`).
    ///
    /// Used by formatters such as the symbolic printer and the pretty-tree
    /// printer so that the mapping lives once on the type rather than being
    /// duplicated in each formatter.
    pub fn sym(&self) -> &'static str {
        match self {
            Self::Arithmetic(ArithmeticKind::Add) => "+",
            Self::Arithmetic(ArithmeticKind::Sub) => "-",
            Self::Arithmetic(ArithmeticKind::Mul) => "*",
            Self::Arithmetic(ArithmeticKind::FloorDiv) => "//",
            Self::Concat => "++",
            Self::Compare(CompareKind::Less) => "<",
            Self::Compare(CompareKind::LessOrEq) => "<=",
            Self::Compare(CompareKind::Greater) => ">",
            Self::Compare(CompareKind::GreaterOrEq) => ">=",
            Self::Compare(CompareKind::Equals) => "==",
            Self::Compare(CompareKind::NotEquals) => "!=",
            Self::BoolLogic(LogicKind::And) => "and",
            Self::BoolLogic(LogicKind::Nand) => "nand",
            Self::BoolLogic(LogicKind::Or) => "or",
            Self::BoolLogic(LogicKind::Nor) => "nor",
            Self::BoolLogic(LogicKind::Xor) => "xor",
            Self::BoolLogic(LogicKind::Xnor) => "xnor",
        }
    }

    /// Returns the function-style name used when this operator is referenced as
    /// a built-in primitive (e.g. `"add"`, `"lt"`, `"concat"`).
    ///
    /// Lambda elimination desugars `a op b` into
    /// `Apply(Tuple([a, b]), Builtin(BinOp(op)))`; this is the printable name
    /// of that built-in, used by [`Builtin::name`] and by the symbolic /
    /// pretty printers.
    pub fn fn_name(&self) -> &'static str {
        match self {
            Self::Arithmetic(ArithmeticKind::Add) => "add",
            Self::Arithmetic(ArithmeticKind::Sub) => "sub",
            Self::Arithmetic(ArithmeticKind::Mul) => "mul",
            Self::Arithmetic(ArithmeticKind::FloorDiv) => "floor_div",
            Self::Concat => "concat",
            Self::Compare(CompareKind::Equals) => "eq",
            Self::Compare(CompareKind::NotEquals) => "neq",
            Self::Compare(CompareKind::Less) => "lt",
            Self::Compare(CompareKind::LessOrEq) => "le",
            Self::Compare(CompareKind::Greater) => "gt",
            Self::Compare(CompareKind::GreaterOrEq) => "ge",
            Self::BoolLogic(LogicKind::And) => "and",
            Self::BoolLogic(LogicKind::Nand) => "nand",
            Self::BoolLogic(LogicKind::Or) => "or",
            Self::BoolLogic(LogicKind::Nor) => "nor",
            Self::BoolLogic(LogicKind::Xor) => "xor",
            Self::BoolLogic(LogicKind::Xnor) => "xnor",
        }
    }
}

/// Unary operation kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOpKind {
    /// Arithmetic negation (`-x`).
    Neg,
    /// Boolean negation (`not x`).
    Not,
}

/// Built-in primitive functions used by the lowered point-free CCL.
///
/// These are the named combinators that earlier passes used to refer to via
/// [`TypedExprNode::Var`](crate::ccl::TypedExprNode::Var) with hard-coded magic
/// strings.  Representing them as a dedicated enum makes it cheap and type-safe
/// for downstream passes (simplify, planning, operator_conversion, …) to
/// recognise primitives without string matching.
///
/// Built-in nodes are produced by [`crate::ccl::lambda_elim`] and
/// [`crate::ccl::planning`]; they never appear in source-lowered CCL prior
/// to lambda elimination, so type inference does not need to reason about
/// them — types are stamped onto the surrounding
/// [`TypedExpr`](crate::ccl::TypedExpr) at the point each built-in is emitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Builtin {
    // Categorical combinators (introduced by lambda elimination).
    /// `id : A → A` — identity morphism.
    Id,
    /// `box : ∀𝑎. 𝑎 ⇒ Σ σ ∈ {𝑎}. σ` — the **only** way into a dependent sum.
    ///
    /// Puts a value into the sum whose single candidate is its own type. Subtyping has
    /// no `𝑇 <: Σ` rule, so a sum is never formed by subsumption and a join can never
    /// produce one the program did not write (`src/ccl/design/type-inference.md`,
    /// "Only a term builds a sum"). What makes `box` useful is not the singleton it builds
    /// but what two of them do at a join: candidate lists union under Σ-width, so
    /// `box(xs) if c else box(ys)` keeps *both* alternatives where the unboxed
    /// conditional has no upper bound at all.
    ///
    /// The candidate position is **invariant**, so `𝑎` is pinned to the argument's type
    /// exactly — `box(5)` is `Σ σ ∈ {5}. σ`, not `Σ σ ∈ {Int}. σ`. Retaining the
    /// alternatives rather than joining past them is the whole service.
    Box,
    /// `curry : ((A, B) → C) → (A → (B → C))`.
    Curry,
    /// `const : A → (B → A)` — lift a value to a constant function.
    Const,
    /// `zip : ((A → B), (A → C)) → (A → (B, C))` — point-free product/fanout.
    Zip,
    /// `apply : (B, B → C) → C` — function application as a morphism.
    Apply,
    /// `map : (B → C) → ((A → B) → (A → C))` — post-composition.
    Map,
    /// `map_domain : (A → B) → (A → A)` — domain-to-domain identity stream.
    MapDomain,
    /// `compose : ((A → B), (B → C)) → (A → C)` — composition as a morphism.
    Compose,
    /// `converse : (A → K) → (K → (A → A))` — group-by-key combinator.
    Converse,
    /// `uncurry : (A → (B → C)) → ((A, B) → C)`.
    Uncurry,
    /// `restrict : (D ⇒ Bool) ⇒ (D ⇒ T) ⇒ ({d: D | p(d)} ⇒ T)` —
    /// mid-chain filter step.
    ///
    /// `restrict` is a *codomain-parametric function transformer*: it
    /// narrows the domain of an upstream value-producer `D ⇒ T` to the
    /// subset satisfying `p`, passing the values `T` through unchanged.
    /// So the refinement lands on the **domain** and `T` is preserved on
    /// the codomain — not the unsound `D ⇒ {d: D | p(d)}` (which would
    /// claim every `d : D` satisfies `p`).  The transformer
    /// `Apply(p, Restrict)` is therefore **applied to** its upstream
    /// (`Apply(upstream, Apply(p, Restrict))`), not composed with it —
    /// its domain is a function type, so it cannot be a morphism in a CCC
    /// `Compose` chain.
    ///
    /// Op-conversion compiles the application via the generic
    /// applied-combinator arm: `upstream` is converted with `input=None`,
    /// then this `Restrict` arm consumes it as `input=Some(_)`, compiles
    /// the predicate against it, and wraps it in a `Restrict` tile.
    /// Emitted by [`crate::ccl::planning`] for every downstream filter —
    /// the outer layers of a nested-refinement iteration site, the
    /// residual predicate of `JoinPlan::Loop`, and the residual predicate
    /// of `JoinPlan::Hash`.  Chain-head iteration is the separate
    /// `Iterate` variant.  See [`crate::ccl::ccl_utils::make_restrict`].
    Restrict,
    /// `iterate : (D ⇒ Bool) ⇒ ({d: D | p(d)} ⇒ {d: D | p(d)})` —
    /// chain-head iteration source.
    ///
    /// `Apply(p, Iterate)` requires `input=None`; op-conversion compiles
    /// it to an `IterateExtent` over `D` (plus a `Restrict` filter when
    /// `p` is non-trivial).  Emitted by [`crate::ccl::planning`] at the
    /// head of every iteration site: aggregate arguments, top-level
    /// program results, sink-bound fields, mutation-loop sources, and
    /// `JoinPlan::Loop` / `JoinPlan::Hash` arm leaves.  Mid-chain
    /// filtering is the separate `Restrict` variant.
    ///
    /// Planning is the sole emitter; lambda elimination never produces
    /// `Iterate`.  The trivially-true predicate `Apply(Lit::Bool(true), Const)`
    /// marks unrefined sites — op-conversion recognises it and emits
    /// just `IterateExtent` (no filter).
    Iterate,
    /// `permute_domain` — reorder positions in a tuple-typed domain.
    PermuteDomain,
    /// `flatten_domain` — flatten selected nested-tuple positions in a domain.
    FlattenDomain,

    /// A binary scalar operation lifted to a function on a 2-tuple
    /// (`(a, b) ▷ BinOp(op)`).
    ///
    /// Covers all arithmetic / string / comparison / boolean-logic operators;
    /// the inner [`BinOpKind`] is the single source of truth for which one.
    /// Lambda elimination desugars `a op b` into this form.
    BinOp(BinOpKind),

    // Unary scalar ops.
    /// `neg : Int → Int`.
    Neg,
    /// `not_fn : Bool → Bool` — boolean negation as a morphism.
    NotFn,

    /// `filter_values : (D ⇒ Bool) ⇒ ({d: D | p(d)} ⇒ V)` — a **value-preserving**
    /// mid-chain filter. `Apply(p, FilterValues)` requires `input=Some(_)` (the
    /// `D ⇒ V` stream to filter) and keeps each surviving element's **codomain
    /// value** `V` — unlike `Restrict`, which returns the domain identity
    /// `{D | p} ⇒ {D | p}` for a source a downstream map re-indexes. Compiles to
    /// the `Filter` tile operator (input stream + predicate, output = filtered
    /// input). Lambda elimination emits it to desugar a value-selecting `Case`
    /// whose gate varies with the element (`λ x → Case{[gᵢ(x) → eᵢ(x)]}`, a writer
    /// decision body) into a **union of domain-restricts** `⧺ᵢ (filter_values(π̂ᵢ)
    /// ≫ eᵢ)`: each arm filters the fed element stream to its first-match gate,
    /// then maps — so a partial op (`//`, `%`) in `eᵢ` runs only where its guard
    /// holds, never eagerly at a rejected position.
    FilterValues,

    // Aggregations (codomain of a function-typed input → scalar).
    /// `sum`.
    Sum,
    /// `max`.
    Max,
    /// `drain` — the terminal aggregate: consume a collection of any element
    /// type and yield `unit` (see [`AggregateKind::Drain`]). Produced only by
    /// the `set` constructor's group collapse.
    Drain,
    /// `final_or_default : Tuple(Fun(D, T), T) → T` — extract the
    /// codomain value at the final position of an iteration stream, or
    /// fall back to the default scalar when the stream's domain is
    /// empty.  Compiles directly to the `ExtractLast` tile operator
    /// (which receives both the stream and the default operator); not
    /// an aggregate fold (no identity element), so it does not
    /// participate in `AggregateKind`.
    ///
    /// Used by `lower_mutation_loop` to expose the scalar final
    /// accumulator of a Record-bodied loop, whose external type is
    /// `Fun(D, Record({step, to_<defer>*}))`: the after-loop scalar acc is
    /// `(acc_stream ▷ Proj("step"), init) ▷ FinalOrDefault`.  The
    /// default is the pre-loop accumulator binding, so an
    /// empty-source loop (`for i in []: x += 1; x`) yields `init`
    /// rather than panicking or returning empty.
    ///
    /// TODO: Make the ordering requirement on this explicit.  Right now
    /// all of our types can be implicitly ordered, but that might not
    /// hold forever, and the implicit ordering might be wrong.  Tracked
    /// jointly with the `.rev().find(…)` in `ExtractLastProducer` —
    /// both assume the source's last position by emission order, not
    /// by sorted domain value.
    FinalOrDefault,

    /// `get_prev_seq : Tuple(Fun(I, V), I, V) → V` — the history value at
    /// the *predecessor* of the given position, or the default at the first
    /// position.
    ///
    /// Applied as a tupled argument, same convention as [`Self::FinalOrDefault`]:
    /// `Apply(Tuple([history, position, default]), Builtin(GetPrevSeq))`.
    /// The polymorphic scheme `∀ι ν. ((ι ⇒ ν), ι, ν) ⇒ ν` lives in
    /// [`crate::ccl::infer::OperatorSchemes`] (shared variables
    /// across positions, like `FinalOrDefault`).
    ///
    /// This is the **guard accessor** for induction-domain recursion in a
    /// [`crate::ccl::TypedExprNode::LetRec`]: a binding whose self-reference
    /// is consumed only as the history argument of `get_prev_seq` depends
    /// only on strictly earlier positions, which is what makes the group
    /// well-founded (see `src/ccl/design/mutability.md`, "The model: histories and causal recursion" /
    /// "Builtins", and [`crate::ccl::letrec::check_letrec_causal`]).
    ///
    /// Op-conversion never compiles this builtin directly: letrec pattern
    /// recognition consumes it (the causal self-cycle becomes the `Recurse`
    /// engine), so its op-conversion arm is a deliberate error, like
    /// `LetRec`'s.
    GetPrevSeq,

    /// `get_prev_txn : Tuple(Fun(Txn, {time: Txn, write: V}), Txn, V) → V` —
    /// the write carried by the latest commit in the history stream *strictly
    /// before* the given time, or the default if none.
    ///
    /// Applied as a tupled argument, same convention as [`Self::GetPrevSeq`]:
    /// `Apply(Tuple([history, time, default]), Builtin(GetPrevTxn))`. Its
    /// polymorphic scheme `∀ν. ((Txn ⇒ {time: Txn, write: ν}), Txn, ν) ⇒ ν`
    /// lives in [`crate::ccl::infer::OperatorSchemes`].
    ///
    /// This is the **transaction-domain guard accessor** for a
    /// [`crate::ccl::TypedExprNode::LetRec`]: a binding whose reference to a
    /// commit-record binding is consumed only as the history argument depends
    /// only on strictly earlier commit times, which is what makes the
    /// `register ↔ commits` cycle well-founded (see
    /// `src/ccl/design/mutability.md`, "Builtins", and
    /// [`crate::ccl::letrec::check_letrec_causal`]).
    ///
    /// Op-conversion never compiles this builtin directly — like
    /// [`Self::GetPrevSeq`], letrec pattern recognition (the commit-operator
    /// complex) consumes it, so its op-conversion arm is a deliberate error.
    GetPrevTxn,

    /// `begin_<site> : 𝐼 ⇒ Txn` — the commit-time **oracle** for one `with
    /// begin():` site: where the site's iteration `𝑟` lands in the global
    /// commit order. Applied as `begin(r)` (`Apply(Var(r), Builtin(BeginTxn))`)
    /// inside a commit-record binding, it produces the transaction's commit time
    /// `t`, at which that writer's register snapshots are read (`balance(t)`).
    ///
    /// Minted by [`crate::ccl::transact_phase`] — one application per site,
    /// *after* inference, so it carries no scheme in
    /// [`crate::ccl::infer::OperatorSchemes`]; its type `𝐼 ⇒ Txn` is
    /// stamped on the node at emission and the post-phase CHECK-mode `typecheck`
    /// (which trusts a builtin's recorded type) validates it directly. Opaque
    /// and consumed by [`crate::ccl::planning::plan_loops`], which reads the
    /// writer's source and body off the commit-record binding and discards the
    /// `begin`/`balance(t)` plumbing. Like [`Self::GetPrevSeq`] /
    /// [`Self::GetPrevTxn`] it never reaches op-conversion, so its op-conversion
    /// arm is a deliberate error. A single shared builtin serves every site: the
    /// site identity recognition needs (the source stream + iteration domain)
    /// lives in the commit-record binding, not in the oracle.
    BeginTxn,

    /// `collection_union : (Fun(A, B), Fun(C, D)) → Fun(Union(A, C), dedup(B, D))`
    ///
    /// Merges two function-typed (collection) values into a single collection whose
    /// domain is the discriminated union of both input domains and whose codomain is
    /// the deduplicated union of both input codomains.  Lowered from Python `a @ b`.
    CollectionUnion,

    /// `as_of : Tuple(Fun(B, _), Fun(Txn, V)) → Fun(B, V)` — the **as-of
    /// (temporal) join**, the live cross-endpoint read. Applied as a tupled
    /// argument `Apply(Tuple([trigger, source]), Builtin(AsOf))`: for each
    /// `trigger` (request-loop) position, latch `source`'s (a transactional
    /// register's running render, `Fun(Txn, V)`) latest-decided value as of that
    /// position. The reply is indexed by the *trigger* (the enclosing request
    /// loop), not the commit clock — an outer-indexed read.
    ///
    /// Born in [`crate::ccl::transact_phase`]'s `rewrite_live_reads`, run
    /// **pre-lambda-elim** (after `channelize`): it recognizes a read-only
    /// reply — a chain of live-register reads `let k₁ = final_or_default((balance.f₁, _))
    /// in … in trigger ≫ (λ r → e)` — and rewrites it, dropping the never-resolving
    /// `final_or_default`s. Reading **one** register → `as_of((trigger, balance.f)) ≫
    /// (λ k → e)`; reading **several** → `as_of((trigger, balance)) ≫ (λ snap → e[kᵢ
    /// ↦ snap.fᵢ])`, a single snapshot record folded at one commit frontier so the
    /// registers are read atomically (§I-c). Running before lambda elimination
    /// keeps a computed reply (`e = k + 1`) a lambda the elim pass point-frees,
    /// rather than a point-free `const` that could only be broadcast. Compiles to
    /// the [`crate::interpreter::commit_operator`] `AsOf` tile operator (scalar- or
    /// record-valued). It carries its **own recorded type** (no inference scheme):
    /// op-conversion and every post-phase `typecheck` read `.ty` directly, and
    /// planning treats it as an iteration-bearing source (it stages the trigger
    /// inside its tuple rather than prepending an `iterate`).
    AsOf,

    /// `keydom#id : 𝐾 ⇒ Bool` — the **characteristic function of one key domain**,
    /// the predicate atom of a concrete keyed collection's domain
    /// `{𝑘: 𝐾 | 𝑘 ▷ keydom#id}`. It is what [`TypeKind::Keyed`](crate::ccl::ty::TypeKind::Keyed) ranges over: the
    /// kind is *every* key domain over 𝐾, and a token names one of them.
    ///
    /// **Opaque, and that is the point.** The token says only "the keys of *this*
    /// collection" — it does not say which keys, and nothing can look inside it. Its
    /// [`KeyDomId`] is minted per creation site, so two collections' key domains are
    /// the same iff they came from the same site. Type identity is therefore an
    /// integer comparison rather than a structural comparison of an embedded
    /// collection term, and a type stops carrying a term that exists only to be
    /// compared. The key type is instead pinned at the *producer*, by a
    /// [`Type::SharedHole`](crate::ccl::Type::SharedHole) linking this token's domain
    /// to the key function's codomain.
    ///
    /// Its type is **pre-stamped** at construction (no
    /// [`crate::ccl::infer::OperatorSchemes`] scheme), so emit reads `.ty` directly.
    ///
    /// **Never executed.** Key-domain membership would be evaluated only at a keyed
    /// *lookup* (`m[k]` totality) or a membership *filter* (`x in s`), neither of
    /// which exists yet. Until then the atom is a *carried* refinement term: planning
    /// compiles it to point-free form along with every other surviving predicate, so
    /// it does appear in post-planning types, but it is never lowered to a `Restrict`
    /// — `Converse` discharges the present-key domain structurally. That makes "no
    /// `KeyDom` reaches op-conversion" a real invariant rather than a coincidence, so
    /// op-conversion **asserts** it (`debug_assert_no_unexecutable_atoms`) instead of
    /// relying on no code path picking the predicate up. See
    /// `src/ccl/design/collections.md`.
    KeyDom(KeyDomId),

    /// `reify : (𝐷 ⇒ 𝑉) → (𝐷 ⤇ 𝑉)` — the sanctioned **capability→collection**
    /// coercion: force a compute function over a countable domain into a data
    /// collection over that same domain. This is the one reverse of the
    /// `Data <: Compute` subtyping direction: `Compute <: Data` is forbidden as a
    /// silent subtype (it would let a capability stand where a lossless collection is
    /// demanded), but `reify` makes the crossing *explicit* — the programmer (or a
    /// lowering) asserts the domain is enumerable and asks for its materialization.
    /// A plain [`cast`](crate::ccl::TypedExprNode::Cast) cannot express this: its
    /// obligation is `value <: target`, and `(𝐷 ⇒ 𝑉) <: (𝐷 ⤇ 𝑉)` is exactly the
    /// rejected direction.
    ///
    /// The gate is **countability**, not finiteness. Every Cambra type is
    /// countable today, and unbounded programs are supported (reifying a function
    /// over all naturals is a legitimate, if divergent-if-forced, request), so
    /// there is no static finiteness obligation to discharge.
    ///
    /// **Eval / op-conversion are deferred.** `reify`'s sole current producer is
    /// `groupby` lowering, and the atom is consumed in two stages, neither of them
    /// op-conversion: **lambda elimination** eliminates the inner cast-lambda to the
    /// point-free group-by source and flips that arrow's kind to `Data` (`reify`'s
    /// only runtime-visible act), and **planning** is what recognizes the resulting
    /// Pi-const source as [`Converse`](Self::Converse)
    /// (`convert_groupby_pointful`). That ordering is forced: the group-by
    /// recognizers must run on the *bare* pointful predicate form, before
    /// `compile_refinement_predicates`. A standalone `reify` (e.g. user-forced
    /// iteration over an unbounded domain) has no runtime yet, and reaching
    /// op-conversion with one is an `Unsupported` conversion error, not a silent
    /// miscompile (see `src/ccl/design/collections.md`). It is a **dependent kind-transformer**, so
    /// inference types `reify(𝑓)` by a dedicated arm in
    /// [`emit_apply`](crate::ccl::infer) that flips the argument function's kind to
    /// `Data` while preserving its (possibly dependent) Pi binder — a flat scheme
    /// `(𝐷 ⇒ 𝑉) → (𝐷 ⤇ 𝑉)` would decompose a group-by's dependent codomain out of
    /// the key binder's scope.
    Reify,

    /// `lookup? : ((𝑘: 𝐷) ⤇ 𝑉, 𝐾) → Option(𝑉[𝑘 ↦ key])` — the **checked** lookup
    /// `c[k]?`, the surface operator for evaluating a finite function at a point that
    /// is *not known to be in its domain* (`docs/chl-spec.md`, "3.9 Subscript and
    /// attribute access").
    ///
    /// It is **not a second application rule.** `c[k]?` is `c(k)` with one thing
    /// relaxed — the domain's *membership* refinement is dropped before the argument
    /// edge runs — and the result wrapped in `Option`. Everything else is ordinary
    /// dependent application: the key is still checked against the domain's base type
    /// (so an `Int` key never reaches a `String`-keyed map), and the Pi binder is still
    /// discharged to the argument, so a group-by lookup's partition predicate reflects
    /// the key it was looked up at. The proven operator `c[k]` is the same edge
    /// *without* the drop, which is why the two are one mechanic and not one rule per
    /// collection kind (`src/ccl/design/collections.md`, "Lookup: membership
    /// discharge").
    ///
    /// Only the **membership** refinement is dropped — the key-domain token — never an
    /// arbitrary one. A restricted map's `{𝐾 | tok ∧ valid(𝑘)}` keeps `valid(𝑘)` as a
    /// genuine obligation: not knowing whether a key is *present* is what `Option`
    /// answers, and it says nothing about whether the key was *admissible*.
    ///
    /// Typed by a dedicated arm in [`emit_apply`](crate::ccl::infer) for the same reason
    /// [`Reify`](Self::Reify) is: the codomain may mention the key binder, and a flat
    /// scheme would decompose it out of that binder's scope.
    LookupChecked,
}

impl Builtin {
    /// Stable, source-style display name for this built-in, used by
    /// [`crate::ccl::symbolic`] and the pretty-printer when rendering
    /// applied primitives.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Id => "id",
            Self::Box => "box",
            Self::Curry => "curry",
            Self::Const => "const",
            Self::Zip => "zip",
            Self::Apply => "apply",
            Self::Map => "map",
            Self::MapDomain => "map_domain",
            Self::Compose => "compose",
            Self::Converse => "converse",
            Self::Uncurry => "uncurry",
            Self::Restrict => "restrict",
            Self::Iterate => "iterate",
            Self::PermuteDomain => "permute_domain",
            Self::FlattenDomain => "flatten_domain",
            Self::BinOp(op) => op.fn_name(),
            Self::Neg => "neg",
            Self::NotFn => "not_fn",
            Self::FilterValues => "filter_values",
            Self::Sum => "sum",
            Self::Max => "max",
            Self::Drain => "drain",
            Self::FinalOrDefault => "final_or_default",
            Self::GetPrevSeq => "get_prev_seq",
            Self::GetPrevTxn => "get_prev_txn",
            Self::BeginTxn => "begin",
            Self::CollectionUnion => "collection_union",
            Self::AsOf => "as_of",
            // The id is deliberately *not* rendered: it is a per-site identity, so
            // printing it would make every type golden depend on minting order.
            Self::KeyDom(_) => "keydom",
            Self::Reify => "reify",
            Self::LookupChecked => "lookup?",
        }
    }

    /// Built-in name for a unary [`UnaryOpKind`].
    pub fn for_unaryop(op: UnaryOpKind) -> Self {
        match op {
            UnaryOpKind::Neg => Self::Neg,
            UnaryOpKind::Not => Self::NotFn,
        }
    }

    /// Built-in name for an [`AggregateKind`].
    pub fn for_aggregate(kind: AggregateKind) -> Self {
        match kind {
            AggregateKind::Sum => Self::Sum,
            AggregateKind::Max => Self::Max,
            AggregateKind::Drain => Self::Drain,
        }
    }

    /// Op-conversion's `Apply { argument, function: Builtin(self) }` arm
    /// compiles `argument` (or, for tuple-shaped arguments, its
    /// iteration-source sub-parts) with `input=None`, treating it as a
    /// function-typed iteration source.  This is op-conversion's
    /// "input-internalising" group.
    ///
    /// Consulted by two helpers in [`crate::ccl::planning`]:
    ///
    /// - `is_internalising_builtin_function` — at `Apply { function }`
    ///   positions during the iteration-site walk, decides which
    ///   builtins' arguments to wrap with `iterate(_)`.  `CollectionUnion`
    ///   and `FinalOrDefault` are in this list because they self-iterate
    ///   from sub-parts of their tuple argument, but the walk's
    ///   per-shape match arms handle them before the catch-all that
    ///   consults this metho — so the per-element wrapping fires first
    ///   and the catch-all isd never reached for them.
    /// - `is_iteration_bearing` — at chain heads, decides which builtins
    ///   already provide their own iteration (and so should not be
    ///   wrapped with another `iterate(_)`).  Scalar-result builtins
    ///   (`Sum`, `Max`, `FinalOrDefault`) are in the list too; the
    ///   caller's `expr.ty.domain()` check filters them out at chain
    ///   heads independently.
    ///
    /// `Iterate` is NOT in this list — it is an iteration source, but
    /// it does not iterate *from* its argument (the argument is the
    /// predicate, threaded with `input=Some`).  `is_iteration_bearing`
    /// handles `Iterate` separately.  `Restrict` is also excluded: it
    /// threads its input through to the predicate (`input=Some`),
    /// neither iterating from arg nor providing its own iteration.
    ///
    /// Keep in sync with the corresponding arms in operator_conversion.rs.
    pub fn iterates_arg(self) -> bool {
        matches!(
            self,
            Self::Sum
                | Self::Max
                | Self::Drain
                | Self::Converse
                | Self::MapDomain
                | Self::Uncurry
                | Self::PermuteDomain
                | Self::FlattenDomain
                | Self::CollectionUnion
                // `GetPrevSeq`/`GetPrevTxn` share `FinalOrDefault`'s
                // classification (a scalar-result builtin over a tuple whose
                // stream sub-part self-iterates), but op-conversion never sees
                // them: letrec pattern recognition consumes them first, and the
                // op-conv arm errors deliberately (see the variant docs).
                | Self::FinalOrDefault
                | Self::GetPrevSeq
                | Self::GetPrevTxn
        )
    }
}

impl From<BinOpKind> for Builtin {
    fn from(op: BinOpKind) -> Self {
        Self::BinOp(op)
    }
}

impl fmt::Display for Builtin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// The key identifying which field a [`TypedExprNode::Proj`](crate::ccl::TypedExprNode::Proj) projects.
///
/// Supports both positional tuple fields (`.0`, `.1`, …) and named record
/// fields (`.name`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProjKey {
    /// Integer-indexed tuple projection: `.0`, `.1`, …
    Index(usize),
    /// Named record-field projection: `.fieldname`.
    Field(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `from_keyword` is a total inverse of `keyword` over every variant — the
    /// law that lets the reader and all writer sites share one spelling table.
    #[test]
    fn base_type_keyword_round_trips() {
        for b in [
            BaseType::Int,
            BaseType::UInt,
            BaseType::String,
            BaseType::Bool,
            BaseType::Unit,
        ] {
            assert_eq!(BaseType::from_keyword(b.keyword()), Some(b));
        }
        assert_eq!(BaseType::from_keyword("List"), None);
    }
}
