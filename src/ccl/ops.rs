//! Scalar primitives shared across the CCL pipeline: base types, literal
//! constants, the binary / unary operator kinds, the [`Builtin`] combinator
//! enum, and projection keys.

use std::fmt;

use crate::ccl::{AggregateKind, FieldKey};

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
    /// Integer addition whose result type records the sum (`^+`).
    ///
    /// Computes exactly what [`Add`](Self::Add) computes; the two differ only in
    /// the trait each states, and so in the type the result takes. `+` is
    /// `Addable` — `Int`, `UInt` or `String` operands, and an unrefined result.
    /// `^+` is `AddableRefined`, whose one row accepts `Int` operands and refines
    /// the result by `__elem == a₁ + a₂` (`src/ccl/infer/solver/traits.rs`).
    AddRefined,
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
            Self::Arithmetic(ArithmeticKind::AddRefined) => "^+",
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
            Self::Arithmetic(ArithmeticKind::AddRefined) => "add_refined",
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
///
/// # Typing
///
/// **Every variant below opens its doc comment with its type**, written
/// `name : 𝑇`, so a built-in's signature is readable at the definition rather
/// than reconstructed from its emitters. Two conventions in those signatures:
///
/// - A built-in that takes a *static* argument before the value it transforms
///   (`restrict`, `permute_domain`, `flatten_domain`, `filter_values`, …) is
///   emitted as `arg ▷ builtin`, so its type is curried and reads
///   `Arg ⇒ (𝐴 ⇒ 𝐵)`. One that names its parameter *in the enum variant*
///   (`variant_project(c)`, `variant_wrap(c)`) instead appears bare, and its
///   type is the uncurried `𝐴 ⇒ 𝐵`.
/// - The handful of built-ins that *are* visible to inference (the binary
///   operators, the aggregations, `final_or_default`, `get_prev_seq`,
///   `get_prev_txn`, `await_final`) additionally carry a polymorphic scheme in
///   [`OperatorSchemes`](crate::ccl::infer::OperatorSchemes), which is the
///   authority for those. The rest are minted post-inference: their type is
///   stamped on the node at emission, and the post-phase CHECK-mode
///   `typecheck` trusts the stamp.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Builtin {
    // Categorical combinators (introduced by lambda elimination).
    /// `id : A → A` — identity morphism.
    Id,
    /// `box : ∀𝑎. 𝑎 ⇒ Σ (σ : [𝑎]). σ` — the **only** way into a dependent sum.
    ///
    /// Puts a value into the sum whose single candidate is its own type. Subtyping has
    /// no `𝑇 <: Σ` rule, so a sum is never formed by subsumption and a join can never
    /// produce one the program did not write (`src/ccl/design/type-inference.md`,
    /// "Only a term builds a sum"). What makes `box` useful is not the singleton it builds
    /// but what two of them do at a join: candidates union in the kind lattice, so
    /// `box(xs) if c else box(ys)` keeps *both* alternatives where the unboxed
    /// conditional has no upper bound at all.
    ///
    /// The candidate position is **invariant**, so `𝑎` is pinned to the argument's type
    /// exactly — `box(5)` is `Σ (σ : [5]). σ`, not `Σ (σ : [Int]). σ`. Retaining the
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
    /// `permute_domain : [Int] ⇒ ((𝐴 ⇒ 𝑋) ⇒ (𝐵 ⇒ 𝑋))` — reorder positions in a
    /// tuple-typed domain. Applied to its permutation list first
    /// (`perm ▷ permute_domain`), yielding the morphism rewriter: `𝐴` and `𝐵`
    /// are the same tuple type under two orderings, and `perm[j]` is where
    /// canonical position `j` sits in `𝐴`.
    PermuteDomain,
    /// `flatten_domain : [Int] ⇒ ((𝐴 ⇒ 𝑋) ⇒ (𝐵 ⇒ 𝑋))` — flatten selected
    /// nested-tuple positions in a domain. Applied to its index list first, like
    /// [`Self::PermuteDomain`]; `𝐵` is `𝐴` with the listed positions spliced open.
    FlattenDomain,

    /// `binop(op) : (𝐴, 𝐵) ⇒ 𝐶` — a binary scalar operation lifted to a function
    /// on a 2-tuple (`(a, b) ▷ BinOp(op)`). The concrete instance is the
    /// operator's own scheme in [`crate::ccl::infer::OperatorSchemes`]
    /// (`(Int, Int) ⇒ Int` for arithmetic, `(𝐴, 𝐴) ⇒ Bool` for comparison, …).
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

    /// `map_filter : ((𝑘: 𝐾) ⤇ (𝐼 ⇒ Bool)) ⇒ ((𝑘: 𝐾) ⤇ ({𝑖: 𝐼 | 𝑝(𝑘, 𝑖)} ⤇ 𝑉))` — a
    /// filter on the **inner collections** of a partition, one outer key at a time.
    ///
    /// `Apply(p, MapFilter)` requires `input=Some(_)`, the curried collection to
    /// filter. [`Self::Restrict`] and [`Self::FilterValues`] both narrow a single
    /// domain; neither reaches the inner domain of a curried function, where the
    /// surviving elements differ per key. Planning emits this when a refinement rides
    /// the inner collection's domain under the outer key's binder, which is what a
    /// per-group filter (`sum([s.amount for s in g if s.qty > 2])`) produces.
    /// Compiles to the `MapFilter` tile operator.
    MapFilter,

    // Aggregations (codomain of a function-typed input → scalar).
    /// `sum : ∀α. (α ⤇ Int) ⇒ Int` — fold a collection's `Int` codomain.
    Sum,
    /// `max : ∀α γ. (α ⤇ γ) ⇒ γ` — fold a collection's codomain to one of the
    /// same type.
    Max,
    /// `final_or_default : Tuple(Fun(D, T), T) → T` — extract the
    /// codomain value at the final position of an iteration stream, or
    /// fall back to the default scalar when the stream's domain is
    /// empty.  Compiles directly to the `ExtractFinal` tile operator
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
    /// jointly with the `.rev().find(…)` in `ExtractFinalProducer` —
    /// both assume the source's final position by emission order, not
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
    /// recognition consumes it (the causal self-cycle becomes the induction-store
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
    /// `mutable variable ↔ commits` cycle well-founded (see
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
    /// `t`, at which that writer's mutable variable snapshots are read (`balance(t)`).
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

    /// `await_final : Mut(𝑉, Txn) ⇒ 𝑉` — the **terminal read** of a transactional
    /// mutable variable: its final committed value, once the whole commit history is
    /// complete. Applied to the mutable variable *handle* (`x ▷ await_final`), which is
    /// why its domain is a `Mut` and not a `𝑉`: `await_final` reduces the history rather than
    /// consuming one sampled value, so the operand is a handle position like a
    /// pass-by-reference argument or a write target (see
    /// `src/ccl/design/mutability.md`, "A mutable variable read is an explicit operation").
    /// Its scheme `∀ν. Mut(ν, Txn) ⇒ ν` lives in
    /// [`crate::ccl::infer::OperatorSchemes`] — the domain pins `Txn`, so awaiting
    /// an induction accumulator is a type error and not a silent success.
    ///
    /// This is the only surface term that waits for a `Txn` history's
    /// *completeness*; every other fed-out mutable variable read is an arbitrary as-of
    /// sample ([`Self::AsOf`]). It is a surface marker in the sense the `For` /
    /// `Begin` / `MutWrite` nodes are: [`crate::ccl::transact_phase`] consumes it,
    /// replacing each occurrence with `final_or_default(hist_x, init)` over the
    /// mutable variable's history binding — the single sanctioned application of
    /// [`Self::FinalOrDefault`] to a commit history. So it never reaches
    /// op-conversion, and its arm there is a deliberate error like
    /// [`Self::BeginTxn`]'s.
    AwaitFinal,

    /// `copair : (Fun(A, B), Fun(C, D)) → Fun(Variant({.0: A, .1: C}), dedup(B, D))`
    ///
    /// Merges two function-typed (collection) values into a single collection whose
    /// domain is the discriminated union of both input domains and whose codomain is
    /// the deduplicated union of both input codomains.  Lowered from Python `a @ b`.
    Copair,

    /// `as_of_read : (Txn ⇒ 𝑉) ⇒ 𝑉` — an **as-of read of a commit history whose position
    /// is not yet supplied**, which is what every fed-out mutable variable read is.
    /// [`crate::ccl::transact_phase`] binds each store key the continuation still names to
    /// one; `rewrite_as_of_reads` then pairs it with the reading loop that indexes it and
    /// rewrites the pair to an [`Self::AsOf`] join, which supplies the position. The two
    /// are one construct in two stages, which is why they share the name.
    ///
    /// The stage exists so that an as-of read and a terminal read are **different terms**.
    /// Both sample the same `Fun(Txn, V)` history and differ only in the position sampled, so
    /// a single term for the pair would separate them by position alone — which does not
    /// survive the passes that legitimately move a read (`channelize` copies a channel's
    /// captured bindings inside the channel), letting an `await_final` land where the rewrite
    /// matches. Distinct terms also make a *missed* rewrite loud: an unpaired `as_of_read` is
    /// rejected after the rewrite rather than compiling to a read that waits forever.
    ///
    /// Minted post-inference, so it carries its own recorded type and has no scheme.
    AsOfRead,

    /// `final_read : (Txn ⇒ 𝑉) ⇒ 𝑉` — the **terminal read** of a transactional mutable
    /// variable: its value at the position its own writers finish.
    /// [`crate::ccl::transact_phase`] mints it for a surface [`Self::AwaitFinal`] marker,
    /// naming the mutable variable's history binding.
    ///
    /// Like [`Self::AsOfRead`] it is a *sample* of the carried value rather than a
    /// reduction of a stream, so it takes no seed operand — tick 0 of every store is its
    /// keys' seeds. Unlike `AsOfRead` it needs no pairing: the position comes from the
    /// store's own closure rather than from a reading loop, so it reaches op-conversion
    /// and compiles to the `StoreFinalRead` tile operator.
    ///
    /// Minted post-inference, so it carries its own recorded type and has no scheme.
    FinalRead,

    /// `as_of : Tuple(Fun(B, _), Fun(Txn, V)) → Fun(B, V)` — the **as-of
    /// (temporal) join**, the live cross-endpoint read. Applied as a tupled
    /// argument `Apply(Tuple([trigger, source]), Builtin(AsOf))`: for each
    /// `trigger` (request-loop) position, latch `source`'s (a transactional
    /// mutable variable's running render, `Fun(Txn, V)`) latest-decided value as of that
    /// position. The reply is indexed by the *trigger* (the enclosing request
    /// loop), not the commit clock — an outer-indexed read.
    ///
    /// Born in [`crate::ccl::transact_phase`]'s `rewrite_as_of_reads`, run
    /// **pre-lambda-elim** (after `channelize`): it recognizes a read-only reply — a chain
    /// of as-of reads `let k₁ = as_of_read(balance.f₁) in … in trigger ≫ (λ r → e)` —
    /// and supplies each read's position from the trigger, which is the one thing
    /// [`Self::AsOfRead`] leaves open. Reading a single mutable variable → `as_of((trigger, balance.f)) ≫
    /// (λ k → e)`; reading **several** → `as_of((trigger, balance)) ≫ (λ snap → e[kᵢ
    /// ↦ snap.fᵢ])`, a single snapshot record folded at one commit frontier so the
    /// mutable variables are read atomically (§I-c). Running before lambda elimination
    /// keeps a computed reply (`e = k + 1`) a lambda the elim pass point-frees,
    /// rather than a point-free `const` that could only be broadcast. Compiles to
    /// the [`crate::interpreter::commit_operator`] `AsOf` tile operator (scalar- or
    /// record-valued). It carries its **own recorded type** (no inference scheme):
    /// op-conversion and every post-phase `typecheck` read `.ty` directly, and
    /// planning treats it as an iteration-bearing source (it stages the trigger
    /// inside its tuple rather than prepending an `iterate`).
    AsOf,

    /// `variant_project(c) : Union({cᵢ: Pᵢ}) ⇒ P_c` — the elimination-side dual
    /// of [`crate::ccl::TypedExprNode::VariantCtor`]/`VariantWrap`. Projects the
    /// arm named `c` out of a tagged-union stream, **restricting to the sub-domain
    /// of positions that carry tag `c`** and yielding that arm's inner payload
    /// column.
    ///
    /// Minted by [`crate::ccl::lambda_elim`] when it compiles a scrutinee-`Case`
    /// over a [`crate::ccl::Type::Variant`] to the union-of-tag-restricts
    /// `⧺ᵢ (𝑑 ≫ variant_project(𝑐ᵢ) ≫ (λ 𝑤ᵢ → 𝑒ᵢ))` — a `≫`-chain, not an
    /// application chain: `𝑑` is the eliminated scrutinee *morphism* out of the
    /// enclosing binder, and both of the elements after it are functions of its
    /// output. It is applied as a
    /// compose element consuming the fed scrutinee stream (`input=Some`, like
    /// [`Self::Restrict`]/[`Self::FilterValues`]), so op-conversion reads the
    /// union extents off the fed input's tiling and builds the
    /// [`crate::interpreter::tile_operators::VariantProject`] tile op. The
    /// per-arm sub-streams are re-totaled by a **flat** `UnionOperator` (the
    /// tags partition the domain exhaustively).
    ///
    /// **Restrict and project are one op** because [`crate::interpreter::ColumnValue::Union`]
    /// stores each arm against the rows that carry it (see the tile-op docs), so
    /// reading the arm *is* the restriction; there is no separate boolean
    /// `Restrict` step and no tag-discriminating `Predicate`.
    ///
    /// **A tag the scrutinee does not carry is not an error** — it projects empty.
    /// That is what makes a width-subtype scrutinee well-formed here.
    ///
    /// Minted after inference, so it carries no [`crate::ccl::infer::OperatorSchemes`]
    /// scheme: its type `Union ⇒ P_c` is stamped on the node and the post-phase
    /// CHECK-mode `typecheck` trusts it (like [`Self::BeginTxn`]).
    VariantProject(FieldKey),

    /// `variant_wrap(c) : P_c ⇒ Union({cᵢ: Pᵢ})` — the introduction-side dual of
    /// [`Self::VariantProject`]: injects a payload at the arm named `c`,
    /// producing a tagged union value. The **point-free** form of
    /// [`crate::ccl::TypedExprNode::VariantCtor`].
    ///
    /// Minted by [`crate::ccl::lambda_elim`] when a `VariantCtor` appears inside
    /// a lambda body (``λ p → `𝑐ᵢ(eᵢ(p))``): the constructor elaborates to
    /// `eᵢ ≫ variant_wrap(𝑐ᵢ)`, a composable morphism `param_ty ⇒ Union` that can
    /// sit as the RHS of a `≫` — e.g. a writer-decision arm
    /// `filter_values(π̂ᵢ) ≫ eᵢ ≫ variant_wrap(Commit)`. (A genuinely scalar
    /// `VariantCtor` outside any lambda keeps its own node + op-conversion arm.)
    ///
    /// Applied as a compose element consuming the fed payload stream
    /// (`input=Some`, like [`Self::VariantProject`]); op-conversion reads the
    /// union extents off the node's codomain and builds the **existing**
    /// [`crate::interpreter::tile_operators::VariantWrap`] tile, which wraps the
    /// payload stream element-wise (preserving the domain).
    ///
    /// Minted after inference, so it carries no [`crate::ccl::infer::OperatorSchemes`]
    /// scheme: its type `P_c ⇒ Union` is stamped on the node and the post-phase
    /// CHECK-mode `typecheck` trusts it (like [`Self::BeginTxn`]).
    VariantWrap(FieldKey),
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
            Self::MapFilter => "map_filter",
            Self::Sum => "sum",
            Self::Max => "max",
            Self::FinalOrDefault => "final_or_default",
            Self::GetPrevSeq => "get_prev_seq",
            Self::GetPrevTxn => "get_prev_txn",
            Self::BeginTxn => "begin",
            Self::AwaitFinal => "await_final",
            Self::Copair => "copair",
            Self::AsOfRead => "as_of_read",
            Self::FinalRead => "final_read",
            Self::AsOf => "as_of",
            // The arm index is rendered by `symbolic` (a `&'static str` cannot
            // carry it); this bare name is the fallback for other callers.
            Self::VariantProject(_) => "variant_project",
            Self::VariantWrap(_) => "variant_wrap",
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
    ///   builtins' arguments to wrap with `iterate(_)`.  `Copair`
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
                | Self::Converse
                | Self::MapDomain
                | Self::Uncurry
                | Self::PermuteDomain
                | Self::FlattenDomain
                | Self::Copair
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
