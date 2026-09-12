//! Semantic refinement subtyping, discharged to an SMT solver.
//!
//! Refinement subtyping in [`super::constrain`] matches refinements by structural
//! predicate equality, which is sound and incomplete: `{Int | __elem == 1 ^+ 3 ^+ 2}`
//! and `{Int | __elem == 1 ^+ 5}` denote one set and compare unequal. This module
//! decides the leftover cases by asking whether the lhs predicates entail the rhs
//! ones.
//!
//! The encoded fragment is linear integer arithmetic over scalars. A product — a
//! record or a tuple — has no sort of its own and is reached through its fields
//! instead: a predicate reads one by projection, and the [`Path`] that read
//! addresses is what an SMT constant is minted for.
//!
//! The fragment is over **surface-syntax** predicate shapes: a variable, a field
//! read, a literal, a unary or a binary operator ([`Encode::expr`]). `lambda_elim`
//! rewrites every predicate point-free — `__elem == 1` becomes
//! `__elem ▷ ((id, 1 ▷ const) ▷ zip ≫ eq)` — so no predicate at or after that pass
//! is encodable, and every check from there on decides its deficits structurally.
//! The reach of the fallback is therefore inference and [`crate::ccl::inline`], not
//! the whole pipeline.
//!
//! `smt_sub` answers `false` for one reason: the solver found a model of
//! `⋀lhs ∧ ¬⋀rhs`, a value of the base satisfying every lhs predicate and
//! violating an rhs one. Every other outcome is an [`SmtError`] naming what
//! happened — a query outside the fragment (a base that is neither a scalar nor a
//! product, floor division, a product of two unknowns, a predicate mentioning an
//! application that is not a projection), a solver that will not start or breaks
//! mid-query, an `unknown`. An `Err` is not a mismatch: nothing decided the
//! entailment.

use std::collections::{HashMap, HashSet};
use std::io;

use easy_smt::{Context, ContextBuilder, Response, SExpr};

use crate::ccl::infer::solve::resolve_var_type;
use crate::ccl::symbolic::symbolic;
use crate::ccl::{
    ArithmeticKind, BaseType, BinOpKind, CompareKind, Lit, LogicKind, Name, ProjKey, Refinement,
    Type, TypedExpr, TypedExprNode, UnaryOpKind,
};

/// The solver subprocess `easy_smt`'s z3 defaults spawn. Named by every
/// [`SmtError`] report, so a machine without it on PATH is told what is missing.
pub const SOLVER_BINARY: &str = "z3";

#[derive(Debug, Clone)]
pub enum SmtError {
    /// A type or term outside the encoded fragment. Translation stops at the
    /// first body it cannot read, so a second such body is not reported.
    Encoding {
        /// The refinement whose predicate has no encoding.
        body: Refinement,
        /// Description of the encoding failure.
        message: String,
    },
    /// The solver process could not be spawned, or the pipe to it failed.
    Process {
        /// A stringified [`io::Error`].
        message: String,
    },
    /// The solver answered `unknown`, which is neither an entailment proof nor a
    /// counterexample.
    SolverReportedUnknown,
    /// The solver's reply to a command was not one this module expects: an
    /// `(error …)` reply, which is a misencoding on this side, or no parsable
    /// reply, which is a solver that stopped answering. `easy_smt` reports both
    /// as [`io::ErrorKind::Other`], which is the only signal separating them from
    /// a broken pipe.
    SolverError {
        /// A stringified [`io::Error`], carrying the solver's reply.
        message: String,
    },
}

/// The report a caller prints for a query that went unasked or unanswered. The
/// [`SmtError::Process`] wording carries the install step, because a machine
/// without a solver sees that variant and no other.
impl std::fmt::Display for SmtError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SmtError::Encoding { body, message } => write!(
                f,
                "the refinement predicate {} is outside the supported SMT encoding ({message})",
                symbolic(&body.predicate)
            ),
            SmtError::Process { message } => write!(
                f,
                "refinement subtyping runs queries against `{SOLVER_BINARY}`, which could not be \
                 started: {message}. Install it and put it on PATH — `./ci.sh solver` checks for \
                 it, and `.github/workflows/ci.yml` pins the release CI installs."
            ),
            SmtError::SolverReportedUnknown => {
                write!(f, "`{SOLVER_BINARY}` answered `unknown`")
            }
            SmtError::SolverError { message } => {
                write!(f, "`{SOLVER_BINARY}` reported an error: {message}")
            }
        }
    }
}

/// SMT representations of Cambra types. If a refinement base type is
/// encountered that cannot be represented by `Sort`, the check fails
/// fast.
#[derive(Debug, Clone)]
pub enum Sort {
    Bool,
    Int,
    /// Represented as `Int` where `_ >= 0`.
    UInt,
    /// Represented as `Int` where `_ >= 0 && _ < n`.
    UIntRange(usize),
    /// A sort reached by the solver's own spelling for it, carrying no constraint
    /// of its own. `String` is the case: z3's built-in string sort, used here as a
    /// sort name. This reaches a built-in sort and not an uninterpreted one,
    /// which would need a `declare-sort` command that nothing here emits.
    Named(String),
}

impl Sort {
    /// Declare a constant of the given sort, and assert any relevant
    /// constraint (such as that the constant is `>= 0`, for a
    /// `UInt`).
    fn declare(self, sym: String, ctx: &mut Context) -> Result<(), SmtError> {
        let sym_atom = ctx.atom(sym.clone());
        let zero = || ctx.numeral(0);
        let non_neg = |x: SExpr| ctx.gte(x, zero());
        let lt = |x: SExpr, y: usize| ctx.lt(x, ctx.numeral(y));
        let (sort_atom, constraint) = match self {
            Self::Bool => (ctx.bool_sort(), None),
            Self::Int => (ctx.int_sort(), None),
            Self::UInt => {
                let c = non_neg(sym_atom);
                (ctx.int_sort(), Some(c))
            }
            Self::UIntRange(n) => {
                let c = ctx.and(non_neg(sym_atom), lt(sym_atom, n));
                (ctx.int_sort(), Some(c))
            }
            Self::Named(s) => (ctx.atom(s), None),
        };
        ctx.declare_const(sym, sort_atom)
            .map_err(exchange_failure)?;
        if let Some(c) = constraint {
            ctx.assert(c).map_err(exchange_failure)?;
        }
        Ok(())
    }
}

/// The lexical scope a solver query runs in — the `Γ` of `Γ ⊢ ⋀lhs ⇒ ⋀rhs`.
///
/// A lookup rather than an enumeration, because that is the whole of what the
/// encoding needs: it meets a free name while translating a predicate and asks
/// what the scope binds it at. Enumerating instead would declare every binder in
/// scope, and a binder nothing mentions can still change the answer — a
/// contradictory one would prove the entailment outright.
///
/// The one implementor that answers is inference's lexical scope (`InferCtx`'s
/// `ScopeStack`, `src/ccl/infer/context.rs`). [`NoScope`] is the empty
/// environment, which every other caller passes: a query raised after inference
/// runs over a tree whose binder types the caller does not hold. See
/// `src/ccl/design/type-inference.md`, "The scope a query runs in".
pub trait ScopeEnv {
    /// The type a value has given `name` here, or `None` when this scope does not
    /// bind it or nothing has settled it.
    ///
    /// Owned, because during emission the slot a binder holds is an inference
    /// variable and answering means resolving it — there is no settled `Type` in
    /// the scope to hand out a borrow of.
    fn binder_type(&self, name: &Name) -> Option<Type>;
    /// Whether a subtyping comparison carrying this environment decides a
    /// refinement deficit structurally, without raising a query at all.
    ///
    /// Caller policy rather than part of the encoding: nothing in this module
    /// reads it, and every implementor outside
    /// [`constrain`](super::constrain) answers `false`. It rides the scope
    /// because the scope is what already reaches the deficit rule. The shape it
    /// wants is a parameter of its own on
    /// [`constrain_subtype_in`](super::constrain::constrain_subtype_in) — an
    /// `Option<&dyn ScopeEnv>`, where `None` is "do not ask" — which collapses
    /// the two empty scopes this flag forces apart.
    fn is_skip_smt(&self) -> bool;
}

/// The empty scope: no name is bound, so every free name in a query is
/// universally quantified with nothing assumed about it.
pub struct NoScope;

impl ScopeEnv for NoScope {
    fn binder_type(&self, _name: &Name) -> Option<Type> {
        None
    }
    fn is_skip_smt(&self) -> bool {
        false
    }
}

/// An access path: a root name and the projections read through it.
///
/// The unit an SMT constant is minted for. The encoded fragment is over scalars,
/// so a product-typed name denotes no constant of its own — each scalar leaf a
/// predicate reads out of it does, and keying that constant by the path is what
/// makes two occurrences of `x.b` one constant. A bare name is the path that reads
/// nothing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Path {
    /// The name the reads start from.
    root: Name,
    /// The projections, in reading order: `x.a.b` keys `[a, b]`.
    keys: Vec<ProjKey>,
}

impl Path {
    /// The path that reads nothing out of `root`.
    fn root(root: Name) -> Self {
        Path {
            root,
            keys: Vec::new(),
        }
    }

    /// The path [`REFINEMENT_BINDER`] addresses: the query's subject, unread.
    ///
    /// [`REFINEMENT_BINDER`]: crate::ccl::REFINEMENT_BINDER
    fn subject() -> Self {
        Path::root(Name::elem())
    }

    /// Whether this path reads the subject of the predicate it appears in rather
    /// than a name the scope binds.
    fn rooted_at_subject(&self) -> bool {
        self.root == Name::elem()
    }

    /// The path a term addresses: a name under zero or more projections. `None`
    /// for any other term, which is then outside the fragment.
    fn of(e: &TypedExpr) -> Option<Self> {
        match &e.node {
            TypedExprNode::Var(name) => Some(Path::root(name.clone())),
            // A field or position read is `Apply(Proj(k), r)`, so a chain of them
            // is a chain of `Apply`s and the keys accumulate innermost-first.
            TypedExprNode::Apply { function, argument } => match &function.node {
                TypedExprNode::Proj(key) => {
                    let mut path = Path::of(argument)?;
                    path.keys.push(key.clone());
                    Some(path)
                }
                _ => None,
            },
            _ => None,
        }
    }
}

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.root)?;
        for key in &self.keys {
            write!(f, ".{key}")?;
        }
        Ok(())
    }
}

/// Whether a term is an access path: a name under zero or more projections
/// ([`Path::of`]). What it denotes is whatever its root is bound to, so — unlike
/// every other shape [`reads`] admits — its own syntax says nothing about the kind
/// of value it is.
pub fn is_access_path(e: &TypedExpr) -> bool {
    Path::of(e).is_some()
}

/// Whether the encoder reads this term — the shapes [`Encode::expr`] translates,
/// tested without a solver and without the types a translation would need.
///
/// A caller minting a predicate out of program terms asks this first: a predicate
/// the encoder cannot read decides nothing, and one built into a *type* is carried
/// by every pass that type reaches. The two walks are one fragment and must agree
/// on its shape (`a_readable_term_is_what_the_encoder_translates`); this one is
/// deliberately blind to sorts, which are a property of a query's scope rather
/// than of the term.
pub fn reads(e: &TypedExpr) -> bool {
    match &e.node {
        TypedExprNode::Lit(Lit::Int(_) | Lit::Bool(_)) => true,
        // A name, or a field read through one. Any other `Apply` addresses no leaf.
        TypedExprNode::Var(_) | TypedExprNode::Apply { .. } => Path::of(e).is_some(),
        TypedExprNode::UnaryOp(_, operand) => reads(operand),
        TypedExprNode::BinOp { left, op, right } => {
            reads_op(*op, left, right) && reads(left) && reads(right)
        }
        _ => false,
    }
}

/// Whether an operator has an encoding at these operands — the operator half of
/// [`reads`], matching [`Encode::binop`]'s arms.
fn reads_op(op: BinOpKind, left: &TypedExpr, right: &TypedExpr) -> bool {
    match op {
        // A product stays linear when one factor is a constant, and `^*` computes
        // the product `*` computes.
        BinOpKind::Arithmetic(ArithmeticKind::Mul | ArithmeticKind::MulRefined) => {
            is_int_literal(left) || is_int_literal(right)
        }
        // SMT-LIB's `div` is Euclidean rather than floor division, `**` is a repeated
        // product with no integer exponentiation to state it with, and `++` is on
        // strings, which have no arithmetic here.
        BinOpKind::Arithmetic(ArithmeticKind::FloorDiv | ArithmeticKind::Pow)
        | BinOpKind::Concat => false,
        BinOpKind::Arithmetic(_) | BinOpKind::Compare(_) | BinOpKind::BoolLogic(_) => true,
    }
}

/// Whether every value of `base` satisfying all of `lhs` satisfies all of `rhs`.
///
/// [`REFINEMENT_BINDER`] is declared once at `base`'s sort and shared by both
/// sides, so the query is `∀ __elem. ⋀lhs ⇒ ⋀rhs`, decided by checking
/// `⋀lhs ∧ ¬⋀rhs` unsatisfiable. A `base` that is a product declares nothing
/// instead: it has no sort, and a predicate reaches its scalars by projection, so
/// each such [`Path`] is declared where it is read.
///
/// Every other leaf a predicate reads is declared at a sort too and is therefore
/// universally quantified as well; what is assumed about it comes from `scope`. A
/// path rooted at a name `scope` binds is declared at the sort its type gives it,
/// and the refinements the types along it carry join the antecedent, restated about
/// the path. Any other path is declared at the sort of the node reading it, with
/// the refinements its own type carries dropped — an assumption left out only
/// weakens the antecedent.
///
/// Both sides' predicates must already be transported into one frame — this
/// compares terms, so a name meaning two different things across the two sides
/// makes the answer meaningless.
///
/// `Ok(false)` is a counterexample the solver produced; anything that leaves the
/// query unasked or unanswered is an [`SmtError`].
///
/// [`REFINEMENT_BINDER`]: crate::ccl::REFINEMENT_BINDER
pub fn smt_sub(
    base: &Type,
    lhs: &[Refinement],
    rhs: &[Refinement],
    scope: &dyn ScopeEnv,
) -> Result<bool, SmtError> {
    if rhs.is_empty() {
        return Ok(true);
    }
    with_solver(|ctx| check(ctx, base, lhs, rhs, scope))
}

/// One query: build it, then run it inside a `push`/`pop` scope so the constants
/// it declares and the formula it asserts leave no trace for the next query.
fn check(
    ctx: &mut Context,
    base: &Type,
    lhs: &[Refinement],
    rhs: &[Refinement],
    scope: &dyn ScopeEnv,
) -> Result<bool, SmtError> {
    // Encoding is pure and can bail; bailing before the `push` leaves no scope to
    // unwind.
    let mut enc = Encode::new(ctx, scope, base);
    let formula = enc.query(lhs, rhs)?;
    let decls = enc.decls;

    ctx.push().map_err(exchange_failure)?;
    // A failed exchange poisons the slot and drops the context, so the `pop`
    // balancing this `push` only has to happen on the paths that leave the solver
    // usable — every path that got an answer, `Unknown` included.
    let response = run(ctx, decls, formula)?;
    ctx.pop().map_err(exchange_failure)?;

    match response {
        Response::Unsat => Ok(true),
        Response::Sat => Ok(false),
        Response::Unknown => Err(SmtError::SolverReportedUnknown),
    }
}

/// The whole exchange: declare the query's constants, assert it, ask.
fn run(
    ctx: &mut Context,
    decls: Vec<(String, Sort)>,
    formula: SExpr,
) -> Result<Response, SmtError> {
    for (sym, sort) in decls {
        log::debug!("declare {sym} at {sort:?}");
        sort.declare(sym, ctx)?;
    }
    log::debug!("check {}", ctx.display(formula));
    ctx.assert(formula).map_err(exchange_failure)?;
    ctx.check().map_err(exchange_failure)
}

/// Classify a failed exchange with a solver that had started.
///
/// `easy_smt` reports every reply it cannot use as [`io::ErrorKind::Other`] and
/// leaves a pipe failure the kind the OS gave it, so the kind is what separates a
/// solver answering something unusable from a solver that is not there.
fn exchange_failure(err: io::Error) -> SmtError {
    let message = err.to_string();
    if err.kind() == io::ErrorKind::Other {
        SmtError::SolverError { message }
    } else {
        SmtError::Process { message }
    }
}

/// Translation from a refinement predicate to an s-expression, plus the constant
/// declarations the result depends on.
///
/// `Context` is borrowed immutably: building s-expressions is pure, and deferring
/// the `declare-const` commands to [`run`] keeps a translation that bails from
/// having sent anything.
struct Encode<'a> {
    ctx: &'a Context,
    /// The scope consulted for each free name met while translating.
    scope: &'a dyn ScopeEnv,
    /// The type the query's subject is refined at. What
    /// [`REFINEMENT_BINDER`](crate::ccl::REFINEMENT_BINDER) is typed by, and so
    /// what a read through it is typed by.
    base: &'a Type,
    /// The path the subject of the predicate being translated addresses. `None`
    /// while translating `lhs`/`rhs`, whose subject is the query's own; `Some(p)`
    /// while translating the refinements carried by the type at `p`, whose subject
    /// is that value.
    subject: Option<Path>,
    /// Leaves encoded so far, keyed by [`Path`] so that one leaf is one SMT
    /// constant across both sides of the query.
    vars: HashMap<Path, SExpr>,
    /// The paths whose types have already been read for assumptions. Separate
    /// from `vars` because a path with no constant of its own still carries
    /// refinements — a product's own predicate reads its fields — and because a
    /// refinement mentioning the value it rides must not send the walk back
    /// through it.
    assumed: HashSet<Path>,
    /// `(symbol, sort)` per entry of `vars`, in declaration order.
    decls: Vec<(String, Sort)>,
    /// `Γ`: what the scope claims about the leaves met so far, in the order they
    /// were met. Collected as translation goes rather than up front, because a
    /// leaf is only known to be part of the query once a predicate reads it.
    assumptions: Vec<SExpr>,
}

impl<'a> Encode<'a> {
    fn new(ctx: &'a Context, scope: &'a dyn ScopeEnv, base: &'a Type) -> Self {
        Encode {
            ctx,
            scope,
            base,
            subject: None,
            vars: HashMap::new(),
            assumed: HashSet::new(),
            decls: Vec::new(),
            assumptions: Vec::new(),
        }
    }

    /// `⋀Γ ∧ ⋀lhs ∧ ¬⋀rhs` — unsatisfiable exactly when the entailment holds.
    fn query(&mut self, lhs: &[Refinement], rhs: &[Refinement]) -> Result<SExpr, SmtError> {
        self.declare_subject(lhs, rhs)?;
        let mut conjuncts = self.conjuncts(lhs)?;
        let goals = self.conjuncts(rhs)?;
        let goal = self.ctx.not(self.ctx.and_many(goals));
        // Gathered after both sides are translated: `Γ` covers a binder first met
        // in the goal as much as one the antecedent mentions.
        conjuncts.append(&mut self.assumptions);
        conjuncts.push(goal);
        Ok(self.ctx.and_many(conjuncts))
    }

    /// Declare the constant the query's subject denotes.
    ///
    /// A scalar base is one constant, declared here so that its sort comes from
    /// the base rather than from whatever a predicate's occurrence of `__elem`
    /// happens to be typed at.
    ///
    /// A product base declares nothing: it has no sort, and a predicate reaches
    /// its scalars by projection, so each such path is declared where it is read
    /// ([`Encode::leaf`]). A base that is neither defeats every predicate about it,
    /// so the first body reports it rather than each one failing on its own mention.
    fn declare_subject(&mut self, lhs: &[Refinement], rhs: &[Refinement]) -> Result<(), SmtError> {
        match self.sort(self.base) {
            Some(sort) => {
                self.declare(Path::subject(), sort);
                Ok(())
            }
            None if matches!(
                self.base.peel_refinements(),
                Type::Record(_) | Type::Tuple(_)
            ) =>
            {
                Ok(())
            }
            None => {
                let body = lhs
                    .first()
                    .or_else(|| rhs.first())
                    .expect("smt_sub queries only a non-empty demand");
                Err(SmtError::Encoding {
                    body: body.clone(),
                    message: format!("the refined base {} has no SMT sort", self.base),
                })
            }
        }
    }

    /// Assume everything the types along `path` claim, prefix by prefix.
    ///
    /// A refinement on a product states its predicate about the product, so the
    /// fact that `x.b` is `3` can be written on `x` (`{{b: Int} | __elem.b == 3}`)
    /// as much as on its `b` field (`{b: Int@3}`). Visiting every prefix and not
    /// the leaf alone is what makes those two spellings one assumption.
    fn assume_along(&mut self, path: &Path) {
        for len in 0..=path.keys.len() {
            let prefix = Path {
                root: path.root.clone(),
                keys: path.keys[..len].to_vec(),
            };
            // Marked before its refinements are translated, so a predicate reading
            // the value it rides terminates rather than re-entering here.
            if !self.assumed.insert(prefix.clone()) {
                continue;
            }
            if let Some(ty) = self.path_type(&prefix) {
                self.assume_refinements(&prefix, &ty);
            }
        }
    }

    /// Record what the type at `path` claims about it: each refinement that type
    /// carries, restated about `path` rather than about the query's subject.
    ///
    /// A refinement predicate is written about the value it rides, so translating
    /// these bodies makes `path` the subject: a bare `__elem` in one of them lands
    /// on the constant just declared, and a read through it lands on a path through
    /// that one. Restoring on the way out is what keeps a nested mention from
    /// leaving this value standing in for the query's subject.
    ///
    /// A body outside the fragment is dropped rather than reported. An assumption
    /// left out only weakens the antecedent, and a query the encoding can
    /// otherwise translate must not fail because of what else is in scope.
    fn assume_refinements(&mut self, path: &Path, ty: &Type) {
        let enclosing = self.subject.replace(path.clone());
        for r in ty.refinements() {
            if let Ok(e) = self.expr(&r.predicate, Some(Sort::Bool)) {
                self.assumptions.push(e);
            }
        }
        self.subject = enclosing;
    }

    /// One s-expression per refinement. [`Encode::expr`] reports the part it
    /// could not translate; this is where the body carrying it is known.
    fn conjuncts(&mut self, refs: &[Refinement]) -> Result<Vec<SExpr>, SmtError> {
        refs.iter()
            .map(|r| {
                self.expr(&r.predicate, Some(Sort::Bool))
                    .map_err(|message| SmtError::Encoding {
                        body: r.clone(),
                        message,
                    })
            })
            .collect()
    }

    /// The SMT sort a Cambra type is encoded at, or `None` outside the fragment.
    ///
    /// The sort a name is declared at carries the constraint pinning it to the
    /// Cambra type, which [`Sort::declare`] asserts: non-negativity for `UInt`,
    /// non-negativity and the upper bound for `UIntRange`.
    ///
    /// An inference variable is resolved for its **shape**, demands included: a
    /// query raised mid-emission reads slots that are still variables, and without
    /// this every such leaf leaves the query unasked. A sort is a representation
    /// choice and not an assumption — it says the leaf is an integer, which the
    /// edge demanding it is what establishes — so reading a demand here does not
    /// let an entailment prove itself from what it was asked to show. What may be
    /// *assumed* about a leaf still comes from the positive reading alone
    /// (`src/ccl/design/type-inference.md`, "The scope a query runs in").
    ///
    /// The resolution runs inside [`with_solver`]'s borrow, so it must raise no
    /// query of its own: the compact → simplify → coalesce pipeline records no
    /// constraints, and a path from it back to [`smt_sub`] would panic on the
    /// re-entrant borrow rather than corrupt the query in flight.
    fn sort(&self, ty: &Type) -> Option<Sort> {
        match ty.peel_refinements() {
            Type::Base(BaseType::Int) => Some(Sort::Int),
            Type::Base(BaseType::UInt) => Some(Sort::UInt),
            Type::UIntRange(n) => Some(Sort::UIntRange(*n)),
            Type::Base(BaseType::Bool) => Some(Sort::Bool),
            Type::Base(BaseType::String) => Some(Sort::Named("String".to_string())),
            Type::History { value, .. } => self.sort(value),
            Type::Infer(_) => match resolve_var_type(ty) {
                // A variable resolving to itself has nothing further to read.
                Ok(Type::Infer(_)) | Err(_) => None,
                Ok(resolved) => self.sort(&resolved),
            },
            _ => None,
        }
    }

    /// A predicate term as an s-expression, or a description of the part with no
    /// encoding. The caller pairs that description with the body it came from.
    ///
    /// `expected` is the sort the position gives the term, which is what a leaf
    /// whose own type settles nothing is declared at
    /// ([`Encode::leaf`]). An operator's operands share a sort, so the one whose
    /// type has a sort supplies it for the other — `x <= 5` declares `x` at `Int`
    /// however little the slot on `x` has resolved to.
    fn expr(&mut self, e: &TypedExpr, expected: Option<Sort>) -> Result<SExpr, String> {
        match &e.node {
            TypedExprNode::Lit(Lit::Int(n)) => Ok(self.numeral(*n)),
            TypedExprNode::Lit(Lit::Bool(b)) => Ok(if *b {
                self.ctx.true_()
            } else {
                self.ctx.false_()
            }),
            // A name, or a field read through one: both address a leaf of the value
            // the root denotes, and the path is what names that leaf. An `Apply`
            // that is not a projection chain addresses no leaf and falls through.
            TypedExprNode::Var(_) | TypedExprNode::Apply { .. } => match Path::of(e) {
                Some(path) => self.leaf(path, &e.ty, expected),
                None => Err(unencodable(e)),
            },
            TypedExprNode::UnaryOp(op, operand) => {
                let inner = match op {
                    // Negation preserves its operand's sort; `not` fixes it.
                    UnaryOpKind::Neg => self.operand_sort(operand, operand).or(expected),
                    UnaryOpKind::Not => Some(Sort::Bool),
                };
                let operand = self.expr(operand, inner)?;
                Ok(match op {
                    UnaryOpKind::Neg => self.ctx.negate(operand),
                    UnaryOpKind::Not => self.ctx.not(operand),
                })
            }
            TypedExprNode::BinOp { left, op, right } => {
                let operands = match op {
                    // Arithmetic is closed over its operands' sort, so the position's
                    // own expectation reaches them; a comparison's does not — it is
                    // `Bool` and its operands are not.
                    BinOpKind::Arithmetic(_) => self.operand_sort(left, right).or(expected.clone()),
                    BinOpKind::Compare(_) => self.operand_sort(left, right),
                    BinOpKind::BoolLogic(_) => Some(Sort::Bool),
                    BinOpKind::Concat => None,
                };
                let l = self.expr(left, operands.clone())?;
                let r = self.expr(right, operands)?;
                self.binop(*op, left, right, l, r)
            }
            _ => Err(unencodable(e)),
        }
    }

    /// The sort two operands share, read off whichever of them has one. A
    /// well-typed operator relates operands of one type, so either answers for
    /// both.
    fn operand_sort(&self, left: &TypedExpr, right: &TypedExpr) -> Option<Sort> {
        self.sort(&left.ty).or_else(|| self.sort(&right.ty))
    }

    fn binop(
        &self,
        op: BinOpKind,
        left: &TypedExpr,
        right: &TypedExpr,
        l: SExpr,
        r: SExpr,
    ) -> Result<SExpr, String> {
        let c = self.ctx;
        Ok(match op {
            // `^+` computes what `+` computes and differs only in the trait it
            // states (`src/ccl/ops.rs`), so both are SMT's `+`; `^*` and `*` are one
            // operation for the same reason.
            BinOpKind::Arithmetic(ArithmeticKind::Add | ArithmeticKind::AddRefined) => c.plus(l, r),
            BinOpKind::Arithmetic(ArithmeticKind::Sub) => c.sub(l, r),
            // A product stays linear when one factor is a constant.
            BinOpKind::Arithmetic(ArithmeticKind::Mul | ArithmeticKind::MulRefined)
                if is_int_literal(left) || is_int_literal(right) =>
            {
                c.times(l, r)
            }
            BinOpKind::Compare(CompareKind::Equals) => c.eq(l, r),
            BinOpKind::Compare(CompareKind::NotEquals) => c.not(c.eq(l, r)),
            BinOpKind::Compare(CompareKind::Less) => c.lt(l, r),
            BinOpKind::Compare(CompareKind::LessOrEq) => c.lte(l, r),
            BinOpKind::Compare(CompareKind::Greater) => c.gt(l, r),
            BinOpKind::Compare(CompareKind::GreaterOrEq) => c.gte(l, r),
            BinOpKind::BoolLogic(LogicKind::And) => c.and(l, r),
            BinOpKind::BoolLogic(LogicKind::Or) => c.or(l, r),
            BinOpKind::BoolLogic(LogicKind::Xor) => c.xor(l, r),
            BinOpKind::BoolLogic(LogicKind::Nand) => c.not(c.and(l, r)),
            BinOpKind::BoolLogic(LogicKind::Nor) => c.not(c.or(l, r)),
            BinOpKind::BoolLogic(LogicKind::Xnor) => c.eq(l, r),
            // Outside the fragment: a product of two unknowns is nonlinear, and
            // SMT-LIB's `div` is Euclidean rather than floor division, so `//`
            // would encode as something else at a negative divisor. `**` is a
            // repeated product, nonlinear for the reason `*` is, and SMT-LIB has
            // no integer exponentiation to state it with. `++` is on strings,
            // which have no sort here.
            BinOpKind::Arithmetic(
                ArithmeticKind::Mul
                | ArithmeticKind::MulRefined
                | ArithmeticKind::FloorDiv
                | ArithmeticKind::Pow,
            )
            | BinOpKind::Concat => {
                return Err(format!(
                    "{} {} {} has no SMT encoding",
                    symbolic(left),
                    op.sym(),
                    symbolic(right)
                ));
            }
        })
    }

    /// SMT-LIB numerals are non-negative, so a negative literal encodes as a
    /// negation applied to its magnitude.
    fn numeral(&self, n: i64) -> SExpr {
        let magnitude = self.ctx.numeral(n.unsigned_abs());
        if n < 0 {
            self.ctx.negate(magnitude)
        } else {
            magnitude
        }
    }

    /// The constant a leaf denotes, minting it on first read.
    ///
    /// The path's own type wins over `ty`, the slot on the term that read it. The
    /// path says what the value is — the subject at `base`, a binder at the type the
    /// scope binds it, a field at the type its product gives it — while the slot
    /// says what the position the read appears in demanded, which mid-emission is
    /// often an unresolved variable. A path type with no sort falls
    /// back to the slot and assumes nothing, on the same footing as a path nothing
    /// settles: declaring the leaf is what the surrounding predicate needs, and the
    /// assumption is the part that can be dropped.
    fn leaf(&mut self, path: Path, ty: &Type, expected: Option<Sort>) -> Result<SExpr, String> {
        let path = self.reroot(path);
        if let Some(e) = self.vars.get(&path) {
            return Ok(*e);
        }
        match self.path_type(&path).and_then(|bound| self.sort(&bound)) {
            Some(sort) => {
                // Declared before the types along the path are read, so a scope
                // whose binders reference each other terminates rather than
                // recurring through this arm.
                let leaf = self.declare(path.clone(), sort);
                self.assume_along(&path);
                Ok(leaf)
            }
            None => {
                let sort = self
                    .sort(ty)
                    .or(expected)
                    .ok_or_else(|| format!("{path} is typed {ty}, which has no SMT sort"))?;
                Ok(self.declare(path, sort))
            }
        }
    }

    /// A path written inside a predicate, rewritten into the frame the query's
    /// constants live in.
    ///
    /// `__elem` addresses the subject of the predicate it appears in, which is the
    /// query's own subject in `lhs`/`rhs` and the value under
    /// [`Encode::assume_refinements`] elsewhere. Splicing the reads onto that
    /// value's path is what makes `__elem.b`, inside the refinement on `x`, the
    /// same leaf as `x.b`.
    fn reroot(&self, path: Path) -> Path {
        match &self.subject {
            Some(subject) if path.rooted_at_subject() => Path {
                root: subject.root.clone(),
                keys: [subject.keys.clone(), path.keys].concat(),
            },
            _ => path,
        }
    }

    /// The type a path denotes: the type its root is bound at, read once per key.
    /// `None` when nothing settles the root, or when a key addresses no field of
    /// what it reads.
    ///
    /// A subject-rooted path reaching here is the *query's* subject —
    /// [`Encode::reroot`] has already replaced any other — so the base is what
    /// types it.
    fn path_type(&self, path: &Path) -> Option<Type> {
        let mut ty = if path.rooted_at_subject() {
            self.base.clone()
        } else {
            self.scope.binder_type(&path.root)?
        };
        // A mutable variable mention in a predicate is a *read*, so what the path
        // denotes is the value the history holds and the facts it carries are that
        // value's. Peeled here rather than in
        // [`Type::refinements`](crate::ccl::Type::refinements), whose contract is one
        // layer at this position — `refined(peel(t), refinements(t)) == t`, which
        // `channelize::join_refinements` rebuilds a type by.
        if let Some(value) = ty.mut_value_type() {
            ty = value.clone();
        }
        for key in &path.keys {
            ty = ty.field(key)?;
        }
        Some(ty)
    }

    /// Assign `path` a fresh constant at `sort`.
    ///
    /// The symbol is positional rather than the path's spelling: a [`Name`]'s
    /// identity is not its spelling (two `Unique`s share a `base`), and a spelling
    /// need not be a legal SMT-LIB symbol.
    fn declare(&mut self, path: Path, sort: Sort) -> SExpr {
        let sym = format!("v!{}", self.decls.len());
        let e = self.ctx.atom(sym.as_str());
        self.decls.push((sym, sort));
        self.vars.insert(path, e);
        e
    }
}

/// The report for a term the encoding does not cover.
fn unencodable(e: &TypedExpr) -> String {
    format!("the term {} has no SMT encoding", symbolic(e))
}

fn is_int_literal(e: &TypedExpr) -> bool {
    match &e.node {
        TypedExprNode::Lit(Lit::Int(_)) => true,
        TypedExprNode::UnaryOp(UnaryOpKind::Neg, operand) => is_int_literal(operand),
        _ => false,
    }
}

/// The per-thread solver subprocess.
enum Slot {
    /// No query has run on this thread yet.
    Unstarted,
    /// Boxed because a `Context` is ~1KB, dwarfing the other variants.
    Ready(Box<Context>),
    /// The failure that broke this thread's solver, returned again by every later
    /// query. Poisoning is permanent: a solver that broke mid-query has an
    /// assertion stack nothing here can account for, and starting a replacement
    /// would hide a misencoding behind a retry.
    Poisoned(SmtError),
}

thread_local! {
    static SOLVER: std::cell::RefCell<Slot> = const { std::cell::RefCell::new(Slot::Unstarted) };
}

/// Run `f` against this thread's solver, starting it on first use.
///
/// A solver that will not start, and an exchange that fails inside `f`, poison the
/// slot: the failure comes back from here and from every later query on the
/// thread.
fn with_solver<T>(f: impl FnOnce(&mut Context) -> Result<T, SmtError>) -> Result<T, SmtError> {
    SOLVER.with_borrow_mut(|slot| {
        if matches!(slot, Slot::Unstarted) {
            *slot = match ContextBuilder::new().with_z3_defaults().build() {
                Ok(ctx) => Slot::Ready(Box::new(ctx)),
                Err(err) => Slot::Poisoned(SmtError::Process {
                    message: err.to_string(),
                }),
            };
        }
        let ctx = match slot {
            Slot::Ready(ctx) => ctx,
            Slot::Poisoned(cause) => return Err(cause.clone()),
            Slot::Unstarted => unreachable!("the block above replaces Unstarted"),
        };
        match f(ctx) {
            // Only a broken exchange poisons: an encoding failure sent nothing,
            // and an `unknown` came back with the query's scope already popped.
            Err(cause @ (SmtError::Process { .. } | SmtError::SolverError { .. })) => {
                *slot = Slot::Poisoned(cause.clone());
                Err(cause)
            }
            result => result,
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ccl::{ArithmeticKind, BinOpKind, CompareKind, TypedExpr};
    use std::rc::Rc;

    fn int() -> Type {
        Type::Base(BaseType::Int)
    }

    /// `__elem <op> rhs` as a refinement over `Int`.
    fn elem_cmp(op: CompareKind, rhs: TypedExpr) -> Refinement {
        Refinement::born(Rc::new(
            TypedExpr::binop(
                TypedExpr::var(Name::elem()).with_ty(int()),
                BinOpKind::Compare(op),
                rhs,
            )
            .with_ty(Type::Base(BaseType::Bool)),
        ))
    }

    fn lit(n: i64) -> TypedExpr {
        TypedExpr::lit(Lit::Int(n)).with_ty(int())
    }

    fn add(l: TypedExpr, r: TypedExpr) -> TypedExpr {
        TypedExpr::binop(l, BinOpKind::Arithmetic(ArithmeticKind::AddRefined), r).with_ty(int())
    }

    /// The case `constrain`'s structural matching cannot decide: two sums that
    /// compare unequal as terms and denote one value.
    #[test]
    fn equal_sums_entail_each_other() {
        let lhs = [elem_cmp(
            CompareKind::Equals,
            add(add(lit(1), lit(3)), lit(2)),
        )];
        let rhs = [elem_cmp(CompareKind::Equals, add(lit(1), lit(5)))];
        assert!(smt_sub(&int(), &lhs, &rhs, &NoScope).unwrap());
        assert!(smt_sub(&int(), &rhs, &lhs, &NoScope).unwrap());
    }

    #[test]
    fn unequal_sums_entail_neither_way() {
        let lhs = [elem_cmp(CompareKind::Equals, add(lit(1), lit(3)))];
        let rhs = [elem_cmp(CompareKind::Equals, add(lit(1), lit(5)))];
        assert!(!smt_sub(&int(), &lhs, &rhs, &NoScope).unwrap());
        assert!(!smt_sub(&int(), &rhs, &lhs, &NoScope).unwrap());
    }

    /// A singleton entails every bound it satisfies, and no bound it violates.
    #[test]
    fn a_singleton_entails_the_bounds_it_satisfies() {
        let five = [elem_cmp(CompareKind::Equals, lit(5))];
        assert!(
            smt_sub(
                &int(),
                &five,
                &[elem_cmp(CompareKind::GreaterOrEq, lit(1))],
                &NoScope
            )
            .unwrap()
        );
        assert!(
            smt_sub(
                &int(),
                &five,
                &[elem_cmp(CompareKind::NotEquals, lit(0))],
                &NoScope
            )
            .unwrap()
        );
        assert!(
            !smt_sub(
                &int(),
                &five,
                &[elem_cmp(CompareKind::Less, lit(1))],
                &NoScope
            )
            .unwrap()
        );
    }

    /// Entailment is over the whole set on each side, conjunctively.
    #[test]
    fn both_sides_are_conjunctions() {
        let bounded = [
            elem_cmp(CompareKind::GreaterOrEq, lit(3)),
            elem_cmp(CompareKind::LessOrEq, lit(4)),
        ];
        let weaker = [
            elem_cmp(CompareKind::NotEquals, lit(0)),
            elem_cmp(CompareKind::Less, lit(10)),
        ];
        assert!(smt_sub(&int(), &bounded, &weaker, &NoScope).unwrap());
        assert!(!smt_sub(&int(), &weaker, &bounded, &NoScope).unwrap());
    }

    /// A free name is universally quantified, so a claim that holds only for some
    /// of its values is not an entailment.
    #[test]
    fn a_free_name_is_universally_quantified() {
        let t = TypedExpr::var(Name::raw("t")).with_ty(int());
        let lhs = [elem_cmp(CompareKind::Equals, add(t.clone(), lit(3)))];
        // `__elem == t + 3` gives `__elem > t`, and gives nothing about `__elem`
        // against a constant.
        assert!(smt_sub(&int(), &lhs, &[elem_cmp(CompareKind::Greater, t)], &NoScope).unwrap());
        assert!(
            !smt_sub(
                &int(),
                &lhs,
                &[elem_cmp(CompareKind::Greater, lit(3))],
                &NoScope
            )
            .unwrap()
        );
    }

    /// The encoder does not typecheck what it sends, so a `String` base under an
    /// integer comparison reaches the solver and comes back as a reply the
    /// exchange cannot use. The claim is the variant — a misencoding on this side
    /// rather than a verdict — and not the solver's wording, which is z3's to
    /// change.
    #[test]
    fn the_solver_will_error_on_type_errors() {
        let refs = [elem_cmp(CompareKind::Equals, lit(5))];
        let err = smt_sub(&Type::Base(BaseType::String), &refs, &refs, &NoScope).unwrap_err();
        assert!(
            matches!(&err, SmtError::SolverError { .. }),
            "expected a SolverError, got: {err:?}"
        );
    }

    /// A term the encoding does not cover bails the whole query, including the
    /// conjuncts around it that would have sufficed on their own, and names the
    /// body it came from rather than the query.
    #[test]
    fn an_unencodable_term_is_not_an_answer() {
        let opaque = TypedExpr::lit(Lit::String("s".into())).with_ty(Type::Base(BaseType::String));
        let lhs = [
            elem_cmp(CompareKind::Equals, lit(5)),
            elem_cmp(CompareKind::Equals, opaque),
        ];
        match smt_sub(
            &int(),
            &lhs,
            &[elem_cmp(CompareKind::GreaterOrEq, lit(1))],
            &NoScope,
        ) {
            Err(SmtError::Encoding { body, .. }) => assert_eq!(body, lhs[1]),
            other => panic!("expected an encoding error: {other:?}"),
        }
    }

    /// An operator outside the fragment reports the term it sits in. `//` is
    /// excluded because SMT-LIB's `div` is Euclidean, not floor division.
    #[test]
    fn an_unencodable_operator_is_not_an_answer() {
        let quotient = TypedExpr::binop(
            TypedExpr::var(Name::raw("t")).with_ty(int()),
            BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
            lit(2),
        )
        .with_ty(int());
        let lhs = [elem_cmp(CompareKind::Equals, quotient)];
        let err = smt_sub(
            &int(),
            &lhs,
            &[elem_cmp(CompareKind::GreaterOrEq, lit(0))],
            &NoScope,
        )
        .unwrap_err();
        assert!(
            matches!(&err, SmtError::Encoding { message, .. } if message.contains("//")),
            "expected the operator reported: {err:?}"
        );
    }

    /// [`reads`] and the encoder agree on the fragment: a term either walk admits
    /// is one the other does too.
    ///
    /// Checked by *running* the encoder rather than by restating its arms, since
    /// restating them is what the two walks already risk drifting on. Each case is
    /// a predicate `__elem == 𝑡` asked against itself, so the only thing that can
    /// fail it is `𝑡`.
    #[test]
    fn a_readable_term_is_what_the_encoder_translates() {
        let name = || TypedExpr::var(Name::raw("t")).with_ty(int());
        let arith = |op| TypedExpr::binop(name(), BinOpKind::Arithmetic(op), lit(2)).with_ty(int());
        let cases: [TypedExpr; 8] = [
            lit(5),
            name(),
            read(name(), "a"),
            arith(ArithmeticKind::Add),
            arith(ArithmeticKind::Mul),
            arith(ArithmeticKind::FloorDiv),
            TypedExpr::unary(UnaryOpKind::Neg, name()).with_ty(int()),
            // An application that is not a projection addresses no leaf.
            TypedExpr::apply(name(), name()).with_ty(int()),
        ];
        for term in cases {
            let rendered = symbolic(&term);
            // The field read needs a product to reach, which only a scope supplies.
            let scope = scoped("t", Type::Record(vec![("a".to_string(), int())]));
            let refs = [elem_cmp(CompareKind::Equals, term)];
            let translated = !matches!(
                smt_sub(&int(), &refs, &refs, &scope),
                Err(SmtError::Encoding { .. })
            );
            assert_eq!(
                reads(&refs[0].predicate),
                translated,
                "`reads` and the encoder disagree on {rendered}"
            );
        }
    }

    /// An encoding failure sends nothing, so it leaves the thread's solver usable
    /// for the next query.
    #[test]
    fn an_encoding_failure_does_not_poison_the_solver() {
        let opaque = TypedExpr::lit(Lit::String("s".into())).with_ty(Type::Base(BaseType::String));
        let unencodable = [elem_cmp(CompareKind::Equals, opaque)];
        assert!(smt_sub(&int(), &unencodable, &unencodable, &NoScope).is_err());

        let five = [elem_cmp(CompareKind::Equals, lit(5))];
        assert!(
            smt_sub(
                &int(),
                &five,
                &[elem_cmp(CompareKind::GreaterOrEq, lit(1))],
                &NoScope
            )
            .unwrap()
        );
    }

    /// Nothing demanded is nothing to prove.
    #[test]
    fn an_empty_demand_holds() {
        assert!(smt_sub(&int(), &[], &[], &NoScope).unwrap());
    }

    /// A scope binding exactly one name.
    struct One(Name, Type);

    impl ScopeEnv for One {
        fn binder_type(&self, name: &Name) -> Option<Type> {
            (self.0 == *name).then(|| self.1.clone())
        }
        fn is_skip_smt(&self) -> bool {
            false
        }
    }

    fn scoped(name: &str, ty: Type) -> One {
        One(Name::raw(name), ty)
    }

    fn var(name: &str) -> TypedExpr {
        TypedExpr::var(Name::raw(name)).with_ty(int())
    }

    /// `Int@n`.
    fn singleton(n: i64) -> Type {
        Type::refined(int(), elem_cmp(CompareKind::Equals, lit(n)).into())
    }

    /// `root.key`, the shape a predicate reading a field has: an `Apply` of a
    /// `Proj` morphism. The root's own slot stays a `Hole` because the encoding
    /// reads the path's type and never that slot; the projection's result slot is
    /// the one it falls back to.
    fn read(root: TypedExpr, key: &str) -> TypedExpr {
        TypedExpr::apply(root, TypedExpr::proj_field(key)).with_ty(int())
    }

    /// `name.key` over a record-typed name.
    fn field(name: &str, key: &str) -> TypedExpr {
        read(TypedExpr::var(Name::raw(name)), key)
    }

    /// `__elem.key` — a read out of the query's subject.
    fn subject_field(key: &str) -> TypedExpr {
        read(TypedExpr::var(Name::elem()), key)
    }

    /// A refinement on a field's type is an assumption about that field:
    /// `__elem == t ^+ x.b` entails `__elem == t + 3` exactly when the scope says
    /// `x`'s `b` is `3`.
    #[test]
    fn a_field_refinement_is_an_assumption() {
        let lhs = [elem_cmp(
            CompareKind::Equals,
            add(var("t"), field("x", "b")),
        )];
        let rhs = [elem_cmp(CompareKind::Equals, add(var("t"), lit(3)))];
        let rec = Type::Record(vec![
            ("a".to_string(), singleton(10)),
            ("b".to_string(), singleton(3)),
        ]);

        assert!(smt_sub(&int(), &lhs, &rhs, &scoped("x", rec)).unwrap());
        // The same query with nothing in scope: `x.b` is universally quantified.
        assert!(!smt_sub(&int(), &lhs, &rhs, &NoScope).unwrap());
    }

    /// One path is one constant, so a predicate relating two reads of it holds
    /// whatever the field is — and a predicate relating it to a constant does not.
    #[test]
    fn two_reads_of_one_path_are_one_constant() {
        let lhs = [elem_cmp(CompareKind::Equals, field("x", "b"))];
        let unrefined = Type::Record(vec![("b".to_string(), int())]);
        let scope = scoped("x", unrefined);
        assert!(
            smt_sub(
                &int(),
                &lhs,
                &[elem_cmp(CompareKind::LessOrEq, field("x", "b"))],
                &scope
            )
            .unwrap()
        );
        assert!(
            !smt_sub(
                &int(),
                &lhs,
                &[elem_cmp(CompareKind::LessOrEq, lit(0))],
                &scope
            )
            .unwrap()
        );
    }

    /// A **product** subject has no constant of its own: the query is about the
    /// leaves a predicate reads out of it, and what the base says about those
    /// leaves is the antecedent. `{x: Int@1, y: Int@0}` refutes `__elem.y != 0`
    /// and establishes `__elem.y == 0`.
    #[test]
    fn a_product_subject_is_read_through_its_fields() {
        let base = Type::Record(vec![
            ("x".to_string(), singleton(1)),
            ("y".to_string(), singleton(0)),
        ]);
        let refutes = [Refinement::born(Rc::new(
            TypedExpr::binop(
                subject_field("y"),
                BinOpKind::Compare(CompareKind::NotEquals),
                lit(0),
            )
            .with_ty(Type::Base(BaseType::Bool)),
        ))];
        let holds = [Refinement::born(Rc::new(
            TypedExpr::binop(
                subject_field("y"),
                BinOpKind::Compare(CompareKind::Equals),
                lit(0),
            )
            .with_ty(Type::Base(BaseType::Bool)),
        ))];
        assert!(!smt_sub(&base, &[], &refutes, &NoScope).unwrap());
        assert!(smt_sub(&base, &[], &holds, &NoScope).unwrap());
    }

    /// A refinement carried by a product states its predicate about that product,
    /// so a read inside it is a read through the binder: `__elem.b == 3` on the
    /// type `x` is bound at is an assumption about `x.b`.
    #[test]
    fn a_read_inside_a_binders_refinement_reroots_onto_the_binder() {
        let refined_rec = Type::refined(
            Type::Record(vec![("b".to_string(), int())]),
            Refinement::born(Rc::new(
                TypedExpr::binop(
                    subject_field("b"),
                    BinOpKind::Compare(CompareKind::Equals),
                    lit(3),
                )
                .with_ty(Type::Base(BaseType::Bool)),
            ))
            .into(),
        );
        let lhs = [elem_cmp(CompareKind::Equals, field("x", "b"))];
        let rhs = [elem_cmp(CompareKind::Equals, lit(3))];
        assert!(smt_sub(&int(), &lhs, &rhs, &scoped("x", refined_rec)).unwrap());
    }

    /// A read no product settles falls back to the slot on the read itself, with
    /// nothing assumed about it — the query is answered rather than reported as
    /// unencodable.
    #[test]
    fn a_read_of_an_unsettled_path_falls_back_to_the_occurrence() {
        let lhs = [elem_cmp(CompareKind::Equals, add(field("x", "b"), lit(1)))];
        let rhs = [elem_cmp(CompareKind::Greater, field("x", "b"))];
        // `x` is bound at a scalar, so `.b` addresses no field of it.
        assert!(smt_sub(&int(), &lhs, &rhs, &scoped("x", int())).unwrap());
        assert!(smt_sub(&int(), &lhs, &rhs, &NoScope).unwrap());
    }

    /// A refinement on the type a name is bound at is an assumption about that
    /// name: `__elem == t ^+ x` entails `__elem == t ^+ 2` exactly when the scope
    /// says `x` is `2`.
    #[test]
    fn a_scope_refinement_is_an_assumption() {
        let lhs = [elem_cmp(CompareKind::Equals, add(var("t"), var("x")))];
        let rhs = [elem_cmp(CompareKind::Equals, add(var("t"), lit(2)))];
        let two = Type::refined(int(), elem_cmp(CompareKind::Equals, lit(2)).into());

        assert!(smt_sub(&int(), &lhs, &rhs, &scoped("x", two)).unwrap());
        // The same query with nothing in scope: `x` is universally quantified.
        assert!(!smt_sub(&int(), &lhs, &rhs, &NoScope).unwrap());
    }

    /// A name the scope binds at a type with no sort is declared at the sort of
    /// the occurrence instead, with nothing assumed about it — the query is still
    /// answered rather than reported as unencodable.
    #[test]
    fn a_scope_type_with_no_sort_falls_back_to_the_occurrence() {
        let lhs = [elem_cmp(CompareKind::Equals, add(var("f"), lit(1)))];
        let rhs = [elem_cmp(CompareKind::Greater, var("f"))];
        let opaque = Type::Fun {
            name: None,
            fun_kind: crate::ccl::ty::FunKind::Compute,
            domain: Box::new(int()),
            codomain: Box::new(int()),
        };
        assert!(smt_sub(&int(), &lhs, &rhs, &scoped("f", opaque)).unwrap());
    }

    /// A binder whose predicate is outside the fragment contributes its constant
    /// and no assumption, rather than defeating the query.
    #[test]
    fn an_unencodable_scope_predicate_is_dropped() {
        // `q : {Int | __elem // 2 == 1}` — `//` has no encoding, so nothing about
        // `q` reaches the solver and `__elem == q` proves only what a free name
        // does.
        let quotient = TypedExpr::binop(
            TypedExpr::var(Name::elem()).with_ty(int()),
            BinOpKind::Arithmetic(ArithmeticKind::FloorDiv),
            lit(2),
        )
        .with_ty(int());
        let unencodable = Type::refined(
            int(),
            Refinement::born(Rc::new(
                TypedExpr::binop(quotient, BinOpKind::Compare(CompareKind::Equals), lit(1))
                    .with_ty(Type::Base(BaseType::Bool)),
            ))
            .into(),
        );
        let lhs = [elem_cmp(CompareKind::Equals, var("q"))];
        let scope = scoped("q", unencodable);
        assert!(
            smt_sub(
                &int(),
                &lhs,
                &[elem_cmp(CompareKind::LessOrEq, var("q"))],
                &scope
            )
            .unwrap()
        );
        assert!(
            !smt_sub(
                &int(),
                &lhs,
                &[elem_cmp(CompareKind::GreaterOrEq, lit(2))],
                &scope
            )
            .unwrap()
        );
    }
}
