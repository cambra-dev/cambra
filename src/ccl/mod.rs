//! Cambra Core Language (CCL) abstract syntax tree.
//!
//! CCL is a λ-calculus–based intermediate representation. Python source is
//! lowered into CCL, where it is type-checked and optimized, then compiled
//! to the dataflow operator graph for execution.
//!
//! See `docs/design-ccl-ast.md` for the full design rationale.

pub mod infer;
pub mod lower;
pub mod pretty;
pub mod symbolic;

use std::{
    cell::RefCell,
    fmt,
    rc::Rc,
    sync::atomic::{AtomicU64, Ordering},
};

/// Global counter for assigning unique IDs to [`Refinement`] instances.
static REFINEMENT_ID_COUNTER: AtomicU64 = AtomicU64::new(0);

pub type RefinementId = u64;

fn next_refinement_id() -> RefinementId {
    REFINEMENT_ID_COUNTER.fetch_add(1, Ordering::Relaxed)
}

// TODO: `BaseType` belongs here (or in a shared module), not in the interpreter.
// Move it to `ccl` and have the interpreter import from `ccl`; this removes the
// upward dependency from `ccl` into `crate::interpreter`. See also `ccl::infer`
// which has the same non-test import.
use crate::interpreter::BaseType;

/// A literal constant value.
///
/// Covers the subset of [`crate::interpreter::Value`] that can appear as
/// compile-time constants.
///
/// Named `Lit` to avoid shadowing `crate::interpreter::Literal`, which is
/// an unrelated operator struct.
#[derive(Debug, Clone, PartialEq)]
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
}

/// Unary operation kinds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnaryOpKind {
    /// Arithmetic negation (`-x`).
    Neg,
    /// Boolean negation (`not x`).
    Not,
}

/// A CCL expression.
///
/// The central type of the CCL AST. Every program is an `Expr`.
///
/// Application is curried: `f(x, y)` is `Apply(Apply(f, x), y)`. Compound
/// expressions may appear inline as arguments — [`Expr::Let`] bindings are
/// optional (unlike strict ANF).
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// A literal constant.
    Lit(Lit),

    /// A variable reference by name.
    Var(String),

    /// Curried function application: `f(x)` written `x ▷ f` in pipeline style.
    ///
    /// Multi-argument calls nest left: `f(x)(y)` becomes
    /// `Apply(Apply(Var("f"), x), y)`.
    ///
    /// Note: `crate::interpreter::Apply` is an unrelated operator struct.
    Apply {
        /// The function being applied.
        function: Box<Expr>,
        /// The argument passed to the function.
        argument: Box<Expr>,
    },

    /// A binary operation.
    BinOp {
        /// The left-hand operand.
        left: Box<Expr>,
        /// The operation kind.
        op: BinOpKind,
        /// The right-hand operand.
        right: Box<Expr>,
    },

    /// A unary operation.
    UnaryOp(UnaryOpKind, Box<Expr>),

    /// An explicit type ascription: `(expr : ty)`.
    ///
    /// Only emitted when a concrete type is known at the annotation site (e.g.
    /// a Python `cast(T, expr)` or an annotated expression outside a binder).
    /// Annotations on binders are carried directly by [`Expr::Let`] and
    /// [`Expr::Lambda`] instead.
    TypeAnnotation(Box<Expr>, Type),

    /// A lambda abstraction.
    ///
    /// `param_ty` may be `None` when unannotated; the type checker fills it
    /// in. Wrapping a lambda in [`Expr::Let`] gives it a name and a natural
    /// annotation site for bidirectional type checking.
    ///
    /// Note: `crate::interpreter::Lambda` is an unrelated operator struct.
    Lambda {
        /// The bound parameter name.
        param: String,
        /// The parameter's type, if known.
        ///
        /// `None` on unannotated lambdas from lowering; filled in by
        /// [`infer::infer`] before compilation. User-written ascriptions on
        /// arbitrary expressions use [`Expr::TypeAnnotation`] instead.
        /// See the `TypedExpr` TODO in [`infer`](crate::ccl::infer).
        param_ty: Option<Type>,
        /// The lambda body.
        body: Box<Expr>,
        /// Refinement on the param type computed by this lambda.
        /// This is a separate field from param_ty because it can be set before the
        /// type is known, and the presence of this field indicates that the refinement
        /// should be interpreted in the scope of this lambda.
        refinement: Option<Refinement>,
    },

    /// A let binding: `let name [: ty] = value in body`.
    ///
    /// Binds `name` to `value` within `body`. Unlike strict ANF, `value`
    /// may be any `Expr`, not only an atomic term.
    Let {
        /// The name being bound.
        name: String,
        /// The type of the bound value, if known.
        ///
        /// `None` when unannotated; filled in by [`infer::infer`] before
        /// compilation. User-written ascriptions on arbitrary expressions use
        /// [`Expr::TypeAnnotation`] instead. See the `TypedExpr` TODO in [`infer`].
        bound_ty: Option<Type>,
        /// The expression being bound.
        bound_expr: Box<Expr>,
        /// The expression in which `name` is in scope.
        body: Box<Expr>,
    },

    /// A list literal: `[e0, e1, ...]`.
    ///
    /// Represents Python list syntax directly in the CCL tree. Elements may be
    /// arbitrary expressions (not restricted to [`Lit`]).
    ///
    /// Distinct from [`Expr::Tuple`] (unnamed product type) and from the
    /// function-encoding of lists used at the operator-graph level.
    List(Vec<Expr>),

    /// Multi-way pattern matching.
    ///
    /// Evaluates `scrutinee` and tests each `(pattern, arm)` pair in order,
    /// binding matched sub-terms in scope for the arm expression.
    ///
    /// Python `if`/`elif`/`else` chains are lowered to `Case` during
    /// Python → CCL lowering; there is no separate `IfThenElse` node.
    Case {
        /// The expression being matched.
        scrutinee: Box<Expr>,
        /// Ordered list of pattern–arm pairs. Evaluated top-to-bottom; the
        /// first matching pattern wins.
        branches: Vec<(Pattern, Expr)>,
    },

    /// A loop join point.
    ///
    /// Defines a named, parameterized loop header. `outer_body` is evaluated
    /// first and must contain the initial [`Expr::Jump`] that enters the loop.
    /// The loop body (`loop_body`) runs on each iteration; it may
    /// [`Expr::Jump`] back to this point with updated parameter values, or
    /// fall through to produce the loop's final value.
    ///
    /// Join points are non-escaping: they cannot be stored in variables or
    /// passed as arguments. All jumps to this point must be tail calls within
    /// `loop_body`.
    ///
    /// Compiles to iterate/feedback operators in the dataflow graph.
    Join {
        /// The join point's label, referenced by [`Expr::Jump`].
        name: String,
        /// The loop variables with optional type annotations.
        params: Vec<(String, Option<Type>)>,
        /// The loop body; evaluated on each iteration. May contain a
        /// [`Expr::Jump`] back to this join point.
        loop_body: Box<Expr>,
        /// Evaluated first; must contain the initial [`Expr::Jump`] into this
        /// join point.
        outer_body: Box<Expr>,
    },

    /// A tail call to a [`Expr::Join`] point.
    ///
    /// Transfers control to the named join point, passing `args` as updated
    /// values for its parameters (in declaration order). Must appear in tail
    /// position within the enclosing [`Expr::Join`] body.
    Jump {
        /// Name of the target [`Expr::Join`].
        target: String,
        /// Updated values for the join point's parameters, in order.
        args: Vec<Expr>,
    },

    /// A tuple constructor: `(e0, e1, ...)`.
    ///
    /// Compiles to a [`crate::interpreter::ConstructRecord`] with fields
    /// named `_0`, `_1`, … (via [`crate::interpreter::tuple_field`]).
    Tuple(Vec<Expr>),

    /// Integer-index access into a tuple: `t[n]`.
    ///
    /// Compiles to a [`crate::interpreter::RecordField`] with field name `_n`.
    TupleIndex(Box<Expr>, usize),

    /// A record constructor. Lowering from Python syntax is not yet implemented.
    Record(Vec<(String, Expr)>),
}

impl Expr {
    pub fn apply(argument: Expr, function: Expr) -> Self {
        Expr::Apply {
            argument: Box::new(argument),
            function: Box::new(function),
        }
    }

    pub fn lambda(param: &str, param_ty: Option<Type>, body: Expr) -> Self {
        Expr::Lambda {
            param: param.to_string(),
            param_ty,
            body: Box::new(body),
            refinement: None,
        }
    }

    pub fn lambda_with_refinement(
        param: &str,
        param_ty: Option<Type>,
        body: Expr,
        refinement: Expr,
        refinement_desc: &str,
    ) -> Self {
        Expr::Lambda {
            param: param.to_string(),
            param_ty,
            body: Box::new(body),
            refinement: Some(Refinement {
                id: next_refinement_id(),
                description: refinement_desc.to_string(),
                kind: RefinementKind::Predicate(Rc::new(RefCell::new(refinement))),
            }),
        }
    }

    /// Build a [`Expr::Lambda`] with a hash-join [`Refinement`].
    pub fn lambda_with_hash_join(
        param: &str,
        param_ty: Option<Type>,
        body: Expr,
        spec: HashJoinSpec,
        desc: &str,
    ) -> Self {
        Expr::Lambda {
            param: param.to_string(),
            param_ty,
            body: Box::new(body),
            refinement: Some(Refinement {
                id: next_refinement_id(),
                description: desc.to_string(),
                kind: RefinementKind::HashJoin(Box::new(spec)),
            }),
        }
    }
}

/// A pattern in a [`Expr::Case`] branch.
///
/// Patterns are tested against the scrutinee. The first branch whose pattern
/// matches wins, and any [`Pattern::Var`] sub-patterns in it are bound in
/// scope for the corresponding arm expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    /// Match a specific literal value.
    Lit(Lit),
    /// Bind the matched value to a name in the arm.
    Var(String),
    /// Destructure a tuple, matching and binding each element in order.
    Tuple(Vec<Pattern>),
    /// Destructure a record by field name, matching each named field.
    Record(Vec<(String, Pattern)>),
    /// Match any value without binding.
    Wildcard,
}

/// A CCL type annotation.
///
/// Appears on [`Expr::Let`] and [`Expr::Lambda`] nodes and as the output of
/// type inference. [`Type::Unknown`] is the placeholder used before
/// type-checking; it has no runtime equivalent and must be fully resolved
/// before operator-graph compilation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// A primitive base type.
    Base(BaseType),
    /// A finite index range `[0, n)`, used as the domain of list types.
    ///
    /// Emitted by `lower_list_comp` to annotate the outer lambda's parameter
    /// with the exact length of the source list. `compile_ccl::extent_of` maps
    /// it directly to `Extent::UIntRange { start: 0, end: n }`.
    UIntRange(usize),
    /// A non-dependent function type: `T ⇒ U`.
    Fun(Box<Type>, Box<Type>),
    /// An ordered product type with unnamed fields (tuple).
    Tuple(Vec<Type>),
    /// A named product type (record).
    Record(Vec<(String, Type)>),
    /// A sum type.
    Union(Vec<Type>),
    /// A refinement of another type
    Refinement(Box<Type>, Refinement),
    /// Pre-type-checking placeholder; filled in by the type checker.
    Unknown,
    // Planned:
    // Pi { param: String, param_ty: Box<Type>, body_ty: Box<Type> }
    // Refinement { base: Box<Type>, predicate: Box<Expr> }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Base(b) => write!(
                f,
                "{}",
                match b {
                    BaseType::Int => "Int",
                    BaseType::UInt => "UInt",
                    BaseType::String => "String",
                    BaseType::Bool => "Bool",
                    BaseType::Unit => "Unit",
                }
            ),
            Type::UIntRange(n) => write!(f, "[0, {n})"),
            Type::Fun(a, b) => write!(f, "{a} ⇒ {b}"),
            Type::Tuple(ts) => {
                let parts: Vec<_> = ts.iter().map(|t| t.to_string()).collect();
                write!(f, "({})", parts.join(", "))
            }
            Type::Record(fields) => {
                let parts: Vec<_> = fields.iter().map(|(n, t)| format!("{n}: {t}")).collect();
                write!(f, "{{{}}}", parts.join(", "))
            }
            Type::Union(ts) => {
                let parts: Vec<_> = ts.iter().map(|t| t.to_string()).collect();
                write!(f, "{}", parts.join(" | "))
            }
            Type::Refinement(t, r) => write!(f, "{{{t} | Refined({})}}", r.description),
            Type::Unknown => write!(f, "_"),
        }
    }
}

/// Represents a type refinement carried by a [`Expr::Lambda`] parameter.
#[derive(Debug, Clone)]
pub struct Refinement {
    /// Unique ID assigned at construction time.
    ///
    /// Used by [`crate::interpreter::compile_ccl::CompileContext`] as a cache key
    /// so that the same restriction [`crate::interpreter::Extent`] is shared across
    /// all uses of the same refinement.
    pub id: RefinementId,
    /// Human-readable description of the predicate or join condition.
    pub description: String,
    /// Whether this refinement is a loop-join predicate or a hash join.
    pub kind: RefinementKind,
}

impl PartialEq for Refinement {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Refinement {}

/// Distinguishes loop-join (predicate) refinements from hash-join refinements and carries join strategy metadata.
#[derive(Debug, Clone, PartialEq)]
pub enum RefinementKind {
    /// Arbitrary boolean predicate; compiled as an element-wise loop join.
    Predicate(Rc<RefCell<Expr>>),
    /// Equality join between two generator key expressions; compiled as a hash join.
    HashJoin(Box<HashJoinSpec>),
}

/// All data needed by [`crate::interpreter::compile_ccl`] to build a hash-join
/// [`crate::interpreter::ComputeRestriction`].
#[derive(Debug, Clone)]
pub struct HashJoinSpec {
    /// Position of the generator for the build side in the original list comp (always the earlier generator for now).
    pub build_gen_position: usize,
    /// Position of the generator for the build side in the original list com
    pub probe_gen_position: usize,
    /// Name of the build-side iterator variable (e.g. `"x"`).
    pub build_var_name: String,
    /// Name of the probe-side iterator variable (e.g. `"y"`).
    pub probe_var_name: String,
    /// CCL expression for the build-side join key; references `build_var_name` as a free variable.
    pub build_key: Rc<Expr>,
    /// CCL expression for the probe-side join key; references `probe_var_name` as a free variable.
    pub probe_key: Rc<Expr>,
    /// CCL expression for the build-side source list (no free generator variables).
    pub build_source: Rc<Expr>,
    /// CCL expression for the probe-side source list (no free generator variables).
    pub probe_source: Rc<Expr>,
}

impl PartialEq for HashJoinSpec {
    fn eq(&self, other: &Self) -> bool {
        self.build_gen_position == other.build_gen_position
            && self.probe_gen_position == other.probe_gen_position
            && self.build_var_name == other.build_var_name
            && self.probe_var_name == other.probe_var_name
            && Rc::ptr_eq(&self.build_key, &other.build_key)
            && Rc::ptr_eq(&self.probe_key, &other.probe_key)
            && Rc::ptr_eq(&self.build_source, &other.build_source)
            && Rc::ptr_eq(&self.probe_source, &other.probe_source)
    }
}
