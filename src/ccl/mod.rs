//! Cambra Core Language (CCL) abstract syntax tree.
//!
//! CCL is a λ-calculus–based intermediate representation. Python source is
//! lowered into CCL, where it is type-checked and optimized, then compiled
//! to the dataflow operator graph for execution.
//!
//! See `docs/design-ccl-ast.md` for the full design rationale.

pub mod lower;
pub mod pretty;
pub mod symbolic;

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

/// Binary operation kinds, using the same nested structure as
/// `crate::interpreter::BinOpKind`. Future unification into a shared module
/// will be a pure relocation with no rename or restructure work.
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
        /// Optional type annotation for the parameter.
        param_ty: Option<Type>,
        /// The lambda body.
        body: Box<Expr>,
    },

    /// A let binding: `let name [: ty] = value in body`.
    ///
    /// Binds `name` to `value` within `body`. Unlike strict ANF, `value`
    /// may be any `Expr`, not only an atomic term.
    Let {
        /// The name being bound.
        name: String,
        /// Optional type annotation for the bound value.
        ty: Option<Type>,
        /// The expression being bound.
        value: Box<Expr>,
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

    /// A tuple constructor. Lowering from Python syntax is not yet implemented.
    Tuple(Vec<Expr>),

    /// A record constructor. Lowering from Python syntax is not yet implemented.
    Record(Vec<(String, Expr)>),
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
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    /// A primitive base type.
    Base(BaseType),
    /// A non-dependent function type: `T ⇒ U`.
    Fun(Box<Type>, Box<Type>),
    /// An ordered product type with unnamed fields (tuple).
    Tuple(Vec<Type>),
    /// A named product type (record).
    Record(Vec<(String, Type)>),
    /// A sum type.
    Union(Vec<Type>),
    /// Pre-type-checking placeholder; filled in by the type checker.
    Unknown,
    // Planned:
    // Pi { param: String, param_ty: Box<Type>, body_ty: Box<Type> }
    // Refinement { base: Box<Type>, predicate: Box<Expr> }
}
