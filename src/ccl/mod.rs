//! Cambra Core Language (CCL) abstract syntax tree.
//!
//! CCL is a λ-calculus–based intermediate representation. Python source is
//! lowered into CCL, where it is type-checked and optimized, then compiled
//! to the dataflow operator graph for execution.
//!
//! See `docs/design-ccl-ast.md` for the full design rationale.

pub mod context;
pub mod infer;
pub mod join_plan;
pub mod lambda_elim;
pub mod lower;
pub mod pretty;
pub mod simplify;
pub mod symbolic;
pub mod unify;

use std::{
    cell::RefCell,
    fmt,
    rc::Rc,
    sync::atomic::{AtomicU32, AtomicU64, Ordering},
};

use smol_str::SmolStr;

/// Global counter for assigning unique IDs to [`Refinement`] instances.
static REFINEMENT_ID_COUNTER: AtomicU64 = AtomicU64::new(0);

pub type RefinementId = u64;

pub fn next_refinement_id() -> RefinementId {
    REFINEMENT_ID_COUNTER.fetch_add(1, Ordering::Relaxed)
}

/// A unique identifier for an inference type variable.
///
/// Every [`Type::Infer`] carries one of these, assigned monotonically by
/// [`fresh_infer_var_id`]. Uniqueness is global across the process so that
/// variables created in different parts of the tree never alias.
///
/// The inner `u32` is `pub(crate)` to prevent external code from constructing
/// arbitrary `InferVarId` values. Use [`Type::infer`] or
/// [`crate::ccl::infer::TypeInferenceContext::fresh_infer_var`] instead.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InferVarId(pub(crate) u32);

impl fmt::Display for InferVarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Global counter for [`InferVarId`] allocation.
static INFER_VAR_COUNTER: AtomicU32 = AtomicU32::new(0);

/// Allocate a fresh, globally-unique [`InferVarId`].
///
/// Called only by [`Type::infer`] (test helper) and
/// [`crate::ccl::infer::TypeInferenceContext::fresh_infer_var`]
/// (which also registers the variable in the
/// [`crate::ccl::unify::UnificationTable`]).
fn fresh_infer_var_id() -> InferVarId {
    InferVarId(INFER_VAR_COUNTER.fetch_add(1, Ordering::Relaxed))
}

/// Reset the inference variable counter to zero.
///
/// For use in tests that need predictable `InferVarId` values in output.
/// Not safe to call concurrently — run such tests with `--test-threads=1`
/// or use `serial_test` if order matters.
#[cfg(test)]
pub fn reset_infer_var_counter() {
    INFER_VAR_COUNTER.store(0, Ordering::Relaxed);
}

use crate::interpreter::{ColumnValue, Extent};

/// Primitive base types shared between the CCL type system and the interpreter.
///
/// Defined here (in `ccl`) and re-exported by the interpreter so that
/// `ccl` does not depend upward on `interpreter`. See `interpreter/types.rs`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

/// The key identifying which field a [`TypedExprNode::Proj`] projects.
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

/// Types of aggregations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AggregateKind {
    Sum,
    Max,
}

impl AggregateKind {
    /// Returns the output type of this aggregation given a specific input type.
    /// If `input_type` is not a valid input type for this aggregation, returns None.
    pub fn output_type(&self, input_type: &Type) -> Option<Type> {
        match (self, input_type) {
            (AggregateKind::Sum, Type::Base(BaseType::Int)) => Some(Type::Base(BaseType::Int)),
            (AggregateKind::Max, Type::Base(b)) => Some(Type::Base(b.clone())),
            _ => None,
        }
    }

    pub fn output_extent(&self, input_extent: &Extent) -> Option<Extent> {
        match (self, input_extent) {
            (AggregateKind::Sum, Extent::Base(BaseType::Int)) => Some(Extent::Base(BaseType::Int)),
            (AggregateKind::Max, Extent::Base(b)) => Some(Extent::Base(b.clone())),
            _ => None,
        }
    }

    /// Returns the identity element for this aggregation over the given accumulator extent.
    ///
    /// Used to seed the [`Tile::Aggregation`](crate::interpreter::tiling::Tile::Aggregation)
    /// accumulator before the first batch of values arrives.
    pub fn initial_accumulator(&self, accumulator_extent: &Extent) -> ColumnValue {
        match (self, accumulator_extent) {
            (AggregateKind::Sum, Extent::Base(BaseType::Int)) => ColumnValue::Ints(vec![0]),
            (AggregateKind::Max, Extent::Base(BaseType::Int)) => ColumnValue::Ints(vec![i64::MIN]),
            (AggregateKind::Max, Extent::Base(BaseType::UInt)) => ColumnValue::UInts(vec![0]),
            (AggregateKind::Max, Extent::Base(BaseType::String)) => {
                ColumnValue::Strings(vec![SmolStr::default()])
            }
            _ => panic!("No identity for {self:?} over {accumulator_extent:?}"),
        }
    }

    /// Fold `values[start..end]` into `accumulator` in place.
    ///
    /// `accumulator` holds the running state (a single-element `ColumnValue`);
    /// `values` is the source column and `start..end` is the slice of elements
    /// to incorporate.  Passing `0..values.len()` incorporates the whole column.
    pub fn accumulate(
        &self,
        accumulator: &mut ColumnValue,
        values: &ColumnValue,
        start: usize,
        end: usize,
    ) {
        match (self, accumulator, values) {
            (AggregateKind::Sum, ColumnValue::Ints(ref mut acc), ColumnValue::Ints(vs)) => {
                acc[0] += vs[start..end].iter().sum::<i64>()
            }
            (AggregateKind::Max, ColumnValue::Ints(ref mut acc), ColumnValue::Ints(vs)) => {
                accumulate_max(acc, &vs[start..end]);
            }
            (AggregateKind::Max, ColumnValue::UInts(ref mut acc), ColumnValue::UInts(vs)) => {
                accumulate_max(acc, &vs[start..end]);
            }
            (AggregateKind::Max, ColumnValue::Strings(ref mut acc), ColumnValue::Strings(vs)) => {
                accumulate_max(acc, &vs[start..end]);
            }
            _ => panic!("Invalid accumulate"),
        };
    }

    /// Convert accumulator state into output state.
    /// Currently, we only have aggregates where the extracted state is equal to the accumulators.
    pub fn extract(&self, accumulator: ColumnValue) -> ColumnValue {
        match (self, &accumulator) {
            (AggregateKind::Sum, ColumnValue::Ints(_))
            | (AggregateKind::Max, ColumnValue::Ints(_))
            | (AggregateKind::Max, ColumnValue::UInts(_))
            | (AggregateKind::Max, ColumnValue::Strings(_)) => accumulator,
            _ => panic!("Invalid accumulate"),
        }
    }
}

fn accumulate_max<T: Ord + Clone>(acc: &mut [T], values: &[T]) {
    let max = values.iter().max().cloned();
    if let Some(max) = max {
        if max > acc[0] {
            acc[0] = max;
        }
    }
}

/// A typed binding site: a named variable together with its type.
///
/// Used in [`TypedExprNode::Lambda`], [`TypedExprNode::Join`], and [`TypedExprNode::Let`] to carry
/// both the inferred type and any user-written annotation at each binding site.
///
/// `ty` starts as [`Type::Hole`] (lowering placeholder) and is converted to a
/// registered [`Type::Infer`] variable at inference entry, then filled in with
/// the concrete type by [`infer::infer`].
/// `user_annotation` is set at construction time by lowering when the source
/// Python carries an explicit type cast; the inference pass checks that the
/// inferred type is compatible with it.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedBinding {
    /// The bound variable name.
    pub name: String,
    /// The variable's type, filled in by type inference.
    ///
    /// Starts as [`Type::Hole`] (lowering placeholder); converted to [`Type::Infer`]
    /// at inference entry and written to a concrete type by [`infer::infer`].
    pub ty: Type,
    /// User-written type annotation, if any.
    ///
    /// Set by lowering when the source Python carries an explicit type annotation
    /// (e.g. `x: int = expr`). The inference pass checks that the inferred type is
    /// compatible with it and raises [`infer::InferError::AnnotationMismatch`] on conflict.
    pub user_annotation: Option<Type>,
}

impl TypedBinding {
    /// Create an unannotated binding with a [`Type::Hole`] placeholder.
    ///
    /// Use this at lowering time when no type is yet known. The inference pass
    /// converts the `Hole` to a registered inference variable before type-checking.
    pub fn new_unannotated(name: &str) -> Self {
        TypedBinding {
            name: name.to_string(),
            ty: Type::Hole,
            user_annotation: None,
        }
    }

    /// Create an annotated binding with a [`Type::Hole`] placeholder and a user annotation.
    ///
    /// Use this at lowering time when the source Python carries an explicit type annotation
    /// (e.g. `x: int = expr`). `ty` is still [`Type::Hole`] — the inference pass fills it in.
    pub fn new_annotated(name: impl Into<String>, annotation: Type) -> Self {
        TypedBinding {
            name: name.into(),
            ty: Type::Hole,
            user_annotation: Some(annotation),
        }
    }
}

/// The expression kind enum for CCL expressions.
///
/// This is the central type of the CCL AST node hierarchy. Every program is a [`TypedExpr`]
/// whose `node` field holds one of these variants.
///
/// Application is curried: `f(x, y)` is `Apply(Apply(f, x), y)`. Compound
/// expressions may appear inline as arguments — [`TypedExprNode::Let`] bindings are
/// optional (unlike strict ANF).
#[derive(Debug, Clone, PartialEq)]
pub enum TypedExprNode {
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
        function: Box<TypedExpr>,
        /// The argument passed to the function.
        argument: Box<TypedExpr>,
    },

    /// A binary operation.
    BinOp {
        /// The left-hand operand.
        left: Box<TypedExpr>,
        /// The operation kind.
        op: BinOpKind,
        /// The right-hand operand.
        right: Box<TypedExpr>,
    },

    /// A unary operation.
    UnaryOp(UnaryOpKind, Box<TypedExpr>),

    /// A lambda abstraction.
    ///
    /// The bound parameter and its type are carried by a [`TypedBinding`].
    /// `param.ty` starts as [`Type::Hole`] on unannotated lambdas from
    /// lowering; [`infer::infer`] converts each `Hole` to a registered
    /// [`Type::Infer`] variable and resolves it before compilation.
    ///
    /// Note: `crate::interpreter::Lambda` is an unrelated operator struct.
    Lambda {
        /// The bound parameter, with its name and inferred/annotated type.
        param: TypedBinding,
        /// The lambda body.
        body: Box<TypedExpr>,
        /// Refinement on the param type computed by this lambda.
        ///
        /// This is a separate field from `param.ty` because it can be set
        /// before the type is known, and its presence indicates that the
        /// refinement should be interpreted in the scope of this lambda.
        refinement: Option<Refinement>,
    },

    /// An aggregation over a function (including, and usually being, a collection)
    /// Computes the aggregate over the codomain of the function, which in the case of
    /// a collection is the elements of the collection.
    Aggregate {
        /// Expression being aggregated over.  Must be of type `Fun`
        input: Box<TypedExpr>,
        /// The type of aggregation to do (e.g. sum, max)
        kind: AggregateKind,
    },

    /// A let binding: `let name = value in body`.
    ///
    /// Binds `name` to `value` within `body`. Unlike strict ANF, `value`
    /// may be any `TypedExpr`, not only an atomic term.
    Let {
        /// The bound name and its type.
        ///
        /// `binding.ty` mirrors `bound_expr.ty` after inference and is filled
        /// in by [`infer::infer`]. `binding.user_annotation` carries any
        /// user-written type annotation on the binding site (e.g. `x: Int = expr`),
        /// which inference checks for compatibility with the inferred expression type.
        binding: TypedBinding,
        /// The expression being bound.
        bound_expr: Box<TypedExpr>,
        /// The expression in which `binding.name` is in scope.
        body: Box<TypedExpr>,
    },

    /// A list literal: `[e0, e1, ...]`.
    ///
    /// Represents Python list syntax directly in the CCL tree. Elements may be
    /// arbitrary expressions (not restricted to [`Lit`]).
    ///
    /// Distinct from [`TypedExprNode::Tuple`] (unnamed product type) and from the
    /// function-encoding of lists used at the operator-graph level.
    List(Vec<TypedExpr>),

    /// Multi-way conditional branching.
    ///
    /// Evaluates each [`Branch`] in order; the first branch whose guard evaluates
    /// to `true` wins. Guards must have type [`Type::Base(BaseType::Bool)`].
    ///
    /// `if`/`elif`/`else` chains are flattened into a single `Case` with one
    /// [`Branch`] per condition. Ternary `if` expressions produce a 2-branch
    /// `Case`. Python `match` statement lowering (planned) will desugar patterns
    /// into guards and [`TypedExprNode::Let`] bindings before producing `Case`.
    ///
    /// NOTE: All arms must currently infer the **same** type. Mismatched arm types
    /// are a hard [`crate::ccl::infer::InferError::TypeMismatch`] rather than
    /// producing a [`Type::Union`].
    Case {
        /// Ordered list of branches. Evaluated top-to-bottom; the first branch
        /// whose guard is `true` wins.
        branches: Vec<Branch>,
    },

    /// A loop join point.
    ///
    /// Defines a named, parameterized loop header. `outer_body` is evaluated
    /// first and must contain the initial [`TypedExprNode::Jump`] that enters the loop.
    /// The loop body (`loop_body`) runs on each iteration; it may
    /// [`TypedExprNode::Jump`] back to this point with updated parameter values, or
    /// fall through to produce the loop's final value.
    ///
    /// Join points are non-escaping: they cannot be stored in variables or
    /// passed as arguments. All jumps to this point must be tail calls within
    /// `loop_body`.
    ///
    /// Compiles to iterate/feedback operators in the dataflow graph.
    Join {
        /// The join point's label, referenced by [`TypedExprNode::Jump`].
        name: String,
        /// The loop variables with their names and inferred/annotated types.
        params: Vec<TypedBinding>,
        /// The loop body; evaluated on each iteration. May contain a
        /// [`TypedExprNode::Jump`] back to this join point.
        loop_body: Box<TypedExpr>,
        /// Evaluated first; must contain the initial [`TypedExprNode::Jump`] into this
        /// join point.
        outer_body: Box<TypedExpr>,
    },

    /// A tail call to a [`TypedExprNode::Join`] point.
    ///
    /// Transfers control to the named join point, passing `args` as updated
    /// values for its parameters (in declaration order). Must appear in tail
    /// position within the enclosing [`TypedExprNode::Join`] body.
    Jump {
        /// Name of the target [`TypedExprNode::Join`].
        target: String,
        /// Updated values for the join point's parameters, in order.
        args: Vec<TypedExpr>,
    },

    /// A tuple constructor: `(e0, e1, ...)`.
    ///
    /// Compiles to a [`crate::interpreter::ConstructRecord`] with fields
    /// named `_0`, `_1`, … (via [`crate::interpreter::tuple_field`]).
    Tuple(Vec<TypedExpr>),

    /// A first-class projection morphism `.n` (tuple) or `.name` (record).
    ///
    /// `Proj(k)` represents the morphism `λ t → t.k` in point-free form.
    /// Tuple index access `t[n]` is lowered as `Apply(Proj(Index(n)), t)`.
    /// Introduced by lowering; absent in the higher-level design.
    Proj(ProjKey),

    /// A record constructor. Lowering from Python syntax is not yet implemented.
    Record(Vec<(String, TypedExpr)>),

    /// A grouping operation over a collection by a key extraction function.
    ///
    /// TODO this is temporary.  We should instead be representing grouping
    /// purely with refinements and letting the optimizer insert Converse operations
    /// as needed to efficiently compute those refinements.
    ///
    /// `groupby(collection, key)` partitions `collection` into groups, where
    /// each element is assigned to the group identified by applying `key` to it.
    ///
    /// - `collection` is the data source (a function from index to element, i.e.
    ///   the standard CCL list-as-function encoding).
    /// - `key` is a function that extracts the grouping key from each element.
    ///
    /// The result type is `Fun(key_output_ty, Fun(Base(UInt), elem_ty))`
    GroupBy {
        /// The collection (function) whose elements are to be grouped.
        collection: Box<TypedExpr>,
        /// A function that computes the grouping key for each element.
        key: Box<TypedExpr>,
    },

    /// A reference to an externally-registered data source, identified by name.
    ///
    /// Emitted by [`crate::ccl::lower`] when a zero-argument call is recognised
    /// as a registered source (e.g. `testsource1()` or `__stdinvalues()`).
    /// [`crate::ccl::infer`] resolves it to a `Fun(DataSource(name), output_type)`
    /// via the source registry; [`crate::interpreter::compile_ccl`] compiles it to
    /// the appropriate reader operator.
    Source(String),

    /// N-ary point-free function composition: `f₀ ≫ f₁ ≫ … ≫ fₙ₋₁`.
    ///
    /// Introduced by [`crate::ccl::lambda_elim`]; always contains at least
    /// two morphisms. [`crate::ccl::simplify`] flattens nested two-element
    /// `Compose` nodes into longer chains.
    ///
    /// Semantics: element `i` is applied before element `i+1`, so
    /// `Compose([f, g])` means "apply `f`, then pipe the result to `g`".
    Compose(Vec<TypedExpr>),
}

/// A CCL expression with a type slot on every node.
///
/// Every node starts with `ty: Type::Hole`; the inference pass
/// ([`infer::infer`]) converts it to a registered [`Type::Infer`] variable,
/// then fills it with the concrete type before compilation.
///
/// `user_annotation` carries an explicit type annotation written by the user
/// (e.g. from a Python `cast(T, expr)` or an annotated binding site). The
/// inference pass checks that the inferred type is compatible with it.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedExpr {
    /// The inferred type of this expression.
    ///
    /// Starts as [`Type::Hole`] (lowering placeholder); converted to [`Type::Infer`]
    /// at inference entry and written to a concrete type by [`infer::infer`].
    pub ty: Type,
    /// The expression kind.
    pub node: TypedExprNode,
    /// User-written type annotation, if any.
    ///
    /// Checked against the inferred type by [`infer::infer`]; `None` for all
    /// nodes produced by the current lowering pass.
    pub user_annotation: Option<Type>,
}

/// Type alias for backward compatibility. `Expr` is now [`TypedExpr`].
pub type Expr = TypedExpr;

impl TypedExpr {
    /// Construct a new [`TypedExpr`] with a [`Type::Hole`] placeholder and no user annotation.
    ///
    /// `Hole` is the lowering-phase placeholder. The inference pass converts it to a
    /// registered [`Type::Infer`] variable before type-checking begins.
    pub fn new(node: TypedExprNode) -> Self {
        TypedExpr {
            node,
            ty: Type::Hole,
            user_annotation: None,
        }
    }

    /// Set the inferred type on this expression, consuming and returning it.
    ///
    /// Used to pre-fill the type in tests or when the type is known at construction time.
    pub fn with_ty(self, ty: Type) -> Self {
        TypedExpr { ty, ..self }
    }

    /// Set the user annotation on this expression, consuming and returning it.
    ///
    /// Used to attach a user-written type annotation in tests.
    pub fn with_user_annotation(self, annotation: Type) -> Self {
        TypedExpr {
            user_annotation: Some(annotation),
            ..self
        }
    }

    /// Construct a literal expression.
    pub fn lit(l: Lit) -> Self {
        Self::new(TypedExprNode::Lit(l))
    }

    /// Construct a variable reference expression.
    pub fn var(name: impl Into<String>) -> Self {
        Self::new(TypedExprNode::Var(name.into()))
    }

    /// Construct a list literal expression.
    pub fn list(elts: Vec<Self>) -> Self {
        Self::new(TypedExprNode::List(elts))
    }

    /// Construct an aggregate expression.
    pub fn aggregate(input: Self, kind: AggregateKind) -> Self {
        Self::new(TypedExprNode::Aggregate {
            input: Box::new(input),
            kind,
        })
    }

    /// Construct a groupby expression.
    pub fn groupby(collection: Self, key: Self) -> Self {
        Self::new(TypedExprNode::GroupBy {
            collection: Box::new(collection),
            key: Box::new(key),
        })
    }

    /// Construct a let binding expression.
    ///
    /// `binding.ty` mirrors `bound_expr.ty` at construction time so that callers
    /// who pre-set the expression type via [`TypedExpr::with_ty`] (e.g. tests that
    /// bypass inference) do not need to set the binding type separately. After
    /// inference both fields hold the same type; [`compile_ccl::compile`] reads
    /// `binding.ty` as the authoritative slot. In normal lowering both start as
    /// [`Type::Infer`] and inference fills them together.
    pub fn let_bind(name: impl Into<String>, bound_expr: Self, body: Self) -> Self {
        let ty = bound_expr.ty.clone();
        Self::new(TypedExprNode::Let {
            binding: TypedBinding {
                name: name.into(),
                ty,
                user_annotation: None,
            },
            bound_expr: Box::new(bound_expr),
            body: Box::new(body),
        })
    }

    /// Construct an annotated let binding expression.
    ///
    /// Like [`let_bind`] but sets [`TypedBinding::user_annotation`] to `annotation`.
    /// Inference validates that the inferred type of `bound_expr` is compatible with
    /// `annotation` and raises [`infer::InferError::AnnotationMismatch`] on conflict.
    pub fn let_bind_annotated(
        name: impl Into<String>,
        bound_expr: Self,
        body: Self,
        annotation: Type,
    ) -> Self {
        Self::new(TypedExprNode::Let {
            binding: TypedBinding::new_annotated(name, annotation),
            bound_expr: Box::new(bound_expr),
            body: Box::new(body),
        })
    }

    /// Construct a tuple expression.
    pub fn tuple(elts: Vec<Self>) -> Self {
        Self::new(TypedExprNode::Tuple(elts))
    }

    /// Construct a first-class projection morphism node.
    ///
    /// `Proj(Field(f))` acts as the function `λ t → t.f`.
    pub fn proj_field(field: impl Into<String>) -> Self {
        Self::new(TypedExprNode::Proj(ProjKey::Field(field.into())))
    }

    /// Construct a first-class projection morphism node.
    ///
    /// `Proj(Index(n))` acts as the function `λ t → t.n`. Tuple subscript `t[n]`
    /// is lowered as `Expr::apply(t, Expr::proj_index(n))`.
    pub fn proj_index(i: usize) -> Self {
        Self::new(TypedExprNode::Proj(ProjKey::Index(i)))
    }

    /// Construct a unary operation expression.
    pub fn unary(op: UnaryOpKind, operand: Self) -> Self {
        Self::new(TypedExprNode::UnaryOp(op, Box::new(operand)))
    }

    /// Construct an n-ary composition expression.
    ///
    /// `exprs` must contain at least two morphisms. The composition is
    /// left-to-right: `exprs[0]` is applied first, `exprs[1]` second, and so
    /// on.
    pub fn compose(exprs: Vec<Self>) -> Self {
        debug_assert!(exprs.len() >= 2, "Compose requires at least two morphisms");
        Self::new(TypedExprNode::Compose(exprs))
    }

    /// Construct a binary operation expression.
    pub fn binop(left: Self, op: BinOpKind, right: Self) -> Self {
        Self::new(TypedExprNode::BinOp {
            left: Box::new(left),
            op,
            right: Box::new(right),
        })
    }

    /// Construct a curried function application.
    ///
    /// `argument` is first, `function` is second, mirroring the pipeline style.
    pub fn apply(argument: TypedExpr, function: TypedExpr) -> Self {
        Self::new(TypedExprNode::Apply {
            argument: Box::new(argument),
            function: Box::new(function),
        })
    }

    /// Build an unannotated or pre-annotated [`TypedExprNode::Lambda`].
    ///
    /// Pass [`Type::Hole`] for `param_ty` when the parameter type is not yet
    /// known (lowering phase); pass the concrete type when it is already known.
    /// Do not pass `Type::Infer(fresh_infer_var())` from lowering — `Hole` is
    /// the correct lowering placeholder.
    pub fn lambda(param: &str, param_ty: Type, body: TypedExpr) -> Self {
        let result_ty = Type::fun(param_ty.clone(), body.ty.clone());
        Self::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: param.to_string(),
                ty: param_ty,
                user_annotation: None,
            },
            body: Box::new(body),
            refinement: None,
        })
        .with_ty(result_ty)
    }

    /// Build a [`TypedExprNode::Lambda`] with a predicate [`Refinement`].
    pub fn lambda_with_refinement(
        param: &str,
        param_ty: Type,
        body: TypedExpr,
        refinement: TypedExpr,
        refinement_desc: &str,
    ) -> Self {
        Self::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: param.to_string(),
                ty: param_ty,
                user_annotation: None,
            },
            body: Box::new(body),
            refinement: Some(Refinement {
                id: next_refinement_id(),
                description: refinement_desc.to_string(),
                kind: RefinementKind::Predicate(Rc::new(RefCell::new(refinement))),
            }),
        })
    }

    /// Build a [`TypedExprNode::Lambda`] with a hash-join [`Refinement`].
    pub fn lambda_with_hash_join(
        param: &str,
        param_ty: Type,
        body: TypedExpr,
        spec: HashJoinSpec,
        desc: &str,
    ) -> Self {
        Self::new(TypedExprNode::Lambda {
            param: TypedBinding {
                name: param.to_string(),
                ty: param_ty,
                user_annotation: None,
            },
            body: Box::new(body),
            refinement: Some(Refinement {
                id: next_refinement_id(),
                description: desc.to_string(),
                kind: RefinementKind::HashJoin(Box::new(spec)),
            }),
        })
    }
}

// Implement Default so that we can use std::mem::take out of Exprs.
impl Default for TypedExpr {
    fn default() -> Self {
        Self::new(TypedExprNode::Lit(Lit::Int(0)))
    }
}

/// A single conditional branch in a [`TypedExprNode::Case`] expression.
///
/// Holds a `guard` (a boolean expression) and a `body` (the value produced
/// when the guard is `true`). [`TypedExprNode::Case`] evaluates branches in
/// order and returns the first body whose guard is satisfied.
#[derive(Debug, Clone, PartialEq)]
pub struct Branch {
    /// Boolean guard; constrained to [`Type::Base(BaseType::Bool)`] during inference.
    pub guard: TypedExpr,
    /// Value expression; evaluated when `guard` is `true`.
    pub body: TypedExpr,
}

/// A CCL type annotation.
///
/// Appears on [`TypedExpr`] nodes and as the output of type inference.
///
/// The two pre-/post-inference variants divide ownership cleanly:
///
/// | Variant | Owner | Meaning | Must be eliminated by |
/// |---|---|---|---|
/// | `Hole` | Lowering | "This slot needs a type; not yet known" | End of inference (hard error if survives) |
/// | `Infer(id)` | Type checker only | "Inference variable N, tracked in table" | End of `resolve()` (ambiguous type if survives) |
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
    /// A partially-known tuple: only the listed index positions are constrained.
    ///
    /// Used as the domain type of index-projection morphisms during inference.
    /// `Proj(Index(n))` gets type `PartialTuple([(n, ?a)]) ⇒ ?a`.
    /// Unifies with [`Type::Tuple`] by constraining each indexed element, and
    /// with another `PartialTuple` by constraining overlapping indices.
    PartialTuple(Vec<(usize, Type)>),
    /// A partially-known record: only the listed named fields are constrained.
    ///
    /// Used as the domain type of field-projection morphisms during inference.
    /// `Proj(Field("x"))` gets type `PartialRecord([("x", ?a)]) ⇒ ?a`.
    /// Unifies with [`Type::Record`] by constraining matching fields, and with
    /// another `PartialRecord` by constraining overlapping fields.
    PartialRecord(Vec<(String, Type)>),
    /// A sum type.
    ///
    /// Representable in the type system but not yet produced by inference.
    /// TODO: Generating and compiling `Union` types.
    Union(Vec<Type>),
    /// A refinement of another type
    Refinement(Box<Type>, Refinement),
    /// Pre-inference placeholder stamped by lowering on every new node.
    ///
    /// Created exclusively by [`TypedExpr::new`] and [`TypedBinding::new_unannotated`].
    /// The inference pass converts each `Hole` to a registered [`Type::Infer`] variable
    /// before type-checking begins. A `Hole` surviving past inference is a compiler bug.
    Hole,
    /// Unresolved type variable, identified by a unique [`InferVarId`].
    ///
    /// Created exclusively by [`crate::ccl::infer::TypeInferenceContext::fresh_infer_var`]
    /// during inference. Variables are registered in the [`crate::ccl::unify::UnificationTable`]
    /// and resolved by the post-inference [`crate::ccl::unify::resolve`] pass.
    Infer(InferVarId),
    /// The opaque domain type of an externally-registered data source.
    ///
    /// Used as the domain in `Fun(DataSource(name), output_type)` types emitted
    /// by the source registry.  [`crate::interpreter::compile_ccl::CompileContext`]
    /// resolves this to a concrete `Extent::DataSourceDomain(rc)` at compilation time
    /// by looking the name up in its source-domain-extent registry.
    DataSource(String),
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
            Type::UIntRange(n) => write!(f, "[0, {}]", n - 1),
            Type::Fun(a, b) => write!(f, "({a} ⇒ {b})"),
            Type::Tuple(ts) => {
                let parts: Vec<_> = ts.iter().map(|t| t.to_string()).collect();
                write!(f, "({})", parts.join(", "))
            }
            Type::Record(fields) => {
                let parts: Vec<_> = fields.iter().map(|(n, t)| format!("{n}: {t}")).collect();
                write!(f, "{{{}}}", parts.join(", "))
            }
            Type::PartialTuple(entries) => {
                let parts: Vec<_> = entries.iter().map(|(i, t)| format!(".{i}: {t}")).collect();
                write!(f, "{{{}..}}", parts.join(", "))
            }
            Type::PartialRecord(entries) => {
                let parts: Vec<_> = entries.iter().map(|(n, t)| format!("{n}: {t}")).collect();
                write!(f, "{{{}..}}", parts.join(", "))
            }
            Type::Union(ts) => {
                let parts: Vec<_> = ts.iter().map(|t| t.to_string()).collect();
                write!(f, "{}", parts.join(" | "))
            }
            Type::Refinement(t, r) => write!(
                f,
                "{{{t} | Refined({})}}",
                match &r.kind {
                    RefinementKind::Predicate(p) => p
                        .try_borrow()
                        .map_or(r.description.clone(), |e| symbolic::symbolic(&e)),
                    RefinementKind::HashJoin(_) => r.description.clone(),
                }
            ),
            Type::Hole => write!(f, "_"),
            Type::Infer(id) => write!(f, "?{}", id.0),
            Type::DataSource(name) => write!(f, "source({name})"),
        }
    }
}

impl Type {
    /// Helper for creating function types
    pub fn fun(domain: Self, codomain: Self) -> Self {
        Type::Fun(Box::new(domain), Box::new(codomain))
    }

    /// If this is a function type, return the domain type, otherwise None.
    pub fn domain(&self) -> Option<Type> {
        if let Type::Fun(domain, _) = &self {
            Some(domain.as_ref().clone())
        } else {
            None
        }
    }

    /// If this is a function type, return the codomain type, otherwise None.
    pub fn codomain(&self) -> Option<Type> {
        if let Type::Fun(_, codomain) = &self {
            Some(codomain.as_ref().clone())
        } else {
            None
        }
    }

    /// Create a fresh, unregistered [`Type::Infer`] variable for use in tests.
    ///
    /// The created variable is **not** registered in any
    /// [`crate::ccl::unify::UnificationTable`], so it cannot be solved by the
    /// resolution pass. Use this only when constructing expressions in tests
    /// that will not be run through inference (e.g. to exercise pretty-printing
    /// or symbolic output). Production inference code must call
    /// [`crate::ccl::infer::TypeInferenceContext::fresh_infer_var`] instead.
    #[cfg(test)]
    pub fn infer() -> Self {
        Type::Infer(fresh_infer_var_id())
    }
}

/// Represents a type refinement carried by a [`TypedExprNode::Lambda`] parameter.
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
    Predicate(Rc<RefCell<TypedExpr>>),
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
    pub build_key: Rc<TypedExpr>,
    /// CCL expression for the probe-side join key; references `probe_var_name` as a free variable.
    pub probe_key: Rc<TypedExpr>,
    /// CCL expression for the build-side source list (no free generator variables).
    pub build_source: Rc<TypedExpr>,
    /// CCL expression for the probe-side source list (no free generator variables).
    pub probe_source: Rc<TypedExpr>,
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
