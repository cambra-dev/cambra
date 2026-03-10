# CCL AST Design

Design decisions for the Cambra Core Language (CCL) abstract syntax tree — the intermediate representation between Python source and the dataflow operator graph.

---

## Overview

CCL is a λ-calculus–based IR. Python source is lowered into CCL, where it is type-inferred and optimized, then compiled to the operator graph for execution.

```
Python source
  → parse          (rustpython_parser)
  → lower          (ccl/lower.rs: Python AST → CCL AST, structural only)
  → infer          (ccl/infer.rs: limited type inference, fills param_ty / Let.ty)
  → type-check     (bidirectional, fills in Type::Unknown annotations)
  → optimize       (tree rewrites on CCL AST)
  → compile        (interpreter/compile_ccl.rs: CCL AST → dataflow operators)
  → subscribe()
  → producer/consumer dataflow
```

---

## Key Design Decisions

### Less normalized than ANF

CCL is a λ-calculus IR, not strict A-Normal Form. In ANF every intermediate result must be named with a `Let` binding; in CCL compound expressions may appear inline. For example, `Apply(f, BinOp(x, Add, y))` is valid without an intermediate binding for `x + y`.

`Let` bindings are available for naming intermediate results (required by the type checker and useful for debugging), but are not mandatory.

Rationale: strict ANF over-normalizes the tree, destroying structural information needed for optimization passes (reordering, equivalency checks, fusion).

### No α-renaming — name uniqueness not guaranteed

CCL does not perform variable renaming (α-renaming) as ANF or SSA IRs do. Python reassignment of the same variable (`x = 1; x = 2`) produces nested `Let` bindings that shadow each other:

```
let x = 1
in let x = 2   ← same name, new binding; value evaluated in outer scope
in x
```

The semantics are correct for sequential code — each `Let` evaluates its value expression in the enclosing scope before the new binding takes effect — but the same name may appear at multiple binding sites in the tree.

Rationale: renaming every assignment to a fresh variable would over-normalize the tree for the same reasons strict ANF does, destroying structural information useful for optimization passes.

### Curried application

Function application is curried: `Apply(Box<Expr>, Box<Expr>)`.
There are no first-class n-ary functions: the Python syntax `f(x, y)` may be written as `f(x)(y)` in CCL but is typically represented as chained applications using `▷`.
Multi-argument calls are represented as nested `Apply` nodes: `f(x)(y)` → `Apply(Apply(f, x), y)`.

Rationale: uniform with the λ-calculus basis; multi-args can be supported via `Record`s.

### Lambda/Apply encoding of collection iteration

Collection iteration (list comprehensions) is encoded using the existing `Lambda` and `Apply` nodes.

The operator graph's Iteration/Argument mode distinction is captured by the way the graph is constructed:

- `Lambda::subscribe()` (no binding) → `VarSource::Iteration` — variable iterates over its extent
- `Lambda::subscribe_to_application(binding)` → `VarSource::Argument` — variable receives from a binding
- `Apply::subscribe()` always calls `subscribe_to_application`, forcing Argument mode

The same distinction applies in CCL:

| CCL node | Compilation path | Operator graph |
|----------|-----------------|---------------|
| Standalone `Lambda` (not inside `Apply`) | `subscribe()` (if execution is forced)| `VarSource::Iteration` |
| `Apply(lambda, collection)` | `subscribe_to_application(collection)` | `VarSource::Argument` |
| `Apply(Var("sum"), xs)` | resolved to built-in aggregate | aggregate operator |

### `Case` only — no `IfThenElse`

Python `if/else` and `if/elif/.../else` chains are lowered to `Case` during Python → CCL lowering. There is no `IfThenElse` node in the CCL AST. `Case` subsumes all multi-way branching.

### `Join`/`Jump` for loops

Python `while` loops are lowered to explicit `Join`/`Jump` nodes rather than recursive `Lambda`/`Let` combinations.

`Join` defines a labeled loop header with typed parameters (the loop variables). `Jump` is a tail call to a `Join` point, passing updated parameter values. The non-escaping property (jumps are always in tail position, join points cannot be stored or passed as arguments) is enforced by construction.

Rationale: encoding loops as recursive lambdas requires detecting recursive bindings by scanning the tree for forward references. `Join`/`Jump` makes the loop structure explicit, simplifying both the lowering pass and optimization passes targeting iterate/feedback operators.

### Shared literal and operator types

`Literal` and `BinOpKind` are defined in a shared module, not in the interpreter. The CCL IR must not depend on interpreter internals.

### Optional type annotations

`Lambda.param_ty` and `Let.ty` are `Option<Type>`. Unannotated terms are valid in the CCL; the type checker fills in `Type::Unknown` annotations. `Type::Unknown` has no runtime equivalent — all types must be resolved before operator-graph compilation.

---

## Node Definitions

```rust
// --- Shared module (no dependency on interpreter) ---

enum Literal {
    Int(i64),
    String(String),
    Bool(bool),
    Unit,
}

enum ArithmeticKind { Add, Sub, Mul, FloorDiv }

enum CompareKind { Equals, NotEquals, Less, LessOrEq, Greater, GreaterOrEq }

enum LogicKind { And, Nand, Or, Nor, Xor, Xnor }

enum BinOpKind {
    Arithmetic(ArithmeticKind),
    BoolLogic(LogicKind),
    Concat,
    Compare(CompareKind),
}

enum UnaryOpKind {
    Neg,  // unary -
    Not,  // boolean not
}

// --- CCL AST ---

enum Expr {
    Lit(Literal),
    Var(String),
    Apply{
      function: Box<Expr>, 
      argument: Box<Expr>
    },         // unary application: f(x) == x ▷ f
    BinOp{
      left: Box<Expr>, 
      op: BinOpKind, 
      right: Box<Expr>,
    },
    UnaryOp(UnaryOpKind, Box<Expr>),
    TypeAnnotation(Box<Expr>, Type),
    Lambda {
        param: String,
        param_ty: Option<Type>,
        body: Box<Expr>,
        /// Optional restriction on the outer iteration variable.
        /// `None` for unrestricted lambdas; `Some(r)` for filtered or joined comprehensions.
        refinement: Option<Refinement>,
    },
    Let {
        name: String,
        bound_ty: Option<Type>,
        bound_expr: Box<Expr>,
        body: Box<Expr>,
    },
    List(Vec<Expr>),                     // list literal [e0, e1, ...]; elements may be arbitrary exprs of the same type
    Case {
        scrutinee: Box<Expr>,
        branches: Vec<(Pattern, Expr)>,
    },
    Join {
        name: String,
        params: Vec<(String, Option<Type>)>,
        loop_body: Box<Expr>,                 // loop body; may contain Jump back to this Join
        outer_body: Box<Expr>,                // evaluated first; contains the initial Jump
    },
    Jump {
        target: String,                  // must name an enclosing Join
        args: Vec<Expr>,
    },
    // Construction — lowering stubbed, deferred
    Tuple(Vec<Expr>),
    Record(Vec<(String, Expr)>),
}

enum Pattern {
    Lit(Literal),
    Var(String),
    Tuple(Vec<Pattern>),
    Record(Vec<(String, Pattern)>),
    Wildcard,
}

enum Type {
    Base(BaseType),
    UIntRange(usize),                    // finite index range [0, n); domain of list types
    Fun(Box<Type>, Box<Type>),           // T ⇒ U
    Tuple(Vec<Type>),
    Record(Vec<(String, Type)>),
    Union(Vec<Type>),
    Unknown,                             // pre-type-checking placeholder
    Refinement(Box<Type>, Refinement),   // refined base type; `Refinement.kind` carries join strategy
    // Future:
    // Pi { param, param_ty, body_ty }  — dependent function type
}

/// Carries the join strategy for a restricted Lambda (i.e. a filtered/joined comprehension).
struct Refinement {
    /// Human-readable description shown by the symbolic printer (e.g. `"x < 10"`, `"x == y"`).
    description: String,
    /// Whether this is a loop join (arbitrary predicate) or hash join (equality between generators).
    kind: RefinementKind,
}

enum RefinementKind {
    /// Arbitrary boolean predicate; compiled to a `ComputeRestriction::new_predicate` loop join.
    /// The `Rc` holds the predicate expression and doubles as the cache key in `CompileContext`.
    Predicate(Rc<RefCell<Expr>>),
    /// Equality key join between two generators; compiled to a `ComputeRestriction::new_join`
    /// hash join using a `Converse` operator.
    HashJoin(Box<HashJoinSpec>),
}

/// Specifies the two sides of a hash join.
///
/// Detection criteria: exactly 2 generators, exactly 1 `if` guard, the guard is
/// `lhs == rhs` where each side references a distinct generator variable.
struct HashJoinSpec {
    build_gen: usize,           // generator index (0-based) for the build side
    probe_gen: usize,           // generator index for the probe side
    build_var_name: String,     // iteration variable name for the build side
    probe_var_name: String,     // iteration variable name for the probe side
    build_key: Rc<RefCell<Expr>>,   // key expression referencing build_var_name
    probe_key: Rc<RefCell<Expr>>,   // key expression referencing probe_var_name
    build_source: Rc<RefCell<Expr>>, // source list for the build side
    probe_source: Rc<RefCell<Expr>>, // source list for the probe side
}
```

---

## Type inference

`ccl::infer` currently implements a "limited" type inference pass that sits between
lowering and the full bidirectional type checker. It handles enough to make
the existing list-comprehension pipeline work end-to-end, while deferring
heavier machinery (BinOp rules, constraint unification) to later phases.

### `collect_param_constraint`

Used for standalone lambdas (not in `Apply(lambda, arg)` position). Walks the
entire lambda body collecting every `Apply(func, Var(param))` pattern and records
the domain of `func`'s inferred `Fun` type as a constraint. All constraints must
agree; conflicting constraints produce a `TypeMismatch` error.

### Comparison with bidirectional type checking and Hindley-Milner

| | Our limited pass | Bidirectional | Full HM |
|---|---|---|---|
| `Apply(Λ x. b, arg)` | special-case Apply rule | elegant check-mode push-down | same |
| Standalone `Λ x. b` | `collect_param_constraint` heuristic | fails in synth mode; needs annotation | type variable + unify |
| Multi-use params | first constraint only | same limitation | unification solves all |
| Needs unification | No | No | Yes |
| Type error reporting | limited | at check sites | at unification failure |

**Delta from our pass to bidirectional**: add a `check(expr, expected, ctx)`
function alongside `infer`; rewrite the Apply rule to check the argument against
the domain. `collect_param_constraint` is still needed for standalone lambdas.
Gains type-mismatch error detection at Apply sites.

**Delta from bidirectional to HM**: add type variables (`Type::Var(u32)`), a
union-find unification table, and an occurs check. Removes the need for
`collect_param_constraint` since type variables unify across all use sites.

### TODOs

- BinOp/UnaryOp type rules (arithmetic, comparison, boolean).
- `Case` arm scope: push pattern variable bindings into ctx.
- Infer `Let.ty` from the type of `value` (required before `Let` nodes can be compiled; see §Compilation).

---

## Compilation

The `compile_ccl` pass (`interpreter/compile_ccl.rs`) transforms a fully-type-inferred CCL AST
into the dataflow operator graph (`interpreter/let_op.rs`).

### `Let` nodes compile to a dedicated `Let` operator

`Let` is compiled to a first-class `Let` operator rather than desugared to `Apply(Lambda, value)`.

The desugaring identity `let x = e1 in e2 ≡ (λx. e2)(e1)` is operationally correct, but
compiling through it loses binding provenance in the graph and introduces unnecessary indirection:
data flows `apply.argument → lambda.var → lambda.body → lambda_producer → apply_producer`,
and `Lambda` must support both `VarSource::Iteration` and `VarSource::Argument` modes even
though a let-binding is always `Argument`.

The `Let` operator stores `(variable: Var, definition: Operator, body: Operator, extent: Extent)`.
`LetProducer::get()` returns the body's output directly — no `FunctionBindings` wrapping.
The bound variable is subscribed to `definition` exactly once via a `VarProducer`, so multiple
`VarRef(name)` nodes in the body all resolve to the same producer and the value is computed once.

**Prerequisite**: `Let.bound_ty` must be `Some(T)` before compilation — the type inference pass
fills this in from the type of `bound_expr`.

---

## Planned implementation order

1. Define the node types above in a new `src/ccl/` module. ✓
2. Add pretty printer (`src/ccl/pretty.rs`) and Python → CCL lowering (`src/ccl/lower.rs`) with snapshot tests. ✓
3. Insert CCL as the IR between Python and operators (in progress):
   - `ccl/lower.rs`:  `lower_list_comp` produces unannotated lambdas
     (`param_ty: None`) — type annotation moved to
     the inference pass. ✓
   - `interpreter/compile_ccl.rs`: CCL → operator compilation step created;
     `CompileContext`, `CompileError`, `compile()`, and unit tests. ✓
   - `ccl/infer.rs`: limited type inference pass; `TypeInferenceContext`, `InferError`,
     `infer()`, `collect_param_constraint()`; unit and pipeline tests. ✓
   - `interpreter/compile_ccl.rs` add support for compiling Let nodes to operators (see §Compilation above). ✓
   - `interpreter/let_op.rs`: dedicated `Let` operator and `LetProducer` replacing the Let-as-Apply-Lambda desugaring. ✓
   - `ccl/mod.rs` + `ccl/lower.rs` + `interpreter/compile_ccl.rs`: hash join detection and compilation
     (`RefinementKind::HashJoin`, `HashJoinSpec`, `compile_hash_join_restriction`). ✓
   - `lowering_via_ccl.rs`: sandboxed end-to-end pipeline tests.
   - `lowering.rs` direct path removed after parity confirmed.
