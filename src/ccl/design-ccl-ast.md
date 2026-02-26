# CCL AST Design

Design decisions for the Cambra Core Language (CCL) abstract syntax tree — the intermediate representation between Python source and the dataflow operator graph.

---

## Overview

CCL is a λ-calculus–based IR. Python source is lowered into CCL, where it is type-checked and optimized, then compiled to the operator graph for execution.

```
Python source
  → parse          (rustpython_parser)
  → lower          (Python AST → CCL AST)
  → type-check     (bidirectional, fills in Type::Unknown annotations)
  → optimize       (tree rewrites on CCL AST)
  → compile        (CCL AST → dataflow operators)
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
    },
    Let {
        name: String,
        ty: Option<Type>,
        value: Box<Expr>,
        body: Box<Expr>,
    },
    List(Vec<Expr>),                     // list literal [e0, e1, ...]; elements may be arbitrary exprs
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
    Fun(Box<Type>, Box<Type>),           // T ⇒ U
    Tuple(Vec<Type>),
    Record(Vec<(String, Type)>),
    Union(Vec<Type>),
    Unknown,                             // pre-type-checking placeholder
    // Future:
    // Pi { param, param_ty, body_ty }  — dependent function type
    // Refinement { base, predicate }   — refinement type
}
```

---

## Planned implementation order

1. Define the node types above in a new `src/ccl/` module. ✓
2. Add pretty printer (`src/ccl/pretty.rs`) and Python → CCL lowering (`src/ccl/lower.rs`) with snapshot tests. ✓
3. Iteratively replace the current Python → operator direct lowering with Python → CCL → operator.
