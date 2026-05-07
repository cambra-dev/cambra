# CCL AST Design

Design decisions for the Cambra Core Language (CCL) abstract syntax tree — the intermediate representation between CHL source and the dataflow operator graph.

---

## Overview

CCL is a λ-calculus–based IR. CHL source is lowered into CCL, where it is type-inferred and optimized, then compiled to the operator graph for execution.

```
CHL source
  → parse          (rustCHL_parser)
  → lower          (ccl/lower.rs: CHL AST → CCL AST, structural only)
  → infer          (ccl/infer.rs: type inference, converts Hole→Infer and fills ty on every node)
  → resolve        (ccl/unify.rs: substitutes solved Infer vars with concrete types)
  → inline         (ccl/inline.rs::inline_non_iterable_lambdas: inline UDF Let bindings with non-iterable domains; beta-reduce at call sites)
  → lambda_elim    (ccl/lambda_elim.rs: Lambda → point-free combinators)
  → remove_defers  (ccl/remove_defers.rs: inline Defer/Feed/Define nodes; see §Defer)
  → optimize       (tree rewrites on CCL AST, currently just join_plan.rs)
  → convert        (interpreter/operator_conversion.rs: CCL AST → tile operators)
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

CCL does not perform variable renaming (α-renaming) as ANF or SSA IRs do. CHL reassignment of the same variable (`x = 1; x = 2`) produces nested `Let` bindings that shadow each other:

```
let x = 1
in let x = 2   ← same name, new binding; value evaluated in outer scope
in x
```

The semantics are correct for sequential code — each `Let` evaluates its value expression in the enclosing scope before the new binding takes effect — but the same name may appear at multiple binding sites in the tree.

Rationale: renaming every assignment to a fresh variable would over-normalize the tree for the same reasons strict ANF does, destroying structural information useful for optimization passes.

### Application shape

Function application is a single `Apply(Box<Expr>, Box<Expr>)` node. Single-argument CHL calls `f(a)` lower to `Apply(a, Var(f))` directly. Multi-argument CHL calls `f(a, b, ...)` lower to `Apply(Tuple([a, b, ...]), Var(f))` — the arguments are tupled so the call shape matches how multi-arg CHL lambdas are uncurried at lowering time (see "CHL `lambda` expressions" below).

Partial / curried application in CCL itself is still represented by chained `Apply` nodes — `f(x)(y)` in source writes the curry explicitly and lowers to `Apply(Apply(Var(f), x), y)`. This path remains unsupported past operator conversion (no `curry` combinator case yet) and is tracked as follow-up work; in normal CHL source, chained applications only arise when users nest lambdas explicitly.

Rationale: keeping application a single-argument node preserves the uniform λ-calculus basis, while the tupled-lowering convention lets the common multi-arg case compile cleanly through `lambda_elim` and operator conversion without threading a curry/uncurry combinator through every pass.

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
| `Aggregate { input: xs, kind: Sum }` | `compile_aggregate` | aggregate operator |

### `Aggregate` — first-class aggregation node

CHL aggregate calls (`sum(xs)`, `max(xs)`) are lowered directly to `Expr::Aggregate` rather than kept as `Apply(Var("sum"), xs)`. This makes aggregate operations structurally distinct from ordinary function calls, which simplifies:

- Type inference: `infer` constrains the input to `Fun(_, codomain)` via `constrain_equal` and dispatches to `AggregateKind::constrain_signature` for the per-variant element-vs-output-type relationship (`Sum`: requires `codomain = Int`, returns `Int`; `Max`: returns `codomain` unchanged).
- Compilation: the compiler dispatches on `Expr::Aggregate` and emits the appropriate aggregate operator without scanning call-site variable names.

`AggregateKind` enumerates the supported operations; each variant carries its own typing rule on `constrain_signature`. New variants (`Count: _ → Int`, `Mean: Int → Float`, …) add their rule there without touching the `Aggregate` inference branch.

### CHL `lambda` expressions — single `Expr::Lambda` (tupled when multi-arg)

CHL `lambda` expressions lower to a single `Expr::Lambda`. A single-parameter `lambda x: body` becomes `λ x → body`. A multi-parameter `lambda x, y, ...: body` is **uncurried at lowering**: it becomes `λ __arg_tuple_N → body[x := __arg_tuple_N.0, y := __arg_tuple_N.1, ...]`, a single-parameter lambda whose parameter is a synthetic tuple and whose body has each named argument replaced in-place by a projection of that tuple. `param.ty` starts as `Type::Hole`; inference resolves it (including the tuple arity for the multi-arg case) from the body's projection constraints and the call-site argument type.

Each multi-arg lambda mints a fresh `N` from a counter on `LoweringContext`, so nested multi-arg lambdas (e.g. `lambda x, y: lambda a, b: x + a`) receive distinct tuple-parameter names. Without the unique suffix, an outer substitution that inserts `Var("__arg_tuple")` into an inner lambda's body would be captured by the inner binder; the fresh suffix plus the reserved `__arg_tuple_` prefix (user code cannot bind double-underscore names here) keeps the in-place substitution non-capture-avoiding yet correct.

Rationale for uncurrying: a curried `λ x → λ y → body` lowering would trigger `lambda_elim`'s nested-lambda rule and produce `curry(body)`, which operator conversion cannot compile. Uncurrying at lowering pairs with the tupled call lowering above so that syntactic multi-arg functions compile without any `curry` combinator appearing in the tree. Users who want genuine partial application still write `lambda x: lambda y: ...` or `curry(f)` explicitly — those produce curried types and are tracked as follow-up work.

In-place substitution (rather than wrapping the body in `let xi = __arg_tuple_N.i`) avoids introducing function-typed `Let` nodes that `lambda_elim`'s Let rule would lift to `ParamTy ⇒ T` and compile into zip-of-projections morphisms that current simplification cannot reduce back to a bare morphism.

Restrictions not yet supported (lowering raises `LoweringError::Unsupported`): `*args`, `**kwargs`, keyword-only arguments, and default values.

### Function definitions — `Let` + single `Expr::Lambda` (tupled when multi-arg)

CHL `def` statements are lowered to `Let` bindings whose value is a single `Expr::Lambda`, mirroring the `lambda`-expression shape above. `def f(x): body` becomes `let f = λ x → lower(body) in ...`; `def f(x, y, ...): body` uncurries to `let f = λ __arg_pair → lower(body)[x := __arg_pair.0, y := __arg_pair.1, ...] in ...`. The function name is bound via `Expr::let_bind`, and the body is lowered via `lower_stmts` (supporting assignments, nested function definitions, and a final expression).

Pairing the definition shape with `lower_call`'s tupled multi-arg shape keeps the common multi-arg `def` path free of the curried-lambda chain that `lambda_elim` would fold into an unsupported `curry(body)`.

### Generator functions — desugaring to Lambda + list-comp encoding

Generator functions whose body ends in a `for` loop with a chain of nested `for` / `if` / `yield` statements are desugared at lowering time to named lambdas wrapping the Lambda/Apply tiling encoding used for list comprehensions. No new CCL AST nodes are required.

`def f(params): for x in iter: yield expr` becomes `let f = uncurry(params, generator_chain(expr, [(x, iter, steps)]))`, where `uncurry(params, body)` is the same shape used by `lambda` and regular `def` lowering — a single-parameter lambda for one argument, and a tupled-parameter lambda with in-place projection substitution for multiple arguments.

**Nested `for` loops** produce one generator per `for` in the chain. The inner iterable may reference outer loop variables (the inner source expression is in scope of the outer iteration lambda).

**Let-bindings in generator bodies** (`y = f(x); yield y`) are lowered as `Expr::Let` nodes interleaved in the Lambda/Apply chain. Each let is placed after the enclosing `for`'s iteration lambda and before the next nested `for` (or the terminal yield), so the bound name is evaluated once per iteration of its enclosing loop. Lets are duplicated into the refinement closure so that if-guards can reference let-bound names.

**Pre-loop lets** (assignments before the outer `for` in a function body) are handled generically by the `lower_stmts` machinery — they wrap the generator expression in `Expr::Let` nodes. Generator lowering itself only starts at the `for` loop.

**Mutation rule**: an assignment inside a generator body is a let-binding (allowed) iff the target name is either fresh or was introduced in the same `for`-body. Assignments to names from an enclosing `for`-body, function arguments, or pre-loop lets are rejected as mutation — they would require the time-indexed mutation machinery from Phase 2. Function definitions inside generator bodies are treated identically to assignments.

Generator expressions `(expr for x in xs)` are lowered identically to `ListComp` via the `lower_list_comp` function (separate from the generator-function path which uses `lower_generator_chain`).

### `GroupBy` — first-class grouping node

`groupby(collection, key)` calls are lowered directly to `Expr::GroupBy` rather than kept as a nested `Apply`. This makes the grouping operation structurally distinct from ordinary calls, which simplifies:

- **Type inference**: `infer` can propagate the collection's element type onto the key lambda's `param_ty` without needing built-in name resolution.
- **Compilation**: the compiler can dispatch on `Expr::GroupBy` and emit the appropriate group operator without inspecting call-site variable names.

The result type is `Fun(K, Fun(UInt, V))` where `K` is the key type and `V` is the element type. The outer function maps a key to a group; the inner function maps an unsigned index to an element within that group — the same encoding used for lists (`Fun(UIntRange(n), V)`), but with an unbounded `UInt` domain since group sizes are not known statically.

### `Case` only — no `IfThenElse`

CHL `if/else`, `elif` chains, and ternary `if` expressions are all lowered to `Case` during CHL → CCL lowering. There is no `IfThenElse` node in the CCL AST. `Case` subsumes all multi-way branching.

`Case` holds an ordered list of `Branch { guard, body }` values. Guards are arbitrary `TypedExpr` nodes constrained to `Bool` at inference time; the first truthy guard wins. `elif` chains are **flattened** into a single `Case`: when `lower_if` recurses into the `orelse` block and the result is itself a `Case`, its branches are extended directly rather than nested, so `if c1: … elif c2: … else: …` produces `{ c1 → …; c2 → …; true → … }`. Structural pattern decomposition is represented as `Let` bindings in arm bodies; literal matching is an equality guard expression.

CHL `match` statements (planned) will desugar entirely at lowering time: the scrutinee is bound with a fresh `Let(__scrut)` node, then each arm produces a guard (`__scrut == lit` for literal patterns, `Lit(true)` for wildcard/structural) and a body (with `Let` bindings for any captured variable names). No IR changes are needed for `match` support.

### `Join`/`Jump` for loops

CHL `while` loops are lowered to explicit `Join`/`Jump` nodes rather than recursive `Lambda`/`Let` combinations.

`Join` defines a labeled loop header with typed parameters (the loop variables). `Jump` is a tail call to a `Join` point, passing updated parameter values. The non-escaping property (jumps are always in tail position, join points cannot be stored or passed as arguments) is enforced by construction.

Rationale: encoding loops as recursive lambdas requires detecting recursive bindings by scanning the tree for forward references. `Join`/`Jump` makes the loop structure explicit, simplifying both the lowering pass and optimization passes targeting iterate/feedback operators.

### Shared literal and operator types

`Literal` and `BinOpKind` are defined in a shared module, not in the interpreter. The CCL IR must not depend on interpreter internals.

### Typed binding sites — `TypedBinding`

All binding sites — `Lambda`, `Join`, and `Let` — use `TypedBinding { name, ty, user_annotation }` rather than separate `name: String` / type fields.

- `ty` starts as `Type::Hole` (lowering placeholder); the inference pass converts it to a registered `Type::Infer` variable at inference entry and fills in the concrete type before compilation.
- `user_annotation` carries an optional user-written type annotation (e.g. from a CHL `cast` expression). Inference validates the inferred type against it; if the body provides no usable constraint the annotation is used directly as the param type.

`Type::Hole` and `Type::Infer(_)` have no runtime equivalents — all types must be resolved to concrete types before operator-graph compilation.

### `TypedExpr` — type slot on every node

Every CCL expression is wrapped in `TypedExpr { node: TypedExprNode, ty: Type, user_annotation: Option<Type> }`.

- `node` holds the expression kind (`TypedExprNode` enum, formerly `Expr`).
- `ty` starts as `Type::Hole` (stamped by `TypedExpr::new()`); the inference pass converts it to a registered `Type::Infer` variable then fills it with the concrete type before compilation.
- `user_annotation` carries an explicit annotation from the source (e.g. a `cast` call). Inference checks it for compatibility with the inferred type and uses it as the final type if present.

`TypeAnnotation` no longer exists as a node variant; annotations are carried uniformly by `TypedExpr.user_annotation` instead.

### `Type::Hole` and `Type::Infer` — the two-way split

The type system uses two distinct pre-/post-inference placeholders with strict ownership:

| Variant | Owner | Meaning | Must be eliminated by |
|---|---|---|---|
| `Type::Hole` | Lowering | "This slot needs a type; not yet known" | End of inference (debug assertion if survives) |
| `Type::Infer(id)` | Type checker only | "Inference variable N, tracked in table" | End of `resolve()` (ambiguous type if survives) |

**`Type::Hole`** is stamped by `TypedExpr::new()` and `TypedBinding::new_unannotated()`. It is a structural placeholder that carries no identity — it is not registered in the `UnificationTable`. The inference pass (`infer::infer`) converts every `Hole` to a registered `Type::Infer` variable at the top of the `infer()` function (before the main dispatch). `fresh_infer_var_id()` must not be called from lowering code; use `Type::Hole` instead.

**`Type::Infer(id)`** is created exclusively by `TypeInferenceContext::fresh_infer_var()`. Each variable is registered in the `UnificationTable` immediately, giving it an identity that can participate in unification and be resolved by `unify::resolve`. This strict ownership means every `Infer(id)` that reaches `resolve()` is a known, tracked variable — never an accidentally-unregistered orphan.

This separation makes test expression construction straightforward: tests that build expressions without running inference use `Type::Hole` (via `TypedExpr::new()`) and never need to synthesize `InferVarId` values.

**Path to full HM**: the current inference pass still mutates `param.ty` and `binding.ty` directly (two sources of truth alongside the `UnificationTable`). The intended follow-up is to move inference toward writing only to the table and having `resolve()` be the single materialization pass — eliminating the two-sources-of-truth problem. Once BinOp/UnaryOp unification rules are added, `collect_param_constraint` can also be removed.

### Union-find unification table (`ccl::unify`)

`ccl::unify::UnificationTable` is a sparse union-find structure over `InferVarId`s, stored in `TypeInferenceContext`. It tracks solved inference variables across the typed-expression tree.

- Each fresh variable is `register`ed when created by `TypeInferenceContext::fresh_infer_var()`.
- `set(id, ty)` records a concrete solution; `probe(id)` retrieves it (with path compression via `find`).
- `unify(a, b)` merges two variables into the same equivalence class, preferring a solved root when one exists.
- After the main inference walk, `unify::resolve(expr, table)` replaces remaining `Type::Infer(id)` placeholders with their solved types. Any `Infer` left after resolution represents an ambiguous type. `resolve` is now called automatically inside the public `infer()` wrapper, so callers no longer need to invoke it explicitly.

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
    /// Left-to-right function composition: `f ≫ g` means "apply f, then g".
    /// Introduced by `lambda_elim`; absent in source-level CCL.
    Compose,
    /// Collection union (`@`): `Fun(A, B) @ Fun(C, D)` → `Fun(Union(A, C), dedup(B, D))`.
    /// Lowered from CHL `a @ b`; lambda elimination desugars this to
    /// `Apply(Tuple([a, b]), Builtin(CollectionUnion))` before operator conversion
    /// produces a `UnionOperator` tile.
    CollectionUnion,
}

enum UnaryOpKind {
    Neg,  // unary -
    Not,  // boolean not
}

enum AggregateKind {
    Sum,  // sum of elements (Int input → Int output)
    Max,  // maximum element (any base type input → same base type output)
}

// --- CCL AST ---

/// Every program is a TypedExpr. `node` holds the expression kind; `ty` is
/// filled in by infer::infer; `user_annotation` carries an explicit cast/annotation.
struct TypedExpr {
    node: TypedExprNode,
    ty: Type,                        // Infer(id) until inference fills it; Error on inference failure
    user_annotation: Option<Type>,   // checked against ty by infer; None for lowered nodes
}

/// Type alias for call-site convenience: `Expr` == `TypedExpr`.
type Expr = TypedExpr;

/// Key for a first-class projection morphism. Identifies which field is projected.
enum ProjKey {
    Index(usize),   // tuple field: .0, .1, …
    Field(String),  // record field: .fieldname
}

enum TypedExprNode {
    Lit(Literal),
    Var(String),
    /// Reference to a built-in primitive function (id, curry, zip, apply,
    /// map, converse, the binops, the unary ops, sum/max, …). Introduced
    /// post-inference by lambda elimination and join planning; matched on
    /// directly by simplify, join_plan, and operator_conversion.
    Builtin(Builtin),
    Proj(ProjKey),
    Apply{
      function: Box<TypedExpr>,
      argument: Box<TypedExpr>
    },         // unary application: f(x) == x ▷ f
    BinOp{
      left: Box<TypedExpr>,
      op: BinOpKind,
      right: Box<TypedExpr>,
    },
    UnaryOp(UnaryOpKind, Box<TypedExpr>),
    Lambda {
        param: TypedBinding,    // name + ty (Unknown until inferred) + user_annotation
        body: Box<TypedExpr>,
        /// Optional restriction on the outer iteration variable.
        /// `None` for unrestricted lambdas; `Some(r)` for filtered or joined comprehensions.
        refinement: Option<Refinement>,
    },
    Let {
        binding: TypedBinding,  // name + ty mirrors bound_expr.ty after inference
        bound_expr: Box<TypedExpr>,
        body: Box<TypedExpr>,
    },
    List(Vec<TypedExpr>),                     // list literal [e0, e1, ...]; elements may be arbitrary exprs of the same type
    Aggregate {
        input: Box<TypedExpr>,                // expression being aggregated (must be of type Fun)
        kind: AggregateKind,                  // the aggregation operation (Sum, Max, …)
    },
    /// Multi-way conditional branching. Evaluates each `Branch` in order;
    /// the first branch whose guard evaluates to `true` wins. Guards must
    /// have type `Bool`. CHL `if/else`, `elif` chains (flattened), and
    /// ternary `if` are all lowered to this node.
    Case {
        branches: Vec<Branch>,  // Branch { guard: TypedExpr, body: TypedExpr }
    },
    Join {
        name: String,       // join-point label
        params: Vec<TypedBinding>,
        loop_body: Box<TypedExpr>,            // loop body; may contain Jump back to this Join
        outer_body: Box<TypedExpr>,           // evaluated first; contains the initial Jump
    },
    Jump {
        target: String,                       // must name an enclosing Join
        args: Vec<TypedExpr>,
    },
    GroupBy {
        collection: Box<TypedExpr>,           // the collection (function) whose elements are grouped
        key: Box<TypedExpr>,                  // key extraction function: element → key
    },
    // Construction — lowering stubbed, deferred
    Tuple(Vec<TypedExpr>),
    Proj(ProjKey),                            // first-class projection morphism: .n or .name
    Record(Vec<(String, TypedExpr)>),
    // Built-in data source
    Source(String),

    // --- Output operators (defer/feed/define) ---
    // See §Defer for semantics and the remove_defers pass.

    /// Placeholder for an output accumulator introduced by `x = defer()`.
    /// The bound name is resolved by the surrounding `Let` binding.
    /// Removed by `remove_defers::run` before operator conversion.
    Defer,

    /// Feed a value into a deferred output: `x << value`.
    /// Lowers from the `<<` (LShift) binary operator when the LHS names a defer.
    /// Has type `Unit`; the value is extracted by `remove_defers` and inlined
    /// into the `Let` that introduced the defer.
    Feed {
        name: String,         // name of the defer binding being fed into
        value: Box<Expr>,
    },

    /// Define a deferred output to a specific value: `x <<= value`.
    /// Lowers from the `<<=` (AugAssign LShift) statement when the LHS names a defer.
    /// Has type `Unit`; the value is extracted by `remove_defers` and replaces the
    /// `Defer` in the surrounding `Let` binding.
    Define {
        name: String,         // name of the defer binding being defined
        value: Box<Expr>,
    },

    /// A bare expression used as a statement, followed by the rest of the block.
    /// `ExprStmt { expr, body }` evaluates `expr` for its side effects (e.g. a `Feed`
    /// or `Define`), then continues to `body`. Introduced by `lower_middle_stmt` for
    /// non-assignment, non-final statements. Dropped by `simplify` once any contained
    /// `Feed`/`Define` nodes have been removed.
    ExprStmt {
        expr: Box<TypedExpr>,
        body: Box<TypedExpr>,
    },
}

enum Type {
    Base(BaseType),
    UIntRange(usize),                    // finite index range [0, n); domain of list types
    Fun(Box<Type>, Box<Type>),           // T ⇒ U
    Tuple(Vec<Type>),
    Record(Vec<(String, Type)>),
    PartialTuple(Vec<(usize, Type)>),    // partial tuple: only listed indices constrained; domain of Proj(Index(n))
    PartialRecord(Vec<(String, Type)>),  // partial record: only listed fields constrained; domain of Proj(Field("x"))
    Union(Vec<Type>),
    Hole,                                // lowering placeholder; converted to Infer at inference entry
    Infer(InferVarId),                   // type-checker variable; registered in UnificationTable
    Error,                               // inference already failed here; suppresses cascades
    Refinement(Box<Type>, Refinement),   // refined base type; `Refinement.kind` carries join strategy
    DataSource(String),                  // opaque domain type of a source
    DeferredCollectionDomain(DeferredCollectionId),  // synthetic domain type for a Defer's function type; see §Defer
    // Future:
    // Pi { param, param_ty, body_ty }  — dependent function type
}

/// Carries the join strategy for a restricted Lambda (i.e. a filtered/joined comprehension).
struct Refinement {
    /// Unique ID for this refinement
    id: RefinementId, 
    /// Human-readable description shown by the symbolic printer (e.g. `"x < 10"`, `"x == y"`).
    description: String,
    /// Always an arbitrary predicate.  TODO flatten this away
    kind: RefinementKind,
}

enum RefinementKind {
    /// Arbitrary boolean predicate expressed as CCL.
    Predicate(Rc<RefCell<TypedExpr>>),
}
```

---

## Source injection

Sources need to be available to all stages of compilation, so they are tracked in a `GlobalContext` struct
which produces references to the other types of contexts.

Each phase of compilation needs different information about the sources: lowering needs just the names, inference needs the types, and compilation needs to track the materialized extents so that they are shared across references to the
same source.

## Type inference

`ccl::infer` currently implements a "limited" type inference pass that sits between
lowering and the full bidirectional type checker. It handles enough to make
the existing list-comprehension pipeline work end-to-end. The pass now includes
a full union-find unification table (`UnificationTable` in `ccl::unify`) and records
solved types into it as inference proceeds; a post-inference `resolve` pass replaces
remaining `Infer(id)` placeholders with their solved types.

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
| Needs unification | `UnificationTable` (union-find) present; BinOp/UnaryOp rules implemented via `constrain_equal` | full | Yes |
| Type error reporting | limited | at check sites | at unification failure |

**Delta from our pass to bidirectional**: add a `check(expr, expected, ctx)`
function alongside `infer`; rewrite the Apply rule to check the argument against
the domain. `collect_param_constraint` is still needed for standalone lambdas.
Gains type-mismatch error detection at Apply sites.

**Delta from bidirectional to HM**: `Type::Infer(InferVarId)` already acts as type
variables, and `UnificationTable` is already in place. BinOp and UnaryOp unification rules
are implemented via `constrain_equal`. Remaining steps: an occurs check and removing
`collect_param_constraint` once type variables unify across all use sites.

### `GroupBy` inference

When inferring `Expr::GroupBy { collection, key }`:

1. Infer the type of `collection`.
2. If the collection type has a codomain (i.e. it is a `Fun(_, elem_ty)`), write `elem_ty` into the key lambda's `param.ty` when `param.ty` is still `Type::Hole` or `Type::Infer(_)`. This mirrors the `Apply` rule where the argument type is pushed onto the lambda parameter.
3. Infer the type of `key` (now annotated); take its codomain as `key_output_ty`.
4. Return `Fun(key_output_ty, Fun(Base(UInt), elem_ty))`. Falls back to `Infer(fresh_var)` if either codomain cannot be determined.

### `constrain_equal` — constraint propagation via the UnificationTable

`TypeInferenceContext::constrain_equal(a, b)` unifies two types through the `UnificationTable`:

- Both `Infer`: union the two variables.
- One `Infer`, one concrete: set the variable to the concrete type.
- Either `Error`: no-op (suppress cascades).
- Both concrete and equal: no-op.
- Both concrete and different: `InferError::TypeMismatch`.

This is used by the BinOp and UnaryOp inference rules to propagate constraints across
operands without requiring explicit type annotations.

### BinOp type rules

| Op kind | Operand constraint | Result type |
|---|---|---|
| `Arithmetic` | both operands constrained equal | operand type |
| `Concat` | both operands constrained to `String` | `String` |
| `Compare` | both operands constrained equal | `Bool` |
| `BoolLogic` | both operands constrained to `Bool` | `Bool` |

**Note**: String + String → `Concat` rewriting is performed at **compile time**
(in `lambda_elim.rs`), not at inference time. The inference
pass only constrains both operands to `String` and returns `String` as the result type.

### UnaryOp type rules

| Op kind | Operand constraint | Result type |
|---|---|---|
| `Neg` | operand constrained to `Int` | `Int` |
| `Not` | operand constrained to `Bool` | `Bool` |

### `Case` inference

For each `Branch { guard, body }`: the guard is constrained to `Type::Base(BaseType::Bool)`; body types across all branches are unified via `constrain_equal`. The overall `Case` type is the unified body type. A 0-branch `Case` is a malformed AST (lowering never produces one) and returns `InferError::EmptyCase`.

### Record literals and field access

CHL record literals use Python dict syntax with **bare identifier keys**:

```python
r = {x: 1, y: "hello"}   # Record([("x", 1), ("y", "hello")])
r.x                        # Apply(r, Proj(ProjKey::Field("x"))) → 1
```

**Lowering:**
- `{k: v, ...}` (all keys must be bare `Name` nodes) → `TypedExprNode::Record([(k, v), ...])`.
  Dict literals with non-identifier keys (e.g. string constants) are rejected with `LoweringError::Unsupported`.
- `expr.field` (Python `Attribute`) → `Apply(lower(expr), Proj(ProjKey::Field("field")))`.

**Type inference:** `Record([(k, e), ...])` infers to `Type::Record([(k, T), ...])` where each `T` is
the inferred type of the corresponding value expression — identical in structure to `Tuple` inference.

**Lambda elimination:** `Record(fields)` inside a lambda body is treated identically to `Tuple`:
each field expression is recursively eliminated, producing `Apply(Record([…elim fields…]), Zip)`.
The inner `Record` node carries type `Record([(k, Fun(D,T)), …])` — a record of morphisms — and
the outer `Zip` application fuses them via a shared `FanOut`, producing a morphism to a record.
This ensures `typecheck` invariants hold: a `Record` node always has a `Record` type.

**Operator conversion:** At the `Apply(Record([…]), Zip)` node, the `Zip` handler dispatches on
the argument shape. For a `Record` argument it uses `fan_in_named`, which selects `FanIn::new_named`
(function-tiling inputs) or `ScalarFanIn::new_named` (scalar inputs) and preserves the declared
field names in the output `Tile::Record`. `Proj(ProjKey::Field(name))` compiles to a
`MapResult` using `FunctionDef::RecordField(name)`, extracting the named field from the upstream
record tile — identical in mechanism to `Proj(ProjKey::Index(n))` for tuples.

### `Proj` inference — `PartialTuple` / `PartialRecord` domain types

A bare `Proj(key)` node — i.e. the projection morphism, not an application of it — is
inferred as a function type whose domain is a **partial** structural type:

| Key | Inferred type |
|---|---|
| `Proj(Index(n))` | `PartialTuple([(n, ?a)]) ⇒ ?a` |
| `Proj(Field("x"))` | `PartialRecord([("x", ?a)]) ⇒ ?a` |

`PartialTuple([(n, ?a)])` means "a tuple whose index `n` has type `?a`; all other
positions are unconstrained." This correctly unifies with any concrete `Tuple` of
length ≥ n+1, constraining `?a` to the element type at that index.

`PartialRecord([("x", ?a)])` means "a record that has at least field `"x"` of type
`?a`; all other fields are unconstrained."

**Unification rules** (in `constrain_equal`):

- `PartialTuple ↔ Tuple`: constrain `?a` against `Tuple[n]`. Out-of-bounds index is a `TypeMismatch`.
- `PartialTuple ↔ PartialTuple`: constrain overlapping indices. Non-overlapping entries are left unconstrained (PR 2 will merge them via `set`).
- `PartialRecord ↔ Record`: constrain `?a` against `Record["x"]`. Missing field is a `TypeMismatch`.
- `PartialRecord ↔ PartialRecord`: constrain overlapping fields only.

**Multi-projection accumulation**: `UnificationTable::set` merges `PartialTuple`/`PartialRecord`
entries when called on a variable that is already solved to one of those types. Overlapping
indices/fields are validated via `constrain_equal`; non-overlapping entries are appended.
Additionally, `collect_constraints_into` detects single-entry `PartialTuple` domains from
projection morphisms and emits `TypeConstraint::TupleField` rather than `TypeConstraint::Type`,
so `reconcile_constraints` can merge multiple projections of the same parameter into a
concrete `Tuple` type.

### `Compose` inference

N-ary `Compose([f₀, f₁, …, fₙ₋₁])` is inferred by chaining: each morphism's codomain is constrained equal to the next morphism's domain. The overall type is `Fun(domain(f₀), codomain(fₙ₋₁))`. This case arises when `infer` is run over output from `simplify`, which can produce `Compose` nodes.

### `Type::Union` semantic equality

`typecheck_equal` treats nested union types as structurally flat: `Union(Union(A,B),C)` is equal to `Union(A,B,C)`. This is needed because the `simplify` pass flattens `CollectionUnion` chains (see §Union flattening below), rewriting the domain type from a nested `Union(Union(A,B),C)` to a flat `Union(A,B,C)`, while inference may have stamped the original nested form on surrounding `Let` nodes. The flat-equality rule prevents spurious type mismatches across this normalization.

### Union flattening (`simplify.rs`)

`a @ b @ c` in CHL lowers to right- or left-associated binary `CollectionUnion` applications. The `simplify` pass's `try_flatten_collection_union` rule detects any `CollectionUnion(tuple)` whose tuple contains a nested `CollectionUnion` element, and rewrites it to a flat N-ary `CollectionUnion(a, b, c)`. The domain type is also normalized from `Union(Union(A,B),C)` to `Union(A,B,C)` by `flatten_union_variants`. The rule fires repeatedly until no nested applications remain, so chains of arbitrary depth are fully flattened. `operator_conversion` then compiles the N-ary form directly to a single `UnionOperator` with N inputs.

### `check_fully_typed` validation

After `resolve`, `infer` calls `check_fully_typed(expr)` to assert that every `ty` and every `TypedBinding::ty` in the tree is a concrete type — no `Type::Hole` or `Type::Infer(_)` anywhere, including inside compound types like `Fun` or `Tuple`. Returns `InferError::UnresolvedHole` or `InferError::UnresolvedInfer(id)` on failure, with the symbolic representation of the offending expression for debugging.

### TODOs

- Infer `Let.ty` from the type of `value` (required before `Let` nodes can be compiled; see §Compilation).
- CHL `match` statement lowering: desugar at lowering time using `Let(__scrut)` + guard expressions (no IR changes needed).

---

## Defer / Feed / Define — Deferred Collection Operators (`ccl/remove_defers.rs`)

`defer()`, `<<`, and `<<=` are CHL-level operators that let a block accumulate a result value progressively. They are reified as three CCL AST nodes (`Defer`, `Feed`, `Define`) during lowering, then **eliminated** before operator conversion by `remove_defers::run`.

TODO: `x = defer()` should be replaced with `deferred x` once we implement a custom parser and aren't stuck with CHL parsing rules. 

### CHL syntax

| CHL | Meaning |
|---|---|
| `x = defer()` | Declare `x` as a deferred accumulator |
| `x << value` | Feed `value` into `x` (used in expression position; any number of feeds) |
| `x <<= value` | Define `x` to be exactly `value` (used as a statement; exactly one define) |

A `defer` binding supports **either** feeds or exactly one define — mixing both is an error.

Both the feed and define expressions evaluate to Unit.

### Lowering

`x = defer()` lowers to `let x = Defer in …`.

`x << expr` in expression or statement position lowers to `Feed { name: "x", value: expr }`, wrapped in an `ExprStmt` when it appears as a non-final statement.

`x <<= expr` lowers to `Define { name: "x", value: expr }`, also wrapped in an `ExprStmt`.

The `ExprStmt { expr, body }` node chains a side-effecting statement before the rest of the block:
```
let x = defer
in ExprStmt(Define(x, 1), x)    # x <<= 1; x
```

### Inference

`Defer` gets a fresh `Type::Infer(_)` type — just an unconstrained inference variable. No `DeferredCollectionDomain` is minted at the `Defer` site.

`Feed { name, value }` establishes the shape of the handle via unification:
1. A fresh codomain inference variable `cod = Type::Infer(fresh)` is allocated.
2. If a previous `Feed` on the same handle has already resolved the handle type to `Fun(DeferredCollectionDomain(existing_id), _)`, that `existing_id` is **reused** — the unification table is probed to check whether the handle's inference variable has already been solved. If so, the existing id is extracted; otherwise `next_defer_id()` mints a new one.
3. `constrain_equal(handle_ty, Fun(DeferredCollectionDomain(id), cod))` imposes the function shape on the handle.
4. `constrain_equal(value_ty, cod)` links the feed value's type to the codomain.
5. Returns `Unit`.

The id-reuse in step 2 is what allows multiple `Feed` sites on the same handle to unify correctly. Without it, each feed would mint a fresh `DeferredCollectionDomain(id_N)`, and the two constraints `Fun(DCD(id_0), cod)` and `Fun(DCD(id_1), cod)` would conflict during unification.

`Define { name, value }` constrains `value`'s type against `name`'s full type and returns `Unit`.

`ExprStmt { expr, body }` infers `expr` for constraints, then returns the type of `body`.

### `remove_defers::run` — the elimination pass

The pass runs after `inline` and `lambda_elim`, and before `join_plan`.

**Preconditions on entry** (established by `inline`):

- Every `Defer` is bound by exactly one `Let { bound_expr: Defer, binding, body }`.
- There are no alias chains: any `let y = x` where `x` is a defer-bound name has
  already been inlined by the alias-inlining step in `inline.rs`.
- Nested defer scopes are already lifted: any `let y = (let x = Defer in …) in …`
  has been flattened to `let y = Defer in …` by the defer-returning lift in `inline.rs`.
- `Feed` and `Define` target strings already name the outer defer binding directly
  (not a stale inner name), because `lambda_elim::substitute` renames them when a
  `Var` replacement flows in.

The pass performs three steps:

1. **`inline_defers`**: walks the tree looking for `Let { bound_expr: Defer, binding, body }`. For each such binding it calls `inline_defer(body, binding.name)` to extract the feed or define value:
   - A `Define(name, value)` for the target name is extracted as the define value; its site is replaced with the `__replaced` sentinel.
   - A `Feed(name, value)` for the target name is extracted as a feed value; scalar values (no domain type) are lifted to `value ▷ const` so the result is always a function.
   - **Single feed** (`N = 1`): the extracted value replaces `Defer` directly as the `Let`'s bound expression.
   - **Multiple feeds** (`N > 1`): `construct_feed_result` merges them into `Apply(Tuple([v0, …, vN-1]), Builtin::CollectionUnion)` with result type `Fun(Union(dom0, …, domN-1), dedup(cod0, …, codN-1))`. This is the same shape `operator_conversion` consumes for `a @ b`, so it lowers to a `UnionOperator` without a raw `BinOp` node.

2. **`substitute_types_in_expr`**: propagates any type-variable mappings collected during step 1 (the feed case maps the old `DeferredCollectionDomain` variable to the inferred result domain).

3. **`simplify`**: the `ExprStmt` nodes containing the now-replaced `Feed`/`Define` sentinels (`Var("__replaced")`) are dropped by `try_drop_pure_expr_stmt` since the sentinels contain no remaining `Feed` nodes.

After the pass, no `Defer`, `Feed`, `Define`, or `ExprStmt` nodes should remain in the tree.

---

## Join Planning (`ccl/join_plan.rs`)

`join_plan::run` is an optimization pass that transforms both keyed aggregates and loop joins into efficient implementations.
This pass runs after `lambda_elim` and before the final `simplify` pass.

### Hash Joins

Loop join patterns — where a predicate filters a cartesian product of two or more collections — are converted to hash-join strategies via `create_hash_joins`.

#### Recognised pattern

A refinement predicate is eligible when it is one of:
- A single equality: `(key_a, key_b) ▷ zip ≫ eq`
- An AND of equalities: `(cond_1, …, cond_N) ▷ zip ≫ and` where each `cond_i` has the single form

Each side of the equality conditions must depend on a *single* arm of the input tuple, identified by `is_function_of_single_tuple_arm`.

#### 2-way join

For two arms the transformation is straightforward:
1. **Build side**: group by the build key using `converse` — yielding `key → (build_type → build_type)`
2. **Probe side**: compose the probe key with the build side lookup — yielding `probe_type → (build_type → build_type)`
3. **Materialise**: `▷ uncurry ▷ map_domain` flattens the curried result back to `(probe_type, build_type) → (probe_type, build_type)`, which is the same as what would have come out of the loop join.

#### N-way join planning

For `n ≥ 3` arms `plan_loop_join` constructs a left-deep binary hash-join tree using a five-step algorithm:

1. **Split conditions** (`split_join_conditions`): partition the conjunction predicate into equality join conditions of the form `(key_a, key_b) ▷ zip ≫ eq` — where each key depends on exactly one arm — and *other predicates* that don't match this form.  For each equality condition, `replace_tuple_project_with_id` strips the tuple projection, leaving a function of just the arm's own type.  Each non-equality predicate is paired with the set of arm indices it references (`collect_arms_used`), so it can be pushed to the right level later.

2. **Build spanning tree** (`spanning_tree_children`): treat each equality condition as an undirected edge `(arm_a, arm_b)` and run BFS from arm 0 over this graph.  Returns `children: Vec<Vec<usize>>` — the BFS spanning tree as an adjacency list — or `None` if the graph is disconnected (some arm has no join path to arm 0).

3. **Build left-deep plan with predicate pushdown** (`build_join_plan`): walk the BFS children recursively, starting from arm 0.  For each child subtree, find a condition that *straddles* the accumulated probe side and the child's subtree, orient it probe/build, and fold it into a `JoinPlan::Hash`.  Any remaining straddling equality conditions become residual predicates at that node.  Non-equality predicates are pushed down greedily: predicates whose required arms are entirely within a child subtree are forwarded into that child's recursive call; predicates whose required arms span the current probe side are applied at the first join node where all required arms are present, after reindexing (`reindex_for_domain`) to match the flat output domain of the current node.  Single-arm predicates that depend only on a leaf arm are pushed all the way into the `JoinPlan::Loop` node's `predicate` field.  Returns `(JoinPlan, arm_order)` where `arm_order[i]` is the canonical arm index at output position `i`.

4. **Emit CCL** (`join_plan_to_expr`): convert the `JoinPlan` tree to a CCL expression bottom-up.
   - `Loop { arms }` → `id` on the tuple type of those arms (or the single arm type)
   - `Hash { probe, build, … }` → the probe/build `converse`/`uncurry`/`map_domain` chain described above.  Additionally, for nested hash joins, we need to convert from the nested 2-tuple structure generated by the join tree back to a flat n-tuple structure, so a new `flatten_domain` combinator is inserted before the `map_domain` as needed.  `flatten_domain` allows for flattening up specific positions of a tuple of tuples.

5. **Restore canonical order**: because BFS visit order depends on the order equality conditions appear in the AND expression, `arm_order` may not be `[0, 1, …, n-1]`.  When it differs, `convert_loop_join` appends `▷ ([perm] ▷ permute_domain) ▷ map_domain`, where `perm[j]` = the position of canonical arm `j` in `arm_order`.  This rewrites the domain from the BFS-induced tuple order back to the original `(T_0, T_1, …, T_{n-1})` order that the rest of the expression expects.

For example, a three way join might end up looking like
```
(arm1 ≫ ((arm3 ≫ arm2 ▷ converse) ▷ uncurry ▷ map_domain ≫ .0 ≫ arm3) ▷ converse) ▷ uncurry ▷ ([1] ▷ flatten_domain) ▷ map_domain ▷ ([0, 2, 1] ▷ permute_domain) ▷ map_domain ≫ join_body
```

#### `JoinPlan` structure

```
JoinPlan::Loop  { arms, predicate }
JoinPlan::Hash  { probe, build,
                  probe_key_idx,  // None if probe is a single-arm leaf
                  probe_key_expr,
                  build_key_idx,  // None if build is a single-arm leaf
                  build_key_expr,
                  predicate }
```

`probe_key_idx` / `build_key_idx` are indices *into the output type of that side's sub-plan*, not into the original tuple.  They are `None` when the respective side is a single-arm `Loop` (no projection needed).  When `Some(i)`, a `Proj(i)` step is inserted before the key expression.

The `predicate` fields correspond to extra predicates that aren't expressable as hash join conditions, and these will be applied using the `Restrict` operator after doing the join logic.

Future work:
1. Support loop joins inside hash joins (today the Loop nodes are always single-arm)
2. Support hash joins inside loop joins.  This will require a new CartesianProduct operator, as currently the only thing that can
do a cartesian product is iterating a type, and this needs to be downstream of nontrivial operators.
3. Bloom filters to optimize joins.  Instead of doing traditional join ordering, we'll do runtime bloom-filter passing as described in https://dl.acm.org/doi/pdf/10.1145/3725283

### Keyed Aggregates

Keyed aggregates are patterns like `sum(x) for x in groupby(xs, key_fn)` where:
- A collection is grouped by a key function
- An aggregation operation is applied to each group
- The pattern iterates first over the key, then over elements within that key's group

### The Optimization

The pass identifies constructs where a `curry` operator is applied to a type with a predicate refinement.
The refinement expresses equality with a key: elements are partitioned when the key function applied
to them equals a particular value. This pattern is rewritten to:

1. Swap the iteration order: instead of iterating both the collection and key together,
   iterate the collection and compute the key for each element
2. Use the `"converse"` combinator to group elements by their key values
3. Apply the aggregation operator to each group

This transformation reduces the domain iteration complexity and allows the runtime to optimize
group-by-key operations using dedicated grouping operators instead of generic iteration.

---

## Lambda Elimination (`ccl/lambda_elim.rs`)

`lambda_elim::run` converts a fully type-inferred CCL expression containing
`Lambda` nodes into a point-free expression of primitive combinators, following
the Cartesian Closed Category (CCC) structure described in
`docs/operational-semantics/lowering.md`.

### Output nodes introduced

| Source form | CCL AST after `lambda_elim` |
|---|---|
| `f ≫ g` | `BinOp { left: f, op: Compose, right: g }` |
| `.n` (projection) | `Proj(ProjKey::Index(n))` |
| `.field` | `Proj(ProjKey::Field("field"))` |
| `a + b` (and other non-compose BinOps) | `Apply { argument: Tuple([a, b]), function: Builtin(BinOp(op)) }` |
| `-x`, `not x` (UnaryOps) | `Apply { argument: x, function: Builtin(Neg) }` |

Non-compose `BinOp` and `UnaryOp` nodes are desugared uniformly to function
application form so that operator conversion can treat all operations as
combinators.  This applies at all levels: inside lambda bodies (via
`elim_lambda`) and at the top level of a program (via `elim_lambdas`).

### Built-in combinators

The output references built-in primitives via the `Builtin` enum carried by
`TypedExprNode::Builtin`. Each variant has a stable display name (matched by
the symbolic printer and used in the historical `Var(...)` rendering):

| Variant | Name | Meaning |
|---|---|---|
| `Builtin::Id` | `id` | identity morphism |
| `Builtin::Apply` | `apply` | function application as a morphism |
| `Builtin::Curry` | `curry` | currying |
| `Builtin::Uncurry` | `uncurry` | uncurrying |
| `Builtin::Const` | `const` | constant lift: `const(c) = λ _ → c` |
| `Builtin::Zip` | `zip` | product/fanout: `zip(f, g) = λ x → (f(x), g(x))`, written `⟨f, g⟩` |
| `Builtin::Map` | `map` | post-composition: `map(g)` applied to a curried function |
| `Builtin::MapDomain` | `map_domain` | domain-to-domain identity stream |
| `Builtin::Compose` | `compose` | composition as a first-class morphism |
| `Builtin::Restrict` | `restrict` | domain restriction for filtered lambdas |
| `Builtin::Converse` | `converse` | grouping by key |
| `Builtin::PermuteDomain`, `Builtin::FlattenDomain` | `permute_domain`, `flatten_domain` | hash-join domain massaging |
| `Builtin::BinOp(op)` for any `op: BinOpKind` | `add`, `sub`, `eq`, `lt`, `and`, `or`, `concat`, … | every arithmetic / compare / boolean-logic / string-concat binary op (one variant, parameterised by the existing `BinOpKind` so the operator enum has a single source of truth) |
| `Builtin::{Neg,NotFn}` | `neg`, `not_fn` | unary operations |
| `Builtin::{Sum,Max}` | `sum`, `max` | aggregations (fold/reduce) |
| `Builtin::CollectionUnion` | `collection_union` | discriminated-union of N collections; `a @ b` lowers to `Apply(Tuple([a, b]), Builtin(CollectionUnion))` and compiles to a `UnionOperator` tile. Chains like `a @ b @ c` produce nested binary applications; the `simplify` pass flattens these to a single N-ary `CollectionUnion(a, b, c)` with a flat `Type::Union` domain (see §Union flattening). |

Earlier passes encoded these with `TypedExprNode::Var("name")` against magic
strings; downstream pattern matches (`simplify`, `join_plan`,
`operator_conversion`) now switch directly on the `Builtin` variant.

### `zip` encoding

`⟨f, g⟩` (pointwise function pairing) is encoded as:
```
Apply { argument: Tuple([f, g]), function: Builtin(Zip) }
```
There is no dedicated `Zip` AST node; it reuses the existing `Apply` + `Tuple`
+ `Builtin` nodes.

### Feed–Define rename in `substitute`

`substitute(expr, name, replacement)` propagates renaming into `Feed` and `Define`
target strings when the replacement is a `Var`:

```
substitute(Feed("x", v), "x", Var("y"))  →  Feed("y", substitute(v, "x", Var("y")))
substitute(Define("x", v), "x", Var("y"))  →  Define("y", substitute(v, "x", Var("y")))
```

This is essential for the defer-returning lift in `inline.rs`: when the inner
binding `x` is substituted with `Var(y)`, every `Feed("x", …)` and `Define("x", …)`
in the inner body must be renamed to target `y`, or `remove_defers` would fail to
find any feeds on the outer binding. The `is_free` check also accounts for the
name field: `Feed("x", v)` counts `x` as a free variable for early-exit purposes.

### `Let` nodes after rule 7

When the lambda-elimination rule 7 rewrites a `Let` inside a lambda body, the
bound variable changes type from `T` to `ParamTy ⇒ T`. The rewritten `Let` node
has `bound_ty: None` because the old annotation is stale and would be incorrect.

---

## Inlining Pass (`ccl/inline.rs`)

`inline_non_iterable_lambdas` runs **after `infer`** and **before `lambda_elim`**.
It performs three structural rewrites on `Let` bindings, in order:

1. **Alias inlining** — eliminate `let y = x` pure α-renamings.
2. **Defer-returning lift** — merge an inner defer scope into the outer one.
3. **UDF inlining** — substitute call sites for functions over non-iterable domains.

### Motivation

**Scalar UDFs** (e.g. `Fun(Int, Int)`): operator conversion compiles `Let`-bound
expressions independently with `input = None`. For a function whose domain is
scalar, this causes the operator graph to insert an `IterateExtent` for the
domain — which panics at runtime ("Attempted to iterate on infinite Extent")
because base types have no finite enumerable extent.

**List-producing UDFs** (e.g. generator `def`s, `Fun(Fun(UIntRange, Int), Fun(UIntRange, Int))`):
these lower to `λ user_arg → λ __iter_record → body`. If that nested-lambda
shape reaches `lambda_elim` intact, the rule emits a `curry` combinator —
and `operator_conversion.rs` doesn't implement `curry`, so compilation fails
with `unrecognised Var(curry)`.

Inlining at the CCL level threads the call-site argument as `input`, and
beta-reducing the outer lambda strips the user-parameter layer, leaving a single
`__iter_record`-wrapping lambda that matches the list-comprehension shape
`lambda_elim` already handles.

### Alias inlining

When the right-hand side of a `Let` is a plain `Var(x)`, the binding is pure
α-renaming. It is eliminated unconditionally by substituting `x` for the bound
name throughout the body — *unless* `x` is rebound by an inner `let x = …`
node inside that body, which would cause variable capture.

Performing this before `lambda_elim` prevents the let-in-lambda rule from
hoisting such bindings into `const(x)` wrappers that would need to be
recognised and stripped by downstream passes.

### Defer-returning lift

When the right-hand side of a `Let { binding: y, bound_expr, body }` is (after
peeling any leading `ExprStmt` nodes) a defer-returning expression —
`let x = Defer in inner_body` where `inner_body` terminates in `Var(x)`, possibly
via `ExprStmt` and nested `Let` nodes — the pass **lifts** the inner defer to the
outer binding:

```text
let y = (ExprStmt*(let x = Defer in inner_body)) in outer_body
  →  let y = Defer
     in inner_body[x→y]
        with terminal Var(y) replaced by (ExprStmt*(outer_body))
```

The substitution `x → Var(y)` — performed by `lambda_elim::substitute` — also
renames every `Feed("x", …)` and `Define("x", …)` to `Feed("y", …)` and
`Define("y", …)` (see §Lambda Elimination / Feed–Define rename). Any leading
`ExprStmt(Feed("old_param", …))` wrappers produced by beta-reducing a
defer-returning argument are similarly renamed to use `y`.

This rewrite must happen before `lambda_elim` so that the single flattened
`let y = Defer in …` shape enters `remove_defers` cleanly, without the nested
defer scopes that the downstream alias map previously had to reconcile.

### What is inlined (UDF step)

A `Let { binding, bound_expr, body }` is inlined when `should_inline(bound_expr.ty)` returns `true`:

- `bound_expr.ty` is `Fun(domain, codomain)`
- `domain` is **not** iterable — i.e. `is_iterable_domain(domain)` is `false`

`is_iterable_domain` returns `true` for:
- `UIntRange(_)`, `DataSource(_)` — finite, enumerable
- `Tuple(ts)` where **all** components are iterable
- `Record(fields)` where **all** fields are iterable
- `Refinement(inner, _)` inheriting the iterability of `inner`

And `false` for:
- `Base(_)` (Int, String, Bool, etc.) — no finite enumeration of all values
- `Fun(_, _)` as domain — there are infinitely many possible functions of any
  given function type, so it cannot be enumerated. This case covers
  list-producing UDFs whose domain is itself a list-shaped function type.

### Substitution and beta-reduction

At each call site, substitution is paired with beta-reduction of the outer
user-parameter lambda. Apply chains terminating in `Var(name)` participate in
beta-reduction; unrelated `Apply(arg, Lambda)` patterns elsewhere in the tree
are left intact so list-comprehension bodies and scalar BinOp desugaring keep
the structure `lambda_elim` + `simplify` expect.

Multi-arg call-site bodies contain `Apply(Tuple(…), Proj(Index(i)))` (from the
uncurried `__arg_pair.i` references). Those literal-tuple projections are
folded later by `simplify::try_literal_tuple_projection`; this pass leaves
them in place.

After beta-reducing a UDF call, `inline_impl` is re-applied to the result so
that any newly-created `Let` bindings (e.g. from a defer-returning argument)
are also processed by the alias-inlining and lift steps.

### Pipeline position

```
infer   →   inline_non_iterable_lambdas   →   lambda_elim   →   join_plan   →   operator_conversion
```

### Limitations

- **Explicitly curried UDFs used unapplied** (e.g. `let f = λ x → λ y → body in g(f)`):
  `f` is inlined because its domain is non-iterable, but with no call site to
  beta-reduce against the outer lambda survives, lambda-elim emits `curry`, and
  compilation fails with "unsupported Builtin(curry)". Fully-applied curried calls
  (`f(1)(2)`) are fine — beta-reduction collapses both layers. Wiring `curry` in
  `operator_conversion.rs` is the follow-up that closes this gap entirely.
- **Collection UDFs** (domain `UIntRange` or `DataSource`): not inlined; they compile
  correctly via `Memo + FanOut` and benefit from sharing.
- **Body duplication**: a UDF called N times has its body duplicated N times in the
  operator graph. Acceptable for now; only collection-typed UDFs warrant caching.
- **Recursive UDFs**: unsupported (already noted in `operator_conversion.rs`).

---

## Compilation

There are two compilation passes that translate CCL into tile-dataflow operators. 

`interpreter/operator_conversion.rs` converts the λ-free CCL produced by `lambda_elim` + `simplify` into `TileOperator`s.  This process is mostly
a 1:1 correspondence, with each type of object lifted up to apply within a chain of composed terms.

| CCL form | Operator |
|---|---|
| `Compose([f, g, …])` | sequential pipeline: output of each feeds next |
| `zip(f, g)` | `FanIn` over a shared `FanOut`-wrapped domain (via the `fan_in` factory) |
| `zip({k: f, …})` | `fan_in_named` — record-of-morphisms fused via `FanIn::new_named` or `ScalarFanIn::new_named` |
| `id` | identity (pass-through) |
| `const(c)` | `MapResultToConst` |
| `map(g)` | `MapResult` |
| `Proj(Index(n))` | `tuple_field(n)` projection |
| `add`, `sub`, … | `apply_binop` |
| `neg`, `not_fn` | `apply_unaryop` |
| `restrict` | `Restrict` |
| `Lit` | `Constant` scalar |
| `Tuple([…])` | `ScalarFanIn` |
| `List([…])` | `MapResult` over index stream |
| `Source(name)` | data-source operator |
| `Let { binding, … }` | `Memo`-wrapped `FanOut` bound in scope |

End-to-end pipeline tests live in `tests/compilation_pipeline.rs`.

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

**Prerequisite**: `binding.ty` on the `Let` node's `TypedBinding` must be resolved to a concrete type before compilation — the type inference pass fills it from the inferred type of `bound_expr`.

