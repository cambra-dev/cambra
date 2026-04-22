# CCL AST Design

Design decisions for the Cambra Core Language (CCL) abstract syntax tree — the intermediate representation between Python source and the dataflow operator graph.

---

## Overview

CCL is a λ-calculus–based IR. Python source is lowered into CCL, where it is type-inferred and optimized, then compiled to the operator graph for execution.

```
Python source
  → parse          (rustpython_parser)
  → lower          (ccl/lower.rs: Python AST → CCL AST, structural only)
  → infer          (ccl/infer.rs: type inference, converts Hole→Infer and fills ty on every node)
  → resolve        (ccl/unify.rs: substitutes solved Infer vars with concrete types)
  → lambda_elim    (ccl/lambda_elim.rs: Lambda → point-free combinators)
  → inline         (ccl/inline.rs: inline scalar function-typed Let bindings)
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

CCL does not perform variable renaming (α-renaming) as ANF or SSA IRs do. Python reassignment of the same variable (`x = 1; x = 2`) produces nested `Let` bindings that shadow each other:

```
let x = 1
in let x = 2   ← same name, new binding; value evaluated in outer scope
in x
```

The semantics are correct for sequential code — each `Let` evaluates its value expression in the enclosing scope before the new binding takes effect — but the same name may appear at multiple binding sites in the tree.

Rationale: renaming every assignment to a fresh variable would over-normalize the tree for the same reasons strict ANF does, destroying structural information useful for optimization passes.

### Application shape

Function application is a single `Apply(Box<Expr>, Box<Expr>)` node. Single-argument Python calls `f(a)` lower to `Apply(a, Var(f))` directly. Multi-argument Python calls `f(a, b, ...)` lower to `Apply(Tuple([a, b, ...]), Var(f))` — the arguments are tupled so the call shape matches how multi-arg Python lambdas are uncurried at lowering time (see "Python `lambda` expressions" below).

Partial / curried application in CCL itself is still represented by chained `Apply` nodes — `f(x)(y)` in source writes the curry explicitly and lowers to `Apply(Apply(Var(f), x), y)`. This path remains unsupported past operator conversion (no `curry` combinator case yet) and is tracked as follow-up work; in normal Python source, chained applications only arise when users nest lambdas explicitly.

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

Python aggregate calls (`sum(xs)`, `max(xs)`) are lowered directly to `Expr::Aggregate` rather than kept as `Apply(Var("sum"), xs)`. This makes aggregate operations structurally distinct from ordinary function calls, which simplifies:

- Type inference: `infer` can derive the output type from `AggregateKind::output_type(input_element_type)` without needing built-in name resolution.
- Compilation: the compiler dispatches on `Expr::Aggregate` and emits the appropriate aggregate operator without scanning call-site variable names.

`AggregateKind` enumerates the supported operations; each variant carries its own typing rule in `output_type`.

### Python `lambda` expressions — single `Expr::Lambda` (tupled when multi-arg)

Python `lambda` expressions lower to a single `Expr::Lambda`. A single-parameter `lambda x: body` becomes `λ x → body`. A multi-parameter `lambda x, y, ...: body` is **uncurried at lowering**: it becomes `λ __arg_tuple_N → body[x := __arg_tuple_N.0, y := __arg_tuple_N.1, ...]`, a single-parameter lambda whose parameter is a synthetic tuple and whose body has each named argument replaced in-place by a projection of that tuple. `param.ty` starts as `Type::Hole`; inference resolves it (including the tuple arity for the multi-arg case) from the body's projection constraints and the call-site argument type.

Each multi-arg lambda mints a fresh `N` from a counter on `LoweringContext`, so nested multi-arg lambdas (e.g. `lambda x, y: lambda a, b: x + a`) receive distinct tuple-parameter names. Without the unique suffix, an outer substitution that inserts `Var("__arg_tuple")` into an inner lambda's body would be captured by the inner binder; the fresh suffix plus the reserved `__arg_tuple_` prefix (user code cannot bind double-underscore names here) keeps the in-place substitution non-capture-avoiding yet correct.

Rationale for uncurrying: a curried `λ x → λ y → body` lowering would trigger `lambda_elim`'s nested-lambda rule and produce `curry(body)`, which operator conversion cannot compile. Uncurrying at lowering pairs with the tupled call lowering above so that syntactic multi-arg functions compile without any `curry` combinator appearing in the tree. Users who want genuine partial application still write `lambda x: lambda y: ...` or `curry(f)` explicitly — those produce curried types and are tracked as follow-up work.

In-place substitution (rather than wrapping the body in `let xi = __arg_tuple_N.i`) avoids introducing function-typed `Let` nodes that `lambda_elim`'s Let rule would lift to `ParamTy ⇒ T` and compile into zip-of-projections morphisms that current simplification cannot reduce back to a bare morphism.

Restrictions not yet supported (lowering raises `LoweringError::Unsupported`): `*args`, `**kwargs`, keyword-only arguments, and default values.

### `GroupBy` — first-class grouping node

`groupby(collection, key)` calls are lowered directly to `Expr::GroupBy` rather than kept as a nested `Apply`. This makes the grouping operation structurally distinct from ordinary calls, which simplifies:

- **Type inference**: `infer` can propagate the collection's element type onto the key lambda's `param_ty` without needing built-in name resolution.
- **Compilation**: the compiler can dispatch on `Expr::GroupBy` and emit the appropriate group operator without inspecting call-site variable names.

The result type is `Fun(K, Fun(UInt, V))` where `K` is the key type and `V` is the element type. The outer function maps a key to a group; the inner function maps an unsigned index to an element within that group — the same encoding used for lists (`Fun(UIntRange(n), V)`), but with an unbounded `UInt` domain since group sizes are not known statically.

### `Case` only — no `IfThenElse`

Python `if/else`, `elif` chains, and ternary `if` expressions are all lowered to `Case` during Python → CCL lowering. There is no `IfThenElse` node in the CCL AST. `Case` subsumes all multi-way branching.

`Case` holds an ordered list of `Branch { guard, body }` values. Guards are arbitrary `TypedExpr` nodes constrained to `Bool` at inference time; the first truthy guard wins. `elif` chains are **flattened** into a single `Case`: when `lower_if` recurses into the `orelse` block and the result is itself a `Case`, its branches are extended directly rather than nested, so `if c1: … elif c2: … else: …` produces `{ c1 → …; c2 → …; true → … }`. Structural pattern decomposition is represented as `Let` bindings in arm bodies; literal matching is an equality guard expression.

Python `match` statements (planned) will desugar entirely at lowering time: the scrutinee is bound with a fresh `Let(__scrut)` node, then each arm produces a guard (`__scrut == lit` for literal patterns, `Lit(true)` for wildcard/structural) and a body (with `Let` bindings for any captured variable names). No IR changes are needed for `match` support.

### `Join`/`Jump` for loops

Python `while` loops are lowered to explicit `Join`/`Jump` nodes rather than recursive `Lambda`/`Let` combinations.

`Join` defines a labeled loop header with typed parameters (the loop variables). `Jump` is a tail call to a `Join` point, passing updated parameter values. The non-escaping property (jumps are always in tail position, join points cannot be stored or passed as arguments) is enforced by construction.

Rationale: encoding loops as recursive lambdas requires detecting recursive bindings by scanning the tree for forward references. `Join`/`Jump` makes the loop structure explicit, simplifying both the lowering pass and optimization passes targeting iterate/feedback operators.

### Shared literal and operator types

`Literal` and `BinOpKind` are defined in a shared module, not in the interpreter. The CCL IR must not depend on interpreter internals.

### Typed binding sites — `TypedBinding`

All binding sites — `Lambda`, `Join`, and `Let` — use `TypedBinding { name, ty, user_annotation }` rather than separate `name: String` / type fields.

- `ty` starts as `Type::Hole` (lowering placeholder); the inference pass converts it to a registered `Type::Infer` variable at inference entry and fills in the concrete type before compilation.
- `user_annotation` carries an optional user-written type annotation (e.g. from a Python `cast` expression). Inference validates the inferred type against it; if the body provides no usable constraint the annotation is used directly as the param type.

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
    /// have type `Bool`. Python `if/else`, `elif` chains (flattened), and
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

### `check_fully_typed` validation

After `resolve`, `infer` calls `check_fully_typed(expr)` to assert that every `ty` and every `TypedBinding::ty` in the tree is a concrete type — no `Type::Hole` or `Type::Infer(_)` anywhere, including inside compound types like `Fun` or `Tuple`. Returns `InferError::UnresolvedHole` or `InferError::UnresolvedInfer(id)` on failure, with the symbolic representation of the offending expression for debugging.

### TODOs

- Infer `Let.ty` from the type of `value` (required before `Let` nodes can be compiled; see §Compilation).
- Python `match` statement lowering: desugar at lowering time using `Let(__scrut)` + guard expressions (no IR changes needed).

---

## Join Planning (`ccl/join_plan.rs`)

`join_plan::run` is an optimization pass that transforms both keyed aggregates and loop joins into efficient implementations.
This pass runs after `lambda_elim` and before the final `simplify` pass.

### Hash Joins

Loop join patterns (where a predicate filters a cartesian product) are converted to hash-join strategies via `create_hash_joins`.
The transformation rewrites cross-product iteration into a more efficient strategy where:
1. One side builds a lookup table using the `Converse` operator
2. The other side probes that lookup table using nested function application

TODO we need to add an explicit filtering step as part of this logic.

This conversion matches patterns of the form `(x, y) ▷ zip ≫ eq` and determines which element(s) of a tuple
correspond to which key arguments in the refinement predicate.

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

### Implementation details

The pass uses `replace_curried_correlated_refinements` to recursively traverse the expression tree,
identifying and replacing patterns where we have a curry whose argument has a refinement of the form
`(x, y) ▷ zip ≫ eq` where one side depends on the collection and the other on the key function.

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
| `a + b` (and other non-compose BinOps) | `Apply { argument: Tuple([a, b]), function: Var("add") }` |
| `-x`, `not x` (UnaryOps) | `Apply { argument: x, function: Var("neg") }` |

Non-compose `BinOp` and `UnaryOp` nodes are desugared uniformly to function
application form so that operator conversion can treat all operations as
combinators.  This applies at all levels: inside lambda bodies (via
`elim_lambda`) and at the top level of a program (via `elim_lambdas`).

### Built-in combinators

The output references the following `Var` names:

| Name | Meaning |
|---|---|
| `"id"` | identity morphism |
| `"apply"` | function application as a morphism |
| `"curry"` | currying |
| `"uncurry"` | uncurrying |
| `"const"` | constant lift: `const(c) = λ _ → c` |
| `"zip"` | product/fanout: `zip(f, g) = λ x → (f(x), g(x))`, written `⟨f, g⟩` |
| `"map"` | post-composition: `map(g)` applied to a curried function |
| `"compose"` | composition as a first-class morphism |
| `"restrict"` | domain restriction for filtered lambdas |
| `"aggregate"` | fold/reduce |
| `"converse"` | grouping by key |
| `"add"`, `"sub"`, `"mul"`, `"floor_div"` | arithmetic operations |
| `"eq"`, `"neq"`, `"lt"`, `"le"`, `"gt"`, `"ge"` | comparison operations |
| `"and"`, `"or"`, `"xor"`, etc. | boolean operations |
| `"neg"`, `"not_fn"` | unary operations |

### `zip` encoding

`⟨f, g⟩` (pointwise function pairing) is encoded as:
```
Apply { argument: Tuple([f, g]), function: Var("zip") }
```
There is no dedicated `Zip` AST node; it reuses the existing `Apply` + `Tuple` nodes.

### `Let` nodes after rule 7

When the lambda-elimination rule 7 rewrites a `Let` inside a lambda body, the
bound variable changes type from `T` to `ParamTy ⇒ T`. The rewritten `Let` node
has `bound_ty: None` because the old annotation is stale and would be incorrect.

---

## Inlining Pass (`ccl/inline.rs`)

`inline::run` is a pass that runs after `lambda_elim` and before `join_plan`. It
eliminates `Let` bindings whose bound expression has a scalar function type by
substituting the body at every call site and dropping the `Let` wrapper.

### Motivation

Operator conversion compiles `Let`-bound expressions independently, with
`input = None`. When the bound expression is a scalar-to-scalar function (domain
`= Int`, `Bool`, etc.), this causes the operator graph to insert an `IterateExtent`
for the domain — which panics at runtime ("Attempted to iterate on infinite Extent")
because base types have no finite enumerable extent.

Inlining at the CCL level threads the call-site argument as `input`, so
`IterateExtent` is never constructed for the domain.

### What is inlined

A `Let { binding, bound_expr, body }` is inlined when `should_inline(bound_expr.ty)` returns `true`:

- `bound_expr.ty` is `Fun(domain, codomain)`
- `domain` has an **infinite** (non-enumerable) extent — i.e. `is_infinite_domain(domain)` is `true`
- `codomain` is **not** itself `Fun` — a defensive narrowing for explicitly-curried UDFs, not a soundness requirement. Syntactic multi-arg Python lambdas are uncurried to tupled-domain functions at lowering, so they have non-Fun codomains and *do* get inlined here. See the comment on `should_inline` in `inline.rs` for the full rationale.

`is_infinite_domain` returns `true` for:
- `Base(_)` (Int, String, Bool, etc.)
- `Tuple(ts)` where **any** component is infinite (e.g. `(UIntRange(3), Int)`)
- `Record(fields)` where **any** field is infinite — same logic as tuples
- `Refinement(inner, _)` inheriting the finiteness of `inner`

And `false` for:
- `UIntRange(_)`, `DataSource(_)` — finite, enumerable
- `Fun(_, _)` as domain — collection/generator UDFs; treated as out-of-scope

### Pipeline position

```
lambda_elim   →   inline   →   join_plan   →   operator_conversion
```

### Limitations

- **Explicitly curried UDFs** (`lambda x: lambda y: body` in source, or explicit `curry(f)`
  calls): their `bound_expr.ty` has a `Fun` codomain, so `should_inline` returns `false`
  and the Let is left intact. Compilation fails cleanly at the bound expression with
  "unrecognised Var(curry)" — fixing this requires wiring `curry` as a combinator in
  `operator_conversion.rs` (follow-up work). Syntactic multi-arg UDFs (`add = lambda x, y:
  x + y`) are **not** in this category; they're uncurried at lowering and inlined like
  single-arg scalar UDFs.
- **Collection UDFs** (domain `UIntRange` or `DataSource`): not inlined; they compile
  correctly via `Memo + Splitter` and benefit from sharing.
- **Body duplication**: a scalar UDF called N times has its body duplicated N times in the
  operator graph. Acceptable; only collection-typed UDFs warrant caching.
- **Recursive UDFs**: unsupported (already noted in `operator_conversion.rs`).

---

## Compilation

There are two compilation passes that translate CCL into tile-dataflow operators. 

`interpreter/operator_conversion.rs` converts the λ-free CCL produced by `lambda_elim` + `simplify` into `TileOperator`s.  This process is mostly
a 1:1 correspondence, with each type of object lifted up to apply within a chain of composed terms.

| CCL form | Operator |
|---|---|
| `Compose([f, g, …])` | sequential pipeline: output of each feeds next |
| `zip(f, g)` | `Zip` fan-out over a shared `Splitter`-wrapped domain |
| `id` | identity (pass-through) |
| `const(c)` | `MapResultToConst` |
| `map(g)` | `MapResult` |
| `Proj(Index(n))` | `tuple_field(n)` projection |
| `add`, `sub`, … | `apply_binop` |
| `neg`, `not_fn` | `apply_unaryop` |
| `restrict` | `Restrict` |
| `Lit` | `Constant` scalar |
| `Tuple([…])` | `ScalarTuple` |
| `List([…])` | `MapResult` over index stream |
| `Source(name)` | data-source operator |
| `Let { binding, … }` | `Memo`-wrapped `Splitter` bound in scope |

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

