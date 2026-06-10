# Cambra Simple-Sub Type Inference Design Document

This document outlines the design, architecture, and nomenclature of the `simple-sub` algebraic subtyping inference engine implemented in Cambra. It details how the algorithm works, how information flows through the system, and where our implementation intentionally departs from the upstream academic reference—most notably through the introduction of a post-inference "saturation" pass.

A [glossary](#5-glossary) at the end defines every term of art used below. The conceptual walkthrough in §1 introduces each term where it is first needed; the glossary is a quick-reference to consult afterward.

---

## 1. Algorithm Overview

The type inference engine is based on Lionel Parreaux's *Simple Essence of Algebraic Subtyping* (ICFP 2020). It replaces standard Hindley-Milner (HM) biunification with a constraint-graph solver that natively supports subtyping, Principal Types (the most general type for each term)[^1], and structural records.

Instead of generating equality constraints and resolving them via unification, the simple-sub algorithm generates directional subtyping constraints written `constrain(lhs, rhs)`, read as "`lhs` must be a subtype of `rhs`" (`lhs <: rhs`). The CCL AST is traversed; each node emits a `ccl::Type` and constrains the resulting types against their expected positions. The solver operates **directly on `ccl::Type`** — there is no separate internal type representation; an inference unknown is a `Type::Infer` carrying mutable bounds (see below).

### The Core Mechanism: Bounds and Recursive Constraints

The entire algorithm revolves around managing **bounds** on type variables. "Variable" here always means a *type variable* — an inference unknown the solver is trying to pin down — not a program/term variable. Every unknown type is a `Type::Infer(Rc<InferVar>)`, where the shared `InferVar` carries a `level`, a stable identity (`uid`), and a `RefCell` of **lower bounds** and **upper bounds**. Because the `InferVar` is shared by `Rc`, recording a bound at one occurrence is immediately visible at every other occurrence of the same variable.

The bound lists are populated by the `constrain` rule, which is where the informal phrase "a type flows into a variable" gets its precise meaning. When a term `x` is used in a position whose expected type is `T`, the solver emits `constrain(type(x), T)`:

* If `T` is a type variable `α`, then `constrain(type(x), α)` records `type(x)` as a **lower bound** of `α`. We say `type(x)` *flows into* `α`: a concrete type has arrived at `α` from below (`type(x) <: α`).
* If `type(x)` is a type variable `β` and `T` is concrete, then `constrain(β, T)` records `T` as an **upper bound** of `β`. We say `β` *must flow into* `T`: `β` is required to be usable wherever a `T` is expected (`β <: T`).

So the two bound lists are just the two sides of recorded subtype facts:

* **Lower bound of `α`:** a type `L` with `L <: α`. (Equivalently: every value of type `L` is a valid value of type `α`.)
* **Upper bound of `α`:** a type `U` with `α <: U`. (Equivalently: every value of type `α` is a valid value of type `U`.)

When a new constraint involves a variable, the solver records the bound and then **recursively propagates** it to maintain transitivity. The propagation is symmetric across the two variable cases:

* **LHS is a variable** — `constrain(Var, rhs)`: add `rhs` to `Var`'s upper bounds, then for each existing lower bound `ℓ` of `Var`, recurse `constrain(ℓ, rhs)`. (Everything that already flowed into `Var` must also be valid for `rhs`.)
* **RHS is a variable** — `constrain(lhs, Var)` where `lhs` is not itself a variable: add `lhs` to `Var`'s lower bounds, then for each existing upper bound `u` of `Var`, recurse `constrain(lhs, u)`. (`lhs` must satisfy everything `Var` is already required to flow into.)

This recursive propagation replaces the traditional "union-find" algorithm used in HM type inference.

Note that propagation only sweeps the *existing* bounds on the side of the new bound — it does not eagerly transfer the other side's bounds onto the variable. For a variable-against-variable constraint `constrain(Var v, Var w)`, the LHS-variable arm fires (recording `w` as an upper bound of `v` and sweeping `v`'s lower bounds); the missing edges are recovered later by walking the bounds graph during simplification. Whether this one-sided handling is purely a redundancy-avoidance optimization or is semantically load-bearing is noted as an open question in the review thread.

### Positions and Polarity

A **position** is a location within a type expression where another type sits. In `A → B`, both `A` (the domain) and `B` (the codomain) are positions; in `{x: T, …}`, each field value is a position. Each position has a **polarity** — positive or negative — determined by how it is reached from the outermost type:

* codomains preserve the current polarity,
* domains flip it,
* record/tuple field values preserve it.

The outermost type starts positive. So in `(A → B) → C`, the argument type `A` lands at a **positive** position: it sits inside the domain of a domain — two flips back to positive. Polarity is therefore *not* the same as "looks like an input vs. an output at the surface"; it is a property of the path to the position.

Traditional subtyping models materialize explicit Union (`⊔`) and Intersection (`⊓`) types. Simple-sub avoids constructing these inside the solver by leaning on polarity:

* **Positive positions (outputs/results):** values the program produces. When a variable appears at a positive position, the type at that position is the *union* of its lower bounds. For example, if a function may return `Int` or `String`, the return variable has lower bounds `[Int, String]`, materializing to `Int ⊔ String`.
* **Negative positions (inputs/arguments):** requirements imposed by a consumer. When a variable appears at a negative position, the type at that position is the *intersection* of its upper bounds. For example, a parameter passed to two functions expecting `Int` and `String` respectively has upper bounds `[Int, String]`, materializing to `Int ⊓ String` — the value must satisfy both.

Because lower and upper bounds are kept as raw lists rather than materialized union/intersection nodes, the solver never performs lattice arithmetic during inference; that work is deferred to coalesce time (see [Coalescing](#coalescing-from-bounds-to-types)).

### Levels, Schemes, and Let-Polymorphism

To handle polymorphism safely, simple-sub distinguishes variables local to a function (which may take different types at different call sites) from variables belonging to an outer scope (which must stay consistent everywhere). It does this with **levels**, **schemes**, and **extrusion**.

Throughout this doc, **larger level numbers correspond to more deeply nested scopes**. The outermost scope is level 0; each nested `let` body adds 1. When we say "level higher than X" we always mean *numerically larger* — i.e. more deeply nested — never lexically more outer.

* **Levels:** Every type variable is minted with an integer `level` recording the scope depth at which it was created. Outer-scope variables have smaller levels (e.g. `0`); variables minted inside nested `let` bodies have larger levels (e.g. `1`, `2`).
* **Schemes (`PolyScheme`):** A `PolyScheme` records a **cutoff level** equal to the depth of the scope that defined the binding. Variables whose level is numerically *greater* than the cutoff — i.e. minted inside the let body, deeper than the defining scope — are the quantified ones; they get freshened at each use site.[^2] For example, inferring `def id(x): return x` yields a body `α → α` with `α` at level 1; instantiating at level 0 mints a fresh `β`, yielding `β → β`.
* **Extrude:** A **level mismatch** occurs during `constrain(Var v, rhs)` (or the mirror case) when the other side contains a type variable whose level is numerically higher than `v`'s. The fast path that simply appends to `v`'s bounds is gated on `other.level ≤ v.level`, because recording an inner-scope (higher-level) variable directly as a bound of an outer-scope (lower-level) variable would let the inner variable escape its scope — unsound under let-polymorphism. **Extrude** is the recovery path: it walks the offending type and replaces each too-high variable with a fresh proxy at `v`'s level, linked back to the original through the polarity-appropriate bound so subtyping information still flows. The result is a level-clean copy safe to record as a bound of `v`.

In the current prototype every variable is minted at level 0, so no level mismatch ever arises and extrude is a no-op (see §3.1).

### Coalescing: From Bounds to Types

The overview so far produces a graph of variables with bound lists. **Coalescing** is the step that turns that graph back into a concrete `ccl::Type`. Its rule is the polarity mapping made concrete:

* at a **positive** occurrence of a variable, materialize the *union* of its lower bounds;
* at a **negative** occurrence, materialize the *intersection* of its upper bounds.

A variable with no bounds on the materializing side has no concrete content; it coalesces to a fresh `Type::Infer` placeholder. The full materialization runs as a three-step pipeline (`compact_type` → `simplify_type` → `coalesce_compact`) detailed in §2, Pass 2; the rule above is what those steps collectively implement.

### Example: Bounding and Typing

Grounding the theory before moving on, let's see how upper and lower bounds naturally form intersections and unions. We'll infer types for three small Python functions.

**1. Lower bounds become unions (outputs / positive polarity)**

```python
def get_status(is_ready):
    if is_ready:
        return 200     # Type: Int
    else:
        return "Wait"  # Type: String
```

* **Inference:** The `if` condition constrains `is_ready` to `Bool`. The return value is a fresh variable `α`, so the function type is `Bool → α`.
* **Bounds:** The two `return` statements emit `constrain(Int, α)` and `constrain(String, α)`; each adds its type to `α`'s lower-bound list: `α.lower = [Int, String]`.
* **Coalesce:** `α` occupies the return slot — a *positive* position — so its lower bounds materialize as a union.
* **Logical result type:** `Bool → (Int | String)`.

*Current status:* Cambra's prototype raises an `IncompatibleBounds` error here rather than emitting the union (see [§4](#4-information-flow-and-type-mapping) and question Q3 in the review). A positive-position *untagged* union is also not productively *consumable*: an untagged sum has no syntactic discriminator to case-split on (a *tagged* `Variant` does — see §4), and without let-polymorphism there is no way to thread the value through a polymorphic function to delay resolution. The principal type is real but has no productive consumer for an untagged primitive collision — so rejecting it is a coherent choice, not merely a missing feature.

**2. Upper bounds become intersections (inputs / negative polarity)**

```python
def extract_info(user):
    name = capitalize(user.name)  # capitalize() requires a String
    age = math_add(user.age, 1)   # math_add() requires an Int
    return name
```

* **Inference:** The parameter `user` is a fresh variable `β`.
* **Bounds:** Passing `user.name` into `capitalize()` and `user.age` into `math_add()` imposes structural requirements that flow contravariantly back into `β` as upper bounds: `β.upper = [{name: String}, {age: Int}]`.
* **Coalesce:** `β` is an argument supplied by the caller — a *negative* position — so its upper bounds materialize as an intersection. For structural records, the intersection of `{name: String}` and `{age: Int}` is the combined record with both fields.
* **Logical result type:** `{name: String, age: Int} → String`.

**3. Unresolved polymorphism (and Cambra's current limitation)**

```python
def identity(x):
    return x
```

* **Inference:** The parameter `x` is a fresh variable `α`; since the body just returns `x`, the type is `α → α`.
* **Bounds:** `x` is never passed to another function (no upper bounds) and never assigned a concrete value (no lower bounds): `α.lower = []`, `α.upper = []`.
* **Coalesce:** `α` has no concrete atoms. In pure simple-sub this is fine — it is the principal, universally quantified type `∀α. α → α`.
* **The Cambra gap:** Cambra's public `ccl::Type` AST currently lacks a `Type::ForAll`. If `identity` is never applied to a concrete value, `α` coalesces to a bare `Type::Infer` slot. To work around this at call sites, the current prototype uses a "bidirectional apply" hack that forces the function's domain to equal the caller's argument, monomorphizing the type (see §2, Pass 1).

### Roadmap and Current Prototype Status

**Implemented today:**

* **Parity with the legacy HM solver.** `let` bindings are kept strictly monomorphic — every variable is at level 0, making extrude a no-op.
* **Tagged variants.** The dual of records, natively supporting sum types and pattern-match exhaustiveness inside the structural solver (see §4). Both named (`.Tag(...)`) and positional (`++`-style) sums are handled.
* **Lattice-carried refinements.** Refinement tags ride the lattice natively (compared by id) rather than being stitched on by a post-pass; see §4 and [`crate::ccl::simple_sub`]'s `# Refinements`.

**Not yet implemented:**

* **Let-polymorphism.** Introducing a `Type::ForAll` and a monomorphization pass, which together retire the bidirectional-apply hack and the opposite-polarity fallback described below.
* **SMT-backed refinements.** Augmenting the lattice-carried refinement tags (today compared by id only) with logical payloads (e.g. `v > 0`) reasoned about — implication, not just equality — by an external SMT solver such as Z3.

*(There are parallel workstreams planned, such as a separate nominal-type/trait-resolution pass, but the core lattice capabilities revolve around these features.)*

---

## 2. The Three-Pass Pipeline

The inference engine drives the AST through three passes, defined in `infer_simple_sub.rs` and `type_saturate.rs`. The first two mirror the academic paper's `typeTerm`/`constrain` and `coalesce` algorithms; the third is Cambra-specific.

### Pass 1: Constraint Emission

The algorithm walks the AST top-down. It normalizes each node's expected type into a solver-ready `ccl::Type` (via `normalize_annotation`: `Hole` → fresh `Type::Infer`; `Refinement` wrappers are *kept* — they ride the lattice as refinement tags, see §4), generates constraints, and writes each node's resulting `Type` directly onto `expr.ty`.

Because inference variables are shared `Rc<InferVar>`s, constraints emitted *after* a node's type is stored continue to accumulate bounds that remain visible through the stored `Type` — so there is no separate side table; the AST node *is* the record of the node's inferred type.

The constraint rules for the fundamental forms, in language-neutral pseudocode:

```
emit(Apply { function, argument }):
    arg_ty    = emit(argument)
    fn_ty     = emit(function)
    result    = fresh_var()
    constrain(fn_ty, Fun(arg_ty, result))      # fn_ty must accept arg_ty, yield result
    return result

emit(Lambda { param, body }):
    param_ty  = fresh_var()
    bind param.name -> param_ty in scope
    body_ty   = emit(body)
    return Fun(param_ty, body_ty)
```

`constrain(lhs, rhs)` then drives the recursive bound-propagation machinery from §1:

```
constrain(lhs, rhs):
    if lhs == rhs: return
    match (lhs, rhs):
        (Fun(d0, c0), Fun(d1, c1)):
            constrain(d1, d0)        # domains: contravariant (flipped)
            constrain(c0, c1)        # codomains: covariant
        (Record(fs0), Record(fs1)):
            for (k, t1) in fs1:      # width subtyping: every rhs field
                constrain(fs0[k], t1) # must exist in lhs with a compatible type
        (Var v, _):                  # record rhs as an upper bound of v,
            v.upper.push(rhs)        # then re-assert v's existing lower bounds
            for low in v.lower: constrain(low, rhs)
        (_, Var v):                  # record lhs as a lower bound of v,
            v.lower.push(lhs)        # then re-assert v's existing upper bounds
            for up in v.upper: constrain(lhs, up)
        # (level-mismatch arms extrude the offending side and retry; see §1)
```

**The bidirectional-apply hack.** The `Apply` rule above shows only the textbook constraint, `constrain(fn_ty, Fun(arg_ty, result))`. The current implementation additionally emits the *reverse* constraint, `constrain(Fun(arg_ty, result), fn_ty)`. This is a temporary monomorphizing workaround for the missing `Type::ForAll` (§1, example 3): constraining both directions forces the function's domain and the argument to share strict equality, collapsing polymorphism at apply sites the way standard HM does. It is not part of the core algorithm and will be removed once a real monomorphization pass lands alongside let-polymorphism.

### Pass 2: Coalesce and Write-back

The algorithm walks the AST a second time. For each node it takes the `Type` already stored on `expr.ty` (whose `Infer` variables now carry their fully accumulated bounds) and runs it through a three-step pipeline, writing the resolved, variable-free `ccl::Type` back into `expr.ty` in place.

The three steps take a `Type` whose `Type::Infer` variables carry mutable lower/upper bound lists and turn it into a flat, per-polarity-position representation that a single concrete type can be read off of:

1. **`compact_type`:** Walks the `Type`, transitively following each variable's bounds at the polarity of its occurrence, and collects everything reachable at a given polarity-position into one flat `CompactType` (the bundle is a `CompactGraph`: the top-level `CompactType` plus a side-table of any recursive-variable definitions). "Compacting" means gathering the scattered bounds that reach a position into a single bag of contributions (variables, atoms, a record shape, a function shape). When two record shapes meet at a position, they merge by polarity: at a **positive** position their fields are *intersected* (a value that is reliably both `{a, b}` and `{a, c}` is only reliably `{a}`); at a **negative** position their fields are *unioned*.
   * *Implementation hack — opposite-polarity fallback:* if walking a variable's polarity-correct bounds yields no concrete structure, the algorithm falls back to the opposite polarity's bounds. This works around the missing `Type::ForAll`: it is sound while everything is monomorphic (a variable's type is the same at both ends) but breaks let-polymorphism, and will be removed alongside a future monomorphization pass.
2. **`simplify_type`:** Runs polar co-occurrence analysis to keep types from growing exponentially. "Dropping" a variable here means removing it from the contribution bags at its occurrences; the position keeps whatever concrete structure remains, and a position left with no contributions coalesces to `Type::Infer`. Three rules:
   * *Polar-only elimination:* a variable whose every occurrence is at a single polarity carries no information (nothing constrains it from the other side), so it is dropped. A purely-negative variable means the function accepts anything there; a purely-positive one means the caller imposes nothing on it.
   * *Co-occurrence merging:* if variable `v` and variable `w` always occur together at a given polarity (and symmetrically), they carry identical information, so `w` is merged into `v`.
   * *Atomic absorption:* if a concrete atom `A` co-occurs with variable `v` at *both* polarities, `v` is sandwiched between two identical `A` constraints and is redundant, so it is dropped.
   * The pass is currently cosmetic (everything is monomorphic) and becomes load-bearing once let-polymorphism introduces genuine polar asymmetry.
3. **`coalesce_compact`:** Materializes the simplified `CompactGraph` into the final `ccl::Type` by counting the concrete structural contributions (e.g. `Int`, a record, a variant) remaining at each position. Variable contributions never appear in the output — their bounds have already been expanded into the structural bags by `compact_type`.
   * *Zero shapes:* emit a fresh `Type::Infer` placeholder.
   * *Exactly one shape:* emit it as the `ccl::Type`. Records with dense `Index` keys (0..n) become `Type::Tuple`; `Name` keys become `Type::Record`; a *sparse* index product (a gap in the indices, which only an open/under-determined position can produce) coalesces to a fresh `Type::Infer` rather than a concrete product; variant maps preserve their tags and become `Type::Variant`.
   * *Multiple shapes:* if several distinct concrete types survive (e.g. `Int` and `String`) with no tag to discriminate them, throw an `IncompatibleBounds` error — the solver won't invent an anonymous sum from a primitive collision. (A genuinely *tagged* `Variant` is one shape, not a collision.)

### Pass 3: The Saturate Pass (Departure from Upstream)

Simple-sub's single-sided `Var <: Var` constrain rule leaves a couple of *structural* blind spots that a post-coalesce pass (`type_saturate.rs`) patches up. **Refinements are no longer one of them** — they ride the lattice natively (see §4) and coalesce straight onto each node, including the predicate's own sub-expression types.

**Why it's needed.** The solver's `Var <: Var` rule records only one bound side (mirroring upstream `Typer.scala`), so a variable that only ever appears at a negative position — e.g. each `Proj` morphism's domain in a `Compose` chain — coalesces to an under-determined `Type::Infer` rather than the concrete record/tuple flowing in. The same single-sidedness means a `Var` reference and a `Let` binding slot are not automatically reconciled to the binder's resolved type.

**How it works.** The `saturate` pass walks the fully coalesced AST with a lexical scope environment:

* **Lexical Scoping:** `Var` nodes adopt their environment binding's resolved type; the scope is populated by enclosing `Lambda`, `Let`, and `Case` pattern binders (a `Case` pattern's payload type comes from `Pattern::binding.ty`, materialized in Pass 2).
* **Let Binding Resolution:** splices the bound expression's resolved type into both the binding slot and the `Let`'s own `expr.ty`.
* **Compose/Proj domain reconstruction:** replaces each `Proj` morphism's under-determined domain with the preceding morphism's codomain (the actual record/tuple flowing in), and rebuilds the `Compose`'s own `Fun(first.domain, last.codomain)` type.

This pass is an architectural workaround intended to shrink over time; folding the Compose/Proj reconstruction into the solver (e.g. a two-sided `Var <: Var` rule) is the path that retires it.

---

## 3. Surprising Mechanics

Because simple-sub drops HM's union-find equality engine, it behaves in ways that can surprise developers familiar with static typing.

### 3.1 Let-Polymorphism is Freshening (Instantiation)

Vanilla simple-sub makes a `let`-bound function polymorphic by **freshening**: every time a generalized binding is used, the solver copies its type graph, minting fresh variables for that use site. This is ordinary let-generalization/instantiation — the same idea as HM's `∀`-quantification — applied to the bound graph rather than to a syntactic type scheme.

**How Cambra forces monomorphization.** The current prototype does not yet support let-polymorphism. To keep `let` strictly monomorphic it bypasses freshening entirely: every variable is minted at `level = 0` and the level is never incremented. Because all variables share level 0, they are linked by reference into one global constraint graph, so every use site shares a single set of bounds.

---

## 4. Information Flow and Type Mapping

Cambra carries features beyond plain algebraic subtyping (explicit refinements, tagged sums); this section describes how each is represented in the solver and materialized back out.

#### The unified tagged sum

Cambra has **one** sum representation, the **tagged variant** — `Type::Variant(Vec<(FieldKey, Type)>)`. Since the solver works on `ccl::Type` directly, there is no second variant form to convert to: inference, coalescing, and the public AST all use this one type. (Internally, `compact_type` keys its transient `CompactType` bag by `FieldKey`, but that is an implementation detail of compaction, not a separate type.)

Tags are [`FieldKey`]s — the same key type as records/tuples — so a sum can be **named** (`FieldKey::Name`, a source-level `.Tag(...)`) or **anonymous/positional** (`FieldKey::Index`, the dual of a tuple). The formerly-separate untagged `Type::Union` is gone: a positional union `A | B` is simply `Variant([(Index 0, A), (Index 1, B)])`, and the surface `++`/CollectionUnion produces exactly that (see §2's `emit_collection_union`). One constructor, one coalesce path, one width-subtyping rule (the dual of records: a subtype has *fewer* tags).

Two senses of "union" remain distinct:

* ***union of lower bounds*** — the lattice operation at coalesce time (§1, §2); an internal solver operation, not an AST node.
* a **positional `Variant`** — the all-`Index` tagged sum that materializes a `++` collection-union or a user `A | B` annotation.

Inference does not *infer* a multi-atom sum from a primitive collision (it raises `IncompatibleBounds`); positional variants enter only via `++` or a user annotation.

#### Tagged-variant expressions

* **`VariantCtor { tag, payload }`** constructs a singleton `Variant({tag: payload})`; width-subtyping flows it into any consumer expecting a superset of tags.
* **`Case`** is the single dispatch node for both logical (`if`/guard) and structural (variant-tag) matching — see §2's `emit_case`. A structural `Case` carries a scrutinee and branches with `Pattern`s; width-subtyping enforces tag coverage and binds each payload at its per-tag narrowed type.

(`VariantCtor`/structural `Case` have no surface syntax yet, so lowering never emits them; they are exercised by direct AST construction in the variant tests.)

#### Refinements as refinement-tag sets

A refinement `{T | p}` carries a **set** of refinement tags (each a `RefinementId`). It is a fourth structural dimension on `CompactType`, width-subtyped exactly like records: **`{b₁ | S₁} <: {b₂ | S₂}` iff `b₁ <: b₂` and `S₂ ⊆ S₁ ∪ tags(b₁)`** — more refinements ⇒ subtype. So `{T | p, q} <: {T | p}` and `{T | p} <: T`, but `{T | q} ⊀ {T | p}` (tags compare by `id` only — no predicate implication). The tag set merges with the *same polarity rule as `rec`* (positive ⇒ intersect, negative ⇒ union) and is carried verbatim through simplification (tags are positional, never folded into a variable's identity, so co-occurrence merging can't move or drop them).

A refinement is **required**, so `constrain_subtype` is strict for *concrete* bases: an unrefined concrete value does **not** flow into a refined position (`T ⊀ {T | p}`), and `{T | q} ⊀ {T | p}`. The one subtlety is the `S₂ ⊆ S₁ ∪ tags(b₁)` clause: when the subtype side's base `b₁` is an **inference variable**, it can still acquire the deficit `S₂ \ S₁`, so the solver flows `b₁ <: {b₂ | S₂ \ S₁}` onto the variable rather than rejecting (the refinement analog of how the record/function arms thread structure through a variable base; it fails later iff the variable resolves to a concrete base lacking those tags). This is what lets a value that is *already* refined be cast to acquire a further tag — `{D | p} ⇒ V <: {?a | q} ⇒ V` records `?a <: {D | p}`, stacking `q` over `p` (nested list-comprehension filters). Acquiring a refinement on a *concrete* value is still an *explicit* operation, not subsumption: the interpreter compiles a refinement on a **collection domain** to a runtime `Restrict`/`Filter` at the iteration boundary (`operator_conversion::iterate_type`), and the explicit `Cast` node (an upcast: `value <: target`) is where a collection function acquires its domain refinement. The post-inference structural `typecheck` is therefore (for now) deliberately **refinement-blind** (it strips refinements before its width-subtyping checks), because the strict solver already enforces refinement correctness during constraint solving, and a coalesced tag can ride any of several non-canonical positions (a collection's domain, a join's codomain, a whole function) for which no single subtype direction holds. The explicit cast operator from [PR #218](https://github.com/cambra-dev/Cambra/pull/218) makes refinement-acquisition an explicit value-producing node, canonicalizing placement so the post-inference checks can enforce refinements strictly and drop the strip (tracked as a TODO on `strip_refinements_deep`). The predicate `Expr` of each tag is inferred/coalesced like any other sub-tree (annotation-borne predicates via `emit_annotation_predicates` / `coalesce_type_predicates`).

### Flowing In: normalizing annotations

There is no conversion *into* a solver type — the solver consumes `ccl::Type` as-is. The only adjustment Pass 1 makes is `normalize_annotation`, which readies a user annotation / expected type for constraint solving:

* **Holes (`Type::Hole`):** become fresh `Type::Infer` variables at the current level.
* **Refinements:** are **kept** (recursing to normalize the inner) — they ride the lattice as refinement tags (above). A `Refinement(Hole, r)` source annotation thus becomes `Refinement(?fresh, r)`.
* **Everything else** — including existing `Type::Infer` vars, `Tuple`/`Record` products, and `Type::Variant` sums — is kept verbatim and handled by the solver's structural constraint rules. Tuples and records are width-subtyped positionally/by name; variants are admissible at both polarities (the dual of records), so they need no fresh-var indirection.

### Flowing Out: coalescing

Once constraints are resolved (Pass 2), `coalesce_compact` resolves each node's `Type::Infer` variables in place:

* **Products:** dense `Index` keys become `Type::Tuple`; `Name` keys become `Type::Record`; a sparse `Index` product (an open/under-determined position) coalesces to a fresh `Type::Infer` rather than a concrete product.
* **Variants:** materialize into `Type::Variant(Vec<(FieldKey, Type)>)` with tags in `BTreeMap` order. A variant payload sits at a record-field-like position, so it inherits that position's polarity and coalesces by the same rule as a record field value. An all-`Index` variant pretty-prints as a bare `A | B | C`.
* **Refinements:** the refinement-tag set carried at a position is re-wrapped as nested `Type::Refinement` layers around the materialized inner type (in `RefinementId` order — deterministic and, since consumers strip at all depths, order-independent).
* **Incompatible bounds:** if a variable accumulates multiple distinct concrete primitives (e.g. `Int` and `String`) with no tag to discriminate them, the solver emits an `IncompatibleBounds` error. A *tagged* sum is unaffected — `[.0: Int | .1: String]` is a single `Variant`, not a primitive collision.
* **Recursive types:** simple-sub has no occurs check, so a self-application like `λx. x x` types successfully as an infinite recursive type. Because that is almost always a mistake in Cambra, residual cyclic types are explicitly rejected at coalesce time with a `RecursiveType` error.

---

## 5. Glossary

Consult these definitions as needed; each term is introduced in context in §1–§4 above.

| Term | Origin | Definition |
| :--- | :--- | :--- |
| **`Type::Infer` / `InferVar`** | Simple-Sub | An inference unknown. `Type::Infer(Rc<InferVar>)`; the shared `InferVar` carries a stable `uid`, a `level`, and a `RefCell` of lower/upper bounds. The solver works directly on `ccl::Type`, so this *is* the constraint-graph node — there is no separate "SimpleType". |
| **Position** | Simple-Sub | A location within a type expression where another type sits (a function domain/codomain, a record field value). Each position has a polarity determined by its path from the outermost type. |
| **Polarity** | Simple-Sub | Positive or negative. The outermost type is positive; codomains and field values preserve polarity, domains flip it. Variables at positive positions materialize as a union of lower bounds; at negative positions, as an intersection of upper bounds. |
| **Lower Bound** | Simple-Sub | A type `L` recorded on variable `α` such that `L <: α` must hold (a type that "flows into" `α`). At a positive occurrence of `α`, the lower bounds are unioned to form the type at that position. |
| **Upper Bound** | Simple-Sub | A type `U` recorded on variable `α` such that `α <: U` must hold (a type `α` "must flow into"). At a negative occurrence of `α`, the upper bounds are intersected to form the type at that position. |
| **Level** | Simple-Sub | An integer scope depth; larger = more deeply nested. The outer scope is 0; each nested `let` body adds 1. Used to handle let-polymorphism safely. |
| **Level mismatch** | Simple-Sub | During `constrain` involving a variable `v`, the condition that the other side contains a variable whose level is numerically higher than `v`'s. Triggers extrude. |
| **Extrude** | Simple-Sub | On a level mismatch, the process of copying a type down to a target level by replacing each too-high variable with a fresh proxy at that level (linked back via the polarity-appropriate bound), so the constraint can be recorded without leaking inner-scope variables. |
| **Scheme (PolyScheme)** | Simple-Sub | A generalized type with a cutoff level. Variables whose level is numerically greater than the cutoff are quantified; using the scheme *instantiates* (freshens) them at the current level. |
| **CompactType** | Simple-Sub | A flat, per-position bag of contributions (variables, atoms, an optional record shape, an optional function shape, and a refinement-tag set) produced for simplification and co-occurrence analysis. |
| **`CompactGraph`** | Simple-Sub | A top-level `CompactType` plus a side-table of recursive-variable definitions; the intermediate produced by `compact_type` and consumed by `simplify_type` / `coalesce_compact`. |
| **Coalesce** | Simple-Sub | Materializing a `CompactGraph` back into an immutable `ccl::Type`: positive occurrences become a union of lower bounds, negative occurrences an intersection of upper bounds. |
| **`FieldKey`** | Simple-Sub | The shared key for record/tuple fields *and* variant tags: `Index(usize)` for positional (anonymous) keys, `Name(SmolStr)` for named ones. |
| **`Variant` (tagged sum)** | Both | The single sum representation: `Type::Variant`, keyed by [`FieldKey`]. Named tags are source-level `.Tag(...)`; positional (`Index`) tags are anonymous sums (what `++` produces). Width-subtyping is the dual of records (a subtype has *fewer* tags). Subsumes the old untagged `Type::Union`. |
| **`ccl::Type`** | Both | The public, immutable, user-facing AST type — and, since the unification, also the solver's working representation. Inference unknowns are `Type::Infer`; `Hole` is normalized to a fresh var, while `Refinement` is kept and rides the lattice as a refinement tag. |
| **Refinement tag** | Both | A `Type::Refinement(T, r)` carries a refinement tag `r` (a `RefinementId` + predicate `Expr`). A type holds a *set* of tags, width-subtyped like records (more refinements ⇒ subtype; `{T\|p,q} <: {T\|p}`). Tags compare by id only. A refinement is *required* — `constrain_subtype` is strict (`T ⊀ {T\|p}`); acquiring one is an explicit runtime `Restrict` at the collection-iteration boundary, not subsumption. |
| **Saturate** | Cambra-Specific | A Cambra-specific, post-coalesce AST pass that fixes up *structural* blind spots from the single-sided `Var <: Var` rule (lexical Var/Let propagation, Compose/Proj domain reconstruction). It no longer touches refinements — those ride the lattice. A *saturated type* is one that has been through this pass. |
| **Let Binding Resolution** | Cambra-Specific | Ensuring a `Let` binding's fully resolved type overwrites the type of any `Var` references to it within the let body. |

---
[^1]: For example, `def f(x): x` has the Principal Type `a -> a`, and `def map(f, collection): ...` might have the Principal Type `(a -> b) -> [a] -> [b]`, where `[a]` denotes a collection for all `a`.
[^2]: When a function like `def id(x): return x` is generalized into a PolyScheme, type variables minted inside the body are assigned a level numerically higher than the surrounding outer scope's depth — the "cutoff." Variables above the cutoff are strictly local to the function (like `x`'s type, `α`); because they are self-contained they are universally quantified and work for all types. Each call instantiates the scheme by minting a fresh variable for `α`, preventing `id(5)` from colliding with `id("hello")`. Variables at or below the cutoff are free variables captured from the enclosing environment; instantiation passes them by reference so all call sites share the same outer-scope constraints.
