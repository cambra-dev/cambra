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

The level is now incremented when emitting a generalized `let`'s RHS (see §3.1), so variables minted there live at a deeper level and extrude can fire on a genuine level mismatch. Outside generalized lets everything still shares level 0.

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
* **The Cambra position:** Cambra's public `ccl::Type` has no `Type::ForAll`. It uses level-based type variables for *implicit* polymorphism because that is efficient and meshes with the simple-sub solver, and it lowers that polymorphism to concrete code by monomorphizing at use sites — the natural fit for an engine that wants concrete types on every node for codegen. An `identity` that is *let-bound and used at several types* is generalized, then specialized per distinct use type during the coalesce walk (see the roadmap above); one that is *never applied* is dropped (its definition is dead code). At every applied call site the function's domain is fixed to the value flowing in, pinning the type to that site — the monomorphic coalescing rule (see §2, Pass 1). This is a pragmatic choice, not a commitment never to *represent* polymorphism: explicit `∀`/Π types could coexist (the `cast`/`iterate` signatures already point that way — see §1, *Roadmap*).

### Roadmap and Current Prototype Status

**Implemented today:**

* **Let-polymorphism (functions).** A `let` whose RHS is a *function definition* is generalized: the RHS is typed one level deeper, generalized into a `PolyScheme` at the binding site, and instantiated freshly per use. Because Cambra targets fully-monomorphized output, generalization is paired with **monomorphization**, integrated into the coalesce walk (`infer_simple_sub::specialize_use`): a use of a generalized binding is specialized at first visit — clone + `freshen_expr_types`, a two-way pin against the use's *live* instantiation type, and a re-entrant coalesce of the clone — and the binding's `let` rebuilds itself as the chain of demanded specializations. Specialization is keyed on the *resolved* type, so same-typed uses **share** one definition. So `def f(x): x == x; f(1); f("foo")` type-checks and runs, a generator used at two element types compiles to two cached specializations (see F2), and a generalized UDF used only inside *another* generalized definition (poly-calls-poly) specializes by plain recursion — its use becomes concrete inside each wrapper clone's re-entrant walk. Levels are live (extrude fires on a genuine level mismatch).
* **Tagged variants.** The dual of records, natively supporting sum types and pattern-match exhaustiveness inside the structural solver (see §4). Both named (`.Tag(...)`) and positional (`++`-style) sums are handled.
* **Lattice-carried refinements.** Refinement tags ride the lattice natively (compared by structural predicate equality) rather than being stitched on by a post-pass; see §4 and [`crate::ccl::simple_sub`]'s `# Refinements`.
* **Dependent refinements (Pi types).** Refinement predicates may close over an outer binder; `Type::Fun` carries an optional Pi binder, the solver derives binder correspondences when constraining function types, and dependent application discharges the binder to its argument at coalesce. Group-by lookup `groupby(xs, key)(𝑘₀)` types as `{𝑖 | 𝑖 ▷ xs ▷ key == 𝑘₀} ⇒ 𝑉`. See §4.5.

**Implicit polymorphism, not `Type::ForAll`.** Cambra's `ccl::Type` has no `Type::ForAll`. The choice is *pragmatic*, not a philosophical ban on representing polymorphism: level-based type variables give implicit polymorphism that is efficient and meshes with the existing simple-sub solver, and monomorphizing at use sites (integrated into the coalesce walk, above) is the natural way to lower it to the concrete-typed output codegen wants. This does **not** preclude *explicit* `∀`/Π types — the `cast` and `iterate` signatures in the pi-types work (`cast : (𝑇: Type) ⇒ {𝑈: Type | 𝑈 <: 𝑇} ⇒ 𝑇`) are quantified over `Type`, i.e. `∀`/Π under another name — and the two may well coexist. Implicit level-based polymorphism is simply the most natural mechanism for the inference engine *today*.

A separate question is the contravariant-domain coalescing in §2. Earlier notes framed it as a temporary hack pending a `Type::ForAll`; that framing was wrong. It implements the **monomorphic coalescing rule** for contravariant domain vars (a function domain is negative, so an argument flowing in lands in the var's *lower* bounds, which negative coalesce can't read), and has two parts: the opposite-polarity fallback (the coalesce-time *read* of a var's own lower bound) and the per-morphism domain specialization in `coalesce_node` (which *recovers* a projection's or lambda's domain structurally from the value flowing in, since the fallback cannot reach `Infer`s buried inside a tuple/record). The latter replaced the emit-time reverse Apply edges (now retired — see §2). What lets these mechanisms be sound is that every variable reaching coalesce is **monomorphically determined** — pinned to one type by its uses, or its bounds collide into an `IncompatibleBounds` error — never silently mis-typed (this invariant predates let-polymorphism; it is the structural-collision check). Let-polymorphism's contribution was **expressiveness** — a multi-type *function* program that previously erred now compiles — not making the fallback sound.

**Not yet implemented:**

* **Explicit quantification (`∀`/Π types).** Explicit `∀`/Π types as a first-class `Type` for the cases implicit level-based polymorphism cannot express. Does not block today's coverage; a natural next step. (The once-anticipated companion item — a general two-sided `Var <: Var` rule to retire the reverse Apply edges — turned out to be the *wrong* mechanism: it over-propagates and corrupts mutually-bounded-but-distinct join vars. The reverse edges were instead retired by *local* per-morphism domain specialization; see §2.)
* **SMT-backed refinements.** Augmenting the lattice-carried refinement tags (today compared by structural equality only) with logical payloads (e.g. `v > 0`) reasoned about — implication, not just equality — by an external SMT solver such as Z3.

*(There are parallel workstreams planned, such as a separate nominal-type/trait-resolution pass, but the core lattice capabilities revolve around these features.)*

---

## 2. The Two-Pass Pipeline

The inference engine drives the AST through two passes, defined in `infer_simple_sub.rs`, mirroring the academic paper's `typeTerm`/`constrain` and `coalesce` algorithms. Two Cambra-specific mechanisms ride *inside* the coalesce walk rather than as separate passes: binder-slot filling (see Pass 2) and let-polymorphism's per-type specialization (integrated monomorphization — see §3.1).

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

**Apply is one-way; under-determined domains are recovered as use-site specialization.** The `Apply` rule emits only the textbook constraints — the shape edge `constrain(fn_ty, domain ⇒ codomain)` and the argument edge `constrain(arg_ty, domain)` (`arg <: domain`). A function domain is contravariant, so one-way edges leave a *morphism*'s domain var under-determined: a `Proj` only constrains the one field it touches, so `.1` applied to a 2-tuple compacts to `Fun((?, T₁), T₁)` — a field-narrow / `Infer`-laden shape that never resolves — and a lambda's domain only ever receives what its *body* demands (a record narrowed to the fields the body reads, a sparsely-touched tuple shortened). That shape — the value actually flowing in — is recovered **structurally during the coalesce walk** by *monomorphizing the morphism to its input*: `coalesce_node`'s `Apply` arm rewrites a projection's or directly-applied lambda's domain to the resolved argument (and a lambda passed *as* the argument — the higher-order case: `filter`/`groupby` key functions, comprehension lowering — to the function's resolved inner domain), the `Compose` arm to the preceding morphism's codomain, and refinement predicates (the join-filter / cast-target case) recover the same way since `coalesce_type_predicates` runs `coalesce_node` over them (see *Closing the single-sided blind spots*). This is the **closed-form case of use-site specialization** — the same operation `specialize_use` performs for a generalized `let` (specialize to the resolved use type), except the morphism's domain *equals* its input, so it collapses to a single overwrite instead of clone+pin+coalesce. See `infer_simple_sub::specialize_projection_domain` / `specialize_lambda_domain`.

This **retired** two earlier emit-time *reverse* edges. The reverse argument edge, `constrain(domain, arg_ty)`, pre-deposited the same shape on the domain var's upper edge *and* eagerly propagated it across the connected component. The propagation was load-bearing (the local opposite-polarity fallback only *reads* a var's own lower bound; it does not spread shape across vars), but it was the wrong generalization: a **general** two-sided `Var <: Var` propagation rule that would spread it uniformly *corrupts* mutually-bounded-but-distinct join vars (it intersects their record shapes, dropping fields), and is non-terminating without SCC-based coalescing — so it is **not** the replacement. The reverse shape edge, `constrain(domain ⇒ codomain, fn_ty)`, made every application's function shape an *equality*, creating var⇄var cycles linked across call chains — the residual equality mesh that forced the constraint cache to dedup on bare `(lhs, rhs)` pairs (conflating substitution-differing constraints) and blocked a fully one-way solver; what it carried, a lambda parameter's full width, is exactly the lambda half of the recovery above. The replacement for both is the *local* per-morphism recovery, which suffices because projections and direct/argument-position lambdas are the morphisms whose domains coalesce under-determined. Function values reached through *opaque* positions (`Var`-bound functions applied at distant call sites, higher-order `Compose` of vars) are outside the closed-form recovery — the same opaque-vs-direct boundary as dependent application. (Genuine polymorphism is handled separately by generalize + per-type monomorphization — see §1, *Roadmap*.)

### Pass 2: Coalesce and Write-back

The algorithm walks the AST a second time. For each node it takes the `Type` already stored on `expr.ty` (whose `Infer` variables now carry their fully accumulated bounds) and runs it through a three-step pipeline, writing the resolved, variable-free `ccl::Type` back into `expr.ty` in place. The same walk also fills the **binder slots** (which are not any node's `expr.ty`) — see *Closing the single-sided blind spots*, below — and specializes generalized `let`s per distinct resolved use type (integrated monomorphization, §3.1).

The three steps take a `Type` whose `Type::Infer` variables carry mutable lower/upper bound lists and turn it into a flat, per-polarity-position representation that a single concrete type can be read off of:

1. **`compact_type`:** Walks the `Type`, transitively following each variable's bounds at the polarity of its occurrence, and collects everything reachable at a given polarity-position into one flat `CompactType` (the bundle is a `CompactGraph`: the top-level `CompactType` plus a side-table of any recursive-variable definitions). "Compacting" means gathering the scattered bounds that reach a position into a single bag of contributions (variables, atoms, a record shape, a function shape). When two record shapes meet at a position, they merge by polarity: at a **positive** position their fields are *intersected* (a value that is reliably both `{a, b}` and `{a, c}` is only reliably `{a}`); at a **negative** position their fields are *unioned*.
   * *Opposite-polarity fallback:* if walking a variable's polarity-correct bounds yields no concrete structure, the algorithm falls back to the opposite polarity's bounds. This *is* monomorphization's coalesce-time read for a contravariant domain var, recovering its type from its lower bounds. (It handles a *bare* under-determined domain var; a projection's domain, which is a structured tuple/record with `Infer`s inside, is recovered separately by `coalesce_node`'s projection-domain specialization — see §2.) It is **sound** because every variable reaching coalesce is **monomorphically determined** — pinned to one type by its uses, or its bounds collide into `IncompatibleBounds` — never silently mis-typed. (A generalized binding's definition is never coalesced in place; only its per-use *instantiations* and its per-type specialization clones — each pinned to a single resolved use type — reach here.) This invariant, not the absence of polymorphism, is what makes the read safe; it is kept deliberately, not pending a `Type::ForAll`.
2. **`simplify_type`:** Runs polar co-occurrence analysis to keep types from growing exponentially. "Dropping" a variable here means removing it from the contribution bags at its occurrences; the position keeps whatever concrete structure remains, and a position left with no contributions coalesces to `Type::Infer`. Three rules:
   * *Polar-only elimination:* a variable whose every occurrence is at a single polarity carries no information (nothing constrains it from the other side), so it is dropped. A purely-negative variable means the function accepts anything there; a purely-positive one means the caller imposes nothing on it.
   * *Co-occurrence merging:* if variable `v` and variable `w` always occur together at a given polarity (and symmetrically), they carry identical information, so `w` is merged into `v`.
   * *Atomic absorption:* if a concrete atom `A` co-occurs with variable `v` at *both* polarities, `v` is sandwiched between two identical `A` constraints and is redundant, so it is dropped.
   * The pass is currently cosmetic (everything is monomorphic) and becomes load-bearing once let-polymorphism introduces genuine polar asymmetry.
3. **`coalesce_compact`:** Materializes the simplified `CompactGraph` into the final `ccl::Type` by counting the concrete structural contributions (e.g. `Int`, a record, a variant) remaining at each position. Variable contributions never appear in the output — their bounds have already been expanded into the structural bags by `compact_type`.
   * *Zero shapes:* emit a fresh `Type::Infer` placeholder.
   * *Exactly one shape:* emit it as the `ccl::Type`. Records with dense `Index` keys (0..n) become `Type::Tuple`; `Name` keys become `Type::Record`; a *sparse* index product (a gap in the indices, which only an open/under-determined position can produce) coalesces to a fresh `Type::Infer` rather than a concrete product; variant maps preserve their tags and become `Type::Variant`.
   * *Multiple shapes:* if several distinct concrete types survive (e.g. `Int` and `String`) with no tag to discriminate them, throw an `IncompatibleBounds` error — the solver won't invent an anonymous sum from a primitive collision. (A genuinely *tagged* `Variant` is one shape, not a collision.)

### Closing the single-sided blind spots (no separate pass)

Simple-sub's single-sided `Var <: Var` constrain rule leaves a few *structural* blind spots — positions where a variable receives a bound on only one side, so coalesce (which reads the polarity-correct side) can't materialize it. **Refinements are not among them** — they ride the lattice natively (see §4) and coalesce straight onto each node, including the predicate's own sub-expression types. Historically these blind spots were patched by a third, post-coalesce `saturate` pass; that pass has been **retired**, its work absorbed into the solver and the coalesce walk.

**Morphism domains (projections and lambdas) — rebuilt during the coalesce walk (`Apply` and `Compose`).** A morphism's domain appears only at a negative position, and the one-way constraints emitted around it (`fn_ty <: domain ⇒ codomain` and `arg <: domain` at an `Apply`; the adjacency `prev_cod <: next_dom` in a `Compose`) deliver the concrete value flowing in only as a *lower* bound, while the uppers carry just what the morphism's own body demands — so negative-polarity coalesce materializes the narrow body-demand shape. A `Proj`'s domain coalesces field-narrow (e.g. `.0` of a multi-accumulator loop's `step` tuple coalesces to a 1-tuple `(T)` instead of the full `(T, U)`); a lambda's record param narrows to the fields its body touches (`{label}` instead of `{id, label}`), with untouched params left `Infer`.

`coalesce_node` rebuilds it **structurally, after coalescing the children**, via the shared `specialize_projection_domain` / `specialize_lambda_domain`: the `Apply` arm replaces a projection's or directly-applied lambda's domain with the resolved argument (and an argument-position lambda's with the function's resolved inner domain), the `Compose` arm with the preceding morphism's already-resolved codomain (and the chain's own type with `Fun(first.domain, last.codomain)`), and refinement predicates recover the same way through `coalesce_type_predicates`. A lambda's body-usage refinement tags are preserved by re-wrapping them around the new base (deduped by structural `Refinement` equality against tags the input already carries), and its `param.ty` binder slot is re-derived from the rewritten domain (`refresh_lambda_param_slot`). This is **use-site specialization** — the closed-form sibling of `specialize_use`'s per-`let` specialization (the morphism's domain *equals* its input, so it is one overwrite rather than clone+pin+coalesce; see §2). Doing it post-coalesce — rather than recording a reverse bound at emit time — is what keeps it robust: an emit-time bound is recorded against a specific inference variable, and let-polymorphism's monomorphization re-mints those variables (splicing freshened definitions at use sites), so the bound would not follow to the variable the node's recorded type ends up carrying. Reading the resolved shapes directly sidesteps that entirely.

**Binder slots — filled during the coalesce walk (no lexical scope needed).** A `Var` use needs *no* scope lookup: it shares its binder's inference variable — a monomorphic `let` binds verbatim (`instantiate` freshens nothing) so every use coalesces to exactly what the binder coalesces to, and a *generalized* `let`'s uses are rewritten by the walk itself to reference per-type specializations (which does carry a scope — the walk's stack of specialization frames and shadow markers; see §3.1). (The old `saturate` pass walked a lexical scope to re-derive `Var` types; that was redundant. It was load-bearing for only *one* thing, below.)

What the bottom-up `expr.ty` resolution *doesn't* reach is the **binder slots**: a binder carries a type that is not any node's `expr.ty` — a `Lambda`'s `param.ty`, a `Let`'s `binding.ty`, a `Case` pattern's `binding.ty`, a `Loop`'s param slots. Each is resolved explicitly in `coalesce_node`, mirroring its definition:

* **`Lambda` `param.ty`** — derived from the lambda's coalesced domain (so body-usage restriction tags, which are negative-polarity facts visible only in the contravariant domain, survive), and re-derived whenever a parent arm specializes the domain (`refresh_lambda_param_slot`).
* **`Let` `binding.ty`** — the (already-coalesced) bound expression's type. *This is the one slot the old `saturate` pass existed to fill*: emit never constrains the binding slot and the generic `expr.ty` resolution skips it, so without this line a `let`-bound `Var`'s **binder slot** (not its uses) stays `Type::Hole`.
* **`Case` / `Loop` slots** — run through `resolve_var_type` like any `expr.ty`.

Refinement predicates are coalesced by recursing into them (in the `Lambda` arm and `coalesce_type_predicates`); their free variables share the enclosing bindings' vars and coalesce identically, just like ordinary `Var` uses — and their projections recover their domains through the same `Apply`/`Compose` arms (see §2).

### The post-inference check (shared rules)

Inference runs once, up front. But the pipeline re-checks types repeatedly *after* it — after inlining, after lambda-elimination, after join-planning — to confirm each transformation pass left a well-typed tree. Historically this check duplicated the *structural* knowledge of inference (what an `Apply` destructures, how a `Compose` chains, which product a constructor rebuilds) in a second, separately-maintained body of code; only the leaf type-comparison was shared.

That duplication is now collapsed behind the **`Typing` trait**. The per-node structural rules (`emit_apply`, `emit_compose`, `emit_proj`, …) are written *once*, generic over `C: Typing`, and two contexts implement the trait:

* **`SimpleSubContext`** — the emission context (Pass 1). Its hooks generate constraints: `fresh` mints an inference variable, `instantiate` freshens a scheme, `require_sub` calls `constrain_subtype`, `subexpr` recurses emitting onto `expr.ty`.
* **`CheckCtx`** — the post-inference check (`infer_simple_sub::check`). The *same* rules run, but the hooks now *verify* rather than *solve*: `subexpr` returns the child's already-recorded `child.ty` (what inference decided) instead of re-deriving it, `require_sub` confirms a relation the solver should already have established, and a final **reconcile** step checks the rule's reconstructed type against the node's recorded type.

So the two passes share one description of the language's structure; they differ only in whether a rule's obligations are *emitted as constraints* or *checked against the recorded solution*. Adding or changing a structural rule updates both at once. Both contexts treat refinements strictly and identically; see §4 for how the check stays refinement-aware (adjacency flow checks with a `cast` acquisition escape) and why the passes that introduce refined types must keep each node reconstructable.

---

## 3. Surprising Mechanics

Because simple-sub drops HM's union-find equality engine, it behaves in ways that can surprise developers familiar with static typing.

### 3.1 Let-Polymorphism is Freshening (Instantiation)

Vanilla simple-sub makes a `let`-bound function polymorphic by **freshening**: every time a generalized binding is used, the solver copies its type graph, minting fresh variables for that use site. This is ordinary let-generalization/instantiation — the same idea as HM's `∀`-quantification — applied to the bound graph rather than to a syntactic type scheme.

**How Cambra applies this — and then lowers it.** A `let` binding a *function definition* (`should_generalize`) is typed one level deeper (`in_let_rhs`) and generalized into a `PolyScheme` at the binding level (`scoped_let`); each `Var` use then `instantiate`s a fresh copy, exactly the freshening above. Because every pass after inference is monomorphic, the generalized binding is lowered to concrete code **inside the coalesce walk** (integrated monomorphization): the walk carries a scope of *specialization frames* — one per in-scope generalized `let`, plus shadow markers for every other binder — and a use of a generalized binding specializes at first visit (`specialize_use`). By coalesce time the constraint graph is *complete* (emission saw the whole program), so a use's instantiation is fully determined when the bottom-up walk reaches it: the walk resolves it off the live graph, and on a memo miss clones the definition (`freshen_expr_types` freshens an independent copy; `freshen_bound_substs` then renames the suspended-substitution payloads riding the copied bound edges, which the per-type freshen cannot reach), **pins the clone two-way to the use's live instantiation type**, coalesces the clone re-entrantly *in the definition site's scope* (entries pushed between definition and use are suspended, so a same-named binder introduced in between cannot capture the clone's references), renames the use to the specialization's globally-unique `{name}__monoN`, and stamps the specialization's resolved type on it. When the `let`'s body walk completes, the node rebuilds itself as the chain of demanded specializations (`coalesce_generalized_let`), running the §6.2 `let`-closing discharge per spliced layer; a binding never demanded is dropped as dead code. Same-typed uses share one clone — the memo is keyed on the resolved type (stored as the specialization's own resolved type, since a use's tag *cells* canonicalize differently before and after the binding's first specialization — see the cell story below). The definition's own subtree is never coalesced in place: its quantified variables have no use-site bounds, so coalescing it would both produce an under-determined type and overwrite the bound-bearing `InferVar`s the clones freshen from.

Specializing *during* the walk — rather than splicing after it, as the retired post-coalesce `monomorphize` pass did — is load-bearing twice over. First, every parent derives its type from concrete children on the first pass: in particular a parent `Apply`'s dependent-codomain discharge forces against the specialization's resolved predicate cells, so there is no second, graph-unreachable copy of the discharge logic re-deriving parent types after a splice (the retired `rederive_dependent_types`). Second, chained polymorphism (a generalized UDF used only inside *another* generalized definition, poly-calls-poly) needs no special ordering: the inner use is reached only inside an outer clone's re-entrant walk, after that clone's pin has driven the use's instantiation concrete, and the inner binding's frame is still in scope below the outer's. The ordering invariant that makes in-walk specialization sound: **specialization may only add bounds to variables the walk has not yet read** — a use's pin touches its own instantiation variables (read right after, at its own stamp), the clone's fresh variables (read only inside the clone's walk), and otherwise deposits only α-copies of demands the instantiation already made at emit; `coalesce_node`'s `Apply` arm coalesces function before argument to keep even those copies behind the read front. The invariant is **checked explicitly, not just argued**: the walk logs every graph read as a `(var-laden type, resolution)` pair (the snapshot shares the live `InferVar`s), and `assert_reads_stable` re-resolves each against the *final* graph at end of pass, requiring the structural skeleton — bases, ranges, shapes, refinement-layer count, with under-determined positions wildcarded and predicate *content* deferred to `check_scope_valid` / the post-inference reconcile — to be unchanged. A pin that retroactively altered an already-read variable's resolution trips it by name (debug builds; free in release). The contravariant-domain coalescing of §2 — the opposite-polarity fallback plus `coalesce_node`'s per-morphism domain specialization (projections and lambdas) — is the monomorphic coalescing rule for those vars; it is sound because every variable reaching coalesce is monomorphically determined (§1).

**Refinement predicates under monomorphization.** A `Refinement` has no synthetic identity: its identity *is* its shared predicate cell (`Rc<RefCell<Expr>>`), aliased between the syntactic anchor (a `Cast` target, a `user_annotation`) and every tag instantiation/`freshen_above` propagates onto inferred types — including *use-site* types outside the definition. Two aliasing hazards follow. First, a free use of the generalized binding may live *only* inside a predicate (a list-comprehension filter calling a UDF lowers to a cast-target predicate); the coalesce walk reaches such uses because `coalesce_type_predicates` runs `coalesce_node` over every predicate it encounters with the walk's specialization scope live, and the post-inference `inline` pass substitutes inside predicates likewise. Second, the shared cells must not entangle the original with its specializations, so passes **retire** a cell by re-minting it: a pre-coalesce pass *privatizes* each generalized definition's anchor cells (`privatize_generalized_defs` — otherwise coalescing the body's use-site tags would corrupt the only pristine copy), and `freshen_expr_types` *de-aliases* each specialized clone's anchor cells (`dealias_refinement_predicate`). Planning likewise rewrites a predicate cell in place when it normalizes the bare predicate to point-free form at an iteration site (`compile_predicates_in_type`). Every retirement is recorded in a `CellRemap` — retired cell → replacement, keyed by cell address, with the retired `Rc` kept alive in the entry so the key cannot be reused. The remap is consulted in three places: `compact_type` **canonicalizes every tag it collects** through it, *before* forcing the accumulated substitution on the tag — so a type materialized from the bound graph points at the live, specialized (hence resolved) cell, and a dependent discharge never copies a retired cell's never-resolved content; `realias_refinement_tags` re-points tags inside each clone right after freshening; and a final whole-tree sweep at the end of `infer` re-points tags on types that were stamped *before* the relevant specialization existed (a sibling read earlier in the walk than the binding's first use), which also consolidates aliases so planning's in-place predicate rewrites reach every tag of one refinement through one cell. A cell retired more than once (one privatized definition specialized at several use types) keeps its *first* recording, so orphaned use-site tags resolve to the first specialization's anchor — sound because tag *equality* is structural and type-blind (`eq_refinement_predicate`): specializations of one predicate differ only in their inferred-type slots, so they remain one refinement under `==`. Passes that need *occurrence* identity rather than equality (visited sets over shared cells) key on the predicate cell's address (`PredicateCellId`).

Generalization is narrow only in *what* it generalizes: function definitions with a quantifiable variable. Non-function (value) bindings are *not* generalized — they are bound monomorphically and shared, since specializing a value would duplicate it, which the feed/define and join-planning machinery does not tolerate. There is deliberately **no** use-count or generator carve-out: a single-use function generalizes to one specialization (later inlined like any monomorphic def), and a generator/collection-producing UDF generalizes to one specialization *per distinct element type* — which `inline` leaves *cached* (its domain is iterable) rather than duplicating. Levels are genuinely incremented at every generalized let, so extrude is live.

**Refinement predicate representation.** A `Refinement` holds a single field,
a **bare** boolean predicate (`Rc<RefCell<Expr>>`), in which one reserved
implicit binder — `REFINEMENT_BINDER` (`"__elem"`) — is free and ranges over the
refined base type. The refinement *is a binding form*: the predicate references
its own element through that one name, and nested refinements simply shadow it
(a predicate only ever references its *own* element plus enclosing `Fun`-binders,
which carry their own distinct names). Because the binder is a fixed shared name,
refinement equality/hashing is plain structural comparison of the bare predicate
— no α-renaming. Every traversal that descends into a predicate (free-variable
collection, substitution, lambda-elim) treats `REFINEMENT_BINDER` as bound, so
the shared name never captures across nested refinements.

A predicate *function* `p : 𝐷 ⇒ Bool` never lives in a refinement type — only in
a *term* (an `Apply(p, Iterate/Restrict)` argument). In a type it is represented
bare as `__elem ▷ p` (`ccl_utils::bare_predicate_of_fn`; its inverse
`planning::fn_of_bare_predicate` recovers `p` when a term needs the function,
e.g. `make_restrict`).

**Important note on Refinement interior mutability.**
The interior mutability, privatization, `CellMap` machinery etc are
a temporary, undesirable state.  We should not add additional dependencies on this, and we will clean it up soon.  Tracked in
`issues/type-checker-immutable-predicate-terms.md`.  The remaining goal is to
replace the mutable cells with immutable predicate terms (bare `Rc<TypedExpr>`)
and one uniform capture-avoiding substitution over terms and types. (The earlier
plan to α-uniquify binders per the Barendregt convention is superseded: a single
shared implicit binder with shadowing-aware traversals achieves the same
capture-freedom without per-site fresh names.)

Two pieces of the integrated-monomorphization machinery above are debt of this
same kind, retired by that migration rather than permanent structure (both
carry `TODO(vault: type-checker-immutable-predicate-terms)` markers in code):

- **`compact_type`'s tag canonicalization.** It exists only because a clone
  cannot own its predicates without re-celling mutable shared cells, stranding
  tags on retired cells that the `CellRemap` chase re-points before the
  discharge force. With immutable predicate terms a clone's predicates are
  produced by the same substitution that freshens its other slots — no cells
  to retire, no remap to consult — so "the force reads specialized content"
  becomes a property of the clone being a proper substitution instance, not a
  pre-pass.
- **`freshen_bound_substs`.** It exists only because freshening is *split*:
  `freshen_above` walks types, but a bound edge's suspended-discharge payload
  is a *term* whose slots it never reaches, patched by this separate sweep.
  The migration's single substitution over terms *and* types renames the
  payload in the same traversal, and the sweep goes away.

### 3.2 The `InferArena`: who owns inference variables

Recording `α <: β` pushes `Type::Infer(β)` into `α`'s bounds and `Type::Infer(α)` into `β`'s bounds (the shared-`Rc` linkage from §1). Mutual constraints — and self-recursive ones — therefore make each `InferVar` hold a *strong* `Rc` to the others through its `RefCell<InferBounds>`. After Pass 2 overwrites every `expr.ty` with a concrete, variable-free type, these cells become unreachable from the final AST yet keep one another alive: reference counting alone never reclaims the cycle, so the entire variable graph would leak after each `infer()` run.

**`InferArena` (`ccl::infer.rs`) is the single owner that breaks the cycle.** It retains one strong handle to *every* variable at the moment it is minted (captured through a thread-local mint sink wired into `InferVar::fresh`), and on `Drop` clears each variable's lower/upper bound lists — severing all bound edges so every refcount can reach zero. A flat `Vec` suffices: variables are never looked up by id (the `Type` carries the `Rc` directly), so the arena only enumerates them once, at teardown. Clearing bounds before the `Vec` drops handles self-cycles and N-way cycles uniformly. This is an end-of-inference lifetime invariant implemented as RAII: the arena is created at the top of `infer()` and drops on the `Ok` and error paths alike.

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

A refinement `{T | p}` carries a **set** of refinement tags (each a [`Refinement`]). It is a fourth structural dimension on `CompactType`, width-subtyped exactly like records: **`{b₁ | S₁} <: {b₂ | S₂}` iff `b₁ <: b₂` and `S₂ ⊆ S₁ ∪ tags(b₁)`** — more refinements ⇒ subtype. So `{T | p, q} <: {T | p}` and `{T | p} <: T`, but `{T | q} ⊀ {T | p}`. Tags match by **type-blind structural equality of their predicate terms** (`Refinement`'s `PartialEq` / `eq_refinement_predicate`) — *not* by predicate implication (`{T | x > 0} ⊀ {T | x > -1}`). Structural matching makes tag identity agnostic to *where* a predicate was constructed (join planning re-mints `{D | p}` at every marker it emits — `make_iterate` / `make_restrict` / `refine_with` — and must match the structurally-identical contract recorded elsewhere on the tree) and to in-place type resolution (copies of one predicate along a monomorphization descent line differ only in their inferred-type slots); a pointer-equal predicate cell short-circuits as the fast path, since a refinement that merely flows around shares its cell. The tag set merges with the *same polarity rule as `rec`* (positive ⇒ intersect, negative ⇒ union) and is carried verbatim through simplification (tags are positional, never folded into a variable's identity, so co-occurrence merging can't move or drop them).


A refinement is **required**, so `constrain_subtype` is strict for *concrete* bases: an unrefined concrete value does **not** flow into a refined position (`T ⊀ {T | p}`), and `{T | q} ⊀ {T | p}`. The one subtlety is the `S₂ ⊆ S₁ ∪ tags(b₁)` clause: when the subtype side's base `b₁` is an **inference variable**, it can still acquire the deficit `S₂ \ S₁`, so the solver flows `b₁ <: {b₂ | S₂ \ S₁}` onto the variable rather than rejecting (the refinement analog of how the record/function arms thread structure through a variable base; it fails later iff the variable resolves to a concrete base lacking those tags). This is what lets a value that is *already* refined be cast to acquire a further tag — `{D | p} ⇒ V <: {?a | q} ⇒ V` records `?a <: {D | p}`, stacking `q` over `p` (nested list-comprehension filters). Acquiring a refinement on a *concrete* value is still an *explicit* operation, not subsumption: the explicit `Cast` node from [PR #218](https://github.com/cambra-dev/Cambra/pull/218) (an upcast — `value <: target` — written `cast({D | r} ⇒ V, value)`) makes refinement-acquisition explicit, and the interpreter compiles a refinement on a **collection domain** to a runtime `Restrict`/`Filter` at the iteration boundary (`operator_conversion::iterate_type`). The predicate `Expr` of each tag is inferred/coalesced like any other sub-tree (annotation-borne predicates via `emit_annotation_predicates` / `coalesce_type_predicates`).

**Refinements in the post-inference check.** The post-inference structural check (`infer_simple_sub::check`, reimplemented on the same structural rules as emission via the `Typing` trait — see §2, *The post-inference check*) is **strict and refinement-aware throughout** — it does not strip refinements before its width-subtyping checks (retiring the old blanket strip and its `strip_refinements_deep` TODO). It runs `constrain_subtype` in two places, both fully refinement-aware:

* **Adjacency rules** (a `Compose` link's `prev_cod <: next_dom`, an `Apply`'s argument-vs-domain) check *refinement flow*: feeding an unrefined producer into a refinement consumer is rejected (`T ⊀ {T | p}`), exactly as the solver is. There is **no cast escape** — a producer must already carry the refinement its consumer demands. A `… ≫ (id ≫ cast({D | r} ⇒ V))` chain composes because join planning surfaces the iterated / join-satisfying extent on the *producing* morphism's codomain, so the upstream genuinely supplies `{D | r}` (see the reconstructability bullets below). The producer's tag and the cast's contract are typically re-minted as distinct predicate cells, so the adjacency relies on the structural-predicate match above. (An earlier design peeled the cast's domain refinement in `emit_compose` — `contains_cast` — to admit a bare upstream; that escape masked a join-planning bug where the producer's extent refinement was genuinely dropped, so it has been removed in favour of carrying the refinement through.)
* **The reconcile** (a node's rule-reconstructed type vs the type inference recorded on it) is the plain strict `rule <: recorded` subtype check (the recorded type may be a width-wider supertype — e.g. an annotation).

For the strict reconcile to hold, the passes that *introduce* refined types post-inference (lambda-elim, join-planning) must leave each node's recorded type **reconstructable** — consistent with what the bottom-up rules rebuild from its children. These sites were emitting internally-inconsistent or under-refined nodes and are now fixed at the source rather than papered over by relaxing the check:

* **Iterated / join-satisfying extents on producer codomains** (`planning`'s `set_codomain` / `refine_codomain`). An iteration source produces the refined extent it iterates, so its codomain is the site's refined domain `{D | p} ⇒ {D | p}` (mirroring `make_iterate`'s symmetry); a hash join folds its equi-conditions into the key structure with no residual `Restrict`, so the extent it yields would otherwise reach the body's `cast` *bare*. Surfacing `{D | p}` on the codomain — threaded down the combinator's whole function spine so the leaf builtin the Check pass rebuilds from agrees — keeps the `producer ≫ cast` adjacency refined-to-refined. Reconstructable because a combinator node carries its own function type and `emit_apply` returns *that* codomain verbatim. This is the post-inference counterpart of the inference-time `make_iterate`/`make_restrict`/`refine_with` refinements; trivially-true layers (`if True`) are dropped by the latter but reintroduced from the site domain so the body's `{D | true}` cast still matches.

* **Dependent groupby refinement** (`lambda_elim`'s cast-wrapped-lambda arm). `groupby` lowers to `λ k → cast({I | key(i) == k} ⇒ A, λ i → c(i))`. Because the key binder `k` is now a genuine **Pi binder** (the refinement closes over it but the *value* does not mention it), lambda-elim emits the Pi-const form `const(cast(c)) : (k) ⇒ ({I | i ▷ c ▷ key == k} ⇒ A)` — the `k`-dependence rides the refinement and is materialized as a `Restrict` at the iteration boundary (the dependent-application model, §4.5). This **retired** the former correlated-refinement uncurrying (the nested-Lambda arm's pair-domain rewrite) and its combinator group-by recogniser. Planning's pointful recogniser (`recognize_groupby_sites` / `convert_groupby_pointful`) matches that Pi-const source directly — identifying the key binder structurally as the free variable on one side of the predicate's equality — and emits the bucketize chain `converse(c ≫ key) ≫ map(c)`.
* **`permute_domain` over a refined morphism** (`join_plan::convert_loop_join`). The combinator is polymorphic in the morphism it rearranges; its declared input type is the morphism's *actual* type (which may carry the join-condition refinement), not a bare `actual ⇒ actual`. Otherwise `apply_function` re-stamps the partially-applied combinator's recorded type to `fun(expr.ty, …)` (carrying the refinement) while its inner `PermuteDomain` builtin keeps the bare declaration — an inconsistent node the reconstruction can't rebuild, because the refinement rides the morphism's *invariant* domain⇒codomain position (where subtyping would demand `T <: {T|p}` *and* `{T|p} <: T` at once).

### Flowing In: normalizing annotations

There is no conversion *into* a solver type — the solver consumes `ccl::Type` as-is. The only adjustment Pass 1 makes is `normalize_annotation`, which readies a user annotation / expected type for constraint solving:

* **Holes (`Type::Hole`):** become fresh `Type::Infer` variables at the current level.
* **Refinements:** are **kept** (recursing to normalize the inner) — they ride the lattice as refinement tags (above). A `Refinement(Hole, r)` source annotation thus becomes `Refinement(?fresh, r)`.
* **Everything else** — including existing `Type::Infer` vars, `Tuple`/`Record` products, and `Type::Variant` sums — is kept verbatim and handled by the solver's structural constraint rules. Tuples and records are width-subtyped positionally/by name; variants are admissible at both polarities (the dual of records), so they need no fresh-var indirection.

### Flowing Out: coalescing

Once constraints are resolved (Pass 2), `coalesce_compact` resolves each node's `Type::Infer` variables in place:

* **Products:** dense `Index` keys become `Type::Tuple`; `Name` keys become `Type::Record`; a sparse `Index` product (an open/under-determined position) coalesces to a fresh `Type::Infer` rather than a concrete product.
* **Variants:** materialize into `Type::Variant(Vec<(FieldKey, Type)>)` with tags in `BTreeMap` order. A variant payload sits at a record-field-like position, so it inherits that position's polarity and coalesces by the same rule as a record field value. An all-`Index` variant pretty-prints as a bare `A | B | C`.
* **Refinements:** the refinement-tag set carried at a position is re-wrapped as nested `Type::Refinement` layers around the materialized inner type (in first-insertion order — deterministic and, since consumers strip at all depths, order-independent).
* **Incompatible bounds:** if a variable accumulates multiple distinct concrete primitives (e.g. `Int` and `String`) with no tag to discriminate them, the solver emits an `IncompatibleBounds` error. A *tagged* sum is unaffected — `[.0: Int | .1: String]` is a single `Variant`, not a primitive collision.
* **Recursive types:** simple-sub has no occurs check. With one-way Apply edges a self-application like `λx. x x` produces no cyclic bound graph — it types cleanly (MLsub would give `(α ∧ (α ⇒ β)) ⇒ β`; Cambra drops the unconstrained `α` leg and infers `(?a ⇒ ?b) ⇒ ?c`, an unapplied-lambda type carrying `Infer`s), while *misusing* one (`(λy. y y)(1)`) still fails with `ExpectedFunction`. Should a residual cyclic bound graph ever form, `coalesce_compact` rejects it with a `RecursiveType` error — a defensive check; no current emission path produces one.

---

## 4.5 Dependent refinements via Pi types

Some refinement predicates **close over an outer binder**. The motivating case is group-by: partitioning `xs` by `key_fn` produces, per key `𝑘`, the partition `{𝑖: 𝐼 | 𝑖 ▷ xs ▷ key_fn == 𝑘} ⇒ 𝑉` — the predicate references `𝑘`, bound *outside* the refinement. Expressing, propagating, and discharging such predicates inside the solver is what the Pi-type machinery adds. (This folds in the durable material from `brainstorm/2026-06-02-dependent-refinements-via-pi-types.md`, which remains the point-in-time proposal.)

**Pi types.** `Type::Fun` carries an optional binder: `Fun { name: Option<String>, domain, codomain }`. `name: Some(𝑥)` is the dependent type `(𝑥: domain) ⇒ codomain`, with `𝑥` bound in `codomain`; `name: None` is the ordinary arrow. `emit_lambda` always names the binder from the lambda parameter, so a predicate that closes over the parameter stays bound. The binder is **cosmetic for ordinary functions** — `coalesce_compact_go` keeps it only when the codomain's refinement predicates actually reference it (queried via `subst::type_free_vars`) and strips it otherwise, so monomorphic output is unchanged and equality/printing don't churn.

**Substitutions and contexts (`ccl::subst`).** A `Subst` is a context morphism that maps *term* binders (`Var` names) to replacement `TypedExpr`s. It never rewrites a type variable — that is freshening's job. Two flavours: a **rename** `[𝑘 ↦ 𝑥]` (invertible) and a **discharge** `[𝑥 ↦ arg]` (one-way). `apply_expr`/`apply_type` are capture-avoiding and a true no-op when no substituted binder occurs free in the term's *value* (so a vacuous discharge from a non-dependent application changes nothing — and triggers no spurious α-rename); an occurrence buried in a sub-expression's type slot is out of the substitution contract — neither rewritten nor counted — with the §6.2 scope-validity check guarding the residual. A **context** (`well_formed` / `type_free_vars`) is the dual *checking* device: a type is well-formed iff its predicates' free term-vars are in scope.

**Edges carry substitutions, stored two-sided in their native direction.** Each entry of a variable's bound lists is a `Bound { self_subst, ty, ty_subst }`: an upper entry on `𝑉` reads `𝑉‹self_subst› <: ty‹ty_subst›`, a lower entry `ty‹ty_subst› <: 𝑉‹self_subst›` (both identity for ordinary bounds). `constrain_subtype` delegates to `constrain_go(lhs, rhs, sl, sr, cache)` — each side under its own morphism. The **Fun/Fun arm derives the binder correspondence** `[𝑘 ↦ 𝑥]` onto the lhs side of the codomain edge, and the contravariant domain edge **swaps the two sides** rather than inverting anything. The var arms record edges verbatim — *nothing is inverted at record time*. This is the load-bearing change from the original (holder-context-normalized) convention, which stored upper edges pre-inverted and re-inverted them during closure: a **discharge has no inverse**, so it degraded to the identity twice over and was silently destroyed whenever a consumer edge was recorded before the producer's concrete codomain arrived — exactly the opaque/higher-order application order (O3). Under identity morphisms every arm reduces exactly to the substitution-free solver, so all monomorphic inference is byte-identical.

**Closure chains by bridging holder views, composing forward only.** When a new edge meets a variable's existing opposite edges, the two entries hold `𝑉` under possibly different morphisms (`lo`, `hi`); `bridge_holder_gap` reconciles them by moving whichever side is movable (substitution application is monotone w.r.t. subtyping): equal morphisms need no bridge; an invertible side bridges by `hi ∘ lo⁻¹` (renames only — lossless); two non-invertible composites that share their discharge part and differ only in correspondence renames are factored (`Subst::split_renames`) and bridged on the rename part. Two *distinct* discharges meeting at one variable is the extent-join corner (O1/O4), guarded by `invert_rename`'s panic — the loud tripwire, never a silent drop. The **constraint cache is σ-aware**: it keys each `(lhs, rhs)` pair on the *set of side-morphism pairs* seen, so `g(0)` and `g(1)` flowing into one position record two distinct edges instead of the second being conflated away; termination holds because cyclic (var⇄var) edges carry renames over the episode's finite binder set, whose composites saturate, while discharges ride acyclic content edges.

**Coalesce forces suspended substitutions.** `compact_go` threads a substitution accumulator: descending a bound edge composes the edge's *rendering morphism* (`edge_render_subst`: `ty_subst`, transported across `self_subst` by rename-inversion, or by the identity for a discharge — exact because the content lives in the post-discharge context and cannot mention the discharged binder, debug-asserted) and the composite is applied — *forced* — at each refinement-predicate leaf. A bound reached transitively through `𝑣 → 𝑤 → …` thus arrives with every edge's morphism composed (the deferred transitive closure recovered by the walk). Identity accumulator ⇒ no-op.

**Dependent application.** `Typing::apply` types `f(arg)`. Emit constrains `fn_ty <: (𝑥: 𝑑) ⇒ result` against an expected Pi (the one-way Apply shape edge of §2) and returns `result` under a suspended discharge `[𝑥 ↦ arg]` on a fresh variable's lower edge, fired on the partition predicate at coalesce. So `groupby(xs, key)(𝑘₀)` types as `{𝑖 | 𝑖 ▷ xs ▷ key == 𝑘₀} ⇒ 𝑉`. The **post-inference check** (`CheckCtx::apply`) re-runs the discharge on the resolved codomain so its reconstruction matches; `force_refinement` rewrites the predicate to the same term in both places, so the two refinements compare equal under structural tag equality (§4).

The expected binder is **always globally fresh** (proposal §5.2 verbatim; the §3.6 freshness discipline). The two-sided edge storage is what makes this sound at every polarity and in every constraint order: the correspondence `[𝑘 ↦ 𝑥]` and the discharge `[𝑥 ↦ arg]` compose forward along the closure regardless of whether `fn_ty` was concrete at the apply site or resolved only later (the opaque/higher-order case — a dependent function received as a *parameter* — now discharges correctly, unblocking O3 at the graph level). A contravariant position is reached by side-*swapping*, not inversion, so the discharge arrives at a `map`/aggregate's parameter domain intact. An earlier revision instead **reused** a concrete `fn_ty`'s own binder to force an identity correspondence — a workaround for the inverted-storage convention destroying the discharge on upper edges; both the workaround and the post-coalesce apply-reconstruction that compensated for the opaque case are retired with it. The remaining deferral is the extent-join corner — two *distinct* discharges meeting at one coalescing position (O1/O4) — guarded loudly by the closure bridge's tripwire.

**Discharged-argument slot resolution.** The discharge substitutes the *argument expression* into the predicate; that copy is captured at emit time with inference-variable type slots and is independent of the main AST, so re-coalescing it standalone yields a placeholder var rather than the argument's resolved type. After coalesce, `retype_predicate_slots` stamps each predicate's free `Var` with its binder's already-resolved type (looked up by lexical scope) — the substituted argument is just a reference to an in-scope binder, so its type *is* that binder's type. (This is the monomorphic-direct realization of O2/O7; the full copy-and-freshen-through-the-shared-cache for *polymorphic* refined values, with a refinement-cycle guard, remains for the polymorphic-dependent-function work.)

**`let`-closing (codomain extraction).** A `let 𝑥 = 𝑣 in body` node's type is the body's type, which may close over `𝑥`. As that type is lifted out of the `let`'s scope, `coalesce_node` discharges `[𝑥 ↦ 𝑣]` into it (derived from the body's already-closed type, so chained `let`s close to fixpoint) — the design's `let`-closing refinement-move site. Together with the contravariant discharge above, every coalesced node's type is **well-formed in its lexical scope**, checked unconditionally at the end of inference by `check_scope_valid` (§6.2): a free predicate variable must be bound by an enclosing Pi binder or AST binder, or be a source. A violation is a compiler bug (a substitution-descent miss leaving a dangling predicate binder), reported as an internal `InferError::ScopeViolation` so it surfaces in release builds instead of flowing into planning as a miscompile; the per-substitution `debug_assert`s in `ccl::subst` remain as fast-path regression guards.

**Lambda elimination.** A `λ 𝑥 → e` whose binder is free only in `e`'s *type* (a refinement closes over it) — not its value — eliminates to the **Pi-const** form `const(e) : (𝑥) ⇒ e.ty` (`is_free_in_value` distinguishes the two). This generalizes the former cast-only special case: after the currying/pairing rule rewrites a captured partition predicate onto a pair domain, the residual `λ __pair → <point-free value>` has its binder free only in that refinement.

**Deferred (flagged in code).**
* **O2 (polymorphic case)** — `freshen_above` still shares a refined value's predicate by `Rc` rather than copy-and-freshening its type slots through the shared cache. This is load-bearing only for a *polymorphic* (let-generalized) refined value used at several types, which our monomorphically-introduced refinements never hit; doing it safely needs a refinement-cycle guard. Left for the polymorphic-dependent-function work. (The *monomorphic* slot resolution it would otherwise be needed for is handled by `retype_predicate_slots` above.)
* **O4** — two *different* discharges of one refinement (`g(0)` vs `g(1)`) are distinguished once forced — `force_refinement` rewrites the predicate term and tag equality is structural (§4) — but the constraint cache still keys on bare `(lhs, rhs)`, so two such discharges arriving at the *same* variable conflate at the edge level before either is forced (the extent-join corner, O1/O4). A σ-aware cache is tracked separately.

The pipeline passes downstream of inference treat function types structurally and compare modulo the Pi binder (`Type::without_pi_names`). **Refinement-predicate compilation is deferred out of lambda-elim** (proposal §6.3): predicates ride through inference and lambda-elim in their bare pointful form (a bare boolean over the implicit `REFINEMENT_BINDER`), and **planning** compiles them. Order matters: the group-by / hash-join recognizers run *first*, on the bare form — compiling first would destroy the pointful shapes they match (see the pointful-join-recognizers plan) — and `planning::compile_refinement_predicates` then runs the lambda-elim → simplify sub-pipeline on each remaining predicate (keyed by predicate `Rc` identity) before the generic `iterate`/`restrict` lowering consumes it. This is what lets a refined collection — including a group-by over a *filtered* source (`[sum(x) for x in groupby([y+10 for y in xs if y<6], key)]`) — compile to a runtime `Restrict`/`Filter` rather than reaching op-conversion as an un-compiled predicate. Single-key dependent lookups (`sum(groupby(xs, key)(k))`) and the nested filtered-source group-by both run end-to-end with correct values.

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
| **Refinement tag** | Both | A `Type::Refinement(T, r)` carries a refinement tag `r` (a shared predicate-`Expr` cell). A type holds a *set* of tags, width-subtyped like records (more refinements ⇒ subtype; `{T\|p,q} <: {T\|p}`). Tags compare by type-blind structural predicate equality (`Refinement`'s `PartialEq`; pointer-equal cells short-circuit) — not implication. A refinement is *required* — `constrain_subtype` is strict (`T ⊀ {T\|p}`); acquiring one is an explicit runtime `Restrict` at the collection-iteration boundary, not subsumption. |
| **Let Binding Resolution** | Cambra-Specific | Ensuring a `Let` binding's fully resolved type overwrites the type of any `Var` references to it within the let body. |
| **`InferArena`** | Cambra-Specific | The single owner of every inference variable minted during one `infer()` run. Captures each mint through a thread-local sink and, on `Drop`, clears all variables' bounds to break the `Rc` cycles that mutual subtyping constraints form — the end-of-inference cleanup that reference counting alone cannot do. See §3.2. |
| **Pi type** | Both | A `Type::Fun` with `name: Some(𝑥)` — the dependent function type `(𝑥: domain) ⇒ codomain`, with `𝑥` bound in `codomain` and referenceable by nested refinement predicates. `name: None` is the ordinary arrow. See §4.5. |
| **`Subst` / discharge / rename** | Cambra-Specific | A context morphism over *term* binders (`ccl::subst`), riding a constraint edge in a two-sided `Bound { self_subst, ty, ty_subst }` (native direction, never inverted at record time). A **rename** `[𝑘 ↦ 𝑥]` is invertible; a **discharge** `[𝑥 ↦ arg]` (dependent application) is one-way. Composed forward along the closure and the coalesce walk, forced at refinement predicates. See §4.5. |
| **Correspondence** | Both | The binder alignment `[𝑘 ↦ 𝑥]` *derived* by `constrain_go`'s Fun/Fun arm when relating two Pi codomains, carried on the codomain edge so a dependent refinement renames consistently. See §4.5. |

---
[^1]: For example, `def f(x): x` has the Principal Type `a -> a`, and `def map(f, collection): ...` might have the Principal Type `(a -> b) -> [a] -> [b]`, where `[a]` denotes a collection for all `a`.
[^2]: When a function like `def id(x): return x` is generalized into a PolyScheme, type variables minted inside the body are assigned a level numerically higher than the surrounding outer scope's depth — the "cutoff." Variables above the cutoff are strictly local to the function (like `x`'s type, `α`); because they are self-contained they are universally quantified and work for all types. Each call instantiates the scheme by minting a fresh variable for `α`, preventing `id(5)` from colliding with `id("hello")`. Variables at or below the cutoff are free variables captured from the enclosing environment; instantiation passes them by reference so all call sites share the same outer-scope constraints.
