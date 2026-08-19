# Cambra's Inference Algorithm

This document outlines the design, architecture, and nomenclature of Cambra's algebraic-subtyping inference engine. It details how the algorithm works, how information flows through the system, and where our implementation intentionally departs from the upstream academic reference—most notably by carrying refinements on the lattice and folding monomorphization into the coalesce walk.

A [glossary](#7-glossary) at the end defines every term of art used below. The conceptual walkthrough in §1 introduces each term where it is first needed; the glossary is a quick-reference to consult afterward.

---

## 1. Algorithm Overview

The type inference engine is based on Lionel Parreaux's *Simple Essence of Algebraic Subtyping* (ICFP 2020). It replaces standard Hindley-Milner (HM) unification with a constraint-graph solver that natively supports subtyping, Principal Types (the most general type for each term)[^1], and structural records.

Instead of generating equality constraints and resolving them via unification, the algorithm generates directional subtyping constraints written `constrain(lhs, rhs)`, read as "`lhs` must be a subtype of `rhs`" (`lhs <: rhs`). The CCL AST is traversed; each node emits a `ccl::Type` and constrains the resulting types against their expected positions. The solver operates **directly on `ccl::Type`** — there is no separate internal type representation; an inference unknown is a `Type::Infer` carrying mutable bounds (see below).

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

A **position** is a location within a type expression where another type sits. In `A → B`, both `A` (the domain) and `B` (the codomain) are positions; in `{x: T, …}`, each field type is a position. Each position has a **polarity** — positive or negative — determined by how it is reached from the outermost type:

* codomains preserve the current polarity,
* domains flip it,
* record/tuple field values preserve it.

The outermost type starts positive. So in `(A → B) → C`, the argument type `A` lands at a **positive** position: it sits inside the domain of a domain — two flips back to positive. Polarity is therefore *not* the same as "looks like an input vs. an output at the surface"; it is a property of the path to the position.

Traditional subtyping models materialize explicit Union (`⊔`) and Intersection (`⊓`) types. The algorithm avoids constructing these inside the solver by leaning on polarity:

* **Positive positions (outputs/results):** values the program produces. When a variable appears at a positive position, the type at that position is the *union* of its lower bounds. For example, if a function may return `Int` or `String`, the return variable has lower bounds `[Int, String]`, materializing to `Int ⊔ String`.
* **Negative positions (inputs/arguments):** requirements imposed by a consumer. When a variable appears at a negative position, the type at that position is the *intersection* of its upper bounds. For example, a parameter passed to two functions expecting `Int` and `String` respectively has upper bounds `[Int, String]`, materializing to `Int ⊓ String` — the value must satisfy both.

Because lower and upper bounds are kept as raw lists rather than materialized union/intersection nodes, the solver never performs lattice arithmetic during inference; that work is deferred to coalesce time (see [Coalescing](#coalescing-from-bounds-to-types)).

### Levels, Schemes, and Let-Polymorphism

To handle polymorphism safely, the algorithm distinguishes variables local to a function (which may take different types at different call sites) from variables belonging to an outer scope (which must stay consistent everywhere). It does this with **levels**, **schemes**, and **extrusion**.

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

*Current status:* Cambra's prototype raises an `IncompatibleBounds` error here rather than emitting the union (see [§4](#4-information-flow-and-type-mapping) and question Q3 in the review). A positive-position *untagged* union is also not productively *consumable*: an untagged sum has no syntactic discriminator to case-split on (a *tagged* `Variant` does — see §4). The principal type is real but has no productive consumer for an untagged primitive collision — so rejecting it is a coherent choice, not merely a missing feature.

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
* **Coalesce:** `α` has no concrete atoms. In pure algebraic subtyping this is fine — it is the principal, universally quantified type `∀α. α → α`.
* **The Cambra position:** Cambra's public `ccl::Type` has no `Type::ForAll`. It uses level-based type variables for *implicit* polymorphism because that is efficient and meshes with the solver, and it lowers that polymorphism to concrete code by monomorphizing at use sites — the natural fit for an engine that wants concrete types on every node for codegen. An `identity` that is *let-bound and used at several types* is generalized, then specialized per distinct use type during the coalesce walk (see the roadmap above); one that is *never applied* is typechecked and then dropped (its definition is dead code — see [Typechecking a never-called definition](#typechecking-a-never-called-definition)). At every applied call site the function's domain is fixed to the value flowing in, pinning the type to that site — the monomorphic coalescing rule (see §2, Pass 1). This is a pragmatic choice, not a commitment never to *represent* polymorphism: explicit `∀`/Π types could coexist (the `cast`/`iterate` signatures already point that way — see §1, *Roadmap*).

### Roadmap and Current Prototype Status

**Implemented today:**

* **Let-polymorphism (functions).** A `let` whose RHS is a *function definition* is generalized:
  the RHS is typed one level deeper, generalized into a `PolyScheme` at the binding site, and
  instantiated freshly per use. Because Cambra targets fully-monomorphized output, generalization
  is paired with **monomorphization**, integrated into the coalesce walk (`infer::specialize_use`):
  a use of a generalized binding is specialized at first visit — clone +
  `freshen_expr_type_slots`, a two-way pin against the use's *live* instantiation type, and a
  re-entrant coalesce of the clone — and the binding's `let` rebuilds itself as the chain of
  demanded specializations. Specialization is keyed on the use's **instantiation identity** (a
  `SpecKey`, not a resolved type — see [Keying a specialization](#keying-a-specialization)), so
  uses that instantiate the definition identically **share** one definition. So
  `def f(x): x == x; f(1); f("foo")` type-checks and runs, a generator used at two element types
  compiles to two cached specializations (see F2), and a generalized UDF used only inside
  *another* generalized definition (poly-calls-poly) specializes by plain recursion — its use
  becomes concrete inside each wrapper clone's re-entrant walk. Levels are live (extrude fires on
  a genuine level mismatch). A `let` bound to a **collection** is not generalized, whatever its
  RHS looks like — see
  [Generalizing a collection is filter pushdown](#generalizing-a-collection-is-filter-pushdown).
* **Two binder-annotation forms.** Exact `𝑥 : 𝑇` fixes the binder's type; bounded `𝑥 <: 𝑇` infers it under an upper bound. Both apply at `let` and at a function parameter, carried by `Type::BoundedHole` in annotation position and erased by `normalize_annotation`. See [Annotation kinds: exact and bounded](#annotation-kinds-exact-and-bounded).
* **Tagged variants.** The dual of records, natively supporting sum types and pattern-match exhaustiveness inside the structural solver (see §4). Both named (a source-level `` `tag(…) ``) and positional (`++`-style) sums are handled.
* **Lattice-carried refinements.** Refinements ride the lattice natively (compared by structural predicate equality) rather than being stitched on by a post-pass; see §4 and [`crate::ccl::infer::solver`]'s `# Refinements`.
* **Dependent refinements (Pi types).** Refinement predicates may close over an outer binder; `Type::Fun` carries an optional Pi binder, the solver derives binder correspondences when constraining function types, and dependent application discharges the binder to its argument at coalesce. Group-by lookup `groupby(xs, key)(𝑘₀)` types as `{𝑖 | 𝑖 ▷ xs ▷ key == 𝑘₀} ⇒ 𝑉`. See §4.5.

**Implicit polymorphism, not `Type::ForAll`.** Cambra's `ccl::Type` has no `Type::ForAll`. The choice is *pragmatic*, not a philosophical ban on representing polymorphism: level-based type variables give implicit polymorphism that is efficient and meshes with the existing solver, and monomorphizing at use sites (integrated into the coalesce walk, above) is the natural way to lower it to the concrete-typed output codegen wants. This does **not** preclude *explicit* `∀`/Π types — the `cast` and `iterate` signatures in the pi-types work (`cast : (𝑇: Type) ⇒ {𝑈: Type | 𝑈 <: 𝑇} ⇒ 𝑇`) are quantified over `Type`, i.e. `∀`/Π under another name — and the two may well coexist. Implicit level-based polymorphism is simply the most natural mechanism for the inference engine *today*.

**Not yet implemented:**

* **Explicit quantification (`∀`/Π types).** Explicit `∀`/Π types as a first-class `Type` for the cases implicit level-based polymorphism cannot express. Does not block today's coverage; a natural next step.
* **SMT-backed refinements.** Augmenting the lattice-carried refinements (today compared by structural equality only) with logical payloads (e.g. `v > 0`) reasoned about — implication, not just equality — by an external SMT solver such as Z3.

*(There are parallel workstreams planned, such as a separate nominal-type/trait-resolution pass, but the core lattice capabilities revolve around these features.)*

---

## 2. The Two-Pass Pipeline

The inference engine drives the AST through two passes, defined in `ccl/infer/`, mirroring the academic paper's `typeTerm`/`constrain` and `coalesce` algorithms. Two Cambra-specific mechanisms ride *inside* the coalesce walk rather than as separate passes: binder-slot filling (see Pass 2) and let-polymorphism's per-type specialization (integrated monomorphization — see §3.1).

### Pass 1: Constraint Emission

The algorithm walks the AST top-down. It normalizes each node's expected type into a solver-ready `ccl::Type` (via `normalize_annotation`: `Hole` → fresh `Type::Infer`; `Refinement` wrappers are *kept* — they ride the lattice natively, see §4), generates constraints, and writes each node's resulting `Type` directly onto `expr.ty`.

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

#### Apply is one-way

**Under-determined domains are recovered as use-site specialization.** The `Apply` rule emits only the textbook constraints — the shape edge `constrain(fn_ty, domain ⇒ codomain)` and the argument edge `constrain(arg_ty, domain)` (`arg <: domain`). A function domain is contravariant, so one-way edges leave a *morphism*'s domain var under-determined: a `Proj` only constrains the one field it touches, so `.1` applied to a 2-tuple compacts to `Fun((?, T₁), T₁)` — a field-narrow / `Infer`-laden shape that never resolves — and a lambda's domain only ever receives what its *body* demands (a record narrowed to the fields the body reads, a sparsely-touched tuple shortened). That shape — the value actually flowing in — is recovered **structurally during the coalesce walk** by *monomorphizing the morphism to its input*: `coalesce_node`'s `Apply` arm rewrites a projection's or directly-applied lambda's domain to the resolved argument (and a lambda passed *as* the argument — the higher-order case: `filter`/`groupby` key functions, comprehension lowering — to the function's resolved inner domain), the `Compose` arm to the preceding morphism's codomain, and refinement predicates (the join-filter / cast-target case) recover the same way since `coalesce_type_predicates` runs `coalesce_node` over them (see [Closing the single-sided blind spots](#closing-the-single-sided-blind-spots-no-separate-pass)). This is the **closed-form case of use-site specialization** — the same operation `specialize_use` performs for a generalized `let` (specialize to the resolved use type), except the morphism's domain *equals* its input, so it collapses to a single overwrite instead of clone+pin+coalesce. See `infer::specialize_projection_domain` / `specialize_lambda_domain`.

The local per-morphism recovery suffices because projections and direct/argument-position lambdas are the morphisms whose domains coalesce under-determined. Function values reached through *opaque* positions (`Var`-bound functions applied at distant call sites, higher-order `Compose` of vars) are outside the closed-form recovery — the same opaque-vs-direct boundary as dependent application. (Genuine polymorphism is handled separately by generalize + per-type monomorphization — see §1, *Roadmap*.)

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

The solver's single-sided `Var <: Var` constrain rule leaves a few *structural* blind spots — positions where a variable receives a bound on only one side, so coalesce (which reads the polarity-correct side) can't materialize it. **Refinements are not among them** — they ride the lattice natively (see §4) and coalesce straight onto each node, including the predicate's own sub-expression types.

**Morphism domains (projections and lambdas) — rebuilt during the coalesce walk (`Apply` and `Compose`).** A morphism's domain appears only at a negative position, and the one-way constraints emitted around it (`fn_ty <: domain ⇒ codomain` and `arg <: domain` at an `Apply`; the adjacency `prev_cod <: next_dom` in a `Compose`) deliver the concrete value flowing in only as a *lower* bound, while the uppers carry just what the morphism's own body demands — so negative-polarity coalesce materializes the narrow body-demand shape. A `Proj`'s domain coalesces field-narrow (e.g. `.0` of a multi-accumulator loop's `step` tuple coalesces to a 1-tuple `(T)` instead of the full `(T, U)`); a lambda's record param narrows to the fields its body touches (`{label}` instead of `{id, label}`), with untouched params left `Infer`.

`coalesce_node` rebuilds it **structurally, after coalescing the children**, via the shared `specialize_projection_domain` / `specialize_lambda_domain`: the `Apply` arm replaces a projection's or directly-applied lambda's domain with the resolved argument (and an argument-position lambda's with the function's resolved inner domain), the `Compose` arm with the preceding morphism's already-resolved codomain (and the chain's own type with `Fun(first.domain, last.codomain)`), and refinement predicates recover the same way through `coalesce_type_predicates`. A lambda's body-usage refinements are preserved by re-wrapping them around the new base (deduped by structural `Refinement` equality against refinements the input already carries), and its `param.ty` binder slot is re-derived from the rewritten domain (`refresh_lambda_param_slot`). This is **use-site specialization** — the closed-form sibling of `specialize_use`'s per-`let` specialization (the morphism's domain *equals* its input, so it is one overwrite rather than clone+pin+coalesce; see §2). Doing it post-coalesce — rather than recording a reverse bound at emit time — is what keeps it robust: an emit-time bound is recorded against a specific inference variable, and let-polymorphism's monomorphization re-mints those variables (splicing freshened definitions at use sites), so the bound would not follow to the variable the node's recorded type ends up carrying. Reading the resolved shapes directly sidesteps that entirely.

#### The collapse happens at the position

The *bare* under-determined variable — a domain variable that receives only `arg` and nothing else — is the half `specialize_lambda_domain` cannot reassemble, and `compact_go` handles it in place: when a variable's polarity-correct bounds yield no shape, it reads the opposite side instead. The principal type of such a variable is `∀α ⊒ 𝐿. …`, and with no `Type::ForAll` and concrete code to emit, the quantifier collapses to its bound. That elimination is how a structurally-typed position acquires a type at all, in both directions: a domain reading the argument that flows in, and a parameter used only through projections reading the open records its uses demand of it.

A collapse is a *choice*, not a subtyping inference, so it does not propagate along subtyping edges — `𝐿 <: 𝑐` and `𝑎 <: 𝑐` together say nothing about `𝐿` versus `𝑎`. It belongs to the variable whose quantifier is being eliminated: the **position** the walk entered, never one reached by following another variable's bounds, which is why the walk resets its parent path at every structural child. `fallback_allowed` (`src/ccl/infer/solver/compact.rs`) carries the rule and its argument.

**When the polarity-correct walk counts as having answered.** The collapse fires only where that walk found no shape, and a *variant* shape is read differently at the two polarities. Positively it comes off the lower bounds and is the value's own tags — what the thing is — so the collapse has nothing to add, and firing past it would replace the value with its own upper bound (a bounded annotation `𝑥 <: 𝑇` reading back as the binder's type). Negatively it comes off the upper bounds and is the arms a body can *handle*, which is not a determination of what flows in; there the collapse must still fetch the argument, or a domain becomes the sum of everything the `match` accepts. Records and atoms need no such split, being the same claim read from either side.

**Asking the other question.** Because the collapse answers "what must this position be", a caller that needs "what actually reached it" has to suppress the collapse — `compact_type_polarity_only`, the polarity-correct walk alone. The distinction is not academic: an upper bound deposited on a never-inhabited position (the trait-requirement sweep does exactly this) makes the ordinary resolve report a type. [The unobservable-arm pin](#an-unobservable-arm-payload-is-pinned-to-what-its-uses-require) is the caller that must not confuse the two, since a demand is precisely what an unreachable arm can acquire.

**Binder slots — filled during the coalesce walk (no lexical scope needed).** A `Var` use needs *no* scope lookup: it shares its binder's inference variable — a monomorphic `let` binds verbatim (`instantiate` freshens nothing) so every use coalesces to exactly what the binder coalesces to, and a *generalized* `let`'s uses are rewritten by the walk itself to reference per-type specializations (which does carry a scope — the walk's stack of specialization frames and shadow markers; see §3.1).

What the bottom-up `expr.ty` resolution *doesn't* reach is the **binder slots**: a binder carries a type that is not any node's `expr.ty` — a `Lambda`'s `param.ty`, a `Let`'s `binding.ty`, a `Case` pattern's `binding.ty`, a `For`'s target slot. Each is resolved explicitly in `coalesce_node`, mirroring its definition (inference runs before the mutability/transaction phases, so the recurrence carriers `LetRec`/`Transact` never reach coalesce):

* **`Lambda` `param.ty`** — derived from the lambda's coalesced domain (so body-usage restriction refinements, which are negative-polarity facts visible only in the contravariant domain, survive), and re-derived whenever a parent arm specializes the domain (`refresh_lambda_param_slot`).
* **`Let` / `LetRec` / mutable-variable `binding.ty`, `Case` pattern payloads, a `For` target** — resolved *in place* by `resolve_binder_slot`. Resolving the slot is **not** copying the coalesced RHS type onto it: the two agree for an unannotated `let` (the binder is bound at its initializer's type) and disagree for the annotated ones — a deref-copy binds at the value type where the RHS is a handle, a mutable-variable introduction at the handle where the RHS is a value.

**Resolving a binder slot is two jobs.** `resolve_var_type` settles the type's *structure*; the refinement predicates riding it are expression trees hanging off type slots, carrying inference variables of their own, and they are settled by `coalesce_type_predicates` — which is exactly what `coalesce_node` runs for every `expr.ty`. A slot that did only the first would keep the **pre-coalesce predicate `Rc`**: the predicate memo redirects only the occurrences it visits, so a slot the walk skipped still points at the original, and the stale copy survives with unresolved variables. `resolve_binder_slot` exists so the two halves cannot drift apart per slot.

That residue is invisible in most programs because something else rebuilds the binder — a *generalized* `let`'s definition is re-coalesced by `specialize_use` at each specialization. It is a **value** binding that exposes it: nothing rebuilds it, so the slot is the only chance. Two independent shapes reach it — a `groupby` (a collection, so a value binding, and dependently refined, so its binder type carries a predicate at all) and a `match` over a conditionally-built collection (whose arm domains carry the conditional's gate).

Refinement predicates are otherwise coalesced by recursing into them (in the `Lambda` arm and `coalesce_type_predicates`); their free variables share the enclosing bindings' vars and coalesce identically, just like ordinary `Var` uses — and their projections recover their domains through the same `Apply`/`Compose` arms (see §2).

### The post-inference check (shared rules)

Inference runs once, up front. But the pipeline re-checks types repeatedly *after* it — after inlining, after lambda-elimination, after join-planning — to confirm each transformation pass left a well-typed tree. This check shares inference's *structural* knowledge (what an `Apply` destructures, how a `Compose` chains, which product a constructor rebuilds) through the **`Typing` trait** rather than re-deriving it in a separate body of code. The per-node structural rules (`emit_apply`, `emit_compose`, `emit_proj`, …) are written *once*, generic over `C: Typing`, and two contexts implement the trait:

* **`InferCtx`** — the emission context (Pass 1). Its hooks generate constraints: `fresh` mints an inference variable, `instantiate` freshens a scheme, `require_sub` calls `constrain_subtype`, `subexpr` recurses emitting onto `expr.ty`.
* **`CheckCtx`** — the post-inference check (`infer::check`). The *same* rules run, but the hooks now *verify* rather than *solve*: `subexpr` returns the child's already-recorded `child.ty` (what inference decided) instead of re-deriving it, `require_sub` confirms a relation the solver should already have established, and a final **reconcile** step checks the rule's reconstructed type against the node's recorded type.

So the two passes share one description of the language's structure; they differ only in whether a rule's obligations are *emitted as constraints* or *checked against the recorded solution*. Adding or changing a structural rule updates both at once. Both contexts treat refinements strictly and identically; see §4 for how the check stays refinement-aware (adjacency flow checks *and* the reconcile) and why the passes that introduce refined types must keep each node reconstructable.

---

## 3. Surprising Mechanics

Because the algorithm drops HM's union-find equality engine, it behaves in ways that can surprise developers familiar with static typing.

### 3.1 Let-Polymorphism is Freshening (Instantiation)

Vanilla algebraic subtyping makes a `let`-bound function polymorphic by **freshening**: every time a generalized binding is used, the solver copies its type graph, minting fresh variables for that use site. This is ordinary let-generalization/instantiation — the same idea as HM's `∀`-quantification — applied to the bound graph rather than to a syntactic type scheme.

**How Cambra applies this — and then lowers it.** A `let` binding a *function definition* (`should_generalize`) is typed one level deeper (`in_let_rhs`) and generalized into a `PolyScheme` at the binding level (`scoped_let`); each `Var` use then `instantiate`s a fresh copy, exactly the freshening above. Because every pass after inference is monomorphic, the generalized binding is lowered to concrete code **inside the coalesce walk** (integrated monomorphization): the walk carries a scope of *specialization frames* — one per in-scope generalized `let`, plus shadow markers for every other binder — and a use of a generalized binding specializes at first visit (`specialize_use`). By coalesce time the constraint graph is *complete* (emission saw the whole program), so a use's instantiation is fully determined when the bottom-up walk reaches it: the walk resolves it off the live graph, and on a memo miss clones the definition (`freshen_expr_type_slots` freshens an independent copy — uniformly over terms and types, so a refinement predicate's slots and the suspended-substitution payloads riding the copied bound edges are renamed in the same traversal as every other slot), **pins the clone two-way to the use's live instantiation type**, coalesces the clone re-entrantly *in the definition site's scope* (entries pushed between definition and use are suspended, so a same-named binder introduced in between cannot capture the clone's references), renames the use to a synthetic `Mono` name (`Name::mono`) carrying the source binding plus a globally-fresh uid, and stamps the specialization's resolved type on it. When the `let`'s body walk completes, the node rebuilds itself as the chain of demanded specializations (`coalesce_generalized_let`), running the §6.2 `let`-closing discharge per spliced layer; a binding never demanded is resolved for its diagnostics and then dropped as dead code (see [Typechecking a never-called definition](#typechecking-a-never-called-definition)). Uses that instantiate the definition identically share one clone — the memo is keyed on a `SpecKey`, taken from the use's live type before its pin, and an entry stores the key of the use that minted it (see [Keying a specialization](#keying-a-specialization)). The definition's own subtree is never coalesced in place *while it has clones*: its quantified variables have no use-site bounds, so coalescing it would both produce an under-determined type and overwrite the bound-bearing `InferVar`s the clones freshen from. A definition with no clones is the never-called case above, where neither objection applies.

Specializing *during* the walk — rather than splicing after it — is load-bearing twice over. First, every parent derives its type from concrete children on the first pass: in particular a parent `Apply`'s dependent-codomain discharge forces against the specialization's resolved predicate terms, so parent types are never re-derived from a second, graph-unreachable copy of the discharge logic. Second, chained polymorphism (a generalized UDF used only inside *another* generalized definition, poly-calls-poly) needs no special ordering: the inner use is reached only inside an outer clone's re-entrant walk, after that clone's pin has driven the use's instantiation concrete, and the inner binding's frame is still in scope below the outer's. The ordering invariant that makes in-walk specialization sound: **specialization may only add bounds to variables the walk has not yet read** — a use's pin touches its own instantiation variables (read right after, at its own stamp), the clone's fresh variables (read only inside the clone's walk), and otherwise deposits only α-copies of demands the instantiation already made at emit; `coalesce_node`'s `Apply` arm coalesces function before argument to keep even those copies behind the read front. The invariant is **checked explicitly, not just argued**: the walk logs every graph read as a `(var-laden type, resolution)` pair (the snapshot shares the live `InferVar`s), and `assert_reads_stable` re-resolves each against the *final* graph at end of pass, requiring the structural skeleton — bases, ranges, shapes, refinement-layer count, with under-determined positions wildcarded and predicate *content* deferred to `check_scope_valid` / the post-inference reconcile — to be unchanged. A pin that retroactively altered an already-read variable's resolution trips it by name (debug builds; free in release). Refinement layers count because a refinement is lattice content like a record field, so a bound determines it as much as it determines the base; the **one** read that excludes them is a use's own instantiation resolution, where the pin that immediately follows the read is itself what moves the refinements (`ReadPurpose::Instantiation`). That is sound because the read's consumers are refinement-insensitive — it seeds the clone's channel-domain pairings and blames a resolution failure — and, in particular, *sharing does not ride on it*: that is the `SpecKey`'s job, and a key consults both bound directions precisely so it does not depend on which polarity a rendering would have picked. The read's *skeleton* is still held fixed — a stale one would pair channel domains wrong. The contravariant-domain coalescing of §2 — the opposite-polarity fallback plus `coalesce_node`'s per-morphism domain specialization (projections and lambdas) — is the monomorphic coalescing rule for those vars; it is sound because every variable reaching coalesce is monomorphically determined (§1).

#### Typechecking a never-called definition

Dropping a never-demanded binding as dead code is a decision about what to *lower*,
not about what to *check*. A definition body is emitted whether or not it is called,
so any demand that conflicts with a concrete type is already reported (`f = \a -> a
and 3` is rejected with no call site). What emission records without judging is a
demand on a **quantified** variable: one bound among several, a conflict only when
the bounds are read together. Reading them together is what resolution does — so a
definition like `f = \a -> (a.0, a.foo)`, which asks `𝑎` to be both a tuple and a
record, was accepted for exactly as long as nobody called it. `coalesce_generalized_let`
therefore resolves an undemanded definition (`typecheck_discarded_definition`) before
dropping it, and keeps only the diagnostics.

The general prohibition on coalescing a definition in place is about definitions with
clones, and neither half of it survives their absence: nothing was freshened from this
definition, and its binding leaves scope at the `let`, so nothing can freshen from it
later. What remains is the under-determination — its quantified variables never
received use-site bounds — which inference tolerates (`Type::Infer`'s invariant) and
no strict check ever sees, because the resolved definition is discarded either way.

The walk descends through uses, so it also typechecks what dead code *calls*: a use
inside it of a generalized binding declared further out specializes normally, which is
what makes the call's argument meet the callee's demands. That specialization must not
be *spliced*, though — its enclosing `let` survives the dead definition and would
gain a binding nothing references. It is still registered, which is what shares the
clone with the next dead use, and marked unreferenced instead
(`Specialization::referenced`), so dead code is checked without re-entering the
program. Which frames that applies to is asked of each frame when it is pushed
(`SpecializeFrame::inside_discarded`) rather than computed from a scope depth: a frame
created *inside* the discarded subtree dies with it, so what it splices is moot, and
the re-entrant clone walk truncates the scope stack, which a depth cannot survive.

**Deadness is the absence of a demand, not of a specialization.** The two come apart
in both directions — a use whose instantiation fails to resolve reports and returns
before minting anything, and a use inside a discarded subtree deliberately does not
mutable variable — so `specs.is_empty()` cannot decide this. `SpecializeFrame::demanded`,
set on entry to `specialize_use`, is what does. Reading the memo instead re-walks the
definition of a binding whose uses merely *failed*, which reports that body's conflict
a second time from its own nodes: one defect, four diagnostics.

*Known gap, not fixed:* a use that fails to resolve is never renamed, so it still
names a binding whose `let` the rebuild then drops — leaving that reference dangling
in the tree a failed pass leaves behind. It is unobservable while an inference error
discards the tree, and the fix is a node meaning "could not be built, errors pending"
(today's `TypedExprNode::Error` is contracted to lowering recovery), which would also
let the rebuild stay unconditional.

**What it costs.** The walk runs unconditionally, in release, on every definition
nothing calls — so the specialization blowup documented under
`SpecializeFrame::specs`, "The remaining gap" (one clone per distinct argument
tuple, compounding through a call chain) is now reachable from code no one calls,
where before dead code cost nothing. Two things keep that bounded rather than
multiplied. A use inside the discarded subtree still *mutable variables* its
specialization, so the memo shares clones exactly as a live use does — declining to
mutable variable instead made every dead use re-clone its callee, which measured ~5× the
shared cost at a call-chain depth of six; splice-liveness is decided separately, at
the rebuild (`Specialization::referenced`). And a dead definition nested inside a
*live* generalized one is walked once per clone of its enclosing binding — which is
correct, since its body can depend on the instantiation — but a diagnostic it
repeats is dropped, so one defect stays one diagnostic however many specializations
enclose it.

**What this does not reach.** Resolution reads the bounds a body *recorded*, so a
requirement that takes effect only when a concrete type is **delivered** is not
evaluated here. Trait obligations are the case: an obligation narrows as bases arrive,
and one whose operand never receives a base rejects nothing, however few
instances could satisfy it. Reading a value's requirements *together* covers it,
which needs no delivery and is a separate pass
([Requirements are read together, once](#requirements-are-read-together-once)). The two
are complementary: that pass runs on every program, and this walk is what makes a dead
definition's bounds resolved in the first place.

**A shape that looks like an escape and is not.** `if 𝑝: [x for x in xs if 𝑞] else: xs`
is accepted with no call site, and rejected at one. That is not laxity: both arms'
domains are the *same* variable (`xs`'s), so the filter is recorded as a refinement on
it rather than as a second domain alternative, and the definition types as
`(…, {𝐷 | 𝑞} ⤇ 𝑉) ⇒ …` — *give me a collection whose domain already satisfies the
filter*, which is exactly the condition under which the two arms share a domain and the
join loses nothing. The requirement is in the type, not dropped. Supplying a concrete
domain at a call site re-materializes the arms as two distinct domains and meets the
interim Σ diagnosis ([The domain join is a Σ](#the-domain-join-is-a-σ)) — which is also
why the same body over a *literal* or *source* collection is diagnosed either way: those
domains are concrete in the body already, so there is no shared variable for the
refinement to land on.

#### Keying a specialization

The memo that decides which uses share a specialization is keyed on a `SpecKey`
(`src/ccl/infer/solver/spec_key.rs`), **not** on a resolved `Type`. The distinction
is the whole content of the design here, because the two answer different questions.

A resolved type answers *"what should be stamped on this node"*, and is
deliberately lossy in service of that: a domain is a negative position, so it
resolves from upper bounds — from what the definition body demands — which narrows
away a position the body never touches, and leaves an argument's refinement (a *lower*
bound, from the emit-time `arg <: domain` edge) invisible except where the
opposite-polarity fallback happens to fire. A specialization key answers *"would
two uses' clones be the same code"*, and must be complete: a clone's interior reads
its parameter at a **positive** position, so it sees exactly the refinements the
domain's rendering drops. Keying on a rendering compares one polarity's view
against a clone built from the other's, which shares a clone between two uses whose
interiors differ — the clone then carries one call site's argument type at another's.

A `SpecKey` is therefore the pair of **directed reads** of the use's instantiation
type, the root taken once at each polarity and the two *kept apart*:

* the **positive** read is the stamping view (domain from the definition's demands);
* the **negative** read is the clone's view (domain from the argument that flowed
  in, codomain from the consumer's demand).

The negative read is the load-bearing half, and the pair is exhaustive:
use-specific information enters an instantiation through exactly two channels — an
`arg <: domain` edge and a consumer's `codomain <: demand` edge — and the negative
read follows precisely those. Merging the two views is wrong, because it forgets
which *direction* a contribution came from and the pin the key stands in for is
direction-sensitive. *Saturating* — following both bound lists at every variable —
is worse: the bound graph is connected across unrelated uses (two calls' arguments
meet at the shared variable of an operator's scheme), so an undirected closure
walks out of one use into every other and every use keys on the whole program's
literals. Within a read, merging is always **union**: a key that narrows can only
under-split, and under-splitting is a miscompile while over-splitting is a wasted
clone. An under-determined position is one canonical empty view rather than a fresh
`Infer` placeholder, so two unexercised uses can still share.

Both sides of the comparison must be computed by **one procedure at one point in
the pin's lifecycle** — from the use's live type, before its own pin — and an entry
stores the key of the use that minted it. Keying an entry on its clone's
*coalesced* type instead is a second, incompatible coordinate system: for any
definition whose clone type gains a refinement across the pin, no candidate key could
ever equal a stored one, so the memo becomes write-only and even identical call
sites clone per site.

**A key is not instantaneous, and it is not a function of the post-emission
graph.** "One point in the pin's lifecycle" is exact about each use's *own* pin,
but the two keys in a comparison are not taken at the same instant: an entry's was
taken before the pin of the use that minted it, a candidate's later, with every
intervening pin already in the graph. The tempting strengthening — that a pin only
*transports* use-specific information across polarity and never creates it, so no
other use's pin can move a key — is **false**. A pin does not only transport; for a
*nested* use it **deposits the consumer's demand**. In `f(f(3))`,
`coalesce_node`'s `Apply` arm takes function before argument, so the outer use of
`f` specializes first and its pin is what drives the outer clone's domain
concrete. That domain *is* the demand on the inner call's result, so it reaches
the inner use through the `codomain <: demand` edge — one of the two channels the
negative read follows *by design*. The inner use is therefore keyed against a
demand that did not exist at end of emission.

Whether the deposit is *visible to the key* depends on how much structure the
demand carries. Where the demand resolves to a bare base the two reads agree and
nothing is observable, which is why a snapshot-and-compare check over the suite
passes here. It stops passing as soon as a demand carries structure a key records:
once an operator's effect on types is itself a type, the same `f = \x -> x * 2`,
`f(f(3))` splits, the inner use's negative read gaining exactly the layer the
outer pin deposited. The positive read does not move, and no key moves for any
other reason.

So key equality is walk-order sensitive, and the memo can compare keys read in two
different graph states. The residue is **over-splitting** — a use keyed against a
thinner demand does not match an entry keyed against a fatter one, and the cost is
a redundant clone, the same direction as the known imprecision below. It is not
symmetric with under-splitting: a thin key and a fat key are unequal, so a use
carrying a real demand cannot be served by an entry that never saw one.

**The key is only expressible in-walk — which is an argument *for* in-walk
specialization, not a cost of it.** A monomorphizer that ran *after* coalesce
would have no choice but to key on a resolved type, because by then a resolved
type is all there is: `expr.ty` has been overwritten in place and the bound graph
it was resolved from is gone. Specializing *inside* the coalesce walk is what
leaves a use's instantiation still var-laden with its bounds still live at the
moment the key is taken — so `SpecKey` is not merely a better key than the
rendering, it is one only this architecture can express. The discriminating
information is present the instant emission finishes; the pin transports it across
polarity rather than discovering it.

**Why other monomorphizers key on a finished value.** rustc keys an instance on
its definition plus its generic arguments, C++ on the template-argument list,
Swift on a substitution map, MLton on the type-argument list in a single
post-inference pass. Every one of them keys on a *finished value*, and can,
because their generic bodies are already typed and instantiation is substitution.
Cambra has no `Type::ForAll` and never types a generic body at all — the
definition's own subtree is never coalesced in place — so monomorphization here
**is** the act of typing the body, not the duplication of already-typed code. That
places it in C++'s category, the one mainstream compiler where instantiation
genuinely re-runs semantic analysis, and it is the real reason the key has to be
read off a live graph. A reader arriving from rustc would otherwise take that for
an implementation choice. What is *not* the reason: poly-calls-poly on its own
does not force the in-walk arrangement — discovering the *set* of instantiations
is a reachability fixpoint in every monomorphizer, and recursing into each new
specialization handles it. (Closest prior art: Lutze, Schuster & Brachthäuser,
*The Simple Essence of Monomorphization*, OOPSLA 2025 — monomorphization as a flow
analysis over an algebraic-subtyping system, including where it stops being
possible, at the cyclic flow of polymorphic recursion.)

**Specializing precisely is the correct rule, not a budget choice.** A refinement
layer on an iterated domain is *compiled* — `planning::iterate` emits one
`restrict(p)` filter per layer — so a refinement is code, and two clones pinned to
different refinements are genuinely different code. Since every literal carries its
own singleton ([A literal is refined by its own value](#a-literal-is-refined-by-its-own-value)),
the practical rule is one specialization per distinct argument tuple. `inline`
beta-reduces scalar UDFs, so the cost lands on collection-producing ones, which it
leaves cached.

**Known imprecision.** The key summarizes the pin's *input*, so two uses differing
only in a position the clone never reads still key apart (`λ a, b → a` at `(1, 2)`
and `(1, 5)` mints two identical clones). Keying on the pin's *output* — the
finished clone, deduped structurally — would share exactly when the emitted code is
identical, but it cannot be a lookup, only a build-then-dedupe, and it needs
α-equivalence over the names minted fresh per clone (`Name::mono` uids, coalesce's
`Infer` placeholders, per-instantiation `ChanDom` names), a way to undo a discarded
clone's pin, and reference-liveness filtering at the splice. The two compose — this
key as the fast path, clone-equality as a precision tier on a miss — so nothing
here has to be undone to get there. Relatedly, a *hit* is not re-pinned: a miss
pins a var-laden clone (identifying variables), while a hit's specialization is
already concrete, and pinning that against a still-var-laden use type is a strictly
stronger demand that rejects uses the key correctly considers shareable. Checking a
hit wants a non-recording subsumption test, which the solver does not have.

**Refinement predicates under monomorphization.** A `Refinement` has no synthetic identity: it carries an *immutable* predicate term (`Rc<TypedExpr>`), and its identity is the **type-blind structural equality** of that term (`eq_refinement_predicate`) — the predicate's embedded `Type` slots are inference metadata and never participate. A predicate occurs at many sites — its syntactic origin (a `Cast` target, a `user_annotation`) and every position `constrain`/`freshen_above` propagates the refinement onto — but those are independent occurrences, not aliases of one mutable cell. Two facts make this work without the cell-retirement machinery the mutable design needed. First, a free use of a generalized binding may live *only* inside a predicate (a list-comprehension filter calling a UDF lowers to a cast-target predicate); the coalesce walk reaches such uses because `coalesce_type_predicates` runs `coalesce_node` over every predicate it encounters with the walk's specialization scope live, and the post-inference `inline` pass substitutes inside predicates likewise. Second, because predicates are immutable, **a use-site coalesce *rebuilds* a predicate rather than mutating one shared with the definition** — so there is nothing to privatize, retire, or re-point: a specialization clone freshens its predicate as a proper substitution instance (`freshen_above`'s `Refinement` arm freshens the predicate's type slots through the same cache, and its `Infer` arm freshens the discharge-payload terms riding copied bound edges), and `compact_type` simply `force_refinement`s each refinement it materializes (a vacuous force shares the `Rc`, a substituting one rebuilds). The residual case the mutable design's whole-tree fix-up swept up — a refinement materialized from the definition's bound *before* its first specialization carries the definition's quantified vars — is harmless here: equality is type-blind, so a predicate carrying the definition's quantified vars compares equal to its specialized instance. Passes that need *occurrence* identity rather than equality (visited sets that dedup a predicate term shared by `Rc` across positions — the term graph is a DAG, since immutable `Rc<TypedExpr>` cannot form a cycle) key on the predicate `Rc`'s address (`PredicateId`).

Generalization is narrow only in *what* it generalizes: function definitions with a quantifiable variable. Non-function (value) bindings are *not* generalized — they are bound monomorphically and shared, since specializing a value would duplicate it, which the feed/define and join-planning machinery does not tolerate. There is deliberately **no** use-count or generator carve-out: a single-use function generalizes to one specialization (later inlined like any monomorphic def), and a generator/collection-producing UDF generalizes to one specialization *per distinct element type* — which `inline` leaves *cached* (its domain is iterable) rather than duplicating. Levels are genuinely incremented at every generalized let, so extrude is live.

**Refinement predicate representation.** A `Refinement` holds a single field,
a **bare**, *immutable* boolean predicate (`Rc<TypedExpr>`), in which one
reserved implicit binder — `REFINEMENT_BINDER` (`"__elem"`) — is free and ranges
over the refined base type. The refinement *is a binding form*: the predicate
references its own element through that one name, and nested refinements simply
shadow it (a predicate only ever references its *own* element plus enclosing
`Fun`-binders, which carry their own distinct names). Because the binder is a
fixed shared name, refinement equality/hashing is plain type-blind structural
comparison of the bare predicate — no α-renaming. Every traversal that descends
into a predicate (free-variable collection, substitution, lambda-elim) treats
`REFINEMENT_BINDER` as bound, so the shared name never captures across nested
refinements.

A rewrite of a predicate (a discharge substituting an argument in, lambda-elim,
inlining's beta step, planning's point-free compilation) produces a **new**
term — structural `Rc` sharing keeps that cheap — rather than mutating one in
place. A pass that processes a predicate at one occurrence must therefore reach
*every* occurrence (each is an independent `Rc`); where a pass walks a tree it
threads a memo keyed on the original predicate's identity so occurrences that
shared one term are re-pointed at the same rebuild (the immutable replacement
for "mutate the shared cell, every alias observes it"). One consequence worth
naming: a `Cast`'s `target` type slot is the cast's recorded type, so passes
that rebuild a predicate on `expr.ty` re-sync the `target` to it
(`ccl_utils::sync_cast_targets`) — the post-inference check reconstructs a cast
from its `target`.

#### Sharing is an invariant, not an optimization detail

One structural predicate should be **one `Rc`** for the whole pipeline. Lowering
establishes that (`Refinement::sharing` puts a single filter predicate on the
source, the map, the cast target, and the consumer contract); every pass that
rebuilds predicates must then *preserve* it, and "every pass" is the whole list —
`uniquify`, constraint emission (`emit_bare_predicate`), `coalesce`,
`subst`'s both modes, `inline`, `simplify`, and planning's compilation. Each
threads one **pass-scoped** `ccl_utils::PredMemo`, whose `rebuild` maps an origin
`Rc` to a single result. A pass that has nothing to say about a predicate reports
no change and keeps the origin `Rc` rather than reallocating an equal one, so
sharing survives even the passes that merely walk past.

Two things make this load-bearing rather than housekeeping:

- **Downstream cost.** Planning's predicate-compilation memo is `Rc`-keyed, so a
  predicate split into 𝑛 occurrences is compiled 𝑛 times. With nested
  comprehensions 𝑛 grows with depth, which is how a split turns into superlinear
  compile time.
- **The keepalive.** The memo keys on the `Rc`'s *address*
  (`PredicateId`), which is sound only while that address cannot be reused.
  Overwriting a slot can drop the last reference to the origin and free an
  address a later `Rc::new` in the same walk reclaims, at which point an
  unrelated predicate collides with the entry and inherits its rebuild. `PredMemo`
  retains every origin for its own lifetime; that is why passes use it rather
  than a bare map.

#### One known exception, scoped and unfixed: generic instantiation

The list above
is the *rebuilding passes*. `freshen_above`'s `Refinement` arm does not thread a
memo — `freshen_refinement_predicate` clones the predicate term, freshens its type
slots, and installs an unconditional `Rc::new` — so every refinement a scheme
instantiation touches comes out `Rc`-distinct, including several slots of one
clone that shared an `Rc` going in. This is why the invariant holds for
comprehension-only programs and fails as soon as a UDF body carries a predicate:
`f = \xs -> [x for x in xs if x > 1]` leaves 4 surplus `Rc`s of 9 distinct at one
call site, 29 of 38 at two. `tests/predicate_sharing.rs` does not observe it (its
corpus is comprehension-only and it measures post-inference). Whether this costs
anything in planning is **unmeasured** — the superlinearity argument above comes
from the original split's shape, not this one — and that measurement is what
decides between fixing the producer (memoize the rebuild, or keep the origin `Rc`
when the freshen is vacuous) and narrowing the invariant to "preserved through
inference, deliberately re-split at instantiation". Tracked in the
lineage-redesign doc, §12.4(9).

A pass reaches predicates through **every type slot a node carries**, not just
`expr.ty`: the node's own type, its `user_annotation`, a `Cast`'s `target`, and —
per binder — both the binder's declared type *and* its annotation. Each holds an
independent predicate `Rc`. `Expr::walk_type_slots{,_mut}` is the single source of
truth for that set, precisely because hand-rolling it per pass is how a pass
silently acquires a blind spot — `Cast.target`, where a comprehension filter's
predicate actually lives, is the one that costs most. `count_free`/`is_free` are on
it too, and that is not cosmetic: several passes *skip work* when `is_free` says
no, so a slot the free-variable walk cannot see is a slot those passes decline to
rewrite.

A binder's **annotation** is the subtle member of that set, and it is the only one
with a bounded lifetime: it is where lowering writes a mutable variable's
`Mut(V, D)` history (`x := e` lowers via `let_bind_annotated`), and it exists only
*until inference consumes it* — see [The binder slot, and why annotations do not
outlive inference](#the-binder-slot-and-why-annotations-do-not-outlive-inference).
A walk over the slot set must still cover it, because the passes that use
`walk_type_slots` include ones that run before and during inference (`uniquify`,
`subst`), and — because an erasure and its own post-condition share that walk — a
slot the walk misses is a slot the check cannot report on.

The claim is *checked*, not asserted: `walk_type_slots_covers_every_carried_type_slot`
stamps a distinct marker into every directly-carried `Type` in the AST and pins
which ones the walk reaches. One is deliberately excluded — `Transact`'s `domain` —
because that node is born by `plan_loops` after every pass on the walk, so covering
it would newly expose the sequencing extent to planning's predicate compilation.
That is a behavioural change in the recurrence engine, and the test pins the
exclusion so it stays a decision rather than drift.

#### The memo key is the predicate *and the conditions it was rebuilt under*

Keying such a memo on the predicate `Rc`'s address alone is half a key: it answers
"have I rebuilt this term?", while every pass needs "have I rebuilt this term
**under the conditions I am rebuilding it under now**?". `PredMemo<C>` carries those
conditions as `C`, and reuses an entry only when it was recorded under an equal
`C`. Supplying the wrong `C` costs a sharing opportunity; it cannot produce a wrong
answer — which is the point, because the key-only design did produce wrong answers
(`subst` discharging a binder its inner scope owned; constraint emission skipping
the emission that bounds an occurrence's own domain).

What each pass supplies:

| pass | `C` | why |
|---|---|---|
| `simplify` | `()` | a function of the term, full stop |
| `uniquify` | `()` | resolves against `env`, but lowering shares an `Rc` only by copying one refinement, and pre-uniquifies a subtree before cloning it |
| `coalesce` | `()` | resolution reads one live constraint graph, so occurrences of one term resolve identically |
| `inline` | `()` | the rewrite is fixed per sweep, and a shadowed subtree is *skipped*, never descended into |
| `subst` | `Subst` | acting differently in different scopes is the point of a substitution |
| planning | `Type` | compilation reads the refinement's base |

The `()` rows are *claims*, and each one's justification lives at its call site —
that is where to check it. One is load-bearing in a way worth flagging: `inline`'s
depends on its binder arms skipping rather than descending-with-a-guard.

A pass that must share *allocations* without sharing *results* uses `TermMemo`
instead. Constraint emission is the case: it binds `REFINEMENT_BINDER` to a domain
`emit_cast` mints fresh per cast node, so no occurrence may reuse another's answer,
yet all should still land on one term. `TermMemo` is a separate type rather than a
flag, so which of the two a pass is entitled to is visible in its signature.

#### The protocol is a closure, so a rebuild cannot be half-done

`PredMemo::rebuild` and `TermMemo::rebuild_always` take the transform as a closure.
An earlier token-based shape (`begin` handing out a token that a `finish` consumed)
could be left open: dropping the token discarded the rebuild, left the occurrence
on its origin `Rc`, and memoized nothing — so a pass that returned early between
the halves rewrote every occurrence *but one*. Two such leaks existed; the closure
form makes them unrepresentable.

The closure is also what lets the memo be a cheap clonable handle
(`Rc<RefCell<_>>`), which matters because three passes own their memo inside the
very context their transform needs mutably — `uniquify`'s `self.expr` → `self.ty`,
`coalesce_node` → `coalesce_type_predicates`, `subexpr` → `emit_node` →
`emit_cast`. Reaching a handle needs only `&ctx`, and no borrow of the store is held
across the callback, so those transforms re-enter the memo freely. Threading the
memo as a plain parameter instead would mean changing `Typing::subexpr` and every
emit rule.

One consequence worth stating: the `changed` bit a callback returns is not the
whole answer. A callback that re-enters the memo can have its copy mutated
underneath it by a nested reuse, with nothing of its own to report; discarding the
copy would throw that re-pointing away and memoize the staleness. `rebuild`
therefore also consults the store's revision counter, and
`walk_refined_predicates_mut` returns a `changed` bit for callers running a
fixpoint.

The invariant is guarded by `tests/predicate_sharing.rs`, which asserts
end-to-end that no two `Rc`-distinct refinements reachable from an inferred tree
are structurally equal — the exact shape a split leaves. That is the sufficient
check, and it needs no magic number. (A counting tripwire — the distinct-`Rc`
count must not *grow* across a rewrite-only pass — used to sit around the retired
predicate re-stamping pass; with no rewrite-only pass left to wrap, the
end-to-end assertion is the whole guard. `ccl_utils::distinct_predicate_rcs`
remains available for one, should a future pass need wrapping.)

A predicate *function* `p : 𝐷 ⇒ Bool` never lives in a refinement type — only in
a *term* (an `Apply(p, Iterate/Restrict)` argument). In a type it is represented
bare as `__elem ▷ p` (`ccl_utils::bare_predicate_of_fn`; its inverse
`planning::fn_of_bare_predicate` recovers `p` when a term needs the function,
e.g. `make_restrict`).

### 3.2 The `InferArena`: who owns inference variables

Recording `α <: β` pushes `Type::Infer(β)` into `α`'s bounds and `Type::Infer(α)` into `β`'s bounds (the shared-`Rc` linkage from §1). Mutual constraints — and self-recursive ones — therefore make each `InferVar` hold a *strong* `Rc` to the others through its `RefCell<InferBounds>`. After Pass 2 overwrites every `expr.ty` with a concrete, variable-free type, these cells become unreachable from the final AST yet keep one another alive: reference counting alone never reclaims the cycle, so the entire variable graph would leak after each `infer()` run.

**`InferArena` (`ccl/infer/`) is the single owner that breaks the cycle.** It retains one strong handle to *every* variable at the moment it is minted (captured through a thread-local mint sink wired into `InferVar::fresh`), and on `Drop` clears each variable's lower/upper bound lists — severing all bound edges so every refcount can reach zero. A flat `Vec` suffices: variables are never looked up by id (the `Type` carries the `Rc` directly), so the arena only enumerates them once, at teardown. Clearing bounds before the `Vec` drops handles self-cycles and N-way cycles uniformly. This is an end-of-inference lifetime invariant implemented as RAII: the arena is created at the top of `infer()` and drops on the `Ok` and error paths alike.

---

## 4. Information Flow and Type Mapping

Cambra carries features beyond plain algebraic subtyping (explicit refinements, tagged sums); this section describes how each is represented in the solver and materialized back out.

#### The unified tagged sum

Cambra has **one** sum representation, the **tagged variant** — `Type::Variant(Vec<(FieldKey, Type)>, Openness)`. Since the solver works on `ccl::Type` directly, there is no second variant form to convert to: inference, coalescing, and the public AST all use this one type. (Internally, `compact_type` keys its transient `CompactType` bag by `FieldKey`, but that is an implementation detail of compaction, not a separate type.)

Tags are [`FieldKey`]s — the same key type as records/tuples — so a sum can be **named** (`FieldKey::Name`, a source-level `` `tag(…) ``) or **anonymous/positional** (`FieldKey::Index`, the dual of a tuple). A positional union `A | B` is simply `Variant([(Index 0, A), (Index 1, B)])`, and the surface `++`/`Copair` produces exactly that (see §2's `emit_copair`). One constructor, one coalesce path, one width-subtyping rule (the dual of records: a subtype has *fewer* tags).

That one rule does **two** jobs, and the [`Openness`] marker is what separates them. Recursing into a tag both sides carry is what pushes the payload into the supertype's slot — how a `match` arm's binder learns its type from the scrutinee. Rejecting a subtype tag the supertype lacks is the exhaustiveness check. A **closed** arm set does both; an **open** one keeps the payload recursion and drops the rejection, which is what a `match` with a `case _:` needs and what no closed judgment can express (on the tag axis the scrutinee is the supertype, on the payload axis its payload is the subtype, and one edge cannot point both ways).

Openness is a property of a *demand*, never of a value: every producer of a sum is closed, and `Open` appears only on the right of a subtyping edge. Compaction and coalescing **carry** it (`CompactVariant` pairs the tag map with its openness) rather than flattening it, because a type *error* naming that demand is resolved through the same round-trip — closing the arm set there would report that the scrutinee failed to be an exact sum, when what it failed was to be a subtype of a partial one, and only the rendered `| …` tells those apart. Nothing else reads it: the runtime `Extent` has no counterpart, and no node's coalesced type comes out open. That last is an invariant, not a theorem, so `types_agree_modulo_unread` compares openness and an escape shows up there as a disagreement.

Two arm sets meeting at one position meet their openness — `Open` survives only if both sides are open, since a closed side is the one contributing a requirement on the tag set. The tag *map* still merges by the ordinary intersect/union rule; that is an approximation when exactly one side is open, and no program reaches it (a scrutinee takes one `Case` demand per `match`).

Two senses of "union" remain distinct:

* ***union of lower bounds*** — the lattice operation at coalesce time (§1, §2); an internal solver operation, not an AST node.
* a **positional `Variant`** — the all-`Index` tagged sum that materializes a `++` collection-union or a user `A | B` annotation.

Inference does not *infer* a multi-atom sum from a primitive collision (it raises `IncompatibleBounds`); positional variants enter only via `++` or a user annotation.

#### Tagged-variant expressions

* **`VariantCtor { tag, payload }`** constructs a singleton `Variant({tag: payload})`; width-subtyping flows it into any consumer expecting a superset of tags.
* **`Case`** is the single dispatch node for both logical (`if`/guard) and structural (variant-tag) matching — see §2's `emit_case`. A structural `Case` carries a scrutinee and branches with `Pattern`s; width-subtyping enforces tag coverage and binds each payload at its per-tag narrowed type.

(`VariantCtor`/structural `Case` have no surface syntax yet, so lowering never emits them; they are exercised by direct AST construction in the variant tests.)

#### A literal is refined by its own value

A literal is typed by *which* literal it is: `5 : {Int | __elem == 5}`, its base refined by the singleton predicate. Not a `Literal(base, value)` constructor — an ordinary refinement, so every rule above applies unchanged and none has to learn a new case.

The reason is that a literal knows more about itself than its base does, and that knowledge is what a proof obligation needs: `a[0]` can only discharge against `Array(3, 𝑇)`'s index range if `0`'s type says it *is* `0`. Typing `5` as plain `Int` throws that away at the one place it is free to keep. The predicate is built **typed** — only *node* annotations get their embedded predicates re-inferred, and this one rides a type the rule makes rather than one a user wrote.

What this changed is instructive, because refinements were rare enough before that several rules assumed their absence. Each was already wrong for a user-written refinement; literals are merely the first thing that makes them reachable.

* **An operator does not *inherit* its operands' refinements**, and does not have to be *made* not to. A refinement is a fact about a value, so an operator that computes a new value cannot carry one over: `𝑥 + 𝑥` where `𝑥` is `2` produces `4`. Arithmetic, comparison and negation state their requirement as a [trait](#traits), over a variable per operand and per associated type — all unrelated — which leaves no path for an operand's refinement to reach the result by sharing (`an_operator_result_carries_no_operand_refinement`). The remaining monomorphic operators (`and`, `++`, `not`) keep an ordinary scheme and pass their operands verbatim — nothing is shared with the result, so a refined operand simply flows into a concrete domain. Aggregates likewise keep theirs, since their operand is a *collection* whose refinements describe its domain and the rule must see them.

  Inheriting is not the same as **computing**, and only the first is ruled out. `{Int | __elem == 2} + {Int | __elem == 3}` genuinely *is* `{Int | __elem == 5}`, and a trait instance is where such a rule would live, since it determines the output type rather than forcing it to be a position the operands already occupy. Today every instance computes a base and stops — a property of the table, not of the mechanism. Two things would have to change to lift it: an instance would need the operands' *types* rather than their bases, and the deposit would have to move to a point where those types are final. Eager deposit is sound for a base because a base never weakens, while a refinement set only shrinks as further lower bounds arrive — so a refinement computed from a partial view is too strong. A rule computing from resolved operands then meets recurrences (`x := x + 1` resolves its operand through its own output), where it must already be sound at the cut; and anything beyond constant folding and interval arithmetic needs predicate *implication*, which the lattice deliberately does not have (refinements match structurally — see this file's module-level note in `src/ccl/infer/solver/mod.rs`).
* **A mutable variable takes no refinement** from its initializer or from any single write. A mutable variable is not one value but the sequence its writes produce, so its value type is the join over all of them; taking one contribution's refinement would assert it never changes, which is what declaring it mutable denies. The rule holds at every place a mutable variable's value type is *built*, not just at the `:=`/`+=` rule: the `Transact` carrier's keys (where the seed is the value type's only lower bound, so an unstripped seed would resolve the mutable variable — and every read of it — to the seed's singleton), the recognition that builds that carrier, and the phase that reads the value type back off the seed binding.
* **Every merge point joins** — a list's elements, a `Case`'s arms, a mutable variable's seed and writes, a channel's contributions. This is the one rule the singleton made load-bearing, and the one place it is easy to get wrong, because a merge that simply *adopts one input's type* looks right until the inputs carry different refinements. The law: a refinement is a fact about **a value**, and a merge point is not one value — it is whichever input the runtime supplies — so a refinement survives the merge only if *every* input establishes it. Two arms depositing different singletons intersect to none (`1 if 𝑐 else 2` is an `Int`); two arms depositing the same restriction keep it (identical filtered comprehensions stay filtered, `5 if 𝑐 else 5` is still `Int@5`). Where the merge is a fresh variable every input flows into, the solver's join *is* the rule and nothing has to strip; where a pass builds the merged type by hand (`channelize`'s channel union, the `Transact` carrier's key seeds) it must intersect the refinements explicitly.

  **Stripping is not the join.** It over-approximates in the safe direction (a refinement every input establishes is thrown away) and it is not variance-stable: for a *collection* input, whose extent rides the contravariant `Fun` domain, relating a refined input to a stripped sibling demands `𝐷 <: {𝐷 | 𝑝}` and rejects two arms that are literally the same expression. `𝐷 <: {𝐷 | 𝑝}` is never a real obligation in this language — acquiring a refinement is an explicit `cast` — so seeing one means an erasure manufactured it. Inputs whose extents genuinely differ meet on the domain (both refinements accumulate — the extent both admit), since that is where a function type's join puts them.
* **A `Mut` input derefs into the join**, exactly as a mutable read derefs into a tuple element, so a `Case` over two mutable variables types as their *value*. The second-class discipline's rule 1 therefore has no `Mut` on the selection to reject; what it protects — a selected mutable variable reaching a position that writes through it — is its argument clause, which reads the argument *node*. See [No aliasing: `Mut` values are second-class (downward-only)](mutability.md#no-aliasing-mut-values-are-second-class-downward-only).
* **`__elem` is bound by the refinement it rides**, so it is never free *in a type* — the free-variable walk must not report it so.
* **Beta reduction discharges a refined parameter** when the argument's type entails it: substituting the argument is what establishes the precondition.

Singletons are *not* erased after inference. They are ordinary refinements and ride through to the runtime like any other, which also keeps them available to a future constant fold. They print as their base pinned to the literal (`Int@5`, not `{Int | __elem == 5}`).

#### Refinements on the lattice

A **refined type** `{T | p}` carries a *set* of [`Refinement`]s, and the lattice treats each as a black box: it accumulates them and matches them by identity, never reasoning about what they imply (the predicate's logical content is real and used by the runtime, just opaque *here*). It is a fourth structural dimension on `CompactType`, width-subtyped exactly like records: **`{b₁ | S₁} <: {b₂ | S₂}` iff `b₁ <: b₂` and `S₂ ⊆ S₁ ∪ refinements(b₁)`** — more refinements ⇒ subtype. So `{T | p, q} <: {T | p}` and `{T | p} <: T`, but `{T | q} ⊀ {T | p}`. Refinements match by **type-blind structural equality of their predicate terms** (`Refinement`'s `PartialEq` / `eq_refinement_predicate`) — *not* by predicate implication (`{T | x > 0} ⊀ {T | x > -1}`). Structural matching makes refinement identity agnostic to *where* a predicate was constructed (join planning re-mints `{D | p}` at every marker it emits — `make_iterate` / `make_restrict` / `refine_with` — and must match the structurally-identical contract recorded elsewhere on the tree) and to in-place type resolution (copies of one predicate along a monomorphization descent line differ only in their inferred-type slots); a pointer-equal predicate `Rc` short-circuits as the fast path, since a refinement that merely flows around shares its `Rc`. The refinement set merges with the *same polarity rule as `rec`* (positive ⇒ intersect, negative ⇒ union) and is carried verbatim through simplification (refinements are positional, never folded into a variable's identity, so co-occurrence merging can't move or drop them).


**A refinement never changes a type's shape.** It is a claim about the value at a position, not part of the structure carrying it, so `{(𝐷 ⇒ 𝑉) | 𝑝}` *is* a function and `{Mut(𝑉, 𝐷) | 𝑝}` *is* a mutable variable. Every rule that dispatches on or destructures a shape therefore looks *through* the outer layers first — `Type::peel_refinements`, and the handle accessors `Type::mut_value_type` / `as_feed` / `is_handle` built on it, which are what the typing rules and the second-class `Mut` discipline both ask "is this a mutable variable?" with. It is the same claim-versus-structure distinction a trait obligation draws when it reads a base off an operand ([Refinements are transparent](#refinements-are-transparent)): what narrowing consumes is the structure, and the refinement rides along untouched.

A refinement is **required**, so `constrain_subtype` is strict for *concrete* bases: an unrefined concrete value does **not** flow into a refined position (`T ⊀ {T | p}`), and `{T | q} ⊀ {T | p}`. The one subtlety is the `S₂ ⊆ S₁ ∪ refinements(b₁)` clause: when the subtype side's base `b₁` is an **inference variable**, it can still acquire the deficit `S₂ \ S₁`, so the solver flows `b₁ <: {b₂ | S₂ \ S₁}` onto the variable rather than rejecting (the refinement analog of how the record/function arms thread structure through a variable base; it fails later iff the variable resolves to a concrete base lacking those refinements). This is what lets a value that is *already* refined be cast to acquire a further refinement — `{D | p} ⇒ V <: {?a | q} ⇒ V` records `?a <: {D | p}`, stacking `q` over `p` (nested list-comprehension filters). Acquiring a refinement on a *concrete* value is still an *explicit* operation, not subsumption: the explicit `Cast` node from [PR #218](https://github.com/cambra-dev/Cambra/pull/218) (an upcast — `value <: target` — written `cast({D | r} ⇒ V, value)`) makes refinement-acquisition explicit, and the interpreter compiles a refinement on a **collection domain** to a runtime `Restrict`/`Filter` at the iteration boundary (the `Iterate`/`Restrict` arms of `operator_conversion`, where `extent_of` strips the domain refinement into a `Restrict`). The predicate `Expr` of each refinement is inferred/coalesced like any other sub-tree (annotation-borne predicates via `emit_annotation_predicates` / `coalesce_type_predicates`).

**Refinements in the post-inference check.** The post-inference structural check (`infer::check`, reimplemented on the same structural rules as emission via the `Typing` trait — see §2, *The post-inference check*) is **strict and refinement-aware throughout** — it does not strip refinements before its width-subtyping checks. It runs `constrain_subtype` in two places, both fully refinement-aware:

* **Adjacency rules** (a `Compose` link's `prev_cod <: next_dom`, an `Apply`'s argument-vs-domain) check *refinement flow*: feeding an unrefined producer into a refinement consumer is rejected (`T ⊀ {T | p}`), exactly as the solver is. There is **no cast escape** — a producer must already carry the refinement its consumer demands. A `… ≫ (id ≫ cast({D | r} ⇒ V))` chain composes because join planning surfaces the iterated / join-satisfying domain on the *producing* morphism's codomain, so the upstream genuinely supplies `{D | r}` (see the reconstructability bullets below). The producer's refinement and the cast's contract are typically re-minted as distinct predicate terms, so the adjacency relies on the structural-predicate match above.
* **The reconcile** (a node's rule-reconstructed type vs the type inference recorded on it) is the plain strict `rule <: recorded` subtype check, refinements included (the recorded type may be a width-wider supertype — e.g. an annotation). A rule that rebuilds a node's type from its children rebuilds its refinements too, so a recorded refinement the reconstruction lacks is a real disagreement about the node — and in practice it is one specific bug: a **merge point that took one input's refinement** instead of the join of all of them (see the merge law above). Comparing modulo refinements here — stripping both sides, or a refinement-blind relation — is the *only* thing that hides that class, and this is the check best placed to catch it. Keeping it strict is what forced each merge point to join.

For the reconcile to hold, the passes that *introduce* refined types post-inference (lambda-elim, join-planning) must leave each node's recorded type **reconstructable** — consistent with what the bottom-up rules rebuild from its children. These sites were emitting internally-inconsistent or under-refined nodes and are now fixed at the source rather than papered over by relaxing the check:

* **Iterated / join-satisfying extents on producers** (`planning`'s `set_extent` / `refine_extent`). An iteration source produces the refined domain it iterates, so it is symmetric `{D | p} ⇒ {D | p}` (`make_iterate`); a hash join folds its equi-conditions into the key structure with no residual `Restrict`, so the extent it yields would otherwise reach the body's `cast` *bare*. `refine_extent` refines **both sides** for that reason: a data function's domain *is* its data, so refining only the codomain would leave the domain claiming rows the join never produces — readable as a supertype under the contravariant reading of a function, but wrong for a collection, and it puts every enclosing type at odds with the site. Threaded down the combinator's whole function spine so the leaf builtin the Check pass rebuilds from agrees. Reconstructable because a combinator node carries its own function type and `emit_apply` returns *that* codomain verbatim. `make_restrict` builds its refinement directly rather than through `refine_with`, whose trivially-true degeneracy is right for `make_iterate` (an unrefined site should not print `{D | true}`) but wrong here: the caller emits one `restrict` per layer the *site* declared, so dropping a vacuous one leaves the source producing a bare extent while the site — and the body's `{D | true}` cast — still demand the refined one.

* **Dependent groupby refinement** (`lambda_elim`'s cast-wrapped-lambda arm). `groupby` lowers to `λ k → cast({I | key(i) == k} ⇒ A, λ i → c(i))`. Because the key binder `k` is now a genuine **Pi binder** (the refinement closes over it but the *value* does not mention it), lambda-elim emits the Pi-const form `const(cast(c)) : (k) ⇒ ({I | i ▷ c ▷ key == k} ⇒ A)` — the `k`-dependence rides the refinement and is materialized as a `Restrict` at the iteration boundary (the dependent-application model, §4.5). Planning's pointful recogniser (`recognize_groupby_sites` / `convert_groupby_pointful`) matches that Pi-const source directly — identifying the key binder structurally as the free variable on one side of the predicate's equality — and emits the bucketize chain `converse(c ≫ key) ≫ map(c)` **at the source's own type** — `(k: K) ⤇ ({I | key(i) == k} ⤇ V)`, group refinement and Pi binder intact. A group holds the members sharing one key, and a data function's domain *is* its data, so typing a group as the bare `I` would claim every element belongs to every group; the binder has to ride the function type as a Pi or the predicate's `k` dangles.
* **`permute_domain` over a refined morphism** (`join_plan::convert_loop_join`). The combinator is polymorphic in the morphism it rearranges; its declared input type is the morphism's *actual* type (which may carry the join-condition refinement), not a bare `actual ⇒ actual`. Otherwise `apply_function` re-stamps the partially-applied combinator's recorded type to `fun(expr.ty, …)` (carrying the refinement) while its inner `PermuteDomain` builtin keeps the bare declaration — an inconsistent node the reconstruction can't rebuild, because the refinement rides the morphism's *invariant* domain⇒codomain position (where subtyping would demand `T <: {T|p}` *and* `{T|p} <: T` at once).

#### Feed handles as an invariant `History` constructor (`Type::History { kind: Feed }`)

A feed handle is `Type::History { value: 𝑇, domain: 𝐷, kind: HistoryKind::Append }` (displayed `feed(𝐷 ⇒ 𝑉)`) — a function `𝐷 ⇒ 𝑇` carried as two children plus a two-valued `kind` marker. It **shares the `Type::History` variant with a mutable variable** (`kind: Overwrite`, displayed `Mut(𝑉, 𝐷)`); the two were unified from the former `Type::Feed(ρ)` / `Type::Mut{…}` pair (see [`Mut` is a CCL type](mutability.md#mut-is-a-ccl-type)). `let 𝑑 = Defer in body` gives `𝑑` a `Feed`-kind history whose channel `𝐷 ⇒ 𝑇` is the *post-desugar result type* of the binding (a `𝐷 ⇒ 𝑇` channel for fed defers, the defined value's type for `<<=`-defined defers). Like `Hole` and `Infer` the `Feed` kind is **transient**, scoped to inference: `channelize` (which runs after inference) eliminates every defer construct along with its feed histories, and no pass downstream of it may observe one. (This is the feed-handle type of [`Feed` is a CCL type](mutability.md#feed-is-a-ccl-type) — what a defer-mediating UDF parameter carries.)

Below, **`Feed(ρ)`** abbreviates a `kind: Feed` history whose reconstructed channel is `ρ = 𝐷 ⇒ 𝑇`; the `value`/`domain` children are the two halves of `ρ`. An `Overwrite` history reaches the relation as a handle — a read has already dereffed at the rule that emitted it — so the four invariance rules below are specifically the `Feed`-kind behavior.

The typing rules (`infer_simple_sub::emit_defer` / `emit_feed` / `emit_define`): `Defer` emits `Feed(fresh ρ)`; `Feed{name, value}` and `Define{name, value}` type as `Unit`, resolve `name` from the scope like a `Var` use, and constrain their contribution into the target's payload (`Fun(fresh δ, value_ty)` for a feed — the channel *domain* is a desugar artifact, so `δ` stays unconstrained and coalesces to `Infer`; the bare `value_ty` for a define). A target that isn't structurally a feed handle (a lambda parameter — ParamAsTarget) is demanded to be one via the upper bound `target <: Feed(ρf)`; the call-site argument edge meets it there and invariance carries the contribution back to the caller's channel. A bare `Defer` RHS is never generalized (`should_generalize` wants a lambda RHS), so feeds and reads of one defer share one `ρ`; a defer minted inside a generalized function instantiates fresh per call site.

`History` is the lattice's only **invariant** constructor. Feeding is a contravariant capability (a feed contributes an element *into* the channel) while reading is covariant, so a feed handle flowing through a function parameter must propagate feed contributions *backwards* to the caller's channel — a one-way `arg <: param` edge would strand the callee's contribution on the parameter variable. Four constraint rules (`constrain_go`), where `Feed(a)`/`Feed(b)` are same-`kind` (`Feed`) histories:

1. **`Feed(a) <: Feed(b)`** ⇒ both `a <: b` and `b <: a` (invariance — payloads are equated). The payload edges run under **identity morphisms**: a payload is the channel's plain value type, not content inside a Pi binder's scope, so apply-site discharges do not transport into it — and must not, or the two-way edge makes two distinct non-invertible discharges meet at one payload variable (the closure-bridge corner) for ordinary chained defer functions. The cost: a binder-dependent refinement inside a fed value's type is not discharged across the handle (out of scope alongside the filter-feed-through-UDF gaps).
2. **`Feed(a) <: 𝑇`** for non-feed `𝑇` ⇒ `a <: 𝑇` — transparent read (`sum(d)`, `d + 1`, `x <<= y` chains discharge through the handle). The post-inference structural check mirrors this: `CheckCtx::as_function` peels `Feed` like outer refinement tags.
3. **`Fun(…) <: Feed(a)`** ⇒ `Fun(…) <: a` — a *channel-shaped* lhs is the read view of the feed handle (coalescing a use position that both held and read the handle surfaces the bare channel; monomorphization's two-way pin then meets that view against the definition's `Feed`).
4. **`𝑇 <: Feed(a)`** for any other non-feed `𝑇` ⇒ `ConstrainError::NotAFeed` — the write capability cannot be conjured from a plain value (`g(5)` where `g` feeds its parameter).

The shared variant keeps the overwrite/feed operator discipline **on the type**: rule 1's invariance arm matches only *same-`kind`* `History`/`History` pairs, so an `Overwrite` history demanded as a feed (or a feed as an overwrite history) is not equated — the `Overwrite` history arrives as the handle it is and meets rule 4, whose left-hand side is any non-feed shape, as `NotAFeed`. So `<<` into a `:=` mutable variable, or `+=` on a `defer` channel, is a type error with no separate structural check (see [`Mut` is a CCL type](mutability.md#mut-is-a-ccl-type)).

Invariance has no MLsub-blessed polar story, so the two polarity-sensitive mechanisms treat it specially:

* **Extrusion** (`extrude_invariant`): a history's `value`/`domain` variables crossing a level boundary each get a *single* fresh proxy linked to the original by **both** a lower and an upper bound (an equality link through the standard lower×upper closure), instead of the polar one-way link. The proxy mutable variables under both `ExtrudeCache` polarity keys.
* **Compaction/coalesce**: the two children occupy a dedicated `CompactType::history_slot` (carrying the `kind`), recursing at the **same polarity** — by compaction time the constraint-level invariance has already propagated both directions, so this is materialization only, not a second polarity analysis. `simplify_type` walks the slot at the same polarity; refinement/co-occurrence behavior is unchanged.
* **Transparent read at joins** (`dissolve_read_feeds`): rule 2 covers a feed handle meeting a concrete consumer *directly*, but a read can also meet other contributions through a shared join variable (`x + 1` flows `Feed(Int)` and `Int` into the binop's `∀α.(α,α)→α`). At coalesce, a position carrying a `Feed`-kind `history_slot` **alongside** non-feed contributions dissolves the handle into its channel before the contribution count; a feed handle alone (or two handles merged) keeps its constructor. Feeding-then-scalar-reading still errors correctly: the dissolved channel is `Fun(?, T)`, which genuinely collides with a scalar.

Freshening (`freshen_above`) is polarity-free and recurses through the payload like any position, so a generalized DI function (`λ𝑛 → let 𝑥 = Defer in …`) instantiates a fresh feed handle per use site — the "fresh defer per call" semantics.

### The binder slot, and why annotations do not outlive inference

A binder's `ty` records **the type the binder is bound at** — the type its references have. For an unannotated binder that is its initializer's type, but the two are not the same thing, and every binder position resolves the slot the same way: emit writes the type it bound the variable at, coalesce resolves it in place. `let` was once the exception, reconstructing its slot afterwards as a copy of the coalesced RHS type, and that is what made annotations look load-bearing after inference.

Two annotated forms are where the initializer's type and the bound-at type diverge, in opposite directions:

* A **deref-copy** `y : 𝑉 = 𝑥` off a mutable variable `𝑥` binds `y` at the value type `𝑉`, while its initializer is a *history*. Recording the initializer's type made `y` an alias of `𝑥` in the type system — so the second-class `Mut` discipline, which keys on types, then misfired on a variable the user declared immutable: `z = y` was rejected as an unannotated `Mut` alias, and `y += 1` was *accepted* as a write.
* A **mutable variable introduction** `𝑥 : Mut(𝑉) := init` binds `𝑥` at the history `Mut(𝑉, 𝐷)`, while its initializer is a plain value. Recording the initializer's type left the mutable variable's own slot reading `𝑉`, so the transaction-mutable variable scan could not classify it from the slot.

Both readers compensated by consulting `user_annotation`, which held the user's declaration and so happened to answer correctly. That is the proxy the slot's honesty removes, and removing it matters because **an annotation is a pre-inference input**: it is a raw type from lowering, never normalized and never coalesced. A pass that pattern-matches one is reading a shape from before inference ran. So `infer` **clears every annotation on success**, and both post-inference walls pin the emptiness (`debug_assert_annotations_cleared`) — an invariant worth checking rather than asserting, since a stale annotation is only *read* by whichever pass thinks to look, and a leak surfaces as a wrong answer somewhere else entirely.

**Both the clearing and the check follow type slots, not just children.** An annotation does not only ride the expression tree: `groupby` stamps the relation tying its key parameter to its key function onto a node inside the cast target's *refinement predicate*, and a predicate hangs off a type slot, which no `walk_children` reaches. A walk over children alone therefore clears every annotation it can see and then certifies the tree clean while a live one sits in a type — the leak and the check blind in exactly the same place, which is why the check could not report it. Both walks compose `walk_type_slots` with `walk_refined_predicates`, so they cover the same ground inference does when it *reads* an annotation.

Nothing has to outlive the annotation. The one fact a later pass used to need from it — *is this binder a mutable variable?* — is answered structurally instead: only `MutDecl` (a `:=` introduction) and a pass-by-reference `Lambda` param bind one, and a `Let` cannot, because `emit_let` reads through an initializer that is a mutable variable. That retired the `Mut` discipline's rule 3 along with the bit that stood in for the declaration (see `src/ccl/design/mutability.md`, "No aliasing: `Mut` values are second-class (downward-only)").

### Annotation kinds: exact and bounded

An annotation at a binder answers one of two different questions, and CHL spells them differently because the answers diverge.

`𝑥 : 𝑇` is **exact**: the binder's type *is* `𝑇`. The initializer (or, at a parameter, the argument) must satisfy `rhs <: 𝑇`, and everything downstream of the binder sees `𝑇` — the value's own type is not observable through it.

`𝑥 <: 𝑇` is **bounded**: the binder's type is *inferred*, with `𝑇` as an upper bound. The value's own type flows through; `𝑇` only constrains what may reach the binder.

The two coincide only where the value's type already *is* the annotation, leaving nothing to discard. They differ wherever the value's type is a **strict** subtype of it — and the annotation's own shape does not decide that, because a Cambra type carries more than a base:

* **Width.** `x : {a: Int} = (a=1, b=2)` binds `x` at `{a: Int}`, so `x.b` is an error. `x <: {a: Int} = (a=1, b=2)` binds `x` at the record's own type, which still has both fields, so `x.b` is `Int@2`.
* **Refinements.** A literal is typed by its own value ([A literal is refined by its own value](#a-literal-is-refined-by-its-own-value)), so `x : Int = 5` binds `x` at `Int` — the annotation is precisely what discards the singleton — while `x <: Int = 5` leaves it at `Int@5`. Only the second still discharges `arr[x]`'s index-range obligation.
* **Delivery.** Trait narrowing consumes bases that *arrive* at an operand ([Delivery: the watch follows the edge](#delivery-the-watch-follows-the-edge)), and only the exact form puts one there — it binds at `Int`, while the bounded form binds at a variable that `Int` sits above. Both `def f(x: Int): x + "s"` and `def f(x <: Int): x + "s"` are ill-typed and both are rejected with no call site, but not by the same machinery: the exact form delivers `Int`, which narrows the obligation until `"s"` empties it, while the bounded form delivers nothing and is caught instead by [Requirements are read together, once](#requirements-are-read-together-once), reading the requirement against the bound already recorded on the value.

  This last one is a difference in *reach*, not in meaning, and it is the only bullet here that is. Do not read it as the split saying that `x <: Int` promises less; what it promises is stated above, and this row is about which mechanism happens to notice.

The refinement case is worth reading twice: the annotation is a bare `Int` and the forms still differ, because `Int@5` is a strict subtype of `Int`. A "simple" annotation is no guarantee that the two agree — only a value that knows nothing beyond the annotation is.

Both kinds apply at both binder positions, `let` and function parameter, with one rule each. The distinction and the two spellings are both settled; the spec states them and gives the reasoning for the tokens ([chl-spec.md](../../../docs/chl-spec.md), "Two annotation forms: exact and bounded"). Nothing below depends on which tokens they are: the mode is a two-valued property of a binder that lowering reads off the surface and turns into `BoundedHole`-or-not, so the surface and the representation are independent.

| | `𝑥 : 𝑇` (exact) | `𝑥 <: 𝑇` (bounded) |
|---|---|---|
| `let` | bind at `𝑇`; require `rhs <: 𝑇` | bind at the inferred RHS type; require it `<: 𝑇` |
| parameter | bind at `𝑇`; every call site requires `arg <: 𝑇` | bind at a fresh variable; require it `<: 𝑇` |

The bounded column is the *only* behaviour that existed before the split, at both positions: a binder annotation contributed one upper bound and nothing else, because `bind_annotation` is one-way (`inferred <: ann` — an annotation has to admit the value, not equal it). A parameter's type was therefore the **meet** of its annotation and whatever its body demanded, which is worth stating plainly because it is neither of the two readings one expects: in `def f(v <: {a: Int}): v.b`, the annotation admits the argument and the projection widens the demand, so `𝑣` ends up at `{a: Int, b: 𝑇}` and callers must supply both fields. That is still what the bounded form means; the split gave it its own spelling and gave `:` the exact reading.

Neither rule needs a mode test at its binder. A parameter binds at `normalize(annotation)`: exact normalizes to `𝑇` itself, bounded to a variable bounded by `𝑇`, and the old two-step (bind at a fresh variable, *then* reconcile against the annotation) is what made an exact annotation behave as neither reading — it contributed one upper bound among several instead of being the type. A `let` binds at the same normalization of its (completed) annotation, and two special cases fall out as consequences rather than tests: a **deref-copy** (`y: Int = x` off a mutable variable) binds at the annotation because that is what exact *means*, and a bare `_` completes to the initializer's type, which for a mutable-variable initializer is the *value* it reads — so `y: _ = x` binds exactly where `y = x` does, and writing through `y` is rejected the same way.

#### BoundedHole is a marker in a type slot, not a type

The bounded form is represented by a `Type::BoundedHole(𝑇)`, which `normalize_annotation` erases into a fresh variable carrying `𝑇` as an upper bound. It is the same kind of object as `Type::Hole` one rung up: `Hole` is the unbounded case, and the two compose in exactly the positions where a compound annotation is partly specified.

Neither is a type, and that is the first thing to know about `BoundedHole`. `Hole`, `Infer`, and `BoundedHole` all inhabit the `Type` enum because *annotation and binder positions are typed positions*, not because they denote anything: `BoundedHole(𝑇)` is not "the type of values below `𝑇`" — no such type exists, since a bound picks out no set of values on its own. It records an obligation for inference to discharge, and inference discharges it by minting a variable and giving it `𝑇` as an upper bound; the bound then lives where bounds belong, on a variable in the constraint graph.

The consequence is that no *typing* rule may take a `BoundedHole`. There is nothing to subtype against, nothing to narrow, nothing to compact — the solver asserts this rather than inventing a rule (`constrain::extrude`, `compact`). Only the structural walks that rewrite every slot uniformly — substitution, free-variable collection, refinement stripping — pass through one, and they do so because they are indifferent to what a slot means.

Putting the bound *in the type* rather than beside it is forced by the **multi-parameter encoding**, not chosen for symmetry. A `def` with more than one parameter uncurries to a single tuple parameter whose annotation is one `Type::Tuple`, with `Hole` at each unannotated position (`lower::functions::uncurry_params`). So `def f(x: 𝐴, y <: 𝐵, z)` has to express three distinct annotation modes *inside one type*, and `Tuple([𝐴, BoundedHole(𝐵), Hole])` does it with no new plumbing. Carrying the mode alongside the type instead would need a mode *tree* mirroring the type's shape, which is this variant in a worse spelling.

#### BoundedHole cannot outlive inference

`BoundedHole` is inference's to erase: Pass 1 replaces it with an `Infer` variable, and nothing downstream can observe one — not by convention but because **the slot it would live in does not survive inference at all**. See [The binder slot, and why annotations do not outlive inference](#the-binder-slot-and-why-annotations-do-not-outlive-inference); the bounded form needs no lifecycle rule of its own.

That the slot does not survive is what makes the guarantee structural, and following `Hole`'s precedent instead would *not* have sufficed. `Hole`'s discipline is erasure plus a check on `ty` slots (`UnresolvedHole`) — which leaves annotation slots covered by neither, so an un-erased marker can sit in one to the end of inference whenever a compound annotation is partly unspecified. That is survivable for `Hole`, which means "unspecified" and is read as such; it is not survivable for `BoundedHole`, which carries a *bound* that something must discharge. A marker whose whole content is a constraint cannot be left somewhere nothing looks.

The remaining backstop is therefore narrow: a binder `ty` is the only slot a `BoundedHole` could reach, and `collect_type_errors` reports `UnresolvedBoundedHole` there. Nothing is expected to trip it — a `BoundedHole` reaching the solver un-normalized fails earlier, since there is no rule for constraining against one.

#### A Hole inside an exact annotation is still inferred

An exact annotation may be partly unspecified — `x: List(_) = [1, 2, 3]`, or the `Feed(_)` bindings the corpus uses. A `Hole` there means "infer this position", so the binder's type is the annotation **with each `Hole` filled from the corresponding position of the inferred RHS type** (`emit::complete_annotation`). That makes `x: _ = e` exactly equivalent to `x = e`, and `x: List(_) = [1, 2, 3]` bind at `List(Int)`. Records complete by *name*, so a field the annotation does not mention is dropped rather than completed — which is exactly the width an exact annotation discards. A **parameter** has no initializer to complete from, so a `Hole` there is simply a fresh variable resolved from the call sites.

The filling is a structural function on the two types, deliberately not a constraint: binding at a normalized annotation and relying on the one-way `rhs <: ann` edge to drive the annotation's fresh variables does *not* work — those variables are minted at the outer level, after the RHS's level has been popped, and escape inference unresolved. Shape disagreements need no handling here, because a `rhs` that cannot flow into `ann` at all is already an `AnnotationMismatch`.

#### A `Mut(…)` annotation is exact

`Type::History` is **invariant in both payloads**: `constrain` relates two histories of
the same kind in both directions, because a mutable variable is read *and* written
through the same binder. A `:=` binder's type is a `Mut(𝑉, 𝐷)`, and those two facts
together rule out both of the spellings a mutable introduction does not accept. Lowering
rejects them (`lower::stmts::check_mut_decl_annotation`) rather than reinterpreting them:

* `𝑥 <: Mut(𝑉) := 𝑒` — under invariance the only type below `Mut(𝑉, 𝐷)` is `Mut(𝑉, 𝐷)`,
  so the bound admits exactly the annotation and `<:` claims nothing `:` does not.
* `𝑥 : 𝑉 := 𝑒` — a plain value type names the wrong thing. The binder is at `Mut(𝑉, 𝐷)`,
  so reading a bare `𝑉` there would make `:` mean something at a `:=` binder that it
  means at no other.

The invariance argument does not depend on the binder being a `:=`, so it rejects a
bounded pass-by-reference parameter too (`lower::functions::mut_param_history_type`):
a `Mut(…)` annotation is exact wherever it is written.

The consequence for the representation is that a `BoundedHole` never wraps a history,
which `normalize_annotation` asserts. That is worth stating, because the alternative is
representable and tempting: **distributing** the bound into the value position, as
`Mut(BoundedHole(𝑉), 𝐷)`. A mutable variable binder's slot must stay structurally a
`History` — `mut_value_type`, the deref coercion in `constrain`, `mut_elim`, and
`transact_phase` all dispatch on that shape, and a variable standing for the whole handle
would skip a write's `value <: 𝑉` edge — so the value position is the only slot a bound
*could* occupy. But that is a fact about the pipeline, not about what `<: Mut(𝑉)`
denotes; distributing silently re-points the bound at a type other than the one written.
Rejecting leaves "a mutable whose value type is inferred under a ceiling" with no
spelling, which is the honest position: under invariance it is not a bound on the
binder's type at all, and no surface syntax puts a bound in a nested position (see
[chl-spec.md](../../../docs/chl-spec.md), "Two annotation forms: exact and bounded").

#### Exact annotations bound monomorphization

An exact parameter annotation is the program's only lever over specialization count, and this is the sharpest practical consequence of the split.

Specialization is keyed on instantiation identity ([Keying a specialization](#keying-a-specialization)), whose negative read follows a domain's *lower* bounds — the argument that flowed in. With a bounded (or absent) parameter annotation the domain is a variable, so each call site's argument type reaches the key, and the definition splits **per distinct argument type, including per literal value**: `let f = λ 𝑣 → 𝑣 + 1 in let a = f(1) in let b = f(2) in a` yields two clones of one body, distinguished only by the singletons `1` and `2`.

An exact annotation binds the parameter at a concrete, level-0 type. `freshen_above` short-circuits it, every instantiation shares one domain, no argument refinement can reach the domain position, and the uses collapse to a single specialization.

Two caveats keep that from being a blanket guarantee. First, the win is confined to the domain, and the key's *codomain* read follows the consumer's demand — deliberately, since the clone is coalesced under this use's pin and a key blind to the consumer would under-split. So an exact annotation collapses the uses only as far as their consumers agree. Second, the bounded form is genuinely per-call-site checked rather than checked once: `freshen_above` copies a variable's bounds, so the `<: 𝑇` obligation is instantiated with each use and enforced at every argument position.

### Flowing In: normalizing annotations

There is no conversion *into* a solver type — the solver consumes `ccl::Type` as-is. The only adjustment Pass 1 makes is `normalize_annotation`, which readies a user annotation / expected type for constraint solving:

* **Holes (`Type::Hole`):** become fresh `Type::Infer` variables at the current level.
* **Bounds (`Type::BoundedHole(𝑇)`):** become fresh `Type::Infer` variables at the current level, carrying `𝑇` as an upper bound — `Hole` with a ceiling (see [Annotation kinds: exact and bounded](#annotation-kinds-exact-and-bounded)).
* **Refinements:** are **kept** (recursing to normalize the inner) — they ride the lattice natively (above). A `Refinement(Hole, r)` source annotation thus becomes `Refinement(?fresh, r)`.
* **Everything else** — including existing `Type::Infer` vars, `Tuple`/`Record` products, and `Type::Variant` sums — is kept verbatim and handled by the solver's structural constraint rules. Tuples and records are width-subtyped positionally/by name; variants are admissible at both polarities (the dual of records), so they need no fresh-var indirection.

### Flowing Out: coalescing

Once constraints are resolved (Pass 2), `coalesce_compact` resolves each node's `Type::Infer` variables in place:

* **Products:** dense `Index` keys become `Type::Tuple`; `Name` keys become `Type::Record`; a sparse `Index` product (an open/under-determined position) coalesces to a fresh `Type::Infer` rather than a concrete product. **No keys at all become `Unit`** — the product of zero fields, which has exactly one representation (see [docs/chl-spec.md](../../../docs/chl-spec.md#66-the-empty-product-is-unit)); `Type::Tuple([])` and `Type::Record([])` are invalid. The empty case has no keys to tell positional from named keying, so without the collapse each site picks a spelling arbitrarily — here on `rec.is_empty()`, in `product` on a vacuously-all-`Name` test — and two spellings for one type fail to reconcile at the consistency wall, which compares a node's recorded type against one rebuilt from its children.
* **Variants:** materialize into `Type::Variant(Vec<(FieldKey, Type)>)` with tags in `BTreeMap` order. A variant payload sits at a record-field-like position, so it inherits that position's polarity and coalesces by the same rule as a record field value. An all-`Index` variant pretty-prints as a bare `A | B | C`. Arm *order* is a presentation detail and nothing depends on it: arms are keyed by tag everywhere downstream — in a `Type::Variant`, in a runtime union column, and in `variant_project`/`variant_wrap` — so a variant a pass constructs by hand (the writer decision variant ``{`commit{𝑃} | `abort}``) and the same variant materialized by the solver in sorted order are interchangeable.
* **Refinements:** the refinement set carried at a position is re-wrapped as nested `Type::Refinement` layers around the materialized inner type (in first-insertion order — deterministic and, since consumers strip at all depths, order-independent).
* **Incompatible bounds:** if a variable accumulates multiple distinct concrete primitives (e.g. `Int` and `String`) with no tag to discriminate them, the solver emits an `IncompatibleBounds` error. A *tagged* sum is unaffected — ``{`i{Int} | `s{String}}`` is a single `Variant`, not a primitive collision.
* **Recursive types:** the algorithm has no occurs check. With one-way Apply edges a self-application like `λx. x x` produces no cyclic bound graph — it types cleanly (MLsub would give `(α ∧ (α ⇒ β)) ⇒ β`; Cambra drops the unconstrained `α` leg and infers `(?a ⇒ ?b) ⇒ ?c`, an unapplied-lambda type carrying `Infer`s), while *misusing* one (`(λy. y y)(1)`) still fails with `ExpectedFunction`. Should a residual cyclic bound graph ever form, `coalesce_compact` rejects it with a `RecursiveType` error — a defensive check; no current emission path produces one.

---

## 4.5 Dependent refinements via Pi types

Some refinement predicates **close over an outer binder**. The motivating case is group-by: partitioning `xs` by `key_fn` produces, per key `𝑘`, the partition `{𝑖: 𝐼 | 𝑖 ▷ xs ▷ key_fn == 𝑘} ⇒ 𝑉` — the predicate references `𝑘`, bound *outside* the refinement. Expressing, propagating, and discharging such predicates inside the solver is what the Pi-type machinery adds. (This folds in the durable material from the original point-in-time design proposal for dependent refinements via Pi types.)

**Pi types.** `Type::Fun` carries an optional binder: `Fun { name: Option<Name>, domain, codomain }`. `name: Some(𝑥)` is the dependent type `(𝑥: domain) ⇒ codomain`, with `𝑥` bound in `codomain`; `name: None` is the ordinary function type. `emit_lambda` always names the binder from the lambda parameter, so a predicate that closes over the parameter stays bound. The binder is **cosmetic for ordinary functions** — `coalesce_compact_go` keeps it only when the codomain's refinement predicates actually reference it (queried via `subst::type_free_vars`) and strips it otherwise, so monomorphic output is unchanged and equality/printing don't churn.

**Substitutions and contexts (`ccl::subst`).** A `Subst` is a context morphism that maps *term* binders (`Var` names) to replacement `TypedExpr`s. It never relabels a type variable — that is freshening's job. Two flavours: a **rename** `[𝑘 ↦ 𝑥]` (invertible) and a **discharge** `[𝑥 ↦ arg]` (one-way). The traversal is uniform over terms and types: `apply_expr` rewrites each node's type slots via `apply_type` in the same pass, so a substituted binder occurring inside a type-borne refinement predicate is discharged where it sits (no value-only contract, no dangling residual for §6.2 to catch in release builds). It is a true no-op when no substituted binder occurs free in the term — value or type slots — so a vacuous discharge from a non-dependent application changes nothing and shares the predicate `Rc`. Capture is impossible under the Barendregt convention (binder uids are minted once at lowering; copies preserve them) and the engine *asserts* it instead of α-renaming. Predicates are immutable, so a substitution always *rebuilds* a changed predicate (a fresh `Rc`); the engine drives two modes that differ only in what else they touch: **transport** (`apply_expr`/`apply_type`, builds new terms — the constraint-edge flavour) and **in-place rewrite** (`rewrite_expr`, mutates the term tree the caller owns; a predicate the substitution actually touches is rebuilt, one it merely walks past keeps its `Rc` — the pass-level flavour that `lambda_elim::substitute`, `channelize::desugar_substitute`, inlining's beta step, and lowering's uncurrying all wrap). Both modes thread the same `PredMemo`, so occurrences that shared one term are re-pointed at the same result. A **context** (`well_formed` / `type_free_vars`) is the dual *checking* device: a type is well-formed iff its predicates' free term-vars are in scope.

**Edges carry substitutions, stored two-sided in their native direction.** Each entry of a variable's bound lists is a `Bound { self_subst, ty, ty_subst }`: an upper entry on `𝑉` reads `𝑉‹self_subst› <: ty‹ty_subst›`, a lower entry `ty‹ty_subst› <: 𝑉‹self_subst›` (both identity for ordinary bounds). `constrain_subtype` delegates to `constrain_go(lhs, rhs, sl, sr, cache)` — each side under its own morphism. The **Fun/Fun arm derives the binder correspondence** `[𝑘 ↦ 𝑥]` onto the lhs side of the codomain edge, and the contravariant domain edge **swaps the two sides** rather than inverting anything. The var arms record edges verbatim — *nothing is inverted at record time*. A **discharge has no inverse**, so edges are recorded in their native direction rather than pre-inverted and re-inverted during closure (which would degrade a discharge to the identity, silently destroying it whenever a consumer edge is recorded before the producer's concrete codomain arrives — the opaque/higher-order application order, O3). Under identity morphisms every arm reduces exactly to the substitution-free solver, so all monomorphic inference is byte-identical.

**Closure chains by bridging holder views, composing forward only.** When a new edge meets a variable's existing opposite edges, the two entries hold `𝑉` under possibly different morphisms (`lo`, `hi`); `bridge_holder_gap` reconciles them by moving whichever side is movable (substitution application is monotone w.r.t. subtyping): equal morphisms need no bridge; an invertible side bridges by `hi ∘ lo⁻¹` (renames only — lossless); two non-invertible composites that share their discharge part and differ only in correspondence renames are factored (`Subst::split_renames`) and bridged on the rename part. Two *distinct* discharges meeting at one variable is the domain-join corner (O1/O4), guarded by `invert_rename`'s panic — the loud tripwire, never a silent drop. The **constraint cache is σ-aware**: it keys each `(lhs, rhs)` pair on the *set of side-morphism pairs* seen, so `g(0)` and `g(1)` flowing into one position record two distinct edges instead of the second being conflated away; termination holds because cyclic (var⇄var) edges carry renames over the episode's finite binder set, whose composites saturate, while discharges ride acyclic content edges.

**Coalesce forces suspended substitutions.** `compact_go` threads a substitution accumulator: descending a bound edge composes the edge's *rendering morphism* (`edge_render_subst`: `ty_subst`, transported across `self_subst` by rename-inversion, or by the identity for a discharge — exact because the content lives in the post-discharge context and cannot mention the discharged binder, debug-asserted) and the composite is applied — *forced* — at each refinement-predicate leaf. A bound reached transitively through `𝑣 → 𝑤 → …` thus arrives with every edge's morphism composed (the deferred transitive closure recovered by the walk). Identity accumulator ⇒ no-op.

**Dependent application.** `Typing::apply` types `f(arg)`. Emit constrains `fn_ty <: (𝑥: 𝑑) ⇒ result` against an expected Pi (the one-way Apply shape edge of §2) and returns `result` under a suspended discharge `[𝑥 ↦ arg]` on a fresh variable's lower edge, fired on the partition predicate at coalesce. So `groupby(xs, key)(𝑘₀)` types as `{𝑖 | 𝑖 ▷ xs ▷ key == 𝑘₀} ⇒ 𝑉`. The **post-inference check** (`CheckCtx::apply`) re-runs the discharge on the resolved codomain so its reconstruction matches; `force_refinement` rewrites the predicate to the same term in both places, so the two refinements compare equal under structural refinement equality (§4).

The expected binder is **always globally fresh** (proposal §5.2 verbatim; the §3.6 freshness discipline). The two-sided edge storage is what makes this sound at every polarity and in every constraint order: the correspondence `[𝑘 ↦ 𝑥]` and the discharge `[𝑥 ↦ arg]` compose forward along the closure regardless of whether `fn_ty` was concrete at the apply site or resolved only later (the opaque/higher-order case — a dependent function received as a *parameter* — now discharges correctly, unblocking O3 at the graph level). A contravariant position is reached by side-*swapping*, not inversion, so the discharge arrives at a `map`/aggregate's parameter domain intact. The remaining deferral is the domain-join corner — two *distinct* discharges meeting at one coalescing position (O1/O4) — guarded loudly by the closure bridge's tripwire.

**Discharged-argument slot resolution.** A predicate's interior is typed **by construction**, and the invariant that makes that hold is that *substitution never discards a type*. A `Discharge` carries a typed argument term and clones it; a `Rename` materializes as a fresh `Var` node and takes the type of the occurrence it replaces, because α-renaming cannot change a term's type — the type belongs to the position, not to the name. Nothing re-derives a predicate's types afterwards, and nothing may: a predicate's interior is outside the walk that resolves node types (its terms ride a *type*), so a slot left untyped here would survive to the post-inference wall as an unresolved variable with no way to recover it except lexical scope — which is a *name* lookup standing in for a type that was thrown away. (`freshen_above` separately copy-and-freshens a specialization clone's predicate type slots.)

**`let`-closing (codomain extraction).** A `let 𝑥 = 𝑣 in body` node's type is the body's type, which may close over `𝑥`. As that type is lifted out of the `let`'s scope, `coalesce_node` discharges `[𝑥 ↦ 𝑣]` into it (derived from the body's already-closed type, so chained `let`s close to fixpoint) — the design's `let`-closing refinement-move site. Together with the contravariant discharge above, every coalesced node's type is **well-formed in its lexical scope**, checked at the end of inference by `check_scope_valid` (§6.2) in debug builds: a free predicate variable must be bound by an enclosing Pi binder or AST binder, or be a source. A violation is a compiler bug (a substitution-descent miss leaving a dangling predicate binder), reported as an internal `InferError::ScopeViolation`. This is a debug-build regression net: because substitution rewrites type-borne occurrences in the same pass as the term, a dangling predicate binder is structurally unrepresentable; the per-substitution `debug_assert`s in `ccl::subst` remain as fast-path guards.

**Lambda elimination.** A `λ 𝑥 → e` whose binder is free only in `e`'s *type* (a refinement closes over it) — not its value — eliminates to the **Pi-const** form `const(e) : (𝑥) ⇒ e.ty` (`is_free_in_value` distinguishes the two). It also fires after the currying/pairing rule rewrites a captured partition predicate onto a pair domain: the residual `λ __pair → <point-free value>` has its binder free only in that refinement.

**Deferred (flagged in code).**
* **O2 (polymorphic case)** — `freshen_above` copy-and-freshens a refined value's predicate type slots through the shared cache (its `Refinement` arm), so a specialization's predicate is a proper freshen instance rather than a shared `Rc`. Immutable predicate terms are acyclic, so no refinement-cycle guard is needed.
* **O4** — two *different* discharges of one refinement (`g(0)` vs `g(1)`) are distinguished once forced — `force_refinement` rewrites the predicate term and refinement equality is structural (§4) — and the constraint cache is σ-aware, so the two discharges record distinct edges rather than conflating. The residual domain-join corner is two *distinct non-invertible* morphisms meeting at one variable (O1/O4), guarded loudly by `bridge_holder_gap`'s panic tripwire rather than silently dropped.

The pipeline passes downstream of inference treat function types structurally and compare modulo the Pi binder (`Type::without_pi_names`). **Refinement-predicate compilation is deferred out of lambda-elim** (proposal §6.3): predicates ride through inference and lambda-elim in their bare pointful form (a bare boolean over the implicit `REFINEMENT_BINDER`), and **planning** compiles them. Order matters: the group-by / hash-join recognizers run *first*, on the bare form — compiling first would destroy the pointful shapes they match (see the pointful-join-recognizers plan) — and `planning::compile_refinement_predicates` then runs the lambda-elim → simplify sub-pipeline on each remaining predicate (keyed by predicate `Rc` identity) before the generic `iterate`/`restrict` lowering consumes it. This is what lets a refined collection — including a group-by over a *filtered* source (`[sum(x) for x in groupby([y+10 for y in xs if y<6], key)]`) — compile to a runtime `Restrict`/`Filter` rather than reaching op-conversion as an un-compiled predicate. Single-key dependent lookups (`sum(groupby(xs, key)(k))`) and the nested filtered-source group-by both run end-to-end with correct values.

## 4.6 Data vs compute functions

A function either represents a collection or is a capability that can be called.
`Type::Fun` stores which as a `FunKind`, either `Data` or `Compute`.

Lowering chooses the kind from the CHL construct. List literals, comprehensions,
`groupby`, `++`, and registered sources are `Data`; a `lambda` and a `def` are
`Compute`, a generator `def` included — it is a capability whose *result* is a
collection. Where lowering does not yet know the domain and codomain, it states the
kind as a `data_fun` annotation and inference reads that as the stamp. A function
parameter is the one thing lowering cannot decide, having no construct to read: it
gets a kind variable, which the argument pins.

Compute functions follow the usual contravariance on the domain. Data functions are
invariant, because the domain is the exact set of elements the collection holds, so
changing it changes the data. Neither kind converts to the other; they are unrelated
by subtyping.

Downstream phases including inlining and planning dispatch on the distinction, so
every pass carries a function's kind rather than rebuilding one. `Type::fun_like` is
the rebuild that does: it copies the exemplar's kind, so rewriting only a domain or a
codomain cannot turn a collection into a capability.

### Generalizing a collection is filter pushdown

`should_generalize` requires a **capability**: a `Lambda` whose kind is not `Data`. The node test
alone does not get there, because `groupby` lowers to a `Lambda` and its type where that predicate
runs is still `(__gb_k: ?𝑘) ⤇ ((__gb_i: {?𝑖 | __elem ▷ xs ▷ key == __gb_k}) ⤇ ?𝑣)` — variables
deeper than the binding level, so the level test admits it. Only the kind catches the one
collection written as a function.

Note *what* that domain refinement is: the dependent group-key predicate of
[Dependent refinements via Pi types](#45-dependent-refinements-via-pi-types). Lookups at different
keys pin `__gb_k` differently, and a `SpecKey`'s negative read follows exactly that
`arg <: domain` edge — so specializing a grouping per use means **one copy of the source filtered
to each reader's key**, which is filter pushdown. That wins when the predicates are selective and
loses when readers are many and overlapping: `sum(g(1)) + sum(g(2)) + sum(g(3))` rebuilds the whole
partition three times where one `Memo` serves all three. The choice is selectivity against reader
count, and inference cannot make it — it runs before planning knows an extent, so the blanket
refusal is the bounded-worst-case side until there is a cost model to consult. The same decision
waits on the term side, where inlining a collection is
[loop fusion](optimization.md#inlining-a-collection-is-loop-fusion).

### The domain join is a Σ

A join of two data functions is **not** the contravariant meet of their domains. The
domain of a collection *is* its data, so meeting `[0,1] ⤇ Int` with `[0,2] ⤇ Int`
down to `[0,1] ⤇ Int` silently discards the third row — a wrong answer with nothing
in the type recording that it happened.

Nor is the join undefined. It is the dependent sum `Σ (𝑤 ∈ {𝐷ᵢ}). 𝑤 ⤇ 𝑉` over the
candidate domains, whose witness `𝑤` is the runtime branch discriminant and which is
eliminated by distributing the consumer over it. (*Witness* here is the standard
sense — the inhabitant that picks which summand you are in — and is deliberately
kept. It is unrelated to the retired sense of the word, which named a refinement in
its role as a black box to the subtyping lattice; that reading is now spelled out
as a property of the lattice instead, under
[Refinements on the lattice](#refinements-on-the-lattice). A sweep for the retired
term should leave this one alone.) **That Σ is the least upper bound**
— data functions over distinct domains are incomparable, and their join is a
different element of the lattice rather than one of them. So the lattice is
*incomplete* without Σ, and the three rules here are one model:

- **Subtyping** relates two data functions when their domains are the same domain
  ([Data domains are invariant](#data-domains-are-invariant)).
- **Joining** two whose domains differ yields the Σ.
- Where the Σ collapses — the candidates turn out to be one domain — the join is
  that plain data function (`[1,2] if c else [3,4]` is `[0,1] ⤇ Int`, and so is
  `xs if c else xs`).

Σ is not yet representable, so the middle rule currently has no answer to produce
and **diagnoses** instead. That is an acceptable interim state only because it is
*loud*: the alternative to a Σ is an error, not a silent miscompile. Pinned
end-to-end by `conditional_collection_rejected_cleanly`.

Tracking the kind is what makes the three rules statable at all. Without it both
are just functions, the compute lattice's meet applies, and the join silently
narrows — correct for capabilities, row-destroying for collections.

**The same fact surfaces at two phases**, because a join can be forced at either.
When a consumer imposes a concrete demand on the joined value, the domains meet at a
`Fun`/`Fun` edge and the invariant domain rule reports it there
(`ConstrainError::DataDomainMismatch`). When nothing forces it — the joined
collection *is* the program's value, or is only let-bound — the candidates ride to
coalesce as alternatives and are reported there
(`CoalesceError::DomainJoinConflict`). Both are "the join is a Σ"; neither path is
redundant, and Σ has to satisfy both.

**Mechanics.** The decision is split across two phases, and the split is forced. At
the compact merge, a positive `Data ⊔ Data` accumulates its domain **alternatives**
(`CompactFun::domains`, unioned and deduplicated by `union_domains` — never met).
It cannot decide there whether the alternatives are really two domains: a compact
domain still carries inference-variable identity that `simplify_type` may merge
afterwards, so two structurally identical domains can arrive as two alternatives.
Coalesce materializes each alternative to a `Type` and deduplicates *again*, and
that second comparison is the one that decides — one survivor is a plain data
function, two or more is the rejection. A `Data ⊔ Compute` collision is a third
outcome, `KindMerge::Conflict`, reported as `DomainJoinConflict` when it would drop
≥ 2 alternatives and as `KindConflict` when a single slot's kind resolved
contradictorily.

Refinements ride *inside* each alternative domain, so differently-filtered arms of
one source (`[x for x in xs if x > 1]` vs `[x for x in xs if x < 3]`) are two
distinct domains and reject like any other pair — refinement is not a special case
here. Meeting them would claim one domain satisfying both filters; picking either
would claim positions the other branch does not produce.

> **Landed — value-`Case` compilation at one domain.** `lambda_elim` compiles a
> value-selecting `Case` to a union of **gated restricts**: one leg per arm, each the
> arm's domain refined by that arm's branch predicate `π̂ᵢ` (compiled from the
> original `if`/`elif` conditions). The gates are exclusive and exhaustive, so
> exactly one leg is non-empty at runtime — an invariant `lambda_elim` asserts at the
> fan-out boundary (a non-exhaustive value-`Case` would realize an empty collection
> on the uncovered path, a silent miscompile) rather than the solver re-proving.
>
> Every arm shares one domain 𝐷 — the case the domain-join rule admits, and the one
> loop-carried accumulators produce (`if p: acc := x else: acc := y`). The legs are
> therefore partial maps over 𝐷 whose supports the gates keep disjoint, and the
> fan-out assembles them with `DisjointJoin` as `𝐷 ⤇ 𝑐` — the arms' join, stated
> where it is known rather than recovered downstream.
>
> Subtyping needs no rule of its own for this. Assembling the fan-out as a
> copairing would give it a `Variant([{𝐷 | π̂ᵢ}])` domain — a claim that the legs
> live over distinct index sets — against consumers that demand 𝐷, and the solver
> would have to carry an arm recognizing a `Variant` of gated 𝐷s and relating each
> leg `{𝐷 | π̂ᵢ} <: 𝐷` back to it. With the disjoint join the two domains are the
> same type and the ordinary arms apply. See [ir.md](ir.md), "`Copair` and `DisjointJoin` — two collection-combining operations, not one".
>
> Arms at *different* domains have no join to assemble against — see
> [The domain join is a Σ](#the-domain-join-is-a-σ) — so the fan-out is built
> only at one domain. Merging at the lossless join of several domains is the same
> dependent sum that rejection is standing in for, and lands with it.

**`Case` arms join by the lattice.** `emit_case` constrains *every* arm into a
fresh result variable (`require_sub`) instead of requiring equality. Homogeneous
arms recover the old behavior; data-collection arms with distinct domains are the
rejection above. There is no `Mut`/`History` exception: a mutable read derefs into
the join like any other, so a `Case` over two mutable variables types as their *value*, and
the second-class discipline still rejects a selected mutable variable reaching a write
position because rule 1 reads the argument *node* rather than its type (see the
merge-law bullets under
[Refinements on the lattice](#refinements-on-the-lattice)).

> **Deferred — heterogeneous-scalar union (follow-up).** The design goal is for
> heterogeneous scalar arms (`1 if c else "x"`) to coalesce to a union.
> A global positive-atom union at coalesce is **unsound** — it is
> indistinguishable there from a binop-operand join (`1 + true`), which must
> stay a hard error. So heterogeneous scalar arms currently remain an
> `IncompatibleBounds` error; the sound union needs strict scalar consumers
> (binops, …) to impose concrete bounds, tracked as a follow-up.

**The codomain is joined, not preserved — and that asymmetry is principled.** Where
two data arms *do* join (a shared domain), the codomain is the ordinary covariant
lattice join `τ₀ ⊔ τ₁` (`CompactFun::merge` merges the codomain at `pol`, the
domains at `!pol`), forgetting which arm contributed which element type. Loss is
forbidden exactly where it is *silent and destroys data* — the domain, where
dropping an index drops a row with no trace. It is permitted exactly where it is
*visible and only coarsens type* — the codomain: `Int | String` sits in the type,
and a consumer that needs `Int` (say `sum`) fails at *its own* constraint site.
Where the LUB is representable this is a structured coarsening that does not error
(record codomains intersect to their common fields, refinements drop to the shared
base); where it is a **scalar** union it is the deferred piece above and errors at
coalesce, the same `IncompatibleBounds` rejection as `1 + true`.

Two further consequences of joining the codomain, on the record. The correlation is
**recoverable by construction**: the correlated form is a tagged variant with each
arm's own codomain, and a program that needs a branch-aware consumer introduces the
choice *explicitly* (`.Ints(xs) if flag else .Strs(ys)`) and `match`es it — the
case-split tax is paid by the code that benefits from it. And the default keeps
consumer complexity **linear**: if the implicit join preserved correlation, every
conditional would default to a variant every downstream consumer must destructure,
and nested conditionals would multiply the arms through the whole consumer graph.
This direction *depends on* tagged-variant **surface syntax** (`.Foo(x)`
constructors + `match`, the open part of [[type-checker-tagged-variants]]): until
that ships the codomain join is a *forced* loss with no recovery path, not a chosen
one. We are also deliberately declining **flow-sensitive typing** — an
occurrence-typing language could keep the arms correlated through the path
condition `flag` itself, with no tag; Cambra does not narrow on opaque `Bool`s, and
the tagged variant is the substitute.

### Data domains are invariant

The `Fun`/`Fun` domain edge is contravariant, which is right for a *compute*
function: the domain is a parameter, nothing in the language can ask a capability
which inputs it accepts, and shrinking the accepted set only under-promises. A
**data** function's domain is invariant instead — the subtyping half of the same
model [The domain join is a Σ](#the-domain-join-is-a-σ) states.

**One lattice.** Subtyping and joining are the same order, so they cannot disagree.
Suppose the contravariant edge applied to data functions, making a wider collection
a subtype of a narrower one — `[0,10] ⤇ 𝑉 <: [0,5] ⤇ 𝑉`, which is `[0,5] <: [0,10]`
at the domain. Then the least upper bound of the arms of `[1,2] if c else [1,2,3]`
is `[0,1] ⤇ Int`, and `sum` of it returns `3` even when the else-arm ran, with
nothing in the type recording that a row was dropped. Under invariance the two
collections are instead incomparable and their least upper bound is the Σ — which
loses nothing, and is why the two halves fit together rather than trading off.

**Why the stand-in is not free.** The contravariant reading is tempting because it
looks like record width subtyping, which *is* sound: `{a: Int, b: Int} <: {a: Int}`
because a consumer of `{a: Int}` can only apply a key it declared, so the extra
field is unobservable. A data function has eliminators that **reflect** its domain
rather than index into it, and they make the difference observable twice over.

- The declared domain **is the loop bound the program runs**. Op-conversion's
  `Builtin::Iterate` arm builds its iteration source as
  `IterateExtent::new(extent_of(𝐷))` from the *static* domain of the iterate
  marker's predicate. So handing an 11-row collection to a slot declared
  `[0,5] ⤇ 𝑉` does not forget rows the way the record forgets `b`; it emits a
  program that reads six of them and reports the result as the collection's.
- The domain is **reproduced in eliminator results**. A comprehension has the shape
  `𝐷 ⤇ 𝐴 ⇒ 𝐷 ⤇ 𝐵`, so `𝐷` occurs covariantly — in an output — as well as
  contravariantly at application, and a variable occurring in both positions is
  invariant. That is the ordinary variance calculus, not a Cambra-specific rule, and
  it is the whole content of the `Data`/`Compute` split: a compute domain occurs
  contravariantly only, because nothing enumerates it.

There is a coherent language in which the wider collection *should* stand in: one
where a declared domain is a **view**, and narrowing it means "give me this much of
it". Cambra is not that language — and the reason is *not* that a data domain is
currently unwritable. It will not stay unwritable:
[`Array(𝑛, 𝑇)`](../../../docs/chl-spec.md#63-direction-collections-as-functions-tentative),
a data function over `Fin(𝑛)`, is a planned surface type. The reason is that both
things the view reading would buy are better bought elsewhere, and the surface
syntax is what makes them cheap:

- **"Works for any length" is quantification, not subsumption.** The function that
  accepts every extent is `∀𝑛. Array(𝑛, 𝑇) ⇒ …`, an ordinary scheme the solver
  already freshens per use. Contravariant widening is a poor stand-in for
  polymorphism: it relates one pair of extents at one site, and charges the row-set
  guarantee everywhere for it.
- **A deliberate prefix is a term, not a coercion.** A program that wants the first
  five rows takes them, and the truncation is then visible where it happens, at an
  extent chosen by the use site. A subsumption edge hides the same truncation in a
  declaration, and only ever at the width that declaration happens to name.

So the rule is stable under a surface data domain. What the syntax changes is that
the explicit forms invariance requires become *writable*, which argues for the rule
rather than against it.

**How it is enforced: both edges, unconditionally.** When both kinds are concretely
`Data`, the `Fun`/`Fun` arm constrains the domains in *both* directions rather than
contravariantly. That is the only order-independent spelling available: any rule
conditioned on what a domain looks like *at the moment the edge fires* — is it still
a variable, does it carry a refinement yet — makes typing depend on constraint
emission order, so two programs differing only in traversal order could type
differently. Invariance is a property of two types, not of when they are compared.

Both directions is also all it takes. `[`Type::UIntRange`]` relating only by equality
already rejects both base directions, and refinement **drop** (`{𝐷 | 𝑝} ⤇ 𝑉 <:
𝐷 ⤇ 𝑉`) is already rejected one step less obviously, since behind a contravariant
domain it demands `𝐷 <: {𝐷 | 𝑝}`. What the reverse edge adds is the case that
inversion left admitted — refinement **acquisition**, `𝐷 ⤇ 𝑉 <: {𝐷 | 𝑝} ⤇ 𝑉`, an
unfiltered collection standing where a filtered domain is declared. A failure in
either direction is reported as `ConstrainError::DataDomainMismatch`, naming the two
domains; `a_data_domain_relates_only_to_itself` pins all four directions plus the
reflexive case, and the compute counterpart that still relates contravariantly.

**Emitting both directions does not preempt a join.** Two domains meeting at one
variable is a join like any other, so what a domain variable joining `[0,1]` and
`[0,2]` *should* become is the same Σ that the arms of a `Case` become — Σ is the
join wherever it arises, not a `Case`-specific construct, and a domain position is
not privileged. Until Σ is representable that join has no answer at either site,
which is why the same program can be diagnosed from the edge or from coalesce
depending on whether a consumer forces the question early (see
[The domain join is a Σ](#the-domain-join-is-a-σ)). The consequence for the Σ work is
that candidate domains must be expected at a domain variable, not only at a `Case`
result.

The rule fires wherever the edge is drawn, the kind edge with it, including the
post-inference re-check in `check.rs`.

### Deliberately incomplete here

Recorded so a reader can tell a deliberate boundary from an oversight.

- **The rejection is a placeholder for the lossless join, not the intended end
  state.** Every program whose branches produce collections of different sizes is
  rejected — including ones with an obvious meaning
  (`sum([1,2] if c else [1,2,3])` is unambiguously `3` or `6`). What makes this an
  acceptable interim state is only that it is diagnosed rather than miscompiled; it
  is not a semantic position. The dependent sum described in
  [The domain join is a Σ](#the-domain-join-is-a-σ) is the answer, and it
  arrives with the collections work.

- **`KindMerge::Conflict` reaches coalesce with two or more domains only in
  hand-constructed compact graphs** (`coalesce_domain_join_conflict_errs`). That
  outcome needs a `Data ⊔ Compute` collision *and* arms at differing domains; no
  source program in the suite produces both at once. Its single-domain outcome is
  reachable from source, and `joining_a_capability_with_a_collection_is_a_kind_conflict`
  is the route: a capability and a collection arrive as two *lower* bounds on one
  variable, and closure relates a lower to an upper rather than a lower to a lower,
  so neither is ever the left of an edge whose right is the other and
  `ConstrainError::KindMismatch` cannot see it.

- **A var-var kind edge carries nothing, and no program in the suite draws one.**
  A concrete kind on either side of an edge pins the variable; two variables meeting
  record nothing, since what the pair resolves to is not known there and deciding it
  from pins arriving later would make typing depend on constraint order. That is only
  sound while the two sides agree, and instrumenting the arm across the suite fired
  zero times — the case is unreached rather than merely benign. A `debug_assert!` in
  the arm catches a disagreement already present when the edge is drawn; a pin that
  lands on one side afterwards is outside what it can see.

- **Σ is the missing type, and it is missing at two sites.** Because a domain join
  can be forced from a `Fun`/`Fun` edge as well as at coalesce, the Σ work has to
  answer both: candidate domains arrive at a **domain variable**, not only at a
  `Case` result. `DataDomainMismatch` and `DomainJoinConflict` are the two faces of
  the same unrepresentable join, and both are live from source
  (`sum([1,2] if c else [1,2,3])` reaches the first; the same conditional as the
  program's own value reaches the second).

---

## Traits

The constraint lattice can state that two positions are **equal** or **related by subtyping**. That is everything an operator needs when its result *is* one of its operands — `max(xs)` returns an element, `x.f` returns the field — because "is one of" is a shared lattice position. It is not enough for an operator whose result is **computed from** its operands, and `+` is the smallest example: the sum of two values is neither of them.

### Vocabulary

* A **trait** is a named requirement a list of types may satisfy — `Addable`, `Orderable`, `Comparable`. **A trait is not a type**: no `Type` variant, no lattice point, no subtyping edge, and the type grammar and `constrain_go`'s rules are untouched. Types *satisfy* traits.
* An **instance** is one row of a trait's table: the types it accepts, and the types it associates with them. Written `Addable(Int, Int ⇝ Int)` — accepted types, then `⇝`, then the associated ones.
* An **associated type** is a type a trait *names* — `Output`, the type an arithmetic operator's result takes. A trait is a requirement rather than a function, so it associates any number, **including none**. A type is associated only when it *depends* on the types satisfying the trait: a comparison's `Bool` is the same for every pair `Equatable` accepts, so it belongs to the operator's signature and `Equatable` associates nothing — recording it as an association would claim the trait determines something it does not.
* An **obligation** is what one *use* of a trait records: the demand that some instance fit the type positions at that use — one **operand position** per argument the trait takes, and one **associated position** per type it names. It is a single claim with two halves, and neither alone is the obligation: *the operand positions are types some instance accepts*, **and** *each associated position is what that same instance associates*. Every position is an ordinary inference variable, unrelated to the others.

A signature carries an obligation beside its type — `𝑓 : 𝐴 ⇒ 𝐵 requires MyTrait(𝐴 ⇝ 𝐵)` — and inference must find an instance satisfying it. Nothing about that is operator-specific: obligations ride variables into schemes ([Requirements are generalized](#requirements-are-generalized)), so a function inherits the requirements of the operators in its body, and `λ 𝑎 𝑏 → 𝑎 + 𝑏` is `∀ 𝐴 𝐵 𝑂. 𝐴 ⇒ 𝐵 ⇒ 𝑂 requires Addable(𝐴, 𝐵 ⇝ 𝑂)`. What is missing is only the *surface* — no CHL syntax writes `requires` yet, so every obligation is minted by an operator. (`requires` is the keyword the spec reserves for it, in [transactions as contextual parameters](../../../docs/chl-spec.md#87-direction-decided-transactions-as-contextual-parameters).)

An operator's own signature is `𝐴₁ ⇒ … ⇒ 𝐴ₙ ⇒ 𝑅` plus its obligation, for the trait's arity `𝑛`, where `𝑅` is either one of the associated positions or a type the operator fixes. The three shapes the current operators take:

| operator | signature | obligation |
|---|---|---|
| `+` | `∀ 𝐴 𝐵 𝑂. 𝐴 ⇒ 𝐵 ⇒ 𝑂` | `Addable(𝐴, 𝐵 ⇝ 𝑂)` |
| `==` | `∀ 𝐴 𝐵. 𝐴 ⇒ 𝐵 ⇒ Bool` | `Equatable(𝐴, 𝐵)` |
| unary `-` | `∀ 𝐴 𝑂. 𝐴 ⇒ 𝑂` | `Negatable(𝐴 ⇝ 𝑂)` |

Mechanism: `src/ccl/infer/solver/traits.rs`.

An associated position like `𝑂` is an ordinary inference variable, not a marker standing for a computation. So information flows *backwards* through an operator's result, and misusing that result is an ordinary diagnostic: `(1 + 2) and True` fails as a bound conflict. A marker could not do this — the solver cannot compare an unreduced computation against anything — and a function could then not be typechecked without seeing its call sites.

### A trait is a relation, and today it relates only types

A trait over `𝑁` operand positions, `𝐴` associated types and `𝐹` associated
**functions** is an `(𝑁 + 𝐴 + 𝐹)`-ary relation in which the `𝑁` operand types
functionally determine the `𝐴` types and the `𝐹` functions; `⇝` separates the
determining side from the determined one. An instance is one hyper-edge, and
resolution is the search for a hyper-edge consistent with what inference has determined
about the operand positions.

Cambra implements `𝑁 ∈ {1, 2}`, `𝐴 ∈ {0, 1}` (`Output`, or nothing) and **`𝐹 = 0`**,
with the relation built into the compiler rather than declared in CHL.

`𝐹 = 0` is a gap rather than a decision. A trait's rows *do* denote distinct
functions — `Addable(String, String ⇝ String)` is concatenation and
`Addable(Int, Int ⇝ Int)` is integer addition — and a trait that cannot associate a
function cannot say which. The function is therefore recovered twice outside the trait:
`simplify.rs` rewrites the `String` case to `Concat` (see
[BinOp type rules](#binop-type-rules)), and the interpreter picks the machine operation
from the operand column's runtime representation (`apply_binop_column`, in
`src/interpreter/binop.rs`). The type system narrows to a row of types and then declines
to name the code.

Associating functions, and a CHL surface for declaring the relation, are the two
extensions this shape exists to take: the instances are already *data*
(`Trait::instances`), so both are table extensions rather than new mechanisms.

#### What the tables hold

Every instance in every table accepts **base types only**, and every one is
homogeneous — `Addable(Int, Int ⇝ Int)`, never `Addable(Int, String ⇝ …)`. Both
facts are the tables' content, not properties of resolution: nothing in narrowing or
deposit assumes either. So `Equatable` rejecting a tuple, a record or a variant is
what these rows happen to be, and not a judgement that such types are incomparable.

### Refinements are transparent

`{𝑇 | 𝑝}` satisfies a trait exactly when `𝑇` does. This holds by construction: satisfaction is judged on each bound contribution as it arrives, and refinements are peeled at that moment, when the base exists. Peeling at emission instead would have nothing to work on, an operand usually being still a variable there.

Transparency follows from incremental resolution and is permanent. A candidate set only ever shrinks ([Resolution is incremental](#resolution-is-incremental)), and a refinement is one of the things a bound can deliver late; if `{𝑇 | 𝑝}` could satisfy a requirement `𝑇` does not, a refinement arriving after the base would have to re-admit a dropped candidate, and order would start to matter.

Growing `𝐹` above zero would not change this. Choosing between two functions by `𝑝` is dispatch on a fact about a *value*, which a table keyed on types cannot express — and which no refinement survives in any case: `𝑥 + 𝑥` where `𝑥` is `2` produces `4`.

### Resolution is incremental

An obligation is a monotone fact, resolved as the graph fills in rather than by a sweep at the end of solving — the shape [`FunKindVar`](#46-data-vs-compute-functions) already uses for kinds. Each operand position carries a **candidate set** of instances that only ever shrinks; each associated type is deposited on its position as an ordinary lower bound once every surviving candidate agrees on it. Order therefore does not matter.

A contribution arriving at a position is one of three things, and each has its own outcome:

| contribution | example | outcome |
|---|---|---|
| a **base** | `Int` | narrows the candidate set |
| **not determined yet** | a variable, a hole, a `Feed` handle whose payload arrives separately | nothing to say |
| **determined, and not a base** | a tuple, record, variant, function | rejected — no instance accepts it ([What the tables hold](#what-the-tables-hold)) |

The third is a rejection and not silence, because "no base here" is true of both it and the second. A tuple that merely failed to narrow would leave `(1, 2) == (3, 4)` well-typed: a comparison has no associated position to strand, so nothing downstream would object either.

A position that stays in the second row for the whole program — nothing ever determines it — is not a rejection either. Its obligation simply never narrows, and the variable is reported as unresolved rather than as a missing instance.

### What an obligation determines

A deposit records what every surviving instance agrees on. It reaches both kinds of position, at opposite polarities:

| position | bound | because |
|---|---|---|
| associated | **lower** | the obligation is its only source — nothing else constrains it from below |
| operand | **upper** | the table states what *may* reach the operand, not what does |

A lower bound on an operand would invent a value the program never supplied, and would let an under-connected lowering pass by supplying the type its missing edge should have carried. An upper bound cannot: it gives coalesce nothing to resolve *to*.

How much is determined follows from the table. `λ 𝑥 → 𝑥 + 1` is `Int ⇒ Int`, because `Int` at the second position leaves only `Addable(Int, Int ⇝ Int)` and one surviving row fixes every position of it. `λ 𝑎 𝑏 → 𝑎 + 𝑏` determines nothing, and both parameters stay open. Adding `Addable(Float, Int ⇝ Float)` would reopen the first case, two rows disagreeing — which is why a deposit waits for agreement rather than firing on a unique candidate.

### Requirements are read together, once

Narrowing consumes one contribution at a time, so an obligation learns only what is *delivered* to it. Requirements that are individually satisfiable and jointly not therefore pass: in `λ 𝑎 → (𝑎 + 1, 𝑎 + "s")` each obligation narrows through its **other** operand, to `{Int}` and `{String}`; neither set is empty, and nothing compares them.

A pass between emission and coalesce closes this. For each value it intersects what every requirement on that value accepts, with three outcomes:

* **Empty** — nothing satisfies them all, so no argument could. `UnsatisfiableOperand`, listing each requirement together with what the trait's other operand accepts, that being what narrowed it.
* **One base** — the requirements determine the value. It is deposited as an upper bound, and the obligations there are narrowed by it directly, since an upper bound does not reach them on its own.
* **Several** — the value stays open.

Before depositing, the pass reads the bounds the value already carries. A base that disagrees is `RequirementContradictsBound`, naming both it and the required type. Left to the write, the same contradiction reaches coalesce as two `IncompatibleBounds` naming no trait: a *bounded* annotation and a monomorphic operator's operand are ordinary bounds, so no intersection of requirements sees them. An *exact* annotation does not reach here at all — it delivers a base, so the obligation narrows and fails on its own ([Annotation kinds: exact and bounded](#annotation-kinds-exact-and-bounded)).

Both rejections say no argument could work, and they differ in what collides. An empty intersection is the requirements contradicting each other. A bound conflict is the requirements agreeing, on something the program has already ruled out.

Placement is forced at both ends. **After emission**, because that is when a definition's requirements are all recorded. **Before coalesce**, because a generalized definition's subtree is never coalesced in place, so a walk of the tree would see only use-site clones — and a clone that goes unsatisfiable already fails by delivery. The pass repeats **to a fixpoint**: determining one value can leave a neighbouring obligation with a single row, determining another.

**One write lands after the sweep, and it only selects.** An unreachable `match` arm's payload is a position no value reaches, so its type comes from a demand recorded on it or from its own reads, and only coalesce can tell that nothing else did. `pin_unobservable_arm_payload` chooses there: the concrete type an upper bound requires the payload to flow into, else a base every requirement the arm's reads state accepts, else `Unit`. Each is a selection from a set this pass read rather than a restriction past it, which `assert_post_emission_narrowing_selects` checks. The pin records its choice in both directions, because an upper bound does not participate in a merge: the `Case`'s join would read the position as contributing nothing and settle on a type narrower than the arm's own slot, which the post-inference check rejects.

A delivery also tightens what the obligation's other positions accept: `Addable` narrowed to `Int` at position 0 accepts only `Int` at position 1. Nothing re-reads a variable standing at such a position against the requirements this pass already intersected for it. What the pin can deliver bounds the exposure. A base the sweep deposited was narrowed into the obligations by the sweep itself, at fixpoint, so the tightening is not new. `payload_trait_default` delivers `Int`, which every trait table contains, so every sibling intersection still accepts it. A base read off a consumer's bound is neither of those, and an obligation that cannot accept it empties and fails the pin's own assertion rather than narrowing quietly. Whether a stale sibling verdict is reachable at all is unresolved — no program in the corpus reaches one, and the bound is a property of the trait tables rather than of this code.

This is the gap [Typechecking a never-called definition](#typechecking-a-never-called-definition) names. The two are complementary. That walk resolves a dead definition's recorded bounds, which catches `λ 𝑎 → (𝑎.0, 𝑎.foo)`; this pass needs no delivery, and does not depend on whether anything calls the definition.

#### The unit is a place, not a variable

Every position of a requirement is an ordinary inference variable, but a requirement is *about* a value, and one value is generally several variables. A **place** is that value. It is named by a root variable plus the path of field selections reaching it — each element of the path a **step** — and the empty path names the root's own value. `places_under` returns, per place, the variables standing at it together with the requirements they carry; it is one *place*'s requirements that are read together.

Places are found by following **upper** bounds: `𝑣 <: 𝑈` means `𝑣`'s value reaches `𝑈`, so a requirement on `𝑈` is one on `𝑣`. A variable bound stays at the same place, `𝑣` and `𝑈` being two variables for one value; a structural one descends, so in `𝑣 <: (𝑈₀, 𝑈₁)` the requirements on `𝑈₀` belong one field deeper and not to `𝑣`. Each `𝑈ᵢ` is itself a variable, which is why the path is load-bearing rather than decorative: it is what separates the value `𝑈₀` stands for from `𝑣`'s, and what lets variables reached by different routes be recognized as one value.

A variable alone is the wrong unit because the parameter a programmer writes is not one variable. `λ 𝑎 𝑏 → …` uncurries to a lambda over a tuple and rewrites each occurrence of `𝑎` to a projection of that tuple, so each occurrence has its own inference variable and none of them carries both of `𝑎`'s requirements. Written curried, `𝑎` is a binder its occurrences share, and one variable carries both. Only the spelling differs.

Which positions are steps is decided per type former, by an exhaustive match. The rules are one comment per former at `places_under`, in `src/ccl/infer/solver/traits.rs`.

A function's **codomain** is a step; its **domain** is not. Descent groups requirements that constrain the same value, and is not how they are reached — every variable is a root, so all requirements are reached regardless. Across `𝑣 <: (𝐷 ⇒ 𝐶)` and `𝑣 <: (𝐷′ ⇒ 𝐶′)`, the codomains `𝐶` and `𝐶′` consume one value, `𝑣`'s result, and so group. `𝐷` and `𝐷′` are two arguments feeding one parameter — two values — and intersecting their requirements would ask a question the program does not pose. `dom(𝑣)` is a root in its own right, so nothing is missed.

Reading the graph once, at the end, is what [`link_watches`](#delivery-the-watch-follows-the-edge) cannot do: it runs when an edge is **recorded**, so an edge predating an obligation never carries it, and it follows **variable** edges only, stopping at the structural hop a multi-parameter lambda introduces. Two consequences: currying is unobservable, `λ 𝑎 𝑏 → (𝑎 + 1, 𝑎 < 𝑏)` and its curried form taking one type; and `λ 𝑎 𝑏 → (𝑎 + 𝑏, 𝑎 + 1, 𝑏 + "s")` is rejected, where no single requirement is wrong and no variable carries two.

Two problems look like they want an obligation of their own, and are not:

* **A mutable variable's value type** is the *join* over its seed and every write, and the join is already the lattice's: every contribution is a *lower* bound of the mutable variable's value variable, and a positive-position read intersects refinement sets, so a refinement survives exactly when every contribution establishes it. Nothing needs to weaken a contribution to get that — the three sites (`MutWrite`, a mutable binding's initializer, a `Transact` key's seed) flow their contribution in verbatim. A mutable variable with a single contribution therefore *keeps* its refinement (`x := 1` is a `Mut(1)`), which is correct: it really does hold that value at every position.

  A write reaching a mutable variable **through a `Mut` parameter** is one of those contributions, and it arrives by the ordinary invariance rule rather than by a mechanism of its own. `emit_apply` decides pass-by-reference from the parameter read off the head of the application spine, and passes the argument's handle through intact; the `(History, History)` arm then relates the two value types in both directions, which is what makes the callee's writes and the caller's declaration one constraint. Reading the parameter's `Mut` syntactically is sound at that one site, since a pass-by-reference parameter is bound at its `Mut(V, D)` by the only code that mints one. While a deref *coercion* sat in the relation this could not work — the handle met a fresh variable and was read through before invariance could see it — so the contribution had to be supplied separately.

  The parameter is read off the **head of the application spine**, not off the function being applied. An n-ary surface call lowers to a curried `Apply` spine, and `apply` types every application as a fresh variable, so the immediately-applied type is a bare `Infer` for every argument after the first — reading it there would contribute for `fw(x, out)` and silently skip `fw(out, x)`. The spine's length is the argument's position, and its parameter is the domain reached by peeling that many codomains off the head (`parameter_type`). For the same reason there is no composite to walk into: rule 2 of the mutability discipline rejects a `Mut` at every position but a domain's root, so a mutable variable is the parameter or it is nowhere.

  A syntactic strip cannot stand in for any of this: `strip_refinements` returns a `Type::Infer` untouched, so it covers a *literal* seed and nothing else — `x := r.a` would type the mutable variable as `{Int | __elem == 0}`. A second strip, on `MutWrite`'s *target*, buys diagnostic ordering by weakening a check that should hold; the constraint is instead skipped outright when the target is not a mutable variable, and `check_mut_write_targets` owns that diagnosis.
* **A projection's domain** resolving to its open-product *demand* rather than to the value flowing in. Replacing the codomain with a field-selection rule does not fix this, because the demand is load-bearing *inference*: `λ 𝑟 → 𝑟.x` infers `{x: ?} ⇒ ?` from that demand alone, and restoring it as a bound puts the narrow record back on the domain. The problem is that a negative position resolves to its demand, which is the same thing the opposite-polarity fallback exists for — see [Closing the single-sided blind spots](#closing-the-single-sided-blind-spots-no-separate-pass).

A **mutable variable** keeps its extent because nothing strips it. A seed contributes verbatim, so `c := [v for v in xs if 𝑝]` types as the filtered collection it is. That shape then fails downstream — it does not terminate in join planning's `insert_iterate_markers`, while everything before completes (inference, the post-letrec `typecheck`, group-by recognition, `simplify`) — and it is the same unfinished area that makes a *write* to a collection mutable variable panic in `planning::loops`'s `split_decision_compose`. Mutable collections are unsupported either way. The loop is a planning bug to fix alongside mutable-collection support, not a restriction to encode in the type system.

### Delivery: the watch follows the edge

An obligation is attached to each operand variable as a *watch* (`InferVar::watches`). The invariant is **delivery**: a concrete type reaching an operand variable must reach the obligation watching it.

The bound closure does not deliver on its own. Where two variables sit at different polymorphism levels — as a `let` RHS produces, being emitted one level deeper — their edge is recorded by the arm whose closure runs against the *other* side's bounds, so a type already on the lower variable is never re-offered. The graph stays correct but is only *transitively* readable, which coalesce does and emission does not.

A variable's lower bounds are written in exactly four places, and delivery is wired into each:

* `constrain_go`'s concrete arm — delivers the contribution directly.
* `constrain_go`'s var-var arm — propagates the watch *downward*, toward the variables feeding the watched one, and delivers what they already know.
* `extrude`'s proxy seeding, and `freshen_above`'s clone — both seed bounds by direct writes rather than through `constrain_go`.

That the list is closed is an argument about today's code, not something the compiler enforces, and a missed delivery is quiet: the obligation never narrows, so a type is left undetermined and surfaces phases later on an interior node. `verify_narrowing_is_complete` checks the argument instead of trusting it — after emission, every watched operand is resolved against the completed graph, and a resolved base must already have narrowed its obligation. `a_concrete_operand_reaches_its_obligation` covers the four writers, a case per mechanism.

### Requirements are generalized

Obligations ride variables through `freshen_above`, so a generalized function carries its operators' requirements into its scheme. Each use instantiates and resolves its **own** copy — sharing one would let a `String` use empty an `Int` use's candidate set.

---

## 5. CCL-specific inference rules

§1–§4 describe the engine generically; the general two-pass structure (emit → coalesce) is §2. This section covers the per-node wiring specific to CCL's AST — the structural rule each `TypedExprNode` variant emits. `ccl::infer` runs on a `TypedExpr` whose nodes all carry `Type::Hole`, calls the emit rules below per node, and coalesces the resulting constraint graph back onto each `expr.ty` (§2). A residual `Type::Infer(id)` after inference means the coalesce pass left a variable genuinely unconstrained (e.g. the parameter of an unapplied identity lambda).

### `groupby`

`groupby` is not a dedicated node. It lowers to a cast-wrapped key lambda — `λ k → cast({I | i ▷ c ▷ key == k} ⇒ A, λ i → c(i))` — so its typing falls out of the ordinary `Lambda`/`Cast` rules plus the dependent-refinement machinery of [§4.5](#45-dependent-refinements-via-pi-types); planning's `convert_groupby_pointful` then recognizes the resulting Pi-const source.

### BinOp type rules

| Op kind | Operand constraint | Result type |
|---|---|---|
| `Arithmetic` | a trait obligation over two *unrelated* variables — `Addable`, `Subtractable`, `Multipliable`, `Divisible` | the trait's `Output` |
| `Compare` | a trait obligation — `Equatable` (`==`, `!=`) or `Orderable` (`<`, `<=`, `>`, `>=`), which associate nothing | `Bool`, fixed by the operator |
| `Concat` | both operands constrained to `String` | `String` |
| `BoolLogic` | both operands constrained to `Bool` | `Bool` |

The bottom two rows are ordinary schemes, because their operand types are fixed. The top two are not, and could not be: see [Traits](#traits).

**Note**: String + String → `Concat` rewriting is performed at **compile time** (in `simplify.rs`), not at inference time. Inference accepts `(String, String) ⇝ String` as an `Addable` instance and returns `String`.

### UnaryOp type rules

| Op kind | Operand constraint | Result type |
|---|---|---|
| `Neg` | a **unary** trait obligation — `Negatable` | the trait's `Output` |
| `Not` | operand constrained to `Bool` | `Bool` |

### `Case` inference

For each `Branch { guard, body }`: the guard flows one-way into `Type::Base(BaseType::Bool)` (a refined boolean is still a boolean); every body flows one-way into one shared variable. The overall `Case` type is that variable — the arms' **join**. Two arms of incompatible base types therefore collide as `IncompatibleBounds` at coalesce, where a heterogeneous list literal or `Copair` reports it, rather than as an eager mismatch here. A 0-branch `Case` is a malformed AST (lowering never produces one) and returns `InferError::EmptyCase`.

The in-flight conditionals stack replaces the arm unification with a genuine lattice join (fresh result variable + per-arm `require_sub`) — see [Data vs compute functions](#46-data-vs-compute-functions); the strict-equality behavior above is current until that lands.

#### An unobservable arm payload is pinned to what its uses require

An arm naming a tag the scrutinee cannot carry receives no lower bound: no value reaches that payload, and nothing else determines it unless a use of it says something. Such an arm is ordinary code rather than an error (a `match` written for the whole `Option` over a scrutinee inference has pinned to one tag), so inference chooses a type for it rather than reaching the post-inference wall with an unresolved variable. Unobservability is read off the **lower** side alone — a bound *above* the position is a use's requirement, which is what the choice below reads, not evidence that a value arrived.

The rule is **pin to a type the payload's requirements accept**, and a requirement reaches the payload in one of two recorded forms:

- A **subtyping upper bound**, `payload <: 𝑈`, from the binder occurring in a position. When `𝑈` resolves concretely it is the strongest requirement available, and pinning past it contradicts the flow. The commonest shape is the body that *is* the binder (`` `b(w) → w ``), where `𝑈` is the arms' result join: choosing `Unit` there does not merely lose information, it enters that join and collides with the reachable arm's type.
- A **trait obligation**, from an operator read (`w + 1` records `Addable`). The obligations choose from the types their surviving instances still accept.

With neither, nothing observes the payload at all and `Unit` — the type that carries no information — is the choice. The two forms do not compete for one payload: an operand's upper bound is the operator's own requirement variable rather than a concrete type.

Each upper bound is resolved **as its own position**, by a walk entered at that variable rather than as a hop along the payload's bound chain — the distinction [the collapse happens at the position](#the-collapse-happens-at-the-position) draws. Reading it through the payload would collapse its quantifier as a side effect and hand the result to every other variable on the chain; deciding it in the pin is one deliberate choice, at the one variable whose quantifier is being eliminated.

The choice is recorded on the *variable*, not in the binder slot, so every occurrence of it agrees — the slot, the scrutinee's expected variant, and hence an enclosing lambda's parameter type. That is also why the pin precedes the scrutinee's own walk and not merely the branches': the scrutinee's type is the variant these payload variables sit inside, so a pin placed after it leaves that reading stale. Unreachable arms are **kept**, not pruned: an arm for a tag the scrutinee cannot carry projects an empty restriction and contributes nothing, while pruning would narrow the arm set relative to the enclosing lambda's declared domain. `pin_unobservable_arm_payload` in `src/ccl/infer/solve.rs` holds the mechanism, including the ordering constraints that place it inside the coalesce walk.

A refined pin is what makes the compaction identity below load-bearing: a bare variable bound contributes an empty refinement set, and an empty set is absorbing under the positive intersection, so `Int@1` arriving from the pin would be erased by the scrutinee's own per-tag variable. `CompactType::imposes_nothing` names the contribution that says nothing at all and makes it the merge identity, which is what every *shape* component already gets from its `None`.

### Record literals and field access

A CHL record value is a parenthesised list of `name=value` fields:

```python
r = (x=1, y="hello")   # Record([("x", 1), ("y", "hello")])
r.x                        # Apply(r, Proj(ProjKey::Field("x"))) → 1
t = (1, "hello")       # Tuple([1, "hello"])
t.0                        # Apply(t, Proj(ProjKey::Index(0))) → 1
```

**Lowering:** the surface has one postfix form for both keyings — the parser holds the key
verbatim in `Attribute { attr }`, and lowering resolves which `ProjKey` it is. The two are
disjoint because an identifier cannot begin with a digit, so *leading digit* is the whole
discriminator; nothing is inferred from context. `[…]` is collection lookup only, and
lowers to the application it *is* (`c[k]` → `Apply(lower(k), lower(c))`), so a product —
having no domain — is never reachable through it.

- `(name=v, ...)` → `TypedExprNode::Record([(name, v), ...])`.
- `expr.field` → `Apply(lower(expr), Proj(ProjKey::Field("field")))`.
- `expr.n` → `Apply(lower(expr), Proj(ProjKey::Index(n)))`.

**Type inference:** `Record([(k, e), ...])` infers to `Type::Record([(k, T), ...])` where each `T` is the inferred type of the corresponding value expression — identical in structure to `Tuple` inference.

**Lambda elimination:** `Record(fields)` inside a lambda body is treated identically to `Tuple`: each field expression is recursively eliminated, producing `Apply(Record([…elim fields…]), Zip)`. The inner `Record` node carries type `Record([(k, Fun(D,T)), …])` — a record of morphisms — and the outer `Zip` application fuses them via a shared `FanOut`, producing a morphism to a record. This ensures `typecheck` invariants hold: a `Record` node always has a `Record` type.

**Operator conversion:** At the `Apply(Record([…]), Zip)` node, the `Zip` handler dispatches on the argument shape. For a `Record` argument it uses `fan_in_named`, which selects `FanIn::new_named` (function-tiling inputs) or `ScalarFanIn::new_named` (scalar inputs) and preserves the declared field names in the output `Tile::Record`. `Proj(ProjKey::Field(name))` compiles to a `MapResult` using `FunctionDef::RecordField(name)`, extracting the named field from the upstream record tile — identical in mechanism to `Proj(ProjKey::Index(n))` for tuples.

### `Proj` inference — open product domains

A bare `Proj(key)` node — i.e. the projection morphism, not an application of it — is inferred as a function type whose domain is an ordinary structural product constraining only the projected field. There is no dedicated "partial" `Type` variant; width-subtyping does the work:

| Key | Inferred domain requirement |
|---|---|
| `Proj(Index(n))` | `Tuple([?_0, …, ?_{n-1}, ?a]) ⇒ ?a` — an `n+1`-tuple padded with fresh vars |
| `Proj(Field("x"))` | `Record([("x", ?a)]) ⇒ ?a` — a single-field record |

The index domain is a `Type::Tuple` padded with fresh variables up to index `n`; the field domain is a single-field `Type::Record` (see `emit_proj`). Width-subtyping lets either unify with any concrete product carrying at least that field, constraining `?a` to the element type there.

**What the padding costs the diagnostics.** `Type::Tuple` is dense, so "has position `𝑛`" is only expressible as "is `𝑛+1` wide" — a positional projection cannot state a *sparse* requirement the way the named one does. Two consequences the error path has to absorb, since both would otherwise report a shape the program never had:

- A projection past the end fails as a **width** violation, and the first absent position is the value's own width rather than the one the user asked for. So the subtyping edge reports the *widest* position the requirement demands (`constrain_go`'s tuple arm), which for a projection is the only position genuinely demanded — `t.99` on a 3-tuple is missing `.99`, not `.3`. `InferError::MissingField` then states the requested position against the found width, rather than the padded 100-tuple.
- Projecting with the *wrong keying* (`r.0`, `t.name`) is a `Record`-vs-`Tuple` constructor mismatch whose "required" side is the partial requirement (`(?31)`, `{name: ?31}`). A record/tuple mismatch is always a keying confusion, so the message carries that as a hint instead of leaving the partial shape to be read as a type.

A projection's domain appears only at a negative position, so the one-way constraints leave it under-determined; its full structure (the value actually flowing in) is recovered structurally during the coalesce walk by monomorphizing the morphism to its input — see [Apply is one-way](#apply-is-one-way) and [Closing the single-sided blind spots](#closing-the-single-sided-blind-spots-no-separate-pass).

### `Compose` inference

N-ary `Compose([f₀, f₁, …, fₙ₋₁])` is inferred by chaining: each morphism's codomain is constrained as a **subtype** of the next morphism's domain (`constrain_subtype(prev_codomain, d_i)`). This allows a refined codomain (e.g. `Refinement(T, pred)`) to feed into a base-typed domain (`T`) without a type error. The overall type is `Fun(domain(f₀), codomain(fₙ₋₁))`. This case arises when `infer` is run over output from `simplify`, which can produce `Compose` nodes.

### Variant (sum) semantic equality

The post-inference structural checks decide type equality via the solver's `constrain_subtype` (bidirectionally, in `typecheck_compatible`), which compares `Type::Variant` tag sets structurally. Nested sums never reach this comparison: `TypedExpr::copair` flattens at construction (next section), so a `Var(y)` referencing a let-bound sum still contributes a single flat variant.

### Union flattening (construction-time)

`a ++ b ++ c` in CHL parses to right- or left-associated binary AST nodes. **`TypedExpr::copair` flattens at construction time**: any operand that is itself a `TypedExprNode::Copair` is spliced into the outer operand list, so the constructor always returns a flat N-ary node. This makes the invariant **"no operand of a `Copair` is itself a `Copair`"** hold from lowering onward — inference, lambda elimination, and operator conversion never need to look through nested AST. The flat AST flows naturally into a flat `Type::Variant` domain (each operand contributes one tag). `operator_conversion` compiles the N-ary node directly to a single `UnionOperator` with N inputs.

### `check_fully_typed` validation

After coalesce, `infer` calls `check_fully_typed(expr)` to assert that every `ty` and every `TypedBinding::ty` in the tree is a concrete type — no `Type::Hole` or `Type::Infer(_)` anywhere, including inside compound types like `Fun` or `Tuple`. Returns `InferError::UnresolvedHole` or `InferError::UnresolvedInfer(id)` on failure, with the symbolic representation of the offending expression for debugging.

### TODOs

- Infer `Let.ty` from the type of `value` (required before `Let` nodes can be compiled; see [optimization.md](optimization.md#compilation)).
- CHL `match` statement lowering: desugar at lowering time using `Let(__scrut)` + guard expressions (no IR changes needed).

---

## 6. Future work

Directions the current design points toward but does not yet implement.

### General `𝑈 ⇒ 𝑇` cast

The [`Cast`](ir.md#cast--explicit-refinement-acquisition) node is named more generally than the current implementation, which only honours `Fun(Refinement(_, _), _)` targets — i.e. it can only attach a refinement to a collection function's *domain*. The name suggests the full upcast semantics `𝑈 ⇒ 𝑇` (re-view a value of any type `𝑈` at any supertype `𝑇`). Two directions are open: **generalize** `Cast` to the full `𝑈 ⇒ 𝑇` upcast (subject to `𝑈 <: 𝑇`), or **rename** it narrower (`Refine` / `AssertDomain`) to match what it does. Acquiring a *value-level* refinement (a covariant narrowing like `Int → {Int | 𝑝}`) is not an upcast — it is a runtime/SMT-checked narrowing — so the general form must keep that boundary. (An in-code `TODO` on the `Cast` node in `ccl/expr.rs` points here.)

### Pattern-match arm binder referenced by the result type

A `match` arm whose result type carries a refinement closing over an arm-local binder:

```python
def filter_against(tagged):
    match tagged:
        case Pair(a, b): return [x for x in xs if x > b]
        case Single(s):  return [x for x in xs if x > s]
```

The right answer is to *inline the case match into the refinement* — produce a refined type whose predicate is itself a `match` on `tagged`:

```
{𝑥 | match tagged:
       case Pair(a, b): 𝑥 > b
       case Single(s):  𝑥 > s }
```

so the refinement's only free variables are `𝑥` (its own binder) and `tagged` (in scope). This needs the type system to express match expressions in predicate position, the inliner to construct them, and the refinement equality/SMT machinery to handle them. Until then inference rejects this shape with a typing error ("result type references arm-local binder `b`").

---

## 7. Glossary

Consult these definitions as needed; each term is introduced in context in §1–§4 above.

| Term | Origin | Definition |
| :--- | :--- | :--- |
| **`Type::Infer` / `InferVar`** | Algebraic subtyping | An inference unknown. `Type::Infer(Rc<InferVar>)`; the shared `InferVar` carries a stable `uid`, a `level`, and a `RefCell` of lower/upper bounds. The solver works directly on `ccl::Type`, so this *is* the constraint-graph node — there is no separate "SimpleType". |
| **Position** | Algebraic subtyping | A location within a type expression where another type sits (a function domain/codomain, a record field value). Each position has a polarity determined by its path from the outermost type. |
| **Polarity** | Algebraic subtyping | Positive or negative. The outermost type is positive; codomains and field values preserve polarity, domains flip it. Variables at positive positions materialize as a union of lower bounds; at negative positions, as an intersection of upper bounds. |
| **Lower Bound** | Algebraic subtyping | A type `L` recorded on variable `α` such that `L <: α` must hold (a type that "flows into" `α`). At a positive occurrence of `α`, the lower bounds are unioned to form the type at that position. |
| **Upper Bound** | Algebraic subtyping | A type `U` recorded on variable `α` such that `α <: U` must hold (a type `α` "must flow into"). At a negative occurrence of `α`, the upper bounds are intersected to form the type at that position. |
| **Level** | Algebraic subtyping | An integer scope depth; larger = more deeply nested. The outer scope is 0; each nested `let` body adds 1. Used to handle let-polymorphism safely. |
| **Level mismatch** | Algebraic subtyping | During `constrain` involving a variable `v`, the condition that the other side contains a variable whose level is numerically higher than `v`'s. Triggers extrude. |
| **Extrude** | Algebraic subtyping | On a level mismatch, the process of copying a type down to a target level by replacing each too-high variable with a fresh proxy at that level (linked back via the polarity-appropriate bound), so the constraint can be recorded without leaking inner-scope variables. |
| **Scheme (PolyScheme)** | Algebraic subtyping | A generalized type with a cutoff level. Variables whose level is numerically greater than the cutoff are quantified; using the scheme *instantiates* (freshens) them at the current level. |
| **CompactType** | Algebraic subtyping | A flat, per-position bag of contributions (variables, atoms, an optional record shape, an optional variant shape, an optional function shape, and a refinement set) produced for simplification and co-occurrence analysis. |
| **`CompactGraph`** | Algebraic subtyping | A top-level `CompactType` plus a side-table of recursive-variable definitions; the intermediate produced by `compact_type` and consumed by `simplify_type` / `coalesce_compact`. |
| **Coalesce** | Algebraic subtyping | Materializing a `CompactGraph` back into an immutable `ccl::Type`: positive occurrences become a union of lower bounds, negative occurrences an intersection of upper bounds. |
| **`FieldKey`** | Algebraic subtyping | The shared key for record/tuple fields *and* variant tags: `Index(usize)` for positional (anonymous) keys, `Name(SmolStr)` for named ones. |
| **`Variant` (tagged sum)** | Both | The single sum representation: `Type::Variant`, keyed by [`FieldKey`]. Named tags are source-level `` `tag(…) ``; positional (`Index`) tags are anonymous sums (what `++` produces). Width-subtyping is the dual of records (a subtype has *fewer* tags). |
| **`ccl::Type`** | Both | The public, immutable, user-facing AST type — and, since the unification, also the solver's working representation. Inference unknowns are `Type::Infer`; `Hole` is normalized to a fresh var, while `Refinement` is kept and rides the lattice as a refinement. |
| **Refinement** | Both | A `Type::Refinement(T, r)` carries a refinement `r` (an immutable predicate `Rc<TypedExpr>`) — a refinement in its role as a black box to the subtyping lattice. A type holds a *set* of refinements, width-subtyped like records (more refinements ⇒ subtype; `{T\|p,q} <: {T\|p}`). Refinements compare by type-blind structural predicate equality (`Refinement`'s `PartialEq`; pointer-equal predicates short-circuit) — not implication. A refinement is *required* — `constrain_subtype` is strict (`T ⊀ {T\|p}`); acquiring one is an explicit runtime `Restrict` at the collection-iteration boundary, not subsumption. |
| **Let Binding Resolution** | Cambra-Specific | Ensuring a `Let` binding's fully resolved type overwrites the type of any `Var` references to it within the let body. |
| **`InferArena`** | Cambra-Specific | The single owner of every inference variable minted during one `infer()` run. Captures each mint through a thread-local sink and, on `Drop`, clears all variables' bounds to break the `Rc` cycles that mutual subtyping constraints form — the end-of-inference cleanup that reference counting alone cannot do. See §3.2. |
| **Pi type** | Both | A `Type::Fun` with `name: Some(𝑥)` — the dependent function type `(𝑥: domain) ⇒ codomain`, with `𝑥` bound in `codomain` and referenceable by nested refinement predicates. `name: None` is the ordinary function type. See §4.5. |
| **`Subst` / discharge / rename** | Cambra-Specific | A context morphism over *term* binders (`ccl::subst`), riding a constraint edge in a two-sided `Bound { self_subst, ty, ty_subst }` (native direction, never inverted at record time). A **rename** `[𝑘 ↦ 𝑥]` is invertible; a **discharge** `[𝑥 ↦ arg]` (dependent application) is one-way. Composed forward along the closure and the coalesce walk, forced at refinement predicates. See §4.5. |
| **Correspondence** | Both | The binder alignment `[𝑘 ↦ 𝑥]` *derived* by `constrain_go`'s Fun/Fun arm when relating two Pi codomains, carried on the codomain edge so a dependent refinement renames consistently. See §4.5. |

---
[^1]: For example, `def f(x): x` has the Principal Type `a -> a`, and `def map(f, collection): ...` might have the Principal Type `(a -> b) -> [a] -> [b]`, where `[a]` denotes a collection for all `a`.
[^2]: When a function like `def id(x): return x` is generalized into a PolyScheme, type variables minted inside the body are assigned a level numerically higher than the surrounding outer scope's depth — the "cutoff." Variables above the cutoff are strictly local to the function (like `x`'s type, `α`); because they are self-contained they are universally quantified and work for all types. Each call instantiates the scheme by minting a fresh variable for `α`, preventing `id(5)` from colliding with `id("hello")`. Variables at or below the cutoff are free variables captured from the enclosing environment; instantiation passes them by reference so all call sites share the same outer-scope constraints.
