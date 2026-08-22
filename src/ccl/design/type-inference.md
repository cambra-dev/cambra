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
domain-join rejection ([The domain join needs `box`](#the-domain-join-needs-box)) — which is also
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

(Both are reachable from source: `` `tag(payload) `` lowers to `VariantCtor`, and `match` / `case` to a pattern-`Case` — `match` needs no IR node of its own.)

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

### The domain join needs `box`

A join of two data functions is not the contravariant meet of their domains. The domain of
a collection is its data, so meeting `[0,1] ⤇ Int` with `[0,2] ⤇ Int` down to
`[0,1] ⤇ Int` discards the third row, with nothing in the type recording that it happened.

Nor is the join undefined. It is the dependent sum `Σ (𝑤 ∈ {𝐷ᵢ}). 𝑤 ⤇ 𝑉` over the candidate
domains, whose witness `𝑤` is the runtime branch discriminant — the inhabitant that picks
which summand a value is in — discharged by distributing the consumer over it. **That Σ is
the least upper bound**: data functions over distinct domains are incomparable, and their
join is a different element of the lattice rather than one of them. The lattice is
incomplete without Σ.

Tracking the kind is what makes any of this statable. Without it both arrows are just
functions, the compute lattice's meet applies, and the join silently narrows — correct for
capabilities, row-destroying for collections.

[collections.md](collections.md) is the collection design built on the sum.

#### The codomain join

**The Σ is lossless on the domain and lossy on the codomain.** The shared body's element
type is the ordinary covariant lattice join `τ₀ ⊔ τ₁` of the arms' codomains
(`CompactFun::merge` merges the codomain at `pol`, the domains at `!pol`), forgetting which
domain pairs with which element type. Where the LUB is a **structured coarsening** it does
not error — record codomains intersect to their common fields, refinements drop to the
shared base, both at any positive position. Where it is a **scalar union** it is
unrepresentable, and that is the deferred piece: a function returning
`[1, 2, 3] if flag else ["a", "b"]` would type as `Σ (𝑤 ∈ {[0,2], [0,1]}). 𝑤 ⤇ (Int|String)`,
no longer recording "length 3 ⟹ all Int", and that codomain errors at coalesce with the
same `IncompatibleBounds` rejection as `1 + true`. It is a positive atom-join,
indistinguishable there from a binop-operand clash, which must stay a hard error — so the
sound union waits on strict scalar consumers imposing concrete bounds.

The asymmetry tracks whether loss is observable. Dropping an index drops a row and leaves
no trace, so domains join into the candidate set and never meet. A coarsened codomain sits
in the type and a consumer that needs `Int` fails at its own constraint site, so the
shared-codomain Σ is a sound widening — a supertype of the correlated form, into which each
arm injects. Preserving correlation by default would instead make every conditional
collection a variant that every downstream consumer destructures, with nested conditionals
multiplying the arms through the whole consumer graph.

The correlated form is a tagged variant carrying each arm's own codomain,
`Variant([(Index(0), α ⤇ τ₀), (Index(1), β ⤇ τ₁)])`. A program that needs a branch-aware
consumer introduces the choice explicitly (`.Ints(xs) if flag else .Strs(ys)`) and
`match`es it, so the case-split cost is paid by the code that benefits from it. Reaching it
depends on tagged-variant **surface syntax** (`.Foo(x)` constructors plus `match`, the open
part of [[type-checker-tagged-variants]]); until that ships the join is a forced loss with
no recovery path rather than a chosen one.

An unfactored `Σ 𝑇 ∈ {𝑇ᵢ}. 𝑇` has no shared codomain to join, so `box(1) if c else box("x")`
is `Σ 𝑇 ∈ {Int, String}. 𝑇` with nothing coarsened. What is missing there is a rule for
*consuming* one, not a representation
([Deliberately incomplete here](#deliberately-incomplete-here)).

**Flow-sensitive typing is declined.** An occurrence-typing language could keep the arms
correlated through the path condition `flag` itself with no tag; Cambra does not narrow on
an opaque `Bool`, and the tagged variant is the substitute.

The codomain loss is orthogonal to the axis the witness recovers. The witness here is a
*type*-witness (`TypeKind::Enumerated` — which branch domain was taken), so the Σ keeps the
exact domain set. A Σ whose witness kind *describes* its domains recovers a different
correlation — a conditionally-sized collection is `Σ (𝐷: UIntRanges). 𝐷 ⤇ 𝑇`, one shape for
every length. Same `Type::Sigma` machinery either way; only the witness kind differs.

### Subtyping for sums

Three rules, and the third one is an absence.

- **No introduction.** `<:` has no rule putting a value into a sum, so a demand never forms
  one and two collections over distinct domains have no upper bound at all. Every sum is
  formed by a term ([Only a term builds a sum](#only-a-term-builds-a-sum)).
- **Width** — `Σ <: Σ` ([The width rule](#the-width-rule)): every member of the left sum
  lies below some member of the right.
- **On the left** — `Σ <: 𝑇` ([A sum on the
  left](#a-sum-on-the-left-forget-the-witness-or-name-it)): a consumer valid at every
  candidate forgets the witness, and one whose result still mentions it names it instead.

Three premises live elsewhere. Kind containment is the sufficient condition the
implementation uses for width's `∃` ([Witness kinds form a
lattice](#witness-kinds-form-a-lattice)); the search discharging that `∃` runs on ground
candidates ([Where the pairing search runs](#where-the-pairing-search-runs)); and a body
edge over `𝑤 ⤇ 𝑉` decomposes into the ordinary data-function arms, whose domain half is
invariant ([Data domains are invariant](#data-domains-are-invariant)).

Everything else the lattice does with sums is derived from these three, the merge laws
([The merge laws are derived, not chosen](#the-merge-laws-are-derived-not-chosen)) and the
equivalence of the two spellings ([A collection sum has two
forms](#a-collection-sum-has-two-forms-and-they-are-equivalent)) included.

#### The width rule

A `box`ed conditional collection is `Σ 𝑤 ∈ {α, β}. 𝑤 ⤇ (τ₀⊔τ₁)`, the [`Type::Sigma`] that
`TypeKind::into_data_fun` builds: one shared body over the witness, whose candidate domains
are the branch domains. The value is one branch, discriminated by the witness where the sum
is consumed. Refinements ride inside each candidate domain, so differently-refined domains
carry both predicates and never reach `merge_refinements`' positive intersect.

These are general dependent-sum rules (`constrain.rs`), not conditional-collection logic. A
Σ denotes a union — `Σ (𝑤: 𝐾). 𝐵[𝑤]` is `⋃{𝐵[𝑑] | 𝑑 ∈ 𝐾}` — so its subtyping rule is
union-on-the-left: every member of the left sum lies below some member of the right.

```
    ∀ d ∈ K₀. ∃ e ∈ K₁. B₀[d] <: B₁[e]
    ──────────────────────────────────
      Σ (w: K₀). B₀   <:   Σ (w: K₁). B₁
```

**There is no candidate-to-candidate relation to decide.** A pairing `(𝑑, 𝑒)` is discharged
by ordinary body subtyping over the ordinary lattice. For the body `𝑤 ⤇ 𝑉` that is one
`Fun`/`Fun` edge, `𝑑 ⤇ 𝑉₀ <: 𝑒 ⤇ 𝑉₁`. A refinement on a candidate is not a special case:
`Σ 𝐷 ∈ {{𝐷₀ | 𝑝}, 𝐷₁}. 𝐷 ⤇ 𝑉 <: Σ 𝐷 ∈ {𝐷₀, 𝐷₁}. 𝐷 ⤇ 𝑉` holds exactly when
`{𝐷 | 𝑝} ⤇ 𝑉 <: 𝐷 ⤇ 𝑉` does, which is the data-function domain rule one level down
([Data domains are invariant](#data-domains-are-invariant)) — so it does not hold, and two
Σs relate only when their candidates match.

**The body is arbitrary.** [`SigmaType`]'s `body` is a general type and the witness may
appear anywhere in it — twice, in a codomain, under another constructor — because a pairing
instantiates both sides before any edge is emitted, so no edge depends on an unfixed
correspondence. Body subtyping recurses through the ordinary arms, which is also what
relates the two bodies' Pi binders.

Witness-kind subtyping `K₀ <: K₁` is a *sufficient* condition for the rule rather than a
premise of it, and the one the implementation uses. See
[Witness kinds form a lattice](#witness-kinds-form-a-lattice) for the kind level and
[Where the pairing search runs](#where-the-pairing-search-runs) for how the `∃` is
discharged without backtracking.

#### A sum on the left: forget the witness, or name it

Two rules put a sum on the left, differing in what happens to the witness. The first
**forgets** it: `Σ 𝑇 ∈ {𝑇ᵢ}. 𝑇 <: 𝑈` exactly when `∀i. 𝑇ᵢ <: 𝑈`. A Σ value is a pair — a
concrete witness together with an element of the body at that witness — so a consumer
valid at every candidate is valid on the pair, by projecting the witness and dispatching on
it.

A consumer that **preserves** the domain has a result that still mentions the witness, and
relating it to a concrete `𝑈` would already have thrown that away. That case
[names the witness](#consuming-a-sum-naming-the-witness); the forgetting rule is its
degenerate case, where the name turns out not to occur in the result.

Neither rule picks a branch. The type-level rule makes the consumer valid at whichever
candidate the witness turns out to be; runtime branch selection is the value-`Case`
fan-out, which gates each domain `𝐷ᵢ` by its branch predicate `π̂ᵢ` compiled from the
original `if`/`elif` conditions. The gates are exclusive and exhaustive, so exactly one
restricted leg is non-empty. The witness ties the layers: type-level it names which domain
was taken, and at runtime that identity is which gate passes.

The gated-union isomorphism is a **construction**, not a subtyping edge. Planning performs
it once ([Realization asserts rather than
rewrites](#realization-asserts-rather-than-rewrites)): a `Case` typed `Σ 𝐷 ∈ 𝐾. 𝐷 ⤇ 𝑉`
becomes a union typed `Variant({𝑖: {𝐷ᵢ | π̂ᵢ}}) ⤇ 𝑉`, and the node asserts its
pre-realization type so nothing above it changes. There is no `Fun(Data) <: Σ` arm relating
the two, because that arm would build a sum. `Type::Variant` stays: it is still
`++`/`CollectionUnion`'s domain and source-level variants'.

Two facts survive from when this was a subtyping question, and both concern a
**same-domain** `Case`, which is not a sum at all. When every arm shares one domain `𝐷` the
arms' join is the plain data function `𝐷 ⤇ 𝑐` — no Σ, nothing to box — and the gated
partition `lambda_elim` builds subtypes that directly, guarded so a heterogeneous `++` into
a fresh-var domain still takes the ordinary contravariant arm.
And the gates' exclusivity and exhaustiveness is a `lambda_elim` construction invariant
asserted at the fan-out boundary, not re-proven in the solver: a non-exhaustive
value-`Case` would realize an empty collection on the uncovered path.

#### Join is the least upper bound under `<:`, and nothing else

There is no separate join law. A law about what joins may form would be a second place for
the answer to live, free to disagree with subtyping. So the entire content of "a sum is not
formed implicitly" is one absence: `<:` has no
[introduction rule](#only-a-term-builds-a-sum). Two collections over distinct domains then
have no upper bound at all, and their join is a `JoinTypeError` — a lattice fact rather
than a rejection anyone wrote down.

What the program can ask for instead:

| written | type | what it keeps |
|---|---|---|
| `xs if c else ys` | `JoinTypeError` | — no upper bound exists |
| `box(xs) if c else box(ys)` | `Σ 𝑇 ∈ {𝑇ₓ, 𝑇ᵧ}. 𝑇` | both domains, and the discriminant; compiles to the value-`Case` fan-out |
| `list(xs) if c else list(ys)` | `List(𝑉)` | the rows, not which range — so a lookup is optional rather than proven |

Two of those three lose something, and which loss to take is a decision about the program.
That is why the type system declines to pick.

The rest follows without further rules. Boxing where the arms agree costs nothing
([Only a term builds a sum](#only-a-term-builds-a-sum) — a singleton sum does not collapse
but is usable as its content). Nested conditionals flatten, because the width rule takes a
candidate listing whole. `box(xs) if c else xs` is `𝑇ₓ`: a bare `𝑇` is an upper bound of
`Σ 𝑈 ∈ {𝑇}. 𝑈` when the sum is consumed, and no sum is an upper bound of a bare `𝑇`, so the
box is discarded rather than spreading.
### Only a term builds a sum

`<:` has no rule that puts a value into a sum. Every sum is **first formed** by a term, and
there is one term per witness kind.

Read it as a statement about *entering*, not about the syntactic origin of every `Type::Sigma`
value: joining two sums forms a third, and must, since a conditional over two boxed
collections has to have a type. That join builds nothing new — its candidates are the joined
sums' — so the property this section names is intact: nothing reaches a sum except through a
term that says so. A demand never forms one.

**`box` — the enumerated sum.** `Σ 𝑇 ∈ {𝑇ᵢ}. 𝑇` — the witness kind is the listing
`Enumerated{𝑇ᵢ}`, the candidates are whole types, and the body is the bare witness:

```
box : ∀𝑎. 𝑎 ⇒ Σ 𝑇 ∈ {𝑎}. 𝑇
```

An ordinary polymorphic builtin, `FunKind::Compute`, with nothing chosen: `Σ 𝑇 ∈ {𝑎}. 𝑇` is
determined by `𝑎`, so there is no target to write and none to infer beyond
instantiating the scheme at each use site. Three properties, each a consequence of the
rules rather than a stipulation:

- **The candidate position is invariant**, so `𝑎` is pinned to the argument's type
  exactly and `box` never widens first. `box(5)` is `Σ 𝑇 ∈ {5}. 𝑇`, not `Σ 𝑇 ∈ {Int}. 𝑇` — which is
  the point: `box(5) if c else box(6)` is `Σ 𝑇 ∈ {5, 6}. 𝑇` where the unboxed conditional is
  `Int`. Retaining the alternatives instead of joining past them is the whole service.
- **A singleton does not collapse.** `Σ 𝑈 ∈ {𝑇}. 𝑈 <: 𝑇` holds by the witness-forgetting rule and not
  conversely, so a one-candidate box sits strictly *below* its content and is usable
  wherever the content is. That is what makes boxing free where the arms agree, with
  no collapse convention to state anywhere.
- **Nesting flattens**, so `box` is idempotent — `Σ 𝑇 ∈ {Σ 𝑈 ∈ {𝑇ᵢ}. 𝑈}. 𝑇 ≡ Σ 𝑇 ∈ {𝑇ᵢ}. 𝑇`,
  a well-formedness condition on the type rather than a subtyping law, and the same
  candidates-taken-whole rule that gives the width rule its associativity. Compare
  [Union flattening (construction-time)](#union-flattening-construction-time). It applies
  at **materialization** ([`SigmaType::into_type`]) rather than where the sum is
  constructed: `box`'s scheme writes `Σ 𝑇 ∈ {𝑎}. 𝑇` with `𝑎` a variable, so the candidate
  has a shape only once the solver resolves it. The outer binder is the one that survives,
  since occurrences elsewhere in the tree already name it. The listing is non-empty by
  construction, which [`SigmaType::over`] already asserts.

**`box` is not a no-op.** A sum is a pair, so introducing one *pairs the value with its
witness*, and that is real content — unlike [`Cast`](ir.md#cast--explicit-refinement-acquisition),
which re-views a value and compiles away. What the pairing costs depends on the kind.
For an enumerated sum over collections it is free in practice: the conditional is
compiled by the gate fan-out either way, and the realized union's extent already *is*
the selected domain, so the witness is a projection of what the value carries rather
than a field beside it — the same reason collections.md can call the `Map → Collection`
re-pairing runtime-free. For a **described** witness (`Collection(𝑇)`) the domain is
knowable only from the value, and reading it is genuinely new machinery: [`extent_of`]
maps a *type* to an `Extent` today. That is not a Σ-specific gap — it is the same
capability an opaque domain already has (`Type::DataSource` resolves to
`Extent::DataSourceDomain`, a handle to the runtime source), so the witness joins that
family rather than founding one.

**`box` is the only way in there is** — the described kinds need no term of their
own, because Σ-**width** already relates a listing to a description. Width quantifies
over kind members and instantiates *both* bodies at their candidates before emitting an
edge, so it does not require the two bodies to have the same shape:

```
box([1,2,3]) <: List(Int)
  𝐾₀ = Enumerated{[0,3) ⤇ Int},  𝐵₀[𝑑] = 𝑑          (the bare witness)
  𝐾₁ = UIntRanges,               𝐵₁[𝑒] = 𝑒 ⤇ Int
  ∀𝑑 ∈ 𝐾₀. ∃𝑒 ∈ 𝐾₁. 𝑑 <: 𝑒 ⤇ Int                    — take 𝑒 = [0,3)
```

So `Array <: List` is not an edge, but `box(arr) <: List(𝑇)` is, and the membership
test that makes it an edge — `[0, 𝑘) ∈ UIntRanges` — is the guard that stops a
*filtered* range passing as a list. Under domain invariance `𝑒` must be the lhs domain
itself, and `{[0, 𝑘) | 𝑝}` is a `Refinement` rather than a `UIntRange`, so it is
rejected. The guard is reached through the ordinary rule rather than restated.

Keyed entry was already explicit for an independent reason: a collection cannot acquire a
domain refinement by subsumption, so an entry needing one carries an explicit
[`Cast`](ir.md#cast--explicit-refinement-acquisition). So it too needs nothing new.

**`Collection(𝑇)` is therefore not a structural top.** `𝐷 ⤇ 𝑉 <: Collection(𝑉)` was
the edge that made it one, and it goes with the rest of that story — necessarily,
not incidentally. A structural top is an upper bound of *every* pair of data
functions, so with it in the relation every collection join succeeds implicitly and
widens maximally, which is exactly the behaviour `box` exists to make visible.
"Boxing is explicit" and "`Collection(𝑇)` is a top" cannot both hold; this design
keeps the first.

The cost is confined to written abstractions. Ordinary consumption is untouched,
because consumers are domain-*polymorphic* rather than `Collection`-typed: the
aggregate schemes are `∀α γ. (α ⤇ γ) ⇒ …` over a fresh domain variable, so `sum(xs)`,
comprehensions, and `groupby` unify with the concrete domain and inject nothing. What
pays is a parameter actually annotated `List(𝑇)` or `Collection(𝑇)`, whose callers now
write the entry term.

### How a sum flows through the solver

A Σ is a type constructor like any other, and in the compact graph every constructor
gets **its own slot** with its own polarity-dual merge law — `rec` intersects at positive
polarity and unions at negative, `variant` is the dual, `fun` is contravariant on its
domain. A sum gets one too:

```
sigma: Option<CompactSigma>          // beside vars / atoms / rec / variant / fun
CompactSigma { kind: CompactWitnessKind, body: Box<CompactType> }
```

The kind holds **compact** candidates rather than ground types, so a candidate that is
still an inference variable can resolve — which is why a sum's candidates are an
invariant position reached through two-way extrusion proxies (see [Deliberately
incomplete here](#deliberately-incomplete-here)).

#### The compact body holds the witness

The body slot holds the body **whole**, with `Type::WitnessRef` compacted to a nullary
witness *atom* — anonymous, because within one sum's body every occurrence names the same
binder, so materialization re-binds them together. The witness then merges by the law atoms
already have: it matches only itself, and meeting a concrete type is the collision `Int`
meeting `String` is.

Storing the witness-**in**dependent residue instead — a shared codomain, or nothing when
the body *is* the witness — is smaller and cannot express `𝐵 ⊓ 𝑇`. A consumer's `?d ⤇ 𝑉` meeting a
collection's `σ ⤇ 𝑉` is exactly a demand landing **on the witness position**, and it is
that merge — `?d` against the witness — that resolves `?d` to `σ`. A residue has nowhere
to put it. Holding the whole body is what makes every Σ law an ordinary recursive merge
instead of a destructure.

#### One carrier per constructor

Every sum reaches the graph through the `sigma` slot and nothing else does, so a data
function's domain slot holds one domain and a candidate *set* lives only on the witness a
Σ binds ([`CompactSigma`]).

That separation is what makes the two constructors independent rather than two readings
of one slot. It rests on two facts, and both are properties of the model rather than of
the carrier: a join forms no sum (only `box` does), so two data functions over distinct
domains never union their domains in place; and a consumed sum *names* its witness rather than
putting one where a domain belongs. Coalesce asserts what is left — a data function's
domain names exactly one domain — so the invariant fails loudly rather than by silently
materializing a candidate set in a `fun` slot.
#### The merge laws are derived, not chosen

Each is the least upper or greatest lower bound under `<:`, so each is derived rather than
declared. The relation is generated by exactly two rules — width and consumption — and that
"exactly" is load-bearing rather than a third rule: `Σ ⊔ 𝑇` dissolves *because* no upper
bound of a bare `𝑇` is a sum, which holds only if nothing introduces one
([only a term builds a sum](#only-a-term-builds-a-sum)). Nothing here is a separate law that
could disagree with subtyping.

**Positive** — a join, what a value could be:

- `Σ ⊔ Σ` — **union the kinds, join the bodies.** Width relates a sum to another when
  its candidates pair into the other's kind, so the least upper bound is the sum over
  both. This is what makes `box(xs) if c else box(ys)` keep both alternatives.
- `Σ ⊔ 𝑇` — **the sum dissolves.** With no edge into a sum, none lies above a bare
  `𝑇`, so any upper bound of both is a non-sum; consuming the sum then requires it to lie
  above every candidate. The join is `𝑇 ⊔ {candidates}`. `box(xs) if c else xs` collapsing
  to `xs`'s type is this law, not a special case.

**Negative** — a meet, what a consumer demands:

- `Σ ⊓ Σ` — **meet the kinds.** A value satisfying both demands is a sum whose candidates
  pair into each.
- `Σ ⊓ 𝑇` — **push `𝑇` into the body.** Only a sum satisfies a sum demand, and a sum
  satisfies a plain demand by being consumed, so the meet is the sum demand with `𝑇`
  strengthening its body.

The two cross-constructor laws are stated here at the shape they take when the demand
misses the witness; where it hits the witness instead, the same rule reads differently,
which is the next section.

#### `Σ ⋈ 𝑇` splits on where the pairing lands, not on the kind

`Σ ⊓ 𝑇` and `Σ ⊔ 𝑇` relate slots that are *different constructors*, so neither can be
decided slot-against-slot the way `Σ ⋈ Σ` is. Every case is the same instance of the
rules — `𝐵[𝑑]` against `𝑇` for whichever `𝑑` the pairing determines — and what varies is
only whether the answer fits in a carrier that stores **one** body for the whole sum. Four
cases, by where the pairing lands:

1. **`Σ ⊔ 𝑇` against a listing kind — the sum dissolves.** The join is `𝑇 ⊔ ⨆_𝑑 𝐵[𝑑]`, the only
   arm needing the candidates *named*. This is `box(xs) if c else xs` collapsing to
   `xs`'s type.
2. **`𝑇` names a domain the kind admits — the sum dissolves.** `𝑇` picks the candidate
   out, so the pairing is the single instance `𝐵[𝑑_𝑇] ⋈ 𝑇`. This is what monomorphizes a
   `List(𝑉)` parameter to the collection actually passed to it.
3. **The body *is* the witness — the candidates move.** `𝐵[𝑑] ⋈ 𝑇` is then `𝑑 ⋈ 𝑇`, so
   the whole pairing lands on the binder: `Σ (w ∈ {𝑑ᵢ}). w ⋈ 𝑇 = Σ (w ∈ {𝑑ᵢ ⋈ 𝑇}). w`.
   Not a special case but the general rule computed exactly, which a one-body carrier can
   do only when the body either is the witness or (case 4) does not meet `𝑇` at the
   witness's position.
4. **Otherwise the sum survives and `𝑇` strengthens its body.** For `⊓`: only a sum
   satisfies a sum demand, and a sum is below `𝑇` when consumed, so the greatest such
   sum keeps `𝐾`. Nothing is enumerated — which is why a described kind needs no
   discharge of its own here.

The split is **not** listing-versus-described. Case 4 is what a described kind reaches, but
it reaches it because a consumer's fresh domain variable names no candidate (case 2
declines), not because the kind describes; a listing kind whose demand names nothing lands
there too.

Case 2 is the one case needing `𝑇` to inhabit the kind outright, and it is sound only
because such a `𝑇` already lies below the sum. Delete that edge and it becomes a
mismatch — which is exactly the change that makes entering an abstract collection type
require `box`.

#### A collection sum has two forms, and they are equivalent

A conditional collection can be written two ways:

- **factored** — `Σ 𝐷 ∈ 𝐾. 𝐷 ⤇ 𝑉`, a sum over *domains* whose body is the collection
- **unfactored** — `Σ σ ∈ {𝐷ᵢ ⤇ 𝑉ᵢ}. σ`, a sum over whole *types*, what `box` builds

Both directions are plain Σ-width, so with a shared element type they are **equivalent**:

```
U <: F   for 𝑑 = 𝐷ᵢ ⤇ 𝑉 take 𝑒 = 𝐷ᵢ:      𝐵ᵤ[𝑑] = 𝐷ᵢ ⤇ 𝑉  =  𝐷ᵢ ⤇ 𝑉 = 𝐵բ[𝑒]
F <: U   for 𝑑 = 𝐷ᵢ      take 𝑒 = 𝐷ᵢ ⤇ 𝑉: 𝐵բ[𝑑] = 𝐷ᵢ ⤇ 𝑉  =  𝐷ᵢ ⤇ 𝑉 = 𝐵ᵤ[𝑒]
```

With element types that differ, `U <: F` still holds (codomains are covariant, `𝑉ᵢ <: ⨆𝑉`)
and the converse fails, so the unfactored form is strictly below — it keeps per-candidate
element types that factoring joins away. Operationally they agree: one is a pair (which
collection, that collection), the other a pair (which domain, a function on it).

Neither form can be dropped. A **described** kind has no unfactored spelling — `List(𝑉)`
names infinitely many domains, so there is no candidate list to pair with a codomain — and
writing one would need kinds that classify whole collection types, carrying an element
type, rather than domains. And the forms cannot be *segregated* by kind either, because a
described sum and a listing sum have to meet: a `List(𝑉)` annotation and a `box`ed
conditional collection arrive as two bounds on one variable.

So both circulate, and the two places that compare sums have to see through the
difference:

- **Σ-width** compares them through the *fibered view* — each candidate as
  `(domain, element)` — which is the rule's `𝐵₀[𝑑] <: 𝐵₁[𝑒]` decomposed the same way the
  factored/factored case already decomposes it, into a domain pairing plus element edges.
  Comparing raw *candidates* instead asks `𝐷₀ ⤇ 𝑉 <: 𝐷₀`, an arrow below a range, which
  never holds — which is why the relation between the forms looked absent rather than
  derivable.
- **`CompactSigma::merge`** puts both into one form before merging, because kinds and
  bodies merge slot against slot and a witness body has no merge with an arrow body. It
  normalizes to factored, since that is the only form a described kind has.
- **Destructuring a sum in function position** reads it through the factored view too
  (`SigmaType::factored_view`, the `Type`-level counterpart of `CompactSigma`'s). A
  consumer needs a domain and an element type, and only the factored form spells either
  out. The element type is the candidates' shared codomain, taken at the base they refine
  where they differ only by a refinement: a claim some candidates make and others do not is
  not a claim about the sum, and `Int@1 ⊔ Int@2` is `Int`. Candidates whose bases differ
  share no element type at all, so there is no arrow to read and the destructuring fails
  by name.

#### Instantiating the body

Every rule is written in terms of `𝐵[𝑑]`, and both levels have it
([`SigmaType::instantiate_body`]). Instantiation is witness substitution with one scoping
asymmetry: a nested sum's **body** is not descended into (its witness belongs to that
binder, and substituting would capture), its **kind** is (candidates are written in the
outer scope). So the rules transcribe directly:

```
width:  ∀ 𝑑 ∈ 𝐾₀. ∃ 𝑒 ∈ 𝐾₁. 𝐵₀[𝑑] <: 𝐵₁[𝑒]
elim:   ∀ 𝑑 ∈ 𝐾.  𝐵[𝑑] <: 𝑈
```

#### Materialization

Coalesce materializes a one-candidate kind as a plain data function and a kind of two or
more as the conditional-collection Σ (`TypeKind::into_data_fun` — the candidate domains
sharing the joined codomain). A data-⊔-compute collision is a loud coalesce error:
`DomainJoinConflict` where two domains meet at one position, `ComputeWhereDataRequired`
where a capability is demanded as a collection.

Candidate order is first-contribution order, and that is a guaranteed contract: it fixes a
deterministic materialization and the discriminant order the value-`Case` fan-out indexes
by. Nothing in subtyping depends on it, because a candidate set is a **set** and the width
rule quantifies over its members rather than pairing them off by position.

Nested conditionals **flatten**. A Σ re-entering compaction lands in the same slot with its
candidates enumerated (`compact_go`'s `Sigma` arm), so `join_witness_kinds` folds them in
and `box(box(xs) if p else box(ys)) if q else box(zs)` forms one flat
`Σ 𝑤 ∈ {xs, ys, zs}. 𝑤 ⤇ 𝑉` rather than a nested Σ. A candidate domain is therefore always
a ground data-function domain, never itself a Σ.

### Witness kinds form a lattice

A kind **classifies types**. [`TypeKind`] is therefore a level above [`Type`], with the
same three questions asked of it: is `𝐾₀ <: 𝐾₁`, what is `𝐾₀ ⊔ 𝐾₁`, what is `𝐾₀ ⊓ 𝐾₁`.
`TypeKind::Any` is the **⊤** of that lattice — the kind that admits every type.

Two things about that relationship are easy to get backwards, and both matter for
anything built on this.

**A kind is not a property of a type, and a type does not have "its" kind.** A type
inhabits an **up-set** of kinds: `[0, 3)` inhabits `UIntRanges`, and `Any`, and
`Enumerated([[0,3)])`, and `Enumerated([[0,3)], [0,5)])`. There is no function from a type
to a kind to invert. What *is* determined by a type is the **minimal** kind containing it —
the singleton listing `Enumerated([𝑑])` — and where the implementation appears to "recover
a kind from a domain" it is forming that representative and then asking containment, never
inverting anything. [`witness_type_kind`] does this for a compacted position; the post-coalesce
kinding check does it for a resolved type.

**`TypeKind` classifies types, not domains.** Nothing in [`TypeKind::admits`] or
[`TypeKind::contains`] mentions domains. The reason every type a kind classifies today
*is* a domain is that the grammar has exactly one kind-carrying slot — a Σ's witness
([`Witness::Type`]) — and a Σ's witness is the data function's domain. That is a fact
about current usage, not a restriction on the notion, and a second kind-carrying position
would need no change to the kind level.

Alongside subtyping, each **described** kind carries one further thing: a **membership
predicate** on a type — is this type a dense prefix range (`UIntRanges`), anything at all
(`Any`), and whatever a later kind adds. Membership and kind subtyping are different
questions and want different signatures. Membership takes a *type* and answers about one
kind; subtyping takes two *kinds*. A listed kind is contained in a described one exactly
when every one of its candidates satisfies that kind's membership predicate — which is how
the two compose, and the only place they meet.

Keeping them apart is what makes a new kind cheap: a variant, a membership predicate, and
a row in the kind order. Nothing in `constrain.rs` changes.

**Away from listed-vs-listed, the order is what the lattice reads rather than a computed
kind.** `order_witness_kinds` runs `contains` in both directions and reports which side is narrower;
a meet keeps the narrower, a join would keep the wider, and unordered is a conflict. In
practice only the **meet** reaches it: every join, at both representations, is a union of
listings, because a value carrying an annotation has had its domain narrowed to a concrete one
before it reaches a join. Two reasons reading the order is the right shape where it is used:

- **One relation, so nothing can drift.** `Array <: List` orders the same way in the compact
  lattice as it does in Σ-width, because it *is* the same call. A separately-implemented
  join would re-encode the same reasoning in a second place.
- **The answer has to be one of the inputs.** A `CompactWitnessKind` carries compacted
  *contents*, not just a kind. Computing a fresh kind would discard them, so the lattice
  operation must *select* a side.

Listed-vs-listed is the exception on both sides, and not by omission: a join **unions**
candidates and a meet merges the contents of two single candidates, neither of which is a
containment question. The union is the one lattice operation that *computes* rather than
selects — and it computes a fresh listing while discarding nothing, because a listing carries
its candidates. Every other pairing delegates to containment, so the one relation still decides
them, which is why `order_witness_kinds` reads the order rather than a pair of join/meet functions
being written.

`Any` holds ⊤ structurally — `contains` answers for it before looking at `self`, rather than
carrying a row per kind — which is what gives `UIntRanges ⊔ Any` an answer (`Any`, since ⊤
absorbs) where the pairing previously conflicted.

Containment reports the edge by returning `Some`, carrying whatever is left to discharge
([`KindObligations`]) rather than a verdict to interpret — so a rejected edge cannot leave
a caller holding obligations it gathered on the way. Where there is no constraint graph to
emit into, `contains_ground` requires the residue to be empty; sharing that one function
between the compact lattice and the post-coalesce check is what keeps them from drifting
from the Σ-width rule they must agree with. See [What the kind level needs from the
solver](#what-the-kind-level-needs-from-the-solver).

#### The wired witness kinds

`TypeKind::Enumerated` is the finite listing [`box`](#only-a-term-builds-a-sum) builds.
`TypeKind::UIntRanges` is the kind of every index range, which is what a `List` is:
`List(𝑇) = Σ (𝐷: UIntRanges). 𝐷 ⤇ 𝑇`. They divide the grammar — **`Enumerated`
classifies whole types and its Σ's body is the bare witness; a described kind classifies
domains and its Σ's body is an arrow over the witness** — which is what tells the two
shapes apart from the witness alone, with no flag to carry.

Making `List` a *kind* rather than a scalar value-witness collapses its rules into the
general one. `list([1, 2, 3])` checks `{[0, 3)} ⊆ UIntRanges`, the same containment
Σ-width runs, reached from the entry term rather than from a subtyping edge. There is no
`{𝑖 | 𝑖 < 𝑛}` domain refinement to discharge, because the kind already says "a dense prefix
range" — which closes a hole the refinement had: a gate that strips refinements before
testing for a range admits a *filtered* collection `{[0, 𝑘) | 𝑝} ⤇ 𝑇` into `List(𝑇)` and
hands it the length witness `𝑘` for a domain with holes. A `Refinement` is not a
`UIntRange`, so kind membership rejects it.

Consuming either kind [names the witness](#consuming-a-sum-naming-the-witness) the same
way. A described kind has no candidate list to present, so a rule that handed the sum over
as the consumed domain would have nothing to hand over but the sum itself — which is why
naming, and not presenting, is what makes the two kinds share one rule.

A **bounded** `List(𝑇)` parameter annotation (`a <: List(𝑇)`) and a consumer's `𝐷 ⤇ 𝑉`
demand are two upper bounds on one variable, and the solver never relates two upper bounds
to each other — so `meet_witness_kinds` decides between a described kind and an enumerated
candidate set by `TypeKind::contains`: containment means the listed side is the narrower,
and an `Array(2, 𝑉)` demanded of a `List(𝑉)` parameter meets at the `Array`. Anything
unordered conflicts loudly. The **exact** form has no such meet, because it leaves no
variable for the two bounds to land on: `a: List(𝑇)` binds the parameter at `List(𝑇)`
itself ([Annotation kinds: exact and bounded](#annotation-kinds-exact-and-bounded)). Under
the exact form a collection parameter is domain-abstract however concrete the argument is,
so a comprehension over it gives back `Σ 𝐷 ∈ UIntRanges. 𝐷 ⤇ 𝑇` rather than the caller's
`[0, 2]`.

Membership in a described kind tests a domain's shape, so a computed collection —
whose domain is still a variable at emit — records a kinding constraint instead
([What the kind level needs from the solver](#what-the-kind-level-needs-from-the-solver)).
The constraint has to live on the **variable** rather than be re-checked from the syntax
later, because no annotation is left on the tree by then: monomorphization rebuilds the
`let` and drops `user_annotation`, the binding becoming an anonymous `__mono`.

`TypeKind::Any` is two containment rows: everything is contained in the universe, and the
universe in nothing narrower, which is what rejects consuming a `Collection` where a
concrete domain is demanded. The **keyed** witness is the one still to be wired, as its own
kind over a `Refinement(𝐾, ⟨opaque key token⟩)` domain — a new kind, not a new witness
flavour.

### What the kind level needs from the solver

There are two things called "kind" here, and they sit on opposite sides of one line:

> A classifier needs its own **inference variable** when *both* (1) membership in it is
> not decidable from the thing classified, and (2) some position must leave it **open**
> for later uses to determine. Fail either and there is nothing to solve for.

[`FunKind`] fails both. On (1) it says so outright: *FunKind is a **provenance** property,
not a function of the domain* — no inspection of an arrow reveals whether it was born a
collection or a capability, since the *same* domain backs either ([Data vs compute
functions](#46-data-vs-compute-functions)), so
there is no membership predicate to write. On (2), note that a *concrete* stamp passes
through unchanged — a list literal is stamped `Data` at construction, a bare lambda
`Compute` at `emit_lambda` — so stamping alone would leave nothing to infer. What forces
[`FunKindVar`] is the **unannotated function parameter**, which leaves the kind open and
lets its uses decide: `sum(c)` forces `Data`, applying `c` as a capability forces
`Compute`. Hence the full apparatus — identity, a [`KindPin`] recording which of the two points
pinned it (or both, which is the conflict), links to the vars above it, and resolution at
coalesce. It pins rather than bounds, because `Data` and `Compute` are incomparable and
there is nothing to accumulate.

[`TypeKind`] fails (1), and [`TypeKind::admits`] *is* that failure made concrete: a
predicate answering membership from the type alone. So (2) never has to be asked, and no
kind variable is needed. It is worth spelling out why that holds rather than treating it
as a coincidence.

**Kinds are constructed, not inferred.** A kind occupies exactly one position in the
grammar — a Σ's witness ([`Witness::Type`]) — and every site that writes that position
names the constructor syntactically:

- an **annotation**: the constructor in the source *is* the choice (`List` → `UIntRanges`,
  `Map(𝐾, 𝑉)` → `Keyed(𝐾)`, `Collection` → `Any`).
- **`emit_case`**: the kind is the enumeration of the arms, and which arms exist is
  syntactic.
- **`SigmaType::over`** on a singleton: given by the caller.

So there is no site that must write "a Σ over some kind to be determined". What is open at
such a site is always the **types inside** the constructor, and those are types:
`Enumerated([?5])` is a known constructor with an open type in it — the kind-level
analogue of `Map(?K, 𝑉)`, not of `?T`. A kind variable would be an unknown of the wrong
sort for the only thing that is ever unknown.

Correspondingly, the two questions inference asks about kinds both have a known kind in
them. *Containment* relates two known kinds. *Membership* asks whether an unknown **type**
inhabits a known kind, which lower and upper **types** cannot express: no type 𝑇 has
`?5 <: 𝑇` iff `?5` is a range. With nowhere to record it, containment has to answer
immediately, which forces a third verdict and a parallel obligation list on the constraint
cache instead of the record-then-resolve the solver already does for types.

**The missing thing was a kinding constraint on a type variable**, and it is now
[`InferBounds::kinds`]: a third constraint slot beside `lower` and `upper`, holding the
kinds whatever the variable resolves to must inhabit. It is not a bound, because it is not
a relation to a type. It is also not **polar** — an assertion about an eventual resolution
is the same fact at either position — so merging two variables' constraints is a plain
conjunction and both scope-crossing paths carry it at both polarities.

The route from record to discharge is the one the bounds already take:

1. **Emission.** `contains` hands the pair `(?𝑣, 𝐾)` back as an obligation and the Σ-width
   arm records it on the variable — without knowing what `?𝑣` will become, which is the
   property that makes it a solver constraint rather than a gate.
2. **Compaction.** The variable walk folds its kinding constraints into the position it
   contributes to ([`CompactType::kinds`]), exactly as it folds its bounds. This is what
   removes the need for a side channel: the constraint arrives where the answer is formed.
3. **Coalesce.** When the position materializes to a type, the **minimal kind containing
   that type** — the singleton listing — is tested against each constraint. Nothing may
   remain outstanding, since post-coalesce there is no graph left to emit into, which is
   what `contains_ground` states.

Because the constraint carries types, it has the same level exposure as an ordinary bound:
`extrude` and `freshen_above` must carry it, or a scope boundary launders it away. That is
not a theoretical hazard — dropping it in `freshen_above` makes a generalized definition's
requirement survive only on the scheme's own variable, which nothing resolves, so *every*
call site type-checks regardless of its source
(`test_kinding_constraint_survives_instantiation`, and
`extrusion_carries_a_kinding_constraint_at_both_polarities` for the other boundary). Both
paths also freshen the kind's own type children, since a parameterized kind carries types
like any other position.

**Only one half of containment needs a recorded constraint**, and the line falls along
listed-versus-described:

- a **described** kind is a *predicate*, so `Enumerated([𝐷₀, 𝐷₁]) <: UIntRanges` is a
  **conjunction** of atomic membership obligations, one per candidate. Atomic conjunctions
  are exactly what a bounds graph records, which is why this half becomes a recorded
  constraint.
- a **listed** kind is a finite *disjunction*: `Enumerated([𝐷₀]) <: Enumerated([𝐸₀, 𝐸₁])`
  is `𝐷₀ = 𝐸₀` **or** `𝐷₀ = 𝐸₁`. A bounds solver records conjunctions of atomic
  constraints; a disjunction needs a *choice*, and a choice here is neither confluent nor
  backtrackable. So this half rejects an unresolved candidate outright, which is what keeps
  a Σ from being formed before coalesce ([Where the pairing search
  runs](#where-the-pairing-search-runs)).

A candidate is undecidable **only** when it is a bare variable. Every other head — a refinement, an
arrow, an atom — is already readable by the predicate, whatever variables sit inside it.
`{[0, 𝑘) | 𝑝}` is a `Refinement` and therefore not a `UIntRange`, and no resolution of 𝑘
changes that. So the constraint attaches to a variable, never to an arbitrary type.

#### What would change the answer

The claim is conditional on (1) above, so it ends if `admits` stops being writable.

`Set(𝐾)` versus `Map(𝐾, unit)` is a genuine failure of (1): with the kind unrepresented
they are the same type, and no inspection of the domain they share distinguishes them. What that costs the solver depends on where the distinction goes. Putting it **in the
kind** trips both conditions — membership stays undecidable and positions remain that must
infer it — so it forces a kind inference variable with bounds and coalesce-time resolution,
for the same reason [`FunKindVar`] has them. A **provenance stamp** like [`FunKind`]'s fails
(1) but never leaves the classifier open, so needs no variable. A **nominal type head**
restores (1) outright, so it needs neither: whether a value is a set of keys or a map to
units becomes readable from the type. That last is the
[tentative direction](collections.md#the-kind-is-declared-not-read-off-the-shape),
where its costs are priced; what matters here is only that a decidable classifier needs no
solver machinery.

**Kind polymorphism is a third thing, and not this one.** An operation generic over the
collection kind that *preserves* it — `filter` on a `Map` yielding a `Map`, on a `List`
yielding a `List` — needs quantification over kinds in a scheme, which is a different
mechanism from a unification variable with bounds. Today `Collection` is ⊤, so such an
operation widens to the top and loses kindedness rather than abstracting over it. And it
is **not** obtained for free by preserving the domain: whether a kind survives is a
property of the type an operation *writes*, and the subtyping arm underwrites nothing here,
since it admits no refinement edge at all.

### Where the pairing search runs

The rule's `∃` is a search, and a search inside a **bounds-recording** solver is
hazardous: different pairings record different constraints on inference variables, so the
choice is not confluent and a wrong commitment cannot be undone. That is the real reason
the existential is not simply written into `constrain_go`.

It decomposes, though, because the two halves of a body edge have different dependencies.
For the conditional-collection body, pairing `(𝑑, 𝑒)` yields:

- the **codomain** edge `𝑉₀ <: 𝑉₁` — the same for every pairing, since one codomain is
  shared across a sum's candidates and the witness does not occur in it. Emit it eagerly.
- the **domain** edge relating 𝑑 and 𝑒 — pairing-dependent. Defer it.

The search's precondition is therefore **ground candidates**, not a particular time.
Comparing two ground types records nothing on any variable — bounds live on the variables,
not on the constraint cache — so a failed attempt leaves no trace and the choice is
confluent. (A scratch cache keeps a failed attempt out of the real one's cycle-breaker
memo, but that is hygiene; groundness is what makes the attempt harmless.) A candidate
that is *not* ground gets only the `𝑒 = 𝑑` instance, which needs no search.

Today that precondition holds **at emission**: every listing-against-listing edge in the
suite arrives with ground candidates, because a Σ only exists there by annotation or by
coalesce having materialized one. So the search runs inline in `constrain_sigma_width`,
and no deferral channel is needed. Post-coalesce becomes the necessary home only once
candidates can be non-ground at emission — which is what forming the Σ at the join
introduces ([Deliberately incomplete here](#deliberately-incomplete-here)), and is the
same argument that puts a membership predicate's discharge late
([Entering a collection type whose domain has no shape
solver](#what-the-kind-level-needs-from-the-solver)).

The codomain edge is not merely an optimization to emit early — it *has* to be emitted
during emission, because **post-coalesce records no bounds**. Anything needed to resolve a
variable must go in while the graph is still being built; withholding it until discharge
would not delay a check, it would produce a worse inference result. Deferral is available
only for what is purely a *check*, which the pairing is and the codomain is not.

**No witness survives a pairing.** The rule never asks which sub-terms mention the
witness: a pairing determines both sides, and the two halves above are emitted directly
rather than by handing instantiated bodies to `constrain_go`. Every other Σ arm likewise
destructures the body through [`SigmaType::body_fun`], so no uninstantiated body is ever
compared — and `Type::WitnessRef` reaching a subtyping edge is therefore `unreachable!`.

That is not merely an unused case. `Type::WitnessRef` is nullary, so an arm relating two
witnesses could only mean "treat the left and right witnesses as the same thing" — the
`𝑒 = 𝑑` reading of the rule rather than the rule, since the left's choice is
arbitrary-but-concrete and the right may answer it *differently for each* left choice.

The tempting alternative — introduce the two witnesses abstractly and compare bodies under
an assumption `𝑤₀ <: 𝑤₁`, Fsub-style — is the rule for a bounded **∀**, not for a sum, and
it is *incomplete* here. Check `Σ 𝐷 ∈ {𝐷₀}. 𝐷 ⤇ 𝑉 <: Σ 𝐷 ∈ {𝐷₀, 𝐷₁}. 𝐷 ⤇ 𝑉`, which is sound: the body edge
`𝑤₀ ⤇ 𝑉 <: 𝑤₁ ⤇ 𝑉` has the witness in a *contravariant* domain position, so it needs
`𝑤₁ <: 𝑤₀` while the assumption supplies `𝑤₀ <: 𝑤₁`. Rejected. A Σ is existential in its
witness, so the left's choice is arbitrary-but-concrete and the right may answer it
*differently for each* left choice; one abstract pair with one assumption forces a uniform
correspondence, which is strictly weaker.

**Width is one-directional, and nothing here is an exact cover.** `∀ 𝑑. ∃ 𝑒` places no
distinctness requirement on the pairing: two of the left's candidates may pair with the
same right candidate, because the rule asks only that every value the left sum can hold
is one the right sum can hold.

That is worth stating because the *other* correspondence in this design — a realized
`Case`'s legs against a sum's candidates — is an exact cover: every candidate needs its
own leg, since a gated partition must realize the whole sum, and the per-leg edge is
covariant refinement width rather than the contravariant domain edge width emits. The two
are not special cases of each other, and the reason they never have to be reconciled is
that the second is not a typing question at all: realization performs the isomorphism
after inference and asserts the pre-realization type ([Realization asserts rather than
rewrites](#realization-asserts-rather-than-rewrites)), so no subtyping rule ever pairs a
leg with a candidate.

The search is the rule: `Enumerated`/`Enumerated` containment hands back a
[`KindObligations::pairing`] and `constrain_sigma_width` discharges it, so a candidate
with no verbatim counterpart can still pair with one its body edge relates to
(`sigma_width_pairs_candidates_by_their_body_edge_not_by_equality`). Set membership
remains as the `𝑒 = 𝑑` instance — the discharge available where there is no solver
([`KindObligations::holds_structurally`]), and the only one available for a non-ground
candidate.

What the search does *not* do is invent edges. Whether a pairing exists is decided by
the body edge, so the direction a refined candidate relates to its bare base is the
data-domain rule below — which relates them in neither direction — not something this
rule settles. And an unresolved
candidate still rejects rather than recording a constraint, which is what keeps a Σ from
being formed before coalesce ([Deliberately incomplete
here](#deliberately-incomplete-here)).

### Where the conditional-collection Σ comes from

A Σ is a **factored union**. `Σ 𝐷 ∈ {𝐷₀, 𝐷₁}. 𝐷 ⤇ 𝑉` is `(𝐷₀ ⤇ 𝑉) | (𝐷₁ ⤇ 𝑉)` with the shared
part pulled out and only the varying part enumerated. Cambra has no general unions —
coalesce rejects `Int | String` — so the Σ *is* the union, restricted to where a factoring
exists: data functions with a joinable codomain.

A sum is formed by a term ([only a term builds a sum](#only-a-term-builds-a-sum)), so what
this section locates is not where the Σ is formed but where its **candidate list** is. That
is the lattice join — the point where a variable's lower bounds become one type — which is
coalesce, and not the `Case`.

The decisive case is a conditional whose arms are both **parameters**:

```
def f(a, b, c):
    b if a else c
f(True, box([1, 2]), box([1, 2, 3]))
```

At the definition there is nothing to enumerate — both arms are inference variables, and
neither `box` is even in scope — and yet the use site correctly yields
`Σ σ ∈ {([0, 1] ⤇ Int), ([0, 2] ⤇ Int)}. σ`, while `f(True, 1, 2)` yields `Int` from the
same definition. No syntactic rule at the `Case` can produce that, because the candidate
list does not exist where the `Case` is written.

Each law about the candidate list is likewise a **join law**, and the lattice already
satisfies all of them:

| law | join property | observed |
| --- | --- | --- |
| candidates are the arms' | union | `Σ σ ∈ {([0, 1] ⤇ Int), ([0, 2] ⤇ Int)}. σ` |
| nested conditionals flatten | associativity | one three-candidate Σ, not a nested Σ |
| identical arms dedup | idempotence | one candidate, still a Σ — the `box`es put it there |
| the codomain is shared | the codomain join, which may **fail** | heterogeneous arms are rejected |
| unboxed collection arms | no upper bound exists | a `DomainConflict`, not a silent narrowing |
| scalar arms produce no Σ | the same join, intersecting refinements | `1 if c else 2` is `Int` |

**What the join must not do is destroy the candidates.** That was a real defect, and it was
not about timing: [`CompactFun::merge`] applied the lossless data law at the *positive*
polarity only, unioning candidates there, while the negative branch met unconditionally and
so merged two data domains' *contents* into one position. The distinction that fixes it is
between an alternative and a demand:

> A listed domain carrying **content** is an alternative the value actually has — two at
> one position means a conditional collection, and for a data function those never
> collapse, because its domain *is* its data. A **bare variable** carries no alternative:
> it is a consumer's fresh domain awaiting resolution, which is what
> [`KindOrder::Resolves`] resolves to the other side.

So alternatives accumulate at either polarity and demands still narrow. `denoted_domains`
survives only as the reading of positions that predate this rule; a merged bag of
alternatives is no longer produced on the join path, so the association between a candidate
and its refinement is kept rather than guessed back.

#### `Case` arms join by the lattice

`emit_case` constrains every arm into a fresh result variable (`require_sub`) rather than
requiring equality, so arms meet at their join. Homogeneous arms join to their common type;
data-collection arms with distinct domains form the conditional-collection Σ. There is no `Mut`/`History` exception:
a mutable read derefs into the join like any other, so a `Case` over two registers types as
their value, and the second-class discipline still rejects a selected register reaching a
write position because rule 1 reads the argument *node* rather than its type (see the
merge-law bullets under [Refinements on the lattice](#refinements-on-the-lattice)).

Consuming a conditional collection through a comprehension
(`[f(x) for x in (box(xs) if c else box(ys))]`) compiles: `lower::comprehension` floats the
source `Case` out of the map so it never becomes a Σ applied to an index, each arm is built
as a data-kinded `Compose`, and the boxed arms then join into one Σ.

### A variable's lower bounds are one value

**Where the pointwise closure looks wrong, and is not.** A variable's lower bounds are
closed against each new upper bound one at a time, which is right in general: `∀𝑖. 𝐿ᵢ <: 𝑈`
and `⋁ᵢ 𝐿ᵢ <: 𝑈` are the same demand in a lattice. It looks wrong for a data function's
**domain**, because two data functions with distinct domains have no `Fun` least upper bound
— their join is the Σ — so a *contravariant* domain edge per candidate would demand the
consumer's domain lie below **every** candidate, i.e. below their meet, which is the silent
narrowing a lossless data join exists to rule out.

The trouble is the edge, not the closure. Consuming a sum does not emit a domain edge at all:
it **names** the witness (see [Consuming a sum: naming the witness](#consuming-a-sum-naming-the-witness)),
and a name is not a bound. Two arms of one conditional reaching one consumer therefore emit
the *same* thing rather than two competing bounds, and the pointwise closure computes the
right answer with nothing assembled ahead of it.

#### One value, one witness

What makes that work is a fact about the variable, not about any
edge: a variable whose lower bounds are dependent sums holds **one** value.
However many arms describe it, the conditional that built it made one choice. Each arm
arrives under whatever binder the term that built it minted, so those binders are competing
names for a single witness, and `unify_sum_witnesses` settles it by α-converting them onto
one — written back to the variable, so compaction reads the same identity off these bounds
that constraining used.

Which name it picks is the whole of witness identity, and it is one rule read from two sides:

- **Unanimous binders are adopted.** A variable that is merely *carrying* one sum
  onward must not rename it, or the value and its consumers would name different witnesses.
- **A disagreement mints.** A variable at which several sums *meet* holds a new
  choice — which arm the conditional took — that none of its inputs is. Borrowing an input's
  name instead is what conflates two conditionals that merely share an arm
  (`a_source_shared_between_two_joins_keeps_the_joins_apart`).

The choice is **sticky**: made once and kept, so an edge drawn before the second arm arrived
names the same witness as one drawn after. That is what removes constraint **order** from
the picture, and it is not obvious — it was initially got wrong here. It is tempting to think
the sum must be a snapshot taken when the consumer's demand is recorded, which would work
only for a `let`-bound conditional collection, whose arms are on the variable before anything
consumes it, and never for a **UDF parameter**, whose demand is recorded while typing the
body with no candidate yet in existence. Nothing is snapshotted; a name is fixed, and the
candidates keep accumulating under it.

**The join itself happens at compaction**, where every join happens — `join_witness_kinds`
over the `sigma` slot, off these same bounds. Assembling one at constraint time as well
would compute it twice, by two rules, and recompute it on every arriving upper edge; that
recomputation is what made a joined sum's binder need an identity stable under
recomputation, which no function of accumulating bounds can be. Two consequences follow for
free. **Associativity**: a nested conditional deposits an already-joined Σ as a lower bound,
and unioning candidate *sets* flattens `Σ 𝑇 ∈ {𝐷₀, Σ 𝑈 ∈ {𝐷₁, 𝐷₂}. 𝑈}. 𝑇` to
`Σ 𝑇 ∈ {𝐷₀, 𝐷₁, 𝐷₂}. 𝑇` with no rule of its own. **Cross-kind meets**: a `List(𝑇)`
annotation and a consumer's `𝐷 ⤇ 𝑉` demand meet as two bounds on one variable, and
compaction is the one place with an order to read them in.

Only the element type stays pointwise, for the ordinary reason: codomains are covariant, so
their join is a position, and each candidate's flows into it.

#### Consumption is decided at the type level

A Σ may be consumed into a
type that does not mention the witness; if the result mentions it, the result is itself a Σ.
The split is by whether the witness occurs in the consumer's result: a *domain-discarding*
consumer `𝑔 : (𝑑 ⤇ 𝑉) ⇒ 𝑊` with 𝑑 not free in 𝑊 genuinely loses the witness, while a
*domain-preserving* one `𝑔 : (𝑑 ⤇ 𝑉) ⇒ (𝑑 ⤇ 𝑊)` carries it through, so `𝑔(x) : Σ (𝑤: 𝐾). 𝑤 ⤇ 𝑊`
and its domain must be related to the **witness** rather than to a materialized union.

Read another way, a domain-preserving consumer is **domain-polymorphic** — `∀𝑑. 𝑑 ⤇ 𝑉 ⇒ 𝑑 ⤇ 𝑊`,
the type of `map` — and applying one to a Σ distributes it over the witness. There are three
places that distribution could happen, and only the third is general:

1. **syntactically, at lowering** — `lower::comprehension` floats an inline source `Case` out
   so each arm becomes its own data-kinded `Compose`, which means a passing inline program
   exercises no Σ machinery at all. It cannot apply when the source is a variable: there is
   no `Case` to float.
2. **by monomorphization** — a collection-consuming UDF is `Compute`, so it beta-reduces per
   call site. The obstruction is ordering: inference must succeed before inlining runs, but
   the type would only be expressible after it.
3. **at the type level** — consuming the sum against its witness, above. The only one that covers a
   `let`-bound conditional, which has no call site to inline through, and the only one that
   makes Σ closed under domain-preserving consumption.

Pinned by `domain_preserving_consumption_of_a_conditional_collection` and
`a_conditional_collection_survives_every_shape_of_consumer`.

**Elimination names the domain rather than presenting one**, for a listing and a described
kind alike. What matters here is what it does *not* do: presenting a listing kind's
candidates as a discriminated union would be the tagged union, isomorphic to the sum but not
equal to it, and the tagged domain would leak into the consumer's result type and re-enter
the candidate list as a spurious extra candidate the next time that result was joined. The
isomorphism is performed where it is a *construction* — realization, in planning — and
nothing at the consuming edge needs the tags.

A **restriction** carried alongside a consumed sum rides the **witness**, not the candidates:
`[y for y in x if 𝑝]` over a conditional collection filters whichever arm the witness took, so
the result is `Σ 𝐷 ∈ {𝐷₀, 𝐷₁}. {𝐷 | 𝑝} ⤇ 𝑊`. That is what the consuming rule above already
gives — the consumer is typed under a name for the witness, and a filter maps `𝑤 ⤇ 𝑉` to
`{𝑤 | 𝑝} ⤇ 𝑉` — so no separate step is needed to put it there.

What it must *not* be is a refined **sum**, `{Σ 𝐷 ∈ 𝐾. 𝐷 | 𝑝}` standing where a domain
belongs: a sum is not a domain. A refined *witness* is a different thing and is one, since
naming the witness is exactly what supplies a domain to refine.

Pushing it onto the candidates instead — `Σ 𝐷 ∈ {{𝐷₀ | 𝑝}, {𝐷₁ | 𝑝}}. 𝐷` — is sound as a type
and destroys a distinction the consumer needs. An **arm's own** filter refines a candidate
too (`box([x for x in xs if 𝑞]) if c else …`), and that one was already compiled inside the
arm; landed in the same position the two are the same shape, and nothing downstream can tell
a restriction still owed an operator from one already discharged. Nor can they be separated
by comparing candidates afterwards, because a single candidate can carry both at once. On the
witness the distinction is structural: candidates carry what the arms brought, the witness
carries what the consumer imposed.

The distributive law still holds — instantiating the witness at a candidate pushes `𝑝` inward
— it is simply not the normal form.

### Consuming a sum: naming the witness

Consuming a sum is the one rule in this design with real scoping in it.

**The rule.** Consuming a sum means getting at its body, and the body mentions the witness.
The witness is not a concrete type, so the consumer is typed under a *name* for it, and its
result closed back over the same name:

```
Γ ⊢ 𝑒 : Σ 𝐷 ∈ 𝐾. 𝐵[𝐷]     Γ, 𝑤 :: 𝐾 ⊢ 𝑓 : 𝐵[𝑤] ⇒ 𝑊
─────────────────────────────────────────────────────
Γ ⊢ 𝑓(𝑒) : Σ 𝑤 ∈ 𝐾. 𝑊
```

Both behaviours a consumer can have fall out of this one rule, with no case analysis on the
consumer. A comprehension's `𝑊` mentions `𝑤`, so the sum survives and the result is a
collection over the same witness. `sum`'s `𝑊` is `Int`, so it does not, and the sum vanishes.

A name is the only thing that can stand in the consumer's domain. A concrete candidate
picks one arm and loses the others, the silent narrowing
[Data domains are invariant](#data-domains-are-invariant) exists to rule out. A type meaning
"one of `𝐾`" — a sum `Σ 𝐷 ∈ 𝐾. 𝐷` standing where a domain belongs — fabricates a type for
what is a variable, and once it is a type the solver asks subtyping questions about it:
`𝑈 <: Σ 𝐷 ∈ 𝐾. 𝐷` would build a sum, an edge this design does not have
([only a term builds a sum](#only-a-term-builds-a-sum)).

The vanishing is a side condition on this rule, not a law about types:

> **A sum's body mentions its witness.** The conclusion is `Σ 𝑤 ∈ 𝐾. 𝑊` when
> `𝑤 ∈ fv(𝑊)` and `𝑊` otherwise.

So the vanishing case forms no sum, rather than forming one that something later collapses.
A sum over a witness its body never mentions would record a choice nothing can observe, and
it is the one shape where two spellings denote one type: the ordinary consumption rule puts
it below its own body, no rule relates it in the other direction, and structural equality —
which decides type identity for a memo key and for the post-inference re-check — would
report the two as different. [`SigmaType::bound`] rejects it, so the shape is
unconstructible and neither an equivalence nor a collapse pass is needed. The substitution
that would otherwise build one **opens** the sum binding the witness it instantiates rather
than rebuilding it (`instantiating_a_sum_at_its_own_binder_opens_it`).

The condition is on occurrence, not on candidate count: `Σ 𝑤 ∈ {𝐷}. (𝑤 ⤇ 𝑉)` has one
candidate and is a sum, because its body mentions `𝑤`.

#### One leaf, and scope decides what it means

A witness reference is a single leaf, [`Type::WitnessRef`], carrying identity alone. Whether
an occurrence is bound or free is a question about *scope*, asked where the answer is
available:

- **compaction** threads the binders it has descended through, and sorts an occurrence into
  an atom (bound — nullary, standing for one candidate without saying which, matching only
  itself) or the witness slot (free — a consumed sum named it and nothing has bound it);
- the **scope-validity pass** (`check_scope_valid`) asks the same question over the finished
  tree, extending the scope with the binders each node's type introduces.

This is how Pi treats a term binder: `Var(𝑥)` is one leaf whether the lambda binding it is
inside the type or outside it, and `check_scope_valid` decides. A second leaf for the free
form would give every bound reference the opacity only a free one needs, and would leave
every rule keeping two spellings of one witness in agreement by hand.

**The range lives on the binder, not on the occurrence.** A reference names a binder, and
the binder is what ranges over something
([The witness range index](#the-witness-range-index)). So a free occurrence is not
self-describing, and the context answers instead.

**The reference is named rather than de Bruijn**, for the reason a Pi binder is a `Name`.
When a pass decomposes a Σ-typed term — λ-elimination scattering a collection into
`id`/`const`/`zip`/`compose` — the witness occurrences spread across the pieces, and which
binder they belong to has to survive that. Nesting position cannot express it, because
position is what decomposition destroys. With a name, `subst_witness_ref` matches by
identity and can descend everywhere safely.

The cost is the one Pi already pays: derived `PartialEq`/`Hash` stop being α-invariant, so
two sums built by different derivations compare unequal though they denote the same type.
Preserving the binder through the compact carrier removes it for anything that merely
round-trips, and [`Type::without_witness_binders`] — the witness counterpart of
`without_pi_names`, canonicalizing by de Bruijn depth rather than erasing ids — is how the
remaining denotational comparisons are made.

Identity matters for a reason not visible in any single-collection program: **two
consumptions can be live at once.** `[x + y for x in a for y in b]` over two conditional
collections names both witnesses, and the result's domain mentions both. One anonymous atom
would merge them into a single position and conflate two different witnesses.

#### The witness range index

A binder's **range** is not a property of any occurrence of it. Its home is the variable
that stands in the witness position; the index is how a reader that holds only a
[`Type::WitnessRef`] finds it.

Its law is **union**, inherited from the range it mirrors, which is what makes an index safe
here rather than a second authority: an entry only grows, no writer can narrow what another
recorded, and a reader cannot observe a narrower range than has been recorded. Two writers
exist and neither needs to know about the other — the rule that names a witness when a sum
is consumed, and a materialized Σ re-entering the solver, which knows its own kind and
publishes it before handing out bare references to its binder.

The index holds **domains**, the factored view, because that is the only view a consumer
contributes: what it needs to know is which domains it must be prepared for. A sum written
unfactored — `Σ 𝜎 ∈ {𝐷ᵢ ⤇ 𝑉ᵢ}. 𝜎`, what `box` builds — is read through its fibered view
(`data_candidate_fibers`) first, so both spellings reach the index having already answered
the same question. That collapse is why consumption needs only one rule for the two forms.

Entries are scoped to one inference run: [`InferArena`] clears the index as it opens, beside
the other per-run indices it resets. Nothing rests on that being timely — binder ids are
globally unique, so an entry that outlived its run is unreachable rather than wrong, and the
clear is a growth bound.

#### A name, not a variable — but transparent through its range

A witness reference is a leaf, not a [`Type::Infer`], so nothing can unify it away. That is
what stops a conditional collection from being narrowed to one arm by a demand: a name
cannot be satisfied except by being the witness.

It is not information-free. Its range constrains it, and a range naming exactly one domain
**determines** it ([`TypeKind::needs_witness`]), which is what lets an `Array(2, 𝑉)` demand
meet a `List(𝑉)` whose range has already narrowed to that one domain. A fully opaque name
would reject it.

The carrier says the same for the bound form: [`AtomKey::Witness`] is a bound nullary type,
standing for one candidate without saying which, so it matches only itself. Naming a witness
reuses that law rather than adding one.

#### The witness carries its range rather than the position carrying a constraint

Recording the range on the free witness rather than as a separate kinding constraint on the
position makes three otherwise-separate problems one fact:

- **Binding can happen wherever it is needed.** Three places read the kind and only one has
  the consumed sum in hand: the carrier's re-pairing of `𝑤 ⤇ 𝑉` into the sum, a
  constraint-time comparison that runs before materialization, and the materialization of a
  **lone** witness position. That last is a legitimate answer rather than an escape —
  `Σ 𝑤 ∈ 𝐾. 𝑤`, "whichever domain the witness picked". With the kind recorded separately
  it has nothing to bind over.
- **The kind check stops running on a name.** Coalesce checks a kinding constraint by asking
  whether the minimal kind containing the *resolved* type is contained in it. A position
  that resolved to a witness fails that immediately — `{𝑤}` is not among a kind's concrete
  domains — because the check is written for domains and a witness is a name for one.
  Carrying the kind removes the separate constraint, so there is nothing to check against
  the name.
- **`𝑈 <: 𝑤` becomes a legitimate edge.** A consumer handed a sum standing where a domain
  belongs meets a concrete demand as `𝑈 <: Σ …`, an edge into a sum, which this design does
  not have. A free witness is a **domain**, so both sides are domains and the question is
  membership in a kind rather than entry into a sum.

Membership holds only for a **determined** witness — a kind naming exactly one domain. A
kind naming several leaves the witness free to be any of them, and accepting a concrete
demand would pin it to one, the silent narrowing
[Data domains are invariant](#data-domains-are-invariant) rules out. So transparency through
the range means transparent when the range *determines* the witness, not whenever it admits
it. Pinned by `conditional_consumed_as_fun`.
#### Naming a position is not filling it

Both witness forms *name* the position they stand in rather than contributing content to it,
and every rule that reads a position has to know the difference: a listing whose candidates
are all names resolves to the side with content, `Σ ⋈ 𝑤` is the sum with nothing to
distribute over, and a name cannot pick a candidate out. This is the reading
[`KindOrder::Resolves`] takes of a bare inference variable, generalized.

Getting this wrong produces no type error at the point of the mistake. It produces a witness
sitting in an atom set beside a concrete domain, read later as two alternatives, and
reported as a collection conflicting with its own witness.

#### Binding the witness is deferred to materialization

The witness is named at a subtype edge and cannot be bound there, because the thing bound
over is the consumer's *result*, an unresolved variable at that moment. So a free witness
lives in the constraint graph:

```
open   at the (Σ, Fun) edge     — 𝑤 enters the graph
  …    𝑤 sits on bound lists, is compacted, merged, joined …
close  at materialization        — the carrier re-binds it
```

That is the lifetime the witness atom already has as `AtomKey::Witness` in compacted
positions; the rule adds a name to it. Making the close eager would require resolving the
consumer's result at the edge, an ordered solve. This is a constraint-graph solver — bounds
accumulate and resolve at coalesce — so deferral is inherent.

#### The origin discipline: a binder is inherited, never invented downstream

Deferring *when* the close happens is sound; deferring *where the binder comes from* is not,
and putting several names on one witness is what happens when a closing site invents one.

> A binder identity is **inherited** from the thing that already has it, or **discharged**
> inside the rule that minted it. It is never manufactured by a site that is deriving,
> closing, or rebuilding.

Pi obeys it two ways. A lambda's binder is the term's own parameter name
(`Type::pi(&param.name, …)`); a dependent application mints `Name::solver_arg()` and
*discharges* it to the argument inside the same rule, so it never has to be recognised
elsewhere. Materialization only ever **filters** — `kept_name` keeps the binder iff it is
free in the codomain, which is witness erasure for Pi — and never invents one.

A witness can take neither route: it has no term-level binder to inherit from, and
discharging it *is* picking a candidate, which the rule forbids. So its identity comes from
the one thing that has one, **the sum being consumed**. The name is a
[`Type::WitnessRef`] to that sum's own binder, and every binding site uses it:

```
open    𝑤 is the consumed sum's own witness      (constrain, check)
  …     𝑤 rides the graph, is compacted, merged …
close   at the consumer's result                  — binds 𝑤, never a new name
```

A violation produces a type that is individually well-formed, so the rule is enforced by
construction rather than by review: a `Witness` carries its binder, so deriving one carries
the identity, and `Witness::fresh` is the visible act of not carrying it.

#### Elimination takes the name the context offers

The origin discipline says which sum a witness's identity comes from. It leaves open which
*name* that sum carries, and two derivations of one consumption answer differently: a
refinement predicate holds its own copy of the source it filters, and that copy carries a
binder minted by its own derivation. The two names denote one witness, and an edge between
them is a mismatch the solver reports as two types that render identically.

> A sum consumed at a position that already names a witness **adopts that name**.

The consuming position is what has a name to offer — an argument's type, the preceding
morphism's codomain in a composition — so `Type::adopting_witnesses_of` α-converts the sum
onto it before the edge is drawn. Positional, because a consuming position need not be a
bare witness: two generators index a tuple, one witness per component, and each adopts its
own. A position that is not a witness reference offers nothing, so the rule is inert during
constraint emission, where the consuming position is a variable and the naming rule above
applies instead.

The same adoption runs at the predicate boundary (`planning::predicates`): a predicate is
closed over `__elem`, bound at the refinement's base, so a witness the predicate mentions
and the base does not is that copy's name for one the base already carries. With one witness
in the base there is one thing it can be; with several the pairing is not determined and the
rule declines rather than guessing.

#### The escape check

Because binding is deferred, "no witness is left free" is a property to **check**:

> A witness reference is well-formed only under a binder — one an enclosing sum introduced,
> or the one a consumed sum named. Nothing is left free at the end.

It is checked as **scope**, in `check_scope_valid`, alongside the identical property for
Pi's term binders: each node's type extends the scope with the binders it introduces, and a
reference free against that scope is a violation. Checking it per *materialized type*
instead cannot work, because coalesce runs bottom-up and at the point a type is built
nothing knows what binds it from outside. Such a check can only ask about the shape of the
type in hand, which forces an exception for a bare witness at an *index* position, whose
binder belongs to the enclosing collection. With a real scope that node is simply in scope.

#### Realization asserts rather than rewrites

Planning's realization of a conditional collection is the one place a term's type changes
after the type system is done, and the sum has to survive that in every enclosing mention.
Rewriting those mentions is the obvious approach and the wrong one: they run through
composes, products and projections, a projection names its component *twice*, and the
chain still does not terminate because the last stale mention is not a sum at all.

So realization asserts instead. [`TypedExprNode::Realize`] re-views the gated union at the
type the `Case` had, and nothing above it changes.

It is **not** a [`TypedExprNode::Cast`], because a cast is an upcast: its whole typing rule
is the subtype obligation `value_ty <: target`, discharged by the ordinary rules. What
realization asserts is an isomorphism the rules *cannot* see — the sum picks one branch, the
tagged union has rows from every leg, and only the gates reconcile them, which no typing
rule can check. Routing it through `Cast` would claim an obligation that does not hold, and
would turn a checked edge into a trusted one for every other cast in the language. What the
node carries, what it does not cover, and why it needs no target field are on
[`TypedExprNode::Realize`] itself.

### Data domains are invariant

The `Fun`/`Fun` domain edge is contravariant, which is right for a *compute*
function: the domain is a parameter, nothing in the language can ask a capability
which inputs it accepts, and shrinking the accepted set only under-promises. A
**data** function's domain is invariant instead — the subtyping half of the same
model [The domain join needs `box`](#the-domain-join-needs-box) states.

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
field is unobservable. A data function has consumers that **reflect** its domain
rather than index into it, and they make the difference observable twice over.

- The declared domain **is the loop bound the program runs**. Op-conversion's
  `Builtin::Iterate` arm builds its iteration source as
  `IterateExtent::new(extent_of(𝐷))` from the *static* domain of the iterate
  marker's predicate. So handing an 11-row collection to a slot declared
  `[0,5] ⤇ 𝑉` does not forget rows the way the record forgets `b`; it emits a
  program that reads six of them and reports the result as the collection's.
- The domain is **reproduced in consumer results**. A comprehension has the shape
  `𝐷 ⤇ 𝐴 ⇒ 𝐷 ⤇ 𝐵`, so `𝐷` occurs covariantly — in an output — as well as
  contravariantly at application, and a variable occurring in both positions is
  invariant. That is the ordinary variance calculus, not a Cambra-specific rule, and
  it is the whole content of the `Data`/`Compute` split: a compute domain occurs
  contravariantly only, because nothing enumerates it.

There is a coherent language in which the wider collection *should* stand in: one
where a declared domain is a **view**, and narrowing it means "give me this much of
it". Cambra is not that language — and the reason is *not* that a data domain is
currently unwritable. It will not stay unwritable:
[`Array(𝑛, 𝑇)`](../../../docs/chl-spec.md#63-direction-collection-types-decided),
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
variable is a join like any other, and it has the same answer as anywhere else: none,
unless the program wrote a `box`. A domain position is not privileged — it does not get
an implicit sum that a `Case` result would not get. So `[0,1]` and `[0,2]` meeting at a
domain variable is a `JoinTypeError`, and the same program can be diagnosed from the edge
or from coalesce depending on whether a consumer forces the question early (see
[The domain join needs `box`](#the-domain-join-needs-box)).

The rule fires wherever the edge is drawn, the kind edge with it, including the
post-inference re-check in `check.rs`.

**The same rule settles the Σ level.** Because a Σ pairing is discharged by ordinary
body subtyping, whether `Σ 𝐷 ∈ {{𝐷₀ | 𝑝}, 𝐷₁}. 𝐷 ⤇ 𝑉` relates to `Σ 𝐷 ∈ {𝐷₀, 𝐷₁}. 𝐷 ⤇ 𝑉` is this arm
applied to `{𝐷 | 𝑝} ⤇ 𝑉 <: 𝐷 ⤇ 𝑉`, not a separate decision about candidates. So
invariance at the arm is invariance at both levels at once, and candidates relate by
membership rather than by subsumption.

**A second, independent reason the drop edge must stay out.** One argument for
admitting it does not survive contact with the consumer side.
[`extent_of`](../../interpreter/operator_conversion.rs) **strips every refinement** —
a domain refinement is realized by a `Filter` operator in the term graph, never as a
restricted extent — so dropping one is invisible to *iteration*, and that is the whole
case for calling it a value coarsening rather than a row change. It is not invisible
to a consumer that **discharges membership**: a filtered list keeps the source's index
numbering, so `{[0, 2] | 𝑝} ⤇ Int` coarsened to `[0, 2] ⤇ Int` licenses proving
`1 ∈ [0, 2]` and typing `xs[1] : Int` while the `Filter` may have removed index 1.
That makes the rule and the lookup design one choice, not two: a domain's *predicate*
must never be a proof source, membership riding the key against the domain's identity.

### Deliberately incomplete here

Everything below is a gap between the model above and what is built. Each item states what
is actually wrong rather than a consequence of one root cause; late materialization of the
Σ is correct, not the shared cause it looks like ([Where the conditional-collection Σ comes
from](#where-the-conditional-collection-σ-comes-from)).

> **An entry names a cause only with a reached-code demonstration** — an instrumented run
> showing the site executing on the failing program, and the outcome changing when the site
> is altered. Three traps make a probe report a site as unreached when it is not: `cargo
> test` captures stderr, so a probe needs `--nocapture`; a probe program that fails at
> *lowering* never reaches inference, so it says nothing about the solver; and a passing
> program is a reference point only if it exercises the same path — lowering distributes a
> comprehension over an inline conditional, so no Σ is consumed there at all.

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

- **A comprehension over two conditional collections compiles when the conditionals are
  written *inline*, and not when they are `let`-bound.** Inline is pinned by
  `two_conditional_sources_compile`, across all four `(c, d)` assignments; the witnesses stay
  apart either way (`two_conditional_sources_keep_their_witnesses_apart`).

  The `let`-bound blocker, measured: op-conversion reports `zip requires an input operator`.
  Realization builds the union around the outermost node binding the witness and copies the
  intervening chain into each leg, and a binding is what puts the product iterate outside the
  copied region, so the legs reach `zip` with no source at their head.

  This entry has carried five superseded causes, each derived from the model rather than from
  a run. Per the discipline above, re-measure before replacing the paragraph above with a new
  one. In particular the `Copair`/`DisjointJoin` split is **not** what it is waiting on: both
  nodes exist, realization emits a `Copair` where the site mentions a witness and a
  `DisjointJoin` where it does not, and the blocker survives that.

- **There is no runtime witness yet, so a described sum cannot be consumed.**
  A sum is a pair, and consuming one projects its witness and dispatches; nothing today
  can read a witness off a value. That is a gap to close, not a property of the design —
  the runtime witness is the load-bearing planned item
  (`src/ccl/design/collections.md`, "Realizing a conditional collection"). For an
  **enumerated** sum this does not bite — the
  gate fan-out compiles the conditional and the realized union's extent is the selected
  domain — which is exactly why the gap has stayed invisible: the conditional-collection
  path is the one case that does not need the general mechanism. It bites for a
  **described** witness: iterating a `Collection(𝑇)` parameter has to find the actual
  runtime domain, and [`extent_of`] maps a *type* to an `Extent`. The shape to follow is
  `Type::DataSource` → `Extent::DataSourceDomain`, which resolves an opaque domain to a
  runtime handle; the witness wants the same treatment. This is the general machinery
  a [first-class `Collection` value](collections.md#realizing-a-conditional-collection)
  needs, and the
  conditional-collection fan-out is its special case rather than a step toward it.

  Consuming a **heterogeneous** sum (`Σ 𝑇 ∈ {Int, String}. 𝑇`) additionally needs the
  consumer valid at every candidate, which for a genuine dispatch is a trait bound. The
  runtime is *not* the obstacle there — `UnionOperator` already produces a
  `Scalar(Union(…))` codomain when its inputs disagree — so what is missing is the
  typing, not the representation. This subsumes the older heterogeneous-scalar-union
  entry, which recorded the opposite diagnosis.

- **A Σ over unresolved candidates cannot be related at all.** The pairing search needs
  ground candidates — a disjunction cannot be recorded as a constraint the way membership
  in a description can — so an unresolved candidate leaves only the `𝑒 = 𝑑` instance,
  which a variable cannot satisfy. That, and not a variance question, is what keeps
  formation late: forming a Σ before coalesce would produce exactly the Σs the rule
  cannot relate.

  Forming a Σ at constraint time makes that constraint *live*, and what it turned out to
  require is that a sum's **candidates are an invariant position**. A candidate is a domain,
  and a domain's content arrives as an **upper** bound — a comprehension's iteration key must
  lie in its source's domain — so a candidate variable typically has no lower bounds at all.
  `extrude`'s polar proxy inherits one side only, and extruding candidates at `!pol` handed a
  sum in a negative position a *positive* proxy, which inherits lower bounds: nothing. The
  candidate then materialized unresolved, `Σ 𝐷 ∈ {?93, [0, 2]}. 𝐷 ⤇ Int`, which is what the
  ground-domain assertion catches. Since Σ-width matches candidates *by value*, neither
  direction is the unused one, so candidates now cross a level boundary through the two-way
  proxies `extrude_invariant` builds — the same treatment, for the same reason, as a `History`
  payload.

  That is the whole of it: no groundness precondition is imposed on the join, and an arm whose
  domain is *inferred rather than written* — any comprehension arm, filtered or not — joins
  like a literal one. Refinements were never the discriminator; they only correlate, because a
  filtered comprehension's domain is a refinement over the same kind of variable.

  Two earlier explanations of this are wrong and are recorded here only so they are not
  reached for again. That candidates must be ground *in principle* — they need not; the copy
  was faithful, the proxy was not. And that the hazard is a candidate "recording a bound at
  the wrong polarity" during compaction — compaction walks candidates at `!pol`, which for the
  common positive sum is negative and therefore correct for a domain.

  An arm that is a **UDF call** is *not* closed by the join, and does not need to be. The join
  declines a bare variable — reading a variable's denotation would mean joining its own lower
  bounds transitively, and skipping it would risk dropping a candidate it later resolves to.
  It works because the **solver** propagates it: the arm's collection reaches the join variable
  transitively as an ordinary lower bound, which is what bound closure is for. Taking the
  transitive read inside the join instead requires variable resolution, then re-pairing the
  witness into a sum, then doing that through a variable — three pieces of compaction
  re-implemented at constraint time — and regresses the parameter route. Long-range and nested
  information is the solver's job.

  A use of a **lambda parameter** carries the
  parameter's own variable, and a binder's type is fixed by the contravariant domain of the
  arrow it binds — the reason `refresh_lambda_param_slot` derives `param.ty` from the coalesced
  domain rather than resolving the slot. Reading that variable *bare*, as the use's own node
  type, loses the same context, and for a data-function domain the loss is not mere
  imprecision: the candidate domains of a conditional collection are alternatives only when
  read **as a domain**, and collide as an untagged sum when read bare. That collision at
  `__iter_record` was the whole of the original failure.

  Two constraints shape the fix, and both are load-bearing. The standalone read must still
  *happen*, because a parent's structural recovery of a contravariant domain
  (`specialize_projection_domain`, `specialize_lambda_domain`) reads it — a record-typed
  parameter's uses are how a projection's domain is recovered at all. And the parameter slot
  must only fill uses the read *left* unresolved, because a use whose read succeeded is at
  least as precise as the slot and often more so: a monomorphized parameter's use carries the
  call's literal singleton where the slot, being the coalesced domain, has widened it. So the
  rule is narrow by construction — the slot answers exactly where the bare read has no answer.
  Pinned by `a_udf_call_arm_joins_through_the_bound_graph` and
  `a_lambda_param_use_falls_back_to_the_param_slot`.

  The candidate list is **not** a redundant second alternatives mechanism layered on the
  position's atom set. A flat atom set
  cannot express *which* candidate a refinement belongs to, and that association is semantic:
  `[q for q in [1,2,3] if 𝑝] if 𝑐 else [1,2]` must be `Σ 𝐷 ∈ {{[0,2] | 𝑝}, [0,1]}. 𝐷 ⤇ 𝑉`,
  not `Σ 𝐷 ∈ {{[0,2] | 𝑝}, {[0,1] | 𝑝}}. 𝐷 ⤇ 𝑉` — the filter restricts the arm that was
  taken, not both.
  Distributing a position's refinement over its atoms produces exactly that wrong type, which
  is why `denoted_domains` refuses a position carrying refinements. Per-candidate association
  is what `CompactWitnessKind::Enumerated` carries.

  Two sites make that survivable today: `compact_go` and `extrude` walk candidates at
  `!pol`, and the ground-candidate `debug_assert!` in `coalesce_compact_go` forbids a free
  variable in a candidate — which is how a one-sided bounds graph gets an invariant
  position for free. They come due with **formation**, not with the search: once a Σ is
  formed at the join its candidates are whatever the arms inferred, and the discharge has
  to move to where they are ground.

- **The kind level has no free-standing join or meet, and does not need one.** Both are
  readings of `order_witness_kinds` except for the listed-vs-listed union, which is written where it
  is used — in `join_witness_kinds`' `Enumerated` arm in compaction, the one place a
  variable's sum-shaped bounds are joined. A free-standing kind-level `join` has a cross-kind
  branch no call site reaches, so the two callers share exactly the one arm they need. Detail in
  [Witness kinds form a lattice](#witness-kinds-form-a-lattice).

- **The fan-out's discriminant order has never met a multi-candidate sum.** The
  value-`Case` fan-out indexes legs by discriminant order, and it is built only where
  every arm shares one domain — a single candidate, nothing for an order to disagree
  about. Candidate order is *not* an input to subtyping (the rule quantifies over a set),
  so the two do not meet today; they would the moment the fan-out is reconciled against a
  sum with two or more candidates. A Σ formed at the join fixes the order by construction.

- **Witness-dependent kinds are unbuilt.** No kind carries a reference to an *enclosing*
  witness — the `Σ (𝑤₁: 𝐾₁). Σ (𝑤₂: 𝐾₂[𝑤₁]). 𝐵` shape. Nothing forecloses it: it is kind
  subtyping under a substitution, an extension of the kind level rather than of the Σ
  rules. Listed because it is the honest edge of "general dependent sums", not because
  anything needs it.

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
