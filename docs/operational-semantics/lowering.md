# Lowering CCL to a Dataflow Graph

See also:
- [semantics.md](semantics.md) — formal definitions of tilings (Section 1), guards (Section 2), and operators (Section 3)
- [example.md](example.md) — worked example that this document uses as a running illustration

---

## Overview

Lowering a CCL program to an executable dataflow graph proceeds in two steps, across two
distinct layers of abstraction.

**Layer 1 — Arbitrary CCL**: CCL programs are typed lambda calculus terms, including lambdas, refinements,
and records. CCL also provides a number of dataflow-oriented combinators (`map`, `converse`, etc.)
as primitives, but programs lowered from CHL will general not be expressed in terms of them.
This layer defines the semantics of the CCL program: the mathematical function it computes, 
expressed as an ordinary higher-order function. This layer defines *what the program computes*.

**Layer 2 — Dataflow CCL**: Arbitrary CCL is rewritten into a representation that corresponds to 
dataflow. Sources in this dataflow graph are primitive function terms (e.g. `stdin`). Sinks are the
fields of the top level record, which can be given special names to route to particular outputs 
(e.g. `stdout` or `kafka`). The transformations are compositions of dataflow combinators consuming
sources to produce the data that feeds a sink. The resulting program is still CCL:
it works in terms of the same syntax, the same types, and the same semantics. It is functionally
equivalent to the original program, but is composed exclusively of dataflow combinators, function
application, function composition, and `let` expressions. There are no lambda terms.

**Layer 3 — Tiling operators**: CCL programs execute in terms of **tiling operators**: monotonic
functions between tilings. This layer defines *how the program is executed*.

Dataflow CCL can be readily converted to tiling operators, as there
is a rough correspondence between the AST elements of CCL and tiling operators:
1. A term corresponds to the upstream closure of an operator graph node.
1. Function application corresponds to an edge in the operator graph.
1. The type of a term corresponds to the tiling of an operator.
1. Dataflow combinators are implemented as specific operators.
1. `let` expressions are represented by the `fanout` operator.

The conversion process applies these correspondences to produce a graph of tiling operators that 
executes the CCL program, and can be automatically scheduled, parallelized, and distributed.


## scratch
we want the overall function to have type Γ ⇒ Ω: input context to output context.
it makes sense to use π functions to get things out of Γ
the result will zip things together into the output record.
  e.g. Γ = { stdin: IOStream }, Ω = { stderr: IOStream, stdout: IOStream }, process: IOStream ⇒ {out: IOStream, err: IOStream}
    main = let res = πstdin ≫ process 
            in zip(stdout = res.out, stderr = res.err)

let's think through cases:
- outermost lambda: `main = λ x → <expr>` it's trivial to see the dataflow from `x` into other operators.
- applied, static lambda: `my_x ▸ λ x → ... ` just replace with `let x = my_x in ...`
- iterated, static lambda: `sum(λ i → ...)`
  - no free vars: 

What is an iteration node in the graph? In point-free representation, there isn't one. A source is
just a function given as a primitive.
What's a good way to think of the program graph? 
- let's use string diagrams: 
- boxes are functions, lines are types
- lines can split or be deleted, represented as black dots along lines
- terms are circles with their definition inside, with a line coming out of the right
- function application is represented by wiring a circle to the left side of a box



---

## Primitive Combinators

The combinators below are the shared vocabulary of both layers. Each has a CCL definition
that specifies what it computes, and a tiling operator that implements it for streaming execution.

### `apply`
**CCL semantics**: Given a pair `{ t: T, f: T ⇒ U }`, returns the result of applying `f` to `t`.

**Tiling operator**: Applies the given function to the argument. Can be implemented in terms of
`map` by lifting the argument to the unit function tiling `t↑ = λ () → t`.

### `curry`
**CCL semantics**: Given a function `f : {f0 : F0, ...} ⇒ T`, curries a subset of its fields,
becoming `fc : {f0 : F0, ...} ⇒ {fn : Fn, ...} ⇒ T`.

**Tiling operator**: Takes a function tile and returns a curried function tile with the 
corresponding fields curried.

### `uncurry`
**CCL Semantics**: Given a function `fc : {f0 : F0, ...} ⇒ {fn : Fn, ...} ⇒ T`, uncurries it into
a function of a single record: `f : {f0 : F0, ..., fn: Fn, ...} ⇒ T`.

**Tiling operator**: Takes a curried function tile and returns a uncurried function tile.

### `const`
**CCL semantics**: Given a constant, lifts it into a constant function over some domain.

**Tiling operator**: Takes a scalar tile and converts it to a function tile, defined on and
constant across its whole domain.

### `map`

**CCL semantics**: Function composition.

```
map(h)(f) = f ≫ h = λ i → i ▸ f ▸ h
```

**Tiling operator**:

```
map(h) : (I ⇀ V) ⇒ (I ⇀ W)
```

Each new mapping `i ↦ v` in the input immediately produces `i ↦ h(v)` in the output.
If `V` and `W` use the scalar tiling, `map` is a **homomorphism** and streams.
Otherwise, it depends on whether `h` is a homomorphism between the tilings for `V` and `W`.

In relational terms: `SELECT h(val)`.

TODO: Semantically, this works fine if `h` is a function tiling, not a scalar function. But
if `h` is a function tiling, what we're really doing is executing a join. In practice, we may 
want to have separate operators for each case. How do we identify each case?

### `converse`

**CCL semantics**: Given a key function `key : I ⇒ K`, `converse(key)` groups a function
tiling by key:

```
converse(key) =  λ k → (λ i | key(i) = k → i)
```

**Tiling operator**:

```
converse(key) : K × I ⇀ I
```

Each new mapping `(k, i) ↦ i` is immediately routed to the fiber at `key(i)`. `converse` is a
**homomorphism** and streams.

In relational terms: `GROUP BY key`.

### `aggregate`

**CCL semantics**: Given a combining operation whose monoid is `op = (Agg, ⊕, ε)`, `aggregate(op)`
reduces a function tiling:

```
aggregate(op)(f)  =  ⊕_{i ∈ dom(f)} f(i)
```

**Tiling operator**

```
aggregate(op) : (I ⇀ Agg) ⇒ Agg
```

Each new input mapping independently updates the running aggregate via `⊕`. `aggregate` can be a
**homomorphism to the aggregate tiling**, in which case it streams. The aggregate tiling type (`Count×Sum`,
`Count×Max`, etc.) is determined by the combining operation.

NOTE: Even if an aggregation streams, the projection that _extracts_ the aggregate may not be a 
homomorphism, and therefore not stream. For example, `sum(nums) > 100` streams into the `Count×Sum`
tiling, but extracting the sum is not homomorphic, and cannot be streamed (because extraction maps it to the scalar tiling, which is terminal as soon as it has a value).

`aggregate` is often used after `converse` to produce a group-reduce:

```
converse(key) ≫ map(aggregate(op)) : (I ⇀ V) → (K ⇀ Agg)
```

`map` lifts `aggregate(op)` to act independently on each fiber, producing one aggregate per
key. This is the canonical pattern for keyed aggregation.

### `zip`

**CCL semantics**: `zip` pairs two functions with the same domain pointwise:

```
zip(f, g)  =  λ i → (f(i), g(i))
```

If field names are provided, the output record has named fields: 
```
zip(f = f, g = g) = λ i → (f = f(i), g = g(i))
```

Note: we use `⟨f, g⟩` as more compact notation for `zip` below.

**Tiling operator**:

```
zip : (I ⇀ V) × (I ⇀ W) → (I ⇀ V × W)
```

An output entry `i ↦ (v, w)` is produced as soon as both `i ↦ v` and `i ↦ w` are available.
The set of bound mappings is the intersection of bound mappings for both input tiles. 
`zip` is a **homomorphism** and streams. If the domains overlap partially, `filter` can be
used before `zip` to restrict the functions to the same domain.

In relational terms: an equijoin on the index domain.

### `restrict`

**CCL semantics**: `restrict` takes a predicate and returns the identity function on the
subdomain where the predicate holds:

```
restrict : (p: I ⇒ Bool) ⇒ {i: I | p(i)} ⇒ {i: I | p(i)} 
restrict(pred)  =  λ i | pred(i) == true → i
```

**Tiling operator**:

```
restrict : (I ⇀ Bool) ⇒ (I ⇀ I)
```

An index `i` passes through as soon as its predicate reaches terminal `true`; indices where the
predicate is terminal `false` are permanently excluded. Until the predicate for `i` is terminal,
`i` is neither passed nor excluded. `restrict` is a **homomorphism** and streams.

Because `restrict` returns the identity on the surviving domain, it composes naturally with any
downstream function: `restrict(pred) ≫ body = λ i | pred(i) → body(i)`. This is the mechanism
for sparse functions with dynamically determined domains: a CCL lambda with a refinement predicate
(`λ i | pred(i) → body(i)`) lowers to `restrict(pred) ≫ body`.

In relational terms: `WHERE pred(i)`.

### `filter`

`filter` is a derived operator that restricts by a predicate on the codomain rather than the domain.
It is more ergonomic when the restriction condition is naturally expressed in terms of
the codomain:

```
filter(f, pred)  =  restrict(f ≫ map(pred)) ≫ f
```

`f ≫ map(pred)` applies `pred : V → Bool` pointwise to the values of `f`, producing the
predicate tiling `I ⇀ Bool`. `restrict` gates the domain to `{i | pred(f(i))}`, and composing
with `f` maps those indices to their values. The result keeps only entries `i ↦ v` where
`pred(v) = true`.

In relational terms: `WHERE pred(val)`.

---

## Lowering Step 1: Lambda Elimination

A CCL program is a lambda calculus term typed over tiling types. Lambda elimination rewrites it
into a **point-free composition** of the primitive combinators and structural morphisms, using
the Cartesian Closed Category (CCC) structure of the tiling type system.

### Lambda-elimination
Following Elliot's [Compiling to Categories](http://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf),
we can eliminate lambdas from the program with the following rules, starting from the outermost term, and applied inductively:
- `λ x → x  ⟹  id`
- `λ x → <arg> ▸ <fn>  ⟹  ⟨λ x → <arg>, λ x → <fn>⟩ ≫ apply`
- `λ x → λ y → <body>  ⟹  curry(λ (x, y) → <body>)`
- `λ x → <expr>  ⟹ const(<expr>)` when `x ∉ fv(<expr>)`, where `fv` is "free variables of". 
  Works for both values and functions:
  `const(v)` lifts a value to a constant morphism; `const(f)` lifts a function, which the
  const-apply simplification rule then reduces when it appears in an `apply` position.
  Note: the identity `const(f) = curry(.1 ≫ f)` holds but need not be introduced eagerly.
- `λ x → (<f1>, <f2>)  ⟹ ⟨λx→<f1>, λx→<f2>⟩`
- `λ x → let <var> = <def> in <body>`
  `  ⟹ let <var> = (λx→ <def>) in λx→ <body>[<var> ↦ x ▸ <var>]`
- `λ x | <pred> → <body>  ⟹  (λx→ <pred>) ▸ restrict ≫ λx→ <body>`
- `λ x → <f> ≫ <g>  ⟹  ⟨λx→<f>, λx→<g>⟩ ≫ (≫)`
  where `(≫) : (A⇒B) × (B⇒C) ⇒ (A⇒C)` is composition as a first-class morphism.


These rules must be applied **outside-in** (outermost lambda first). Applying them inside-out
is incorrect: a nested lambda `λ y → body` that captures a free variable `x` of an outer `λ x`
would treat `x` as a constant via `const(x)`, when it must instead become a projection from
the combined environment `(x, y)` produced by eliminating the outer lambda first via the nested
lambda rule `λ x → λ y → body ⟹ curry(λ(x,y) → body)`.

### Simplifying expressions

However, the absence of lambdas is insufficient, because in general, these rules will introduce
a large number of redundant combinations of `curry`, `zip`, and `apply`. These redundancies are
eliminated by an additional set of simplifying rules:
- **Compose identity**: `id ≫ f  ⟹  f` and `f ≫ id  ⟹  f`. The category identity laws.
- **Product beta**: `⟨f, g⟩ ≫ .0  ⟹  f` and `⟨f, g⟩ ≫ .1  ⟹  g`. Projecting out of a
  zip selects the corresponding arm. This is the universal property of Cartesian Categories.
- **CCC universal property**: `⟨.1, .0 ≫ curry(f)⟩ ≫ apply  ⟹  f` where
  `f : A × B → C, ∀ A B C: Type`. The universal property of Closed Cartesian Categories.
- **Exponential beta**: `⟨g, curry(h)⟩ ≫ apply  ⟹  ⟨id, g⟩ ≫ h`. The CCC analog of
  beta reduction `(λx.M)N → M[N/x]`: applying a curried function to an argument substitutes
  the argument into the body. Implied by the CCC universal property.
- **Exponential eta**: `curry(⟨.1, .0 ≫ f⟩ ≫ apply)  ⟹  f`. The expression `⟨.1, .0 ≫ f⟩ ≫ apply`
  is the uncurried form of `f`: it pairs the inner argument with `f` of the outer argument,
  then applies. Currying recovers `f` exactly — this is the CCC identity
  `curry(uncurry(f)) = f`. Useful when `curry` is applied to a body whose only reference to
  the inner variable is via a single `apply`.
- **Curry-compose**: `curry(f ≫ g)  ⟹  curry(f) ≫ map(g)`. Follows from
  `map(g)(h) = h ≫ g`: the curried function `curry(f)(k) = λi → f(k,i)` post-composed with
  `g` is `λi → g(f(k,i))`, which is exactly `curry(f ≫ g)(k)`. This lets a suffix of the
  curried body be pulled out as a `map`.
- **Const-apply**: `⟨f, const(g)⟩ ≫ apply  ⟹  f ≫ g`. Direct consequence of
  `const(g) = curry(.1 ≫ g)`, exponential beta, and product beta. When a function slot holds
  a constant (e.g. a typeclass-resolved operation like `sum` or `cnt` that does not vary with
  the current key), the `apply` collapses to plain composition.
- **Product eta**: `⟨f ≫ .0, f ≫ ._1⟩  ⟹  f`. Collapses a zip that merely destructs and
  re-pairs the same source morphism. Analogous to the function-type eta rule
  `λ x → f x  ⟹  f`.

### Examples of Lambda elimination, step by step
Basic composition:
```
λ i → i ▸ f ▸ g
⟨λi→i▸f, λi→g⟩ ≫ apply                                         [λ x → arg ▸ fn]
⟨⟨λi→i, λi→f⟩ ≫ apply, const(g)⟩ ≫ apply                       [λ x → arg ▸ fn; λ x → const]
⟨⟨id, const(f)⟩ ≫ apply, const(g)⟩ ≫ apply                     [λ x → x = id; λ x → const]
⟨id ≫ f, const(g)⟩ ≫ apply                                      [const-apply]
⟨f, const(g)⟩ ≫ apply                                            [compose identity]
f ≫ g                                                             [const-apply]
```

**Curried Lambda**
This example has a curried lambda where the inner variable `j` is unused in the body.
We treat `a + b` as sugar for `(a, b) ▸ add` (tuple construction applied to `add`).
The inner sub-derivation for `λ(i,j) → i ▸ c1` (where `i = .0` of the pair) is shown indented.

```
λ i → λ j → i ▸ c1 + i ▸ c2
curry(λ(i,j) → i ▸ c1 + i ▸ c2)                                         [λ x → λ y → body]
curry(λ(i,j) → (i ▸ c1, i ▸ c2) ▸ add)                                  [expand +]
curry(⟨λ(i,j) → (i ▸ c1, i ▸ c2), λ(i,j) → add⟩ ≫ apply)              [λ x → arg ▸ fn]
curry(⟨⟨λ(i,j) → i ▸ c1, λ(i,j) → i ▸ c2⟩, const(add)⟩ ≫ apply)       [λ x → (f1,f2); λ x → const]

  -- sub-derivation: λ(i,j) → i ▸ c1, where i = .0
  ⟨λ(i,j) → i, λ(i,j) → c1⟩ ≫ apply                                     [λ x → arg ▸ fn]
  ⟨.0, const(c1)⟩ ≫ apply                                                [λ(i,j)→i = .0; λ x → const]
  .0 ≫ c1                                                                  [const-apply]

  -- similarly: λ(i,j) → i ▸ c2 = .0 ≫ c2

curry(⟨⟨.0 ≫ c1, .0 ≫ c2⟩, const(add)⟩ ≫ apply)
curry(⟨.0 ≫ c1, .0 ≫ c2⟩ ≫ add)                                        [const-apply]
```

The unused variable `j` drops out entirely: the result only involves `.0`. Contrast with the
next example, where both components of the record are used.

**Lambda of tuple**

```
λ r: {I, J} → r.0 ▸ c1 + r.1 ▸ c2
λ r → (r.0 ▸ c1, r.1 ▸ c2) ▸ add                                       [expand +]
⟨λr → (r.0 ▸ c1, r.1 ▸ c2), λr → add⟩ ≫ apply                        [λ x → arg ▸ fn]
⟨⟨λr → r.0 ▸ c1, λr → r.1 ▸ c2⟩, const(add)⟩ ≫ apply                 [λ x → (f1,f2); λ x → const]

  -- sub-derivation: λr → r.0 ▸ c1, where r.0 = .0(r)
  ⟨λr → r.0, λr → c1⟩ ≫ apply                                           [λ x → arg ▸ fn]
  ⟨.0, const(c1)⟩ ≫ apply                                                [.0 projection; λ x → const]
  .0 ≫ c1                                                                  [const-apply]

  -- similarly: λr → r.1 ▸ c2 = .1 ≫ c2

⟨⟨.0 ≫ c1, .1 ≫ c2⟩, const(add)⟩ ≫ apply
⟨.0 ≫ c1, .1 ≫ c2⟩ ≫ add                                               [const-apply]
```

Compare with Example 1: `λ i → λ j → i ▸ c1 + i ▸ c2` yields `curry(⟨.0 ≫ c1, .0 ≫ c2⟩ ≫ add) : I ⇒ J ⇒ T`,
a curried function that ignores its second argument. This example yields `⟨.0 ≫ c1, .1 ≫ c2⟩ ≫ add : I × J ⇒ T`,
an uncurried function consuming both components. The CCC eliminates the lambda in both cases;
the type difference reflects the original binding structure.

**Free variable capture** — `λ i → (i, c) ▸ f` (a closed-over constant `c` is paired with the input):

```
λ i → (i, c) ▸ f
⟨λi → (i, c), λi → f⟩ ≫ apply                                   [λ x → arg ▸ fn]
⟨⟨λi → i, λi → c⟩, const(f)⟩ ≫ apply                            [λ x → (f1,f2); λ x → const]
⟨⟨id, const(c)⟩, const(f)⟩ ≫ apply                              [λ x → x = id; λ x → const]
⟨id, const(c)⟩ ≫ f                                              [const-apply]
```

The result `⟨id, const(c)⟩ ≫ f` is a point-free function that pairs each input `i` with the
constant `c` and feeds the pair to `f`. In the dataflow graph, this corresponds to an edge from
the `const(c)` node wired alongside the identity edge into `f`.

**Let binding / fanout** — `λ i → let x = i ▸ f in (x, x ▸ g)` (a value used twice):

Applying the let rule, with `<def> = i ▸ f` and `<body> = (x, x ▸ g)`. The substitution
replaces each use of the value `x` in the body with the application `i ▸ x`, since `x` is now
a function:

```
λ i → let x = i ▸ f in (x, x ▸ g)
let x = (λi → i ▸ f) in λi → (i ▸ x, i ▸ x ▸ g)               [let rule, x ↦ i ▸ x]
let x = f in λi → (i ▸ x, i ▸ x ▸ g)                           [λi→i▸f = f]
let x = f in ⟨x, x ≫ g⟩                                        [λi→i▸x = x; λi→i▸x▸g = x ≫ g; tuple]
```

The `let` binding makes explicit that `f` is computed once and shared by two downstream paths.
In the dataflow graph, the `let` becomes a `fanout` node: `f` feeds both an identity edge and `g`.

**Refinement lambda** — `λ i | pred(i) → i ▸ f` (a lambda with a guard):

Applying the refinement rule, then reducing the resulting trivial lambdas:

```
λ i | pred(i) → i ▸ f
(λi → pred(i)) ▸ restrict ≫ (λi → i ▸ f)                 [λ x | pred → body]
pred ▸ restrict ≫ f                                      [λi→i▸h=h]
```

`pred ▸ restrict ≫ f` applies `restrict` to the predicate function `pred`, producing the
filtered identity, then maps the body `f` over the surviving entries.


**Keyed Aggregation** — `λ k → sum(λ i | i▸key == k → i▸val)`

This is the canonical keyed group-reduce: for each key `k`, filter the stream to items whose
key matches and sum their values. Applying the application rule on the outer lambda, the
curried-lambda rule to pair `k` and `i`, then the refinement rule on the inner guard:

```
λ k → sum(λ i | i▸key == k → i▸val)
λ k → (λ i | i▸key == k → i▸val) ▸ aggregate(+)                             [sum = aggregate(+)]
⟨λk → (λ i | i▸key == k → i▸val), const(aggregate(+))⟩ ≫ apply             [λk→arg▸fn]
⟨curry(λ(k,i) | i▸key == k → i▸val), const(aggregate(+))⟩ ≫ apply          [λk→λi→body = curry(λ(k,i)→body)]

  -- inner sub-derivation: λ(k,i) | i▸key == k → i▸val  (i = .1, k = .0)
  (λ(k,i) → i▸key == k) ▸ restrict ≫ (λ(k,i) → i▸val)                       [refinement rule]

    -- λ(k,i) → i▸key == k = λ(k,i) → (i▸key, k) ▸ eq:
    ⟨⟨key, ._0⟩, const(eq)⟩ ≫ apply                                 [λx→arg▸fn; λx→(f1,f2); λx→const]
    ⟨key, ._0⟩ ≫ eq                                                   [const-apply]

    -- λ(k,i) → i▸val = .1 ≫ val
    (⟨key, ._0⟩ ≫ eq) ▸ restrict ≫ (.1 ≫ val)

⟨curry((⟨key, ._0⟩ ≫ eq) ▸ restrict ≫ .1 ≫ val), const(aggregate(+))⟩ ≫ apply          [sub-deriv]
curry((⟨key, ._0⟩ ≫ eq) ▸ restrict ≫ .1 ≫ val) ≫ aggregate(+)                        [const-apply]
curry((⟨key, ._0⟩ ≫ eq) ▸ restrict ≫ .1) ≫ map(val) ≫ aggregate(+)                   [curry-compose, g=val]
converse(key) ≫ map(val) ≫ aggregate(+)                                             [curry((⟨key,._0⟩≫eq)▸restrict≫.1) = converse(key)]
```

The result instantiates the canonical keyed group-reduce pattern from
[Primitive Combinators](#primitive-combinators): `converse(key)` groups items into per-key
fibers, `map(val)` value-projects each fiber, and `aggregate(+)` reduces each fiber to a running
sum. 

---

## Lowering Step 2: Transport to Tilings

After point-free compilation, the program is a composition of primitive
combinators and structural morphisms. Transport instantiates this categorical representation
in terms of the Tiling/Operator category.

Each primitive combinator is replaced by its tiling operator (defined in
[Primitive Combinators](#primitive-combinators) above). Correctness follows from the fact that
the tiling operator computes the same function as the CCL semantics of the combinator;
streaming follows from the homomorphism property of each operator.

The structural morphisms of the CCC reduce to graph wiring:

- **Fanout** `⟨f, g⟩` becomes a node with multiple output edges.
- **Projections** `.0`, `.1` become edge selections from a product-typed wire.
- **`curry` and `apply`** correspond to the function tiling type itself — function tilings are
  first-class edges in the graph.

The result is a **dataflow graph** whose:

- **Nodes** are tiling operators.
- **Edges** are data flows between nodes, each of a given tiling.
- **Topology** encodes all variable and binding structure from the original CCL term.

This graph can be scheduled, parallelized, and distributed. Streaming, early termination, and
compaction emerge from the tiling properties of individual operators
(see [semantics.md](semantics.md), Section 3) without requiring special treatment in the graph
structure itself.

---

## Example

The program from [example.md](example.md), with typeclass-resolved operations (`key`, `val`,
`cnt`, `sum`) treated as constants:

```
stdout =
  let stats      = memo (λ k : Key →
                     let group = λ i | i▸key == k → i▸val
                     in sum(group))
      small_avgs = λ k | k▸stats < 100 →
                     k▸stats / k▸cnt
  in small_avgs
```

Lambda elimination is applied **outside-in** to each lambda. The top-level `let` is a closed
binding (no outer lambda), so the two definitions are derived independently and assembled.

**Deriving `stats-fn`:**

`stats-fn = λk → sum(λi | i▸key == k → i▸val)` is exactly the keyed aggregation example
from above, with `sum = aggregate(+)`:

```
stats-fn = converse(key) ≫ map(val) ≫ sum
```

**Deriving `small_avgs`** (with `stats` bound by the outer `let`):

Apply the refinement rule to `λk` while `stats` is a free variable (its sharing is
already captured by the `let` binding — no need to eliminate it):

```
λk | k▸stats < 100 → k▸stats / k▸cnt
= (λk → k▸stats < 100) ▸ restrict ≫ (λk → k▸stats / k▸cnt)   [refinement]
```

With `stats` free, each `k`-lambda reduces directly:

```
  λk → k▸stats         = stats                    [λk→k▸f = f]
  λk → k▸stats < 100   = stats ≫ (< 100)          [compose with (< 100)]
  λk → k▸cnt           = cnt                      [λk→k▸f = f]
  λk → k▸stats / k▸cnt = ⟨stats, cnt⟩ ≫ (/)       [tuple, then divide]
```

Giving:

```
small_avgs = (stats ≫ (< 100)) ▸ restrict ≫ (⟨stats, cnt⟩ ≫ (/))
```

The two references to `stats` — in the predicate and in the value computation — are shared
through the outer `let` binding. No further lambda elimination is needed; `stats` remains a
named reference.

**Point-free program:**

```
stdout = let stats      = memo(converse(key) ≫ map(val) ≫ sum)
             small_avgs = (stats ≫ (< 100)) ▸ restrict ≫ (⟨stats, cnt⟩ ≫ (/))
         in small_avgs
```

`stats : Key ⇀ Sum` is the memoized key-to-aggregate
function. `small_avgs` directly references `stats` twice (in the predicate and the value
computation); the `let` binding ensures both references share the same upstream computation.

**After Step 1 (Point-free compilation)**, the original CCL variables `k`, `i`, and `group` have
been eliminated. `stats` is preserved as a `let`-bound name whose two uses — in the predicate
and the body of `small_avgs` — become a fanout in the dataflow graph.


**After Step 2 (transport)**, each combinator becomes a tiling operator. The resulting dataflow
graph:

```
              [key: I⇒Key]
                    │
                    ▼
              [converse(key)]
                    │
                    ▼
               [map(val)]
                    │
                    ▼
                 [sum]
                    │
                    ▼
                 [memo]
                    │
           let stats : Key⇀Sum
                    │
         ┌──────────┴──────────────┐
         │                         │
         ▼                         ▼
  [map(< 100)]             [zip(·, ·)] ←── [cnt: Key⇒Nat]
   Key⇀Bool                 Key⇀Sum×Nat
         │                         │
         ▼                         ▼
     [restrict]               [map(_/_)]
      Key⇀Key                   Key⇀V
         │                         │
         └──────── [>>] ───────────┘
                    │
             small_avgs : Key⇀V
```

Every node is a named tiling operator. The original CCL variables do not appear — their
structure is encoded in the graph topology. The `let` binding of `stats` is represented by
the fanout from the `memo` node: `stats` feeds both `map(< 100)` (predicate path) and
`zip` (value path). `restrict` acts as a domain gate: it emits only keys where the predicate
holds, gating which entries the downstream `zip ≫ map(/)` pipeline computes.
