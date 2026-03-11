# Lowering CCL to a Dataflow Graph

See also:
- [semantics.md](semantics.md) — formal definitions of tilings (Section 1), guards (Section 2), and operators (Section 3)
- [example.md](example.md) — worked example that this document uses as a running illustration

---

## Overview

Lowering a CCL program to an executable dataflow graph proceeds in two steps, across two
distinct layers of abstraction.

**Layer 1 — CCL**: CCL programs are lambda calculus terms typed over tiling types. Each
primitive combinator (`map`, `converse`, etc.) is defined here by its **CCL semantics**: the
mathematical function it computes, expressed as an ordinary higher-order function. This layer
defines *what the program computes*.

**Layer 2 — Tiling operators**: Each primitive combinator has a corresponding **tiling
operator**: a monotone function over tiling values. This
layer defines *how the program is executed*.

The two lowering steps are:

1. **Point-free compilation**: Rewrite the CCL term into a point-free composition of the primitive
   combinators and structural morphisms (products, projections, currying). Variables and lambda
   bindings are eliminated; their structure is encoded in graph topology. The output is still a
   CCL expression, but one that uses only the named primitives — no lambdas over tiling domains.


2. **Transport to Tilings**: Instantiate each primitive combinator in the point-free expression
   as the corresponding tiling operator. The result is a dataflow graph of tiling operators that
   can be scheduled, parallelized, and distributed.

---

## Primitive Combinators

The five combinators below are the shared vocabulary of both layers. Each has a CCL definition
that specifies what it computes, and a tiling operator that implements it for streaming execution.

### `map`

**CCL semantics**: Given a scalar function `h : V ⇒ W`, `map(h)` applies it pointwise:

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

**CCL semantics**: `restrict` filters a function tiling to the subdomain where a predicate
holds:

```
restrict(f, pred)  =  λ i | pred(i) = true → f(i)
```

**Tiling operator**:

```
restrict : (I ⇀ V) × (I ⇀ Bool) → (I ⇀ V)
```

An entry `i ↦ v` appears in the output only when the predicate for `i` has reached a terminal
value of `true`; entries where the predicate is terminal `false` are permanently excluded. Until
the predicate for `i` is terminal, the entry is neither included nor excluded. `restrict` is a
**homomorphism** and streams.

This is the mechanism for sparse functions with dynamically determined domains: a CCL lambda
with a refinement predicate (`λ i | pred(i) → body(i)`) lowers to
`restrict(body, predicate)`.

In relational terms: `WHERE pred(i)`.

### `filter`

`filter` is a derived operator that restricts by a predicate on the codomain rather than the domain.
It is more ergonomic when the restriction condition is naturally expressed in terms of
the codomain:

```
filter(f, pred)  =  restrict(f, f ≫ map(pred))
```

`f ≫ map(pred)` applies `pred : V → Bool` pointwise to the values of `f`, producing the
predicate tiling `I ⇀ Bool` that `restrict` expects. The result keeps only entries `i ↦ v`
where `pred(v) = true`.

In relational terms: `WHERE pred(val)`.

---

## Lowering Step 1: Point-free compilation

(TODO: should we call this "liberation"? lol)

A CCL program is a lambda calculus term typed over tiling types. Point-free compilation rewrites it
into a **point-free composition** of the primitive combinators and structural morphisms, using
the Cartesian Closed Category (CCC) structure of the tiling type system.

### The CCC structure

The tiling types form a CCC whose:

- **Objects** are tiling types: scalar tilings `Scalar(T)`, function tilings `I ⇀ V`,
  aggregate tilings (`Count×Sum`, `Count×Max`, etc.), and products `A × B`.
- **Morphisms** are CCL functions between tiling types.

The CCC structure provides:

- **Products** `A × B` with projections `fst`, `snd`, and fanout `⟨f, g⟩` (sends the same
  input to both `f` and `g`).
- **Terminal object** `1` (discards context).
- **Exponentials**: the function tiling `A ⇀ B` acts as the hom-object, with
  `eval : (A ⇀ B) × A → B` and `curry : (C × A → B) → (C → A ⇀ B)`.

### How variables disappear

Each kind of variable binding is handled structurally:

**Lambda parameters** (`λ k → body`): the body is compiled in an extended context that
includes `k`. Within the body, `k` is accessed as the projection `π_k`. The whole expression
is then `curry_k(⟦body⟧)`, which produces a morphism whose input type includes `k`. At the
graph level, `k` is simply an input edge to the body's subgraph.

**Let bindings used once** (`let x = e in body`): the binding normalizes away by the rule
`extend_x(⟦e⟧) ≫ π_x = ⟦e⟧`. The intermediate name `x` inlines directly to its use site
and leaves no trace in the graph.

**Let bindings used multiple times**: become named nodes in the graph with explicit fanout —
multiple outgoing edges from the same node. No duplication of computation occurs; the graph
represents sharing directly.

**Free variables** (`key`, `val`, etc. from an enclosing scope): become projections `π_key`,
`π_val` from the context record. At the graph level, they are input edges.

After normalization, no variables remain. The graph topology encodes what the variable names
encoded: which computations feed which.

### The two-level boundary

Not all of a CCL program lowers to the tiling graph. Expressions whose result is a scalar
tiling, or a function over a non-iterable domain, are **leaf nodes**: opaque subprograms
compiled by a traditional backend (e.g. LLVM). They appear in the graph as black-box morphisms
with typed input and output edges.

Point-free compilation descends into a term until it reaches a leaf node type, at which point it
stops and treats the subexpression as an atomic morphism. The scalar functions passed to `map`
— such as `(/ )` or `(< 100)` — are examples: they are leaf nodes, not recursively expanded.

### What determines graph quality

The compilation produces a clean graph only if the source program uses the primitive
combinators directly. A raw lambda over a function domain:

```
λ k → sum(λ i | key(i) == k → val(i))
```

compiles to a tangle of `eval`, `restrict`, and `eq` nodes — technically correct, but with no
recognizable structure. The same computation written with explicit primitives:

```
converse(key) ≫ map(val ≫ aggregate(v-sum))
```

compiles to two named nodes connected by a typed edge.

This is a design constraint on the CCL surface language: by the time a CCL program is given to the
Point-free compiler, **tiling-level computations should be expressed using the tiling primitives**, not 
as raw lambdas over function domains. Point-free compilation is a neutral mechanism; the clarity of the 
output graph depends on the vocabulary the programmer uses.

---

## Lowering Step 2: Transport to Tilings

After point-free compilation, the program is a composition of primitive
combinators and structural morphisms, typed by tiling types. Transport instantiates this
expression as an executable dataflow graph.

Each primitive combinator is replaced by its tiling operator (defined in
[Primitive Combinators](#primitive-combinators) above). Correctness follows from the fact that
the tiling operator computes the same function as the CCL semantics of the combinator;
streaming follows from the homomorphism property of each operator.

The structural morphisms of the CCC reduce to graph wiring:

- **Fanout** `⟨f, g⟩` becomes a node with multiple output edges.
- **Projections** `fst`, `snd` become edge selections from a product-typed wire.
- **`curry` and `eval`** correspond to the function tiling type itself — function tilings are
  first-class edges in the graph.

The result is a **dataflow graph** whose:

- **Nodes** are tiling operators (transported primitives or opaque scalar subprograms).
- **Edges** are data flows between nodes, typed by tiling types.
- **Topology** encodes all variable and binding structure from the original CCL term.

This graph can be scheduled, parallelized, and distributed. Streaming, early termination, and
compaction emerge from the tiling properties of individual operators
(see [semantics.md](semantics.md), Section 3) without requiring special treatment in the graph
structure itself.

---

## Example

The program from [example.md](example.md), rewritten using the primitive combinators:

```
stats      = converse(key) ≫ map(val ≫ aggregate(v-sum)) ≫ memo
small_avgs = restrict(zip(stats, cnt) ≫ map(/),  stats ≫ map(< 100))
stdout     = small_avgs
```

**After Step 1 (Point-free compilation)**, the original CCL variables `k`, `i`, and `group` have
been eliminated. The fanout of `stats` — used in both the predicate and the body of
`small_avgs` — is made explicit as a shared binding.

**After Step 2 (transport)**, each combinator becomes a tiling operator. The resulting dataflow
graph:

```
              [key: I⇒Key]
                    │
                    ▼
              [converse(key)]
                    │
                    ▼
      [map(val ≫ aggregate(v-sum))]
                    │
                    ▼
                 [memo]       stats : Key⇀Sum
                    │
                 (fanout)
          ┌─────────┴──────────────────┐
          │                            │
          ▼                            ▼
   [map(< 100)]                   [zip(·, ·)] ←── [cnt: Key⇒Nat]
    Key⇀Bool                       Key⇀Sum×Nat
          │                            │
          │                            ▼
          │                        [map(_/_)]
          │                         Key⇀V
          │                            │
          └──→ [restrict(·, ·)]  ←─────┘
                      │
               small_avgs : Key⇀V
```

Every node is a named tiling operator. The original CCL variables do not appear — their
structure is encoded in the graph topology. The two uses of `stats` are represented by the
fanout edge from the `memo` node.
