# [WIP] Operational Semantics: Monotonic Progress through Progress Algebras

**This document is a Work in Progress. Its content is not authoritative and may not even be coherent.**

This document describes the operational semantics of CCL (Cambra Core Language). See also:
- [src/interpreter/design-operators.md](/src/interpreter/design-operators.md) — per-operator specifications
- [brainstorm/guards-and-separation-algebras.md](brainstorm/guards-and-separation-algebras.md) — historical brainstorm that originated
  many of the ideas here

---

## 1. The Model

At any point during execution, every term's runtime state is a **monotonically-growing element**
of a structured algebra. As more information is computed, the element grows larger in the
extension order, and dependent terms can themselves be further computed. A program terminates when
all terms have reached their final state.

The starting state for every term is `⊥` (bottom) — zero information. Computation adds knowledge;
nothing is ever retracted.

---

## 2. Progress Algebras

The algebraic structure used is a **separation algebra** (also called a cancellative partial
commutative monoid, or PCM). We call the separation algebra for a given type its **progress
algebra** to emphasize that it describes the operational accumulation of knowledge, not the type
itself.

### Formal Definition

A progress algebra is a set `E` equipped with:

1. A **partial binary operation** `⊕ : E × E ⇀ E`. This operation combines information; it is
   defined only for *compatible* pairs — pairs whose information does not contradict or overlap.
   `⊕` is commutative and associative (wherever it is defined).
2. An **identity element** `⊥ ∈ E`, representing zero information. `x ⊕ ⊥ = x` for all `x`.
3. **Cancellativity**: if `x ⊕ z = y ⊕ z` then `x = y`. This guarantees that once you select
   some portion of an element's information, the remaining portion is uniquely determined. It
   enables sound reasoning about how much computation is left.
4. An **extension order**: `x ≤ y` iff `∃h. x ⊕ h = y`. An element with more information is
   larger. Computation proceeds upward through this order, monotonically.

### Instances

**Scalar terms** (e.g., `Int`, `Bool`): The progress algebra is `{⊥} ∪ T`, where `T` is the
carrier set of the type. `x ⊕ y` is defined iff at least one of `x`, `y` is `⊥`; combining two
concrete values is incompatible (a scalar can take on only one value). A scalar is therefore
determined in a single step: from `⊥` to its final value.

**Function terms** (e.g., `T ⇒ U`): The progress algebra is the set of partial functions `T ⇀ U`.
`f ⊕ g` is defined iff the domains of `f` and `g` are disjoint; the result is their union. This
is the same structure used in separation logic for heap reasoning, and in effect algebras for
quantum measurement. Functions can be determined incrementally, with each increment covering a
disjoint portion of the domain.

---

## 3. Computing Values

Computing the value of a term can be done in multiple **increments**. Each increment is an element
of the progress algebra, and all increments must be mutually compatible. The term's final value is
defined as `⊕` of all increments.

For **scalars**: only one increment is possible (by the definition of the scalar progress algebra),
so the value is determined in a single step.

For **function terms**: computation can be spread across many increments, each over a disjoint
portion of the domain. This is what enables streaming, pipelining, and vectorized execution.

---

## 4. Guards

A **guard** is a predicate over an extent, describing a subset of the possible values for a term.
Guards appear in the producer/consumer protocol in two roles:

**Intent guard**: A consumer registers its interest in a region of the producer's extent.
"Please make this region total — compute the function for all inputs in this predicate."

**Obsolete guard**: A consumer retracts interest in a region it no longer needs. "I no longer
need totality on this region; you may reclaim resources."

Intent and obsolete guards are predicates on the *extent* (the type). They are consumer-side
concerns about which parts of the producer's output are needed, and are separate from the
producer-side progress model.

Guards are **freely joinable** — any two guards can be unioned, without restriction. This
distinguishes them from progress algebra elements, where `⊕` is partial. See Section 6 for why.

---

## 5. Yield Guards and Embedded Closure

### The Problem with Separate Yield Guards

The original protocol included a third guard role:

**Yield guard**: a producer's assertion that a region of its extent is final — no further
increments will cover that region.

For scalar terms, this was coherent: a yield guard narrows the set of possible output values by
ruling out a region.

For function terms, it was problematic. A `Domain(D)` yield guard says "all mappings for inputs
in D are final" — but this is a statement about *progress*, not a predicate on the function's
*value*. The guard-as-predicate framing breaks down, and yield guards become a leaky abstraction
where progress information lives outside the data structure it describes.

### The Direction: Embedded Closure

The resolution is to embed closure information *inside* the progress algebra element itself. A
richer element for a function term can be represented as a pair:

```
(partial_function: T ⇀ U, closed: RegionPredicate)
```

where `closed` is a monotonically-growing set of domain regions guaranteed to receive no further
mappings. The `⊕` for two such pairs combines the partial functions (requiring disjoint domains)
and takes the **join** of the `closed` sets (freely, since `closed` is a lattice).

Under this design:
- The element is **self-describing** about its own finality. A consumer calls `get()`, receives
  an element, and can determine both what has been computed and which regions will not grow further
  — without consulting any out-of-band signal.
- `Notification::Yield(Guard)` is deprecated and targeted for removal. A notification always
  triggers a `get()`, and the returned element encodes both data and closure.
- The `yield_guard` field in `GetResult` is a transitional encoding of this embedded closure
  information, and should be superseded by the `closed` component of the returned element once
  the type system for elements is fleshed out.

### Static vs. Dynamic Domains

For **static domains** (e.g., a list literal with a known index range), the `closed` set is the
full domain immediately, or can be omitted as implicitly always-full.

For **dynamic domains** (e.g., stdin, a live timeseries), `closed` grows as the data source
signals completion of each region, enabling incremental, streaming consumers.

The richer element representation handles both cases uniformly.

---

## 6. The Two-Layer Picture

There are two distinct algebraic structures at play:

**The separation algebra** (the *data* layer): Elements represent partial computations — what is
*known* about a term. The partial `⊕` enforces that only compatible (non-overlapping) contributions
are merged. Consistency is enforced here.

**The guard lattice** (the *progress description* layer): Elements are predicates over the extent —
region descriptions. These are **freely joinable** (any two guards can be unioned) because
describing a larger region creates no contradiction. This is how progress is *communicated*.

The connection between layers: a guard `G` is "realized" when the current separation algebra
element is defined on the region G. Guards describe *where* computation has reached; algebra
elements describe *what* has been computed there.

This is why guards can always be combined (they are in a lattice) while data contributions cannot
always be combined (they are in a separation algebra with partial `⊕`). The asymmetry is
fundamental, not accidental.

---

## 7. Protocol Rules

The producer/consumer protocol, stated in terms of progress algebra elements and guards:

```
// Operator creates the dataflow link
Operator::subscribe(intent_guard: Guard, consumer: Consumer, var_scope: VarScope) -> Producer

// Producer pushes notifications to consumer
Consumer::notify(Notification::NewData)
    // New increment available — consumer should call get()
Consumer::notify(Notification::Yield(guard))
    // [Deprecated] Region is closed, no new data — closure now embedded in element

// Consumer pulls data and manages lifecycle
Producer::get() -> GetResult { column_value, yield_guard }
    // Returns current element; yield_guard is transitional encoding of closure
Producer::release(obsolete_guard: Guard) -> Guard
    // Consumer retracts interest; producer may reclaim resources
```

**Invariants**:
- A producer's element grows monotonically: each `get()` returns an element `≥` all previously
  returned elements in the extension order.
- Each `Notification::Yield(guard)` covers a region no smaller than all previous yield guards
  (the yield guard is monotonically growing). This allows implementations to store a single
  yield guard rather than a history.
- The obsolete guard passed to `release()` must be a sub-region of the original intent guard.

---

## 8. Terminology Note

Two terms that are easily confused:

**Extent**: the *type* — the set of possible final values a term can take on. `Int` has extent ℤ.
For a function type `T ⇒ U`, the extent is the set of all total functions from `T` to `U`.

**Progress algebra**: the *separation algebra* for a type — the structure of possible *operational
states* during computation, from `⊥` (nothing known) up through partial computations to the final
value. `Int` has progress algebra `{⊥} ∪ ℤ`; `T ⇒ U` has progress algebra `T ⇀ U` (partial
functions, composable by disjoint-domain union).

The distinction matters because the extent is a simple set, while the progress algebra is an
algebraic structure with `⊕`, `⊥`, and the extension order. Confusing them leads to muddled
reasoning about what "more information" means at runtime.

The code currently uses "extent" in both senses; the term "progress algebra" was introduced
during the brainstorm in [brainstorm/guards-and-separation-algebras.md](brainstorm/guards-and-separation-algebras.md) and should
progressively replace the overloaded usage.
