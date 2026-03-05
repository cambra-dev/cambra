# Operational Semantics: Deprecating Yield Guards

This section explains the transition from the previous operational semantics to the one
described in [semantics.md](semantics.md).

---

## The Problem with Separate Yield Guards

The original protocol included an additional guard role:

**Yield guard**: a producer's assertion that a region of its tiling is final — no further
tiles will cover that region.

For scalar terms, this was coherent: a yield guard narrows the set of possible output values by
ruling out a region.

For function terms, it was problematic. A `Domain(D)` yield guard says "all mappings for inputs
in D are final" — but this is a statement about *progress*, not a predicate on the function's
*value*. Trying to interpret such a statement for a value, rather than the steps along the way
to computing the value, makes the guard vacuous.

Because of this confusing, the code currently conflates extents and tilings. The new model
distinguishes them more clearly.

---

## The Direction: Tilings for Sparse Functions

The resolution is to define the notion of progress as part of the tiling. Nontrivial yield
guards are only needed when computing a function with a dynamically-defined domain (e.g. stdin,
timeseries): `f: (t: T | P(t)) ⇒ U`, where `P` is a predicate that must be computed at runtime.

An intutive approach is to lift `P` out of the type and define an intermediate function:

```
f_opt : T ⇒ Option(U)
  = λ t →  if P(t) then Some(t) else None

f = λ t | f_opt(t) != None → case f_opt(t)
    Some(u) → u
    None → unreachable
```

We can then use the standard partial-function tiling over `T ⇒ Option(U)` to describe its semantics.
However, if the domain `T` is unbounded, the `None` mappings of `f_opt` can grow to be arbitrarily large.
So, we can represent it at runtime as a set of mappings and a predicate defining the region mapped to `None`.
```
SparseFn(T, U) = {somes: T ⇀ U, nones: Predicate(T)}
sparse_apply : { SparseFn(T, U), T } ⇒ functionTiling(T, Option(U)).Tile
  = λ (somes, nones), t →
      if t ∈ somes      then Some(somes(t))
      else if t ∈ nones then None
      else ⊥
```

`SparseFn` implements the partial function tiling for `T ⇒ Option(U)`, but with a more compact
representation than mapping every element of the domain.
This tiling has universal split-determinism, as all partial-function tilings do.

This representation allows consumers to split on the function's domain and receive a compact
sub-tile in response. It also replaces yield guards, which formerly provided an out-of-band version
of the `nones` predicate. Consumers lose the ability to only request the `nones` predicate, but
that's not a problem because they retain the ability to restrict the requested domain. That is,
they'll receive all data within a region of the domain, whether mapped to `Some` or `None`, which
is what they needed anyway.

NOTE: If there are a large number of `some` mappings _outside_ of the `nones` predicate, calls to
`get(¬nones)` may end up repeatedly returning large amounts of data. This is a special case of
an unsolved problem: how and whether to provide a "get everything since my last call to get"
concept. Any homomorphic operator can stream like this, so it could make sense to provide first-class
support for it in the protocol. However, we are deferring solving this problem until we find a
compelling need.

NOTE: An alternative approach to incremental gets specific to this case is to come up with a
tiling that allows splitting the `somes` mappings from the `nones` predicate. The approach
above does not permit this because it doesn't distinguish between "defining a mapping" and
"sealing part of the domain". If we wanted to make that distinction, we could probably do so by
adding epoch numbers to the mappings and sealing predicates. That would let us talk about
"the subtiling of tiles that had sealed a certain predicate by a certain time", which would permit
projection guards to split the mappings and the sealing predicate into separate tiles. Then,
consumers could use this "sealed by" guard to project out progress information with no data.

---

## New Protocol

The producer/consumer protocol, stated in terms of tiles and guards:

```
// Operator creates the dataflow link
Operator::subscribe(intent: Guard, consumer: Consumer, var_scope: VarScope) -> Producer

// Producer pushes notifications to consumer
Consumer::notify()
    // New tile available — consumer should call get()

// Consumer pulls data and manages lifecycle
Producer::get(projection: Guard) -> GetResult { compact_obsolete, relevant }
    // Returns the producer's current state, projected by the consumer's projection guards:
    //   compact_obsolete: compacted summary of tiles the consumer has released
    //   relevant: the non-released tile within the consumer's intent subtiling
Producer::release(obsolete: Guard) -> Guard
    // Consumer retracts interest; producer may compact and reclaim resources
```

**Invariants**:
- `get()` returns the producer's current decomposed state, projected by the consumer's
  projection guards. Progress monotonicity is structural: `compact_obsolete` accumulates via `⊕`, and
  `relevant` reflects all non-released tiles received so far.
