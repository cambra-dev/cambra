# Mutability model

Status: a proposal under review. This design supersedes [mutability.md](mutability.md), which
describes the current implementation and stays until this design is reviewed and the code that
cites it is migrated. Nothing here is implemented. The effects stack in progress (`requires` and
`causes` clauses) is read as current work that this design may change, not as a fixed constraint.

[A walkthrough of this design](https://claude.ai/artifact/Fu13L3Jr1Dhn7c7ULjoqQu), with an
interactive example for each section and shared review notes, is on claude.ai.

## Summary

**Values, places and variables.** A value is immutable data. A place holds a value: `Mut` and
`Cell` are mutable places, and `Feed` and `OnceMap` are immutable places whose values are defined
piecewise. A variable of one of these four types is a place variable: it names a place, and it is
never stored in data, returned or aliased. Every other variable is a value variable. A reference
value, such as a `Ref` or a key, points at a place, and `Ref::new` allocates a place that no
variable names ([Values, Places, and Variables](#values-places-and-variables)).

**Mutable places.** A program chooses between two kinds by type.

- **A `Mut(𝑉)`** is exclusive and sequential. It holds a value under Mutable Value Semantics (MVS),
  is never shared, and never needs a transaction
  ([Mutable Value Semantics](#mutable-value-semantics)).
- **A cell, `Cell(𝑉, 𝑅)`,** is shared and transactional. A `Ref` can point at it, it belongs to a
  realm `𝑅`, and it is read and written only inside a `with begin():` block ([Cells](#cells)). Every
  transaction is strictly serializable. Static analysis never weakens isolation; it lets the engine
  skip work it can prove unnecessary.

**Immutable places: deferred collections.** A `Feed(𝑇)` or a `OnceMap(𝐾, 𝑉)` is a place that holds
an immutable value, defined piecewise. Its contributions combine without order, its value is read
only when final, and it has no history. A module exports values and never places, and it takes
input through functions ([Deferred collections](#deferred-collections),
[Modules and deferred collections](#modules-and-deferred-collections)).

**Borrowing.** A `Mut`, a `Feed` and a `OnceMap` can be borrowed for the duration of a call, marked
`&` at the use, and a root cell's content is lent as a `Mut`. Every contribution to a place variable
is marked at a site in its scope ([Values, Places, and Variables](#values-places-and-variables)).

**References.** A program refers to a place in four ways
([Four kinds of reference](#four-kinds-of-reference)):

- a **borrow**, `&x`, which is not a value and ends with its call;
- a **`Ref(𝑉, 𝑅)`**, an opaque value that points at a cell, which the collector manages;
- a **validated key**, whose referential integrity the compiler checks at each deletion;
- an **unvalidated key**, which the program checks with a guard.

**Versions and views.** These follow from cells:

- A type whose definition reads a cell is a version-indexed type, declared with `requires
  Transaction` ([Versions and version-indexed types](#versions-and-version-indexed-types)).
- A function that reads cells is a view. `@materialize` makes the system maintain its value,
  inside each writing transaction or after commit ([Views](#views)).
- A refinement in a cell's content type is an invariant over every committed version
  ([Invariants over cell contents](#invariants-over-cell-contents)).

**Execution.**

- A transaction's footprint is its read requirements and write effects, named per place. The
  compiler uses footprints to skip conflict checks, never to weaken isolation
  ([Footprints and elision](#footprints-and-elision)).
- Unreachable cells are reclaimed by reference counting. A program whose type graph of cells has a
  cycle is rejected, so no cell is traced ([Garbage collection](#garbage-collection)).

## Terms

| Term | Meaning |
|---|---|
| **value** | Pure data, which is immutable. Two equal values are interchangeable. |
| **place** | Where a value is held: the place a place variable names, a place allocated with `Ref::new`, or a projection of either (`.f`, `[k]`, `*`, `->`). |
| **reference value** | A value that points at a place: a `Ref`, a `Pin`, a map key or a list index. |
| **value variable** | A variable bound to a value, such as an `=` binding or a plain parameter. |
| **place variable** | A variable whose type is `Mut`, `Cell`, `Feed` or `OnceMap`: it names a place. It is never stored in data, returned, aliased or public, and is borrowed only for the duration of a call. |
| **merge law** | How the contributions to a place combine: overwrite, commutative union or disjoint definition. The term is `src/ccl/design/mutability.md`'s, which gives `Mut` the overwrite law and `Feed` the append law. |
| **deferred collection** | A `Feed(𝑇)` or a `OnceMap(𝐾, 𝑉)`: a place that holds an immutable value, defined by contributions that combine without order and read only when final. |
| **declaring scope** | The scope whose declaration introduces a deferred collection. Every contribution to the collection is in it ([Which contributions participate](#which-contributions-participate)). |
| **cell** | A place that holds a shared, mutable value, with concurrent mutation managed by transactions. A `Ref` can point at it. |
| **allocation site** | The `Ref::new` expression that allocated a cell, or the declaration of a root cell. |
| **realm** | The cells and views that can interact transactionally, and their commit order, named by a nominal type with a `std::txn::Realm` instance. A program that declares none uses one unnamed default realm. |
| **`Txn(𝑅)`** | The commit order of realm `𝑅`: the domain of the histories of `𝑅`'s cells. `Txn` alone means the default realm's. |
| **version** | The content of one realm's cells at one point: the content after a commit, or at a point inside a transaction after some of its writes. Written `𝜏`. |
| **version-indexed type** | A type declared with `requires Transaction`: one type per version, written `𝑇@𝜏` when the version matters. |
| **view** | A function `() ⇒ 𝑉 requires Transaction` whose definition reads cells. |
| **footprint** | The cells, and the parts of cells, that a transaction reads and writes. |
| **dataflow** | The computation outside every transaction, over immutable data, ordered only by data dependence ([Crossing between dataflow and transactions](#crossing-between-dataflow-and-transactions)). |

## Principles

1. **Isolation is fixed.** Every transaction is strictly serializable. A program that gives up a
   static guarantee gets runtime conflict checks, never weaker isolation.
2. **A contribution goes to exactly one place.** A `Mut` or a cell is a history, and a deferred
   collection is its final value. `Mut`s and deferred collections satisfy the rule because they
   have no aliases. Cells satisfy it because each cell is one place with one history, whether a
   variable names it or a `Ref` points at it.
3. **Only a cell can be pointed at by a `Ref`.** Sharing a mutable place between concurrent
   computations, and storing or returning a reference to one, need a `Ref`. A program that needs
   any of these uses a cell. A key or an index points at a place within a collection, relative to
   that collection.
4. **Static knowledge buys performance, not semantics.** Footprints, commutativity and the type
   graph of cells let the engine skip conflict checks and collector work. The result is the same
   with or without them.
5. **Integrity checks are explicit or proved.** The compiler never inserts a runtime check that
   can fail a transaction. A deletion that could leave a validated key dangling is either proved
   safe or guarded by a check the program writes.

## Values, Places, and Variables

A **value** is pure data, such as an `Int` or a `Ref`. It is immutable.

A **place** holds a value. `Mut` and `Cell` are mutable places: the value a place holds changes over
time. `Feed` and `OnceMap` are immutable places, whose value is defined piecewise elsewhere in the
code.

A **variable** is a name bound to a value or to a place. A variable whose type is `Mut`, `Cell`,
`Feed` or `OnceMap` is a **place variable**, and every other variable is a **value variable**. Place
variables are restricted in how they are used, so that each keeps naming its one place.

A **reference value** is a value that points at a place: a `Ref`, a `Pin`, a map key or a list
index. Dereferencing a reference value reaches its place. `Ref::new` **allocates** a place at run
time. No name in the program denotes such a place, and the program reaches it only through `Ref`s.

Places are mutable or immutable:

| Place | Holds | Contributions |
|---|---|---|
| `Mut(𝑉)` | A mutable value | Exclusive and sequential |
| `Cell(𝑉, 𝑅)` | A mutable value | Shared, in transactions |
| `Feed(𝑇)`, `OnceMap(𝐾, 𝑉)` | An immutable value, defined piecewise | Combine without order; the value is read only when final |

Place variables have rules defining their semantics and governing their use:

| Variable type | Merge law | Contributors | History over | Pointed at by a `Ref` |
|---|---|---|---|---|
| `Mut(𝑉)` | Overwrite | Exclusive and sequenced | Its induction domain | No |
| `Cell(𝑉, 𝑅)` | Overwrite | Serialized by transactions | `Txn(𝑅)` | Yes: `ref(x)` gives a `Ref` |
| `Feed(𝑇)` | Commutative union | Unordered | None | No |
| `OnceMap(𝐾, 𝑉)` | Disjoint definition | Unordered | None | No |

Place variables share these rules:

- **A place variable is never stored in data, returned, or captured by a closure that outlives its
  scope.** A value refers to a cell through a `Ref`. No `Ref` points at a `Mut` or a deferred
  collection.
- **A place variable is never public.** A module exports a value, such as `pub output = f`, which
  exports `f`'s final value. No module borrows or writes a place variable that another module
  declares; it calls one of that module's functions instead.
- **A place type nests in nothing.** A place holds a value, which may be nested to any depth. No
  type places a `Mut` in a cell, a feed in a `Mut`, or a cell in a record.
- **Using a place variable as a value copies its value at the reader's position.** A `Mut` gives its
  value at that point in the program. A cell gives its content at the reading transaction's version.
  A deferred collection gives its final value wherever the read stands. Assignment, return, storing
  in data and passing to a plain parameter are such uses.
- **A borrow lasts for one call.** A `Mut(𝑉)`, `Feed(𝑇)` or `OnceMap(𝐾, 𝑉)` parameter borrows its
  argument to contribute to it. A root cell's content is lent by name, `&counts`. The content of a
  cell reached through a `Ref` is lent through `*` or `->`: `&*r`, `&r->items` ([Converting a cell
  to a Mut](#converting-a-cell-to-a-mut)).
- **Only places can be borrowed.** A place is named by a place variable, by a path from one such as
  `xs[i]` or `s.cart.items`, or by a path through a reference such as `*r` or `r->items`. A value
  is not a place: `&x` with `x` a value variable, and `&f(y)`, are type errors. In `&r->items`, the
  value variable `r` is not lent; the place lent is the one its `Ref` points at.
- **A borrow is marked at the use.** `&` binds tighter than the postfix operators `.`, `[ ]` and
  `->`, so `&xs.push(v)` is `(&xs).push(v)`. It marks the place that follows as used mutably, and
  the steps after it keep that place mutable. A marked place in a borrowing position is lent at its
  full path. The borrowing positions are an argument to a `Mut(𝑉)`, `Feed(𝑇)` or `OnceMap(𝐾, 𝑉)`
  parameter, and the receiver of a method that takes `self: Mut(Self)`. A marked place anywhere
  else is a type error, and so is an unmarked place in a borrowing position. An unmarked argument
  is always a copy.
- **A projection maps a place to a place.** `.f` and `[k]` extend a place's path from the same
  root, by rule 3 of [The rules](#the-rules). `*r` is the place of the content of the cell `r`
  names, rooted at that cell, and `r->f` is `(*r).f`. A function call yields a value, never a
  place.
- **A parameter's borrow mode is part of its type, and inference supplies it.** In a `def`, the
  body's marked uses decide it. `a := …`, `a += …` or `&a` makes `a` a `Mut(𝑉)` parameter, `a << v`
  a `Feed(𝑇)` and `a[k] = v` a `OnceMap(𝐾, 𝑉)`. A parameter that is only read is a plain parameter.
  A function value called as `g(&x)` is inferred to borrow that argument. A written annotation
  asserts the mode. A type with no term to infer from states it: a Module type, a trait method's
  signature, or an alias of a function type. A body that starts or stops contributing to a parameter
  makes every caller whose mark disagrees a type error, so no caller's meaning changes silently.
- **A parameter is never rebound locally.** `a := …` on a parameter writes the caller's place. A
  function that wants its own copy writes `b := a`.
- **No operation moves a place variable.** A place variable is introduced by its declaration and
  ends with its scope. [Parameter conventions](#parameter-conventions) lists no consume convention.

| Written | Lends |
|---|---|
| `f(&n)`, with `n = 3` a value variable | Nothing: a type error |
| `tally(&counts, order)` | `counts` |
| `&xs.push(v)`, which is `(&xs).push(v)` | `xs` |
| `&s.cart.items.push(v)` | `s.cart.items`, not `s` |
| `swap(&xs[i], &xs[j])` | `xs[i]` and `xs[j]`, which must be disjoint |
| `x = &stack.pop()` | `stack`; `x` is bound to the result |
| `&*r`, with `r: Ref(𝑉)` | The content of the cell `r` names |
| `&r->items.push(v)` | Field `items` of that cell's content |
| `&r`, with `r: Ref(𝑉)` an immutable binding | Nothing: a type error |
| `&x`, with `x: Mut(Ref(𝑉))` | The variable `x`: which cell it refers to |
| `&*x` or `&x->items`, with `x: Mut(Ref(𝑉))` | The content of the cell `x` refers to, or its field `items` |

Footprints and exclusivity use the lent path, so `&s.cart.items.push(v)` does not overlap a use of
`s.name`. Only a place is lent. A temporary is not a place, so `xs.sorted().push(v)` is a type
error when `push` takes a `Mut(Self)` receiver.

Every contribution to a place variable is therefore marked at a site in the variable's scope: `:=`
and the other assignment operators, `<<`, `m[k] = v`, and `&x` in a borrowing position. A `def`
never writes a captured `Mut`, by rule 2 of [The rules](#the-rules). A contribution to a deferred
collection inside a `def` that captures it is a site in the collection's scope when the `def` is in
that scope ([Which contributions participate](#which-contributions-participate)). A caller of that
`def` does not see the contribution, as it does not see any write a function makes to its own
module's cells; the function's inferred effects record it.

A cell is written with the same marks as a local `Mut`. A transaction makes the cells it touches
appear exclusive to it, because transactions are serializable. Sharing happens between
transactions, outside any one block.

A place is accessed in three ways:

| Access | Marked by | Lasts | Who can contribute | Where the contributions are found |
|---|---|---|---|---|
| Copy | Nothing | It is a value | No one | Nowhere: no one contributes to a copy |
| Borrow | `&x` at the use | One call | The callee: exclusively for a `Mut`, shared for a deferred collection | In the variable's scope |
| `Ref` | Nothing at the call | Until the collector reclaims the cell | Any holder of the `Ref`, inside a transaction in the cell's realm | At each write site, `r->f := v`, and in the inferred `WriteCell` effects ([Footprints are requirements and effects](#footprints-are-requirements-and-effects)) |

A `Ref` gives mutable access with no marker at the call, because pointing at a place is what a `Ref`
is for (principle 3). The search of a place variable's scope therefore finds every contribution to a
`Mut`, a deferred collection and a root cell named directly, and no write to a cell reached through
a `Ref`. Footprints find those. A closure that holds a `Ref` and writes its cell is called with no
marker, and its effects record the write. No `Ref` points at a deferred collection, so a borrow is
the only way to contribute to one from outside its declaring scope.

An allocated place's content is reached through `*` or `->` (`to_mut`), which yields a `Mut` for
the duration of the access.

The merge law decides the rest. Overwrites do not commute, so the contributors to a `Mut` are
exclusive and sequenced, and the contributors to a cell are serialized by transactions. Unions
commute and disjoint definitions do not overlap, so the contributors to a deferred collection need
neither, and a deferred collection has no history to read.

## Mutable Value Semantics

The rules in this section are `Mut`'s. [Values, Places, and Variables](#values-places-and-variables)
states which of them deferred collections and cells share.

### The rules

MVS (Racordon et al., "Implementation Strategies for Mutable Value Semantics", 2022, the model of
the Hylo language) has four rules:

1. **Values are independent.** `b = a` copies `a`'s value. A write through one name is never
   visible through another.
2. **References are second-class.** A reference exists only as a `Mut` parameter for the duration
   of a call. It cannot be stored, returned or captured by a closure that outlives the call. MVS
   needs no lifetimes because every reference ends with its call.
3. **Writing a part writes the whole.** `m[k].f += 1` writes one field of one entry of `m`, in
   place.
4. **Exclusivity.** While a value is passed for mutation, nothing else accesses it.
   `swap(&xs[i], &xs[j])` is legal only where `xs[i]` and `xs[j]` are disjoint.

The current second-class discipline (`mutability.md`, "No aliasing: `Mut` values are second-class
(downward-only)") already implements rules 1 and 2, with one gap: no pass rejects a `def` that
writes a captured mutable variable, and the write is invisible to the segment its call sits in.
This design adds:

- **Paths as write targets.** `m[k].f := v` writes a part, and a path can be passed to a `Mut`
  parameter. The history records the write at that path.
- **Exclusivity at the granularity of parts.** Two `Mut` arguments must be disjoint paths.
  Disjointness of computed indices (`i != j`) is a refinement obligation discharged by z3.

```python
def tally(counts: Mut(Map(Sku, Int)), order: Order):
    for line in order.lines:
        counts[line.sku] += line.qty      # writes one entry, in place

def swap(a: Mut(Int), b: Mut(Int)):
    t = a                                 # a snapshot of a's value
    a := b
    b := t

swap(&xs[i], &xs[j])                      # accepted only where i != j is provable
```

### Parameter conventions

| Convention | Hylo | Cambra | Native code |
|---|---|---|---|
| Read-only borrow | `let` | plain parameter | pointer, no copy |
| Exclusive mutable borrow | `inout`, with `&` at the call | `Mut(𝑉)` parameter, with `&` at the call | pointer, no copy |
| Initialize | `set` | `:=` introduction | — |
| Consume | `sink` | none | move |

`sink` is left out until profiling shows copies that uniqueness analysis cannot remove.

### Performance under native code generation

Mutability elimination already turns local mutation into pure recurrences. In-place update is an
optimization on that pure program. A value is updated in place when it has one consumer. Under MVS
exactly three things create a second consumer:

1. a snapshot (`b = a`) followed by a write to either name;
2. a read of the history at a position earlier than the predecessor;
3. a value that reaches two consumers in the dataflow graph.

Where none applies, a recurrence compiles to one register and an aggregate to one buffer. Where
uniqueness is not provable, the fallback is reference counting with reuse when the count is one, as
in Perceus (Koka) and Lean 4.

### What MVS cannot express

Shared mutable graphs, back-pointers and callbacks that write shared places. In Cambra each is
either a structure of cells linked by `Ref`s, or a table whose rows hold keys.

## Cells

### Types

| Type | What it is | Copyable and storable | Lifetime |
|---|---|---|---|
| `Cell(𝑉, 𝑅)` | A cell declared at a module's top level: `x: Cell(𝑉, 𝑅) := init`. A **root cell**; each run of the module has its own. | The variable is not; `ref(x)` gives a `Ref` | Until every consumer releases it |
| `Ref(𝑉, 𝑅)` | An opaque reference to a cell | Yes | Keeps its cell alive |
| `Pin(𝑉, 𝑅)` | A transparent key to an allocated cell, for references that leave the program | Yes, and serializable | Until `unpin`, or until its time-to-live passes |

`Cell(𝑉, 𝑅)` replaces `Mut(𝑉, Txn)`. With `Txn` gone from `Mut`, the domain slot of `Mut` holds
only induction domains, which inference always supplies, so the surface type is `Mut(𝑉)`. `Txn(𝑅)`
remains as the internal domain of cell histories.

The second argument is the cell's realm ([Realms](#realms)), fixed where the cell is created. A root
cell's declaration names it; `x: Cell(𝑉) := init` places the cell in the default realm.
`Ref::new` allocates in the realm of the enclosing transaction. Every other annotation may omit the
realm, as in `Ref(𝑉)`, and inference supplies it from the flow of the value.

A root cell's consumers are the code that names it, the materialized views defined over it, and the
`Ref`s to it. A consumer **releases** a part of the cell once it can no longer read that part.
Storage is reclaimed per part, once every consumer has released it:

| Part | Released when |
|---|---|
| A past version | No consumer can still read at that version: the low watermark has passed it |
| A deleted key, and the history under it | No consumer can still read a version in which the key was present |
| A key range | No consumer can read keys in that range again, for example below a bound it has passed |
| The whole cell | Every consumer has released it: no loop or transaction that names it can still run, and no `Ref` to it is reachable |

Until a part is released by every consumer, it is a root for the collector.

A cell's content `𝑉` is a value. It may contain `Ref`s, keys and nested collections. A row inside a
cell's collection is part of the cell's value: removing it from the collection deletes it.

### Operations

```text
Ref::new(v: V) => Ref(V, R)            requires Transaction(R)
ref(x: Cell(V, R)) => Ref(V, R)
to_mut(r: Ref(V, R)) => Mut(V)         requires Transaction(R)   # spelled *r; r->f is (*r).f
r == s                                                           # same cell; hashable
pin(r: Ref(V, R)) => Pin(V, R)               requires Transaction(R)
pin(r: Ref(V, R), ttl: Duration) => Pin(V, R)   requires Transaction(R)
unpin(p: Pin(V, R))                          requires Transaction(R)
resolve(p: Pin(V, R)) => Option(Ref(V, R))   requires Transaction(R)
```

- **`Ref::new` requires a transaction**, so a cell's creation is part of a commit. The new
  place is named by its allocation site and the position where `Ref::new` runs, so allocation
  never conflicts.
- **A pin ends by `unpin` or by its time-to-live.** `pin(r, ttl)` suits a reference that expires,
  such as a session cookie. Once `ttl` has passed since the pin committed, the system unpins the
  cell in a commit of its own.
- **`Ref` has equality and hashing but no order.** An order would expose allocation order.
- **A root cell is read and written by name. A cell reached through a `Ref` is read and written
  through `*r` and `r->f`** ([Converting a cell to a Mut](#converting-a-cell-to-a-mut)).

### Converting a cell to a Mut

`to_mut` yields a cell's content as a `Mut`, and requires a transaction in the cell's realm. It has
two cases, which differ in whether the access goes through a `Ref`:

| Case | Spelling | Inserted by the compiler |
|---|---|---|
| A root cell named directly | `x`, as for a local `Mut` | Always |
| A cell reached through a `Ref` | `*r`, or `r->f` for a field | Never |

- **A root cell's name always means its content.** No parameter has a `Cell` type, so a root cell is
  never an argument. Only `ref(x)`, `history(x)` and `await_final(x)` take the cell itself, and
  they take it by name as special forms. Everywhere else the conversion is unambiguous.
- **`*` and `->` mark where an access goes from a `Ref` to the place it points at.** They apply to
  a `Ref`. On a cell
  they are type errors.
- **`*` binds looser than the postfix operators, as in C, and `->` is a postfix operator beside
  `.`.** `*r.f` is `*(r.f)`, the content of the cell named by the `Ref` in field `f`. `r->f` is
  `(*r).f`. A chain through `Ref`s needs no parentheses: with `s: Ref(Session)`, whose `cart`
  field holds a `Ref(Cart)`, the cart's items are `s->cart->items`, as in [Example](#example).
- **A pair is written `k ↦ v`.** `->` was the pair arrow, and `a -> b` is the two-tuple `(a, b)`
  ([spec 2.4](../../../docs/chl-spec.md#24-atoms)), so `(k, v)` is the spelling of a pair without
  `↦`. A lambda keeps `\x -> body`. The parse is unambiguous, because a lambda's binders are names
  and type annotations, and no type uses `->`.

`to_mut` is a projection, not an ordinary function. Rule 2 of [The rules](#the-rules) forbids a
function from returning a `Mut`; a projection yields a `Mut` place that lasts as long as the
access, as a Hylo subscript yields an `inout` projection. The result is read, written and passed to
`Mut` parameters, and is never stored, returned or used outside the transaction that produced it.
The `Ref` operations follow from it:

| Form | Meaning |
|---|---|
| `v = *r` | Copies the cell's content: a snapshot, by rule 1 of [The rules](#the-rules), which later writes to the cell do not change |
| `*r := v` | Writes the whole cell |
| `r->f`, `r->xs[k]` | `(*r).f`, `(*r).xs[k]`: parts of the cell's content |
| `r->f := v`, `r->xs[k] += 1` | Writes a part |
| `r.f` | A type error: a `Ref` has no fields |
| `r == s` | Whether `r` and `s` point at the same cell |

`to_mut(𝑥)` holds the cell's content at the transaction's current version. A write to it, or to a
path within it, produces the transaction's next version, and the cell receives the write when the
transaction commits ([Transaction boundaries](#transaction-boundaries)).

Nothing is inserted at an argument, so an argument's spelling says which place is lent.
`tally(&counts, order)` with `counts: Cell(Map(Sku, Int))` lends the root cell's content, and
`tally(&*r, order)` lends the content of the cell `r` names.

Rule 4 of [The rules](#the-rules), exclusivity, applies to `Mut`s that come from cells. A local
`Mut` and a cell's `Mut` never overlap, because no `Ref` points at a local `Mut` and no cell can
name it. Two cells' `Mut`s overlap when they can name the same cell and their paths within that cell
overlap. The compiler proves them disjoint from:

| Fact | Example |
|---|---|
| Two root cells with different names are different cells | `swap(&x, &y)` |
| Two `Ref`s, or a `Ref` and a root cell, whose site kinds share no site, name different cells. `ref(𝑥)` has `𝑥` as its site. | `swap(&x, &*ref(y))` is accepted; `swap(&x, &*ref(x))` is rejected |
| A refinement establishes that two `Ref`s differ | `swap(&*r, &*s)` inside `if r != s:` |
| Two paths within one cell are disjoint, as for local values | `swap(&r->xs[i], &r->xs[j])` where `i != j` is provable |

A borrow must also be disjoint from the callee's writes through `Ref`s passed beside it. In
`f(&*r, s)`, `f` may write through `s` while the content of `*r` is lent. The call's lent paths must
be disjoint from the callee's inferred effects through its other arguments, and the facts above
discharge that obligation as they do for two borrows.

A program whose disjointness the compiler cannot prove is rejected until it writes the check, such
as `if r != s:` around the call. The compiler never inserts it (principle 5).

### When a transaction is required

| Operation | Requires a transaction |
|---|---|
| Reading or writing a `Mut(𝑉)` variable | No |
| Holding or passing a `Cell(𝑉)`, `Ref(𝑉)` or `Pin(𝑉)` | No |
| Reading or writing a cell, through its name, a `Ref` or `to_mut` | Yes, in the realm its type names |
| Reading a view | Yes, in the view's realm; see [Views](#views) |
| Holding a value whose type is version-indexed, such as a `UserKey` | Yes; see [Types that require a transaction](#types-that-require-a-transaction) |

A local `Mut` variable may hold a value containing `Ref`s. Writing through those `Ref`s still
requires a transaction.

### Example

```python
Cart = {items: Map(Sku, Int)}
Session = {user: UserId, cart: Ref(Cart)}

carts_by_user: Cell(Map(UserId, Ref(Cart))) := Map::empty

for req in logins:
    token = with begin():
        u = req.user
        cart = carts_by_user[u]! if u in carts_by_user.keys() else Ref::new((items=Map::empty))
        carts_by_user[u] := cart
        pin(Ref::new((user=u, cart=cart)))                # the Pin goes into a cookie
    login_resps << str(token)

for req in adds:
    with begin():
        match resolve(parse_pin(req.token)):
            case Option::some(s):
                s->cart->items[req.sku] += req.qty
            case Option::none:
                pass                                      # unknown session: no write
```

The transaction in the `adds` loop reads a `Session` cell allocated in `logins` and writes the path
`items[req.sku]` of a `Cart` cell allocated in `logins`. Which cells those are is known only after
the transaction reads the `Pin`.

`Ref::new` returns a `Ref`, and the cart's cell lives in the implicit map of its allocation site
(see [Ref as a key into an implicit map](#ref-as-a-key-into-an-implicit-map)). It stays reachable
through `carts_by_user` and through the pinned `Session`; a transaction that stored the `Ref`
nowhere would leave the cell garbage.

### Transaction boundaries

Every transaction is an explicit `with begin():` block. No transaction is implicit: a statement
outside a block never runs as its own transaction, and a loop iteration is a transaction only where
its body opens a block.

Inside a block, a cell is read and written through `to_mut`, and a `Mut` declared outside the block
is read and written as a `Mut`. The block reads its own writes. Nothing outside the block sees them
before the commit: another transaction sees a cell's new content at the commit's version, and the
enclosing loop sees a write to an outer `Mut` at that loop step. A denied or aborted transaction
leaves no write. An append to a feed inside a block is therefore a contribution only on commit,
which is the gating [spec 8.4](../../../docs/chl-spec.md#84-feeds-are-the-second-form-of-mutability)
states for a reply fed inside `with begin():`. A `OnceMap` definition inside a block is partial
([Totality and transactions](#totality-and-transactions)).

### Transaction outcomes

[Spec 8.2](../../../docs/chl-spec.md#82-transactions-with-begin) decides what a block yields. A
block in value position is the value of its last statement. A path that writes nothing, such as the
deny idiom, commits with no writes, and the code after the block runs with that path's value. An
exception that escapes the block aborts it: none of its writes commits, it takes a commit position
at which it commits nothing, and the exception propagates to a `try`
([Exceptions](../../../docs/chl-spec.md#exceptions)). This design adds a deadline:

```python
for k ↦ req in srv::reqs:
    try:
        v = with begin(deadline=time::millis(50)):
            reserve(req.body.sku, req.body.qty)
        resps[k] = http.ok(v)
    except GaveUp:
        resps[k] = http.unavailable()
```

- **A deadline sheds load.** `with begin(deadline=𝑑):` raises `std::txn::GaveUp`, a nominal
  exception, when the transaction has not committed within `𝑑`. The limit is a duration, not an
  attempt count, because the number of attempts depends on the engine's strategy.
- **A block with a deadline causes `Raise(GaveUp)` and requires `ObserveWorld`.** Whether it gives
  up depends on load and time, as a reading of the clock does.
- **A block that gives up takes a commit position with no writes, as an aborted block does.** Its
  outcome depends on load and time, so the commit order records it, and reload and recovery replay
  it. The commit position is where the sequencer decides between the last attempt committing and
  the deadline firing.
- **A program catches `GaveUp` inside the loop body.** An exception that escapes an iteration
  orders the iterations ([Exceptions](../../../docs/chl-spec.md#exceptions)).
- **Conflict retries are internal to the engine.** A program observes one result per block and
  never the attempts behind it.
- **The engine guarantees progress under contention.** A transaction that conflicts repeatedly
  still commits, so no program needs a retry limit to terminate. Many established techniques
  provide this guarantee, and this design does not choose one.
- **No write survives an abort.** Writes to cells and to outer `Mut`s stay gated on commit. A retry
  policy is ordinary code outside the block: it catches the exception, counts attempts in its own
  `Mut`, and passes the attempt number into the body as an argument. A policy that needs data from
  a failed attempt gets it from the exception's payload.
- **Isolation is unchanged.** An aborted block and a block that gave up write nothing, so no other
  transaction can tell them apart from a transaction that wrote nothing.
- **A failed attempt has no output.** No log or sink receives output from an attempt that did not
  commit, so whether the engine retries or takes locks stays unobservable. The engine's
  per-transaction metrics show contention. A logging channel for failed attempts is left out until
  a program needs one, because it would make the engine's strategy observable.

### Realms

A realm is a nominal type with an instance of the marker trait `std::txn::Realm`. A program that
declares none has one unnamed default realm:

```python
type Analytics = {}
instance std::txn::Realm(Analytics)

with begin(Analytics):
    ...
```

- **A realm is identified by its type.** A nominal type is identified by its declaring module's
  path, its name and its implicit arguments (`src/ccl/design/nominal-types.md`), so a realm stays
  the same realm across reloads. `requires Transaction(𝑅)` takes a type, so a transaction's realm is
  known statically, and generic code takes the realm as a type parameter:
  `def f(R, …) requires Transaction(R)`.
- **The marker trait is required.** A nominal type without a `std::txn::Realm` instance is not a
  realm, so `Transaction(User)` is an error.
- **Runs share a realm.** Two runs of a module given the same arguments hold the same nominal
  type, so they share its realm, while each run has its own cells. A module that needs a realm
  per run takes the realm as a type parameter.
- **Visibility controls access.** A module that does not export its realm type keeps the realm
  private.
- **Each realm has its own commit order**, `Txn(𝑅)`, and is strictly serializable on its own.
  No ordering holds between two realms except what a deferred materialized view establishes (see
  [Deferred materialized views](#deferred-materialized-views)).
- **A transaction runs in one realm.** It reads and writes only that realm's cells and views. A
  value crosses between realms only as plain data: a transaction's result, or an argument to a
  later transaction.
- **The capability takes the realm.** `requires Transaction(𝑅)` requires a transaction in `𝑅`. A
  bare `requires Transaction` means the default realm, on a function, a view and a type
  declaration alike. `requires Transaction(_)` infers the realm from the cells the definition
  reads. An omitted realm is the default realm and is never inferred.
- **The engine may split a realm.** It may run a realm's transactions in several smaller commit
  orders when no transaction spans two of them. No program can observe the split.

## Versions and version-indexed types

### A cell's content depends on the version

A cell denotes a history `Txn ⤇ 𝑉`. Inside a transaction, each write produces a new version, because
a transaction reads its own writes. Mutability elimination already represents those versions as a
chain of shadowing `let`s, so each version is an immutable value:

```text
let users₀ = <snapshot read of users>
let k : {Int | k ∈ users₀} = …
let users₁ = users₀ ∖ {j}
… a use of k against users₁ requires k ∈ users₁, that is, k ≠ j
```

A refinement over a version is therefore an ordinary refinement, and z3 discharges its
obligations. What remains to design is how a type names the version it is checked against.

### Types that require a transaction

A type whose definition reads a cell is declared with `requires Transaction`. It is a
**version-indexed type**: one type per version.

```python
users: Cell(Set(Int)) := Set::empty
type UserKey requires Transaction = {Int where _ in users}
```

The version belongs to the realm of the cells the definition reads, and a definition reads cells of
one realm. The clause names that realm, `requires Transaction(App)`, or infers it,
`requires Transaction(_)`; a bare clause names the default realm ([Realms](#realms)).

`UserKey` elaborates to `UserKey@𝜏`. A value's type is always applied, so every mention of
`UserKey` as the type of a value needs a version supplied by something in scope:

| Supplier | What it supplies |
|---|---|
| A `with begin():` block | The current version at each point in the block |
| `Cell(𝑉)`, `Ref(𝑉)`, `Pin(𝑉)` | To `𝑉`: every committed version, and inside a transaction, the version being read |
| A type declared with `requires Transaction` | To the types in its definition: the version it was given |
| A function type with `requires Transaction` | To its parameter and result types: the caller's version, at each call |

A constructor that supplies no version inherits the requirement from its arguments.
`Map(UserKey, Int)` requires a transaction. `Cell(Map(UserKey, Int))` does not, because `Cell`
supplies the version.

### Functions

`requires Transaction` on a function gives the function an implicit version parameter. A signature
that mentions `UserKey` without the clause is ill-formed:

```python
def f(k: UserKey) => T:                          # error: UserKey requires Transaction,
    ...                                          #   and nothing in f's signature supplies it

def f(k: UserKey) => T requires Transaction:     # ok
    ...
```

The clause stops the requirement at the function type. `(k: UserKey) ⇒ 𝑇 requires Transaction` is
a function value that can be held anywhere. Calling it requires a transaction, and the callee
receives the caller's version.

The clause has the same meaning in both positions: it adds an implicit version parameter to an
abstraction. On a type it sits in the declaration's head, before `=`. On a function it follows the
result. A declaration can use both, and each attaches to its own abstraction:

```python
type Handler requires Transaction = (k: UserKey) => T requires Transaction
```

A function's `requires` clause lists requirements, as in the effects stack: `Transaction`, and
`ReadCell(𝑝)` for each path it reads. A type's clause supplies a version and grants no access, so it
is exactly `Transaction`.

### Version-indexed parameters

A version-indexed type can be passed unapplied where the expected kind is version-indexed:

```python
def eg(Fam: Type requires Transaction, v: Fam) => R requires Transaction
```

`v: Fam` is an application, so `eg` needs its own clause. `Cell` has this kind for its argument: it
takes a version-indexed type and supplies each committed version to it.

### Leaving a transaction

A value whose type is indexed by a transaction's version cannot leave the transaction's
`with begin():` block. To leave, it is explicitly converted to a type that mentions no version. A
`UserKey` returned from the block is cast to `Int`, which makes it correct data and an unvalidated
key. A value whose type has no version-free supertype, such as a closure whose type mentions the
version, cannot leave at all.

- **The cast is required.** A block whose result type is version-indexed is an error without one.
  The compiler asserts that no type outside a transaction is version-indexed.
- **A cell initialized from the result holds the cast's type.** The value has lost its version, so
  it is not a `UserKey`:

```python
def pick_user() => UserKey requires Transaction: ...

u: Int = with begin(): pick_user()      # the cast: a type ascription on the binding
k: Cell(UserKey) := u                   # error: an Int is not a UserKey
k: Cell(Int) := u                       # ok
```

The cast is a type ascription on the binding that receives the block's result, `u: Int = with
begin(): …`. A result with no version-free supertype is an error at the ascription.

## Views

A **view** is a function `() ⇒ 𝑉 requires Transaction` whose definition reads cells. Calling it
evaluates the definition at the caller's version, including the calling transaction's own writes.
A view needs nothing beyond an ordinary function.

- **A view reads one realm.** Its definition reads the cells and views of the realm its `requires`
  clause names. Values move between realms only as plain data or through a deferred materialized
  view ([Deferred materialized views](#deferred-materialized-views)).
- **A view is not a `Cell`.** A cell's value at a version is whatever the last write left there.
  A view's value at a version is determined by the cells it reads, and a view admits no writes.
- **The definition is available to the refinement checker.** A fact read from a view, together
  with the definition, entails a fact about the cells it reads.

`@materialize` makes a view a **materialized view**: the system maintains its value eagerly and
incrementally as the cells it reads change. Caches and indexes are materialized views.

### Two kinds of materialized view

|                                 | In-transaction materialized view                | Deferred materialized view                                                                |
| ------------------------------- | ----------------------------------------------- | ----------------------------------------------------------------------------------------- |
| Declared                        | `@materialize`                                  | `@materialize(realm=𝑅, delay=𝑡)`, or `@materialize(delay=𝑡)`                             |
| Realm                           | Its sources' realm                              | `𝑅`, or the default realm when the annotation names none; it may be its sources' realm  |
| Value read at version `𝜏`      | Its definition applied to the sources at `𝜏`   | Its definition applied to the sources at a committed version `src(𝜏)` of the source realm |
| Maintained                      | Inside each transaction that writes a source    | After the sources commit, by commits in the materialized view's realm                    |
| Cost to writers                 | Footprint and latency of the maintenance writes | None                                                                                      |
| Discharges deletion obligations | Yes                                             | No                                                                                        |
| Typical use                     | Indexes, integrity                              | Analytics, streaming                                                                      |

Both kinds reuse DBSP's incremental view maintenance (Budiu et al., VLDB 2023). A `@materialize`
definition that DBSP's operators cannot maintain incrementally is rejected. Coverage of every
definition is not a goal.

### In-transaction materialized views

Each write to a source also writes the affected entries of the materialized view, inside the
writing transaction, so the definition holds at every version, including inside a transaction
after a write. The maintenance writes are part of the writer's footprint.

#### Indexes

An index is an in-transaction materialized view. With the running example from
[Four kinds of reference](#four-kinds-of-reference):

```python
@materialize
def carts_by_item() => FullMap(ItemKey, Set(CartKey)) requires Transaction:
    refs = [i ↦ c for c ↦ cart in carts for i in cart.lines]
    return map([i ↦ set([r.1 for r in g]) for i ↦ g in groupby(refs, \r -> r.0)])

with begin():
    if k not in carts_by_item().keys():
        items.remove(k)        # carts: proved by the view's definition
```

- **An absent entry discharges the deletion obligation.** `k` absent from the index, together with
  the definition, entails that no cart's `lines` contains `k`.
- **An index has a narrow footprint.** Adding a cart with lines `[i₁, i₂]` writes
  `carts_by_item()[i₁]` and `carts_by_item()[i₂]`. The set inserts commute, so they do not conflict
  with each other. Testing `k in carts_by_item().keys()` conflicts only with writers that add or
  drop a reference to `k`. A scan would conflict with every writer to `carts`.
- **`@index` declares an index.** The declaration names the source cell, the field function and
  the index:

  ```python
  @index(carts, \c -> c.lines)
  lines_to_carts
  ```

  `lines_to_carts` maps each item key to the carts whose `lines` contain it, as `carts_by_item`
  does. The checker carries a built-in lemma for an index, "an absent key implies no occurrence in
  the source field", in place of unfolding a comprehension into quantified formulas.

### Deferred materialized views

`@materialize(realm=𝑅, delay=𝑡)` declares a deferred materialized view in realm `𝑅`. The
declaration names both realms:

- **The `requires` clause names the source realm.** The definition is an ordinary view and is
  checked as one: `requires Transaction(App)` means a transaction in `App`, the realm of the cells
  it reads.
- **The annotation names the materialized view's realm.** Callers in `𝑅` read the materialized view
  as `() ⇒ 𝑉@src(𝜏) requires Transaction(𝑅)`; the annotation derives this type, and the `requires`
  clause keeps its meaning. Without `realm=`, the materialized view is in the default realm.
- **The two realms may be one.** A deferred materialized view in its sources' realm is still
  maintained after the writing transactions commit, not inside them. A program that never names a
  realm can use one this way, at the cost of rule 5.

Each maintenance step is a commit in the materialized view's realm that installs the definition
applied to the sources at a later committed version of the source realm. `delay=𝑡` is a
scheduling target, not a bound on staleness: the engine schedules maintenance so that each
maintenance commit installs a source version committed `𝑡` before it, and maintenance that runs
long installs an older one. Commit order comes from each realm's sequencer, not from a clock, and
clock readings carry no ordering guarantee ([`docs/durability.md`](../../../docs/durability.md)).

```python
type Analytics = {}
instance std::txn::Realm(Analytics)

@materialize(realm=Analytics, delay=time::minutes(5))
def revenue_by_sku() => Map(Sku, Int) requires Transaction:
    return map([sku ↦ sum(o.qty * o.price for o in orders.values() if o.sku == sku) for sku in skus])

for req in dashboard_reqs:
    report = with begin(Analytics):
        revenue_by_sku()
    dashboard_resps << render(report)
```

The rules:

1. **A read has a version in the materialized view's realm.** At each version `𝜏` of that realm,
   the materialized view holds its definition applied to the sources at version `src(𝜏)` of the
   source realm. `src` is monotone in `𝜏`, and the engine schedules maintenance so that `src(𝜏)`
   committed `delay` before `𝜏`. A read at `𝜏` has type `𝑉@src(𝜏)`.
2. **`source_version` exposes the source version.** `source_version(revenue_by_sku)` returns
   `src(𝜏)` at the reading transaction's version, a position in the source realm's commit order. Two
   deferred materialized views in one realm can have different source versions at one `𝜏`, for
   example when their delays differ; a transaction that reads both sees each consistent with its
   own sources and compares their source versions. Other data is aligned with a result by an as-of
   join against its source version, in dataflow rather than in the reading transaction
   ([history and await_final](#history-and-await_final)).
3. **A deferred materialized view is computed from one committed prefix.** Its definition is a
   view, so it reads one realm, and it reads all of its sources at one source version, never at a
   separate lag for each source. A deferred materialized view defined over another reads it in the
   upstream's realm, as it reads any source.
4. **A deferred materialized view moves values between realms.** No view reads two realms. To join
   data in `R1` with data in `R2`, a program declares a deferred materialized view in `R2` whose
   sources are in `R1`, and joins it with `R2`'s other data in a view or a transaction in `R2`.
5. **Only a separate realm keeps a deferred materialized view apart from its sources.** A
   transaction in a separate realm reads no cell of the source realm, so it never sees a
   source-realm write beside a materialized view that predates it, a combination no serial order
   produces. A transaction in the sources' realm can read both, and then sees the sources at `𝜏`
   and the materialized view at `src(𝜏)`. The program's own constraints decide whether that is
   correct, as for a search index that lags its documents. A separate realm is the practice
   wherever they do not.
6. **Dataflow through a deferred materialized view may be cyclic.** A value derived from a deferred
   materialized view reaches a write to its sources only as plain data: a transaction's result,
   passed to a later transaction in the source realm, which is strictly serializable in its own
   realm like any transaction that receives input. The cycle is a feedback loop with a lag, as in
   a fraud score that gates new orders. Whether the loop settles is a property of the program.
7. **Keys from a deferred materialized view are data.** `ItemKey` is indexed by versions of `App`,
   and a key read from the materialized view is valid at `src(𝜏)`, not at the reader's version. A
   key leaves the materialized view only through an explicit cast to its base type, and a
   transaction in the source realm validates it with a guard. A deferred materialized view never
   discharges a deletion obligation.

## Deferred collections

`Feed(𝑇)` and `OnceMap(𝐾, 𝑉)` are **deferred collections**: immutable places whose value is defined
piecewise, by contributions that combine without order. A deferred collection has no history. Its
name denotes its final value, and no read observes it partly defined. Their semantics is
**deferred value semantics**, the counterpart of [Mutable Value Semantics](#mutable-value-semantics)
for places whose contributions combine without order.

| Type | Contribution | Denotes | Obligation on the contributions |
|---|---|---|---|
| `Feed(𝑇)` | `f << v` appends `v` | The union of its contributions, each keyed by the positions of the loops around its `<<` ([spec 3.7](../../../docs/chl-spec.md#37-feed-operator-)) | None |
| `OnceMap(𝐾, 𝑉)` | `m[k] = v` defines `k` | A total map `𝐾 ⤇ 𝑉` | Each key of `𝐾` defined exactly once |

```python
out: Feed(Int)
for x in [1, 2, 3]:
    out << x * 10
total = sum(out)                          # 60
```

`f <<= xs` defines a feed outright as the value `xs`
([spec 4.4](../../../docs/chl-spec.md#44-define-statement-)).

### Contributions

- **A `OnceMap` entry is a definition.** `m[k] = v` is written with `=`, because nothing is
  overwritten. A `OnceMap` has no `:=`.
- **Each key is defined at most once.** This is a refinement obligation. A key that is distinct by
  construction discharges it, such as the key of the enclosing loop's position, or the key of a
  source that declares its keys distinct. A definition whose obligation is not proved is a type
  error, not a runtime failure ([Principles](#principles), 5).
- **Every key is defined.** A `OnceMap(𝐾, 𝑉)` is total over `𝐾`, so a lookup `m[k]` has type `𝑉`,
  not `Option(𝑉)`. The compiler proves totality from the declaring scope's own code: a loop over a
  source of the keys of `𝐾` that defines `m[k]` on every path through its body. A function that the
  program may call any number of times, or never, does not establish totality.
- **Neither type has a contribution that removes or replaces.** A program that needs one uses a
  `Mut` or a cell holding a `Map` or a `List`. An entry defined once by a transaction, such as an
  idempotent charge, is a cell holding a `Map`, written under an `if id not in receipts.keys():`
  guard.

### Totality and transactions

A contribution inside a `with begin():` block happens only if the block commits
([Transaction outcomes](#transaction-outcomes)). A `OnceMap` definition inside a block is therefore
partial, and it does not count toward totality. The program defines the entry outside the block,
from the block's value:

```python
for k ↦ req in srv::reqs:
    v = with begin():
        reserve(req.body.sku, req.body.qty)
    resps[k] = to_response(v)             # defined on every path through the block
```

Every path through a block in value position commits, a deny path included, so the definition
after the block runs on every path. A block that may raise needs a `try` around it, as in
[Transaction outcomes](#transaction-outcomes), for the definition to be total.

A feed has no totality obligation. An append inside a block is a contribution only if the block
commits ([Transaction boundaries](#transaction-boundaries)).

### Which contributions participate

The program text determines the contributions that define a deferred collection:

- the `<<` and `=` contributions in its declaring scope;
- the contributions in a function to which the declaring scope lends the collection, `hungry(&f)`,
  for the duration of that call;
- the contributions in a `def` in the declaring module that captures the collection.

The third case departs from rule 2 of [The rules](#the-rules). That rule forbids a `def` from
writing a captured `Mut`, because the write would have no position in its caller's history. A
contribution to a deferred collection needs no position, and its site is still in the declaring
module. The contributions of different calls to such a `def` are keyed by call site, as a feed with
contributions from several sites is a `Copair` tagged by its sites (`src/ccl/design/sites.md`,
"Channel tags").

Nothing else contributes to a deferred collection. Every use of it as a value copies its final value
([Values, Places, and Variables](#values-places-and-variables)), so a function that returns one
returns that value, and no caller contributes to a collection a callee returned. A deferred
collection has no move. A move would make the participating contributions depend on where the move
falls among them, and the contributions have no positions to order them by.

Two borrowers of one deferred collection are not ordered. `hungry(&f)` called twice runs both
calls concurrently, because their contributions commute in a feed and do not overlap in a
`OnceMap`. Two borrowers of one `Mut` are sequenced. The `&` marker is the same for both; the
merge law decides the ordering.

### Reads

- **A pointwise read waits for its point.** `m[k]` completes once `k` is defined, before the rest
  of the map is. This is the read of an I-structure (Arvind, Nikhil & Pingali, TOPLAS 1989).
- **A read of the whole collection waits until it is complete.** `sum(f)`, `len(m)` and a scan
  complete once every contribution has been made. A deferred collection whose contributors never
  finish has no complete value, and such a read never completes. The compiler does not reject it:
  termination checking is future work ([Termination checking](#termination-checking)).
- **A read does not depend on its position.** `g = f` gives `f`'s final value even where the
  assignment stands above some of `f`'s contributions. A read of the whole collection inside a loop
  that contributes to it would make the collection depend on itself, and it is rejected.
- **Elements are delivered before completion.** An element of the final value is delivered to
  consumers once it is contributed. Which consumers produce output before completion is a property
  of the operational semantics (`docs/operational-semantics/`), and types do not record it.

A deferred collection is not a queue. It has no operation that consumes an element, peeks at one,
or counts the elements not yet processed. A queue that one loop fills and another drains is a cell
holding a list.

Both merge laws are instances of LVars (Kuper & Newton, FHPC 2013): contributions are joins in a
lattice, and a pointwise read is a threshold read. Other lattices are future work ([Other merge
laws](#other-merge-laws)).

## Crossing between dataflow and transactions

**Dataflow** is the computation outside every transaction: comprehensions, loops and reads of
deferred collections over immutable data, ordered only by data dependence. A value whose parts are
never overwritten, such as a source, a comprehension result, a deferred collection or a history's
final value, is immutable data, and time does not appear in its type. A source's elements arrive
over time, and the run records each arrival in its observation log
([`docs/durability.md`](../../../docs/durability.md#the-observation-log)), but no element is
replaced. A `Mut` or a cell has a history of overwrites, and a read of it names a position. Each
crossing between dataflow and a transaction has one form:

| From | To | Form |
|---|---|---|
| A value | A transaction | Read as plain data. A read of the whole value waits until the value is complete. |
| A source or a deferred collection, arriving over time | A transaction, as of the transaction's version | A loop writes each element into a cell in a transaction; transactions read the cell |
| A transaction | A deferred collection | An append inside the block, delivered on commit, or a definition outside the block from the block's value |
| A `Mut` | Dataflow | The trailing read after its loop |
| A cell | Dataflow | `await_final`, or a transaction's result |
| A cell's committed versions | Dataflow | `history(𝑥)`, a feed keyed by commit position |
| A cell's committed versions | Later transactions, in any realm | A deferred materialized view ([Deferred materialized views](#deferred-materialized-views)) |

A transaction that reads a source or a deferred collection directly reads the whole collection and
waits for it to be complete. The second row is the form that reads arriving elements as of a
version:

```python
arrivals: Cell(List(Req)) := []
for r in reqs:
    with begin():
        arrivals := arrivals ++ [r]
```

The loop also keeps realms independent. A collection carries no commit order. Each realm that reads
it orders its elements by the commits of its own loop.

### history and await_final

`history(𝑥)` on a cell `𝑥: Cell(𝑉, 𝑅)`, named directly or through a `Ref`, is a feed with one
element per commit that writes `𝑥`: the content `𝑥` holds after that commit, keyed by the commit's
position in `Txn(𝑅)`. It is the cell's history (`src/ccl/design/mutability.md`, "The model:
histories and causal recursion") as a value, and the cell's change log, which a deferred
materialized view consumes, deriving each change from two consecutive elements. It is a value, so it
is read outside any transaction, and its elements are delivered as the commits happen.
`await_final(𝑥)` is its last element. Both accept a `Ref`. A loop that reads either is a consumer of
the cell and keeps it alive ([Types](#types)).

Only a cell has `history`. A deferred collection's contributions have no order, and a history of one
would make the engine order contributors that otherwise run in parallel.

`history(𝑥)` is complete only when no transaction can write `𝑥` again, at the end of the run, so a
transaction that reads it as plain data waits for the run to end, and a join against it runs in
dataflow. Aligning a deferred materialized view's result with `history(𝑥)` is such a join: the
elements keyed at or before the result's `source_version`.

The join is a dataflow operation over a feed keyed by `Txn(𝑅)` and a position `𝑝` in `Txn(𝑅)`. It
yields the elements keyed at or before `𝑝`, and it completes once delivery of the feed has passed
`𝑝`, before the run ends. To detect that, the engine delivers `history(𝑥)` in commit order or
carries the latest delivered position with it. The operational semantics needs a completion rule
for this prefix of a deferred collection.

A deferred materialized view whose sources the program writes only by appending receives only
insertions. If its definition is monotone, DBSP maintains it without retractions. The compiler
infers append-only writes from the whole program. The inference changes only how maintenance runs,
so a reload that adds another kind of write changes performance and not meaning (principle 4).

### Sinks

A sink consumes a collection that the program defines, and it takes that collection as an argument.
A source and a sink that are paired, such as an HTTP route, are one run of a module. The module
exports the source as a member, the key type of the source as a type, and a function that takes
the sink's collection:

```python
run http::serve("8080", "POST", "/order") as srv
resps: OnceMap(srv::Reqs, srv::Response)
for k ↦ req in srv::reqs:
    v = with begin():
        reserve(req.body.sku, req.body.qty)
    resps[k] = to_response(v)
srv::respond(resps)
```

- **Every request gets a response.** `srv::respond` takes a `FullMap(srv::Reqs, srv::Response)`, so
  the call is where `resps` must be total, and `respond` sends each entry once it is defined. The
  proof of totality is in the caller's code, and `http::serve` needs none. A response escapes only
  once the observations it depends on are durable
  ([`docs/durability.md`](../../../docs/durability.md#escape)).
- **The module provides the key type.** `srv::Reqs` is the domain of `srv::reqs`, so the program
  declares `resps` over it with no refinement of its own.
- **`respond` declares its dependencies.** Consuming `resps` never feeds `srv::reqs`. That fact
  makes the definition of `resps` from `srv::reqs` well-founded, and the program's own code needs
  no causality check across calls.
- **The module's feeds stay inside it.** `http::serve` may connect `respond`'s argument to its sink
  through a feed of its own. Whole-program compilation joins each module's feeds into one dataflow.
- **A sink never hands its caller a collection to fill.** A callee that returns a deferred
  collection returns its final value ([Which contributions
  participate](#which-contributions-participate)), so no information flows back through a return.

## Modules and deferred collections

A module exports values as members and takes input through functions:

- **A module exports values, never places.** A place variable is never public ([Values, Places,
  and Variables](#values-places-and-variables)). A module that defines a deferred collection
  exports its final value, `pub output = out`, or exports the value directly when no out-of-order
  definition is needed. Another module reads it through a qualified reference, `bob::output`. No
  module contributes to another module's deferred collection or writes its cells, except by
  calling its functions.
- **A module takes input through a function.** A function such as `receive` loops over its argument
  and writes its own module's cells. Its `requires` and `causes` clauses name those writes.
- **Wiring is a call below the runs.** A `run` statement's arguments name only runs above it, so
  two runs cannot each be passed the other's output ([spec 9.3](../../../docs/chl-spec.md#93-runs)).
  A call below both runs passes each its peer's output, with no cycle between runs and no `rec`
  ([spec 9.11](../../../docs/chl-spec.md#911-the-module-graph)).

```python
# agent.cambra
prompts: _                            # the run's own source

pub output = [stuff(m) for m in prompts]

pub def receive(input):
    for i in input:
        do_recv(i)                    # writes the run's cells

# root.cambra
run agent as alice
run agent as bob
alice::receive(bob::output)
bob::receive(alice::output)
```

- **The cycle between the two runs goes through their cells.** `do_recv` writes a run's cells in
  transactions, and `stuff` reads them in later transactions, so no value depends on itself. If
  `receive` contributed to `output` directly, `alice::output` would depend on `bob::output` and the
  reverse. That cycle of values is well-founded only where each element depends on earlier
  elements, which needs a causality check across calls.
- **A call that starts a loop returns at once.** Its loop runs for as long as its input does, as the
  loop in spec 3.7's `fanout` does.
- **`receive` may be called any number of times.** Each call is a loop over its own input. A call
  that never happens leaves `alice` with no input from that peer.
- **Modules are not records.** A run bundles cells and logic under one name. Its outputs are
  members, and its inputs are functions.
- **A wiring call is a statement.** `receive` causes effects, so a call to it is not a bare value
  expression, and [spec 9.17](../../../docs/chl-spec.md#917-no-trailing-expressions) admits it at
  a module's top level.

## Four kinds of reference

A borrow is not a value, and it ends with its call ([Values, Places, and
Variables](#values-places-and-variables)). The other three are reference values, which can be stored
in data and outlive the code that made them.

### Comparison

| | Borrow, `&x` | `Ref(𝑉)` | Validated key | Unvalidated key |
|---|---|---|---|---|
| Representation | None: not a value | Opaque | Transparent, with a proof in the type | Transparent |
| Holders | One callee, for one call | Internal, and every one is typed | Internal, in cells the compiler knows | External, unknowable |
| Deletion | None: the place outlives the borrow | The collector, by reference counting | The program, proved safe | The program, unchecked |
| Version-indexed | No | No | Yes | No |
| Dereference | Always succeeds | Always succeeds | Always succeeds | A guard or `resolve`, which can fail |
| Classic analogue | Hylo's `inout`; Rust's `&mut` without lifetimes | Managed reference | Foreign key with `ON DELETE RESTRICT`, checked at compile time | Manual memory management |

A database checks foreign keys at run time. The validated key is the new form: at each deletion,
the compiler proves that no dependent holds the key, or the program writes the check.

The running example in this section:

```python
items: Cell(Map(Int, Item)) := Map::empty
type ItemKey requires Transaction = {Int where _ in items.keys()}

type Cart requires Transaction = {lines: List(ItemKey)}
carts: Cell(Map(Int, Cart)) := Map::empty
type CartKey requires Transaction = {Int where _ in carts.keys()}
```

`carts` is a dependent of `items` through the key set `items.keys()`.

### Validated keys

1. **In a cell's content type, a refinement is an invariant.** `Cell` supplies every committed
   version, so every `ItemKey` in `carts` is in `items` in every committed version. A key read from
   `carts` is valid at the version that last wrote `carts`, and rule 3 carries it to later
   versions. Before the transaction writes `carts`, that version is the committed one.
2. **Elsewhere, a refinement holds at the current version of the transaction.** A guard
   `if k in items.keys():` refines `k` to `ItemKey`, as any guard refines.
3. **A write to a key set re-checks later uses.** An insert preserves every key. A remove of `𝑗`
   requires `𝑘 ≠ 𝑗` at each later use of a key `𝑘`. z3 decides each obligation from the version
   chain.
4. **A key leaves the transaction only through an explicit cast to its base type**, as in
   [Leaving a transaction](#leaving-a-transaction).
5. **A refinement may mention only cells of its own module.** Every dependent of a key set is then
   visible to the module that owns it. Adding a module never makes another module's deletions
   fail. A key that crosses a module boundary is an unvalidated key. A module parameter is never a
   cell: a run passes a cell to another module as a `Ref`. A refinement therefore never mentions a
   cell its module received, and the rule covers child modules.

Removing `𝑗` from a key set narrows `ItemKey`, and every dependent must hold no `𝑗` at the commit
point. [Invariants over cell contents](#invariants-over-cell-contents) states that obligation, the
writes that create one, and the four ways to discharge it. Overwriting the value under an existing
key changes no key set and creates no obligation.

### Concurrency

A transaction that holds a validated key read the entry that justified it: either the key's
membership in the key set, or a dependent entry containing the key. That read is in its footprint.
A concurrent deletion must write one of those entries, because restrict requires removing every
reference first, so the two transactions conflict. Validated keys add no conflict checks beyond
the reads that justified them.

### Ref as a key into an implicit map

Each allocation site `𝜌` has an implicit cell keyed by an abstract type `Addr_𝜌`, which has no
constructor and no order:

```text
heap_ρ : Cell(Map(Addr_ρ, V))
Ref(V) = Σ (ρ : Sites(V)). {a : Addr_ρ | a ∈ dom(heap_ρ)}
Ref::new(v) = insert v at a fresh Addr_ρ
*r          = heap_ρ[r]            r->f := v  is  heap_ρ[r].f := v
```

A `Ref`'s deletion policy differs from a validated key's in which holders it counts. A validated
key counts references in committed dependent cells, and the program deletes once the obligation is
discharged (restrict). A `Ref` counts every holder, in cells, in locals and in values held outside
any transaction, and the collector deletes (collect). A `Ref` can be held outside a transaction
and a later transaction must still reach its cell, so every holder counts; counting every holder is
decidable only if the holders are exactly the `Ref`-typed values, which requires that `Addr_𝜌`
cannot be built from data. The collector is what collect adds over restrict: it finds holders
outside cells.

Consequences:

- **One footprint system.** The per-site, per-path requirements and effects in [Footprints are
  requirements and effects](#footprints-are-requirements-and-effects) are per-key requirements and
  effects on `heap_𝜌`.
- **A collected map cannot be enumerable.** Iterating `heap_𝜌` would hand out keys from the map
  itself, so every entry would stay reachable. A program-declared map with the collect policy is
  possible only if its keys are minted by `Ref::new` and it has no `keys()` or iteration.
- **A `Ref` leaves a transaction only if the transaction commits.** An aborted transaction
  delivers no result. A later transaction sees the allocation by real-time order.

### Unvalidated keys

An unvalidated key is an `Int` or other plain data naming a row, or a `Pin(𝑉)` naming an
allocated cell. A guard validates it at the current version: `if k in items.keys():` for a row,
`resolve(p)` for a pin. `resolve` returns an `Option` because the key may name nothing.

The holders of an unvalidated key are outside the program, so the collector cannot see them. A
program that hands a reference to an allocated cell to the outside world roots the cell itself:
`pin` adds the cell to a root set of `heap_𝜌`, and `unpin` removes it. A key to a row in a
program-declared map needs no pin, because only the program removes rows.

### References to substructure

A `Ref` points at a whole cell. An element of a cell's collection is a place, a projection of the
cell, but no `Ref` points at it. Each need for a reference to substructure is met by an
existing form:

| Need | Form | What it gives |
|---|---|---|
| Access for the duration of one call | Lend the path to a `Mut` parameter: `f(&xs[i])` | A borrow that ends with the call (see [The rules](#the-rules)). For a cell reached through a `Ref`, the path crosses with `->`, `f(&r->xs[i])`, inside a transaction. |
| A durable reference whose target the program deletes | `Cell(Map(𝐾, 𝑇))` and a validated key `{𝐾 where _ in xs.keys()}` | A transparent key, valid within one transaction, under restrict |
| A durable, opaque reference that the collector manages | Allocate each element as its own cell: `Cell(List(Ref(𝑇)))` | A `Ref(𝑇)` that keeps its element alive, at the cost of an edge in the type graph of cells |

An opaque reference that pairs a container's `Ref` with a path does not exist. Two facts rule it
out:

- **A position does not follow its element.** After an insert at the front, `xs[3]` names a
  different element; after `xs[0] := xs[1]`, no element is the one the reference meant. A key into a
  `Map` is a stable position, which is the validated-key row above.
- **The entry can be deleted while the reference is held.** Holding the pair keeps the container
  alive, not the entry. Restricting the entry's deletion makes the reference valid only within the
  transaction that checked it, a validated key; having the collector keep the entry alive manages
  it apart from its container, a separately allocated cell.

A program that wants the pair writes the record `{map: Ref(Map(𝐾, 𝑇)), key: 𝐾}` and validates
the key with a guard in each transaction.

## Invariants over cell contents

A refinement in a cell's content type is an invariant over every committed version, because `Cell`
supplies every committed version to its content type. Any write to a cell that the refinement
reads can break it. Removing a key from a key set, which breaks every dependent that still holds
the key, is one case of the rule below.

### The obligation

- **Read set.** The read set of a version-indexed type is the cells its definition reads.
  `ItemKey` reads `items`.
- **Dependents.** The dependents of a cell `𝑑` are the cells whose content types mention a
  version-indexed type whose read set contains `𝑑`. `carts` is a dependent of `items`.
- **The rule.** A write to `𝑑` produces a version `𝜏′`. Each dependent's content at `𝜏′` must
  inhabit its content type instantiated at `𝜏′`.

A write to a dependent has no additional obligation: the value written is typed at the current
version, as any value is. A dependent that may violate its type at `𝜏′` is a type error that names
the dependent and the position: after `items.remove(k)`, "`carts` may contain `k` in `lines`".

### Which writes create an obligation

Whether a write to `𝑑` can break a dependent depends on how a version-indexed type `𝑇` occurs in the
dependent's content type, and on whether the write narrows or widens `𝑇`:

| Occurrence                                                | Example                                                            | Writes that create an obligation                                   |
| --------------------------------------------------------- | ------------------------------------------------------------------ | ------------------------------------------------------------------ |
| Covariant: the dependent holds values of `𝑇`              | `List(ItemKey)`, the keys of a `Map(K, V)`                         | A write that narrows `𝑇`, such as a remove from the key set |
| Contravariant: the dependent accepts values of `𝑇`        | A stored function of type `(k: UserKey) ⇒ 𝑇 requires Transaction` | A write that widens `𝑇`, such as an insert                  |
| Invariant: the dependent's type is exactly `𝑇`            | `FullMap(UserKey, 𝑇)`, whose domain is every `UserKey`            | Every write that changes `𝑇`                                |

Whether a write narrows or widens `𝑇` is a comparison of two instances, `𝑇@𝜏′ ⊆ 𝑇@𝜏` or `𝑇@𝜏 ⊆
𝑇@𝜏′`. Membership in a key set is monotone in the set, so an insert widens and a remove narrows with
no solver query. Other predicates go to z3 ([Classifying writes](#classifying-writes)). A write
the compiler cannot classify creates an obligation for every occurrence. A write that changes no
instance, such as overwriting the value under an existing key, creates none.

### Examples

**A total map over a key set.** Every user has preferences:

```python
users: Cell(Set(Int)) := Set::empty
type UserKey requires Transaction = {Int where _ in users}
prefs: Cell(FullMap(UserKey, Prefs)) := …

with begin():
    users.add(u)                # widens UserKey: prefs needs a row for u
    prefs[u] := default_prefs   # supplies it

with begin():
    users.remove(u)             # narrows UserKey: prefs must drop u's row
    prefs.remove(u)             # drops it
```

Adding a user obligates `prefs` to gain a row, and removing one obligates `prefs` to lose it. In
both transactions the version between the two writes violates the invariant whichever write comes
first, and both typecheck because obligations are checked at the commit point.

**A bound held in a cell.** Every expense fits the current budget:

```python
budget: Cell(Int) := 1000
type Spend requires Transaction = {Int where _ <= budget}
expenses: Cell(List(Spend)) := []
```

Raising `budget` widens `Spend` and creates no obligation for `expenses`, a covariant occurrence.
Lowering it to `𝑏` obligates every expense to be at most `𝑏`. A guard over an in-transaction
materialized view of the largest expense discharges it.

### Discharge

An obligation is discharged by the commit point of the transaction that creates it, in one of four
ways. Each is written by the program or proved, and an obligation none discharges is a type error.

- **A compensating write.** The new `prefs` row above, or a cascade. A filtering comprehension
  gives each element the type `{ItemKey | _ != k}`, so the new value of `carts` typechecks at the
  new instance with no quantified reasoning:
  ```python
  with begin():
      carts := map([c ↦ Cart::new(lines=[i for i in cart.lines if i != k]) for c ↦ cart in carts])
      items.remove(k)
  ```
- **A guard.** A key-position dependent needs one lookup: `if k not in carts.keys():`. A
  value-position dependent needs a scan:
  `if sum(1 for cart in carts.values() if k in cart.lines) == 0:`. A scan's footprint is the whole
  dependent, so it conflicts with every concurrent writer to `carts`.
- **The version chain alone.** For example, the transaction has just removed the only entry that
  could hold `k`.
- **A lookup in an index.** An in-transaction materialized view whose definition entails that an
  absent key means no occurrence ([Indexes](#indexes)).

A materialized view is not a dependent. An in-transaction materialized view's value at `𝜏′` is its
definition applied to the sources at `𝜏′`, which typechecks by construction. A deferred materialized
view holds its definition at `src(𝜏′)`, which also typechecks by construction
([Deferred materialized views](#deferred-materialized-views)).

### When obligations are checked

Obligations on cell contents are checked at the commit point, against the transaction's last
version. A check at each write's version would reject every invariant occurrence, as the `prefs`
example shows, and deleting a reference cycle fails the same way.

Inside a transaction, a cell's content is typed like a local value. It has the type it had at the
version that last wrote it, or at the committed version if the transaction has not written it. Rule
3 of [Validated keys](#validated-keys) re-checks each use at a later version: a key read from
`carts` after `items.remove(𝑗)` needs `𝑘 ≠ 𝑗` at its use, as a local key does.

A write through `*r` may write a cell `x` when `r`'s site kind contains `x`. Unless the exclusivity
facts ([Converting a cell to a Mut](#converting-a-cell-to-a-mut)) separate such a write from `x`, it
counts as a write to `x` at an unknown path. `x`'s content returns to its declared type, and
rule 3 of [Validated keys](#validated-keys) re-checks the keys read from it earlier. Refinements
learned about `x` before the write are lost where the facts cannot separate the cells.

Between two writes, a cell's content can have a type that no signature names. In the first `prefs`
transaction, after `users.add(u)` and before `prefs[u] := default_prefs`, `prefs` is not a
`FullMap(UserKey, Prefs)` at the current version, because it has no row for `u`. A call there to a
helper that takes `p: Mut(FullMap(UserKey, Prefs))` is a type error, although the declared types
suggest it is allowed, and the error names a type the program never wrote.

The module-local rule ([Validated keys](#validated-keys), rule 5) and the concurrency argument
([Concurrency](#concurrency)) apply to every obligation unchanged.

## Footprints and elision

### Footprints are requirements and effects

A transaction's footprint is its read requirements and its write effects. As in the effects stack, a
read is a requirement, `requires ReadCell(𝑝)`, and a write is an effect, `causes WriteCell(𝑝)`. The
argument `𝑝` is a place expression, written as the access it names is written, and type-checked as
that access is: `ReadCell(carts_by_user)`, `WriteCell(items[k])`, `WriteCell(s->cart->items[sku])`.
A path has no syntax of its own. A place starts at a root cell or at a parameter in scope. `.f` and
`[k]` select a field or an entry, and `*` and `->` cross into the cell a `Ref` names ([Values,
Places, and Variables](#values-places-and-variables)). A place with no steps names the whole cell.
An access's footprint names the place the access names, so `r->f := v` has the effect
`WriteCell(r->f)`. A place the type checker rejects as an access is rejected in a footprint.

`ReadCell` and `WriteCell` replace the per-variable `ReadTxn(x)` requirement and `WriteTxn(x)`
effect of the effects stack, which cannot name an allocated cell or a key within a collection, and
cannot decide whether `xs[i]` and `xs[j]` are disjoint. A written clause follows the effects
stack's rules unchanged (its spec, "6.9 Capabilities"): in a `def` it is a lower bound that
inference extends, `only` makes it an upper bound as well, and a written function type's clauses
are exact.

A `Ref`'s type carries the allocation sites of the cells it can name, as the kind of its `Σ` binder
([Ref as a key into an implicit map](#ref-as-a-key-into-an-implicit-map)), inferred from the flow of
references. Every site in the kind allocates in the `Ref`'s realm, and a root cell `x` is its own
site. The compiler resolves each path to the sites it can reach and to the path within each. A site
variable `𝜌` appears only in the compiler's form of an effect, as `?N` does; a program never writes
one.

A cell allocated during a transaction needs no effect until it escapes: no other transaction can
hold a `Ref` to it before the commit, so its reads and writes conflict with nothing and stay out of
the footprint, and the allocation inserts a fresh key into `heap_𝜌`, which conflicts with nothing
either. The cell escapes by being returned or stored into another cell, and later effects on it
name a path through that value: the caller's binding of the return value, or the cell that holds
it, as in `WriteCell(carts_by_user[u]->items)`. Every effect a signature states therefore has a
path in scope, and a signature needs no site parameters.

### Elisions

| Elision | Condition | Effect on the engine |
|---|---|---|
| Disjointness | Two transactions' footprints are provably disjoint | No conflict check between them |
| Partitioning | Two transactions are disjoint whenever their inputs differ in a known way, such as different `req.user` | Route by key; check only within a partition |
| Commutativity | A write whose read feeds only that write, such as `balance += x` or `events := events ++ [e]` | No validation of that read |
| Deterministic scheduling | The footprint is known before execution | Order transactions without aborts, as in Calvin |

Strict serializability constrains every elision: a commutative update merged late, or a read served
from an old snapshot, can be serializable without respecting real-time order, so each elision needs
an argument for real-time order as well as for serializability.

### References read from cells

When a transaction obtains a `Ref` or a key by reading a cell, as the `adds` loop of
[Example](#example) does, its footprint's sites are known statically and its exact cells and keys
are not. Execution then needs a reconnaissance step that performs those reads first, as in Calvin's
OLLP. This is the main runtime cost of `Ref`s.

### Across modules

Every module is linked into one program before inference and planning. The planner therefore sees
every `with begin():` block that touches a cell, whichever module it is in, and elision needs no
footprint declarations in signatures. Declared footprints serve a different purpose: stability
across reloads. An elision is a proof about the whole program, and a reload that adds a write to a
shared cell can invalidate it. A module type that bounds its runs' footprints lets a reload within
those bounds keep other modules' plans ([Reloads that widen
footprints](#reloads-that-widen-footprints)).

A `Ref` that crosses a module boundary has an abstract site kind. Its effects name the run's cells
as a whole. The effects stack writes this `WriteTxn(inv::*)`, a glob over the run's variables.
That is not a place expression, and in this design `*` is the dereference of a `Ref`.

## Garbage collection

Unreachable cells, and versions no consumer can read, are eventually reclaimed. Cells are
reclaimed by reference counting. A program whose type graph of cells has a cycle is rejected, so
no cycle of cells forms and no cell is traced.

### The type graph of cells

After specialization every type is concrete. The compiler builds a graph whose nodes are
allocation sites. An edge from 𝐴 to 𝐵 means a value stored in a cell of 𝐴 can hold a `Ref` to a
cell of 𝐵. The graph is complete only if every type shows the `Ref`s its values can hold; a
closure whose captured `Ref`s did not appear in its type would add an edge the compiler cannot
see. A cell's content refers to other data in one of four ways, and only the last two are edges of
the graph:

| Kind | Example | Collector work |
|---|---|---|
| Key | A row stores a `UserId` or an `ItemKey` | None. Validated and unvalidated keys are data. |
| Containment | A row inside a cell's `Map` | None. The row is deleted when removed. |
| Counted | A `Ref(𝐵)` in 𝐴's content, with 𝐴 and 𝐵 in no cycle of the graph | A count update per `Ref` stored or removed |
| Cyclic | A `Ref(𝐵)` in 𝐴's content, with 𝐴 and 𝐵 in one strongly connected component of the graph | None: the program is rejected |

A recursive type whose cycle passes through no `Ref` adds no edge. Its values, such as an
immutable tree or DAG, are built from values that already exist, so they form no cycle and need no
tracing. Only mutable recursive structure, a cycle through `Ref`s, would need it.

### Guarantees

1. **A collection whose type contains no `Ref` is never visited by the collector.** This is decided
   from the type. A table keyed or filled by validated keys is such a collection.
2. **A write costs collector work proportional to the `Ref`s it stores or removes.** No table is
   scanned to find roots.
3. **No cell is traced.** A cycle in the type graph is a compile error that names the cycle. The
   check reads only types: `type Foo` holding a `Ref(Bar)` and `type Bar` holding a `Ref(Foo)` is
   rejected whether or not a program would link two cells.

### Cycle collection

Admitting cycles is later work. It adds cycle collection, confined to the cyclic components of the
type graph: collection starts from candidates, which are cells whose count decreased without
reaching zero, and explores only what they reach within their component (Bacon & Rajan,
"Concurrent Cycle Collection in Reference Counted Systems", 2001). Partitioning the heap by static
connectivity follows Hirzel, Diwan & Hertz, "Connectivity-Based Garbage Collection", 2003.

`@NoTrace` on a root cell or a cell type then asserts that it lies in no cyclic component. If the
type graph has a cycle through it, compilation fails with an error naming the cycle. The
annotation bounds tracing, so that no collection pass explores a large collection.

### Reference counting under transactions

- **Count updates commute.** They are blind increments and decrements, and only the collector reads
  them. They need no validation and conflict with no transaction.
- **Only references stored in cells are counted.** References held in local values or in an
  in-flight transaction are not, as in deferred reference counting (Deutsch & Bobrow). A zero
  count makes a cell a candidate, and a root scan decides.
- **Reclamation at zero is safe.** Suppose a cell's count reaches zero at commit 𝑇. A transaction
  that read a reference to it from a version before 𝑇 read it from a cell content that changed by
  𝑇. If that transaction stores the reference, its read fails validation. No reference to the cell
  can reappear after 𝑇.
- **Old versions are covered by the watermark.** The cell is reclaimed once the low watermark
  passes 𝑇, so reads of older versions still reach it. The same watermark drives removal of old
  history versions, which is the past-version case of release (see [Types](#types)).

The safety argument for reclamation depends on the read being validated. An elision cannot apply
to that read, because the transaction that removed the reference is a conflicting writer.

### Pins

A pinned cell is a root until `unpin`, or until its time-to-live passes. The collector does not
count unvalidated keys. A `Pin` whose cell has been unpinned and reclaimed resolves to `None`.

## Staging

The design lands in the steps below, in order. Each step leaves the compiler and the spec
consistent, and names the [proposed spec changes](#proposed-changes-to-the-spec-and-the-compiler)
that land with it. Work not listed here is in [Future work](#future-work).

1. **`OnceMap`.** `OnceMap(𝐾, 𝑉)` joins `Feed(𝑇)` as a deferred-collection type, on today's
   representation of feeds ([Deferred collections](#deferred-collections)). A definition
   `m[k] = v` is checked to define each key at most once, totality is proved from the declaring
   scope's code, and a lookup has type `𝑉`. `http::serve` becomes a module that is run, whose
   `respond` takes a `FullMap` ([Sinks](#sinks)). A feed loses its aliases and its moves. Spec 3.7,
   3.9, 4.4, 7.3 and 8.4 change.
2. **A foundation for places.** The compiler gains one representation of a place: a place
   variable and a path of projections from it ([Values, Places, and
   Variables](#values-places-and-variables)). The rules for place variables are checked once,
   over that representation: never stored, returned, aliased or public; a copy on use as a value;
   a borrow marked `&` in a borrowing position; a parameter's borrow mode inferred from the body.
   Today `Mut` and `Feed` are separate CCL types with separate second-class checks
   (`src/ccl/design/mutability.md`, "No aliasing: `Mut` values are second-class (downward-only)").
   1. **`Mut`, `Feed` and `OnceMap` move onto the foundation.** An argument to a place parameter
      is written `&x`, and an unmarked argument is always a copy. Two borrowers of one `Mut` are
      sequenced, and two borrowers of one deferred collection are not. A module exports values
      and no place. Spec 8.1, 9.6 and 9.7–9.9 change, and so does the worked example of
      `docs/modules.md`. Only whole place variables are lent.
   2. **Borrows of substructure.** A path is a write target, `m[k].f := v`, and a borrow lends a
      path, `swap(&xs[i], &xs[j])` ([Mutable Value Semantics](#mutable-value-semantics)).
      Exclusivity is checked per part, and the disjointness of computed indices is a z3
      obligation.
3. **`Mut(_, Txn)` becomes `Cell`.** A root cell is declared `x: Cell(𝑉) := init` and is read and
   written by name inside a transaction ([Cells](#cells)). `to_mut` is inserted only for a root
   cell named directly. Realms arrive as nominal types, with the default realm where none is
   named ([Realms](#realms)). A block may carry a deadline, which raises `GaveUp`
   ([Transaction outcomes](#transaction-outcomes)). Footprints name paths from root cells,
   `ReadCell(𝑝)` and `WriteCell(𝑝)` ([Footprints and elision](#footprints-and-elision)). Spec 8.2
   changes.
4. **`Ref`, with reference counting.** `Ref::new`, `ref(x)`, `*` and `->` reach cells allocated at
   run time, and `Pin` hands them outside the program ([Operations](#operations)). The pair arrow
   becomes `↦` first, which frees `->` (spec 2.4). The collector counts the `Ref`s stored in cells
   and scans the roots, and a cycle in the type graph of cells is a compile error ([Garbage
   collection](#garbage-collection)). Footprints name allocation sites, and a transaction that
   reads a `Ref` from a cell needs a reconnaissance step ([References read from
   cells](#references-read-from-cells)).
5. **Deferred materialized views.** `@materialize(delay=𝑡)`, in the sources' realm or another,
   maintained by DBSP after commit from `history(𝑥)` ([Deferred materialized
   views](#deferred-materialized-views)). A read at `𝜏` sees the definition at `src(𝜏)`, and
   `source_version` exposes it.
6. **In-transaction materialized views.** `@materialize` with no delay, maintained inside each
   writing transaction, and `@index` ([In-transaction materialized
   views](#in-transaction-materialized-views)). Their footprint and latency fall on the writers.

## Changes relative to the current implementation and the effects stack

| Today | This design |
|---|---|
| `Mut(𝑉, Txn)` | `Cell(𝑉, 𝑅)`, with `𝑅` the default realm when omitted |
| `Mut(𝑉, 𝐷)` with an inferred induction domain | `Mut(𝑉)` |
| Transactional variables only at a module's top level | Root cells at the top level, and cells allocated with `Ref::new` anywhere a transaction is supplied |
| A `Mut` argument written like a copy, with the call shape taken from the callee's type ([spec 9.6](../../../docs/chl-spec.md#96-qualified-references)) | `&x` at the call; an unmarked argument is always a copy |
| `to_mut` inserted wherever a `Mut` is expected and a cell or a `Ref` is given | Inserted for a root cell named directly; a `Ref` is dereferenced with `*` or `->`, never implicitly |
| `k -> v`, the pair arrow | `k ↦ v`, or the tuple `(k, v)`; `->` is the field access through a `Ref` |
| `Mut(_, Txn)` parameters | `Ref(𝑉, 𝑅)` parameters, effects on captured cells, or a cell passed to a `Mut(𝑉)` parameter through `to_mut` |
| `requires ReadTxn(x)`, `causes WriteTxn(x)` per variable | `requires ReadCell(𝑝)`, `causes WriteCell(𝑝)` per path, resolved to sites by the compiler |
| `causes Append(x)` on a feed, from any module | `causes Append(x)` only from the feed's declaring scope ([Which contributions participate](#which-contributions-participate)) |
| Footprints per variable | Footprints per site and path |
| `Mut` writes to a whole variable | Writes to paths, with exclusivity checked per part |
| Refinements over values only | Refinements may read the module's cells, through types that require a transaction |
| `requires Transaction` on functions only | Also on type declarations, as a version index |
| One commit order for the program | Realms named by nominal types, each with its own commit order; `requires Transaction(𝑅)` |
| No views | Views (functions that require a transaction); `@materialize` materialized views, maintained inside each writing transaction, or after commit with `delay=𝑡`, in its sources' realm or another |
| `Feed(𝑇)`, a history under the append merge law, which can be aliased and moved | `Feed(𝑇)`, a deferred collection with no history, no alias and no move |
| A keyed feed, `resps[req.id] = …` ([spec 7.3](../../../docs/chl-spec.md#73-sources), sketch) | `OnceMap(𝐾, 𝑉)`: `m[k] = v` defines a key once, and the map is total |
| A lookup in a feed decides absence only once the feed is complete ([spec 3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access)), or at a cut such as `o.time < now` | A loop writes the elements into a cell, and a transaction reads the cell at its version |
| A feed handle in a tuple ("A deferred collection inside a data structure [Open]") | No handle: a deferred collection is never stored, and its final value is |
| Public feeds and `Mut`s, and a public feed with contributions from other modules ([spec 9.9](../../../docs/chl-spec.md#99-running)) | No public place; a module exports values, and other modules pass input through its functions |
| A sink that returns a feed for its caller to fill | A sink that takes the collection as an argument ([Sinks](#sinks)) |
| `await_final` on a top-level `Mut(𝑉, Txn)`, named directly ([spec 8.6](../../../docs/chl-spec.md#86-await_final)) | `await_final` and `history` on a cell or a `Ref` ([history and await_final](#history-and-await_final)) |
| Transactional variables' storage never reclaimed | Parts of root cells reclaimed as their consumers release them; allocated cells reclaimed by reference counting, with cycles in the type graph rejected |

### Proposed changes to the spec and the compiler

Proposals for the owners of each part.

- **[Spec 8.1](../../../docs/chl-spec.md#81-mutation-is-explicit-the--operator) and
  [9.6](../../../docs/chl-spec.md#96-qualified-references).** An argument to a `Mut`, `Feed` or
  `OnceMap` parameter is written `&x`, and an unmarked argument is always a copy. The call shapes
  that dispatch on the callee, and their planned extension through a Module-typed parameter, are
  removed. A parameter's borrow mode is inferred from the body where it is not written. A method
  that takes `self: Mut(Self)` is called on a marked receiver, `&xs.push(v)`, where `&` binds
  tighter than `.` and `[ ]`. Prefix `&` leaves infix `&` (logical and) unchanged.
- **[Spec 2.4](../../../docs/chl-spec.md#24-atoms) and the precedence table.** The pair arrow
  becomes `↦`. `->` becomes a postfix operator beside `.`, the field access through a `Ref`, and
  prefix `*` is the dereference, binding looser than the postfix operators. A lambda keeps
  `\x -> body`.
- **[Spec 8.4](../../../docs/chl-spec.md#84-feeds-are-the-second-form-of-mutability).** "Feeds are
  the second form of mutability" becomes: a feed is a deferred collection, an immutable place with
  no history ([Deferred collections](#deferred-collections)).
- **[Spec 3.7](../../../docs/chl-spec.md#37-feed-operator-).** `fanout` takes the collection it fans
  out as a parameter and does not return a feed. "A deferred collection inside a data structure
  [Open]" is closed: a deferred collection nests in nothing, and a data structure holds its final
  value.
- **[Spec 3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access).** A lookup in a
  `OnceMap` has type `𝑉`. "Absence at a cut [Open]": a transaction's version is the cut for a
  cell's content.
- **[Spec 4.4](../../../docs/chl-spec.md#44-define-statement-).** `<<=` stays, as a contribution in
  the feed's declaring scope. Its Direction note is resolved.
- **[Spec 7.3](../../../docs/chl-spec.md#73-sources).** `http_serve` becomes a module that is run,
  `run http::serve(…) as srv`. It exports the request source `srv::reqs`, its key type `srv::Reqs`,
  a response type, and a `respond` function that takes a `FullMap` of responses, in place of a
  pair whose second half is a feed ([Sinks](#sinks)).
- **[Spec 9.7](../../../docs/chl-spec.md#97-importing-asserts-a-shareable-module),
  [9.8](../../../docs/chl-spec.md#98-module-types) and
  [9.9](../../../docs/chl-spec.md#99-running).**
  Declaring a feed still makes a module one that is run. No place variable is public: the spec's
  `pub stock: Mut(…)` and `pub counts: Feed(Int)` become values, `pub counts = …`, or functions.
  "eu and us feed one `audit::events`" no longer holds
  ([Modules and deferred collections](#modules-and-deferred-collections)).
- **[`docs/modules.md`](../../../docs/modules.md#worked-example-two-storefronts-and-an-audit-log),
  "Worked example: two storefronts and an audit log".** `storefront` exports its events as a
  value, `pub events = …`, and takes no `audit` parameter. `audit` exports a `receive` function
  that writes events into a cell, and its handler reads the cell in a transaction. The root calls
  `audit::receive(eu::events ++ us::events)` below the runs. Today's `audit` handler reads the whole
  of a live feed, so it never responds.
- **[Spec 8.2](../../../docs/chl-spec.md#a-block-is-also-the-value-it-computes), "A block is also
  the value it computes".** `with begin(deadline=𝑑):` raises `std::txn::GaveUp` when the
  transaction has not committed within `𝑑`, and a block that gives up takes a commit position with
  no writes ([Transaction outcomes](#transaction-outcomes)). A block whose result type is
  version-indexed needs an explicit cast ([Leaving a transaction](#leaving-a-transaction)); the
  check may land after the rest, with an `[Open]` marker that 1.0 removes.
- **[Spec 8.5](../../../docs/chl-spec.md#85-ordering-and-concurrency).** "Nothing is ordered by its
  position in the source text" does not hold for two loops that write one `Mut`: the second loop
  continues the first's history in statement order (`src/ccl/design/mutability.md`, the
  sequencing-domains table). `t := 0`, a loop adding `[1, 2, 3]`, then a loop multiplying by `[10,
  20]`, gives `1200`; with the loops swapped, `6`.
- **Mutability elimination.** `Feed`'s `HistoryKind::Append` and the `LetRec` groups `channelize`
  assembles stay as the implementation of feeds. The surface loses a feed's history, its aliases and
  its moves.
- **Inference.** `Feed(𝑇)` stays a variable type, no longer a mutable variable's. `OnceMap(𝐾, 𝑉)`
  joins it as the second deferred-collection type.

## Future work

The design leaves these out. Each is a candidate for a later revision.

### Validated keys

Refinements that read cells, through version-indexed types, and the obligations they put on writes
([Versions and version-indexed types](#versions-and-version-indexed-types), [Validated
keys](#validated-keys), [Invariants over cell contents](#invariants-over-cell-contents)). They
land in two parts. Module-local validated keys come first: a refinement mentions only its module's
cells, and each obligation is discharged by the commit point of the transaction that creates it,
by a compensating write, a guard, the version chain or an index, or the program is rejected. No
runtime check is inserted. Cross-module validated keys follow. A deletion can no longer see every
dependent, so the program reads a system-maintained reference count, `refs(𝑆)`, built on the
counting of staging step 4, as an explicit guard, or the deletion is rejected. The required cast
out of a transaction ([Leaving a transaction](#leaving-a-transaction)) lands with the first part.

### Tracing garbage collection

Reference counting reclaims no cell on a cycle, so staging step 4 rejects every cycle in the type
graph of cells. A tracing collector admits them. Tracing is confined to the cyclic components of the
type graph, starting from cells whose count decreased without reaching zero, and `@NoTrace` asserts
that a cell lies in no cyclic component ([Cycle collection](#cycle-collection)).

### User-defined projections

Field access `.f`, lookup `[k]` and `to_mut` (`*`) are the built-in projections: each yields a
place rather than returning a value. Programs will define projections, as Hylo's subscripts do, and
the design of the form is not written. A definition would map a place to a place, as in
`proj f_at(xs, i): xs[i].f`, used as `ys.f_at[i]` on `ys: Mut(List({f: Int}))`. A projection might
instead be a function with an effect or a capability, which would make it an ordinary function
rather than a separate concept.

### Materialized views with parameters

A view takes no parameters (`() ⇒ 𝑉 requires Transaction`), so a materialized view holds one value.
A view with parameters, such as `orders_for(u: UserId)`, could be materialized only for the
arguments that are read, as Noria does: the value for an argument is computed by an upquery on its
first read, maintained incrementally after that, and can be evicted. With it, `@materialize`
applies to functions that take parameters as well as to views, and the names for the two need
choosing.

### Termination checking

A read of the final value of a history or a deferred collection whose contributors never finish,
and a cell write of a value that is never final (`c := stdin()`), never complete. A check that
rejects them waits until the system is more mature.

### Other merge laws

Feeds and `OnceMap`s are instances of LVars: contributions are joins in a lattice, and a pointwise
read is a threshold read ([Reads](#reads)). Other laws, such as a maximum or the Z-sets of DBSP,
could join them, and a materialized view could then be a value.

### Borrowing a point of a deferred collection

`&m[k]` would lend one entry of a `OnceMap` for its callee to define, as `&xs[i]` lends one element
of a `Mut`. The parameter needs a type that `Mut` does not supply, such as `Defer(𝑉)`, a place that
holds a `𝑉` defined once:

```python
def set_to_1(v: Defer(Int)):
    v = 1

m: OnceMap(Int, Int)
set_to_1(&m[0])
```

With `Defer`, `OnceMap(𝐾, 𝑉)` could be `FullMap(𝐾, Defer(𝑉))`, and `Feed(𝑇)` could be
`_ ⤇ Defer(𝑇)`, where `_` is a domain that inference fixes per feed, neither universally quantified
nor a `Σ`. Whether the model is useful, and whether it is the right one, is not settled.

### Keys of captured contributions called from another module

A `def` that appends to a feed its module declares, called from another module, contributes at the
caller's call site ([Which contributions participate](#which-contributions-participate)). How those
keys are formed, and what a reload that adds or removes such a call does to them, is not written.

### Classifying writes

Membership in a key set is the one predicate the compiler classifies as monotone in its read set
without a solver query ([Which writes create an obligation](#which-writes-create-an-obligation)).
Built-in rules for further shapes, such as negated membership or a comparison against a numeric
cell, would replace z3 queries with checks of predictable cost.

### Declared invariants

Cell contents could carry invariants beyond refinements and views, letting the compiler check
explicit boundaries and admit more elisions (Bailis et al., VLDB 2015; Gotsman et al., POPL 2016).

### Prior work on static restrict

Branded indices (Kiselyov & Shan) and GhostCell prove validity for one collection over one scope,
without deletion against persistent dependents. A literature search for statically checked
referential integrity waits for the full design and implementation of validated keys.

### Lowering `Ref`

Native code might lower `heap_𝜌[r]` to a pointer dereference, with `Addr_𝜌` as the address and no
materialized index, under MVCC versioning of the cells.

### Reloads that widen footprints

A reload may re-plan other modules, or stay within declared footprints
([Across modules](#across-modules)). The rule is not written.

## References

The review walkthrough of this design, with the notes taken during it, is a page in Cambra's
claude.ai organization: <https://claude.ai/artifact/Fu13L3Jr1Dhn7c7ULjoqQu>.

Citations are from memory. Confirm venue and year before quoting.

- Racordon, Shabalin, Zheng, Abrahams, Saeta. "Implementation Strategies for Mutable Value
  Semantics." *Journal of Object Technology*, 2022.
- Reinking, Xie, de Moura, Leijen. "Perceus: Garbage Free Reference Counting with Reuse." PLDI
  2021.
- Bacon, Rajan. "Concurrent Cycle Collection in Reference Counted Systems." ECOOP 2001.
- Hirzel, Diwan, Hertz. "Connectivity-Based Garbage Collection." OOPSLA 2003.
- Deutsch, Bobrow. "An Efficient, Incremental, Automatic Garbage Collector." CACM 1976.
- Arvind, Nikhil, Pingali. "I-Structures: Data Structures for Parallel Computing." TOPLAS 1989.
- Kuper, Newton. "LVars: Lattice-Based Data Structures for Deterministic Parallelism." FHPC 2013.
- Budiu, McSherry, Ryzhyk, Tannen. "DBSP: Automatic Incremental View Maintenance for Rich Query
  Languages." VLDB 2023.
- Kiselyov, Shan. "Lightweight Static Capabilities." PLPV 2006.
- Yanovski, Dang, Jung, Dreyer. "GhostCell: Separating Permissions from Data in Rust." ICFP 2021.
- Thomson, Diamond, Weng, Ren, Shao, Abadi. "Calvin: Fast Distributed Transactions for
  Partitioned Database Systems." SIGMOD 2012.
- Shasha, Llirbat, Simon, Valduriez. "Transaction Chopping: Algorithms and Performance Studies."
  TODS 1995.
- Bailis, Fekete, Franklin, Ghodsi, Hellerstein, Stoica. "Coordination Avoidance in Database
  Systems." VLDB 2015.
- Gotsman, Yang, Ferreira, Najafzadeh, Shapiro. "'Cause I'm Strong Enough: Reasoning about
  Consistency Choices in Distributed Systems." POPL 2016.
- Gjengset, Schwarzkopf, Behrens, Araújo, Ek, Kohler, Kaashoek, Morris. "Noria: Dynamic,
  Partially-Stateful Data-Flow for High-Performance Web Applications." OSDI 2018.
- Warszawski, Bailis. "ACIDRain: Concurrency-Related Attacks on Database-Backed Web
  Applications." SIGMOD 2017.

