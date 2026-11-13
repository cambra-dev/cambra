# Mutability model

Status: a proposal under review. This design supersedes [mutability.md](mutability.md), which
describes the current implementation and stays until this design is reviewed and the code that
cites it is migrated. Nothing here is implemented. The effects stack in progress (`requires` and
`causes` clauses) is read as current work that this design may change, not as a fixed constraint.

## Summary

Cambra has two kinds of mutable state, and a program chooses between them by type.

- **Local state** is a `Mut(𝑉)` variable. It holds a value under Mutable Value Semantics (MVS),
  is never shared, and never needs a transaction.
- **Transactional state** is a **cell**, `Cell(𝑉, 𝑅)`: a value with an identity, in a realm
  `𝑅`. A cell is read and written only inside a `with begin():` block, and is named and passed
  around outside one.

Every transaction is strictly serializable. Static analysis never weakens isolation; it lets the
engine skip work it can prove unnecessary.

The rest of the design follows from the cell:

- A type whose definition reads a cell is a family indexed by a version, declared with `requires
  Transaction` ([Versions and version-indexed types](#versions-and-version-indexed-types)).
- A function that reads cells is a view. `@materialize` makes the system maintain its value,
  inside each writing transaction or after commit in another realm
  ([Derived state: views](#derived-state-views)).
- `Log(𝑇)` and `OnceMap(𝐾, 𝑉)` are collections whose existing elements never change. Grown
  inside a `Mut` or a `Cell`, they replace `Feed(𝑇)` ([Growing collections](#growing-collections)).
- A value refers to transactional state through an opaque `Ref(𝑉, 𝑅)`, which the collector
  manages; through a validated key, whose referential integrity the compiler checks at each
  deletion; or through an unvalidated key, which the program checks with a guard
  ([Three kinds of reference](#three-kinds-of-reference)).
- A refinement in a cell's content type is an invariant over every committed state
  ([Invariants over cell contents](#invariants-over-cell-contents)).
- A transaction's footprint is its read requirements and write effects, named per path. The
  compiler uses footprints to skip conflict checks, never to weaken isolation
  ([Footprints and elision](#footprints-and-elision)).
- Unreachable cells are garbage-collected, and the type graph of cells decides which collections
  the collector can ever visit ([Garbage collection](#garbage-collection)).

## Terms

| Term                   | Meaning                                                                                                                                                                                                                                                                 |
| ---------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **history**            | The function from positions of a sequencing domain to the value a variable holds at each position. The model in `src/ccl/design/mutability.md`, "The model: histories and causal recursion".                                                                            |
| **induction domain**   | The positions of a loop: the iteration source's keys. Local state's histories range over one.                                                                                                                                                                           |
| **realm**              | The cells and views that can interact transactionally, and their commit order, named by a nominal type with a `std::txn::Realm` instance. A program that declares none uses one unnamed default realm.                                                                                     |
| **`Txn(𝑅)`**          | The commit order of realm `𝑅`: the domain of the histories of `𝑅`'s cells. `Txn` alone means the default realm's. |
| **version**            | The content of one realm's cells at one point: a committed state, or a point inside a transaction after some of its writes. Written `𝜏`.                                                                                                                  |
| **value**              | Data with no identity. Two equal values are interchangeable.                                                                                                                                                                                                            |
| **cell**               | A unit of transactional state with an identity. Its history ranges over `Txn`.                                                                                                                                                                                          |
| **allocation site**    | The `Ref::new` expression that allocated a cell, or the declaration of a top-level cell.                                                                                                                                                                                     |
| **type family**        | A type declared with `requires Transaction`: one type per version, written `𝑇@𝜏` when the version matters.                                                                                                                                                            |
| **key set**            | The keys of a cell's collection, used to refine a key type, such as `users` in `{Int where _ in users}`.                                                                                                                                                                |
| **dependent**          | A cell whose content type mentions a type family whose definition reads another cell. `carts`, whose rows hold `ItemKey`s, is a dependent of `items`.                                                                                                                    |
| **view**               | A function `() ⇒ 𝑉 requires Transaction` whose definition reads cells. It needs no maintenance machinery.                                                                                                                                                              |
| **materialized view**  | A view marked `@materialize`, whose value the system maintains eagerly and incrementally. An **in-transaction materialized view** is maintained inside each writing transaction. A **deferred materialized view** (`@materialize(realm=𝑅, delay=𝑡)`) is maintained after commit in realm `𝑅`. |
| **growing collection** | A `Log(𝑇)` or a `OnceMap(𝐾, 𝑉)`: a collection whose existing elements never change. See [Growing collections](#growing-collections).                                                                                                                                       |
| **footprint**          | The cells, and the parts of cells, that a transaction reads and writes.                                                                                                                                                                                                 |
| **conflict check**     | Runtime validation that a transaction's reads were not invalidated by a concurrent commit.                                                                                                                                                                              |
| **elision**            | Skipping a conflict check the compiler has proven unnecessary.                                                                                                                                                                                                          |

## Principles

1. **Isolation is fixed.** Every transaction is strictly serializable. A program that gives up a
   static guarantee gets runtime conflict checks, never weaker isolation.
2. **A variable is a history.** The model holds only when a write changes exactly one history.
   Local state satisfies this because it has no aliases. Cells satisfy it because each cell is one
   history, named by its identity rather than by a variable.
3. **Identity exists only in cells.** Sharing state between concurrent computations, storing a
   reference in data, and returning a reference all require identity. A program that needs any of
   these uses a cell.
4. **Static knowledge buys performance, not semantics.** Footprints, commutativity and the type
   graph of cells let the engine skip conflict checks and collector work. The result is the same
   with or without them.
5. **Integrity checks are explicit or proved.** The compiler never inserts a runtime check that
   can fail a transaction. A deletion that could leave a validated key dangling is either proved
   safe or guarded by a check the program writes.

## Local state: Mutable Value Semantics

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
   `swap(xs[i], xs[j])` is legal only where `xs[i]` and `xs[j]` are disjoint.

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

swap(xs[i], xs[j])                        # accepted only where i != j is provable
```

### Parameter conventions

| Convention | Hylo | Cambra | Native code |
|---|---|---|---|
| Read-only borrow | `let` | plain parameter | pointer, no copy |
| Exclusive mutable borrow | `inout` | `Mut(𝑉)` parameter | pointer, no copy |
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

### What local state cannot express

Shared mutable graphs, back-pointers and callbacks that mutate shared state. In Cambra each is
either a structure of cells linked by `Ref`s, or a table whose rows hold keys.

## Transactional state: cells

### Types

| Type | What it is | Copyable and storable | Lifetime |
|---|---|---|---|
| `Cell(𝑉, 𝑅)` | A cell declared at a module's top level: `x: Cell(𝑉, 𝑅) := init`. A **root cell**; each run of the module has its own. | The variable is not; `ref(x)` gives a `Ref` | Until every consumer releases it |
| `Ref(𝑉, 𝑅)` | An opaque reference to a cell | Yes | Keeps its cell alive |
| `Pin(𝑉, 𝑅)` | A transparent key to an allocated cell, for identities that leave the program | Yes, and serializable | Until `unpin` |

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
| A prefix of a `Log` | Every consumer has read past it |
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
to_mut(r: Ref(V, R)) => Mut(V)         requires Transaction(R)   # also on a Cell; spelled *r
r == s                                                           # identity equality; hashable
pin(r: Ref(V, R)) => Pin(V, R)               requires Transaction(R)
unpin(p: Pin(V, R))                          requires Transaction(R)
resolve(p: Pin(V, R)) => Option(Ref(V, R))   requires Transaction(R)
```

- **`Ref::new` requires a transaction**, so a cell's creation is part of a commit. The cell's
  identity is derived from its allocation site and the position where `Ref::new` runs, so
  allocation never conflicts.
- **`Ref` has equality and hashing but no order.** An order would expose allocation order.
- **A cell's content is read and written through `to_mut`** ([Converting a cell to a
  Mut](#converting-a-cell-to-a-mut)). A root cell is also read and written by name.

### Converting a cell to a Mut

`to_mut` yields a cell's content as a `Mut`. It accepts a cell or a `Ref` and requires a
transaction in the cell's realm. `*` is its operator spelling, as `+` is `add`'s.

`to_mut` is a projection, not an ordinary function. Rule 2 of [The rules](#the-rules) forbids a
function from returning a `Mut`; a projection yields a second-class `Mut` that lasts as long as the
access, as a Hylo subscript yields an `inout` projection. The result is read, written and passed to
`Mut` parameters, and is never stored, returned or used outside the transaction that produced it.
The `Ref` operations follow from it:

| Form | Meaning |
|---|---|
| `v = *r` | Copies the cell's content: a snapshot, by rule 1 of [The rules](#the-rules), which later writes to the cell do not change |
| `*r := v` | Writes the whole cell |
| `r.f`, `r.xs[k]` | `(*r).f`, `(*r).xs[k]`: a `Ref` has no fields, so a step through it converts it |
| `r.f := v`, `r.xs[k] += 1` | Writes a part, through `(*r).f` and `(*r).xs[k]` |
| `r == s` | Compares identities. A `Ref` in a value position is not converted. |

`to_mut(𝑥)` holds the cell's content at the transaction's current version. A write to it, or to a
path within it, produces the transaction's next version, and the cell receives the write when the
transaction commits ([Transaction boundaries](#transaction-boundaries)).

The conversion is implicit. Where a `Mut` is expected and a `Cell` or a `Ref` is given, the
compiler inserts `to_mut`: in a read or write by name (`x := v`, `x << v`), in a write through a
`Ref` (`r.f := v`), and in an argument to a `Mut(𝑉)` parameter. `tally(counts, order)` with
`counts: Cell(Map(Sku, Int))` is `tally(to_mut(counts), order)`.

Rule 4 of [The rules](#the-rules), exclusivity, applies to `Mut`s that come from cells. A local
`Mut` and a cell's `Mut` never overlap, because a local value has no identity and no cell can name
it. Two cells' `Mut`s overlap when they can name the same cell and their paths within that cell
overlap. The compiler proves them disjoint from:

| Fact | Example |
|---|---|
| Two root cells with different names are different cells | `swap(x, y)` |
| Two `Ref`s, or a `Ref` and a root cell, whose site kinds share no site, name different cells. `ref(𝑥)` has `𝑥` as its site. | `swap(x, *ref(y))` is accepted; `swap(x, *ref(x))` is rejected |
| A refinement establishes that two `Ref`s differ | `swap(*r, *s)` inside `if r != s:` |
| Two paths within one cell are disjoint, as for local values | `swap(r.xs[i], r.xs[j])` where `i != j` is provable |

A program whose disjointness the compiler cannot prove is rejected until it writes the check, such
as `if r != s:` around the call. The compiler never inserts it (principle 5).

### When a transaction is required

| Operation | Requires a transaction |
|---|---|
| Reading or writing a `Mut(𝑉)` variable | No |
| Holding or passing a `Cell(𝑉)`, `Ref(𝑉)` or `Pin(𝑉)` | No |
| Reading or writing a cell, through its name, a `Ref` or `to_mut` | Yes, in the realm its type names |
| Reading a view | Yes, in the view's realm; see [Derived state: views](#derived-state-views) |
| Holding a value whose type is a type family, such as a `UserKey` | Yes; see [Types that require a transaction](#types-that-require-a-transaction) |

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
                s.cart.items[req.sku] += req.qty
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

Every transaction is an explicit `with begin():` block. Implicit transactions, such as a single
statement outside a block running as its own transaction, are set aside until programs show many
single-statement blocks (question 1).

Inside a block, a cell is read and written through `to_mut`, and a `Mut` declared outside the block
is read and written as a `Mut`. The block reads its own writes. Nothing outside the block sees them
before the commit: another transaction sees a cell's new content at the commit's version, and the
enclosing loop sees a write to an outer `Mut` at that loop step. A denied or aborted transaction
leaves no write. A reply appended inside a block to the enclosing loop's `Mut(Log(𝑇))` is therefore
delivered only on commit, which is the gating [spec
8.4](../../../docs/chl-spec.md#84-feeds-are-the-second-form-of-mutability) states for a reply fed
inside `with begin():`.

### Transaction outcomes

A `with begin():` block in value position yields its outcome, a variant. This resolves the spec's
Direction "a block is also the value it computes"
([spec 8.2](../../../docs/chl-spec.md#82-transactions-with-begin)):

| Outcome | Cause | Writes | Determined by the snapshot |
|---|---|---|---|
| `` `commit(𝑣) `` | The block committed; `𝑣` is the value of its last statement | All of the block's | Yes |
| `` `aborted(𝑒) `` | The block called `abort(𝑒)`, or a guard denied it (the deny idiom), with `𝑒 = unit` | None | Yes |
| `` `gave_up `` | The transaction did not commit before the block's deadline | None | No: it depends on load and time |

```python
outcome = with begin(deadline=time::millis(50)):
    reserve(sku, qty)
match outcome:
    case `commit(v):  http.ok(v)
    case `aborted(e): http.conflict(e)
    case `gave_up:    http.unavailable()
```

- **Conflict retries are internal to the engine.** A program observes one outcome per block and
  never the attempts behind it.
- **The engine guarantees progress.** After a bounded number of optimistic failures it runs the
  transaction against its footprint, which is known before execution
  ([Footprints and elision](#footprints-and-elision)), so the transaction cannot conflict again. No
  program needs a retry limit to terminate.
- **A deadline sheds load.** `with begin(deadline=𝑑):` yields `` `gave_up `` when the transaction
  has not committed within `𝑑`. The limit is a duration, not an attempt count, because the number of
  attempts depends on the engine's strategy.
- **A block with a deadline requires `ObserveWorld`.** Its outcome depends on load and time, as a
  read of the clock does, and the requirement shows that in its signature. This assumes the effects
  stack's `ObserveWorld` covers it.
- **No write survives an abort.** Writes to cells and to outer `Mut`s stay gated on commit. A retry
  policy is ordinary code outside the block: it counts outcomes in its own `Mut` and passes the
  attempt number into the body as an argument. A policy that needs data from a failed attempt gets
  it from the payload of `abort(𝑒)`.
- **Isolation is unchanged.** An aborted block and a block that gave up write nothing, so no other
  transaction can tell them apart from a transaction that never ran.

### Realms

A realm is a nominal type with an instance of the marker trait `std::txn::Realm`. A program that
declares none has one unnamed default realm:

```python
type Analytics = {}
instance std::txn::Realm(Analytics)

with begin(Analytics):
    ...
```

- **A realm's identity is its type's.** A nominal type is identified by its declaring module's
  path, its name and its implicit arguments (`src/ccl/design/nominal-types.md`), so a realm keeps
  its identity across reloads. `requires Transaction(𝑅)` takes a type, so a transaction's realm is
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
  reads.

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

A type whose definition reads a cell is declared with `requires Transaction`. It is a family of
types, one per version:

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

### Family-kinded parameters

A type family can be passed unapplied where the expected kind is itself a family:

```python
def eg(Fam: Type requires Transaction, v: Fam) => R requires Transaction
```

`v: Fam` is an application, so `eg` needs its own clause. `Cell` has this kind for its argument: it
takes a family and supplies each committed version to it.

### Leaving a transaction

A value whose type is indexed by a transaction's version cannot leave the transaction's
`with begin():` block. To leave, it is explicitly converted to a type that mentions no version. A
`UserKey` returned from the block is cast to `Int`, which makes it correct data and an unvalidated
key. A value whose type has no version-free supertype, such as a closure whose type mentions the
version, cannot leave at all. The spelling of the cast is open (question 4).

## Derived state: views

A **view** is a function `() ⇒ 𝑉 requires Transaction` whose definition reads cells. Calling it
evaluates the definition at the caller's version, including the calling transaction's own writes.
A view needs nothing beyond an ordinary function.

- **A view is not a `Cell`.** A cell's value at a version is whatever the last write left there.
  A view's value at a version is determined by the cells it reads, and a view admits no writes.
- **The definition is available to the refinement checker.** A fact read from a view, together
  with the definition, entails a fact about the cells it reads.

`@materialize` makes a view a **materialized view**: the system maintains its value eagerly and
incrementally as the cells it reads change. Caches and indexes are materialized views.

### Two kinds of materialized view

|                                 | In-transaction materialized view                | Deferred materialized view                                                                |
| ------------------------------- | ----------------------------------------------- | ----------------------------------------------------------------------------------------- |
| Declared                        | `@materialize`                                  | `@materialize(realm=𝑅, delay=𝑡)`                                                           |
| Realm                           | Its sources' realm                              | `𝑅`, named by the annotation and different from its sources'                              |
| Value read at version `𝜏`      | Its definition applied to the sources at `𝜏`   | Its definition applied to the sources at a committed version `σ(𝜏)` of the source realm |
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
[Three kinds of reference](#three-kinds-of-reference):

```python
@materialize
def carts_by_item() => FullMap(ItemKey, Set(CartKey)) requires Transaction:
    refs = [i -> c for c -> cart in carts for i in cart.lines]
    return map([i -> set([r.1 for r in g]) for i -> g in groupby(refs, \r -> r.0)])

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
- **Index syntax is planned.** A form such as `index(carts, \c -> c.lines)` is shorter, and the
  checker can carry a built-in lemma for it ("an absent key implies no occurrence in the source
  field") in place of unfolding a comprehension into quantified formulas (question 5).

### Deferred materialized views

`@materialize(realm=𝑅, delay=𝑡)` declares a deferred materialized view in realm `𝑅`. The
declaration names both realms:

- **The `requires` clause names the source realm.** The definition is an ordinary view and is
  checked as one: `requires Transaction(App)` means a transaction in `App`, the realm of the cells
  it reads.
- **The annotation names the materialized view's realm.** `realm=𝑅` must differ from the source
  realm. Callers in `𝑅` read the materialized view as `() ⇒ 𝑉@σ(𝜏) requires Transaction(𝑅)`; the
  annotation derives this type, and the `requires` clause keeps its meaning.

Each maintenance step is a commit in the materialized view's realm that installs the definition
applied to the sources at a later committed version of the source realm. `delay=𝑡` bounds
staleness: each maintenance commit installs a source version committed at most `𝑡` before it, and
the engine schedules maintenance to meet the bound.

```python
type Analytics = {}
instance std::txn::Realm(Analytics)

@materialize(realm=Analytics, delay=time::minutes(5))
def revenue_by_sku() => Map(Sku, Int) requires Transaction:
    return map([sku -> sum(o.qty * o.price for o in orders.values() if o.sku == sku) for sku in skus])

for req in dashboard_reqs:
    report = with begin(Analytics):
        revenue_by_sku()
    dashboard_resps << render(report)
```

The rules:

1. **A read has a version in the materialized view's realm.** At each version `𝜏` of that realm,
   the materialized view holds its definition applied to the sources at version `σ(𝜏)` of the source
   realm. `σ` is monotone in `𝜏`. A read at `𝜏` has type `𝑉@σ(𝜏)`.
2. **`source_version` exposes the source version.** `source_version(revenue_by_sku)` returns
   `σ(𝜏)` at the reading transaction's version, a position in the source realm's commit order. Two
   deferred materialized views in one realm can have different source versions at one `𝜏`, for
   example when their delays differ; a transaction that reads both sees each consistent with its
   own sources and compares their source versions. Other data is aligned with a result by an as-of
   join against its source version, in dataflow rather than in the reading transaction
   ([history and await_final](#history-and-await_final)).
3. **A deferred materialized view is computed from one committed prefix.** A materialized view with
   several sources reads all of them at one `σ`, never at a separate lag for each source. A deferred
   materialized view defined over another deferred materialized view lives in a third realm, and
   its source version is no later than its upstream's.
4. **A transaction never observes a deferred materialized view together with its sources.** A
   transaction in the materialized view's realm reads no cell of the source realm, so no
   transaction sees a source-realm write beside a materialized view that predates it, a
   combination no serial order produces.
5. **Dataflow through a deferred materialized view may be cyclic.** A value derived from a deferred
   materialized view reaches a write to its sources only as plain data: a transaction's result,
   passed to a later transaction in the source realm, which is strictly serializable in its own
   realm like any transaction that receives input. The cycle is a feedback loop with a lag, as in
   a fraud score that gates new orders. Whether the loop settles is a property of the program.
6. **Keys from a deferred materialized view are data.** `ItemKey` is a family over `Txn(App)`, and a
   transaction in the materialized view's realm cannot read `items` to validate against it. A key
   leaves the materialized view's realm only through an explicit cast to its base type, and a
   transaction in the source realm validates it with a guard. A deferred materialized view never
   discharges a deletion obligation.

## Growing collections

Two nominal collection types never change an existing element: `Log(𝑇)` and `OnceMap(𝐾, 𝑉)`. A
value of either type is an ordinary immutable collection. A program grows one by holding it in a
`Mut` or a `Cell`, and the container's rules apply unchanged: MVS for a `Mut`, identity and
transactions for a `Cell`. A `Log` guarantees the property: its only write, `x << v`, adds `v` at a
key no earlier write used. A `OnceMap` requires it of each writer: its write, `m[k] := v`, carries
the obligation that `k` is absent at the write's version, and the property holds because every
write in the program discharged it. The engine uses the property to release storage, skip conflict
checks and deliver elements before a history completes.

The two types replace `Feed(𝑇)`. A feed today is a history under an append merge law ([spec
8.4](../../../docs/chl-spec.md#84-feeds-are-the-second-form-of-mutability), "Feeds are the second
form of mutability"). Here the append law is a property of the content type, and the history is the
container's.

### The types

| Type | Write | Guaranteed by the type | Obligation on the writer |
|---|---|---|---|
| `Log(𝑇)` | `x << v` appends `v` | The write adds one element at a fresh key and changes no existing element | None |
| `OnceMap(𝐾, 𝑉)` | `m[k] := v` defines `k` | Given the obligation, the write changes no existing entry | `k not in m.keys()` at the write's version |

- **An element of a `Log` is keyed by the position of the write that appended it.** In a `Mut`, the
  key is the position of the loops around the `<<`, as a feed's contribution is keyed today ([spec
  3.7](../../../docs/chl-spec.md#37-feed-operator-)). In a `Cell`, it is the transaction's commit
  position in `Txn(𝑅)` together with the append's position within the transaction.
- **A `Log` in a `Cell` exposes the commit order of its keys.** The exact order, within a
  transaction and between transactions, is open (question 7). A `Log` in a `Mut` is ordered as its
  loop's positions are, which the spec leaves open ("Accumulator iteration order is not yet
  defined [Open]").
- **Both types are data functions.** A `Log(𝑇)` is a data function from its keys to `𝑇`, and a
  `OnceMap(𝐾, 𝑉)` is one from `𝐾` to `𝑉`. Neither is defined in terms of the other.
- **A `OnceMap` obligation is discharged like any refinement**: by a guard
  `if k not in m.keys():`, by the version chain, or by a key that is distinct by construction, such
  as the key of the enclosing loop's position. A definition whose obligation the compiler cannot
  prove is a type error, not a runtime failure ([Principles](#principles), 5).
- **Neither type has a write that removes or replaces.** A program that needs one uses `Map` or
  `List`.

### In a `Mut`

```python
out := Log::empty
for x in [1, 2, 3]:
    out << x * 10
sum(out)                                  # 60

resps := OnceMap::empty
for k -> req in reqs:
    resps[k] := handle(req)               # k is distinct at each position
```

Reads follow the `Mut` rules: inside the loop, the value at the current position; after it, the
final value. A `Mut(Log(𝑇))` parameter replaces a `Feed(𝑇)` parameter. A `Mut` is second-class,
so a `Mut(Log(𝑇))` is never a handle stored in data or returned from a function; a function may
return a `Log` value.

### In a `Cell`

```python
orders: Cell(Log(Order)) := Log::empty

for req in order_reqs:
    with begin():
        orders << req.order

for req in stats_reqs:
    total = with begin():
        sum(o.price * o.qty for o in orders)    # the log at this transaction's version
    stats_resps << str(total)
```

A transaction reads a `Cell(Log(𝑇))` at its version, as it reads any cell. The value is the log of
the appends committed before it, together with the transaction's own appends. The read never waits
on a writer that commits later. The storefront program's `orders.filter(\o -> o.time < now)`
(`tests/programs/storefront/v1.cambra`) is not needed.

```python
receipts: Cell(OnceMap(OrderId, Receipt)) := OnceMap::empty

with begin():
    if id not in receipts.keys():
        receipts[id] := charge(order)           # defined once: an idempotent charge
```

### The final value

The trailing read of a `Mut` after its loop, and `await_final(𝑥)` on a cell ([history and
await_final](#history-and-await_final)), give the history's final value. For a `Log` or `OnceMap`
the denotation is the same as for any content type. Operationally, every version is a prefix of the
final value, so an element present at any version is an element of the final value. The engine
delivers it to consumers before the history completes. Which consumers produce output before
completion is a property of the operational semantics (`docs/operational-semantics/`), and types do
not record it.

- **A lookup in a final `OnceMap` answers `some` once the key is defined.** It answers `none` only
  once the history completes, which is the rule for any collection ([spec
  3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access), "Subscript and attribute
  access").
- **A history whose writers never finish has no final value.** A read that needs the whole value,
  such as `sum`, never completes. The compiler does not reject such a read: termination checking is
  deferred (question 8).

### What the facts enable

Each fact below holds of a `Log` because of its type, and of a `OnceMap` because every definition
discharged its obligation.

| Fact | Enables |
|---|---|
| A present element or entry never changes | A read of it needs no conflict check: it holds at every later version |
| The key set only grows | A validated key over a `OnceMap`'s keys needs no re-check at later writes, and stays valid in every later transaction of its realm; the type of such a key outside a transaction is open (question 4) |
| Every version is a prefix of the final value | Elements of a final value are delivered before the history completes |
| An append reads nothing | Concurrent appends to one cell do not conflict ([Elisions](#elisions), commutativity) |
| A consumer has read past a prefix | The prefix is released ([Types](#types)) |

A grow-only key set is declared by its type, `OnceMap`, and never inferred from the absence of a
shrinking write in the program. An inferred property would let a reload that adds a remove change
the meaning of every type built on the set, and static knowledge buys performance, not semantics
(principle 4).

A read of absence is an ordinary read and is validated, as is a read that depends on the whole
collection, such as a count or an aggregate. A `Mut(Log(𝑇))` read only through its final value
need not be stored: each element flows to consumers when it is appended, as a feed's
contributions do today.

## Crossing between dataflow and transactions

A value with no history, such as a source, a comprehension result or a history's final value, is
immutable data, and time does not appear in its type. A `Mut` or a `Cell` is a history, and a read
of it names a position. Each crossing between the two has one form:

| From | To | Form |
|---|---|---|
| A value | A transaction | Read as plain data. A read of the whole value waits until the value is final. |
| A source arriving over time | A transaction, at its version | A loop appends each element to a `Cell(Log(𝑇))` in a transaction; transactions read the cell |
| A `Mut` | Dataflow | The trailing read after its loop |
| A cell | Dataflow | `await_final`, or a transaction's result |
| A cell's committed versions | Dataflow | `history(𝑥)`, a `Log(𝑉)` |
| A cell's committed versions | Another realm | A deferred materialized view ([Deferred materialized views](#deferred-materialized-views)) |

A transaction that reads a source directly reads the whole stream and waits for it to end. The
second row is the form that reads an arriving stream as of a version:

```python
arrivals: Cell(Log(Req)) := Log::empty
for r in reqs:
    with begin():
        arrivals << r
```

### history and await_final

`history(𝑥)` on a cell `𝑥: Cell(𝑉, 𝑅)`, named directly or through a `Ref`, is a `Log(𝑉)` with one
element per commit that writes `𝑥`: the content `𝑥` holds after that commit, keyed by the commit's
position in `Txn(𝑅)`. It is the history of [Terms](#terms) as a value, and the cell's change log,
which a deferred materialized view consumes, deriving each change from two consecutive elements. It
is a value, so it is read outside any transaction, and its elements are delivered as the commits
happen. `await_final(𝑥)` is its last element. Both accept a `Ref`, because a sink's loop reads the
cell it allocated ([Sinks](#sinks)); the loop is a consumer of the cell and keeps it alive
([Types](#types)).

`history(𝑥)` is final only when no transaction can write `𝑥` again, at the end of the run, so a
transaction that reads it as plain data waits for the run to end, and a join against it runs in
dataflow. Aligning a deferred materialized view's result with `history(𝑥)` is such a join: the
elements keyed at or before the result's `source_version`.

The join is a dataflow operation over a `Log` keyed by `Txn(𝑅)` and a position `𝑝` in `Txn(𝑅)`.
It yields the elements keyed at or before `𝑝`, and it completes once delivery of the log has passed
`𝑝`, before the run ends. To detect that, the engine delivers `history(𝑥)` in commit order or
carries the latest delivered position with it. The operational semantics needs a completion rule
for this prefix of a growing collection.

A deferred materialized view whose definition reads a `Cell(Log(𝑇))` receives only insertions; if
the definition is monotone, DBSP maintains it without retractions.

### Sinks

A sink consumes writes made after the function that created it returns: `http::serve`, or the spec's
`fanout` ([spec 3.7](../../../docs/chl-spec.md#37-feed-operator-)), which declares a feed, loops
over it and returns it. Here it is a function that allocates a cell with `Ref::new`, runs a loop
over the cell's final value, and returns the `Ref`. Callers write the cell in transactions.

`http::serve` takes a realm `𝑅` as a type parameter, allocates the response cell in `𝑅`, and
returns `(reqs, resps)` with `resps: Ref(OnceMap(ReqId, Response), 𝑅)`. The server sends each
entry once it is committed. Each `resps[k] := v` carries the obligation `k not in resps.keys()`;
for `resps[req.id]` the source discharges it by declaring request ids distinct. A response written
inside a handler's transaction is sent only if that transaction commits, which is the gating spec
8.4 states.

A `Mut` returned by move does not work as a sink: the callee's read of the final value would need
the caller's binding to continue the callee's history, and a rule rejecting a write that depends on
the final value of its own history.

## Three kinds of reference

### Comparison

| | `Ref(𝑉)` | Validated key | Unvalidated key |
|---|---|---|---|
| Representation | Opaque | Transparent, with a proof in the type | Transparent |
| Holders | Internal, and every one is typed | Internal, in cells the compiler knows | External, unknowable |
| Deletion | The collector, by tracing | The program, proved safe | The program, unchecked |
| Version-indexed | No | Yes | No |
| Dereference | Always succeeds | Always succeeds | A guard or `resolve`, which can fail |
| Classic analogue | Managed reference | Foreign key with `ON DELETE RESTRICT`, checked at compile time | Manual memory management |

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
   version, so every `ItemKey` in `carts` is in `items` in every committed state. A key read from
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
   fail. A key that crosses a module boundary is an unvalidated key.

Removing `𝑗` from a key set narrows the family, and every dependent must hold no `𝑗` at the commit
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
*r          = heap_ρ[r]            r.f := v  is  heap_ρ[r].f := v
```

A `Ref`'s deletion policy differs from a validated key's in which holders it counts. A validated
key counts references in committed dependent cells, and the program deletes once the obligation is
discharged (restrict). A `Ref` counts every holder, in cells, in locals and in values held outside
any transaction, and the collector deletes (collect). A `Ref` can be held outside a transaction
and a later transaction must still reach its cell, so every holder counts; counting every holder is
decidable only if the holders are exactly the `Ref`-typed values, which requires that `Addr_𝜌`
cannot be built from data. Tracing is what collect adds over restrict: it finds holders outside
cells and reclaims cycles.

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

A `Ref` names a whole cell. An element of a cell's collection has no identity of its own, so no
`Ref` points into a cell's content. Each need for a reference to substructure is met by an
existing form:

| Need | Form | What it gives |
|---|---|---|
| Access for the duration of one call | Pass the path as a `Mut` parameter: `f(xs[i])` | A second-class reference that ends with the call (see [The rules](#the-rules)). For a cell's content, the argument is converted by `to_mut` inside a transaction. |
| A durable reference whose target the program deletes | `Cell(Map(𝐾, 𝑇))` and a validated key `{𝐾 where _ in xs.keys()}` | A transparent key, valid within one transaction, under restrict |
| A durable, opaque reference that the collector manages | Allocate each element as its own cell: `Cell(List(Ref(𝑇)))` | A `Ref(𝑇)` that keeps its element alive, at the cost of an edge in the type graph of cells |

An opaque reference that pairs a container's `Ref` with a path does not exist. Two facts rule it
out:

- **A position is not an identity.** After an insert at the front, `xs[3]` names a different
  element; after `xs[0] := xs[1]`, no element is the one the reference meant. A key into a `Map`
  is a stable position, which is the validated-key row above.
- **The entry can be deleted while the reference is held.** Holding the pair keeps the container
  alive, not the entry. Restricting the entry's deletion makes the reference valid only within the
  transaction that checked it, a validated key; having the collector keep the entry alive manages
  it apart from its container, a separately allocated cell.

A program that wants the pair writes the record `{map: Ref(Map(𝐾, 𝑇)), key: 𝐾}` and validates
the key with a guard in each transaction.

## Invariants over cell contents

A refinement in a cell's content type is an invariant over every committed state, because `Cell`
supplies every committed version to its content type. Any write to a cell that the refinement
reads can break it. Removing a key from a key set, which breaks every dependent that still holds
the key, is one case of the rule below.

### The obligation

- **Read set.** The read set of a type family is the cells its definition reads. `ItemKey` reads
  `items`.
- **Dependents.** The dependents of a cell `𝑑` are the cells whose content types mention a family
  whose read set contains `𝑑`. `carts` is a dependent of `items`.
- **The rule.** A write to `𝑑` produces a version `𝜏′`. Each dependent's content at `𝜏′` must
  inhabit its content type instantiated at `𝜏′`.

A write to a dependent has no additional obligation: the value written is typed at the current
version, as any value is. A dependent that may violate its type at `𝜏′` is a type error that names
the dependent and the position: after `items.remove(k)`, "`carts` may contain `k` in `lines`".

### Which writes create an obligation

Whether a write to `𝑑` can break a dependent depends on how the family occurs in the dependent's
content type, and on whether the write narrows or widens the family:

| Occurrence                                                | Example                                                            | Writes that create an obligation                                   |
| --------------------------------------------------------- | ------------------------------------------------------------------ | ------------------------------------------------------------------ |
| Covariant: the dependent holds values of the family       | `List(ItemKey)`, the keys of a `Map(K, V)`                         | A write that narrows the family, such as a remove from the key set |
| Contravariant: the dependent accepts values of the family | A stored function of type `(k: UserKey) ⇒ 𝑇 requires Transaction` | A write that widens the family, such as an insert                  |
| Invariant: the dependent's type is exactly the family     | `FullMap(UserKey, 𝑇)`, whose domain is every `UserKey`            | Every write that changes the family                                |

Whether a write narrows or widens a family is a comparison of two instances, `𝑇@𝜏′ ⊆ 𝑇@𝜏` or
`𝑇@𝜏 ⊆ 𝑇@𝜏′`. Membership in a key set is monotone in the set, so an insert widens and a remove
narrows with no solver query. Other predicates go to z3 (question 10). A write the compiler cannot
classify creates an obligation for every occurrence. A write that changes no instance, such as
overwriting the value under an existing key, creates none.

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
      carts := map([c -> Cart::new(lines=[i for i in cart.lines if i != k]) for c -> cart in carts])
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
view belongs to another realm ([Deferred materialized views](#deferred-materialized-views)).

### When obligations are checked

Obligations on cell contents are checked at the commit point, against the transaction's last
version. A check at each write's version would reject every invariant occurrence, as the `prefs`
example shows, and deleting a reference cycle fails the same way.

Inside a transaction, a cell's content is typed like a local value. It has the type it had at the
version that last wrote it, or at the committed version if the transaction has not written it. Rule
3 of [Validated keys](#validated-keys) re-checks each use at a later version: a key read from
`carts` after `items.remove(𝑗)` needs `𝑘 ≠ 𝑗` at its use, as a local key does.

The module-local rule ([Validated keys](#validated-keys), rule 5) and the concurrency argument
([Concurrency](#concurrency)) apply to every obligation unchanged.

## Footprints and elision

### Footprints are requirements and effects

A transaction's footprint is its read requirements and its write effects. As in the effects stack,
a read is a requirement, `requires ReadCell(𝑝)`, and a write is an effect, `causes WriteCell(𝑝)`.
Each names a path: `ReadCell(carts_by_user)`, `WriteCell(items[k])`,
`WriteCell(s.cart.items[sku])`. A path starts at a root cell or at a parameter in scope. Each `.f`
or `[k]` step selects a field or an entry, and a step through a `Ref` continues in the cell it
names. A path with no steps names the whole cell. A read or write of `to_mut(𝑥)` at a path `𝑝` is
the requirement or effect on `𝑥` followed by `𝑝`.

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
it, as in `WriteCell(carts_by_user[u].items)`. Every effect a signature states therefore has a
path in scope, and a signature needs no site parameters.

### Elisions

| Elision | Condition | Effect on the engine |
|---|---|---|
| Disjointness | Two transactions' footprints are provably disjoint | No conflict check between them |
| Partitioning | Two transactions are disjoint whenever their inputs differ in a known way, such as different `req.user` | Route by key; check only within a partition |
| Commutativity | A write whose read feeds only that write, such as `balance += x` | No validation of that read |
| Stable entries | A read of an element of a `Log`, or of a present entry of a `OnceMap` | No validation of that read |
| Deterministic scheduling | The footprint is known before execution | Order transactions without aborts, as in Calvin |

Strict serializability constrains every elision: a commutative update merged late, or a read served
from an old snapshot, can be serializable without respecting real-time order, so each elision needs
an argument for real-time order as well as for serializability.

### References read from state

When a transaction obtains a `Ref` or a key by reading a cell, as the `adds` loop of
[Example](#example) does, its footprint's sites are known statically and its exact cells and keys
are not. Execution then needs a reconnaissance step that performs those reads first, as in Calvin's
OLLP. This is the main runtime cost of first-class references.

### Across modules

Every module is linked into one program before inference and planning. The planner therefore sees
every `with begin():` block that touches a cell, whichever module it is in, and elision needs no
footprint declarations in signatures. Declared footprints serve a different purpose: stability
across reloads. An elision is a proof about the whole program, and a reload that adds a write to a
shared cell can invalidate it. A module type that bounds its runs' footprints lets a reload within
those bounds keep other modules' plans (question 16).

A `Ref` that crosses a module boundary has an abstract site kind. Its effects name the run's cells
as a whole, as `WriteTxn(inv::_)` does in the effects stack.

## Garbage collection

The design avoids leaks: unreachable cells, cycles included, and versions no consumer can read are
eventually reclaimed.

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
| Cyclic | A `Ref(𝐵)` in 𝐴's content, with 𝐴 and 𝐵 in one strongly connected component of the graph | Count updates, plus cycle collection within that component |

### Guarantees

1. **A collection whose type contains no `Ref` is never visited by the collector.** This is decided
   from the type. A table keyed or filled by validated keys is such a collection.
2. **A write costs collector work proportional to the `Ref`s it stores or removes.** No table is
   scanned to find roots.
3. **Tracing is confined to cyclic components.** Cycle collection starts from candidates, which are
   cells whose count decreased without reaching zero, and explores only what they reach within
   their component (Bacon & Rajan, "Concurrent Cycle Collection in Reference Counted Systems",
   2001). Partitioning the heap by static connectivity follows Hirzel, Diwan & Hertz,
   "Connectivity-Based Garbage Collection", 2003.
4. **A bound can be asserted.** `@NoTrace` on a root cell or a cell type asserts that it lies in no
   cyclic component. If the type graph has a cycle through it, compilation fails with an error
   naming the cycle. The annotation checks a property; it does not restrict what programs may
   build.

Cycle collection in a component that contains a large collection is proportional to the part of
the component explored. The compiler reports such components; a program avoids the cost by storing
those edges as keys.

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

A pinned cell is a root until `unpin`. The collector does not trace unvalidated keys. A `Pin` whose
cell has been unpinned and reclaimed resolves to `None`.

## Staging

`Ref` with the collect policy is the plan of record. The steps toward it:

1. **Module-local validated keys, checked statically.** Refinements mention only the module's own
   cells. Each obligation is discharged by the commit point of the transaction that creates it, by
   a compensating write, a guard, the version chain or an index, or the program is rejected. No
   runtime check is inserted.
2. **`Ref` with the collect policy.** This step introduces reference counts, the root scan and
   cycle collection.
3. **Cross-module validated keys.** A deletion can no longer see every dependent. The program reads
   a system-maintained reference count, `refs(𝑆)`, built on step 2's counting, as an explicit
   guard, or the deletion is rejected.

## Changes relative to the current implementation and the effects stack

| Today | This design |
|---|---|
| `Mut(𝑉, Txn)` | `Cell(𝑉, 𝑅)`, with `𝑅` the default realm when omitted |
| `Mut(𝑉, 𝐷)` with an inferred induction domain | `Mut(𝑉)` |
| Transactional state only at a module's top level | Root cells at the top level, and cells allocated with `Ref::new` anywhere a transaction is supplied |
| `Mut(_, Txn)` parameters | `Ref(𝑉, 𝑅)` parameters, effects on captured cells, or a cell passed to a `Mut(𝑉)` parameter through `to_mut` |
| `requires ReadTxn(x)`, `causes WriteTxn(x)` per variable | `requires ReadCell(𝑝)`, `causes WriteCell(𝑝)` per path, resolved to sites by the compiler |
| `causes Append(x)` on a feed | `causes Write(x)` on a `Mut(Log(𝑇))`, or `causes WriteCell(𝑝)` on a cell holding a `Log` |
| Footprints per variable | Footprints per site and path |
| `Mut` writes to a whole variable | Writes to paths, with exclusivity checked per part |
| Refinements over values only | Refinements may read the module's cells, through types that require a transaction |
| `requires Transaction` on functions only | Also on type declarations, as a version index |
| One commit order for the program | Realms named by nominal types, each with its own commit order; `requires Transaction(𝑅)` |
| No derived state | Views (functions that require a transaction); `@materialize` materialized views, maintained inside each writing transaction or deferred into another realm with `realm=𝑅, delay=𝑡` |
| `Feed(𝑇)`, a history under the append merge law | `Log(𝑇)` content in a `Mut` or a `Cell`; `<<` appends to a `Log` |
| A keyed feed, `resps[req.id] = …` ([spec 7.3](../../../docs/chl-spec.md#73-sources), sketch) | `OnceMap(𝐾, 𝑉)` content in a `Mut` or a `Cell`; `m[k] := v` defines a key once |
| A feed read in a transaction waits for its domain to be final, or for a cut such as `o.time < now` | A `Cell(Log(𝑇))` read at the transaction's version |
| A feed handle in a tuple ("A deferred collection inside a data structure [Open]") | A `Ref(Log(𝑇))` or `Ref(OnceMap(𝐾, 𝑉))` to a cell the callee created ([Sinks](#sinks)) |
| `await_final` on a top-level `Mut(𝑉, Txn)`, named directly ([spec 8.6](../../../docs/chl-spec.md#86-await_final)) | `await_final` and `history` on a cell or a `Ref` ([history and await_final](#history-and-await_final)) |
| No reclamation of transactional state | Parts of root cells reclaimed as their consumers release them; allocated cells garbage-collected |

### Proposed changes to the spec and the compiler

Proposals for the owners of each part.

- **[Spec 3.7](../../../docs/chl-spec.md#37-feed-operator-) and
  [8.4](../../../docs/chl-spec.md#84-feeds-are-the-second-form-of-mutability).** `<<` appends to a
  `Log` held in a `Mut` or a `Cell`. "Feeds are the second form of mutability" becomes: a `Log` is a
  content type whose writes only add.
- **[Spec 3.7](../../../docs/chl-spec.md#37-feed-operator-), "A deferred collection inside a data
  structure [Open]".** Closed: the handle is a `Ref`, which a data structure holds like any other
  `Ref`.
- **[Spec 3.9](../../../docs/chl-spec.md#39-subscript-and-attribute-access), "Absence at a cut
  [Open]".** A transaction's version is the cut for a `Cell(Log(𝑇))` or `Cell(OnceMap(𝐾, 𝑉))`.
- **[Spec 8.2](../../../docs/chl-spec.md#82-transactions-with-begin), "a block is also the value
  it computes" [Tentative].** Decided: the block yields `` `commit(𝑣) ``, `` `aborted(𝑒) `` or
  `` `gave_up ``. A reply fed outside the block fires for every outcome, with the outcome as its
  value ([Transaction outcomes](#transaction-outcomes)).
- **[Spec 8.5](../../../docs/chl-spec.md#85-ordering-and-concurrency).** "Nothing is ordered by its
  position in the source text" does not hold for two loops that write one `Mut`: the second loop
  continues the first's history in statement order (`src/ccl/design/mutability.md`, the
  sequencing-domains table). `t := 0`, a loop adding `[1, 2, 3]`, then a loop multiplying by `[10,
  20]`, gives `1200`; with the loops swapped, `6`.
- **Mutability elimination.** `Feed`'s `HistoryKind::Append` becomes a property of `Log` content
  under `mut_elim`, and the `Feed`-kind `LetRec` groups `channelize` assembles become `Log`
  histories.
- **Inference.** `Feed(𝑇)` leaves the type language; `Log(𝑇)` and `OnceMap(𝐾, 𝑉)` are nominal
  types with methods.

## Open questions

Candidates listed under a question are proposals with their costs, not decisions.

**Transactional state**

1. **Transaction boundaries.** Whether a loop iteration over a source becomes the default
   transaction, with the compiler splitting it where transaction chopping (Shasha et al., 1995)
   proves serializability preserved, and whether `Ref::new` is allowed outside a block, which needs
   a creation commit of its own. For now every transaction is an explicit `with begin():` block, and
   `Ref::new` requires one ([Transaction boundaries](#transaction-boundaries)). Also whether a realm
   sets a default deadline for its transactions ([Transaction outcomes](#transaction-outcomes)).
2. **`Pin` lifetime.** Explicit `unpin` only, or a time-to-live (`pin(r, ttl)`) for identities
   such as session cookies that expire.
3. **User-defined projections.** `to_mut` is the only projection: an operation that yields a
   second-class `Mut` rather than returning a value. Whether programs can define projections, as
   Hylo's subscripts do, is not decided. If they can, `to_mut` and `*` become ordinary
   definitions.

**Versions**

4. **The cast out of a transaction.** Its spelling ([Leaving a
   transaction](#leaving-a-transaction)), and the type outside a transaction of a key over a
   grow-only key set, which stays valid in every later transaction of its realm ([What the facts
   enable](#what-the-facts-enable)). Candidates for the spelling:
   - (a) A type ascription on the receiving binding, `k: Int = with begin(): …`. A result with no
     version-free supertype is an error at the ascription.
   - (b) A builtin applied inside the block that maps a value to its base type. Cost: a second
     spelling for what an ascription states.
   - (c) An implicit coercion of a block's result to its version-free supertype. Cost: the point
     where the proof is dropped is invisible, against principle 5.
   - Recommendation: (a).

**Derived state**

5. **Index syntax.** The spelling of an index and its built-in lemma ([Indexes](#indexes)).
6. **Materialized views with parameters.** Future work. A view takes no parameters
   (`() ⇒ 𝑉 requires Transaction`), so a materialized view holds one value. A view with
   parameters, such as `orders_for(u: UserId)`, could be materialized only for the arguments that
   are read, as Noria does: the state for an argument is computed by an upquery on its first read,
   maintained incrementally after that, and can be evicted. This design does not include it.

**Growing collections and dataflow**

7. **Order of a `Log`'s keys in a cell.** A key is the commit's position in `Txn(𝑅)` with the
   append's position within the transaction ([The types](#the-types)); the order between keys is not
   decided.
   - (a) Lexicographic: commit position, then the position a `Mut`'s log uses within the transaction
     ([spec 3.7](../../../docs/chl-spec.md#37-feed-operator-)). The open part is then the spec's
     "Accumulator iteration order is not yet defined [Open]".
   - (b) Commit position only, with one commit's appends unordered. Cost: a `Log` is not a
     sequence within a commit.
   - Recommendation: (a).
8. **Termination checking.** A read of the final value of a history whose writers never finish,
    and a cell write of a value that is never final (`c := stdin()`), never complete. A check that
    rejects them is deferred until the system is more mature.

**References and invariants**

9. **Child modules.** A child module reaches its parent's state only through the arguments of
    its `run` (spec: "Runs share state only by being passed"). Whether a refinement may mention a
    cell received as a module parameter decides whether staging step 1's restriction covers
    children.
10. **Classifying writes.** Which predicates the compiler classifies as monotone in their read
    set without a solver query, beyond membership in a key set.
11. **Refinements across possibly aliased cells.** Inside a transaction a cell's content keeps the
    type it had at the version that last wrote it ([When obligations are
    checked](#when-obligations-are-checked)). A write through `*r` may have written `x` when `r`'s
    site kind contains `x`, and the rule for the refinements the transaction learned about `x`'s
    content is not written.
    - (a) A write through `*r` that the exclusivity facts ([Converting a cell to a
      Mut](#converting-a-cell-to-a-mut)) do not separate from `x` counts as a write to `x` at an
      unknown path: `x`'s content returns to its declared type, and rule 3 of [Validated
      keys](#validated-keys) re-checks keys read from it earlier. Cost: refinements learned before
      the write are lost where the facts cannot separate the cells.
    - (b) The write is rejected unless disjointness from every cell read earlier in the
      transaction is proved. Cost: rejects every write through a `Ref` whose site kind contains a
      root cell the transaction has read.
    - Recommendation: (a).
12. **Declared invariants.** Whether cell contents should carry invariants beyond refinements and
    views, letting the compiler check explicit boundaries and admit more elisions (Bailis et al.,
    VLDB 2015; Gotsman et al., POPL 2016).
13. **Prior work on static restrict.** Branded indices (Kiselyov & Shan) and GhostCell prove
    validity for one collection over one scope, without deletion against persistent dependents. A
    literature search for statically checked referential integrity has not been done.
14. **Lowering `Ref`.** Whether native code can lower `heap_𝜌[r]` to a pointer dereference, with
    `Addr_𝜌` as the address and no materialized index, under MVCC versioning of the cells.

**Footprints**

15. **Written path effects.** Which paths a clause may name beyond those starting at a root cell
    or a parameter, such as a path through a value the body computes.
16. **Reloads that widen footprints.** Whether a reload may re-plan other modules, or must stay
    within declared footprints ([Across modules](#across-modules)).

## References

Citations are from memory. Confirm venue and year before quoting.

- Racordon, Shabalin, Zheng, Abrahams, Saeta. "Implementation Strategies for Mutable Value
  Semantics." *Journal of Object Technology*, 2022.
- Reinking, Xie, de Moura, Leijen. "Perceus: Garbage Free Reference Counting with Reuse." PLDI
  2021.
- Bacon, Rajan. "Concurrent Cycle Collection in Reference Counted Systems." ECOOP 2001.
- Hirzel, Diwan, Hertz. "Connectivity-Based Garbage Collection." OOPSLA 2003.
- Deutsch, Bobrow. "An Efficient, Incremental, Automatic Garbage Collector." CACM 1976.
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

