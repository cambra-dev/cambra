# Mutability, transactions, and feeds

Cambra's surface language (CHL) is Pythonic: programs reassign variables, accumulate
in loops, run transactions, and stream replies out to sinks. The runtime is a pure
dataflow graph over *tilings* — there is no mutable cell anywhere. This document explains
how the two are reconciled: the semantic model that makes mutation, transactions, and
feeds one idea, the surface syntax, and how the compiler realizes them.

## The idea in one line

A mutable variable **is** a function from a **sequencing domain** (a time axis) to a value.
"Mutation" is the incremental revelation of that function's values as the domain advances;
"reading the variable" is looking up a value at a position. Sequential rebinding, loop
accumulation, and concurrent transactions are then *one* model over three domains, not three
mechanisms — and a feed (a reply or yield) is just an output of that model, a function over
the same domain.

This rests on the existing extent-vs-tiling correspondence
([operational-semantics/summary.md](../../../docs/operational-semantics/summary.md)) applied to a
time domain: a value type's *extent* is its set of final values; its *tiling* is the progress
algebra of partial states. A mutable variable's extent is the set of total functions `𝐷 ⇒ 𝑉`;
its tiling is the accumulating partial function `𝐷 ⇀ 𝑉`, each mutation a `⊕`-extension by one
position. The tiling *implements* the function; it does not redefine it.

## The model: histories and guarded recursion

A mutable variable of value type `𝑉` over sequencing domain `𝐷` denotes a total function
`𝐷 ⇒ 𝑉`: its **history**. The history functions of a program's mutable variables form one
**mutually recursive definition group** (a `letrec`), well-founded because every recursive
reference is **guarded** — it consults only *strictly earlier* positions of the domain, through
one of two accessor builtins:

- `get_prev_seq(ℎ, 𝑖, 𝑑)` — for an **induction domain** (a loop's iteration index): the value of
  history `ℎ` at the predecessor of `𝑖`, or the default `𝑑` at the first position.
- `get_prev_txn(𝑤, 𝑡, 𝑑)` — for the **transaction domain** `Txn` (a total order of commit times):
  the value carried by the latest commit in stream `𝑤` at a time *strictly before* `𝑡`, or the
  default `𝑑` if there is none.

Because every cycle in the group crosses a guard, values at any position depend only on strictly
earlier positions, and the group has a unique solution by induction along the domain order.

### Sequencing domains

| Mutation context | Sequencing domain | Guard |
|---|---|---|
| Sequential statements | degenerate (each position used once) | plain `let` shadowing; no letrec binding |
| `for` loop | the iteration source's domain (`UIntRange` for a literal list, a `DataSource` domain for a stream) | `get_prev_seq` |
| `with begin():` transaction | `Txn`, an anonymous total order issued by the runtime | `get_prev_txn` |
| `while` loop *(future)* | a prefix of `Nat` bounded by the running condition | `get_prev_seq` over a self-ceiling domain |

The structural difference between the two guards mirrors a difference between the two kinds of
variable:

- An **induction variable** has exactly one writer (its loop), and its domain *is* that writer's
  domain. Its history binding is directly the recurrence:
  `cnt = λ 𝑟 → get_prev_seq(cnt, 𝑟, init) + 1`.
- A **transactional variable**'s domain (`Txn`) is *not* any writer's domain — writers iterate
  request streams, and an oracle assigns each transaction a commit time. So its history is defined
  *indirectly*, through **commit records**: each writing site produces one `{time, write}` record
  per iteration, and the variable's history searches those records by time. The commit-time oracle
  is a per-site builtin `begin_<site> : 𝐼 ⇒ Txn` mapping the site's iteration index to the
  transaction's position in the commit order.

Feeds are the letrec's **outputs**: the body of the letrec is a record of channels (one field per
defer/sink), each a function over its contributing loop's domain, free to reference the letrec's
bindings.

## Surface language

### Mutability is explicit, by the `:=` operator

A variable is mutable **by the operator that introduces it**: `:=` introduces (and writes) a
mutable store; plain `=` is an ordinary immutable binding and *never* mutates. The `Mut[…]`
annotation is **optional** — it carries the value type and, for the transactional case, the
sequencing domain — but it is `:=`, not the annotation, that makes a variable a store.

```python
cnt := 0                     # loop accumulator; value type and sequencing domain both inferred
cnt: Mut[Int] := 0           # same, with the value type spelled explicitly
store: Mut[Int, Txn] := 0    # transactional register over the commit order
out: Feed[_]                 # a feed (deferred output); no initializer
```

- `:=` — the mutation operator, for both the initial introduction (`cnt := 0`) and every
  subsequent write (`cnt := cnt + 1`), inside a loop or transaction or at the top level. `+=` is
  its compound shorthand. A plain `=` binds immutably: `x = 0; x = x + 1` is ordinary `let`
  shadowing, and a plain `=` to a name bound outside a loop is a lowering error that points at
  `:=`.
- `Mut[𝑉]` / `Mut[𝑉, 𝐷]` — the optional store annotation. `𝑉` is the value type (inferred if
  omitted, i.e. a bare `cnt := 0`); the second parameter `𝐷` is the sequencing domain, omitted
  (or `_`) it is inferred as the domain of the loop that writes the variable. `Txn` — the
  transactional case — is **never inferred**: sharing a variable across concurrent writers or
  endpoints is a semantic commitment the program must spell, so a transactional register is
  introduced with `store: Mut[𝑉, Txn] := …`. `Mut[…]` is also legal as a function *parameter*
  annotation — pass-by-reference, under the downward-only discipline in
  [`Mut` is a CCL type](#mut-is-a-ccl-type). A `Mut[…]` annotation with a plain `=`
  (`x: Mut[Int] = 0`) is contradictory and rejected — use `:=`.
- `Feed[𝑉]` — a deferred output channel, fed with `<<`. Introduced by a bare annotation
  (`out: Feed[_]`, no value), or arriving from a builtin (`http_serve` returns its response
  channel at a `Feed` type).
- `_` is a **wildcard** accepted anywhere in a user type annotation, meaning "infer this slot."
  `Mut[_]`, `Feed[_]`, `Mut[_, Txn]`, `List[_]` are all legal.

A name needs `:=` exactly when its history spans iterations or transactions; a value that is
computed once and never re-stored stays a plain `=` binding.

### Transactions

A transaction is a `with begin():` block, usable anywhere a statement can appear — as a loop body
(one transaction per iteration) or standalone (a single transaction):

```python
for req in incr_reqs:
    with begin():
        store += 1
```

`begin()` is the transaction marker. The handle form `with t = begin():` binds `t` to the
transaction's commit time (a `Txn` value): `t` *is* the position `begin_<site>(𝑟)` the letrec
manipulates. Writes to `Txn`-domain variables are legal only inside a `with begin():` block; all
writes in one block commit atomically. Nested transactions are rejected — a block commits as one
unit, so a `with` inside it has no coherent meaning.

### Reads

- **Inside the mutating context** — a bare reference denotes the value at the current position:
  the previous iteration's value, or, after a write in the same iteration/block, the written value
  (read-your-writes).
- **After a loop** — a bare trailing read of an induction variable is its final value
  (`last_or_default` over the completed history; the loop has ended, so "latest" is unambiguous).
- **A `Txn` register is read only inside a `with begin():` block.** A bare read outside one is an
  error (hint: "read transactional variable `x` inside a `with begin():` block"). Reading inside a
  block pins a snapshot-consistent view — several `Txn` reads in one block see one commit snapshot,
  which is the point of requiring the block. A read fed out of a block that does *not* write that
  store is a **live as-of read**: `for r in reqs: with begin(): out << store` reads the store's
  latest committed value as of each request and replies indexed by the *request loop* (the outer
  context), not the commit clock — the live cross-endpoint read. The **terminal** read is the
  degenerate case: a trailing standalone `with begin(): out << store` latches the store's final
  value once its writers complete (`out` is the one-element stream `[final]`). Both are the same
  as-of read.

## CCL representation

### Direct-mirror nodes: `For`, `MutWrite`

Lowering emits nodes that mirror the CHL statements, doing no semantic work — it changes
representation only, leaving structure for the type checker and the unified phase to interpret:

- `For { target, iter, body }` — **every** statement `for` loop, generator / side-effecting /
  mutation alike (comprehensions keep their expression lowering). Lowering does *not* distinguish
  the loop kinds — that classification is the phase's, post-inference (see
  [Store-ness is the type](#store-ness-is-the-type-no-lowering-registry)). Value `Unit`;
  `iter : 𝐼 ⇒ 𝑇`, `target : 𝑇` bound in `body`.
- `MutWrite { name, value }` — one write to a variable. Value `Unit`. Its target **must** be
  `Mut`-typed: inference peels the target's `Mut[𝑉, 𝐷]` and requires `value ⊑ 𝑉`; a write whose
  target is *not* `Mut` is a **type error**, never a shadowing rebind (`x += e` on a plain `x` is
  rejected, not silently turned into `x = x + e`). `x += e` lowers to `MutWrite(x, x + e)`, the
  embedded read being the in-context read.
- `Feed { name, value }` / `Defer` — a `<<` feed and its channel. These survive into inference (so
  a defer binding is typed, at `Feed[𝑉]`) and are eliminated by the unified phase.

`For`/`MutWrite`/`Feed`/`Defer` are **pre-phase surface-structure nodes**: pure placeholders no
pass executes, eliminated wholesale by the unified phase. The purity invariant
([src/ccl/CLAUDE.md](../CLAUDE.md)) holds the same way it does for `Defer` — the phase asserts no
residue, and planning/op-conversion never see them.

### Store-ness is the type (no lowering registry)

Whether a name denotes a mutable store is carried **only** by the store type
`Type::History { kind: Store }` (displayed `Mut[𝑉, 𝐷]`), and is therefore known
only after inference. Lowering never tracks it — there is no lowering-side store registry. This is
what keeps lowering a pure representation change: it emits the markers above by *shape and scope
alone*, and every decision that needs store-ness happens later, keyed on the type.

Lowering's two choices, both scope-only:

- **Introduction vs. write.** `x := e` where `x` is *not* in scope is an introduction — a
  `let x = e` whose binding is stamped `Mut[𝑉, 𝐷]` (`𝐷 = Txn` iff annotated `Mut[𝑉, Txn]`, else a
  `Hole` the phase resolves). `x := e` / `x += e` where `x` *is* in scope is a write — a bare
  `MutWrite(x, e)`. The choice is membership in the ambient scope set (which lowering already
  threads for other reasons); it consults no mutability record.
- **Loop shape.** Every `for` becomes a `For` marker (above). Lowering does not decide
  generator-vs-mutation.

Everything store-dependent is then a post-inference decision on the store `Type::History`:

1. **Writes require a mutable** (`MutWrite` target must be `Mut`, above). A `+=` / `:=` to a plain
   binding is a type error, not a shadow. This is the single rule that makes "declare it with `:=`"
   a real discipline rather than a lowering-time heuristic.
2. **Pass-by-reference requires the `Mut[…]` annotation.** The annotation is *what gives the
   parameter a store `Type::History`*, so its body writes type-check (rule 1) and the phase can classify the
   writer; an unannotated parameter is non-`Mut`, so writing it is rejected by rule 1. Carrying the
   annotation means store-ness is present in the type from the parameter inward through the whole
   pipeline — inlining, the phase, planning — with nothing to reconstruct.
3. **Loop routing is the phase's** (see [The unified phase](#the-unified-phase)): a `For` whose body
   writes a `Mut` store bound outside the loop is an accumulator recurrence; any other `For` (only
   feeds/yields, or writes to loop-local stores) is a plain map — rebuilt as the
   `Compose([iter, λ target → body])` generator shape. Transactional-context checks (a `Txn`
   register written outside `with begin():`, an induction store written inside one) are likewise
   post-inference, dispatching on `Mut`'s domain.

The payoff: lowering has one loop path and one write path, no `is_mutable`/`with_shadowed`
book-keeping, and no base-name scoping scaffolding — a shadowing parameter spelled like an outer
store is just a different binding with its own (non-`Mut`) type, handled by ordinary inference.

### `Mut` is a CCL type

`Type::History { value: 𝑉, domain: 𝐷, kind: HistoryKind::Store }` (displayed `Mut[𝑉, 𝐷]`) — a
wrapper variant carried on the introduction's binding and on every reference to it. It shares the
`Type::History` variant with a feed channel, distinguished by `kind` (see
[#1](#1-collapse-mut--feed-into-one-history-variant)); a store is the `Store` kind. Making mutability
a real type buys two things:

- **Pass-by-reference.** A function can take a mutable variable as a parameter
  (`def bump(c: Mut[Int]): c += 1`) and write *the caller's* variable. Because the unified phase
  runs after inlining, this needs no new machinery: beta-reduction substitutes the argument
  variable for the parameter, so the callee's `MutWrite`s land at the call site naming the actual
  store — the same route by which `Feed`-parameter UDFs work. The cross-function transactional
  writer falls out:

  ```python
  def transfer(src: Mut[Int, Txn], dst: Mut[Int, Txn], amt: Int):
      with begin():
          src -= amt
          dst += amt
  ```

- **Mutability survives α-renaming structurally** — a type rides the binding through every rename.

Typing:

- **Reads are implicit derefs**: `Mut[𝑉, 𝐷]` coerces to `𝑉` wherever a non-`Mut` type is demanded
  (a coercion arm in `constrain`, not structural subtyping). `cnt + 1`, `f(cnt)` for an `Int`
  parameter, and a trailing `cnt` all read; only a position that *expects* `Mut` (a `Mut`-annotated
  parameter) receives the handle. After inlining, no `Mut`-expecting positions remain, so the
  phase's rewrite is purely structural — every surviving `Mut`-typed occurrence is a write target
  or a read, decided by context.
- A parameter `Mut[Int]` means `Mut[Int, _]`; the domain instantiates per call site through the
  let-generalization of UDF bindings. Whether a write site requires `Txn` is the phase's structural
  check, post-inline — so one `bump` can serve an induction accumulator and a transactional
  register.

**No aliasing: `Mut` values are second-class (downward-only).** Passing a reference *down* is safe
exactly as long as the compiler can statically resolve which introduction every write targets. The
discipline:

1. A `Mut`-typed expression must be a **bare variable reference** — an argument to a `Mut`
   parameter is a variable, never a conditional or computed expression.
2. `Mut` may not appear **inside any composite type** — tuples, records, lists, function codomains
   (so it is never a return type), `Feed` payloads, or another `Mut`.
3. An **unannotated binding may not have `Mut` type**: `b = a` is an error, not an alias. To copy
   the current value, demand the deref (`b: Int = a`); to seed a *new* store from it, introduce one
   with `:=` (`b: Mut[Int] := a`, the initializer being a read).

One structural check after inference enforces all three. `Feed` deliberately stays more
first-class (it is returned in `http_serve`'s tuple): aliasing a feed is benign — multiple feeders
are already the semantics, merged by `++` — whereas a last-write-wins register needs its writer set
known statically.

`Mut`-parameter functions must reach their call sites, so they must be inlineable — the stance the
pipeline already takes for writers and `Feed`-mediating UDFs. (When general recursion lands,
recursive functions that don't fully inline need either the letrec treatment or a ban on `Mut`
parameters — deferred to that design.)

### `Feed` is a CCL type

`Type::History { value: 𝑉, domain: 𝐷, kind: HistoryKind::Feed }` (displayed `feed(𝐷 ⇒ 𝑉)`) — the
type of a feed handle: what a bare `out: Feed[_]` introduces, what `http_serve`'s response half
returns, what a defer-mediating UDF parameter (`λ out → out << e`) carries. It is the same
`Type::History` variant a store uses, under the `Feed` kind (see
[#1](#1-collapse-mut--feed-into-one-history-variant)); unlike a store it reads as its whole stream
`𝐷 ⇒ 𝑉`, not a scalar deref. Feed handles are fully first-class — returnable and tuple-packable —
because feed aliasing is benign (multiple feeders union by `++`). `desugar_defers` eliminates every
feed-typed term when it resolves channels, so no history type survives to planning.

### `Txn` is a CCL type

`Type::Txn` — the commit-time domain: an anonymous total order issued by the runtime. It is the
domain of transactional histories (`Txn ⇒ 𝑉`), the codomain of the `begin_<site>` oracles, and the
type of a transaction handle. Like a `DataSource` domain, it has no enumerable static extent; its
positions exist only in the tile.

### `LetRec`

```rust
LetRec {
    /// The mutually recursive definition group. Every binding's name is in
    /// scope in every binding's body (and in `body`). Each binding carries
    /// its full type (generated by the unified phase; always concrete).
    bindings: Vec<(TypedBinding, TypedExpr)>,
    /// The continuation, with the group in scope.
    body: Box<TypedExpr>,
}
```

Typing: with `Γ, 𝑏₁ : 𝑇₁, …, 𝑏ₙ : 𝑇ₙ` check each binding body against its declared `𝑇ᵢ` and
synthesize the letrec body as usual. The phase generates the binding types itself (from inferred
loop-source domains and value types), so the post-phase strict `typecheck` validates them directly.

**Well-formedness (guardedness).** In the reference graph over the group, an edge is *guarded* when
the reference is the history argument of a `get_prev_*` call; unguarded references must be
position-non-increasing (they pass the ambient position through, as `store(𝑡)` does inside the
commit record for time `𝑡`). Every cycle must contain a guarded edge — equivalently, the
unguarded-reference subgraph is acyclic. A structural check enforces this; op-conversion treats an
unrecognized unguarded cycle as a compile error rather than attempting fixpoint iteration.

`LetRec` is deliberately more general than mutability needs: `while` loops (recursion over a
condition-bounded prefix of `Nat`), recursively-defined collections, and general structural
recursion all target the same node.

Symbolic rendering: `letrec 𝑏₁ = 𝑒₁; …; 𝑏ₙ = 𝑒ₙ in body`.

### Builtins

| Builtin | Type | Meaning |
|---|---|---|
| `get_prev_seq` | `(𝐼 ⇒ 𝑉, 𝐼, 𝑉) ⇒ 𝑉` | history value at the predecessor of the given position; default at the first |
| `get_prev_txn` | `(𝐼 ⇒ {time: Txn, write: 𝑉}, Txn, 𝑉) ⇒ 𝑉` | write of the latest commit strictly before the given time; default if none |
| `begin_<site>` | `𝐼 ⇒ Txn` | the commit-time oracle for one `with begin():` site — where site `𝑠`'s iteration `𝑟` lands in the global commit order |

`begin()` never reaches CCL — lowering records the block structure, and the phase mints one
`begin_<site>` per site. The oracles are opaque, strictly monotone in arrival order (which is what
gives cross-endpoint external consistency), with pairwise-disjoint ranges; the commit engine
realizes them by tick allocation, not by computing anything.

Multi-variable atomic blocks produce one shared record `{time, writes: {𝑘₁: 𝑉₁, …}}` per commit,
and each variable's history reads it through a per-key view — atomicity by construction, since one
record either exists or does not. A conditional write (`with begin(): if 𝑝: x := 𝑒`) adds a
`commit: Bool` field that `get_prev_txn` filters on. Multiple writer sites for one variable merge
their commit streams (ordered by time) before the search.

## Compilation pipeline

```
CHL source
  → parse              (annotations incl. _, Mut[…]/Feed[…]/Txn forms, with begin())
  → lower              (direct mirror: For / MutWrite / Feed / Defer; Mut/Feed types from annotations;
                        NO store classification — every loop is a `For`, intro-vs-write is scope-only)
  → uniquify
  → infer + check      (on the direct-mirror tree; Feed[V] types the defers)
  → inline             (UDFs — incl. writers and defer-mediating lambdas — reach their call sites)
  → UNIFIED PHASE      (collect mutable state + route feeds + emit let/letrec;
                        eliminates For / MutWrite / Feed / Defer)
  → typecheck          (strict wall; the letrec rule)
  → lambda_elim → planning → simplify
  → operator_conversion (recognize letrec patterns → engines)
```

Inlining runs **before** the phase: a UDF that writes a `Mut` parameter or feeds a `Feed` parameter
is beta-reduced to its call site, where the phase sees its writes and feeds in the scope of the
store and channels they target. Generators survive inlining because direct-mirror lowering leaves
nothing to lose — a generator body is `For` + `Feed` nodes against an implicit result feed,
substituted wholesale.

### The unified phase

Input: a typed, inlined, direct-mirror tree. Output: `let`/`letrec` algebra with every
`For`/`MutWrite`/`Feed`/`Defer` eliminated. It:

0. **Normalizes to the flat-spine invariant** (`flatten_spine`). Inlining a pass-by-reference
   writer splices its body — a bare `MutWrite`, possibly a multi-statement `ExprStmt` chain — at
   the call site, which can bury a store write off the statement spine: under another `ExprStmt`
   (`bump2(cnt)` with a two-write body), as a `Let` bound-expression (`y = bump(cnt)`), or in
   terminal/value position (a trailing `cnt += 1`). Commuting conversions (gated on the moved
   effect being a `MutWrite`, so `Feed`/`Define` chains and unrelated `Let` subplans are untouched)
   push every write back to a direct `ExprStmt` effect; a value-position write terminalizes to
   `ExprStmt(MutWrite, unit)` (its store's final state is unobserved, so its value is `unit`).
   Downstream collection and read-your-writes rewriting then see only on-spine writes.
1. **Collects** the `Mut` introductions and each variable's writing sites (loops, `with begin():`
   blocks — post-inline, so writes through `Mut` parameters have landed), and each feed's sites.
2. **Resolves domains**: an induction variable takes its writing loop's source domain; a `Txn`
   variable takes `Txn`.
3. **Builds bindings**: per induction variable, the direct recurrence (in-context reads replaced by
   `get_prev_seq` / read-your-writes shadows); per `with begin():` site, a commit-record binding
   over the site's loop domain; per `Txn` variable, the history
   `λ 𝑡 → get_prev_txn(view, 𝑡, init)` over the (merged, per-key-viewed) commit streams.
4. **Routes feeds**: each channel becomes a letrec-body output — a function over its contributing
   loop's domain, unioned (`++`) across sites. A feed inside a `with begin():` block reads its
   value off the commit record (a per-commit tap).
5. **Routes loops and rewrites reads**: a `For` whose body writes a `Mut` store bound outside it is
   an accumulator recurrence (built in step 3); **any other `For` is rebuilt as its map shape** —
   `Compose([iter, λ target → body])`, with feeds/yields already routed in step 4 — so a generator
   or bare side-effect loop needs no letrec at all. Trailing induction reads → `last_or_default(history,
   init)`; a `Txn` read fed out of a read-only block → a broadcast of the store history over the
   enclosing loop, which planning latches through the as-of read.

Stateless programs never build a letrec — the phase degenerates to plain feed routing.

## Worked example

A transactional register and an induction counter shared across two HTTP endpoints:

```python
incr_reqs, incr_resps = http_serve("8080", "POST", "/incr")
get_reqs,  get_resps  = http_serve("8080", "GET",  "/get")

store: Mut[Int, Txn] := 0
cnt: Mut[Int] := 0

for req in incr_reqs:
    with begin():
        store += 1
        cnt += 1
    incr_resps << "ok {cnt}\n"

for req in get_reqs:
    with begin():
        get_resps << store
```

Note the mix: `store` is transactional; `cnt` is a plain induction accumulator *written inside* the
transaction block. That is legal — `cnt`'s writes sequence on the incr loop's induction domain,
independent of the commit order — and the lowering makes the difference literal. (A write to
`store` outside a `with begin():` would be rejected.)

After the unified phase (with `IncrIdx`/`GetIdx` the two request-source domains):

```
letrec
    store: Txn ⇒ Int =
        λ t → get_prev_txn(incr_commits, t, 0)

    cnt: IncrIdx ⇒ Int =
        λ r → get_prev_seq(cnt, r, 0) + 1

    incr_commits: IncrIdx ⇒ {time: Txn, write: Int} =
        λ r → let t = begin_incr(r) in
              {time: t, write: store(t) + 1}
in
    { incr_resps: λ r → incr_commits(r) ▷ (λ c → "ok " + cnt(r) + "\n"),
      get_resps:  begin_get ≫ store }
```

Reading it off:

- **`incr_commits`** — one commit record per POST. `begin_incr(𝑟)` is where request `𝑟`'s
  transaction lands in the commit order; `store(𝑡)` reads the snapshot (resolving, via `store`'s own
  definition, to the latest commit *strictly before* `𝑡` — no self-reference), and `+ 1` is the
  write.
- **`store`** — the register's history: at any `𝑡`, the latest earlier commit's write, else the
  initializer. The `store ↔ incr_commits` cycle is well-founded — the trip around it crosses
  `get_prev_txn` once, so position strictly decreases.
- **`cnt`** — the induction recurrence, self-guarded by `get_prev_seq`; its domain is `IncrIdx`, not
  `Txn`, because its annotation said so.
- **`incr_resps`** — the reply for `𝑟` depends on `incr_commits(𝑟)` (then discards it): the reply is
  sequenced after the commit, so a client that receives `ok 2` then GETs observes `≥ 2` (external
  consistency, given the oracles' arrival-order monotonicity).
- **`get_resps`** — the live read: assign the GET a commit time, read the store's history there,
  reply indexed by the GET request loop. No commit record, no write set — composition.

## Semantics

- **Serial denotation, concurrent engine.** The letrec denotes a *serial* execution: `Txn` is a
  total order, and each transaction reads exactly the prefix strictly before its own time.
  Optimistic concurrency — snapshots, backward validation, retry — is engine implementation,
  correct iff observationally equivalent to the serial denotation.
- **Atomicity is representational**: one commit record per block. There is no partially visible
  commit because no term denotes one.
- **Read-your-writes** within a block is `let` shadowing inside the record body.
- **Deny** (`if` around a write) is `commit: false` on the record; `get_prev_txn` skips it. A denied
  transaction contributes no visible write and no reply.
- **Induction and transaction domains are independent.** In the worked example `cnt` advances per
  request even though its write sits inside the block; only `Txn`-domain variables participate in
  the atomic commit. A program that needs the counter transactionally consistent with the store
  declares it `Mut[Int, Txn]`.
- **Liveness.** Induction domains are finite or stream-complete; `Txn` histories complete when all
  writer sources do. A terminal read resolves only on a complete history; a live read reads as-of
  its own position and does not wait for completeness.

## Op-conversion: recognizing letrec patterns

Recognition runs where the letrec meets the operator layer. It **must precede `lambda_elim`**,
because it keys on the pointful shape of the group, and op-conversion operates on lambda-free CCL —
so it cannot re-derive a recurrence from a point-free tree. The recognized recurrence therefore
travels to op-conversion on a **carrier node**, the domain-parameterized
`Transact { keys, writers, domain }`: explicit key/writer header slots plus an opaque writer-body
lambda, which is exactly what lets `lambda_elim` point-free the body, `planning` iterate-wrap the
writer source, and op-conversion build the engine. One carrier serves both domains — there is no
separate loop node.

Recognition is anchored on the builtins (`get_prev_seq`, `get_prev_txn`, `begin_<site>`) — opaque,
like aggregates, so `lambda_elim`/`planning`/`simplify` normalize *around* them without destroying
them.

| Letrec pattern | Engine |
|---|---|
| a binding referenced only via `get_prev_seq(𝑏, …)`, over a finite/stream induction domain | `Recurse` — the sequential loop engine |
| commit-record bindings + `begin_<site>` oracles + `Txn` histories read via `get_prev_txn` | the commit operator (`CommitOperator`, `TransactWriter`, cyclic `FanOut`, `StoreValueStream`) |
| a `Txn` history read out of a read-only block (`begin_<site> ≫ store`) | the as-of read (`AsOf`), latching the store's latest-decided commit, indexed by the outer trigger loop |
| an unguarded cycle, or a guarded shape the recognizer does not know | compile error (no silent fallback) |

### The runtime engines

- **`Recurse`** — the induction loop. It emits the prev-accumulator stream `𝐷 ⇀ 𝑉` (`init` at
  position 0, the body's output at `𝑖-1` for `𝑖 > 0`), internalizing the cycle in a cyclic `FanOut`
  so the static operator graph stays acyclic. A single always-commit writer over a finite domain.
- **The commit operator** — the concurrent generalization of `Recurse`, for the `Txn` domain. The
  store is an MVCC commit log `Txn ⇀ (Key ⇀ Value)`. A writer reads a snapshot of its footprint,
  runs its pure body, and proposes `{reads, writes}`; the operator validates the read set against
  the current store (backward / optimistic concurrency) *before* allocating a timestamp — a valid
  proposal commits and consumes a tick, a stale one is skipped and retries against the advanced
  snapshot. Disjoint footprints commit concurrently; overlapping ones serialize. `release` is the
  commit acknowledgment (the retry signal rides the existing producer/consumer channel). The store
  compacts by the MVCC law and GCs the released prefix.
- **`AsOf`** — the as-of (temporal) join, for a live cross-endpoint read. Given a *trigger* (the
  request stream — the positions to sample at) and a *source* (a store's `StoreValueStream`), it
  latches, for each trigger position, the source's latest-decided value at the moment that position
  is first observed. The output is indexed by the **trigger** (the outer request loop), not the
  commit clock — which is why a live reply matches its request by position and needs no explicit
  correlation id. It is the dual of the commit `Recurse`: `Recurse` latches a private accumulator
  per source step; `AsOf` latches a foreign stream's head per trigger step. The terminal read is
  the degenerate case — a standalone read-only transaction's singleton trigger latches the final
  committed value.

The two loop engines are **not interchangeable**: the commit operator is built for an open commit
clock and mis-drives an incremental/live source, while `Recurse` is the ordered loop recurrence.
Dispatch on the sequencing domain is load-bearing, not an optimization.

### Watermarks

A consumer reading "as of `𝑡`" must know no further commits will land at `≤ 𝑡`. The runtime already
carries this: function tiles hold a `domain_predicate` marking the complete region of the domain. A
watermark *is* a `domain_predicate` advancing over `Txn`. Conflict validation — which depends on
which value combinations were observed — is deliberately engine-level, above the tiling algebra,
because that is exactly what extent predicates cannot express.

## Concurrency and distribution

The transactional case is the concurrent sequencing domain, and most of it falls out of the
algebra: out-of-order commits are fine (`⊕` is commutative; writes at distinct timestamps are
compatible tiles), and watermarks are `domain_predicate`s over `Txn`. What is *not* in the algebra
is conflict validation (read-set dependence), which is the engine's job. The design generalizes to
distributed execution with no model change: the compiler knows the full set of writes a transaction
*could* perform, so distributed commit can be decided from complete local knowledge rather than a
two-phase handshake. Serializable is the default (working hypothesis: the only level needed), made
affordable by that complete compile-time knowledge.

## Future work

- **`while` loops** — a letrec binding over a condition-bounded prefix of `Nat`; the self-ceiling
  domain is a new *domain*, not a new construct.
- **Nested `for` loops** — lexicographic product domains; data-dependent bounds meet the
  refinement-types work as dependent sums.
- **Mutable collections** — sigma types (`List[𝑇] = Σ 𝐼 . 𝐼 ⤇ 𝑇`) as letrec bindings; the
  append-only `Appendable` case first, as a commit stream whose history *is* the collection. This
  is also what first-class `Mut` (returning or storing references) needs: carrying store identity in
  types is a sigma/index-types question. Until then the second-class discipline is the aliasing
  firewall.
- **History access / auditing** — `get_prev_*` generalized to user-facing reads at explicit
  positions; the transaction handle (`t = begin()`) already names the position.
- **Recursively-defined values** generally — the `LetRec` node and guardedness check are the general
  mechanism; only recognition patterns need to grow.

## Planned simplifications (representation unification)

The features above add domains and recognition patterns to the *same* machinery. These entries
instead **collapse representations** — closing the gap between the "one model" this document opens
with and an implementation that still carries mutation, feeds, and their carriers as separate
constructs. They are design-of-record for work not yet done; ordered by dependency.

### 1. Collapse `Mut` / `Feed` into one `History` variant

**Status: implemented.**

`Type::Mut { value: 𝑉, domain: 𝐷 }` and `Type::Feed(𝐷 ⇒ 𝑉)` were the same object under two names —
an invariant, deref-transparent `𝐷 ⇒ 𝑉`. During inference they *already* behaved identically: the
constraint solver treated both invariant and rejected a plain value flowing into a feed (the
`NotAFeed` write guardrail is the `Feed` half of what
[`check_mut_write_targets`](#store-ness-is-the-type-no-lowering-registry) is for `Mut`). Neither the
`Mut`/`Feed` split nor the pair of variants was load-bearing.

**Done:** `Type::Mut` and `Type::Feed` are deleted, replaced by one
`Type::History { value: 𝑉, domain: 𝐷, kind: HistoryKind }` where `HistoryKind` is `Store | Feed` — a
function `𝐷 ⇒ 𝑉` plus a two-valued marker. `Store` is a mutable store (deref-on-read to the scalar
`𝑉`, carry-forward terminal, scalar-last read); `Feed` is a feed channel (read as the whole stream
`𝐷 ⇒ 𝑉`, stream terminal). Lowering stamps `Store` on a `:=` introduction and `Feed` on a `defer`;
the store histories are erased to a bare `Type::Fun` by the unified phase (`letrec_phase` /
`transact_phase`) and the feed histories by `desugar_defers` — exactly as `Mut`/`Feed` were erased
before — so no history type survives to planning and "later stages are just `Fun`" holds. (A
`history` *field* on the universal `Type::Fun` was considered and rejected: it would thread a
rarely-set marker through ~150 construction sites — every lambda, collection, and morphism — and
muddy the most-used type in the IR. The dedicated variant keeps the history concern localized while
remaining, exactly, "a function plus a marker." A `bool` was likewise rejected for a named enum:
`HistoryKind::Store` / `::Feed` reads at every match site instead of a bare `true`/`false`.)

The two `kind`-distinguished responsibilities stay *on the type*, threaded uniformly through
inference, compaction, and coalescing:

- **Operator discipline** — `<<` / `<<=` may target only a `defer`-introduced channel, and
  `:=` / `+=` only a `:=`-introduced store. This is kept as the **type-level** guardrail (design
  decision: "(a) is ok for now"): the invariance `constrain` arm matches only *same-kind*
  `History`/`History` pairs, so a store demanded as a feed (or vice versa) falls through to the
  `NotAFeed` arm — a `<<` into a `:=` store is a type error, no separate structural check needed.
- **Read mode** — a store's trailing read derefs to the scalar `𝑉` (`last_or_default`); a channel's
  is the whole stream `𝐷 ⇒ 𝑉`. The `constrain`/`coalesce` deref arms dispatch on `kind`: a `Store`
  history meeting a demand derefs to `𝑉` *before* the `Infer` arms (so a store var coalesces to its
  value), while a `Feed` history is read through to the reconstructed `𝐷 ⇒ 𝑉` and, alone at a
  position, keeps its constructor (so a feed var coalesces to a feed).

**`<<=` requires a collection RHS.** With the collapse there is no scalar `Feed` payload to
accommodate: `<<=` (define a channel to a whole collection) and `<<` (feed one element) both yield a
`𝐷 ⇒ 𝑉` history. A scalar `𝑑 <<= 𝑒` is a **type error** — the scalar `𝑒` fails to align with the
channel's `𝐷 ⇒ 𝑉` stream, caught by inference with no dedicated lowering check (use `=` for a plain
scalar binding); the genuine use — cross-channel forward references, `𝑥 <<= 𝑦; 𝑦 <<= [ … ]` — is
unaffected, since a feed RHS reads through to its stream.

This is the enabling step for the next two: with feeds and mutation sharing one type, a defer
channel is simply a `Feed`-kind letrec binding, read as a stream instead of scalar-last.

### 2. Unify conditional writes and conditional feeds (one fan-out)

**Status: feed half landed; write half is an open question.** The N-arm conditional *feed* fan-out
is implemented: a feeding `if`/`elif` in a for-loop body fans out to one refined-source channel per
feeding arm, restricted to `gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ` (first-match order) and unioned via `++`
(`synthesize_arm_predicate` / `try_extract_fanout_feed` in `desugar_defers`; the `elif`-in-generator
lowering gate is lifted). Conditional *writes* are **not** landed, and the sketch below turns out to
under-specify them: a store is a **shared recurrence** — every arm reads `get_prev_seq(total, 𝑟)`, so
the arms are *not* independent. The literal `⧺`-union with a carry-forward arm therefore has a
cross-arm dependency (the taken arm needs `total` at the off-path positions and vice-versa) that a
plain union cannot compute — the `Recurse` engine would have to interleave the arms in domain order.
The alternative — a value-`Case` recurrence step — is rejected by `lambda_elim` (only the 2-arm
filter shape `{𝑔 → action; true → unit}` → a *restricted* source survives, which drops the off-guard
positions: correct for a partial feed, wrong for a total store). So enabling conditional writes needs
new machinery (a `lambda_elim` extension for the carry-forward step, or engine interleaving) — not
the mechanical reuse this section implies. The unification is real at the **predicate** level (both
use the path-condition fan-out); it is the store's carry-forward that is not a mere extra union arm.

A conditional write (`if 𝑝: total += x`) carries the previous value forward off-path; a conditional
feed (`if 𝑝: o << x`) is absent off-path. These are **not two mechanisms** — both are the same
refinement fan-out over the branch path conditions, which is exactly the value-`Case` lowering the
N-arm-Case-with-feeds gap already needs:

```
target  =  ⧺ᵢ (source | 𝑝ᵢ ≫ (λ 𝑟 → 𝑣ᵢ))
```

Each arm is a *filter* `Case` (the `source | 𝑝ᵢ` restriction) composed with the arm's value — both of
which compile today, so the monolithic value-`Case` that "errors at `lambda_elim`" never has to
exist; it is fanned out into unioned filters before it gets there. **`elif` / `else` need no
complement-refinement machinery.** Because CHL has boolean operators, a later arm's predicate is
synthesized by conjoining the negations of the earlier ones — `else` is just one more arm with the
synthetic predicate `¬(𝑝₁ ∨ … ∨ 𝑝ₙ)` — so every path, `else` included, is an ordinary
boolean-predicate filter.

The **only** difference between a store and a channel is one extra arm. A guarded target (a store)
appends a **carry-forward** arm over the `else` (complement) domain:

```
total  =  ⧺ᵢ (source | 𝑝ᵢ ≫ (λ 𝑟 → 𝑣ᵢ))  ⧺  (source | ¬⋁ᵢ𝑝ᵢ ≫ (λ 𝑟 → get_prev_seq(total, 𝑟, init)))
```

An unguarded target (a channel) omits it, so its history stays partial (absent off-path). That extra
arm *is* the guardedness — the same `HistoryKind` (`Store` / `Feed`) marker
[#1](#1-collapse-mut--feed-into-one-history-variant) puts on the history. So #2 is the
**conditional generalization of #1**, not a separate unification:
the fan-out reads the history marker to decide whether to emit the carry-forward arm, and one
lowering then serves conditional writes, conditional feeds, and the transaction deny-guard (whose
`commit = ⋁ᵢ𝑝ᵢ` is this fan-out's taken-path disjunction — the store advances on the write arms and
carries forward on `¬commit`; feeds fire on their arms and are absent otherwise).

Two consequences: **domain totality is not a separate property** — "store total / channel partial" is
exactly the presence or absence of the carry-forward arm. And **multi-site channels** (`o << x` in one
loop, `o << y` in another) are just more union arms, so the current `++` cross-site channel assembly
in `desugar_defers` is the same fan-out — which is how a defer channel folds into the letrec model.

### 3. Retire the `Transact` carrier; keep `LetRec` through op-conversion

*(Depends on 1 and 2.)* `Transact` exists only to carry the recognized recurrence across
`lambda_elim` (recognition is pointful; op-conversion is lambda-free). But recognition anchors on
the guard builtins, which *survive* `lambda_elim` — so recognition could run on the point-free
`LetRec` directly, letting one `LetRec` (bodies point-freed, group intact) travel to op-conversion
and retiring `Transact` as a second representation of the same group.

### 4. Retire `desugar_defers`: feeds lower through the unified phase

**Status: in progress.** Landed so far:

- The entire defer-mediating-UDF machinery (the Phase-1 chain rewriter, lambda classification,
  DI-chain wrapping, return-Record body rewrite, and the call-site smart walker, ~1700 lines) is
  deleted. It was dead against every real program: `inline` beta-reduces every defer-mediating UDF at
  its call site *before* desugar runs, so desugar only ever sees flattened `let d = defer in …`
  chains. `desugar_defers` is now a single-phase cluster channelizer.
- The conditional feed (`if guard: d << v` in a loop) compiles end-to-end, now generalized to the
  **N-arm** (`if`/`elif`) case: each feeding arm `i` fans out to a refined-source channel with the
  *bare element predicate* `__elem ▷ source ▷ (λ p → gᵢ ∧ ¬⋁ⱼ<ᵢ gⱼ)` — the same element form a
  filtered comprehension `[v for p in source if guard]` builds ([`lower::comprehension`]), fully
  typed at construction (a `Refinement` predicate is immutable, so `retype` never re-derives it) —
  and the channels are unioned via `++`. Planning reifies each into an `IterateExtent` + `Restrict`.
  The `elif`-in-generator lowering gate is lifted; the former two-arm `try_extract_filter_feed` is
  the degenerate one-feeding-arm case of `try_extract_fanout_feed`. This completes the feed half of
  [#2](#2-unify-conditional-writes-and-conditional-feeds-one-fan-out).

**Remaining:** relocating the live channel assembly — feed extraction, `++` union, topological
ordering, α-renaming, defer-returning normalization, and channel-domain resolution — into the
sequencing phase so `desugar_defers` disappears entirely, and `retype` with it. This is the large
refactor the rest of this section targets. `retype` is heavily load-bearing on the *current* desugar
(with it disabled, ~all feed and generator programs fail the strict post-desugar typecheck), so it
can only be retired once the relocated assembly is type-preserving *by construction* — as the
conditional-feed fan-out already is. Conditional *writes* (the store half of
[#2](#2-unify-conditional-writes-and-conditional-feeds-one-fan-out)) stay gated at lowering pending
that section's design resolution.
The rest of this section is the target design.

*(Depends on 1 and 2; the payoff the whole unification is for.)* `desugar_defers` is a bespoke
*second* lowering of exactly the machinery the unified phase already runs. It walks a cluster of
`let d = defer` bindings, extracts every `<<` / `<<=` contribution, assembles each channel as a `++`
of its per-site contributions, topologically orders the cluster's cross-referencing bindings,
α-renames the channel downstream of the wrap site, and finally re-synthesizes the types it disturbed
(`retype`). Once a defer channel is just a `Feed`-kind history (#1) and a conditional feed is just a
fan-out arm (#2), every one of those steps has a counterpart on the store path:

- **Feed extraction + channel `++` assembly** is the conditional fan-out of
  [#2](#2-unify-conditional-writes-and-conditional-feeds-one-fan-out) with no carry-forward arm — a
  channel is `⧺ᵢ (source | 𝑝ᵢ ≫ (λ 𝑟 → 𝑣ᵢ))`, absent off-path, which is what a `Feed` history's
  partial domain already means.
- **Cluster topological ordering** (and cross-cluster sequencing) is the `LetRec` group plus the
  guardedness ordering `letrec_phase` already builds — a defer that references another is just a
  later group member, no separate wrap.
- **`Infer` channel-domain resolution** (the Unit thunk / source / `Variant` union a channel's
  domain coalesces to) is each fan-out arm's `source` domain, unioned into the same `Variant` the
  fan-out already produces.
- **`retype`** is *not needed*: the fan-out is built type-preservingly, exactly as `letrec_phase`
  emits a well-typed `LetRec` by construction, so there is no residue to re-derive.

So `defer` lowers to an (unguarded) `Feed`-kind history binding and `<<` / `<<=` to feed statements
the fan-out folds into that binding, read as a stream; feeds then travel the same
`For`/`MutWrite` → unified phase → `LetRec` → recognition road as stores, differing only in the
`HistoryKind::Feed` marker and the absent carry-forward arm. The whole `desugar_defers` module — the
cluster algorithm, channelization, α-renaming, and `retype` — is deleted. The one currently-ignored
gap (the filter-feed refined-source case `retype` cannot re-derive) disappears with `retype` itself,
because there is nothing left to re-synthesize.

## Implementation status

Working end-to-end: induction accumulators and generators (`Recurse`); feeds, including per-commit
feeds inside a transaction block; batch transactions over finite sources — single- and
multi-variable, atomic multi-write, conditional grant/deny, read-your-writes; the cross-function
transactional writer `def transfer(src, dst: Mut[_, Txn], amt)` applied to two registers (a
multi-`Mut`-parameter pass-by-reference writer, inlined to name the caller's stores); and live
cross-endpoint reads (the `AsOf` path). **Both** the induction and transaction paths are genuinely
letrec-based, and share one representation: `For`/`MutWrite` → the unified phase → a guarded
`LetRec` → recognition → `Transact` → engine. The induction path guards with `get_prev_seq` (→
`Recurse`); the transaction path (`transact_phase`) emits the `get_prev_txn`-guarded `store ↔
commits` cycle of the worked example — one history binding `store_k = λ t → get_prev_txn(view, t,
init)` per key, one commit-record binding `commits_j = λ r → let t = begin(r) in {time,
write_targets, decision}` per `with begin():` site (the decision is the writer body applied to the
store snapshot `(store_rk(t) …, source(r))` at the commit time `begin(r)`) — and recognition
(`letrec_phase::recognize`) destructures it back into the `Transact{domain: Txn}` the commit engine
consumes. Two HTTP programs run over a real server: `http_accumulator` (an induction accumulator
replying per request) and `http_counter` (a `POST` writing a `Txn` register, a `GET` reading it
live).

The `begin_<site>` oracle is realized as a single shared `Builtin::BeginTxn` applied once per site
(the site identity recognition needs — the writer's source stream and iteration domain — lives in
the commit-record binding, not the oracle). Like `get_prev_seq`/`get_prev_txn` it is minted after
inference, carries no inference scheme, and is consumed by recognition before op-conversion (a
deliberate op-conversion error arm guards the invariant).

The commit log is **bounded** under live workloads. Every writer releases its store branch — a
collection-append (empty read set) releases the whole decided prefix; a register drawdown (non-empty
read set) releases strictly below the oldest tick it read — and the `FanOut`-intersected
`gc_released_prefix` reclaims the released prefix (always keeping each key's latest write). A live
`AsOf` reader still pins its own branch while active (it may answer an as-of query at any past
request position), so a store that is *only* read live retains its history; a store with a writing
endpoint sheds its superseded prefix.

Realized on this branch:

- **The store `Type::History` is first-class; induction store-ness is the type, transactional identity is the type.**
  Mutability rides the introduction's binding and every reference as
  `Type::History { value, domain, kind: Store }` (displayed `Mut[value, domain]`, so
  it survives α-renaming structurally), reads deref through the coercion arm, and the second-class
  discipline is enforced post-inference (`check_mut_discipline`). Both introduction forms stamp the
  binding: `x: Mut[V]` → `Mut[V, _]` (induction, domain inferred to the writing loop's extent) and
  `x: Mut[V, Txn]` → `Mut[V, Txn]` (a transactional register).
- **The lowering-side *induction* registry is gone.** `mutable_vars` and its `is_mutable` / `register` /
  `snapshot` / mask machinery are deleted. Lowering makes only scope-based choices: a `:=` to a fresh
  name is a `let`-`Mut` introduction, a `:=` / `+=` to an in-scope name is a `MutWrite`; loop routing
  is `find_mutation_loop_vars` (scope-only). A write to a non-store is a post-inference type error
  (`check_mut_write_targets`), so `x = 0; x += 1` is rejected, never a shadow.
- **Pass-by-reference writers** work for **both** induction and transactions, single- and
  multi-parameter: `def bump(c: Mut[Int]): c += 1` and
  `def transfer(src, dst: Mut[Int, Txn], amt): with begin(): …` lower their bodies to `MutWrite`s on
  the `Mut`-typed parameters, and the call beta-reduces at the call site, renaming each write target to
  the caller's store. A multi-`Mut`-parameter function is lowered — and applied — *curried* (a chain of
  named lambdas) rather than tupled, because a `Mut` parameter must stay a named binder for that rename
  (a tuple projection cannot be a `MutWrite` target); such functions are always inlined, so the curried
  chain never reaches `lambda_elim`. `transact_phase` identifies transactional stores by the
  `Mut[_, Txn]` type on the **α-unique binding** (`collect_txn_stores` over the inlined, typed tree —
  which sees cross-function writers' stores and is immune to a local merely spelled like a register),
  *not* by a base-name registry.
- **A transactional-only registry survives at lowering — by necessity, not as a bridge.** Unlike
  induction store-ness, which the post-inference store-`Type::History` check recovers, a `with begin():` block's
  structure is *erased* by lowering: the `MutWrite`-vs-`Let` shape decision inside a block, the loop's
  `with begin():` classification, and the out-of-block read/write gate all have to be made at lowering
  time, when the block scoping is still visible. These are driven by a small `transactional_vars` set
  (base-name keyed, scope-disciplined via `snapshot_transactional` and the `with_shadowed` shadow
  stack) that records only `Mut[_, Txn]` registers and is *not* handed to the phase (which keys on the
  type). The induction dual — an induction store written *inside* a block, which the phase would
  swallow — is rejected at the block-body write site (`transactions::write_or_let`) with no registry at
  all: inside a block the only legal `:=` / `+=` target is a transactional register, so a
  non-register, non-shadowed write is always the error.
- **Loop routing takes the scope-only form**, not the fuller "every loop is a `For`" of
  [Store-ness is the type](#store-ness-is-the-type-no-lowering-registry): a loop that writes an
  outer-scope name lowers to a `For`, a pure generator/side-effect loop still lowers directly to
  `Compose` (`lower_generator_for`). This is registry-free (for induction) but keeps two loop paths at
  lowering.
- **Reads require a `with begin():` block for `Txn` variables**, and the terminal read is the
  standalone read-only transaction's as-of read — there is no separate terminal-read operator.
- **The in-transaction guard is deny-only** (implemented); general conditional logic is designed
  but blocked on a missing primitive. Today a bare `if 𝑝: …` is a deny guard (the transaction
  commits iff `𝑝` holds over its snapshot); an `elif` chain or an `else` that writes is rejected at
  lowering. The **intended** end state is a uniform *path-based* model: walking a block threads a
  path condition (a branch guard `𝑔` extends it to `path ∧ 𝑔`), and the block denotes
  `snapshot ⇒ {commit, writes, to_<defer>*}` where **`commit` is the disjunction of the
  path-conditions of every store-write and feed** (an empty taken path — no write or feed, including
  a missing `else` — denies), and **each write key is a `Case` merged over the branch structure**
  (read-your-writes; a branch that doesn't write a key keeps its snapshot value). This is
  keyword-free, subsumes the current deny (`if 𝑝: x = 𝑒` → one write at path `𝑝` → `commit = 𝑝`),
  and admits value-selection, cross-key routing, `elif`, nesting (conjunction) and sequencing
  (independent commits). One restriction rides with it: a reply must be delivered on *every*
  committing path (fed on all committing branches); conditional reply *presence* would need a
  tap-present flag in the decision record.
  **Blocker:** the model needs a *value-selecting* `Case` (`x = if 𝑝: 𝑒₁ else: 𝑒₂`) to be a
  compiled construct, but only the *filter* `Case` (`[𝑔 → action, true → unit]` → `Restrict`)
  compiles today; a value `Case` errors at `lambda_elim`. This is the same missing primitive as the
  **N-arm Case-with-feeds gap** (`docs/plan.md`; `multi_arm_case_with_some_feeding_branches_is_a_known_gap`),
  whose planned fix — refinement-based fan-out, lowering a value `Case` to a union of restricts
  `⧺ᵢ (source | pathᵢ ≫ 𝑒ᵢ)` — unblocks both the feeds gap and transaction conditionals. Deferred to
  that work; `transact_phase` then emits the `Case`-merged decision (recognition lifts it verbatim,
  so it needs no change).
- **Multi-register *live* reads are snapshot-consistent.** The model (§"Reads") promises that
  several `Txn` reads in one `with begin():` block observe *one* commit snapshot. A **multi-register
  live** read — a live reply reading two registers, `resp << a + b` — is served by a **single bundled
  `as_of((trigger, __store))`** over the whole store: `transact_phase::rewrite_live_reads` collects
  the chain of live reads feeding the reply and, when the reply reads more than one register, emits
  `as_of((trigger, __store)) ≫ (λ snap → e[a ↦ snap.a, b ↦ snap.b])`. The record-valued `AsOf`
  latches a whole-store **snapshot record** per request, folding every field from *one* source render
  at one commit frontier (`store_current` over the same `Tile::Store`), so `a` and `b` are read
  atomically; the reply projects each register off the latched snapshot. This preserves the **outer
  (request) indexing** an `AsOf` gives. A single-register read stays a scalar `AsOf`; a batch read
  (`[unit]` trigger) still resolves through the terminal `ExtractLast`. What remains unsupported is a
  reply that combines the request element *with* a store read (`resp << store + req`): the response is
  then a function of both the trigger and the store, wanting a `zip(trigger, as_of)` shape, so
  `check_live_reads_resolved` **rejects** it (a surviving used live `last_or_default` beside a live
  `DataSource`-triggered broadcast) rather than emitting a silent hang.

  **Live-read recognition moved into `transact_phase` (pre-lambda-elim).** It previously lived at the
  *end of planning* (`planning::rewrite_live_reads`), matching the point-free `iterate(B) ≫
  const(page)` broadcast — which forced a **computed** live read (`resp << store + 1`, whose
  const-arg is `page + 1`, not a bare `page`) to be *rejected* by a `check_live_reads_resolved`
  band-aid, because lifting the `+ 1` back into a per-request map after lambda elimination would mean
  synthesizing a combinator by hand. Recognizing the reply `let x = last_or_default(…) in trigger ≫
  (λ r → e)` *before* lambda elimination keeps `e` a lambda: the rewrite emits `as_of((trigger,
  store_k)) ≫ (λ x → e)` and the elim pass point-frees `e` for free, so computed live reads now
  compile. `planning::rewrite_live_reads`, `make_as_of`, `match_live_read`, and
  `check_live_reads_resolved` are retired; planning's `insert_iterate_markers` /
  `is_iteration_bearing` treat `as_of` as an iteration-bearing source (staging the trigger inside its
  tuple, never prepending an `iterate`).
- **Not yet implemented**: `while` loops (parse error today), nested `for` loops with loop-carried
  variables, mutable collections (pending sigma types), and history/auditing reads.
