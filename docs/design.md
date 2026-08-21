# Cambra

Cambra is a programming language that implements a new programming paradigm.
It abstracts over concepts like memory, threads, connections, filesystems, and databases, enabling programmers to focus on the logic of their program, non-functional requirements, and high-level architectural decisions.

This document is the guided tour: the language's important features, the architecture underneath them, and how the two connect. It sits between the [README](../README.md) (what Cambra is and why it exists) and the deep documents — the [CHL specification](chl-spec.md), the [operational semantics](operational-semantics/summary.md), and the per-module design docs indexed in [src/design.md](../src/design.md).

## How to read this document

**Unmarked text describes what the compiler implements today.** Everything aspirational carries a marker:

- **[Planned]** — well-understood, near-term work.
- **[Decided]** — a recorded design decision, not yet implemented.
- **[Sketched]** — an in-progress sketch; expect it to change. (The [spec](chl-spec.md) spells this marker **[Tentative]**.)
- **[Open]** — a known question with no answer yet.

When in doubt, [demo-programs.md](demo-programs.md) is the ground truth: every claim about "what runs" is pinned there by an executable program and a test.

## The shape of Cambra

A Cambra program passes through three layers:

1. **CHL** (Cambra High-level Language) — the surface syntax a programmer writes.
    - The syntax is inspired by Python.
    - The language has a powerful, structural type system.
    - Formal verification is supported through SMT-checked static assertions. *[Sketched]*
    - Collections and functions are first class (lambdas, comprehensions, generators).
    - Concurrency and parallelism are the default. *[Decided]*
    - Durable state *[Sketched]* and transactions are built in.
2. **CCL** (Cambra Core Language) — the small core CHL lowers into: literals, variables, tuples, records, collections, lambdas, let-bindings, application, aggregates, and recursion. CCL is pure and referentially transparent — CHL's impure surface forms (`:=` mutation, `<<` feeds) are compiled away into pure recursion over time domains, so every CCL node denotes a value. After inference every node carries a type. This is the language's reasoning surface: type checking, optimization, planning, and program comparison all happen here.
3. **Dataflow runtime** — CCL is converted into a graph of _operators_ implementing a producer/consumer interface; a scheduler drives the graph with streaming dataflow semantics. Parallelization *[Sketched]*, vectorization, pipelining, transactionality, and durability *[Sketched]* are properties of the execution model rather than features provided in libraries.

Programs are run on the Cambra engine, which compiles and executes CHL programs. This engine provides the operational tooling to interact with a CHL program:
- An **Inspector** to observe and debug running programs.
- Commands to run and kill programs. *[Open]*
- The ability to create a **branch** of a running program, cloning its state and running a new program version using that cloned state. *[Open]*

## The language

### Types: inference and refinement

CHL supports full type inference, so all type annotations are optional. Its type system brings together **structural subtyping** ("if it has the right shape, it works") and **refinement types** ("a type such that its terms satisfy a given predicate"). The type checker is a constraint-based inference engine over the whole program — emission, solving, and coalescing are described in [src/ccl/design/type-inference.md](../src/ccl/design/type-inference.md). Base vocabulary: `Int`, `Bool`, `String`, unit, `List(T)`, tuples, records, variants (AKA "sum types" or "enums" — written `` {`some{Int} | `none} ``, constructed `` `tag(payload) ``, matched with `match` — [docs/chl-spec.md](chl-spec.md#65-variants)), and functions.

**Refinement types** look like this: `{𝑥: 𝑇 | 𝑝(𝑥)}` — a value of the base type for which a predicate holds. The machinery is implemented inside the checker today — basic refinement inference, constraint solving over refined subtyping, explicit refinement acquisition, and specialization of polymorphic call sites — and built-ins like `groupby` produce refined types internally. What does **not** exist yet is the surface syntax: the CHL spelling is `{T where p(_)}`, which drops the named binder in favour of `_` for the refined value ([docs/chl-spec.md](chl-spec.md#64-refinement-syntax)) and is **[Decided]** but not in the grammar. Verifiable, whole-application contracts expressed through refinements are the driving design direction rather than a current capability. The `{𝑥: 𝑇 | 𝑝(𝑥)}` form above stays the *internal* notation — a dependent codomain refinement has to name the binder it closes over — so it is what compiler output and the CCL design docs show.

### Functions

Functions are defined like in Python, with optional type annotations. They are first-class, and capture their environment lexically. Every function takes exactly **one** argument (*[Decided]*) whose product structure carries the arity: an n-parameter function is a function on a tuple, and a keyword-argument function is a function on a record — `f(x=1, y=2)` *is* `f` applied to the record `(x=1, y=2)`. Curried functions are supported, but not considered best practice.

For example:

```python
def repeat(n: Int, y: String) => String: # return type syntax is [Sketched]
  z := "" # Muts inside fn bodies are [Planned]
  for i in range(n): # range is [Planned]
    z += y
  return z
```

A `Mut(_)` parameter annotation gives pass-by-reference access to a caller's mutable variable, under a deliberately *second-class* discipline — mutables flow down into calls but are not returned or stored in data structures (see [src/ccl/design/mutability.md](../src/ccl/design/mutability.md)). Captures of ordinary bindings are read-only. Captures of transactional variables are **[Decided]** (§8 of the [spec](chl-spec.md)).

### Collections are unordered

In CHL, collections have no inherent ordering. By default, a `for` loop's iterations may run in **any order, including in parallel**. The only way to sequence iterations is to create data dependencies between them. For example, using a mutable variable in a loop (`acc += i`) creates a data dependency from one iteration to the next, and that dependency serializes the loop according to its natural ordering. Transactions allow different iterations of a loop to operate on the same state without imposing a predefined order on them. This contract lets the runtime parallelize by default instead of by annotation.

Lists do carry an integer *addressing* structure (`xs[i]` is well-defined), but ordering is only observable when program logic depends on it. Similarly, sources have a real *arrival* order, which is the natural ordering when iterating them. 

> **Direction [Sketched].** The target collections model is more nuanced: `Array` and `List` become genuinely ordered, while `Set`, `Map`, and `Collection` stay unordered, with order-dependent operations taking their ordering explicitly as a contextual instance.

### Comprehensions and generators are the query language

Comprehensions and generators are CHL's primary collection-level construct — what `SELECT … FROM … WHERE …` is to SQL:

```python
[ (customer=u.name, total=o.amount) # `(=,)` record syntax is [Decided], currently `{:,}`
  for u in users
  for o in orders
  if u.id == o.user_id ]
```

A comprehension denotes the bag of element evaluations over the cross-product of its `for` clauses, filtered by its `if` guards. A guard that depends only on outer variables *prunes* the inner product — a semantic requirement, not an optimization. Over an unbounded source the comprehension is streaming: it produces elements as inputs arrive.

A `def` whose body contains `yield` is a **generator function**: calling it produces the bag of yielded values, lazily, so a generator over `stdin()` is an unbounded stream. Today the compiler restricts generator bodies to a single top-level `for` loop (general shapes are **[Planned]**).

The compiler recognises comprehension shapes and emits specialised dataflow: an equality guard between two clauses compiles to a **hash join** rather than a nested loop, and `for g in groupby(c, key)` produces a **keyed aggregate** dispatch. Users get query-planner behaviour from ordinary language constructs — there is no embedded query DSL to switch into.


### Sources, sinks, and feeds

Programs interact with the world through **sources** (`stdin`, `http_serve(...)`) and through **sinks** (`stdout`, http responses).

Sources are simply collections of data that comes in from outside of the program.
As more data comes in to a source, its corresponding collection grows, and expressions defined over that collection can proceed with their computation.

Sinks are collections of data that go out of the program. They are defined as expressions over sources, and eventually compiled into terminal nodes in the program's dataflow graph.

CHL provides a primitive called **feeds** to make it ergonomic to define append-only collections (such as sinks). Given a feed variable `d`, you can append
data to it using `d << data`. Generators (`yield`) are syntax sugar over feeds:
a function with `yield`s has a hidden result-collection variable, and each
`yield` translates exactly to a feed append into that collection — so the
compiler query-plans generators and feeds uniformly.
Today, a feed variable is introduced as `out = defer()` or arrives from a builtin like `http_serve`; a new syntactic form `out: Feed(_)` is designed but **not yet implemented**. 

The APIs of library sources and sinks are **[Open]**.

### Mutability, time, and transactions

Cambra's model of state is **temporal functional mutation**: a mutable variable *is* a total function from a **sequencing domain** (a time axis) to a value — its **history**. "Mutation" is the incremental revelation of that function as the domain advances; "reading" is lookup at a time. Conceptually, nothing is ever overwritten — there is no concept of a mutable cell in CCL: the compiler eliminates every mutable write into a pure, well-founded recursive definition whose cycles all pass through *causal accessors* (values at a position depend only on strictly earlier positions). This model is documented in [src/ccl/design/mutability.md](../src/ccl/design/mutability.md).

Mutability has two forms:
- **Inductive** mutability is an exclusive mutable variable over a statically-determined time domain. The time domain is all of the writes to that variable.
- **Transactional** mutability is the _only_ mechanism for shared, mutable state. The time domain is defined by an external oracle (the transaction engine), which establishes an atomic, serializable order of transactions at runtime.

The implemented surface:

```python
cnt := 0                       # mutable by the introducing operator; := writes, += is shorthand
cnt: Mut(Int) := 0             # optional annotation; value type inferred if omitted
balance: Mut(Int, Txn) := 0    # transactional variable over the commit order — Txn is never inferred
```

`:=` is imperative assignment (in the Algol tradition); plain `=` is an immutable binding and never mutates. Transactions are `with begin():` blocks: writes to `Txn`-domain variables are legal only inside one, all writes in a block commit atomically on exit, and reads inside a block see one snapshot-consistent view. Sharing state across concurrent writers is a semantic commitment the program must spell (`Mut(V, Txn)`). It's never inferred.

Mutability is still being implemented. See the [not-yet-implemented list](../src/ccl/design/mutability.md#not-yet-implemented) for the authoritative list.

Time domains are also what make **time-pinned views** meaningful: an aggregate over a live stream, restricted to elements before the reading transaction's time, is a well-defined "as of now" value (the README's rolling-revenue example) — and a materializable one, which the runtime may maintain incrementally. The substrate is in; the handle form it reads from is on the not-yet list above.

### Recursion

Cambra currently does not support recursion, but both function and collection recursion are **[Decided]**.

Self-referential *function* definitions have well-established semantics, and CHL will implement them accordingly.

Self-referential *collection* definitions solve an equation as a least fixpoint in the tradition of Datalog. The compiler's fixpoint substrate already exists: the mutability stack compiles histories and feed channels into guarded, causally-well-founded `letrec` groups. The north-star `reachability` program pins both fixpoint forms. See the spec for more details.

### Pattern matching and conditionals

`if`/`elif`/`else` (statement) and `e₁ if cond else e₂` (ternary) are implemented, with semantic non-strictness: a non-taken branch contributes nothing and need not be defined. `match`/`case` tag dispatch over a variant is implemented too, and is the *same* first-match rule over the same IR node — an arm carries a tag pattern where an `if` carries a guard, which is why a tag test and a boolean guard will eventually sit on one arm with no new structure. Patterns are shallow: one tag per arm, no nesting, no literal patterns, no per-arm guard, and no expression form. Mechanism: [src/ccl/design/lowering.md](../src/ccl/design/lowering.md), "Variants and match".

### Currently omitted

`while` loops, floats, `%`/`**`/bit-shifts, classes, exceptions, imports (CHL is single-file today), identity (`is`), and membership operators are omitted while we focus on the areas of highest technical risk. The spec's [reserved-for-future-work section](chl-spec.md) is the authoritative list. CHL resembles Python; it does not promise Python.

## Program Execution Pipeline

```
CHL source
  → parse            (chl_parser, see src/chl_parser/design-chl-parser.md)
  → lower            (ccl/lower/: CHL AST → CCL Expr)
  → uniquify         (ccl/uniquify.rs: α-uniquify binders — Barendregt convention, base+uid Names)
  → infer            (ccl/infer/: type inference; delegates to ccl/infer/solver/, the constraint solver;
                      runs on the user-shaped tree so type errors report against the program as written)
  → inline           (ccl/inline.rs: inline capability (non-collection) Let bindings; beta-reduce at
                      call sites. Runs *before* channelize so the letrec phase can route an in-loop
                      feed against inlined pass-by-ref writers; it therefore still sees Defer/Feed/Define)
  → transact_phase   (ccl/transact_phase.rs: each `with begin():` block over Mut(V, Txn) variables folds into
                      a get_prev_txn-causal LetRec over the commit domain (per-key histories + per-site
                      commit records). 
                      See src/ccl/design/mutability.md)
  → mut_elim     (ccl/mut_elim.rs: the induction mutability phase — every non-transactional
                      mutation loop (For/MutWrite markers, feed-free or feeding) becomes a causal LetRec
                      group over the induction domain (get_prev_seq recurrence, final_or_default trailing
                      read); see src/ccl/design/mutability.md. Runs before channelize so a
                      per-iteration feed inside a loop is hoisted to an ordinary feed of the loop's history)
  → channelize       (ccl/channelize.rs: Defer/Feed/Define → `++`-union channel bindings, each defer
                      cluster emitted as a mutually-scoped Feed-kind LetRec group; the feed-routing step
                      of mutability elimination (mut_elim + channelize), type-preserving by construction. Feed reads type concretely
                      via rigid ChanDom channel domains, erased here by substitution — no retype pass.
                      Runs after the letrec phase, so an in-loop feed is already hoisted to a feed of the
                      loop's history)
  → lambda_elim      (ccl/lambda_elim.rs: lambda → point-free combinators, then CCC-simplified)
  → plan_loops       (ccl/planning/loops.rs::plan_loops: AFTER lambda_elim, on the point-free normal form,
                      lower each causal LetRec group onto the domain-parameterized Transact carrier —
                      induction domain → InductionStore, Txn domain → commit operator. Anchors on the guard
                      builtins (which survive elimination), so one LetRec travels through channelize +
                      lambda_elim and is planned point-free — no pointful/point-free double
                      representation. Transact is loop planning's output carrier to op-conversion)
  → planning        (ccl/planning/: hash-join and keyed aggregate optimization; brackets iteration-marking with ccl/simplify.rs)
  → operator_conversion  (interpreter/operator_conversion.rs: λ-free CCL → tile operators)
  → subscribe()
  → tile producer/consumer dataflow
```

Why the pass order is what it is: parsing recovers from errors (partial ASTs with placeholder nodes, multiple diagnostics per file — see [src/chl_parser/design-chl-parser.md](../src/chl_parser/design-chl-parser.md)); uniquify establishes the Barendregt convention so every later pass can substitute without capture; inference runs early, on the user-shaped tree, so type errors report against the program as written and every later pass transforms fully-typed trees. The three-pass middle — `transact_phase`, `mut_elim`, `channelize` — is **mutability elimination**: transactions, mutation loops, and feeds each become pure, causally-guarded `letrec` groups, so everything downstream sees only the pure value language. Lambda elimination then rewrites the program into point-free combinators because **operators are point-free** — an operator graph has no binders, so lambdas must be compiled away, not closed over; loop planning lowers the letrec groups onto runtime carriers on that same point-free form; and planning is where comprehension shapes become joins and keyed aggregates. Each pass's own design doc is indexed in [src/ccl/design/README.md](../src/ccl/design/README.md) and [src/design.md](../src/design.md).

## The execution model

The runtime's formal model (in full: [operational-semantics/summary.md](operational-semantics/summary.md), definitions in [semantics.md](operational-semantics/semantics.md), a worked example in [example.md](operational-semantics/example.md)) rests on three concepts:

- **Extent** — the plain set of final values a term can take. No structure; just the answer space.
- **Tiling** — a *progress algebra* over a term's computation: every intermediate state is a **tile**, tiles combine when they cover non-overlapping parts of the computation, and combination only ever adds information. Tiles therefore have a natural progress order with a bottom element `⊥`.
- **Operator** — the runtime counterpart of a CCL function: a monotone map from input tiles to output tiles whose behaviour on terminal inputs matches the function's denotation.

A running program assigns each term a tile, starting at `⊥` and growing monotonically as dependencies deliver new tiles; the program terminates when no tile can be extended. **Guards** decompose tilings structurally — a consumer requests a portion of a producer's tile (projection), declares the region it will ever need (intent), and releases regions it is done with (obsolete), letting the producer **compact** released history into a summary. A **scheduler** orchestrates the graph, triggering sources and coordinating operators.

The headline properties fall out rather than being bolted on. Operators that are homomorphisms **stream**: each input tile transforms independently and merges into the output. Monotone growth is **incrementality**: a new order flowing into a revenue view extends tiles; nothing recomputes from scratch. Unordered-bag semantics plus data-dependency-only ordering is **parallelism**: the scheduler may run any non-dependent work concurrently. And early termination (an operator producing terminal output before its input completes) is what makes short-circuit semantics real at runtime rather than a source-level fiction.

## What the architecture buys

The connections between the layers above and the capabilities Cambra claims:

- **Query-planner behaviour for whole programs.** Because the entire application lives in one typed core with no component boundaries, the planner sees everything — a filter can be pushed across what would be an API boundary in a conventional stack, because there is no boundary.
- **Incremental views by construction.** Monotone tilings mean live aggregates are maintained, not recomputed. The materializable time-pinned view is the decided form of this — the history substrate is implemented, the transaction-handle read it needs is not yet (the ledger's `txn_kv` pins it).
- **Verification [Sketched].** A small referentially-transparent core plus a refinement-typed checker means a semantic predicate established at one point composes across the whole program. The machinery exists today; whole-application contracts on top of it are the driving direction.
- **Validation and program branching [Open].** Referential transparency makes program versions *syntactically comparable with well-defined semantics*, and temporal functional mutation makes state a value over time domains — *branchable and pinnable by construction*. Together they are the substrate for branching a running application — logic and state — exercising the branch under a realistic workload, and diffing behaviour.
- **Live update [Partial].** A running program can be replaced by a new version of its source over the control port (`--control`): `/diff` reports how the two versions differ at any pipeline stage, and `/update` swaps the program. The new version inherits the running one's sources and sinks, may add to them, and retires a route it stops serving, and inherits the operator behind every `Let` binding whose computation is unchanged; a variable whose logic the edit did touch resumes from the value it held. The one refused update is one that cannot take over the state — a variable the new version no longer declares, declares at a different type, or moved to a different loop. See [live-update.md](/src/ccl/design/live-update.md). Running two versions at once is not implemented.
- **Observability.** The compilation pipeline preserves a legible chain from source to running state; the web inspector (`--inspect`) serves the CHL AST, the lowered CCL, the operator graph, and live per-producer runtime state for any running program.

## Feature status at a glance

| Feature | Status |
| --- | --- |
| Comprehensions, with hash-join and keyed-aggregate planning | Implemented |
| Streaming sources and sinks (`stdin`, `http_serve`) | Implemented |
| Generator functions | Implemented (single-`for` bodies; general shapes **[Planned]**) |
| `:=` mutation and loop accumulators (induction histories) | Implemented |
| Transactions: `with begin():` over `Mut(V, Txn)` variables | Implemented (single deny-guard conditionals only; handle form and `abort()` still landing) |
| Aggregates | `sum`, `max` implemented; `min`/`count`/`avg`/`len` **[Planned]** |
| Refinement typing | Machinery implemented (internal); surface syntax **[Decided]** |
| Feed channels | Via `defer()` / `http_serve` implemented; `Feed(_)` declarations designed, not yet |
| Contextual parameters (`requires` / `given` / `summon`) | **[Decided]** |
| `rec` fixpoint bindings | **[Decided]** |
| Collections-as-functions model | Organizing idea decided; encodings **[Sketched]** |
| `match` / `case` | Tag dispatch implemented; deeper patterns **[Tentative]** |
| Live update of a running program (`--control`) | Implemented for logic, endpoint changes, and state resume; running two versions at once is **[Open]** |
| `while`, floats, imports, classes, exceptions | Absent (see the spec) |

The [spec](chl-spec.md) carries the authoritative per-construct markers; [demo-programs.md](demo-programs.md) maps them to runnable programs and their blockers.

## Notation conventions

Design docs that mix CCL syntax with meta-theoretic variables (placeholders for any specific term, type, or predicate) italicize the placeholders using Unicode mathematical italic characters:

- Single-letter term/value metas: `𝑎` `𝑏` `𝑐` `𝑑` `𝑒` `𝑓` `𝑔` `ℎ` `𝑖` `𝑗` `𝑘` `𝑙` `𝑚` `𝑛` `𝑜` `𝑝` `𝑞` `𝑟` `𝑠` `𝑡` `𝑢` `𝑣` `𝑤` `𝑥` `𝑦` `𝑧` (U+1D44E–U+1D467, with `ℎ` at the legacy U+210E).
- Single-letter type metas: `𝐴` `𝐵` `𝐶` `𝐷` `𝐸` `𝐹` `𝐺` `𝐻` `𝐼` `𝐽` `𝐾` `𝐿` `𝑀` `𝑁` `𝑂` `𝑃` `𝑄` `𝑅` `𝑆` `𝑇` `𝑈` `𝑉` `𝑊` `𝑋` `𝑌` `𝑍` (U+1D434–U+1D44D).
- Digit subscripts: `₀` `₁` `₂` `₃` `₄` `₅` `₆` `₇` `₈` `₉` (U+2080–U+2089) for indexed variants like `𝐷₁`, `𝐶₂`.

Multi-character placeholders (`body`, `arg`, `param`, `predicate`, ...) and concrete identifiers (`xs`, `__gb_k`, `key_fn`, ...) stay upright. The convention applies to inline pseudo-code in backticks and to prose mentions; fenced code blocks (which represent literal source) stay in regular characters.

### Function types and terms

Cambra's `Type::Fun` has an optional binder name; the symbolic form distinguishes the two cases:

- `(𝑥: 𝐴) ⇒ 𝐵` — function type with named binder. `𝑥` is bound in `𝐵` and may be referenced by refinements or other types nested there.
- `𝐴 ⇒ 𝐵` — function type with no named binder. The codomain is independent of the argument value.

Refinement types use the standard subset-type notation `{𝑥: 𝑇 | 𝑝(𝑥)}`. The function-type arrow `⇒` is right-associative: `𝐴 ⇒ 𝐵 ⇒ 𝐶` parses as `𝐴 ⇒ (𝐵 ⇒ 𝐶)`.

At the term level: `λ 𝑥 → body` is a lambda (the `→` separates the binder from the body); `𝑎 ▷ 𝑓` is forward apply (`𝑓(𝑎)` with the argument first); `𝑓 ≫ 𝑔` is forward compose (`λ 𝑥 → 𝑔(𝑓(𝑥))`).

The two arrows are deliberately distinct: `⇒` is the type arrow, `→` is the term-level lambda separator. Don't mix them.

## Where to go next

- [chl-spec.md](chl-spec.md) — the surface language, construct by construct, with the full status-marker discipline.
- [operational-semantics/summary.md](operational-semantics/summary.md) — the runtime model in two pages; [semantics.md](operational-semantics/semantics.md) for the formal definitions.
- [demo-programs.md](demo-programs.md) — runnable programs mapped to status: what works, what's blocked, and on what.
- [src/design.md](../src/design.md) — source layout and the index of per-module design docs.
