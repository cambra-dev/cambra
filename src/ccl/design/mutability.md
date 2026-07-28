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
mechanisms.

A **feed** (a reply or yield, written `<<`) is the *same* object — a function over the same
kind of domain — and is therefore **the second form of mutability**, not a separate concept:
`o << e` is surface-impure exactly as `x := e` is (action-at-a-distance on a channel bound
elsewhere; both break referential transparency). The two forms differ only in their
**merge/read law**:

- **mutable variable** — *last-write-wins* (overwrite). The value at a position is the latest
  write ≤ it; a read derefs to that scalar. Introduced with `:=` / `+=`.
- **feed** — *append-only*. Contributions union (`++`); there is no carry-forward, and a read
  yields the whole stream. Written with `<<`.

So there is one idea — *surface-impure histories* `𝐷 ⇒ 𝑉`, eliminated into pure dataflow — in
two merge laws. This distinction is the through-line of the whole document: it is what the
`HistoryKind` marker (`Overwrite` / `Append`) encodes in the type, why the two disciplines
differ (a last-write-wins register needs a resolvable writer; an append merge is commutative
and safe to alias), and why the eliminator has two halves.

This rests on the existing extent-vs-tiling correspondence
([operational-semantics/summary.md](../../../docs/operational-semantics/summary.md)) applied to a
time domain: a value type's *extent* is its set of final values; its *tiling* is the progress
algebra of partial states. A mutable variable's extent is the set of total functions `𝐷 ⇒ 𝑉`;
its tiling is the accumulating partial function `𝐷 ⇀ 𝑉`, each mutation a `⊕`-extension by one
position. The tiling *implements* the function; it does not redefine it.

## The model: histories and causal recursion

A mutable variable of value type `𝑉` over sequencing domain `𝐷` denotes a total function
`𝐷 ⇒ 𝑉`: its **history**. The history functions of a program's mutable variables form one
**mutually recursive definition group** (a `letrec`), whose unique solution is **well-founded**
because every recursive reference is **causal** — it consults only *strictly earlier* positions
of the domain, through one of two **causal accessor** builtins:

- `get_prev_seq(ℎ, 𝑖, 𝑑)` — for an **induction domain** (a loop's iteration index): the value of
  history `ℎ` at the predecessor of `𝑖`, or the default `𝑑` at the first position.
- `get_prev_txn(𝑤, 𝑡, 𝑑)` — for the **transaction domain** `Txn` (a total order of commit times):
  the value carried by the latest commit in stream `𝑤` at a time *strictly before* `𝑡`, or the
  default `𝑑` if there is none.

Because every cycle in the group crosses a causal accessor, values at any position depend only on
strictly earlier positions, and the group has a unique (well-founded) solution by induction along
the domain order. (Only the *overwrite* law forms these cycles: an append feed carries no
carry-forward, so channels never close a causal cycle — see [merge laws](#the-idea-in-one-line).)

### Sequencing domains

| Mutation context | Sequencing domain | Causal accessor |
|---|---|---|
| Sequential statements | degenerate (each position used once) | plain `let` shadowing; no letrec binding |
| `for` loop | the iteration source's domain (`UIntRange` for a literal list, a `DataSource` domain for a stream) | `get_prev_seq` |
| `with begin():` transaction | `Txn`, an anonymous total order issued by the runtime | `get_prev_txn` |
| `while` loop *(future)* | a prefix of `Nat` bounded by the running condition | `get_prev_seq` over a self-ceiling domain |

The structural difference between the two causal accessors mirrors a difference between the two
kinds of variable:

- An **induction variable** has exactly one writer (its loop), and its domain *is* that writer's
  domain. Its history binding is directly the recurrence:
  `cnt = λ 𝑟 → get_prev_seq(cnt, 𝑟, init) + 1`.
- A **transactional variable**'s domain (`Txn`) is *not* any writer's domain — writers iterate
  request streams, and an oracle assigns each transaction a commit time. So its history is defined
  *indirectly*, through **commit records**: each writing site produces one `{time, write}` record
  per iteration, and the variable's history searches those records by time. The commit-time oracle
  is a per-site builtin `begin_<site> : 𝐼 ⇒ Txn` mapping the site's iteration index to the
  transaction's position in the commit order.

Feeds — the **append-only** form of mutability — are realized as the letrec's **outputs**: the
body of the letrec is a record of channels (one field per defer/sink), each a function over its
contributing loop's domain, free to reference the letrec's bindings. (They are outputs by
*realization*, not by nature: `<<` is impure surface mutation like `:=`, discharged into a pure
history by the same eliminator — it is only the *append* merge law, with no carry-forward, that
lets a feed be a plain output rather than a cyclic binding.)

## Surface language

The surface syntax and the behaviour a programmer observes — `:=` mutation, `with begin():`
transactions, the read rules (read-your-writes, the trailing induction read, the `Txn`-register
block-read rule and as-of reads), feeds as the append-law sibling of mutation, `await_final`, and the
ordering-and-concurrency contract — are specified in the
[CHL spec, "Mutability, transactions, and feeds"](../../../docs/chl-spec.md#8-mutability-transactions-and-feeds).
This document specifies the **realization**: how lowering, `mut_elim`, `channelize`, planning, and the
runtime engines eliminate all of it into pure dataflow. The spec is the observable contract;
everything below is how that contract is met.

Two surface facts are load-bearing for the realization and worth restating here:

- **`:=` introduces and writes; `Txn` is never inferred.** A mutable variable is made by the `:=`
  operator, not the annotation; a transactional register must be spelled `x: Mut(𝑉, Txn) := …`
  (`Txn` never arises by inference). Type application is parenthesised at both the surface and the
  CCL `Display` level, so `Mut(𝑉, 𝐷)` renders the same way throughout this document and in the
  language.
- **A `Txn` register is read only inside a `with begin():` block, and a fed-out read is an as-of
  sample** (compiled to `AsOf`); the sole terminal register read is `await_final`, designed but not
  built. These two facts drive the
  [live-read rewrite](#replies-live-cross-endpoint-reads-and-commit-ordered-taps) and the
  [`AsOf` engine](#the-runtime-engines) below.

## CCL representation

### Surface-marker nodes: `For`, `MutWrite`, `Begin`, `Feed`

Lowering emits **surface-CCL** markers — nodes in 1:1 structural correspondence with the CHL
statements, doing no semantic work; they change representation only, leaving structure for the type
checker and `mut_elim` to interpret. ("Surface CCL" names the short-lived dialect that still carries
these markers; `mut_elim` + `channelize` rewrite it into **pure CCL** — the marker-free value algebra
the rest of the pipeline runs on. This is the concrete input→output contract of the mutability
eliminator, stated by content rather than by a "mirrors CHL" adjective.)

- `For { target, iter, body }` — **every** statement `for` loop, generator / side-effecting /
  mutation alike (comprehensions keep their expression lowering). Lowering does *not* distinguish
  the loop kinds — that classification is the phase's, post-inference (see
  [Mutability is the type](#mutability-is-the-type-no-lowering-registry)). Value `Unit`;
  `iter : 𝐼 ⇒ 𝑇`, `target : 𝑇` bound in `body`.
- `MutWrite { name, value }` — one write to a variable. Value `Unit`. Its target **must** be
  `Mut`-typed: inference peels the target's `Mut(𝑉, 𝐷)` and requires `value ⊑ 𝑉`; a write whose
  target is *not* `Mut` is a **type error**, never a shadowing rebind (`x += e` on a plain `x` is
  rejected, not silently turned into `x = x + e`). `x += e` lowers to `MutWrite(x, x + e)`, the
  embedded read being the in-context read.
- `Begin { body }` — one `with begin():` transaction block, made a *single* `Unit`-valued statement
  (`ExprStmt(Begin{block}, rest)`) so a loop body may freely mix a per-iteration transaction, sibling
  induction writes, and feeds. `body` is the per-transaction statement chain. The transaction phase
  strips it: a block writing a `Mut(_, Txn)` register becomes a commit site (partitioned by register
  domain — induction writes lifted onto the enclosing loop); a read-only block is unwrapped onto the
  loop spine. A standalone block lowers to a singleton `For` wrapping a `Begin`.
- `Feed { name, value }` / `Defer` — a `<<` feed and its channel. These survive into inference (so
  a defer binding is typed, at `Feed(𝑉)`) and are eliminated by mut_elim (feeds via channelize).

`For`/`MutWrite`/`Begin`/`Feed`/`Defer` are **pre-phase surface-structure nodes**: pure placeholders
no pass executes, eliminated wholesale by mut_elim + channelize. The purity invariant
([src/ccl/CLAUDE.md](../CLAUDE.md)) holds the same way it does for `Defer` — the phase asserts no
residue, and planning/op-conversion never see them.

### Mutability is the type (no lowering registry)

Whether a name denotes a mutable variable is carried **only** by the mutable-variable type
`Type::History { kind: Overwrite }` (displayed `Mut(𝑉, 𝐷)`), and is therefore known
only after inference. Lowering never tracks it — there is no lowering-side mutable-variable registry. This is
what keeps lowering a pure representation change: it emits the markers above by *shape and scope
alone*, and every decision that needs mutability happens later, keyed on the type.

Lowering's two choices, both scope-only:

- **Introduction vs. write.** `x := e` where `x` is *not* in scope is an introduction — a
  `let x = e` whose binding is stamped `Mut(𝑉, 𝐷)` (`𝐷 = Txn` iff annotated `Mut(𝑉, Txn)`, else a
  `Hole` the phase resolves). `x := e` / `x += e` where `x` *is* in scope is a write — a bare
  `MutWrite(x, e)`. The choice is membership in the ambient scope set (which lowering already
  threads for other reasons); it consults no mutability record.
- **Loop shape.** Every `for` becomes a `For` marker (above). Lowering does not decide
  generator-vs-mutation.

Everything mutability-dependent is then a post-inference decision on the `Type::History`:

1. **Writes require a mutable** (`MutWrite` target must be `Mut`, above). A `+=` / `:=` to a plain
   binding is a type error, not a shadow. This is the single rule that makes "declare it with `:=`"
   a real discipline rather than a lowering-time heuristic.
2. **Pass-by-reference requires the `Mut(…)` annotation.** The annotation is *what gives the
   parameter a mutable `Type::History`*, so its body writes type-check (rule 1) and the phase can classify the
   writer; an unannotated parameter is non-`Mut`, so writing it is rejected by rule 1. Carrying the
   annotation means mutability is present in the type from the parameter inward through the whole
   pipeline — inlining, the phase, planning — with nothing to reconstruct.
3. **Loop routing is the phase's** (see [mut_elim](#mut_elim-eliminating-overwrite-mutability)): a `For` whose body
   writes a `Mut` variable bound outside the loop is an accumulator recurrence; any other `For` (only
   feeds/yields, or writes to loop-local mutable variables) is a plain map — rebuilt as the
   `Compose([iter, λ target → body])` generator shape. Transactional-context checks (a `Txn`
   register written outside `with begin():`, an induction accumulator written inside one) are likewise
   post-inference, dispatching on `Mut`'s domain.

The payoff: lowering has one loop path and one write path, no `is_mutable`/`with_shadowed`
book-keeping, and no base-name scoping scaffolding — a shadowing parameter spelled like an outer
mutable variable is just a different binding with its own (non-`Mut`) type, handled by ordinary inference.

### `Mut` is a CCL type

`Type::History { value: 𝑉, domain: 𝐷, kind: HistoryKind::Overwrite }` (displayed `Mut(𝑉, 𝐷)`) — a
wrapper variant carried on the introduction's binding and on every reference to it. It shares the
`Type::History` variant with a feed channel, distinguished by `kind`; a mutable variable is the
`Overwrite` (last-write-wins) kind. Making mutability a real type buys two things:

- **Pass-by-reference.** A function can take a mutable variable as a parameter
  (`def bump(c: Mut(Int)): c += 1`) and write *the caller's* variable. Because mut_elim
  runs after inlining, this needs no new machinery: beta-reduction substitutes the argument
  variable for the parameter, so the callee's `MutWrite`s land at the call site naming the actual
  mutable variable — the same route by which `Feed`-parameter UDFs work. The cross-function transactional
  writer falls out:

  ```python
  def transfer(src: Mut(Int, Txn), dst: Mut(Int, Txn), amt: Int):
      with begin():
          src -= amt
          dst += amt
  ```

- **Mutability survives α-renaming structurally** — a type rides the binding through every rename.

Typing:

- **Reads are implicit derefs**: `Mut(𝑉, 𝐷)` coerces to `𝑉` wherever a non-`Mut` type is demanded
  (a coercion arm in `constrain`, not structural subtyping). `cnt + 1`, `f(cnt)` for an `Int`
  parameter, and a trailing `cnt` all read; only a position that *expects* `Mut` (a `Mut`-annotated
  parameter) receives the handle. After inlining, no `Mut`-expecting positions remain, so the
  phase's rewrite is purely structural — every surviving `Mut`-typed occurrence is a write target
  or a read, decided by context.
- A parameter `Mut(Int)` means `Mut(Int, _)`; the domain instantiates per call site through the
  let-generalization of UDF bindings. Whether a write site requires `Txn` is the phase's structural
  check, post-inline — so one `bump` can serve an induction accumulator and a transactional
  register.

**No aliasing: `Mut` values are second-class (downward-only).** Passing a reference *down* is safe
exactly as long as the compiler can statically resolve which introduction every write targets. The
discipline:

1. A `Mut`-typed expression must be a **bare variable reference** — an argument to a `Mut`
   parameter is a variable, never a conditional or computed expression. The two halves catch
   different things, because a *conditional* over two registers is not itself `Mut`-typed: a
   mutable read derefs into the arms' join exactly as it derefs into a tuple element (see *Reads
   are implicit derefs* above), so `x if c else y` reads their values and types as a plain `V`.
   What the rule is protecting is the write capability travelling somewhere its target can't be
   traced, and that is the **argument** half: `bump(x if c else y)` is rejected on the argument's
   node, not its type.
2. `Mut` may not appear **inside any composite type** — tuples, records, lists, function codomains
   (so it is never a return type), `Feed` payloads, or another `Mut`.
3. An **unannotated binding may not have `Mut` type**: `b = a` is an error, not an alias. To copy
   the current value, demand the deref (`b: Int = a`); to seed a *new* mutable variable from it, introduce one
   with `:=` (`b: Mut(Int) := a`, the initializer being a read).

One structural check after inference enforces all three. The real fault line is the **merge law**,
not `Feed`-vs-`Mut`. *Append-only* mutability merges commutatively — a feed by `++`, and (at
runtime) a `Txn` register by the commit operator's timestamped merge — so multiple writers are
already the semantics and aliasing is benign; that is why `Feed` deliberately stays first-class (it
is returned in `http_serve`'s tuple). *Last-write-wins* mutability instead needs a **resolvable
writer set** — but that requirement is fundamental only for an **induction** accumulator, which
compiles to a single-writer `Recurse`. A `Txn` register already tolerates an open writer set (its
sites merge their commit streams by time), so applying the uniform second-class discipline to it is
a conservative stopgap, not a necessity. (Future work splits the same way: the induction aliasing
rule is a blunt approximation of **affine typing** — a use-at-most-once handle keeps the writer
unique by construction while lifting downward-only — and first-class `Txn` needs only a runtime
register key into the already-keyed MVCC store, not the full sigma/index-types generality.)

`Mut`-parameter functions must reach their call sites, so they must be inlineable — the stance the
pipeline already takes for writers and `Feed`-mediating UDFs. (When general recursion lands,
recursive functions that don't fully inline need either the letrec treatment or a ban on `Mut`
parameters — deferred to that design.)

### `Feed` is a CCL type

`Type::History { value: 𝑉, domain: 𝐷, kind: HistoryKind::Append }` (displayed `feed(𝐷 ⇒ 𝑉)`) — the
type of a feed handle: what an `out = defer()` introduces, what `http_serve`'s response half
returns, what a defer-mediating UDF parameter (`λ out → out << e`) carries. It is the same
`Type::History` variant a mutable variable uses, under the `Append` kind; unlike an overwrite
variable it reads as its whole stream `𝐷 ⇒ 𝑉`, not a scalar deref. Feed handles are fully first-class — returnable and tuple-packable —
because feed aliasing is benign (multiple feeders union by `++`). `channelize` eliminates every
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
    /// its full type (generated by mut_elim; always concrete).
    bindings: Vec<(TypedBinding, TypedExpr)>,
    /// The continuation, with the group in scope.
    body: Box<TypedExpr>,
}
```

Typing: with `Γ, 𝑏₁ : 𝑇₁, …, 𝑏ₙ : 𝑇ₙ` check each binding body against its declared `𝑇ᵢ` and
synthesize the letrec body as usual. The phase generates the binding types itself (from inferred
loop-source domains and value types), so the post-phase strict `typecheck` validates them directly.

**Well-formedness (causality).** In the reference graph over the group, an edge is *causal* when
the reference is the history argument of a `get_prev_*` call; non-causal references must be
position-non-increasing (they pass the ambient position through, as `balance(𝑡)` does inside the
commit record for time `𝑡`). Every cycle must contain a causal edge — equivalently, the
non-causal-reference subgraph is acyclic. A structural check enforces this; op-conversion treats an
unrecognized non-causal cycle as a compile error rather than attempting fixpoint iteration.

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
| `final_or_default` | `(𝐷 ⇒ 𝑉, 𝑉) ⇒ 𝑉` | final value of a completed history; the default if the domain is empty. The trailing induction read (`ExtractLast`). Applied to a `Txn` register only through the surface [`await_final`](#await_final) primitive (designed, not yet built); a bare fed-out register read never becomes one |

`begin()` never reaches CCL — lowering records the block structure, and the phase mints one
`begin_<site>` per site. The oracles are opaque, strictly monotone in arrival order (which is what
gives cross-endpoint external consistency), with pairwise-disjoint ranges; the commit engine
realizes them by tick allocation, not by computing anything.

Multi-variable atomic blocks produce one shared record `{time, writes: {𝑘₁: 𝑉₁, …}}` per commit,
and each variable's history reads it through a per-key view — atomicity by construction, since one
record either exists or does not. There is no `commit: Bool` in the per-key view: the commit-record
stream carries only committed transactions (allocate-on-commit — a denied decision proposes nothing,
so the engine allocates no tick and appends no entry), so `get_prev_txn` searches the latest write
`≤ t` with no filter, matching its declared `{time, write}` codomain. Multiple writer sites for one variable merge their commit
streams (ordered by time) before the search — the emitted term is spec-true: each key's history
searches the `⧺`-union of its writing sites' per-key views
`commits_j ≫ (λ 𝑐 → {time: 𝑐.time, write: 𝑐.decision.writes.𝑖})`, shapes the causality check
admits (pointwise maps and unions of causal streams change *what* is read per position, never
*which* positions the accessor consults).

## Compilation pipeline

```
CHL source
  → parse              (annotations incl. _, Mut(…)/Feed(…)/Txn forms, with begin())
  → lower              (surface CCL: For / MutWrite / Begin / Feed / Defer; Mut/Feed types from annotations;
                        NO mutability classification — every loop is a `For`, intro-vs-write is scope-only)
  → uniquify
  → infer + check      (on the surface-CCL tree; Feed(V) with a rigid ChanDom domain types the defers)
  → inline             (UDFs — incl. writers and defer-mediating lambdas — reach their call sites)
  → mut_elim           (overwrite-mutability elimination: collect mutable state + emit causal LetRec,
                        writer bodies decision-factored; eliminates For / MutWrite)
  → channelize         (append-mutability elimination: route feeds on the LetRec tree; erase ChanDom
                        by substitution; eliminates Feed / Defer)
  → live-read rewrite  (bare history reads fed out of read-only blocks → AsOf)
  → lambda_elim        (the LetRec travels through — bodies point-freed, group intact)
  → typecheck          (strict wall)
  → plan_loops         (planning/loops.rs: point-free letrec patterns → the Transact carrier;
                        causality re-checked by the point-free matcher)
  → planning           (stages the carrier's writer sources) → simplify
  → operator_conversion (Transact → engines, dispatched on the domain)
```

**Mutability elimination has two halves, one per merge law** — `mut_elim` discharges *overwrite*
mutability (`:=`/`+=`/`MutWrite`) into a causal `LetRec`, and `channelize` discharges *append*
mutability (`<<`/`Feed`/`Defer`) into the letrec's output channels. Together they are the surface-CCL
→ pure-CCL step, the mutability analog of `lambda_elim` (which eliminates lambdas → point-free CCL).

**One `LetRec` representation travels from `mut_elim` through `channelize` and
`lambda_elim`; `plan_loops` consumes its point-free normal form.** `mut_elim`
emits every binding **decision-factored** — the writer body is an opaque
tuple-param lambda applied to a snapshot (`(get_prev_*(…), 𝑟 ▷ iter) ▷ body`
for induction; the commit-record `decision` for transactions) — so after
`lambda_elim` both domains share one shape, `(snapshot, source) ▷ zip ≫ body`,
and `plan_loops` splits scaffold from body structurally, lifting the body
**verbatim**. The `Transact` carrier is born at loop planning and spans only
`plan_loops` → planning → op-conversion.

Inlining runs **before** `mut_elim`: a UDF that writes a `Mut` parameter or feeds a `Feed` parameter
is beta-reduced to its call site, where `mut_elim` sees its writes and feeds in the scope of the
mutable variables and channels they target. Generators survive inlining because surface-CCL lowering
leaves nothing to lose — a generator body is `For` + `Feed` nodes against an implicit result feed,
substituted wholesale.

### mut_elim: eliminating overwrite mutability

Input: a typed, inlined, surface-CCL tree. Output: pure CCL (`let`/`letrec` algebra) with every
`For`/`MutWrite`/`Begin`/`Feed`/`Defer` eliminated (feeds routed here, then discharged by `channelize`). It:

0. **Normalizes to the flat-spine invariant** (`flatten_spine`). Inlining a pass-by-reference
   writer splices its body — a bare `MutWrite`, possibly a multi-statement `ExprStmt` chain, or a
   body that computes an intermediate first (`tmp = c + 1; c := tmp`) — at the call site, which can
   bury a mutable write off the statement spine: under another `ExprStmt` (`bump2(cnt)` with a
   two-write body), inside a `Let` bound to a value (`y = bump(cnt)`) or in a `Let`-headed effect
   (a bare `bump(cnt)` whose body has a leading `let`), or in terminal/value position (a trailing
   `cnt += 1`). Commuting conversions (gated on the affected body's spine performing a `MutWrite`,
   so `Feed`/`Define` chains and unrelated `Let` subplans — a join subplan spine holds no
   `MutWrite` — are untouched) lift every writer body's leading statements and intermediate `let`s
   onto the spine so the write lands as a direct `ExprStmt` effect; a value-position write
   terminalizes to `ExprStmt(MutWrite, unit)` (its mutable variable's final state is unobserved, so its value
   is `unit`). Downstream collection and read-your-writes rewriting then see only on-spine writes.
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
5. **Routes loops and rewrites reads**: a `For` whose body writes a `Mut` variable bound outside it is
   an accumulator recurrence (built in step 3); **any other `For` is rebuilt as its map shape** —
   `Compose([iter, λ target → body])`, with feeds/yields already routed in step 4 — so a generator
   or bare side-effect loop needs no letrec at all. Trailing induction reads → `final_or_default(history,
   init)`; a `Txn` read fed out of a read-only block → a broadcast of the history over the
   enclosing loop, which planning latches through the as-of read.

Stateless programs never build a letrec — the phase degenerates to plain feed routing.

## Worked example

A transactional register and an induction counter shared across two HTTP endpoints:

```python
incr_reqs, incr_resps = http_serve("8080", "POST", "/incr")
get_reqs,  get_resps  = http_serve("8080", "GET",  "/get")

balance: Mut(Int, Txn) := 0
cnt: Mut(Int) := 0

for req in incr_reqs:
    with begin():
        balance += 1
        cnt += 1
    incr_resps << "ok {cnt}\n"

for req in get_reqs:
    with begin():
        get_resps << balance
```

Note the mix: `balance` is transactional; `cnt` is a plain induction accumulator whose write here sits
*inside* the transaction block. **In the model** this is legal — `cnt`'s writes sequence on the incr
loop's induction domain, independent of the commit order, so `cnt` does not join `balance` in the
atomic commit (it is absent from `incr_commits` below). Writing an induction accumulator inside a
`with begin():` block **is implemented for a bare, top-level write**: the transaction phase partitions
the block by register domain, lifting each top-level-spine induction `MutWrite` onto the enclosing loop
as its own recurrence while the register writes form the commit decision. Because the write is lifted
out entirely, block placement is *inert* for it — a bare in-block induction write is **exactly the
out-of-block form** (it fires once per iteration unconditionally, independent of whether the co-located
transaction commits). A **guarded** in-block induction write (`if q: cnt += 1`) is a different matter:
committing it only when the transaction commits needs commit-gated carry-forward (the value-`Case`
machinery upstack), so today it is **rejected** (`check_no_guarded_induction_writes`) rather than
silently lifted with the wrong (unconditional) semantics. A commit *decision* that reads an induction accumulator
(`balance += cnt`) **is also implemented** — the accumulator is threaded through the writer source and
the commit engine co-iterates it (see [Reading an induction accumulator in a commit
decision](#reading-an-induction-accumulator-in-a-commit-decision)). (A write to `balance` *outside* a
`with begin():` block is rejected in both the model and the implementation.)

After mut_elim (with `IncrIdx`/`GetIdx` the two request-source domains):

```
letrec
    balance: Txn ⇒ Int =
        λ t → get_prev_txn(incr_commits, t, 0)

    cnt: IncrIdx ⇒ Int =
        λ r → get_prev_seq(cnt, r, 0) + 1

    incr_commits: IncrIdx ⇒ {time: Txn, write: Int} =
        λ r → let t = begin_incr(r) in
              (time: t, write: balance(t) + 1)
in
    ( incr_resps: λ r → incr_commits(r) ▷ (λ c → "ok " + cnt(r) + "\n"),
      get_resps:  read_at_get ≫ balance )
```

Reading it off:

- **`incr_commits`** — one commit record per POST. `begin_incr(𝑟)` is where request `𝑟`'s
  transaction lands in the commit order; `balance(𝑡)` reads the snapshot (resolving, via `balance`'s own
  definition, to the latest commit *strictly before* `𝑡` — no self-reference), and `+ 1` is the
  write.
- **`balance`** — the register's history: at any `𝑡`, the latest earlier commit's write, else the
  initializer. The `balance ↔ incr_commits` cycle is well-founded — the trip around it crosses
  `get_prev_txn` once, so position strictly decreases.
- **`cnt`** — the induction recurrence, self-referential through `get_prev_seq` (causal); its domain is `IncrIdx`, not
  `Txn`, because its annotation said so.
- **`incr_resps`** — the reply for `𝑟` depends on `incr_commits(𝑟)` (then discards it): the reply is
  sequenced after the commit.
- **`get_resps`** — the fed-out register read: `read_at_get` picks the GET's *observation time* (a `Txn`
  position — wherever the read lands in the commit order) and `balance` is sampled there, replied
  indexed by the GET request loop. This is the **same store-level-timestamp mechanism** the `AsOf`
  sections describe as "a sample at an arbitrary observation-time position": the read takes a timestamp
  at its observation point and returns the committed prefix as of that time — described uniformly here
  and there, not as rival semantics. `read_at_get` is deliberately *not* a `begin_<site>` oracle: a
  read-only block mints none — it commits nothing, produces no `{time, write}` record, and takes no
  commit slot (`begin_<site>`/`BeginTxn` is the *writer* oracle only). It is pure composition, no
  commit record, no write set. **External consistency** is a real property of this same mechanism (not
  a competing guarantee): a GET issued *after* a POST's `ok`-reply lands at an observation time ≥ that
  POST's commit (arrival-order monotonicity), so a client that sees `ok 2` then GETs observes `≥ 2`;
  a read with no such causal ordering samples an *arbitrary* position among concurrent commits — which
  is all the "arbitrary as-of" of the `AsOf` sections means.

## Semantics

The observable guarantees are the spec's (see the CHL spec,
["Mutability, transactions, and feeds"](../../../docs/chl-spec.md#8-mutability-transactions-and-feeds));
this section states how the letrec model *delivers* them.

- **Serial denotation, concurrent engine.** The letrec denotes a *serial* execution: `Txn` is a
  total order, and each transaction reads exactly the prefix strictly before its own time.
  Optimistic concurrency — snapshots, backward validation, retry — is engine implementation,
  correct iff observationally equivalent to the serial denotation.
- **Atomicity is representational**: one commit record per block. There is no partially visible
  commit because no term denotes one.
- **Read-your-writes** within a block is `let` shadowing inside the record body.
- **Deny** (`if` around a write) is `commit: false` on the record; `get_prev_txn` skips it. A denied
  transaction contributes no visible write and no reply.
- **Induction and transaction domains are independent.** In the worked example's model form `cnt`
  advances per request even though its write sits inside the block (a mix the current lowering
  rejects — see the caveat there); only `Txn`-domain variables participate in the atomic commit. A
  program that needs the counter transactionally consistent with the register declares it
  `Mut(Int, Txn)`.
- **Liveness.** Induction domains are finite or stream-complete; `Txn` histories complete when all
  writer sources do. A fed-out `Txn` register read reads as-of its own position in the commit clock
  and does not wait for completeness. The one term that *does* wait for a register's completeness is
  [`await_final`](#await_final) (designed, not yet built); it is well-defined precisely because it
  closes the writer set (the register is unreferenceable afterward, so no later writer can extend the
  history it just declared complete).

## Ordering and concurrency

The observable ordering contract — maximum parallelism subject to dependency edges rooted at **events**
(program start, source arrivals, forced data dependencies, `await_final`), and the guarantees a program
may rely on — is specified in the
[CHL spec, "Ordering and concurrency"](../../../docs/chl-spec.md#85-ordering-and-concurrency). This
section records the **realization** side: how the engines deliver that contract, and which points
remain open in the model.

**Engine freedom, stated symmetrically.** The two loop engines sit at opposite ends, and the contrast
is why dispatch on the sequencing domain is load-bearing (not an optimization):

- **Induction (`Recurse`)** reads position `𝑖-1`, so it is a *strict total-order data-dependence
  chain*: necessarily sequential, independent iterations **not** reordered.
- **`Txn` (commit operator)** has a *serial denotation* (a total commit order, each transaction reading
  the prefix strictly before its time) but a *concurrent engine* (optimistic concurrency), correct iff
  observationally equivalent to that denotation. Disjoint footprints commit concurrently.

**How the program-start-anchored case is realized.** A standalone `with begin():` or a literal-list
loop depends only on program start, which — being a single event — imposes no order among the blocks it
triggers (the spec's ordering model), so their commit order is unconstrained. The engine realizes that
freedom through its serialization choice (`drain_start`); any serialization the model admits is a
correct outcome. This is why the batch programs in `tests/compilation_pipeline/transactions.rs` pass
only because their bodies are commutative — they add no edge that distinguishes their commit order, so
they are effectively engine tests.

**Open / under-specified.** Two genuine model questions remain: the merge order of a feed `++`-union
across multiple feeders (or several feeds in one body), and the multi-writer commit-stream merge order
for one register.

## Loop planning (`plan_loops`): letrec patterns → the Transact carrier

`plan_loops` (in `planning/loops.rs`) runs **after `lambda_elim`**, on the letrec's point-free normal
form — anchored on the builtins (`get_prev_seq`, `get_prev_txn`, `begin_<site>`), which are opaque,
like aggregates, so `lambda_elim` normalizes *around* them without destroying the scaffold. Because
`mut_elim` emits decision-factored bindings, the writer body arrives already point-free and loop
planning lifts it verbatim; the causal accessor's defaults carry the key inits and the snapshot's
trailing slot the source. The planned recurrence travels to op-conversion on the **carrier node**
`Transact { keys, writers, domain }` — explicit key/writer header slots plus the opaque writer
body — which `planning` iterate-wraps the writer sources of and op-conversion builds the engine
from. One carrier serves both domains — there is no separate loop node. It is the loop analog of the
other planning-phase iteration recognizers (`plan_loop_join` for joins, group-by for aggregates), so
it sits beside them in `planning/`. Causality is re-checked at loop planning's wall by the point-free
causal matcher (`letrec::check_letrec_causal`).

| Letrec pattern | Engine |
|---|---|
| a binding referenced only via `get_prev_seq(𝑏, …)`, over a finite/stream induction domain | `Recurse` — the sequential loop engine |
| commit-record bindings + `begin_<site>` oracles + `Txn` histories read via `get_prev_txn` | the commit operator (`CommitOperator`, `TransactWriter`, cyclic `FanOut`, `StoreValueStream`) |
| a `Txn` history read out of a read-only block (any reading loop — a live request stream, a finite loop, or a standalone singleton) | the as-of read (`AsOf`), latching the store's value as of the reading transaction's position, indexed by the outer reading loop |
| a non-causal cycle, or a causal shape loop planning does not know | compile error (no silent fallback) |

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
- **`AsOf`** — the as-of (temporal) join: **every** fed-out `Txn` register read, regardless of the
  reading loop's domain. Given a *trigger* (the reading loop — the positions to sample at) and a
  *source* (the store), it latches, for each trigger position, the store's value as of the moment
  that position is first observed. The output is indexed by the **trigger** (the outer reading loop),
  not the commit clock — which is why a reply matches its reader by position and needs no explicit
  correlation id. It is the dual of the commit `Recurse`: `Recurse` latches a private accumulator per
  source step; `AsOf` latches the store's current value per trigger step. It is a *sample at
  observation time* — an arbitrary as-of position, which is exactly the read a transaction gets: the
  store as of where it lands in the commit order. The only terminal/final register read is
  [`await_final`](#await_final) (designed, not yet built): when implemented it is `ExtractLast` over the
  key's `StoreValueStream` (the register-carry stream `StoreValueStream` already projects), folding the
  completed commit-value stream to its last value — no new engine, the same `final_or_default →
  ExtractLast` path the induction final uses, applied for the first time to a `Txn` history. Absent it,
  a standalone read is just the singleton-trigger case of the same `AsOf`; under the batch scheduler it
  observes the drained store, but that coincidence is not part of the semantics.
- **`StoreValueStream`** — projects one key's `CommitTs ⇀ V` commit-value stream by folding the
  store changelog. It backs the **in-block reply tap** (`out << e` inside a block — a per-commit,
  commit-tick-indexed event stream) and is the fold `AsOf` samples. It is *not* reduced by
  `ExtractLast` for a register read — that path (a fold-to-completion "final register value") does
  not exist. `ExtractLast` itself remains, but for the two genuinely-terminating histories that do
  have a final: a post-loop **induction** accumulator, and the **broadcast source** (a sibling
  induction loop's final, broadcast into a commit decision).

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
  is also what first-class `Mut` (returning or storing references) needs: carrying register identity in
  types is a sigma/index-types question. Until then the second-class discipline is the aliasing
  firewall.
- **History access / auditing** — `get_prev_*` generalized to user-facing reads at explicit
  positions; the transaction handle (`t = begin()`) already names the position.
- **Recursively-defined values** generally — the `LetRec` node and causality check are the general
  mechanism; only loop-planning patterns need to grow.

## Reading an induction accumulator in a commit decision

A commit decision may read an induction accumulator at its request position
(`with begin(): balance += cnt` — the register write folds in `cnt(r)`). The intended letrec is the
[worked example](#worked-example)'s: `𝑐𝑛𝑡` (induction, `IncrIdx`) and `balance`/`incr_commits`
(transaction, `Txn`) mutually in scope, so `incr_commits(𝑟)` reads `𝑐𝑛𝑡(𝑟)`.

**CCL — outer induction letrec, accumulator threaded through the writer source.** The transaction
phase folds the entangled induction loop (via `fold_induction_loop`, shared with `transform_loop`)
into its own **outer** single-binding induction letrec wrapping the transaction letrec — dependency
order, since `incr_commits` reads `𝑐𝑛𝑡` and `𝑐𝑛𝑡` is self-guarded — so `recognize` nests the two
carriers (`Recurse` outer, commit engine inner) with **no** cross-domain group logic. The read itself
rides the **writer source**: an accumulator the decision reads is zipped into the source,
`source ↦ λ 𝑟 → (reqs(𝑟), 𝑐𝑛𝑡-view(𝑟)) : 𝐼 ⇒ (item, 𝑉)`, and the decision body reads it off the item
tuple's slot. This keeps recognition's writer round-trip intact — `recover_writer` lifts the source
verbatim (a `zip` is opaque to its shape parser), so no recognition change is needed.

**Engine — co-iterating the accumulator with the loop source.** Two small changes carry it:

- *`zip` conversion.* A register-read arm of a `zip` (`__cnt.acc`) is a **leaf** source over its own
  domain, not an iteration-driven morphism. The generic `zip` path converts such an arm with *no*
  input (rather than fanning the shared iteration input into it, which it would reject); `fan_in`
  then co-aligns the leaf accumulator stream with the input-driven request stream by domain position.
- *Source decoding.* The co-iterated source's codomain is a `Record` (the `(item, acc(𝑟))` tuple);
  `decode_source_items` decodes each position into a `Value::Record`, which the writer body reads off
  its `._0` / `._𝑖` slots.

The accumulator stream is on the writer's own request domain, so it is position-aligned and needs no
as-of latch. The `balance ↔ incr_commits` cycle is unchanged (`get_prev_txn`-guarded); `𝑐𝑛𝑡` sits
outside it, read-only to the transaction, so guardedness is unaffected. No new operator — the
existing `zip`/`fan_in` co-iteration plus a wider source decode.

### Co-indexed vs. cross-loop (broadcast)

The above is the **co-indexed** case: `𝑐𝑛𝑡` is written by the transaction's *own* loop, so its value
is request-indexed and threads through the writer source. When the decision instead reads an
accumulator written by a **different, already-completed loop** (`for i in xs: cnt += 1` *then*
`for r in reqs: with begin(): balance -= cnt`), there is no per-request correspondence between the two
loops' domains — the read is that accumulator's **final** value, the same scalar broadcast into every
transaction. The phase distinguishes the two by the site's *enclosing-loop write set*
(`RawSite::enclosing_writes`, from `loop_induction_writes`): an accumulator in it is co-indexed
(zipped into the source); one not in it is broadcast — its read is bound to the loop's
`final_or_default` final (`cross.reads`, in scope in the writer body), which op-conversion compiles to
a `Constant` broadcast (via `MapResultToConst`) over the transaction domain.

The one engine subtlety is **driving** that broadcast to convergence. The final's `ExtractLast` is
empty until the sibling loop's `Recurse` drains (one position per body pull), and nothing external
re-pulls the writer: the store's own convergence loop stops once the commit frontier stalls, and the
frontier cannot advance until this writer commits, which needs the value still converging. The writer
resolves this the same way `Recurse` resolves its own one-step-per-pull convergence (see #291): when
its decision body is not ready, it re-arms itself on the scheduler's **deferred-wakeup queue**
(`WakeupQueue::request`) and returns non-terminal, keeping its pending body-input row so a re-pull
reuses it (a re-push would duplicate a buffer position against the body's `Memo`). Each demand-driven
re-pull advances the sibling loop one step until the decision is ready — no blocking loop inside
`get`, and it composes with an async sibling source (the source's own notification drives the
re-pulls). A fed-out read *of* the result register is an `AsOf` (an in-block reply tap, or a trailing
standalone read), which demand-drives this convergence: each committed reply pulls the writer, which
advances the sibling loop, exactly as an in-block reply drives the writer in the co-indexed case. The
co-indexed and non-cross paths are untouched.

(Note the asymmetry: the broadcast **source** — the sibling induction loop's accumulator — *does*
have a final, read via `ExtractLast`, because an induction loop terminates and its last value is
denotable. The result **register** does not: a `Txn` register has no final-value term, so reads of it
are `AsOf`, never `ExtractLast`.)

## Replies: live cross-endpoint reads and commit-ordered taps

A `<<` reply takes one of two forms, by where it sits relative to the `with begin():` block.

**As-of read (reply *of* a register, outside the writing block).** A read-only block
`with begin(): resp << 𝑒` reading a `Txn` register replies the register as of the reading transaction's
position. The pre-lambda-elim `rewrite_live_reads` turns it into an as-of join indexed by the reading
loop, not the commit clock — uniformly, whether that loop is a live request stream, a finite loop, or
a standalone singleton (the live cross-endpoint read is one instance, not a distinct compilation).
Three shapes:

- **one register** — `as_of((trigger, balance.f)) ≫ (λ 𝑘 → 𝑒)` (`resp << balance`, `resp << balance + 1`);
- **several at one snapshot** — `as_of((trigger, {fᵢ: histᵢ})) ≫ (λ snap → 𝑒[𝑘ᵢ ↦ snap.fᵢ])`
  (`resp << a + b`), one whole-register snapshot per request (§I-c);
- **request element combined with a register read** — `zip((trigger, as_of((trigger, source)))) ≫ (λ p
  → 𝑒[req ↦ p.0, 𝑘ᵢ ↦ p.1(.fᵢ)])` (`resp << balance + req`): the request rides alongside its register
  snapshot. The `as_of` arm is a leaf that op-conversion's `zip` co-iterates with the request stream
  (the same `is_leaf_zip_arm` path as the commit-decision read above) — no new operator.

**Commit-ordered / commit-gated reply (reply *inside* the writing block).** A `<<` inside the block
rides the writer decision as a `to_<defer>` tap, committed atomically with the register write and
read back as a per-commit value-stream (commit-tick-indexed). So it is **sequenced after the commit**
and **gated**: a denied transaction (`if 𝑝:` false) proposes no write and emits no tap, replying
nothing. The tap may read an induction accumulator (`resp << cnt`), which composes with the
commit-decision co-iteration above. Contrast a sibling reply *outside* the block (`resp << cnt`),
which rides the induction domain and fires every iteration regardless of commit — value-correct,
request-indexed, but not commit-ordered. To gate or commit-order a reply, put it in the block.

## Not yet implemented

These features belong to the model above but are not yet built. Each is rejected at compile time
today rather than silently mishandled.

### General in-transaction conditionals (and conditional writes)

A `with begin():` block admits a single bare `if 𝑝:` **deny guard** — the transaction commits iff
`𝑝` holds over its snapshot. An `elif` chain, an `else` that writes, or more than one `if` guard in a
block is rejected at lowering.

The intended end state is a uniform *path-based* model. Walking a block threads a path condition (a
branch guard `𝑔` extends it to `path ∧ 𝑔`); the block denotes
`snapshot ⇒ {commit, writes, to_<defer>*}` where **`commit` is the disjunction of the path-conditions
of every mutable write and feed** (an empty taken path — including a missing `else` — denies), and
**each write key is a `Case` merged over the branch structure** (read-your-writes; a branch that does
not write a key keeps its snapshot value). This is keyword-free, subsumes the current deny
(`if 𝑝: x := 𝑒` → one write at path `𝑝` → `commit = 𝑝`), and admits value-selection, cross-key
routing, `elif`, nesting (conjunction), and sequencing.

The same path-condition fan-out is what a **conditional induction write** needs. A conditional feed
(`if 𝑝: o << x`) is absent off-path; a conditional mutable write (`if 𝑝: total += x`) instead carries
the previous value forward off-path — one extra **carry-forward** arm over the complement domain:

```
target = ⧺ᵢ (source | 𝑝ᵢ ≫ (λ 𝑟 → 𝑣ᵢ))                                  -- channel: partial off-path
total  = ⧺ᵢ (source | 𝑝ᵢ ≫ (λ 𝑟 → 𝑣ᵢ)) ⧺ (source | ¬⋁ᵢ𝑝ᵢ ≫ (λ 𝑟 → get_prev_seq(total, 𝑟, init)))
```

The presence or absence of that carry-forward arm *is* the `Overwrite`/`Feed` distinction. **Blocker:**
both need a *value-selecting* `Case` (`x = if 𝑝: 𝑒₁ else: 𝑒₂`) as a compiled construct, but only the
*filter* `Case` (`[𝑔 → action; true → unit]` → `Restrict`) compiles today — a value `Case` errors at
`lambda_elim`. The planned fix (refinement-based fan-out, lowering a value `Case` to a union of
restricts `⧺ᵢ (source | pathᵢ ≫ 𝑒ᵢ)`) unblocks both the transaction conditionals and the same-shaped
N-arm Case-with-feeds gap.

### `with t = begin():` transaction handle

Designed — it binds `t` to the transaction's commit time (see the CHL spec,
[transactions](../../../docs/chl-spec.md#82-transactions-with-begin)) — but rejected at lowering today.

### `await_final`

The **terminal read of a transactional register** — surface, semantics, and the unreferenceable-after
rule are specified in the
[CHL spec, "`await_final`"](../../../docs/chl-spec.md#86-await_final-decided): `await_final(𝑥)` reads a
`Mut(𝑉, Txn)` register's last committed value once its whole commit history completes, and `𝑥` is
unreferenceable afterward so the completion event is well-defined. In the [ordering
model](../../../docs/chl-spec.md#85-ordering-and-concurrency) it is the register-domain analog of loop
completion — a **completeness** edge on the `Txn` domain. Designed, not built. This section is the
intended realization.

**Intended realization (no new engine).** `await_final(𝑥)` lowers to `final_or_default(𝑥.history, init)`
— the *single* permitted application of `final_or_default` to a `Txn` history (a bare fed-out register
read never becomes one; see the CHL spec, [reads](../../../docs/chl-spec.md#83-reads)). It compiles through the existing `final_or_default →
ExtractLast` path, with `ExtractLast` folding the key's `StoreValueStream` — the register-carry
(`carry_forward`) commit-value stream `StoreValueStream` already projects — to its last value. Contrast
the fed-out as-of read, which hands `AsOf` the raw store fan and samples an *arbitrary* position: same
`StoreValueStream` source, different reducer (fold-to-last vs. sample-at-trigger). No new operator, no
new runtime node — `await_final` is the first term to reduce a register stream to completion.

**Build sketch** (for whoever implements it): a `"await_final"` arm in `lower_call`
(`src/ccl/lower/exprs.rs`) emitting the register-final read; the unreferenceable-after rule enforced by
the scope machinery that already backs the read/write gates (`LoweringContext`'s transactional-register
set in `src/ccl/lower/mod.rs`) — drop `𝑥` from scope at the await point so a later reference hits the
existing gate; and the completeness read allowed to survive the live-read rewrite
(`rewrite_live_reads` in `src/ccl/transact_phase.rs`) rather than being dropped as an unresolved
`final_or_default` over a live history. **Not built today**: a program that names `await_final` does not
compile.

