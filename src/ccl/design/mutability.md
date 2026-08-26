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
differ (a last-write-wins mutable variable needs a resolvable writer; an append merge is commutative
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

A mutable variable's domain is fixed by **where it is introduced**, which is why an introduction may not
sit inside the context that would sequence it. A `:=` inside a `for` body, or inside a
`with begin():` block, would need a domain nested within the enclosing one — the loop's iteration
extent per iteration, or a `Txn` order per transaction — and neither the recurrence nor the commit
model has a carrier for that. Both are rejected at lowering, at every spelling: an annotation on
the introduction says nothing about whether it introduces a mutable variable, so gating on one accepted
`y := 0` and rejected `y: Mut(Int) := 0` for the same construct. The fallback that rejection
replaces is a per-iteration shadowing `let`, which silently discards each update at the boundary —
the failure `:=` exists to make impossible.

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

### A mutable variable read is an explicit operation

A mutable variable mention that denotes its **value** is dereffed by the rule that emits it
(`infer::emit::emit_value_read`), not by the subtyping relation. `Mut(𝑉) <: 𝑉` is not a
subtyping fact.

The handle survives in exactly **three** positions, and the second-class discipline is what
makes them enumerable: rule 1 forces a `Mut`-typed value to be a bare `Var` and rule 2
keeps `Mut` out of every composite, so a parent always knows whether the operand it is
about to constrain is a handle position.

- A **pass-by-reference argument**, decided in `emit_apply` by reading the parameter off
  the head of the application spine. The handle reaches the parameter, so the invariance
  rule relates the two value types directly.
- A **write's target**, which is resolved by name rather than as a subexpression. The
  written *value* is an ordinary value position and reads.
- **[`await_final`](#await_final)'s operand.** The terminal read reduces the mutable variable's
  history rather than one sampled value, so its scheme `∀ν. Mut(ν, Txn) ⇒ ν` puts a `Mut` in
  the domain. Inference sees the pass-by-reference case above — `emit_apply` reads that `Mut`
  off the head of the spine — and lowering resolves the operand by name as it does a write
  target, so the mention never becomes a value position at all.

A lambda's result is deliberately *not* dereffed: that is where rule 2 catches a function
returning a `Mut`, and dereffing would silently accept the escape by turning it into a
read.

That check reads what the body **denotes**, not what its root node is stamped with, and
the difference is load-bearing. A **statement's continuation** and a **mutable variable
introduction's body** report their continuation's *value* — they emit it as a value
operand — so a program ending in a read of its accumulator has that accumulator's value
rather than a handle. Their coalesce-time lifted type derefs for the same reason
(`solve.rs`): a lift that copied the continuation's type verbatim would re-stamp the node
with the handle the read just looked through, leaving the node's recorded type
contradicting the rule that typed it. A **`Let` body** is the one tail that does *not*
deref: a `Let` owns nothing — it cannot even bind a mutable variable — so it reports whatever its
body reports, handle included, which is what leaves rule 2 an escape to catch. The same
deref would hide an escape one line away from the boundary: reading the
type alone, `λ 𝑐 → (𝑐 += 1; 𝑐)` looks like it returns an `Int` while `λ 𝑐 → 𝑐` returns the
handle. So the escape check walks the tails to the term that actually produces the value.
Every tail is walked, the mutable variable introduction included — a mutable variable does not escape its
own introduction either, so returning one declared inside the function is the same escape
as returning a parameter.

**Neither direction is a subtyping fact**, and the symmetry is the point: `Mut(𝑉) <: 𝑉`
would put a mutable variable *below* its value and `𝑉 <: Mut(𝑉, 𝐷)` would put it *above*, while
`Mut` is invariant in `𝑉`. Either one is a coercion wearing a subtyping rule's clothes,
and — because both fire against a fresh inference variable — neither can distinguish a
read from a handle being passed along. The relation therefore relates a mutable variable only to
another mutable variable, by invariance, and every position that means the *value* says so in the
rule that emits it: `emit::emit_value_read` for an ordinary value position, and `emit_apply` reading
through the parameter's handle for the one position where a `Mut` parameter is given
something that is not a mutable variable (a program the second-class discipline rejects, but which
still has to be typed to be reported well).

## Surface language

The surface syntax and the behaviour a programmer observes — `:=` mutation, `with begin():`
transactions, the read rules (read-your-writes, the trailing induction read, the `Txn`
block-read rule and as-of reads), feeds as the append-law sibling of mutation, `await_final`, and the
ordering-and-concurrency contract — are specified in the
[CHL spec, "Mutability, transactions, and feeds"](../../../docs/chl-spec.md#8-mutability-transactions-and-feeds).
This document specifies the **realization**: how lowering, `mut_elim`, `channelize`, planning, and the
runtime engines eliminate all of it into pure dataflow. The spec is the observable contract;
everything below is how that contract is met.

Two surface facts are load-bearing for the realization and worth restating here:

- **`:=` introduces and writes; `Txn` is never inferred.** A mutable variable is made by the `:=`
  operator, not the annotation; a transactional mutable variable must be spelled `x: Mut(𝑉, Txn) := …`
  (`Txn` never arises by inference). Type application is parenthesised at both the surface and the
  CCL `Display` level, so `Mut(𝑉, 𝐷)` renders the same way throughout this document and in the
  language.
- **A `Txn` mutable variable is read only inside a `with begin():` block, and a fed-out read is an as-of
  sample** (compiled to `AsOf`). The one read that waits for the whole history instead of sampling it
  is [`await_final`](#await_final). These facts drive the
  [as-of-read rewrite](#replies-live-cross-endpoint-reads-and-commit-ordered-taps) and the
  [`AsOf` engine](#the-runtime-engines) below.

> **Design commitment — transactional mutability is deliberately *unordered*.** There is no
> ordering guarantee between transactions on the same `Txn` variable beyond the existence of *a*
> commit order the runtime picks; a program may not assume one transaction serializes before
> another, and nothing in the compiler or engine should impose such an order. The arbitrary-position
> fed-out read above is the direct consequence, **not a defect**: a trailing `with begin(): out <<
> balance` after a loop whose first iteration *denies* may observe the mutable variable before the first commit
> lands (its singleton read samples an early position). The only ways a `Txn` value interacts with
> the world are: read/written **inside** a `with begin():` (rejected outside one — as a feed RHS or
> anywhere else), or observed as a definite committed value through
> [**`await_final`**](#await_final) — the single sanctioned terminal read. Do not add
> inter-transaction ordering to "fix" the early-read case; the unordering is the intended model, and
> `await_final` is where determinism comes from when a program needs it.

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
- `MutDecl { binding, init, body }` — one mutable variable **introduction** (`x := init`),
  binding `x` as a mutable variable over `body`. The declaring half of `:=`, paired with
  `MutWrite` for its writing half; before it existed the introduction was a `Let`
  carrying a `Mut` annotation, and every pass that had to recognize one consulted
  that annotation as a proxy for the declaration. It is the **only** node that binds
  a mutable variable (a pass-by-reference `Mut` parameter aside), which is what makes
  "is this binder mutable?" a question about the node rather than about a type that
  happened to survive inference.
- `MutWrite { name, value }` — one write to a variable. Value `Unit`. Its target **must** be
  `Mut`-typed: inference peels the target's `Mut(𝑉, 𝐷)` and requires `value ⊑ 𝑉`; a write whose
  target is *not* `Mut` is a **type error**, never a shadowing rebind (`x += e` on a plain `x` is
  rejected, not silently turned into `x = x + e`). `x += e` lowers to `MutWrite(x, x + e)`, the
  embedded read being the in-context read.
- `Begin { body }` — one `with begin():` transaction block, made a *single* `Unit`-valued statement
  (`ExprStmt(Begin{block}, rest)`) so a loop body may freely mix a per-iteration transaction, sibling
  induction writes, and feeds. `body` is the per-transaction statement chain. The transaction phase
  strips it: a block writing a `Mut(_, Txn)` mutable variable becomes a commit site (partitioned by mutable variable
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
   mutable variable written outside `with begin():`, an induction accumulator written inside one) are likewise
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

- **Reads deref at the rule that emits them**: `cnt + 1`, `f(cnt)` for an `Int` parameter, and a
  trailing `cnt` all read, and each reads because the rule typing that position asks for a value
  operand (`emit::emit_value_read`). Only a position that *expects* `Mut` — a pass-by-reference
  argument, a write's target — receives the handle. `Mut(𝑉) <: 𝑉` is deliberately not a subtyping
  fact; see [A mutable variable read is an explicit operation](#a-mutable-variable-read-is-an-explicit-operation)
  for why putting it in the relation could not distinguish a read from a handle passed along.
  After inlining, no `Mut`-expecting positions remain, so the phase's rewrite is purely structural
  — every surviving `Mut`-typed occurrence is a write target or a read, decided by context.
- **A read derefs the constraint, not the node.** The deref decides what an operand is
  *constrained against*; the operand's own type slot keeps `Mut(𝑉, 𝐷)`, because that stamp is
  how the phase finds the read in the first place. So the parameter a mutable variable was passed to
  holds 𝑉 while the argument node holds the handle, and a later pass comparing the two is
  comparing types at different levels unless it reads through the handle itself. `inline`'s
  refinement-entailment check is where that bites: an unwritten mutable variable's value type is still
  its seed's singleton, so a parameter left to inference acquires a refinement — one the
  argument does establish, but of the value it denotes rather than of the handle.
- A parameter `Mut(Int)` means `Mut(Int, _)`; the domain instantiates per call site through the
  let-generalization of UDF bindings. Whether a write site requires `Txn` is the phase's structural
  check, post-inline — so one `bump` can serve an induction accumulator and a transactional
  mutable variable.

#### No aliasing: `Mut` values are second-class (downward-only)

Passing a reference *down* is safe exactly as long as the compiler can statically resolve which
introduction every write targets. The discipline:

1. A `Mut`-typed expression must be a **bare variable reference** — an argument to a `Mut`
   parameter is a variable, never a conditional or computed expression. The two halves catch
   different things, because a *conditional* over two mutable variables is not itself `Mut`-typed: a
   mutable read derefs into the arms' join exactly as it derefs into a tuple element (each is a
   value position, above), so `x if c else y` reads their values and types as a plain `V`.
   What the rule is protecting is the write capability travelling somewhere its target can't be
   traced, and that is the **argument** half: `bump(x if c else y)` is rejected on the argument's
   node, not its type.
2. `Mut` may not appear **inside any composite type** — tuples, records, lists, function codomains
   (so it is never a return type), `Feed` payloads, or another `Mut`.
3. A plain `=` off a mutable **reads** it: `b = a` binds `b` at `a`'s value — a
   snapshot, exactly as any other value position reads a mutable variable. This is not a
   rule but a consequence: `emit_let` reads through an initializer that is a mutable variable, so a
   `Let` *cannot* bind a register and the alias is unrepresentable rather than
   rejected. Writing through the copy (`b += 1`) is then the ordinary
   write-to-a-non-mutable error, which blames the write instead of the binding.
   The only mutable variable binders are `MutDecl` (a `:=` introduction) and a
   pass-by-reference `Mut` parameter — both declarations by construction. Pinned
   by `infer::api::debug_assert_no_mut_var_let`.

One structural check after inference enforces the two rules. The real fault line is the **merge law**,
not `Feed`-vs-`Mut`. *Append-only* mutability merges commutatively — a feed by `++`, and (at
runtime) a `Txn` mutable variable by the commit operator's timestamped merge — so multiple writers are
already the semantics and aliasing is benign; that is why `Feed` deliberately stays first-class (it
is returned in `http_serve`'s tuple). *Last-write-wins* mutability instead needs a **resolvable
writer set** — but that requirement is fundamental only for an **induction** accumulator, which
compiles to a single-writer `InductionStore` changelog. A `Txn` mutable variable already tolerates an open writer set (its
sites merge their commit streams by time), so applying the uniform second-class discipline to it is
a conservative stopgap, not a necessity. (Future work splits the same way: the induction aliasing
rule is a blunt approximation of **affine typing** — a use-at-most-once handle keeps the writer
unique by construction while lifting downward-only — and first-class `Txn` needs only a runtime
mutable variable key into the already-keyed MVCC store, not the full sigma/index-types generality.)

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
| `final_or_default` | `(𝐷 ⇒ 𝑉, 𝑉) ⇒ 𝑉` | final value of a completed history; the default if the domain is empty. The trailing induction read (`ExtractFinal`). Over a `Txn` history it is only ever the surface [`await_final`](#await_final)'s read — a fed-out read is an `as_of_read`, a different term |
| `as_of_read` | `(Txn ⇒ 𝑉) ⇒ 𝑉` | a commit history read at an unspecified position — every fed-out mutable variable read. `rewrite_as_of_reads` pairs it with the reading loop that indexes it and builds the `AsOf` join; an unpaired one is a compile error, since nothing downstream supplies a position |
| `await_final` | `Mut(𝑉, Txn) ⇒ 𝑉` | the terminal read of a transactional mutable variable — a surface marker `transact_phase` replaces with a `final_or_default` over the mutable variable's history binding. Its domain is the **handle**, not a value. See [`await_final`](#await_final) |

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

### Tagged sums in a decision, and in a mutable variable

A decision is a **choice**, and the two things it chooses between carry different data: a grant
carries a write set, a denial carries nothing. Today that is encoded as a record with a `commit:
Bool` beside a `writes` field that is meaningless when `commit` is false — a product standing in for
a sum, so nothing stops a reader consulting `writes` on a denied decision. The direction is the sum
itself, `` `commit(writes) `` / `` `abort(unit) ``, which makes the write set reachable *only* on the
granting path.

What exists today is the algebra that shape needs, in both directions:

- **Introduction.** A writer decision is a value-`Case` inside the writer lambda, so a
  variant-valued arm has to be a *composable morphism* `param_ty ⇒ Union` — the RHS of a `≫` in the
  fan-out `⧺ᵢ (filter_values(π̂ᵢ) ≫ 𝑒ᵢ)`. That is `variant_wrap(𝑐ᵢ)`, and `lambda_elim` elaborates a
  `VariantCtor` in a lambda to `𝑒ᵢ ≫ variant_wrap(𝑐ᵢ)` to produce it.
- **Elimination.** Reading the decision back is a scrutinee-`Case`, compiled to the union of
  tag-restricts `⧺ᵢ (𝑑 ≫ variant_project(𝑐ᵢ) ≫ (λ 𝑤ᵢ → 𝑒ᵢ))` — a `≫`-chain, since `𝑑` is the
  eliminated scrutinee morphism and both elements after it are functions of its output. The per-key view is the shape that
  needs the *outer-binder* form, because its arm reads both the record's sibling field and the
  granted payload: ``λ 𝑐 → match 𝑐.decision { `commit(𝑤) → (time: 𝑐.time, write: 𝑤.𝑖) }``. There the
  projection is zipped alongside the whole element so the two co-iterate by key.

Both are specified in [design-operators.md](../../interpreter/design-operators.md#tile-operators) (the `VariantWrap` and `VariantProject` rows).

**A variant-valued mutable variable** follows from the same law, and needs nothing specific to
mutable variables. A
mutable variable's seed and its writes are *alternatives at one position*, exactly as a conditional's arms
are, so the mutable variable's value space is their **join**: a `` `none `` seed with `` `some `` writes is
the two-tag sum `` {`none | `some{Int}} `` with the arm that did not occur left empty, and every
emission is built at that declared space rather than at the width of whichever alternative occurred.
``acc := `some(𝑖)`` under a `` `none `` seed, and a conditional write choosing between tags, are both
just that.

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
  → as-of-read rewrite (bare history reads fed out of read-only blocks → AsOf)
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

### How many commit stores a program has

**One per set of mutable variables a `with begin():` block relates** — not one per program, and
not one per mutable variable. `transact_phase::partition_keys` computes the partition; each part
becomes its own `LetRec`, its own `Transact{domain: Txn}`, and its own `CommitOperator`. The
induction path partitions the same way: `mut_elim::transform_loop` emits one letrec per loop.

A block is what forces mutable variables together, for two reasons that coincide on the block's
footprint. The store is not a user-facing concept: the
[CHL spec's ordering model](../../../docs/chl-spec.md#85-ordering-and-concurrency) says only that
two blocks are ordered when they mention a mutable variable in common, and that blocks sharing no
variable are unordered. The partition is how that is realized — a program never has to reason
about it.

- **Atomicity.** A writing block produces one commit record, so every key it *writes*
  advances at one tick, and every key it *reads* is read at that tick's snapshot.
  `{reads ∪ writes}` is therefore one store — which is why the `limit` a guard consults is
  in the same store as the `total` it guards, though nothing writes `limit`.
- **Snapshot consistency.** A read-only block's reads are latched at one frontier, which
  `rewrite_as_of_reads`'s `build_snapshot` realizes by handing `AsOf` a single mutable variable
  record. Keys read together must be in that record. Such a block is *unwrapped* onto the
  spine and leaves no `WriterSite`, so `strip` keeps its footprint explicitly
  (`Stripped::read_only_footprints`).

Nothing else forces sharing. Two consequences are observable:

- **Completion.** A store reports terminal only once all of its writers have drained,
  and a fed-out read is an `AsOf`, non-terminal until its store is. So a finite mutable
  variable's trailing read settles even while an unrelated mutable variable has a live-source
  writer (`a_finite_mut_var_completes_despite_a_live_unrelated_writer`).
- **Commit clocks.** Unrelated mutable variables share no commit order, so nothing imposes an
  interleaving between transactions that never interact.

A mutable variable **no block writes at all** is not a key of any store, and relates nothing by
being read. Nothing can advance it — the lowering write gate admits a mutable variable write only
inside a block, and a block write would put it in a write set — so its history is constant at its
seed and every read of it is that seed. It keeps its introduction on the spine. Only a read-only
footprint reaches this case: `limit` above is unwritten too, but a *writing* block reads it, which
makes its value a question about a commit snapshot rather than about a constant.

**Placement.** `plan_store` plans each store (its keys' history bindings, its writers'
commit records, its taps) and `splice_stores` places them in one spine walk. A store's
letrec sits below everything its bindings need — a writer's iteration source, chiefly —
and above everything that reads its keys. Each spine statement gets a **level**: 0 if it
reads no store, else one past the last store it reads, transitively through statements
already carried. Level 0 keeps its place above every letrec; the rest ride inside the
store they read. A statement cannot read two stores at once, which is what makes the
level well-defined — reading two mutable variables together is a block, and the partition put
those keys in one store so the read has one snapshot to come from.

"Reads a store" means *names anything that store's body binds*: a key, a history binding, or a
**defer fed inside the store** — either an in-block feed, whose tap the store's body binds, or
the feed of a read-only block, carried in as an effect statement. The defer has no fallback: a
key left above the letrec would still find its seed introduction, whereas a defer fed only inside
the store exists nowhere else. That is also why an effect statement counts for the transitive
step — it binds no name, but it contributes to one.

The folded cross-domain induction loops (`CrossDomain`) get a level of their own, by the
same rule. Outermost is the usual answer and what the invariant demands — an accumulator a
commit decision reads must be bound outside any store that reads it, and outermost
satisfies that for all of them at once (`a_cross_domain_read_coexists_with_a_second_store`).
But the group can itself depend on a store, through an [`await_final`](#await_final), so
`cross_level` puts it inside the innermost store it *reads*. The two demands never
conflict, because an awaited variable's writers all precede the await while a store reading
the accumulator commits after the accumulator's loop
(`a_cross_domain_accumulator_depending_on_an_await_nests_inside_that_store` pins the
induction carrier landing *between* two commit stores).

**One post-condition covers all of it.** The level assignment, the cross-domain level, and
the store nesting order are three separate arguments that a reference stays in scope, none
of them enforced by the shapes being built — so `splice_stores` release-asserts the thing
they are all arguments *for*: the placed tree may not have gained a free name. An escape
survives the strict typecheck and would surface much later as an unrecognised variable in
op-conversion.

Both paths close a group through one shared routine, `mut_elim::close_recurrence_group`
— trailing reads, then feed hoists, then the causality assert, then the `LetRec`. The two
differ in how they *find* their bindings and where the group is spliced, not in how a group
is closed.

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

A transactional mutable variable and an induction counter shared across two HTTP endpoints:

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
the block by mutable variable domain, lifting each top-level-spine induction `MutWrite` onto the enclosing loop
as its own recurrence while the mutable variable writes form the commit decision. Because the write is lifted
out entirely, block placement is *inert* for it — a bare in-block induction write is **exactly the
out-of-block form** (it fires once per iteration unconditionally, independent of whether the co-located
transaction commits). A **guarded** in-block induction write (`if q: cnt += 1`) is a different matter:
committing it only when the transaction commits needs commit-gated carry-forward (the value-`Case`
machinery upstack), so today it is **rejected** (`check_no_guarded_induction_write_in_block`) rather than
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
- **`balance`** — the mutable variable's history: at any `𝑡`, the latest earlier commit's write, else the
  initializer. The `balance ↔ incr_commits` cycle is well-founded — the trip around it crosses
  `get_prev_txn` once, so position strictly decreases.
- **`cnt`** — the induction recurrence, self-referential through `get_prev_seq` (causal); its domain is `IncrIdx`, not
  `Txn`, because its annotation said so.
- **`incr_resps`** — the reply for `𝑟` depends on `incr_commits(𝑟)` (then discards it): the reply is
  sequenced after the commit.
- **`get_resps`** — the fed-out mutable variable read: `read_at_get` picks the GET's *observation time* (a `Txn`
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
- **Deny** (`if` around a write, no path taken) is the decision's **`` `abort ``** tag; `get_prev_txn`
  skips it. A denied transaction contributes no visible write and no reply. A *committing*
  transaction is **`` `commit(⟨writes, replies⟩) ``** — the (dense) write/reply payload rides the tag, so
  an illegal "no-commit yet real writes" state is unrepresentable.
- **Induction and transaction domains are independent.** In the worked example's model form `cnt`
  advances per request even though its write sits inside the block (a mix the current lowering
  rejects — see the caveat there); only `Txn`-domain variables participate in the atomic commit. A
  program that needs the counter transactionally consistent with the mutable variable declares it
  `Mut(Int, Txn)`.
- **Liveness.** Induction domains are finite or stream-complete; `Txn` histories complete when all
  writer sources do. A fed-out `Txn` mutable variable read reads as-of its own position in the commit
  clock and does not wait for completeness. The one term that waits for a mutable variable's
  completeness is [`await_final`](#await_final), and it is well-defined because it closes the writer
  set: the mutable variable is unreferenceable afterward, so no later writer can extend the history it
  just declared complete.

## Ordering and concurrency

The observable ordering contract — maximum parallelism subject to dependency edges rooted at **events**
(program start, source arrivals, forced data dependencies, `await_final`), and the guarantees a program
may rely on — is specified in the
[CHL spec, "Ordering and concurrency"](../../../docs/chl-spec.md#85-ordering-and-concurrency). This
section records the **realization** side: how the engines deliver that contract, and which points
remain open in the model.

**Engine freedom, stated symmetrically.** The two loop engines sit at opposite ends, and the contrast
is why dispatch on the sequencing domain is load-bearing (not an optimization):

- **Induction (`InductionStore`)** reads position `𝑖-1`, so it is a *strict total-order data-dependence
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
for one mutable variable.

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
| a binding referenced only via `get_prev_seq(𝑏, …)`, over a finite/stream induction domain | `InductionStore` — the position-driven changelog loop engine (read densely via `StoreDenseRead`) |
| commit-record bindings + `begin_<site>` oracles + `Txn` histories read via `get_prev_txn` | the commit operator (`CommitOperator`, `TransactDriver`, `TransactWriter`, cyclic `FanOut`, `StoreValueStream`) |
| a `Txn` history read out of a read-only block (any reading loop — a live request stream, a finite loop, or a standalone singleton) | the as-of read (`AsOf`), latching the store's value as of the reading transaction's position, indexed by the outer reading loop |
| a non-causal cycle, or a causal shape loop planning does not know | compile error (no silent fallback) |

### The runtime engines

- **`InductionDriver` + `InductionStore` (+ `StoreDenseRead`)** — the induction loop, as a cycle
  through a `FanOut::new_cyclic`. The store consumes the body's decisions and writes a
  `Tile::Store` changelog (`init` at position 0; a `commit: false` position carries the prior
  value forward); the driver reads that changelog back to produce the body's `(prev…, item)`
  input, taking the next position from the decided frontier and the prev-accumulator from the
  value at it. The accumulator therefore crosses between them as a tile, like every other
  operator-to-operator value, at one position per pull. `StoreDenseRead` then folds the
  changelog over the loop domain to the dense `𝐷 ⇀ 𝑉` stream (serving both a scalar-final
  `ExtractFinal` and a co-iterated `fan_in`). A single always-commit or commit-gated writer over a
  finite *or* async domain.
- **The commit operator** — the concurrent generalization of the induction accumulator, for the `Txn` domain. The
  store is an MVCC commit log `Txn ⇀ (Key ⇀ Value)`. A writer reads a snapshot of its footprint,
  runs its pure body, and proposes `{reads, writes}`; the operator validates the read set against
  the current store (backward / optimistic concurrency) *before* allocating a timestamp — a valid
  proposal commits and consumes a tick, a stale one is skipped and retries against the advanced
  snapshot. Disjoint footprints commit concurrently; overlapping ones serialize. `release` is the
  commit acknowledgment (the retry signal rides the existing producer/consumer channel). The store
  compacts by the MVCC law and GCs the released prefix.
- **`AsOf`** — the as-of (temporal) join: **every** fed-out `Txn` mutable variable read, regardless of the
  reading loop's domain. Given a *trigger* (the reading loop — the positions to sample at) and a
  *source* (the store), it latches, for each trigger position, the store's value as of the moment
  that position is first observed. The output is indexed by the **trigger** (the outer reading loop),
  not the commit clock — which is why a reply matches its reader by position and needs no explicit
  correlation id. It is the dual of the induction accumulator: the induction accumulator latches a private accumulator per
  source step; `AsOf` latches the store's current value per trigger step. It is a *sample at
  observation time* — an arbitrary as-of position, which is exactly the read a transaction gets: the
  store as of where it lands in the commit order. A *standalone fed-out* read is the
  singleton-trigger case of the same `AsOf`, latching at its own arrival like any other: the
  position is arbitrary whatever the trigger's domain, and a program that means the final value
  spells it [`await_final`](#await_final).
- **`StoreValueStream`** — projects one key's `CommitTs ⇀ V` commit-value stream by folding the
  store changelog. It backs the **in-block reply tap** (`out << e` inside a block — a per-commit,
  commit-tick-indexed event stream), is the fold `AsOf` samples, and is what `ExtractFinal` reduces
  for an [`await_final`](#await_final) — no new engine, the same `final_or_default → ExtractFinal`
  path a post-loop **induction** accumulator and a **broadcast source** (a sibling loop's final, fed
  into a commit decision) already take, applied to a `Txn` history.

The two loop engines are **not interchangeable**: the commit operator is built for an open commit
clock and mis-drives an incremental/live source, while the induction accumulator is the ordered loop recurrence.
Dispatch on the sequencing domain is load-bearing, not an optimization.

### Watermarks

A consumer reading "as of `𝑡`" must know no further commits will land at `≤ 𝑡`. The runtime already
carries this: function tiles hold a `domain_predicate` marking the complete region of the domain. A
watermark *is* a `domain_predicate` advancing over `Txn`. Conflict validation — which depends on
which value combinations were observed — is deliberately engine-level, above the tiling algebra,
because that is exactly what domain predicates cannot express.

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
  is also what first-class `Mut` (returning or storing references) needs: carrying mutable variable identity in
  types is a sigma/index-types question. Until then the second-class discipline is the aliasing
  firewall.
- **History access / auditing** — `get_prev_*` generalized to user-facing reads at explicit
  positions; the transaction handle (`t = begin()`) already names the position.
- **Recursively-defined values** generally — the `LetRec` node and causality check are the general
  mechanism; only loop-planning patterns need to grow.

## Reading an induction accumulator in a commit decision

A commit decision may read an induction accumulator at its request position
(`with begin(): balance += cnt` — the mutable variable write folds in `cnt(r)`). The intended letrec is the
[worked example](#worked-example)'s: `𝑐𝑛𝑡` (induction, `IncrIdx`) and `balance`/`incr_commits`
(transaction, `Txn`) mutually in scope, so `incr_commits(𝑟)` reads `𝑐𝑛𝑡(𝑟)`.

**CCL — outer induction letrec, accumulator threaded through the writer source.** The transaction
phase folds the entangled induction loop (via `fold_induction_loop`, shared with `transform_loop`)
into its own **outer** single-binding induction letrec wrapping the transaction letrec — dependency
order, since `incr_commits` reads `𝑐𝑛𝑡` and `𝑐𝑛𝑡` is self-guarded — so `recognize` nests the two
carriers (`InductionStore` outer, commit engine inner) with **no** cross-domain group logic. The read itself
rides the **writer source**: an accumulator the decision reads is zipped into the source,
`source ↦ λ 𝑟 → (reqs(𝑟), 𝑐𝑛𝑡-view(𝑟)) : 𝐼 ⇒ (item, 𝑉)`, and the decision body reads it off the item
tuple's slot. This keeps recognition's writer round-trip intact — `recover_writer` lifts the source
verbatim (a `zip` is opaque to its shape parser), so no recognition change is needed.

**Engine — co-iterating the accumulator with the loop source.** Two small changes carry it:

- *`zip` conversion.* An arm of a `zip` that reads a mutable variable (`__cnt.acc`) is a **leaf** source over its own
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

The one engine subtlety is **driving** that broadcast to convergence. The final's `ExtractFinal` is
empty until the sibling loop's `InductionStore` drains (one position per body pull), and nothing external
re-pulls the writer: the store's own convergence loop stops once the commit frontier stalls, and the
frontier cannot advance until this writer commits, which needs the value still converging. The writer
resolves this the same way the mutable writer resolves its own one-step-per-pull convergence (see #291): when
its decision body is not ready, it re-arms itself on the scheduler's **deferred-wakeup queue**
(`WakeupQueue::request`) and returns non-terminal, keeping its pending body-input row so a re-pull
reuses it (a re-push would duplicate a buffer position against the body's `Memo`). Each demand-driven
re-pull advances the sibling loop one step until the decision is ready — no blocking loop inside
`get`, and it composes with an async sibling source (the source's own notification drives the
re-pulls). A fed-out read *of* the result mutable variable is an `AsOf` (an in-block reply tap, or a trailing
standalone read), which demand-drives this convergence: each committed reply pulls the writer, which
advances the sibling loop, exactly as an in-block reply drives the writer in the co-indexed case. The
co-indexed and non-cross paths are untouched.

(Note the asymmetry: the broadcast **source** — the sibling induction loop's accumulator — *does*
have a final, read via `ExtractFinal`, because an induction loop terminates and its final value is
denotable. The result **mutable variable** does not: a `Txn` mutable variable has no final-value term, so reads of it
are `AsOf`, never `ExtractFinal`.)

## Replies: live cross-endpoint reads and commit-ordered taps

A `<<` reply takes one of two forms, by where it sits relative to the `with begin():` block.

**As-of read (reply *of* a mutable variable, outside the writing block).** A read-only block
`with begin(): resp << 𝑒` reading a `Txn` mutable variable replies the mutable variable as of the reading transaction's
position. The pre-lambda-elim `rewrite_as_of_reads` turns it into an as-of join indexed by the reading
loop, not the commit clock — uniformly, whether that loop is a live request stream, a finite loop, or
a standalone singleton (the live cross-endpoint read is one instance, not a distinct compilation).
Three shapes:

- **one mutable variable** — `as_of((trigger, balance.f)) ≫ (λ 𝑘 → 𝑒)` (`resp << balance`, `resp << balance + 1`);
- **several at one snapshot** — `as_of((trigger, {fᵢ: histᵢ})) ≫ (λ snap → 𝑒[𝑘ᵢ ↦ snap.fᵢ])`
  (`resp << a + b`), one whole-variable snapshot per request (§I-c);
- **request element combined with a mutable variable read** — `zip((trigger, as_of((trigger, source)))) ≫ (λ p
  → 𝑒[req ↦ p.0, 𝑘ᵢ ↦ p.1(.fᵢ)])` (`resp << balance + req`): the request rides alongside its mutable variable
  snapshot. The `as_of` arm is a leaf that op-conversion's `zip` co-iterates with the request stream
  (the same `is_leaf_zip_arm` path as the commit-decision read above) — no new operator.

**commit-ordered / commit-gated reply (reply *inside* the writing block).** A `<<` inside the block
rides the writer decision as a `to_<defer>` tap, committed atomically with the mutable variable write and
read back as a per-commit value-stream (commit-tick-indexed). So it is **sequenced after the commit**
and **gated**: a denied transaction (`if 𝑝:` false) proposes no write and emits no tap, replying
nothing. The tap may read an induction accumulator (`resp << cnt`), which composes with the
commit-decision co-iteration above. Contrast a sibling reply *outside* the block (`resp << cnt`),
which rides the induction domain and fires every iteration regardless of commit — value-correct,
request-indexed, but not commit-ordered. To gate or commit-order a reply, put it in the block.

## `await_final`

The **terminal read of a transactional mutable variable**. Surface, semantics, and the
unreferenceable-after rule are specified in the
[CHL spec, "`await_final`"](../../../docs/chl-spec.md#86-await_final-decided); in the [ordering
model](../../../docs/chl-spec.md#85-ordering-and-concurrency) it is the commit-domain analog of
loop completion — a **completeness** edge on the `Txn` domain.

**A sample, not a reduction.** A `Txn` read takes the key's carried value at some commit
position, and this read's position is where `𝑥`'s writers finish. `await_final(𝑥)` becomes
`final_read(𝑥.history)`, which op-conversion compiles to `StoreFinalRead` over the store branch.
That operator takes the same sample the fed-out as-of read does, through the same `store_current`;
the two differ in what fixes the position — a trigger's arrival there, the store's own closure here.
Neither term carries a seed operand, because tick 0 of every store is its keys' seeds.

Completion is **coarser than the contract**: `StoreFinalRead` waits for the whole store, so an
await settles once every writer of the *store* has drained rather than every writer of `𝑥`, and a
variable whose own writers are finite waits on a store-mate's live writer. Closing the gap takes one
fact and one disjunct: the store publishes which keys can no longer be written, computed from the
per-writer write footprints `WriterSite::write_keys` holds at the CCL level, and the operator's gate
becomes that fact or the store's own closure.

A key **no writer site writes** never reaches the operator. `resolve_writer_free_awaits` replaces
its await with its seed, its write history being statically empty. That covers a variable no block
mentions and a variable some block only reads — a footprint key under `{reads ∪ writes}`, whose
runtime completion would otherwise wait on writers that cannot write it
(`a_read_only_mentioned_key_completes_while_a_live_writer_runs`).

`resolve_await_finals` mints the read at the await's own site, and placement then needs no
await-specific logic: the resolved read names the history binding, which is already how a statement
is carried into its store (["How many commit stores a program
has"](#how-many-commit-stores-a-program-has)).

The two reads are separated by **term**, not by position: a fed-out read is
`as_of_read(⟨history⟩)`, and only that term is what `rewrite_as_of_reads` matches. Position alone
would not hold, because a pass may legitimately move a read — `channelize` copies a channel's
captured bindings inside the channel it closes, which lands a bound await's read
(`f = await_final(pool)`, read by a feed loop) directly above the broadcast, where the rewrite
matches (`await_final_bound_then_read_in_a_feed_loop_stays_final`). Distinct terms also make a
missed pairing loud: an unpaired `as_of_read` is rejected at the end of the rewrite, where spelling
it `final_read` would compile it to a terminal read that waits for a store nothing will drain.

The operand is the mutable variable **handle** — the third position alongside a pass-by-reference
argument and a write target (["A mutable variable read is an explicit
operation"](#a-mutable-variable-read-is-an-explicit-operation)). `Builtin::AwaitFinal`'s scheme
`∀ν. Mut(ν, Txn) ⇒ ν` pins the domain, so awaiting an induction accumulator is a type error; and
lowering resolves 𝑥 by name, as it does a write target, rather than through the value-reading path
whose out-of-block gate would reject the very read this is.

**Four rules, in three places.** Two are order-independent and belong at lowering: the operand must
be a `Mut(_, Txn)` mutable variable named bare, and the await may not sit inside a `with begin():`
block. The other two need the inlined tree in source order — lowering folds its statement chain
right-to-left, and a callee's mention becomes a read, a write, or a `Begin` only once inlined:

- `check_await_final_linearity`, post-inline beside the other transaction pre-checks — the mutable
  variable is **consumed**: no `Var` or `MutWrite` naming it may follow its await.
- `check_store_acyclicity`, inside the phase because the rule is *store*-relative and the partition
  is what decides which awaits a given writer or seed may not depend on — **a store may not depend
  on its own await**. An await of a key in another store is an ordinary one-way edge between
  two recurrences, which is what makes **phase separation** — drain one transaction, seed the next
  from its final value — compile.

**A mutable variable no `with begin():` block mentions** is a key of no store, so it has no history
binding to read and its await resolves to the seed directly (`resolve_writer_free_awaits`) — the
empty-history case, known empty statically. An all-deny history is the other case: it does build a
store, and its `final_or_default` reports the seed as that store's default.

## Not yet implemented

These features belong to the model above but are not yet built. Each is rejected at compile time
today rather than silently mishandled.

### Value-selecting `Case` and conditional induction writes (partially implemented)

> **Status: value-selecting `Case`s and conditional induction writes both compile.**
>
> **Implemented**: scalar / compute ternaries (the C-form), data-collection selection (the gate
> fan-out, reconciled to the Σ by Σ-introduction), source-less conditional
> feeds, a **conditional element** in a comprehension (`[a if g(x) else b for x in xs]`, fanned out
> over the source by the element-dependent gate), a comprehension **over a conditional collection**
> (`[f(x) for x in (xs if c else ys)]`, the source `Case` floats out of the map), a conditional
> **between** standalone comprehensions (`([…]) if c else ([…])` — the maps carry `Data` after kind
> inference, so their arms join into a Σ), a **conditional induction write** (`if 𝑝: total += x`
> — one commit-gated writer over the changelog, below), and an **`if`/`else` that writes both arms**
> of one accumulator (`if 𝑝: acc += a else: acc += b`) — the per-accumulator value-`Case` write set
> compiles via the value-preserving `filter_values` union-of-restricts inside the writer lambda (see
> below and `../../interpreter/design-operators.md`). That desugar also resolves the former residual —
> a value-selecting `Case` inside a lambda with no visible iteration source (a UDF body, or a
> comprehension `if`-filter beside the element `Case`). A conditional *feed* on an induction path
> (`if 𝑝: out << e`) is **implemented** — it rides the same decision as a `to_<defer>__fire`-gated tap
> (below).

The *filter* `Case` (`[𝑔 → action; true → unit]` → `Restrict`), the value-selecting `Case`, and the
conditional induction write all compile. The value-`Case` compilation is a **literal union of
restricts** — the CCL algebra stays restricts + unions — and an **off-path arm is never evaluated**,
so a guard-protected partial expression (`x // y if y != 0 else 0`) never faults on the path its guard
excludes. A **data-collection** fan-out is lazy structurally: an arm whose gate is false restricts to
an empty extent, and an empty extent is never iterated. The **scalar** value-`Case` C-form gates a
`Units(1)` driver and swaps in each arm's constant via `MapResultToConst`; when a false gate empties
the driver (all rows deleted), `MapResultToConst` returns a terminal-empty tile *without* pulling the
arm's constant — so the off-path value (a `//`, `%`, or index that the gate guards) is never computed.
Every fan-out shares one first-match encoding, `πᵢ = 𝑔ᵢ ∧ ¬⋁ⱼ˂ᵢ 𝑔ⱼ` (`synthesize_arm_predicate` in
`ccl_utils`, shared between channelize, the value fan-outs, and the transaction path walk).

A **conditional induction write** takes a different, simpler route than the value fan-out: it rides
the induction accumulator's own `` {`commit{writes} | `abort} `` **decision variant** rather than a union of
restricted sources. `lower_loop_body_chain` lowers `if 𝑝: acc += e` to a statement-position `Case`
(`[𝑝 → acc += e; true → unit]`), and `mut_elim::transform_chain`'s `Case` arm merges its
branches into **one uniform, carry-complete writer decision over the full loop source**: a committing
position is `` `commit(⟨writes⟩) `` and a full-carry (non-writing) position is `` `abort ``. The commit
selector is `⋁ⱼ π̂ⱼ` (the disjunction of the writing branches' first-match guards — the value-`Case`
guard that picks the `` `commit `` arm; `ccl_utils::wrap_decision_variant` folds it into the tag), and
each accumulator's `writesᵢ = Case[π̂ⱼ → wⱼᵢ; …; true → snapshotᵢ]` — a per-accumulator value-`Case`
whose trailing `true` arm is the **carry** (the entering accumulator). `` `abort `` positions are dropped
from the changelog store (`InductionStore`, see `../../interpreter/design-operators.md`) — sparse —
and the carry arm keeps the `` `commit `` payload **dense** (total at every committing position). So the `Overwrite`/`Feed` distinction and
the carry-forward live *inside one decision on one writer* — no per-leg restricted source, no
complement leg, and none of the cyclic-convergence hazard a restricted-source multi-leg realization
carried. Recognition packages it as an ordinary single-writer `Transact`; op-conversion routes it to
the changelog store, and reads fold the changelog densely (`StoreDenseRead`). The per-accumulator value-`Case` is value-selecting inside the writer lambda,
compiled to the **value-preserving `filter_values` union-of-restricts** (`⧺ᵢ filter_values(π̂ᵢ) ≫ eᵢ`;
`Builtin::FilterValues` → the `Filter` tile op, flat-merged with `UnionOperator::new_flat`) — an
off-path arm is never evaluated, so a **partial op** (`//`) in a written value never faults at a
guard-rejected position. See `../../interpreter/design-operators.md`.

Both a **finite** loop and an **async** (streaming) source drive an induction accumulator — the
model treats a finite domain as a stream that terminates (§Liveness) — and every induction accumulator
uses *one* realization: the changelog `InductionStore`. Plain, conditional, and feed-carrying loops
over finite or async extents all route through it. The
driver reads its source by absolute domain position (async domains arrive unordered), reclaims the
consumed prefix as it advances, and carries reply feeds as `__fire`-gated taps — see *Induction
stores as a changelog* in `../../interpreter/design-operators.md`.

The value-`Case` positions ride the same union-of-restricts:

- **Scalar / compute-typed selection** (a ternary, a per-key merge inside a decision body)
  — *implemented* (`lambda_elim::build_value_case_cform`): restricts of gated one-shot lifts over
  the `UIntRange(1)` driver, extracted by the rewrite itself —
  `((unit | π̂₀ ≫ const 𝑒₀) ⧺ … ⧺ (unit | π̂ₙ ≫ const 𝑒ₙ), 𝑒ₙ) ▷ final_or_default` — exhaustive by
  the trailing `true` arm, so the union has exactly one element and the outer type is unchanged.
  The gate is constant in the driver element; the existing `Restrict` masks the extent by the
  constant boolean directly (no new runtime capability).
- **Data-typed selection** (`zs = xs if c else ys`) — *implemented*
  (`lambda_elim::build_value_case_fanout`): each arm's whole collection restricted by a
  constant-in-element gate, then assembled with `DisjointJoin` over the one domain the arms
  share (see `design/type-inference.md`, "4.6 Data vs compute functions"). The gate rides a
  **`cast`** whose target refines the arm's domain — the same shape a comprehension filter lowers
  to — rather than being written onto the arm's type in place. Planning reifies a domain
  refinement into the arm's `restrict`, but only at a site it recognizes as not-yet-materialized,
  which is a question about the *term* (`is_iteration_bearing`); refining the type alone answers
  it with whatever node sits underneath, so a literal arm would keep its gate while an arm naming
  a collection (`xs`) would silently lose it and contribute its rows unconditionally. A refinement
  no term carries is one nothing downstream is obliged to honour. The join lands on that domain
  and carries the type the type system gave the `Case`, so the strict `typecheck` pass has no
  coproduct claim to undo. Arms at differing domains have no shared domain to land on and
  inference rejects them, so the fan-out is only built at one domain; `Σ` is the recorded design
  for the differing case (`design/type-inference.md`, "The domain join is a Σ"), where
  **Σ-introduction** relates a structural `Variant`-domain type to the Σ — the compiled gated
  partition realizes the whole sum, by the finite-Σ = gated-coproduct iso with the legs' base
  domains set-equal to the candidates. `elif` chains flatten to one N-choice
  partition first. A conditional collection is *consumed* (aggregate, program result) via the
  `Σ <: Fun` subtyping rule, and *through a comprehension* by floating the source `Case` out of the
  map (see the comprehension bullet below).
- **Source-less conditional feeds** (`if c: o << 1 else: o << 2` outside any loop) — *implemented*
  (`channelize`): each feeding arm becomes a gated one-shot lift `λ __unused : {Unit | π̂ᵢ} → 𝑣ᵢ`,
  one channel per arm — replacing `PartialFeedCaseUnsupported` for guard-only `Case`s. A
  scrutinee / pattern feed stays rejected; a no-else partial feed is still blocked earlier at
  lowering (bare `if` as a value expression).
- **Comprehension over / with a conditional** — *implemented* (`lower::comprehension`). Two shapes,
  both fanning out the source (a value `Case` has no fixed driver, so it must gate the *iteration
  source*, not a `Units(1)` one): a conditional **element** (`[a if g(x) else b for x in xs]`) fans
  the source out by each arm's *element-dependent* gate — `⧺ᵢ [eᵢ for x in xs if π̂ᵢ]`, a union of
  filtered maps (`fan_out_element_case`); a conditional **source** (`[e for x in (xs if c else ys)]`)
  floats the source `Case` out of the map — `Case{gᵢ → [e for x in srcᵢ]}`, each arm a data-kinded
  `Compose` so the arms `sigma_join` (`float_comp_source_case`). Both reduce to constructs already
  compiled (the filter refinement, the gate fan-out); neither duplicates the loop, only the map.
- **Bound-then-used values in a loop feed** (`x = 𝑒₁ if 𝑝 else 𝑒₂; o << f(x)`) — *deferred*
  (case-float in the loop-body / feed path, distinct from the comprehension forms above):
  `𝐶[Case{[𝑔ᵢ → 𝑒ᵢ]}] → Case{[𝑔ᵢ → 𝐶[𝑒ᵢ]]}` (sound by purity) then the channel fan-out generalized
  from feed-arms to value-arms — only the fed context duplicates, never the loop.

### General in-transaction conditionals (and conditional writes)

A `with begin():` block admits `if`/`elif`/`else` and multiple sibling `if` guards, compiled by a
uniform **path-based** walk (`transact_phase::walk_block`/`walk_case`).

A **path** is one straight-line route through the block's branch structure: the statements a single
execution runs, given a choice of arm at every `if`/`elif`/`else` it passes through. Nested and
sibling conditionals multiply, so a block with two independent `if`s has four paths. Each path
carries a **path condition** — the conjunction of the guards it took, each `elif` guard first-match
adjusted (`π̂ᵢ = 𝑔ᵢ ∧ ¬𝑔₀ ∧ … ∧ ¬𝑔ᵢ₋₁`). A path condition is a `Bool` expression over the
transaction's *snapshot* alone — resolved through whatever the path has already written
(read-your-writes), but never reading a later commit tick, which is what keeps the whole block one
serialization point. The block's **spine** — the statements outside every
`if` — is the path condition `true`; descending into an arm narrows it to `path ∧ π̂`. Paths are
mutually exclusive and, taken together with the implicit empty arm of a guard that matches nothing,
exhaustive: exactly one path runs per transaction.

Paths are a *compile-time* enumeration, not a runtime branch: the walk visits every path and emits
**one** decision variant, whose `` `commit ``/`` `abort `` tag and per-tap fire fields are path conditions
and whose per-key writes are `Case`s over the local branch guards — so every path is evaluated in
one straight-line writer body and one transaction is still one decision. Walking a block threads
`(path, env)` (read-your-writes) and the block denotes
`` snapshot ⇒ {`commit{writes, to_<defer>*} | `abort} `` — a decision **variant**
(`ccl_utils::wrap_decision_variant`) where:

- **the `` `commit ``/`` `abort `` tag is chosen by the disjunction of the path-conditions of every
  mutable write and feed** (`or_commit`; an empty taken path — a position matching no guard, including a
  missing `else` — is `` `abort ``). A spine write's path is `true`, so a write beside a guard commits
  unconditionally: **a guard scopes only its own arm's writes**, not the whole transaction. (This
  subsumes the former single-deny: `if 𝑝: x := 𝑒` → one write at path `𝑝` → `` `commit `` iff `𝑝`,
  observationally identical.) The whole-transaction grant/deny is the *tag*, not a `commit` field — an
  illegal "denied yet real writes" state is unrepresentable.
- **each written key is rejoined as a carry-forward `Case`** over the branch structure
  (read-your-writes; a branch that does not write a key contributes its snapshot value). An
  unconditional write never enters a `Case` (it stays a bare write); cross-key routing
  (`if 𝑝: a := … else: b := …`) routes each key per path.

The per-key merges are value-selecting `Case`s over the snapshot inside the writer lambda, compiled
to the **value-preserving `filter_values` union-of-restricts** (`⧺ᵢ filter_values(π̂ᵢ) ≫ eᵢ`; the
retired eager `FunctionDef::Select` is gone) — so a **partial op** (`//`, `%`) in a merge value is
evaluated only where its guard holds, never at a rejected position. The block stays **one decision
variant per transaction** — per-path writer sites are unsound (a path
predicate reads the snapshot, which exists only at the commit tick; one `begin()` is one
serialization point; multi-key read-your-writes needs one snapshot and one write-set).

A conditional feed under genuine cross-key *routing* fires only on its own route. A feed under one
arm would otherwise ride the transaction's (broader) commit and over-fire on a sibling route's
commit, so each such tap carries a **per-tap fire field** — `to_<defer>_k__fire : Bool`, its own
control-flow path (`F_FIRE_SUFFIX`) — that the commit engine (`body_decision_at`) checks: a committed
transaction appends the tap only where its fire gate holds. A single-guard feed (`if 𝑝: w; out << 𝑒`,
path == commit) and a spine feed omit the field and fire with their transaction — so unconditional
programs keep their fire-field-free shape.

A write key written *only* conditionally (an absolute `k := 𝑒` inside a `Case` arm, never read) is
finalized into the *read* set by `collect_footprint`, so it has a snapshot to **carry** on the paths
its arm does not fire; a read-modify-write already reads the key, and a purely spine (unconditional)
write needs no carry and stays write-only.

**A leading deny is ordinary.** A block that denies (matches no writing/feeding guard) at the first
transaction leaves the store's first commit to a later position, which no read has to accommodate: a
fed-out read samples at its own arrival and may see the seed at any position, and `await_final`
reduces the whole history whatever order the commits land in
(`tx_if_elif_leading_deny`).

**Not yet implemented**: `with t = begin():` (the handle) is still rejected.

**Future work (deferred optimizations).** The `` `commit `` payload is currently **dense**:
an unwritten key on a committing path carries its snapshot value (a no-op re-write), and a routed
reply tap carries a `to_<defer>_k__fire : Bool` gate (`F_FIRE_SUFFIX`) the engine checks. Two deferred
refinements, scoped by the review as "worth doing later, not now":

1. ***Partial* writes** — materialize only the keys a committing path actually changed, encoding an
   absent key as carry directly (e.g. a `Some | None` per write key), rather than re-writing the
   snapshot. This needs a dense presence encoding: a naive sparse per-key column is silently dropped
   by the record `zip`'s inner-join (it deletes the committing positions where any conditionally-
   written key is absent), so it cannot be a bare non-exhaustive `Case`.
2. **Folding `__fire` into payload presence** — a routed reply would be *present in the `` `commit ``
   payload iff its route fired*, retiring the separate `to_<defer>_k__fire` gate. Same dense-presence
   requirement as (1).

**An off-path partial op cannot fault.** Both induction and transaction value-`Case`s compile through
the lazy `filter_values` union-of-restricts, so a guard-protected `//`/`%` is never evaluated on the
path its guard excludes.

### `with t = begin():` transaction handle

Designed — it binds `t` to the transaction's commit time (see the CHL spec,
[transactions](../../../docs/chl-spec.md#82-transactions-with-begin)) — but rejected at lowering today.

### Conditional transactions (a `with begin():` inside a conditional)

Rejected at lowering today (`lower/loops.rs` — a `with begin():` under an `if` hits the "only
assignments and function definitions" gate). This is the **dual** of the general in-transaction
conditionals above: there, one transaction takes one snapshot and a path-based walk merges per key;
here the *transaction itself* is conditional — `if 𝑝: with begin(): x := 𝑒` fires a transaction on
some iterations and not others.

**Mechanism — source-restriction fan-out (the value-`Case` machinery, reused).** A conditional
transaction is a transaction over a *restricted source*: the site's iteration source (and its
`begin_<site>` oracle domain) is refined to the sub-domain where the guard holds — `(reqs ↾ π̂) ≫
⟨body⟩`, which is exactly `refine_source_domain` + `synthesize_arm_predicate` (the first-match
`π̂ᵢ = 𝑔ᵢ ∧ ¬⋁ⱼ˂ᵢ 𝑔ⱼ` encoding) applied to a transaction site rather than a feed. The work is
mostly *lowering*: stop rejecting the nested `with begin():`, let the branch structure reach the
transaction phase, and have the phase refine a transaction site sitting under a path condition.
Everything else in the branch (feeds, induction writes) rides the same `π̂` refinement, so it
composes. `elif`/`else` land as disjoint sites over `reqs ↾ π̂` and `reqs ↾ ¬π̂`, merged into the
shared store by the existing multi-writer commit-stream machinery. A standalone (non-loop)
`if 𝑝: with begin(): …` refines the `Units(1)` one-shot driver, so the transaction fires
zero-or-one times.

**Why this is sound where per-path writer sites *inside* one block are not** (contrast the "one
decision record per transaction" verdict above): the guard `𝑝` is a **source-domain** predicate —
evaluated on the request element *before* the transaction, not on its snapshot — so it may
legitimately restrict the source; each branch's block is a **distinct transaction** with its own
`begin_<site>`, so distinct serialization points are correct rather than a violation; and atomicity
is intact — still one snapshot, one commit, one write-set per transaction. The whole difference is
"two transactions" vs. "one transaction, two paths".

**Footgun — a variable-reading guard is not an atomic check.** These are *not* equivalent:

```text
if balance > 0: with begin(): balance -= req      # (A) non-atomic pre-check
with begin(): if balance > 0: balance -= req       # (B) atomic — checked in the snapshot
```

In (A) `balance > 0` is a **live/as-of read outside the transaction** — a TOCTOU pre-check that can
go stale between the read and the commit. It is faithfully compilable (the guard becomes a gating
as-of read deciding whether the transaction fires), but it is not an atomic guard, and a user who
wrote (A) most likely meant (B), the in-block deny guard. This form should at least be documented,
ideally linted (a variable-reading guard on a conditional transaction) with a pointer at (B).

