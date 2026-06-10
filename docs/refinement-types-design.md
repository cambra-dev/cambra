# Dependent Refinements via Pi Types

Status: design proposal, 2026-05-20

## Problem statement

Cambra's current refinement type system can't express refinement
predicates that close over enclosing binders, except via a single
special-cased path in lambda elimination — the *correlated refinement*
branch of `elim_lambda_impl`'s nested-Lambda rule. Every other path that
introduces a refinement (structural `restrict(_)` from
list-comprehension lowering; the for-loop if-guard recognizer; any
future refinement-introducing form) produces a refinement whose
predicate cannot reference outer-scope variables without breaking
downstream passes.

The fundamental issue is that the `Refinement` struct treats its
predicate as a closed function `𝐷 ⇒ Bool`. When the predicate
syntactically references a variable bound by an enclosing scope (e.g.,
`groupby`'s partition condition `𝑖 ▷ collection ▷ key_fn == 𝑘` where
`𝑘` is bound by an outer `λ 𝑘 → ...`), nothing in Cambra's type system
acknowledges the dependency. Inference treats the predicate as opaque;
`unify` strips the refinement when comparing against an unrefined type;
lambda elimination either special-cases or produces unsound output. The
predicate is *materially* dependent on `𝑘` but the type system says
it's not.

Two concrete failure modes:

1. The let-bound filter bug
   (`tests/programs/filter_and_aggregate`): `xs = [...]; [x for x in xs
   if p(x)]` silently produces every element of `xs` because the
   refinement carrying `𝑝` is dropped between lambda-elim and
   operator-conversion. The current fix lowers the filter as a
   structural `restrict(pred)`; this works for *closed*
   predicates but offers no path to handle predicates with captures.

2. `groupby`'s correlated-refinement path: today the nested-Lambda
   rule in `elim_lambda_impl` (lambda_elim.rs:645–672) detects "the
   predicate captures the outer parameter" via `is_in_free_vars` and runs an
   ad-hoc pair-substitution + `elim_lambdas` dance to consolidate the
   refinement onto a pair-typed function. This is the *only* code path
   that handles captured refinements correctly, and it only fires on
   `Lambda { refinement: Some(_) }` adjacency. Replicating it
   structurally for the new representation breaks repeatedly because
   the structural form doesn't expose the adjacency the rule needs.

The system needs a uniform way to express, propagate, transform, and
compile dependent refinement predicates. The proposal below is to give
the type system explicit dependent function types (Pi) and named-binder
refinements, and to fold all iteration-site discovery and join
pattern-matching into a single planning pass that prepares the IR for
operator conversion by materializing iteration sites and
lambda-eliminating their predicates.

## Design overview

Five interlocking pieces.

**1. `Type::Fun` carries an optional binder name.** Function types
become `Fun { name: Option<String>, domain, codomain }`. When `name`
is `Some(𝑥)`, `𝑥` is bound in `codomain` and refinements nested in
`codomain` may reference it. When `None`, the codomain is independent
of the argument value. Inference always populates `name` from the
source-level parameter; downstream passes query `is_in_free_vars` on the
codomain to determine whether the dependency is actually used. No
Pi-vs-Fun choice has to be made at function introduction time.

**2. Named-binder refinements.** `Refinement { name, base, predicate }`
binds `name` and exposes it to `predicate`, which is a bare expression
(not a lambda). The predicate may reference `name` and any in-scope
function-type binders via ordinary scoping. Same predicate shape
regardless of where the refinement was introduced.

**3. Pointful refinement predicates throughout the pipeline.** Lambda
elimination does not process refinement predicates. They remain bare
expressions, referencing names according to ordinary scoping. A new
pointful-simplify pass and planning both work directly on these
pointful expressions, where structural patterns are more legible
than their combinator equivalents. The existing (point-free)
simplify continues to operate on the rest of the AST.

**4. Planning subsumes iteration discovery and join recognition.**
A single CCL-to-CCL pass between simplification and operator
conversion. Walks the AST, identifies every iteration site, and at
each one emits `Builtin::Iterate` applied to the source (the
universal iteration marker) plus — if the source's type carries a
refinement — either a specialized CCL fragment matching a
recognized pattern (hash join, semi-join, anti-join, ...) or a
filter operator pre-composed with `iterate` (the "loop join"
fallback). Planning emits **CCL only** — no tile graphs, no
operator instantiation; that work is op-conversion's job. Planning
is self-driving and recursive: emitted CCL fragments may themselves
contain nested iteration sites, which planning descends into and
plans before returning the fragment to its caller. By the time
planning is done, every iteration site in the AST has `iterate`
marking it and any required filter or specialized join construct
attached as further CCL.

**5. Op-conversion radically simplified.** Planning is responsible
for marking every iteration site. Op-conversion compiles
`Builtin::Iterate` applications to `IterateExtent` tiles, the
filter operators planning may have pre-composed to `Restrict` tiles,
and specialized join CCL fragments to their tile equivalents.
`iterate` is the *only* term in op-conversion that does not
require an `input`: it generates its own iteration stream from the
domain encoded in its type. Every other term expects an `input`,
and op-conversion's invariant is to fail an assertion if any
non-`iterate` term reaches it without one. This is the mechanism
that catches unplanned iteration sites: an iteration that planning
missed leaves the downstream consumer without an `input`.

The IR remains CCL throughout — `Builtin::Iterate` is a new
builtin, not a new AST shape. The same `Type` system, lambda
elimination machinery, and operator types apply.

## Type system

### `Type::Fun` with an optional bound name

Cambra's existing `Fun(Box<Type>, Box<Type>)` constructor gains an
optional name that binds in the codomain:

```rust
enum Type {
    // existing variants ...

    /// Function type.  If `name` is `Some`, it binds in `codomain` and
    /// may be referenced by refinements nested anywhere within
    /// `codomain`.  If `None`, `codomain` is independent of the
    /// argument value.
    ///
    /// Inference always populates `name` when introducing a function
    /// type from a lambda: every lambda's parameter name goes into the
    /// typing context for its body.  Whether the codomain actually
    /// references the name is a *property* of the resulting type,
    /// queryable on demand by `is_in_free_vars` — not a structural decision
    /// inference has to make up front.
    Fun {
        name: Option<String>,
        domain: Box<Type>,
        codomain: Box<Type>,
    },
}
```

This is a single constructor doing double duty for what would
otherwise be Pi (dependent function) and Fun (non-dependent function).
The structural marker that distinguishes them is whether `codomain`
syntactically references `name`.

**Symbolic notation.** In prose and inline pseudo-code the two
forms are written:

- `(𝑥: 𝐴) ⇒ 𝐵` for a function type with named binder
  (`name: Some("x")`). The binder `𝑥` is in scope in `𝐵` and may
  be referenced by refinements or other types nested there.
- `𝐴 ⇒ 𝐵` for a function type with no named binder
  (`name: None`). The codomain is independent of any per-call
  value of the argument.

Refinement types continue to use the standard subset-type
notation `{𝑥: 𝑇 | 𝑝(𝑥)}`. The function-type arrow `⇒` is
right-associative (`𝐴 ⇒ 𝐵 ⇒ 𝐶` parses as `𝐴 ⇒ (𝐵 ⇒ 𝐶)`).
At the term level, `→` is the lambda body separator (`λ 𝑥 → body`)
and is distinct from `⇒` — type arrows and term arrows never mix.

The advantage: inference never has to commit to a Pi-vs-Fun choice at
function-introduction time. When `infer_lambda(λ 𝑥 → body)` runs, it
just produces `Fun { name: Some("x"), domain: x_ty, codomain: body.ty }`.
Whether `body.ty` references `𝑥` may not be knowable yet (the body's
inferred type may have unresolved `Type::Infer(_)` slots whose
predicates aren't yet final). Any pass that *cares* about the
dependency — operator conversion when materializing iteration,
optimization passes that want to hoist — can query `is_in_free_vars(name,
codomain)` when they need the answer.

Optionally, a late pass can strip unused names (`name: Some(𝑛) →
None` when `!is_in_free_vars(𝑛, codomain)`). This is purely cosmetic /
canonicalization; it doesn't affect correctness.

### `Refinement`

```rust
struct Refinement {
    id: RefinementId,
    description: String,
    /// The binder name introduced by this refinement, visible in
    /// `predicate`.  Cambra-source-derived refinements use
    /// descriptive names (`__iter_record`, `__gb_i`, ...); synthetic
    /// refinements use generated names.  Names are *not* load-bearing
    /// for type identity — see "Unification" below.
    name: String,
    /// The unrefined base type.
    base: Box<Type>,
    /// A bare expression of type `Bool` (not a lambda).  The
    /// expression's free variables — `name`, plus any in-scope
    /// Fun-binders from enclosing types, plus any AST-level
    /// let-bound names — are resolved by ordinary lexical scoping
    /// against the surrounding context.
    ///
    /// Held as an immutable `Rc<TypedExpr>` so the same predicate
    /// can be cheaply shared across the many refinement instances
    /// inference propagates via type unification and substitution.
    /// Mutation is not allowed; capture-avoiding substitution at
    /// Apply sites produces a new predicate rather than mutating
    /// the shared one.
    predicate: Rc<TypedExpr>,
}
```

The refinement's predicate is an *open* expression: it has free
variables that resolve to in-scope binders via ordinary lexical
scoping. The scope at the refinement's position is determined by the
enclosing type tree — every `Pi(name, _)` ancestor contributes a
binder, and the refinement itself contributes `name`.

`Rc<TypedExpr>` (immutable, shared) is the chosen representation
for the predicate: inference propagates refinements freely via
unification and substitution, and a shared-immutable form lets
those propagations be cheap `Rc` copies rather than deep clones.
Substitution at Apply sites creates a new `Rc<TypedExpr>` for the
result, leaving the original predicate intact for any other
refinements still pointing at it. If simplify-style rewrites
diving into refinement predicates later produce enough churn to
motivate it, there's room to grow to some flavor of
context-aware interning / memoization (vaguely: hash-cons or
memoize keyed on the predicate plus its free-variable resolution
to Γ) — exact scheme TBD when the need is concrete.

### Scoping rules

A refinement at position 𝑃 in a type tree has these names in scope:

- The refinement's own `name`.
- For each `Fun { name: Some(𝑛), .. }` on the path from the type root
  to 𝑃, `𝑛` is in scope within the function's codomain (and thus at 𝑃
  if 𝑃 is reached via the codomain).
- Any names bound at the AST level outside the type (e.g., let-bound
  variables in the surrounding program).

The predicate's free variables must all be in scope. A predicate that
references a name not in scope is a typing error.

### Unification

α-conversion at unification time is unavoidable: inference is
non-local, so two `Fun` types constructed on independent paths may
be constrained equal later, and at construction time there is no
shared context that would let either side pick a canonical binder
name the other side would also pick. Whatever names get attached
at construction (source-level parameter names, monotonic counter,
hash-of-position) will differ across independently-constructed
types that should unify, so unify must do the α-renaming itself.
The capture-avoiding-substitution machinery this needs is the same
machinery Apply-site substitution needs (see below); unification
reuses it.

The unification rules for `Fun` types:

- `Fun { name: Some(𝑥), domain: 𝐷₁, codomain: 𝐶₁ }` unifies with
  `Fun { name: Some(𝑦), domain: 𝐷₂, codomain: 𝐶₂ }` when `𝐷₁ ≡ 𝐷₂`
  and the codomains are α-equivalent. The renaming strategy
  prefers reusing one of the existing names rather than minting a
  fresh one — see "Binder-name reuse" below.
- `Fun { name: Some(𝑥), .. }` unifies with `Fun { name: None, .. }`
  as long as the codomain doesn't reference `𝑥` (i.e., `𝑥` is in
  scope inside the named version but unused). Stripping the
  unused binder is a no-op on the type's meaning.
- Two `Fun { name: None, .. }` unify structurally on domain and
  codomain — the existing `Fun` unification.

For refinements: two refinements with the same predicate up to
α-renaming of their own `name` unify. Different refinements
(different `id`) on the same base type may unify or fail
depending on predicate equivalence — SMT-hard in general;
structural equality (with Rc-sharing as acceleration) suffices for
the common case.

**Binder-name reuse.** Always generating a fresh name on each
unification damages debugging: error messages and IDE hover-info
that reference a binder are easier to read when the binder keeps
a name a human wrote, instead of being rewritten to a synthetic
identifier on every unification. So:

1. **Same-name case** — `𝑥 ≡ 𝑦`. Short-circuit: skip substitution,
   unify the codomains directly. This is the common case
   (source-level parameter names tend to match across types built
   from the same lambda).
2. **Different-name case** — `𝑥 ≠ 𝑦`. Pick one (the left-hand
   side's by convention) and substitute the other side to match.
   If the chosen name is shadowed in the other side's codomain by
   a nested binder, fall back to a fresh name and substitute both
   sides — this is the only case where a synthetic name leaks
   into the resulting type.

Whether case 2's "reuse one side's name" is always safe without
subtle interactions needs verification during implementation. If
reuse turns out to be fragile, fall back to fresh names
everywhere; correctness isn't at stake, only debugging quality.

### Substitution at Apply sites

`Apply(arg, fn)` where `fn : Fun { name: Some(𝑥), codomain: 𝑈 }`
produces a value of type `𝑈[𝑥 ↦ arg]`. Substitution descends into
`𝑈`'s structure, including refinements; when it encounters a refinement
whose predicate references `𝑥`, it substitutes inside the predicate as
well.

If `fn : Fun { name: None, codomain: 𝑈 }`, Apply produces `𝑈`
unchanged — no substitution needed (and none possible).

Substitution is capture-avoiding. If `𝑈` contains a `Fun { name:
Some(𝑦), .. }` or `Refinement { name: 𝑦, ... }` that would capture
`arg`'s free variables, `𝑦` is α-renamed first.

### Dependency tracking via the binder name

Under this design, *inference never has to decide* whether a function
is dependent. Every lambda produces a `Fun { name: Some(param), .. }`;
whether the binder is actually referenced is a property of the
codomain that can be queried later.

Passes that care about dependency call `is_in_free_vars(name, codomain)` at
the point they need the answer. The relevant call sites:

1. **Apply-site substitution**: when computing the result of
   `Apply(arg, fn)` where `fn` has a named binder, substitution
   descends the codomain looking for free occurrences. The walk is
   the existing capture-avoiding substitution; it handles refinements,
   nested binders, and Rc-shared predicates naturally.

2. **Planning**: when constructing the synthetic lambda chain
   for a refinement predicate at the loop-join fallback, determine
   which in-scope Fun-binders the predicate needs parameterized
   over. Walk up from the refinement's position collecting
   `Fun { name: Some(𝑛), .. }` binders; for each, check whether the
   predicate references it. Build the chain over the binders that
   need lifting (i.e., are not already in scope at the `iterate`
   marker's insertion position).

3. **Optimization (optional)**: a late pass can strip
   `name: Some(𝑛)` to `None` when `!is_in_free_vars(𝑛, codomain)`. Reduces
   memory and makes types canonical, but not required for
   correctness.

#### Tri-state `is_in_free_vars` for partially-resolved types

A subtle but load-bearing point: `is_in_free_vars(name, ty)` cannot always
return a definitive yes/no while inference is still running.

If `ty` contains unresolved `Type::Infer(_)` slots, those slots may
later be solved to types containing refinements whose predicates
reference `name`. At the time of the query, the answer is genuinely
unknown — the resolved form could go either way.

`is_in_free_vars` therefore needs to return a tri-state:

```rust
enum Freeness {
    /// `name` is definitely free in `ty` — found a structural occurrence.
    Yes,
    /// `name` is definitely not free in `ty` — the walk completed with
    /// no occurrences and no unresolved `Type::Infer` slots.
    No,
    /// Indeterminate — the walk encountered one or more unresolved
    /// `Type::Infer` slots whose eventual resolution may or may not
    /// contain a free reference to `name`.
    Unknown,
}
```

Callers must handle `Unknown` per their needs:

- **Apply-site substitution**: substitute eagerly anyway. The
  substitution is capture-avoiding and idempotent; if the eventual
  resolved type didn't reference `name`, the substitute is a no-op.
- **Planning**: unreachable. Planning runs after inference has fully
  resolved types, so by the time it queries `is_in_free_vars`,
  `Unknown` shouldn't occur. If it does, that's an inference bug
  (a leftover `Type::Infer` that should have been resolved).
- **Optimization (binder stripping)**: treat `Unknown` as `Yes`. Don't
  strip a binder we're not sure is unused. Strip only when the answer
  is definitively `No`.

The conservative discipline — "treat `Unknown` as a referenced
binder" — keeps the design sound regardless of partial-resolution
ordering. Any pass that depends on `is_in_free_vars` returning a definitive
answer must explicitly check the inference state, or run after
inference resolution, or accept the conservative interpretation.

## Pipeline phases

### Lowering (`src/ccl/lower.rs`)

In the redesigned world, the `refinement` field on
`TypedExprNode::Lambda` is removed and the `Expr::lambda_with_refinement`
helper goes with it. Refinement-introducing forms lower to
applications of `cast`, the type-change operator:

  `cast : (𝑇: Type) ⇒ {𝑈: Type | 𝑈 <: 𝑇} ⇒ 𝑇`

`cast` is a pure type-level assertion — it does not change the
value at runtime, only the type it is viewed under. Filtering forms
exploit function-domain contravariance: `𝐷 ⇒ 𝑉 <: {𝐷 | 𝑝} ⇒ 𝑉`, so
casting a function with unrefined domain to one with refined domain
is a well-typed upcast. The actual selection of values satisfying
the predicate happens at iteration time, materialized by planning
when it sees the refined function type.

The lambda capturing the iteration index lives inside the predicate
position of the refinement type itself, where its parameter becomes
the refinement's named binder via inference's term/type-level
bridge. Inference's `infer_cast` rule (see Inference section below)
recognizes applications of `cast` whose target type is a
refined-domain function and stitches the lambda's parameter onto
the `Refinement.name` field of that type.

Examples:

  - List comprehension `[x for x in xs if p(x)]` lowers to
    `cast({𝐷 | 𝑝(𝑥)} ⇒ 𝑉, xs)` — i.e., xs viewed at the refined
    domain type. The refinement carries the predicate `𝑝(𝑥)`; the
    runtime selection happens at the eventual iteration site, not
    here.
  - For-loop with `if`-guard lowers the same way, with the
    refinement's binder being the loop's iteration variable.
  - `groupby(𝑐, key_fn)` lowers to
    `λ __gb_k → cast({𝐷 | key_fn(𝑐(__gb_i)) == __gb_k} ⇒ 𝑉, 𝑐)`.
    The outer lambda binds the partition key; the body casts `𝑐`
    to a partition-refined function type. The cast's target type
    captures `__gb_k` from the outer lambda — making this the
    canonical "captured refinement" case, but with no special-case
    AST shape.

The two value-level builtins for refinement-related work are
`cast` (lowering-time, type-level assertion, no runtime effect) and
`iterate` (planning-time, marker that op-conversion compiles to a
real iteration; see the Planning section below). There is no
separate "filter" or "restrict" builtin — filtering is the runtime
consequence of `iterate`-ing a refined-domain function.

**User type ascriptions (future).** If Cambra grows surface syntax
for refinement annotations (`x: {Int | x > 0} = ...`), lowering of
the annotation would introduce the refinement at the type level
directly. This is a separate, future concern; nothing else in the
redesign depends on it.

Lowering does not need to track Pi vs Fun; the only function
constructors it produces are lambdas, and inference decides their
types.

### Inference (`src/ccl/infer.rs`)

`infer_lambda(param, body)`:

1. Bind `param.name` in the typing context.
2. Infer `body.ty` with `param.name` in scope.
3. Produce `Type::Fun { name: Some(param.name.clone()), domain:
   param.ty, codomain: body.ty }` — always named, regardless of
   whether `body.ty` actually references the binder. Inference does
   not decide; the binder is always available, and downstream passes
   query it on demand.

`infer_apply(arg, fn)`:

1. Infer `arg.ty` and `fn.ty`.
2. Match on `fn.ty`:
   - `Fun { name: Some(𝑥), domain: 𝐷, codomain: 𝐶 }`: constrain
     `𝐷 ≡ arg.ty`, return `𝐶[𝑥 ↦ arg]` (capture-avoiding substitution
     into `𝐶`, including into nested refinement predicates).
   - `Fun { name: None, domain: 𝐷, codomain: 𝐶 }`: constrain
     `𝐷 ≡ arg.ty`, return `𝐶` unchanged.
3. If `fn.ty` is an unresolved inference variable, constrain it to
   `Fun { name: None, domain: arg.ty, codomain: fresh }` and return
   `fresh`. Inference variables resolve to anonymous Fun by default;
   if a later constraint introduces a binder, unification handles the
   refinement.

`infer_cast(cast(<refined-target>, source))` — the rule fires on
an application of `cast` whose target type carries a refinement,
and whose source has a subtype of that target. Specifically, when
the target is a refined-domain function `{𝐷 | 𝑝(𝑥)} ⇒ 𝑉` and the
predicate `𝑝(𝑥)` is written in source as a lambda
`λ 𝑥 → predicate_body`:

1. Infer the predicate-lambda's type via the usual `infer_lambda`
   path: `predicate_body` is typed with `𝑥` in the typing context,
   yielding `Fun { name: Some("x"), domain: 𝐷, codomain: Bool }`.
2. Construct the type-level `Refinement { name: "x", base: 𝐷,
   predicate: <body as bare expression> }`. The lambda's parameter
   becomes the refinement's binder; the lambda's body becomes the
   bare predicate. This is the term/type-level bridge: the binder
   migrates from the lambda parameter to the `Refinement.name`
   field, and the body remains unchanged as the now-bare predicate.
3. The whole Apply yields a value of the cast's target type,
   `Fun { name: None, domain: refined, codomain: 𝑉 }` where
   `refined = Refinement { name: "x", base: 𝐷, predicate: <body> }`.
   The cast does not change the value's runtime data; only the
   type ascribed to it.

**Scope validity invariant.** When inference propagates a refinement
to a new position (Apply codomain extraction, type-variable
resolution, codomain inlining past a local binder), the predicate's
free variables must all be in scope at the destination. The
propagation is malformed if not.

Enforced as a `debug_assert!`-style runtime check at every
refinement-move site — after substitution completes, after a type
variable resolves, after the inliner closes a binding, after
planning lifts a predicate into a synthetic chain. The assertion
checks the resulting refinement's predicate's free variables
against the in-scope binders at the destination position and panics
on mismatch with a message identifying which pass and which binder
caused the violation.

In release builds the check is typically compiled out (gated on
`cfg(debug_assertions)`); in dev/test it runs at every propagation
site. The intent is to catch compiler bugs — incorrect α-renaming,
missed descent into predicates during substitution, an inliner
that fails to handle some binding form, a unification rule that
resolves `?α` to a type whose free vars aren't in scope at every
site `?α` was placed. In a correct implementation on a well-typed
program, the assertion should never fire. If it does, that's a
compiler bug to file, not a program to fix.

User-facing scoping errors (programs that reference unbound names
in refinements) are caught earlier by inference with proper
source-location context and never reach this assertion. See the
appendix for the test-case matrix that exercises each binding
form's interaction with the assertion.

### Lambda elimination (`src/ccl/lambda_elim.rs`)

Processes value-level lambdas as today, converting them to point-free
combinator chains. *Does not* descend into refinement predicates — they
remain bare expressions in their type slots.

The legacy correlated-refinement special case in
`elim_lambda_impl`'s Lambda arm (lines 645–672) goes away, but the
work it was doing is preserved: when a nested lambda with a captured
refinement gets curried into a pair-argument form, the refinement on
the inner binder still has to be rewritten to live on the pair domain,
and its predicate's references to the outer binder still have to
become pair projections. Under the new representation that happens
naturally through the existing capture-avoiding-substitution
machinery. The curry combinator's output type is itself a Pi —
`(𝐴, 𝐵) ⇒ 𝐶` becomes `𝐴 ⇒ (𝐵 ⇒ 𝐶)` where `𝐶` may reference the outer
binder — and the substitution descent that runs when we Apply this
type to a pair argument rewrites the inner refinement's predicate
from `pred(𝑎, 𝑏)` to `pred(pair.0, pair.1)` automatically. The net
effect on the AST is the same as today's correlated branch, just
expressed via the generic substitution walk instead of a dedicated
rule.

One incidental cleanup: today's correlated-branch output uses
`Type::Refinement(Box::new(Fun(...)), pred)` — refinement wraps the
whole function. The new shape places the refinement on the function's
domain: `Fun(Refinement(domain, pred), codomain)`. This is the
canonical form for refined function types: the refinement lives on
the domain, never wraps the whole function.

### Simplify

Two complementary passes run at the simplify stage of the pipeline:

**Point-free simplify (`src/ccl/simplify.rs`)** continues to do
combinator-level rewrites on the post-lambda-elim AST. Refinement
predicates live in type slots and are not part of its working
set; the point-free rewrites it knows are about Compose chains,
combinator identities, etc., and they don't change here. Existing
Compose-element guards (`contains_structural_restrict`, etc.) are
reviewed against the new representation; most of them are about
the structural form of refinements in the AST, which is now
different.

**Pointful simplify** is a new pass with the same kind of
rewriting capability as the point-free one, but operating on the
pointful refinement predicates that lambda elim leaves alone.
Pattern matching here is structural at the expression level; for
example, an equality-condition predicate is matched as a
`BinOp(_, Eq, _)` directly rather than as the combinator pattern
it would lower to. The pointful pass handles the rewrites that
are most legible against the structural expression form
(predicate normalization, dead-clause elimination, constant
folding inside predicates, etc.), and runs alongside the existing
point-free pass — neither replaces the other.

### Planning (`src/ccl/planning.rs`)

CCL-to-CCL pass between simplify and operator conversion. Walks the
AST, identifies every iteration site, and resolves each one to a
CCL chain that marks the iteration and, if the source is refined,
encodes either a specialized join or a generic filter as further
CCL.

#### A new builtin (no new AST variant)

```rust
// In Builtin enum:

/// Marks a planned iteration site.  Signature:
///
///   `iterate : (T: Type) ⇒ (p: T ⇒ Bool) ⇒ {t: T | p(t)} ⇒ {t: T | p(t)}`
///
/// `iterate` is *not* the identity function despite its type
/// shape — it is a marker for "iteration happens here," and
/// op-conversion compiles it to an `IterateExtent` + `Restrict`
/// tile pair (or just `IterateExtent` if the predicate is
/// trivially `λ _ → true`).
///
/// Planning introduces `iterate` at each iteration site by:
///   1. Lambda-extracting the refinement predicate from the
///      iterated function's domain type.
///   2. Running lambda elimination + simplify on the extracted
///      predicate to produce a self-contained point-free chain.
///   3. Emitting `Apply(<chain>, iterate)` (with the appropriate
///      `T` instantiation), composed with the source function.
Iterate,
```

`iterate` is introduced *only* by planning. Lowering and inference
produce `cast`, which is the type-level counterpart that asserts
the refined type without changing runtime semantics. Planning
reifies the type-level predicate into a value-level argument to
`iterate` at each iteration site.

**Loop-join fallback shape.** When the source's domain is refined
and no specialized pattern matches, planning emits a chain of the
form:

```
iterate(predicate) ≫ source
```

where `predicate` is the lambda-eliminated predicate extracted
from the source's domain refinement. Concrete example for an
iteration over `[0, 100]` filtered to even integers (where the
source's type, post-lowering and inference, is
`{𝑖: Int | 𝑖 % 2 == 0 ∧ 𝑖 ∈ [0, 100]} ⇒ 𝑉`):

```
iterate(λ 𝑖 → 𝑖 % 2 == 0) ≫ [0, 100]
```

`iterate(predicate)` has type `{𝑖: Int | predicate(𝑖)} ⇒ {𝑖: Int |
predicate(𝑖)}`. Semantically a marker rather than an identity —
op-conversion treats it as an iteration trigger, not as a
no-op.

**Unrefined shape.** When the source's domain has no refinement,
planning still emits `iterate(λ _ → true)` to mark the iteration
site, but op-conversion recognizes the trivial predicate and emits
just `IterateExtent` with no `Restrict` tile.

**Specialized-join shape.** When a recognized pattern (group-by,
hash join, semi-join, anti-join, ...) matches, planning emits a
specialized CCL chain that still has `iterate` at its root(s) —
the iteration itself is always expressed via `iterate` — but
composes additional builtins (`converse`, `zip`, fan-out, fan-in)
to express the join structure on top of that iteration. For
example, a binary equality join is planned as: iterate the
key-function's domain, take the `converse` (key → elements with
that key), then fan that out and in to look up the corresponding
values on each side. The `iterate(predicate)` form is the
fallback for sites that don't match a specialized recognizer; in
the specialized cases, the predicate is consumed by the join's
structural composition rather than appearing as `iterate`'s
predicate argument.

**When planning fires.** Iteration sites are bounded. There are
exactly two:

1. A function value passed to an aggregate (`Sum`, `Max`, ...).
   The aggregate iterates the function's domain.
2. A function value returned as the program's result (a result
   binding or a sink). The runtime iterates the domain to produce
   output.

No other AST positions are iteration sites. Planning's site
recognizer enumerates exactly these cases.

**Pattern-matching at each site.** Planning looks at the refinement
on the source's domain, if any, and tries the recognizers in
order.

*Group-by recognition.* When the iterated function is curried as
`λ 𝑘 → <lambda refined by a predicate of the form `key_fn(𝑖) == 𝑘`>`,
planning recognizes a group-by:
pre-bucketize the inner source by `key_fn` once and let the outer
iteration over `𝑘` look up its bucket per iteration step. This is
`convert_groupby` in the existing code (`planning.rs`),
rewritten to operate on the new pointful refinement form. Planning
emits the bucketize-and-lookup CCL chain — `iterate` over the
distinct-keys side, partition-fetch over the buckets, and the
existing aggregate or sink as the consumer.

*Hash-join recognition.* When the refinement's predicate is a
top-level `BinOp(Eq, lhs, rhs)` and the two sides reference
disjoint sets of variables (or product projections), planning
recognizes a hash join — hash the build side, probe with the
build-side keys against the probe source. Self-joins (both sides
iterating the same collection under different binders) are
included; the matcher cares about variable-set disjointness, not
source identity. This is `create_hash_joins` in the existing
code, rewritten for the pointful form. Planning emits the
build-and-probe CCL chain.

*Other specialized patterns* (semi-join, anti-join, ...)
recognized analogously, each by its own structural matcher on the
refinement's predicate shape.

If no specialized pattern matches, planning falls back to the loop
join:

1. Lift the refinement's predicate out of the type slot.
2. Walk up from the refinement's position collecting
   `Fun { name: Some(𝑛), .. }` binders on the path to the iteration
   site; for each, check whether the predicate references `𝑛`
   directly *and whether that binder is in scope at the iteration
   site's AST position*. Binders not in scope at the insertion
   position need to be lifted into the predicate's parameter list;
   binders that *are* in scope stay as ordinary free references in
   the predicate body.
3. Build the predicate as `λ 𝑏₁ → λ 𝑏₂ → ... → λ refinement_name
   → predicate_body`, with `𝑏₁, 𝑏₂, ...` being only the binders
   that needed lifting.
4. Recursively invoke the upstream pipeline on this lambda:
   lambda elimination, then simplify, then planning (on any
   iteration sites the predicate itself exposes). The output is a
   fully point-free, fully resolved combinator chain.
5. Emit the Compose chain
   `iterate(<combinator chain>) ≫ source`
   as the iteration-site CCL, with `iterate`'s type instantiated
   so its predicate parameter matches the lambda-eliminated chain
   and its refined-domain matches the source's domain.

If the source's domain has no refinement, emit
`iterate(λ _ → true) ≫ source`. Op-conversion recognizes the
trivial predicate and emits just `IterateExtent` with no `Restrict`
tile.

**Recursive planning of specialized fragments.** A specialized
CCL fragment (hash-join build/probe, etc.) may itself expose
nested iteration sites — e.g., the build side of a hash join
iterates a collection whose domain is refined. Planning
recursively descends into the emitted fragment to plan those
sites before returning the fragment to its caller. By the time
the outer call returns, every iteration site the fragment touches
has been resolved.

**Type-preservation invariant.** `iterate(predicate)` has type
`{𝑇 | predicate} ⇒ {𝑇 | predicate}`, so composing it with a
source whose domain already matches that refined type preserves
the source's overall type. Specialized join CCL chains likewise
preserve the iterated value's type — the planner rewrites the
expression structure, not the value-level semantics.

**Termination.** Each level of recursion operates on a strictly
smaller subtree — either a sub-fragment emitted by a specialized
join, or a synthetic predicate lambda that itself may nest
iterations. The source program's structure bounds the depth.

### Operator conversion (`src/interpreter/operator_conversion.rs`)

Op-conversion expects every iteration site to have been resolved
by planning to a CCL chain that includes either `Apply(predicate,
Builtin::Iterate)` (the loop-join shape) or a specialized join
construct. It is *not* responsible for site discovery.

The invariant op-conversion enforces: **operator conversion never
implicitly creates iteration; the iteration must already be
present in the CCL.** Planning has marked every iteration site
with `iterate`, so op-conversion never has to synthesize one.

Many terms require no `input` at all during conversion (scalar
operations, applied combinators, and so on); the invariant says
nothing about those. For a term that *does* require an `input`,
reaching conversion without one is a compiler bug, not user error:
it means planning missed an iteration site, leaving the downstream
consumer with no one to supply its `input`. Such a term fails an
assertion — that assertion is how unplanned iteration sites are
caught.

A new arm handles `Apply(predicate, Builtin::Iterate)`:

```rust
TypedExprNode::Apply(predicate, fn_expr)
    if matches!(fn_expr.node, TypedExprNode::Builtin(Builtin::Iterate)) =>
{
    let domain_ty = fn_expr.ty.refined_domain().expect("iterate(p)'s type must be {T|p} ⇒ {T|p}");
    let extent = ctx.extent_of(&domain_ty.base)?;
    let iter = Box::new(IterateExtent::new(extent));
    if predicate_is_trivially_true(predicate) {
        iter
    } else {
        // `Restrict` derives its iteration from the predicate's
        // domain, so the `IterateExtent` feeds the predicate's
        // conversion as `input` and `Restrict` wraps the result —
        // it takes the predicate operator alone, not (iter, pred).
        let pred_op = convert_impl(predicate, Some(iter), ctx)?;
        Box::new(Restrict::new(pred_op))
    }
}
```

Specialized join CCL chains compile to their respective tile
equivalents via dedicated arms or helpers, recognizing the
specialized builtins planning emits for those constructs.

`cast` applications are no-ops at op-conversion: their runtime
effect is nothing (the value passes through unchanged), and any
refinement they introduced into the type has already been
consumed by planning to produce the right `iterate(predicate)` or
specialized chain. Op-conversion simply converts the cast's
argument and discards the cast wrapper.

`Var`-arm handling, `Let`-arm handling, and the rest of
op-conversion are unchanged — they don't need to look at
refinements anymore because all iteration sites are explicitly
marked.

## Iteration marker specification

See the `Builtin::Iterate` declaration above. Key properties:

- **Signature**:
  `iterate : (T: Type) ⇒ (p: T ⇒ Bool) ⇒ {t: T | p(t)} ⇒ {t: T | p(t)}`.
  The predicate `p` is the iteration's filter; the type signature
  guarantees that an iterate application only ever produces values
  that satisfy `p`.

- **Marker semantics, not identity semantics**: despite the
  identity-shaped signature, `iterate(p)` is *not* compiled as a
  no-op. It is a planning-introduced marker for "iteration happens
  here." Op-conversion compiles it to an `IterateExtent` + `Restrict`
  tile pair (or just `IterateExtent` when `p` is trivially
  `λ _ → true`).

- **Predicate is a closed combinator chain**: by the time planning
  emits `iterate(p)`, `p` has been lambda-extracted from the
  refinement type and run through lambda elim + simplify, so it's
  a self-contained point-free chain with no free variables outside
  the chain's parameter list.

- **Compositional**: filter predicates can themselves contain
  iteration sites (e.g., a predicate that iterates a refined
  sub-collection). The recursive planning call handles this
  naturally — planning a predicate recursively plans any iteration
  sites it exposes.

- **Op-conversion is local**: each `Apply(p, Builtin::Iterate)`
  compiles independently to an `IterateExtent` + optional `Restrict`
  tile pair. No global analysis needed.

- **Specialized joins still iterate via `iterate`**: specialized
  join CCL chains (group-by, hash join, semi-join, anti-join, ...)
  always have `iterate` at their root(s) — that's how the
  iteration itself is expressed regardless of pattern. Specialized
  recognizers compose additional builtins (`converse`, `zip`,
  fan-out, fan-in) on top of `iterate` to express the join's
  structure. `iterate(p)` with a non-trivial `p` is the fallback
  shape for sites where no specialized recognizer matched; in the
  specialized cases, the predicate is consumed by the structural
  composition rather than as `iterate`'s predicate argument.

## Open questions

### Interaction with the in-progress structural-subtyping work

A teammate is independently working on a structural subtyping type
checker. Some of the inference-time invariants proposed here (Pi-vs-Fun
decision, scope validity, Apply substitution) will need to coexist
with subtyping rules. Coordination needed: agree on which pass is
responsible for which invariants, and what the typed-AST contract is
at the boundary between subtyping and dependent inference.

## Migration plan

Incremental migration from the current code, in suggested order:

**Prerequisite (mechanical):** rename the existing helper
`ccl_utils::is_free` to `is_in_free_vars`, along with its call sites in
`src/ccl/lambda_elim.rs` (4 callers including a test) and
`src/ccl/remove_defers.rs` (2 callers). The name `is_free` is
ambiguous between "free to use this name" and "this name appears as
a free variable"; `is_in_free_vars` disambiguates to the latter.
Purely a rename — no behaviour change. Landing this first means
subsequent steps' new code (the substitution walks in inference,
the free-variable checks in planning, the binder-stripping pass)
use the disambiguated name from the start.

1. **Type system additions**: change `Type::Fun` to its struct-form
   with `name: Option<String>`. Update the `Refinement` struct
   shape. Add a `TypedExprNode::Cast { value, target }` node and
   `Builtin::Iterate` to the `Builtin` enum (cast is a node, not a
   builtin — it carries its own typing rule and structural shape),
   along with their type signatures in the builtin-stamping logic.
   Stub out exhaustive-match arms with
   `unimplemented!` everywhere they're needed. The compile-error
   count provides a touch-point inventory.

2. **Inference updates**: update `infer_lambda` to emit
   `Fun { name: Some(param), .. }`. Update `infer_apply` to handle
   the named case via capture-avoiding substitution. Update
   unification for the optional binder. Add the `infer_cast` rule
   for cast-to-refined-domain. The scope-validity invariant comes
   for free with capture-avoiding substitution.

3. **Lowering updates**: remove the `refinement` field on
   `TypedExprNode::Lambda` and the `Expr::lambda_with_refinement`
   helper. Rewrite the lowering of `groupby` at `lower.rs:805` to
   emit `λ __gb_k → cast({𝐷 | key_fn(𝑐(__gb_i)) == __gb_k} ⇒ 𝑉, 𝑐)`
   instead of a nested lambda with a refinement attached. Rewrite
   list-comp filter lowering and for-loop if-guard lowering to emit
   `cast` applications around the iterated source.

4. **Lambda elim cleanup**: remove the correlated-refinement special
   case from the nested-Lambda rule. The named-binder Fun handles
   the dependency information that the special case used to extract
   from the AST structure.

5. **Planning rewrite**: rework `planning` to be the single
   planning pass — CCL-to-CCL, walks the AST, identifies iteration
   sites, recognizes specialized patterns (group-by, hash join,
   semi-join, anti-join, ...) and emits their CCL chains, falls
   back to `iterate(predicate) ≫ source` for unrecognized refined
   sites (and `iterate(λ _ → true) ≫ source` for unrefined ones),
   recurses into emitted CCL fragments to plan nested sites. The
   existing recognizers (`convert_groupby`, `create_hash_joins`,
   `convert_loop_join`, plus the curried-correlated dispatch) are
   retained algorithmically but rewritten to operate on the
   pointful-predicate form and to emit `iterate` chains rather
   than `restrict` ones.

6. **Op-conversion simplification**: remove `iterate_type`'s
   type-slot diving. Add the `Apply(predicate, Builtin::Iterate)`
   arm, the `cast`-passthrough behaviour, and
   assertion-on-unplanned-site as described above. Also remove the
   `input_ty` param on `convert_impl` (and thread it out of the
   call sites): it exists only to force iteration to a type when
   `Compose`'s refined type isn't present on its first child
   (`operator_conversion.rs:350`), which planning now resolves by
   marking iteration explicitly. Update tests.

7. **Pointful simplify pass**: add a new simplify pass that
   operates on refinement predicates in their pointful form, with
   the same kind of rewriting capability as the existing
   point-free `simplify.rs` (predicate normalization, dead-clause
   elimination, constant folding inside predicates, etc.). The
   existing point-free pass is *not* replaced — it continues to
   handle the rest of the AST. The two run side by side at the
   simplify stage. Existing point-free guards in `simplify.rs`
   that reference refinement structure (e.g.,
   `contains_structural_restrict`) are reviewed and adjusted to
   match the new representation.

8. **Optional optimization pass**: strip unused
   `Fun { name: Some(𝑛), .. }` binders to `None` once the codomain
   is final and `is_in_free_vars(𝑛, codomain) == false`. Purely
   cosmetic; not required for correctness.

9. **Remove `Builtin::Restrict`**: once steps 1–8 have landed and
   the migration is complete, delete the `Builtin::Restrict` variant
   and its supporting code. Its responsibilities are now split
   between the `Cast` node (lowering) and `Builtin::Iterate`
   (planning).

## Appendix: worked example for `groupby`

Source program:

```python
[sum(g) for g in groupby(xs, key_fn)]
```

After lowering, the CCL is (simplified for exposition):

```
λ 𝑘 → sum(cast({𝑖: 𝐼 | 𝑖 ▷ xs ▷ key_fn == 𝑘} ⇒ 𝑉, xs))
```

This elides several details of what lowering actually emits — the
list comprehension introduces an extra internal variable, the
comprehension binder `g` is still present, `sum` is composed onto
the end rather than applied inline, and there may be more. None of
that detail bears on the point of the example (how the partition
predicate surfaces at the type level via `cast`), so it is omitted
here.

The outer `λ 𝑘 → ...` maps each partition key to the sum of that
partition. The `cast` casts `xs` (of type `𝐼 ⇒ 𝑉`) to the refined
domain type — a no-op at the value level, but it surfaces the
partition predicate at the type level. `sum` then aggregates over
the (refined) domain.

Inference assigns the outer lambda type `𝐾 ⇒ Int`. The
codomain is just `Int` — `sum` produces a scalar, not a function.
The refinement-with-`𝑘`-dependency lives inside the lambda body,
on the cast's target type
`{𝑖: 𝐼 | 𝑖 ▷ xs ▷ key_fn == 𝑘} ⇒ 𝑉`, not on the outer lambda's
type signature. The outer Fun's binder `𝑘` is populated by
inference (always, regardless of whether the codomain references
it), but here the codomain `𝐼𝑛𝑡` doesn't reference `𝑘`, so the
named-binder form is just the explicit version of the same
function type.

Lambda elimination processes the outer lambda's body normally,
producing a point-free combinator chain. The cast's refinement
predicate `𝑖 ▷ xs ▷ key_fn == 𝑘` is left untouched inside the
type slot — lambda elim does not descend into refinement
predicates.

Simplify operates on the typed AST. No iteration-specific work here;
the refinement predicate is left in its pointful form.

Planning walks the AST. The `Sum` is an aggregate, so its input is
an iteration site. Planning emits `iterate` and inspects the
source's refinement. The structure is the canonical group-by
shape: the iterated function is `λ 𝑘 → ...` whose inner function's
domain is refined by `key_fn(𝑖) == 𝑘` over the same source `xs`
that the outer 𝑘 indexes. Planning's group-by recognizer matches
this shape and emits a bucketize-and-lookup CCL chain: bucketize
`xs` by `key_fn` once at iteration start, then `iterate` over the
distinct keys and look up each 𝑘's bucket. All CCL; no tiles yet.

(If the predicate were not a key-equality form but a different
two-sided equality, hash-join recognition might fire instead. If
no specialized pattern matched — e.g., predicate
`𝑖 + 𝑘 > 0` — planning would fall back to the loop join: build
the synthetic lambda `λ 𝑘 → λ 𝑖 → 𝑖 + 𝑘 > 0`, run it through
lambda elim and simplify, and emit
`iterate(<resulting combinator chain>) ≫ source` at the
iteration site.)

Op-conversion compiles the group-by CCL chain to its tile
equivalent — `IterateExtent` for the `iterate` marker, plus the
hash-bucket build and per-key lookup tiles. At runtime, the
bucketization runs once on `xs`; then the outer iteration over
the distinct keys looks each one up in the prebuilt buckets to
retrieve the matching `𝑖`s.

The same shape applies to any dependent refinement, regardless of
where it was introduced — list-comp filters that happen to capture an
outer binder, for-loop if-guards that reference outer-scope state,
custom refinement-introducing constructs added in the future.

## Appendix: scope-validity test cases

Cases below exercise each binding form the dependent-inference
machinery must handle, organized by the mechanism that resolves the
case before the scope-validity assertion observes the refinement. The
test matrix is the verification surface for the assertion: every
inline case must produce a refinement whose free variables are all in
scope at the destination position, every promote case must preserve
the binder as part of the type, and every reject case must be turned
away by inference with a typing error before any propagation happens.

### Inlined at codomain extraction

#### A. `let`-binding referenced by the body's type

```python
def filtered(collection):
    threshold = 5
    return [x for x in collection if x > threshold]
```

The list-comp filter lowers to a `cast` to refined-domain function
type whose predicate is `𝑥 > threshold`. The refinement's predicate
references the let-bound `threshold`. When inference extracts the
function's codomain past the binding, the inliner substitutes
`threshold ↦ 5` into the predicate. The resulting refinement has
predicate `𝑥 > 5`; free vars `{𝑥}`, all in scope (the refinement's
own binder). Assertion ✓.

#### B. Destructuring `let` over a tuple

```python
def filtered(pair_and_xs):
    (lo, hi) = pair_and_xs.bounds
    return [x for x in pair_and_xs.xs if x > lo and x < hi]
```

The filter predicate references `lo` and `hi`, both bound by the
tuple destructure. Inliner projects: `lo ↦ pair_and_xs.bounds.0`,
`hi ↦ pair_and_xs.bounds.1`. Resulting predicate
`𝑥 > pair_and_xs.bounds.0 and 𝑥 < pair_and_xs.bounds.1`; free vars
`{𝑥, pair_and_xs}`, in scope. ✓

#### C. Destructuring `let` over a record

```python
def filtered(config):
    {lower: lo, upper: hi} = config.bounds
    return [x for x in config.xs if x > lo and x < hi]
```

Same shape as B with field projections: `lo ↦ config.bounds.lower`,
`hi ↦ config.bounds.upper`. Predicate becomes
`𝑥 > config.bounds.lower and 𝑥 < config.bounds.upper`. ✓

(Pending: record-destructure surface syntax. Substitute Cambra's
chosen form once it's nailed down.)

#### D. Chained `let`s (transitive inlining)

```python
def filtered(xs):
    base = 10
    offset = base + 1
    return [x for x in xs if x > offset]
```

The predicate references `offset`, which references `base`. The
inliner runs until fixpoint: `offset ↦ base + 1` then
`base ↦ 10`, yielding predicate `𝑥 > (10 + 1)`. Free vars `{𝑥}`. ✓

This case exists specifically to verify the inliner runs to
fixpoint rather than stopping after one substitution.

#### E. For-loop terminal accumulator value

```python
def filter_against_acc(xs, result):
    acc = mut(0)
    for x in xs:
        acc += x
    return [y for y in result if y < acc]
```

The filter predicate references `acc`. After the for-loop, the
final value of `acc` is the terminal value of the accumulator —
semantically equivalent to a fold of the loop body over `xs`.
Mutability lowering exposes this terminal value as a pure
expression (the fold result), and the inliner substitutes
`acc ↦ <fold expression>` into the predicate. Free vars after
inlining: `{𝑦, xs}` (plus whatever the fold expression
references). All in scope. ✓

The mutable binding is local to the function body; only the
*terminal* value escapes via the inlined fold expression.
Intermediate mid-loop values of `acc` are unobservable from
outside the loop, so they don't need to be exposed in the type.

### Resolved at planning

#### F. List-comp filter capturing an outer Fun-binder (chain-lifted)

```python
def filter_for_key(k):
    return [i for i in xs if some_pred(i, k)]
```

The filter lowers to `cast({𝐼 | some_pred(𝑖, 𝑘)} ⇒ 𝑉, xs)`. The
refinement's predicate references `𝑘`, a function parameter on a
function-typed value whose iteration site, once it reaches
planning, is not in `𝑘`'s lexical scope (the function value gets
iterated wherever a caller passes it to an aggregate, which need
not be inside the function's body). Planning lifts `𝑘` into the
predicate's parameter list — synthetic lambda
`λ 𝑘 → λ 𝑖 → some_pred(𝑖, 𝑘)` — runs it through lambda elim and
simplify, and emits the loop-join CCL
`iterate(<lambda-eliminated chain>) ≫ source`. Assertion at the
refinement's position observes free vars `{𝑖, 𝑘}`; `𝑖` is the
refinement's binder, `𝑘` is the enclosing Fun's. In scope. ✓

This is the canonical "captured refinement" case that motivated
the design.

#### G. (Non-example) For-loop iteration variable referenced by a nested filter (placed in scope)

```python
def process_rows(rows):
    for i in rows:
        process([x for x in i.children if x > i.threshold])
```

The inner list-comp's iteration site sits inside the for-loop's
body. Planning emits the iterate-and-filter CCL chain at the call
to `process`, leaving the predicate's reference to `𝑖` as an
ordinary free-variable reference into the surrounding lexical
scope:

```
process(iterate(λ 𝑥 → 𝑥 > 𝑖.threshold) ≫ 𝑖.children)
```

At this AST position `𝑖` is in scope (bound by the enclosing
for-loop), so no chain lifting is needed — the filter predicate
just references `𝑖` directly. Assertion at the filter predicate's
position observes free vars `{𝑥, 𝑖}`, both in scope. ✓

Contrast with F: there, the iteration site that planning marks
is not inside `𝑘`'s lexical scope (it's wherever the caller
iterates the returned function), so `𝑘` has to be lifted into the
predicate's parameter list. Here `𝑖` is already in scope at the
iteration site, so it stays as a free reference.

### Promoted to a type-level binder

#### H. Function parameter referenced by the body's filter

```python
def filter_less(k):
    return [x for x in xs if x < k]
```

Inference produces `Fun { name: Some("k"), domain: 𝐾, codomain:
... { refined domain on 𝑥 < 𝑘 } ... }`. The function's parameter
is preserved as a Pi-binder on the resulting Fun type; no inlining
is done because `𝑘` is *the* outer binder, not a body-local one.
The refinement's predicate references the Fun's name, which is in
scope inside the codomain by construction. ✓

This is the trivial case — Pi-promotion is the default behavior;
the test exists to verify that function parameters are *not* run
through the inliner.

### Tracked future work

#### I. Pattern-match arm binder referenced by the result type

```python
def filter_against(tagged):
    match tagged:
        case Pair(a, b):
            return [x for x in xs if x > b]
        case Single(s):
            return [x for x in xs if x > s]
```

The result type of each arm carries a refinement whose predicate
references the arm-local binder (`b` in the first arm, `s` in
the second). This is a reasonable thing to want to write, and
the right answer is to *inline the case match into the
refinement* — i.e., produce a refined type whose predicate is
itself a `match` expression that branches on `tagged` to recover
the per-arm value:

```
{𝑥 | match tagged:
       case Pair(a, b): 𝑥 > b
       case Single(s):  𝑥 > s }
```

The refinement's free variables after this transformation are
`𝑥` (its own binder) and `tagged` (in scope at the call site), so
the assertion would pass. But case-inlining into refinement
predicates is a non-trivial feature — it requires the type
system to express match expressions in predicate position, the
inliner to know how to construct them, and the SMT/structural
equality machinery on refinements to handle them. **Tracked for
future work; not implemented in this proposal.** Until then,
inference rejects programs of this shape with a typing error
("result type references arm-local binder `b`"), and the test
matrix should cover that rejection path.

### Assertion unit tests

The scope-validity assertion is a small, isolated piece of code
that takes a refinement (or any type containing one) and a scope
description, and panics if the refinement's predicate has free
variables that aren't in the scope. The tests below exercise the
assertion's implementation directly — they construct in-memory
types and scopes via the type-system API, call the assertion,
and verify it fires (or doesn't) as expected. They are unit
tests against the assertion function, not integration tests over
Cambra source programs.

#### J. Assertion fires on a free variable not in scope

Construct a `Refinement { name: "v", base: Int, predicate:
<expression mentioning 𝑥> }` and a scope that does *not* contain
`𝑥`. Call the assertion against this refinement at the empty
position. The assertion should panic with a message naming `𝑥`
as the unresolved free variable.

#### K. Assertion succeeds on a refinement whose only free vars are in scope

Construct the same refinement (predicate mentions `𝑥`) but with a
scope that *does* contain `𝑥` — say, an enclosing
`Fun { name: Some("x"), .. }` binder on the path. Call the
assertion; it should return cleanly without panicking.

#### L. Assertion succeeds on a refinement whose only free var is its own binder

Construct `Refinement { name: "v", base: Int, predicate:
<expression mentioning 𝑣 only> }` with an empty surrounding
scope. The predicate's only free variable is the refinement's
own binder, which is always in scope inside its own predicate.
Assertion returns cleanly.

#### M. Assertion fires after a buggy substitution

Simulate a substitution bug: construct
`Fun { name: Some("x"), codomain: Refinement {
predicate: <expression mentioning 𝑥> } }`, then mechanically
strip the Fun's binder without updating the refinement (the
shape a buggy `substitute_in_type` that forgets to descend into
predicates would produce). Call the assertion at the new outer
position; it should fire, identifying `𝑥` as out-of-scope.

This is the regression fixture for any future bug in substitution
descent — the test pins the assertion's behavior to "catches this
specific shape of malformed state."
